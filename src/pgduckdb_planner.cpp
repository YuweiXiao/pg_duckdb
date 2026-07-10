#include "pgduckdb/pgduckdb_planner.hpp"

#include "duckdb.hpp"

#include "pgduckdb/catalog/pgduckdb_transaction.hpp"
#include "pgduckdb/scan/postgres_scan.hpp"
#include "pgduckdb/pgduckdb_types.hpp"
#include "pgduckdb/pgduckdb_planner.hpp"
#include "pgduckdb/pgduckdb_table_am.hpp"

extern "C" {
#include "postgres.h"

#include "access/htup_details.h"
#include "access/xact.h"
#include "access/table.h"
#include "catalog/pg_type.h"
#include "nodes/makefuncs.h"
#include "nodes/nodes.h"
#include "nodes/nodeFuncs.h"
#include "nodes/params.h"
#include "optimizer/optimizer.h"
#include "optimizer/planner.h"
#include "optimizer/planmain.h"
#include "parser/parse_coerce.h"
#include "rewrite/rewriteHandler.h"
#include "tcop/pquery.h"
#include "utils/typcache.h"
#include "utils/rel.h"
#include "utils/syscache.h"
#include "utils/guc.h"
#include "parser/parse_relation.h"
#include "utils/acl.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"

#include "pgduckdb/pgduckdb_ruleutils.h"

#include "executor/executor.h"
}

#include "pgduckdb/pg/types.hpp"
#include "pgduckdb/pgduckdb_duckdb.hpp"
#include "pgduckdb/pgduckdb_node.hpp"
#include "pgduckdb/vendor/pg_list.hpp"
#include "pgduckdb/utility/cpp_wrapper.hpp"
#include "pgduckdb/pgduckdb_types.hpp"

static bool
ContainValueRTE(Query *query) {
	foreach_node(RangeTblEntry, rte, query->rtable) {
		if (rte->rtekind == RTE_VALUES) {
			return true;
		} else if (rte->rtekind == RTE_SUBQUERY) {
			if (ContainValueRTE(rte->subquery)) {
				return true;
			}
		}
	}
	return false;
}

bool
IsAllowedPostgresInsert(Query *query, bool throw_error) {
	if (query->commandType == CMD_SELECT) {
		return false;
	}

	int elevel = throw_error ? ERROR : DEBUG4;
	if (query->commandType != CMD_INSERT) {
		elog(elevel, "DuckDB only supports INSERT/SELECT on Postgres tables");
		return false;
	}

	Assert(list_length(query->rtable) >= query->resultRelation);
	RangeTblEntry *target_rel = (RangeTblEntry *)list_nth(query->rtable, query->resultRelation - 1);
	if (pgduckdb::IsDuckdbTable(target_rel->relid)) {
		return false;
	}

	/* Checking supported INSERT types */
	RangeTblEntry *select_rte = NULL;
	foreach_node(RangeTblEntry, rte, query->rtable) {
		if (rte->rtekind == RTE_SUBQUERY) {
			select_rte = rte;
		}
	}

	if (!select_rte) {
		elog(elevel, "DuckDB does not support INSERT without a subquery");
		return false;
	}

	/*
	 * The referenced rtables in the subquery should not include value RTEs. Literal input may vary between Postgres and
	 * DuckDB, such as differences in bytea representation and numeric rounding.
	 */
	if (ContainValueRTE(select_rte->subquery)) {
		elog(elevel, "DuckDB does not support INSERTs with value subqueries");
		return false;
	}

	Relation rel = RelationIdGetRelation(target_rel->relid);
	TupleDesc target_desc = RelationGetDescr(rel);
	bool ret = true;
	for (int i = 0; i < target_desc->natts; i++) {
		Form_pg_attribute attr = TupleDescAttr(target_desc, i);
		if (attr->attisdropped) {
			continue;
		}

		/*
		 * Check if the target column type is supported by pg_duckdb. The type is allowed as long as the type conversion
		 * is implemented.
		 */
		auto duckdb_col_type = pgduckdb::ConvertPostgresToDuckColumnType(attr);
		if (duckdb_col_type.id() == duckdb::LogicalTypeId::INVALID) {
			elog(elevel, "DuckDB does not support INSERTs into tables with column `%s` of unsupported type (OID %u). ",
			     NameStr(attr->attname), attr->atttypid);
			ret = false;
			break;
		}
	}
	RelationClose(rel);

	return ret;
}

duckdb::unique_ptr<duckdb::PreparedStatement>
DuckdbPrepare(const Query *query, const char *explain_prefix) {
	Query *copied_query = (Query *)copyObjectImpl(query);
	const char *query_string;
	if (IsAllowedPostgresInsert(copied_query)) {
		RangeTblEntry *select_rte = NULL;
		foreach_node(RangeTblEntry, rte, copied_query->rtable) {
			if (rte->rtekind == RTE_SUBQUERY) {
				select_rte = rte;
			}
		}

		/* A subquery must be present at this point; other cases should have been filtered out during the
		 * pre-planning phase */
		Assert(select_rte);
		query_string = pgduckdb_get_querydef(select_rte->subquery);
	} else {
		query_string = pgduckdb_get_querydef(copied_query);
	}

	if (explain_prefix) {
		query_string = psprintf("%s %s", explain_prefix, query_string);
	}

	elog(DEBUG2, "(PGDuckDB/DuckdbPrepare) Preparing: %s", query_string);

	auto con = pgduckdb::DuckDBManager::GetConnection();
	return con->context->Prepare(query_string);
}

typedef struct FindSubqueryVarContext {
	int select_rti;
	AttrNumber attno;
} FindSubqueryVarContext;

static bool
FindSubqueryVarWalker(Node *node, void *context) {
	FindSubqueryVarContext *ctx = (FindSubqueryVarContext *)context;
	if (node == NULL) {
		return false;
	}

	if (IsA(node, Var)) {
		Var *var = (Var *)node;
		if (var->varno == ctx->select_rti) {
			ctx->attno = var->varattno;
			return true;
		}
		return false;
	}

#if PG_VERSION_NUM >= 160000
	return expression_tree_walker(node, FindSubqueryVarWalker, context);
#else
	return expression_tree_walker(node, (bool (*)())((void *)FindSubqueryVarWalker), context);
#endif
}

/*
 * ReconstructTargetListForInsert - Aligns the target list with the table's columns
 *
 * The DuckDB scan produces the output columns of the SELECT source, but the
 * ModifyTable node expects one value per table column, in the order of the
 * table definition. The INSERT might assign the SELECT columns to a subset of
 * the table's columns and in a different order than the table definition, so
 * we cannot simply map them positionally. Instead we use the Var in each
 * entry of the INSERT its targetlist, which references the SELECT column that
 * is assigned to that table column, and that matches the position of the
 * DuckDB scan output. Columns that the INSERT doesn't assign get their
 * default expression that the rewriter put in the targetlist, or NULL when
 * there is none.
 */
static List *
ReconstructTargetListForInsert(TupleDesc pg_tupdesc, Query *query, List *duckdb_targetlist) {
	List *target_list = NIL;

	FindSubqueryVarContext ctx = {0, 0};
	int rti = 1;
	foreach_node(RangeTblEntry, rte, query->rtable) {
		if (rte->rtekind == RTE_SUBQUERY) {
			ctx.select_rti = rti;
		}
		rti++;
	}

	for (int i = 0; i < pg_tupdesc->natts; i++) {
		Form_pg_attribute attr = TupleDescAttr(pg_tupdesc, i);

		/*
		 * For dropped columns the ModifyTable node expects a NULL constant,
		 * see ExecCheckPlanOutput.
		 */
		if (attr->attisdropped) {
			TargetEntry *null_entry =
			    makeTargetEntry((Expr *)makeNullConst(INT4OID, -1, InvalidOid), attr->attnum, NULL, false);
			target_list = lappend(target_list, null_entry);
			continue;
		}

		/*
		 * Locate the matching column in the query target list. If its
		 * expression references a SELECT column we use the matching column
		 * of the DuckDB scan. If it doesn't, it's either a default value
		 * that the rewriter put there, or an unknown-type constant that the
		 * parser inlined instead of creating a Var for it. In both of those
		 * cases the expression itself produces the value to insert, so we
		 * can use it directly.
		 */
		TargetEntry *target_entry = NULL;
		foreach_node(TargetEntry, query_target_entry, query->targetList) {
			if (query_target_entry->resno == attr->attnum) {
				ctx.attno = 0;
				FindSubqueryVarWalker((Node *)query_target_entry->expr, &ctx);
				if (ctx.attno != 0) {
					if (ctx.attno > list_length(duckdb_targetlist)) {
						elog(ERROR, "SELECT column assigned to column \"%s\" is missing from the DuckDB result",
						     NameStr(attr->attname));
					}
					target_entry =
					    (TargetEntry *)copyObjectImpl(list_nth_node(TargetEntry, duckdb_targetlist, ctx.attno - 1));
					target_entry->resno = attr->attnum;
				} else {
					target_entry = query_target_entry;
				}
				break;
			}
		}

		if (target_entry) {
			target_list = lappend(target_list, target_entry);
			continue;
		}

		/* For column not found in the target list, create a NULL Expr for it */
		target_entry = makeTargetEntry((Expr *)makeNullConst(attr->atttypid, attr->atttypmod, attr->attcollation),
		                               attr->attnum, pstrdup(NameStr(attr->attname)), false);
		target_list = lappend(target_list, target_entry);
	}

	return target_list;
}

static Plan *
CreatePlan(Query *query, bool throw_error) {
	int elevel = throw_error ? ERROR : WARNING;
	/*
	 * Prepare the query, se we can get the returned types and column names.
	 */

	duckdb::unique_ptr<duckdb::PreparedStatement> prepared_query = DuckdbPrepare(query);

	if (prepared_query->HasError()) {
		elog(elevel, "(PGDuckDB/CreatePlan) Prepared query returned an error: %s", prepared_query->GetError().c_str());
		return nullptr;
	}

	CustomScan *duckdb_node = makeNode(CustomScan);

	auto &prepared_result_types = prepared_query->GetTypes();

	for (size_t i = 0; i < prepared_result_types.size(); i++) {
		Oid postgresColumnOid = pgduckdb::GetPostgresDuckDBType(prepared_result_types[i], throw_error);

		if (!OidIsValid(postgresColumnOid)) {
			return nullptr;
		}

		HeapTuple tp;
		Form_pg_type typtup;

		tp = SearchSysCache1(TYPEOID, ObjectIdGetDatum(postgresColumnOid));
		if (!HeapTupleIsValid(tp)) {
			elog(elevel, "(PGDuckDB/CreatePlan) Cache lookup failed for type %u", postgresColumnOid);
			return nullptr;
		}

		typtup = (Form_pg_type)GETSTRUCT(tp);
		typtup->typtypmod = pgduckdb::GetPostgresDuckDBTypemod(prepared_result_types[i]);

		/*
		 * We hardcode varno 1 here, because our final plan will only have a
		 * single RTE (this custom scan). In the past we put 0 here, and then
		 * filled it in later. If at some point we need multiple RTEs again, we
		 * might want to start doing that again.
		 */
		Var *var = makeVar(1, i + 1, postgresColumnOid, typtup->typtypmod, typtup->typcollation, 0);

		TargetEntry *target_entry =
		    makeTargetEntry((Expr *)var, i + 1, (char *)pstrdup(prepared_query->GetNames()[i].c_str()), false);

		/* Our custom scan node needs the custom_scan_tlist to be set */
		duckdb_node->custom_scan_tlist = lappend(duckdb_node->custom_scan_tlist, copyObjectImpl(target_entry));

		/* For the plan its targetlist we use INDEX_VAR as the varno, which
		 * means it references our custom_scan_tlist. */
		var->varno = INDEX_VAR;

		/* But we also need an actual target list, because Postgres expects it
		 * for things like materialization */
		duckdb_node->scan.plan.targetlist = lappend(duckdb_node->scan.plan.targetlist, target_entry);

		ReleaseSysCache(tp);
	}

	if (IsAllowedPostgresInsert(query)) {
		RangeTblEntry *target_rel = (RangeTblEntry *)list_nth(query->rtable, query->resultRelation - 1);
		Relation rel = RelationIdGetRelation(target_rel->relid);
		TupleDesc pg_tupdesc = RelationGetDescr(rel);

		/*
		 * This also needs to happen when the column counts match, because an
		 * INSERT that specifies all columns can still assign them in a
		 * different order than the table definition.
		 */
		duckdb_node->scan.plan.targetlist =
		    ReconstructTargetListForInsert(pg_tupdesc, query, duckdb_node->scan.plan.targetlist);

		RelationClose(rel);
	}

	duckdb_node->custom_private = list_make1(query);
	duckdb_node->methods = &duckdb_scan_scan_methods;

	return (Plan *)duckdb_node;
}

/* Creates a matching RangeTblEntry for the given CustomScan node */
static RangeTblEntry *
DuckdbRangeTableEntry(CustomScan *custom_scan) {
	List *column_names = NIL;
	foreach_node(TargetEntry, target_entry, custom_scan->scan.plan.targetlist) {
		column_names = lappend(column_names, makeString(target_entry->resname));
	}
	RangeTblEntry *rte = makeNode(RangeTblEntry);

	/* We need to choose an RTE kind here. RTE_RELATION does not work due to
	 * various asserts that fail due to us not setting some of the fields on
	 * the entry. Instead of filling those fields in with dummy values we use
	 * RTE_NAMEDTUPLESTORE, for which no special fields exist. */
	rte->rtekind = RTE_NAMEDTUPLESTORE;
	rte->eref = makeAlias("duckdb_scan", column_names);
	rte->inFromCl = true;

	return rte;
}

/*
 * CoerceTargetList - Coerces the target list from DuckDB to match PostgreSQL types
 *
 * This function takes a target list from a DuckDB query and ensures that each column
 * has the correct data type expected by PostgreSQL. It adds type coercions where
 * necessary to make the types compatible.
 *
 * Parameters:
 *   duckdb_targetlist - The target list from the DuckDB query
 *   pg_tupdesc - PostgreSQL tuple descriptor containing the expected column types
 *
 * Returns:
 *   A new target list with appropriate type coercions applied
 */
List *
CoerceTargetList(List *duckdb_targetlist, TupleDesc pg_tupdesc) {
	List *ret = NIL;

	foreach_node(TargetEntry, source_te, duckdb_targetlist) {
		AttrNumber attnum = source_te->resno;
		if (attnum > pg_tupdesc->natts) {
			elog(ERROR, "DuckDB query returns more columns than Postgres wants");
		}

		/* Get expected target type */
		Form_pg_attribute attr = TupleDescAttr(pg_tupdesc, attnum - 1);
		Oid targetTypeId = attr->atttypid;
		int32 targetTypeMod = attr->atttypmod;

		/* Get source expression and its type */
		Expr *expr = source_te->expr;
		Oid sourceTypeId = exprType((Node *)expr);
		int32 sourceTypeMod = exprTypmod((Node *)expr);

		/* Add coercion if needed */
		if (sourceTypeId != targetTypeId || sourceTypeMod != targetTypeMod) {
			expr = (Expr *)coerce_to_target_type(NULL, (Node *)expr, sourceTypeId, targetTypeId, targetTypeMod,
			                                     COERCION_EXPLICIT, COERCE_IMPLICIT_CAST, -1);

			if (expr == NULL)
				elog(ERROR, "cannot coerce column %d from type %u to target type %u", attnum, sourceTypeId,
				     targetTypeId);

			/* Create a new target entry with coerced expression */
			TargetEntry *new_te = makeTargetEntry(expr, attnum, source_te->resname, source_te->resjunk);
			ret = lappend(ret, new_te);
		} else {
			ret = lappend(ret, source_te);
		}
	}

	return ret;
}

static void
check_view_perms_recursive(Query *query) {
	ListCell *lc;

	if (query == NULL) {
		return;
	}

	foreach (lc, query->rtable) {
		RangeTblEntry *rte = lfirst_node(RangeTblEntry, lc);

#if PG_VERSION_NUM < 160000
		if (rte->relkind == RELKIND_VIEW) {
			bool result = ExecCheckRTEPerms(rte);
			if (!result) {
				aclcheck_error(ACLCHECK_NO_PRIV, OBJECT_VIEW, get_rel_name(rte->relid));
			}
		}
#else
		if (rte->perminfoindex != 0 && rte->relkind == RELKIND_VIEW) {
			RTEPermissionInfo *perminfo = getRTEPermissionInfo(query->rteperminfos, rte);
			bool result = ExecCheckOneRelPerms(perminfo);
			if (!result) {
				aclcheck_error(ACLCHECK_NO_PRIV, OBJECT_VIEW, get_rel_name(perminfo->relid));
			}
		}
#endif

		if (rte->rtekind == RTE_SUBQUERY && rte->subquery) {
			check_view_perms_recursive(rte->subquery);
		}
	}

	if (query->cteList) {
		ListCell *lc_cte;
		foreach (lc_cte, query->cteList) {
			CommonTableExpr *cte = (CommonTableExpr *)lfirst(lc_cte);
			if (IsA(cte->ctequery, Query)) {
				check_view_perms_recursive((Query *)cte->ctequery);
			}
		}
	}
}

PlannedStmt *
DuckdbPlanNode(Query *parse, int cursor_options, bool throw_error) {

	/* Properly check perms if there's a view or WITH statement */
	check_view_perms_recursive(parse);

	/* We need to check can we DuckDB create plan */

	Plan *duckdb_plan = InvokeCPPFunc(CreatePlan, parse, throw_error);
	CustomScan *custom_scan = castNode(CustomScan, duckdb_plan);

	if (!duckdb_plan) {
		return nullptr;
	}

	/*
	 * If creating a plan for a scrollable cursor add a Material node at the
	 * top because or CustomScan does not support backwards scanning.
	 */
	if (cursor_options & CURSOR_OPT_SCROLL) {
		duckdb_plan = materialize_finished_plan(duckdb_plan);
	}

	/*
	 * For INSERTs into Postgres tables only the SELECT source of the INSERT
	 * runs in DuckDB. We let standard_planner build the normal INSERT plan,
	 * so that the ModifyTable node and the result relation metadata are all
	 * filled in correctly, and then replace the plan that produces the rows
	 * to insert with our CustomScan node.
	 */
	if (IsAllowedPostgresInsert(parse)) {
		Query *copied_query = (Query *)copyObjectImpl(parse);
		PlannedStmt *postgres_plan = standard_planner(copied_query, NULL, cursor_options, NULL);
		Assert(IsA(postgres_plan->planTree, ModifyTable));
		TupleDesc target_desc = ExecTypeFromTL(outerPlan(postgres_plan->planTree)->targetlist);
		duckdb_plan->targetlist = CoerceTargetList(duckdb_plan->targetlist, target_desc);
		outerPlan(postgres_plan->planTree) = duckdb_plan;

		/* Put a DuckDB RTE at the end of the rtable */
		RangeTblEntry *insert_rte = DuckdbRangeTableEntry(custom_scan);
		postgres_plan->rtable = lappend(postgres_plan->rtable, insert_rte);

		/*
		 * CreatePlan hardcodes varno 1 in the custom_scan_tlist, because
		 * normally our CustomScan is the only RTE in the plan. Here it got
		 * appended after the RTEs of the INSERT statement, so we need to
		 * update the varnos to point to the actual position of our RTE.
		 */
		foreach_node(TargetEntry, target_entry, custom_scan->custom_scan_tlist) {
			Var *var = castNode(Var, target_entry->expr);
			var->varno = list_length(postgres_plan->rtable);
		}

		return postgres_plan;
	}

	RangeTblEntry *rte = DuckdbRangeTableEntry(custom_scan);

	PlannedStmt *result = makeNode(PlannedStmt);
	result->commandType = parse->commandType;
	result->queryId = parse->queryId;
	result->hasReturning = (parse->returningList != NIL);
	result->hasModifyingCTE = parse->hasModifyingCTE;
	result->canSetTag = parse->canSetTag;
	result->transientPlan = false;
	result->dependsOnRole = false;
	result->parallelModeNeeded = false;
	result->planTree = duckdb_plan;
	result->rtable = list_make1(rte);
#if PG_VERSION_NUM >= 160000
	result->permInfos = NULL;
#endif
#if PG_VERSION_NUM >= 190000
	result->resultRelationRelids = NULL;
#else
	result->resultRelations = NULL;
#endif
	result->appendRelations = NULL;
	result->subplans = NIL;
	result->rewindPlanIDs = NULL;
	result->rowMarks = NIL;
	result->relationOids = NIL;
	result->invalItems = NIL;
	result->paramExecTypes = NIL;

	/* utilityStmt should be null, but we might as well copy it */
	result->utilityStmt = parse->utilityStmt;
	result->stmt_location = parse->stmt_location;
	result->stmt_len = parse->stmt_len;

	return result;
}
