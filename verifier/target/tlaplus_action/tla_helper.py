from .tlaast import *

def _(symbol):
    if isinstance(symbol, str) or isinstance(symbol, int):
        return TlaSymbol(str(symbol))
    else:
        assert(isinstance(symbol, TlaAST))
        return symbol

def tla_eq(lexpr, rexpr):
    return TlaBinaryExpr(TLA_EQ, lexpr, rexpr)

def tla_neq(lexpr, rexpr):
    return TlaBinaryExpr(TLA_NEQ, lexpr, rexpr)

def tla_gt(lexpr, rexpr):
    return TlaBinaryExpr(TLA_GT, lexpr, rexpr)

def tla_ge(lexpr, rexpr):
    return TlaBinaryExpr(TLA_GE, lexpr, rexpr)

def tla_lt(lexpr, rexpr):
    return TlaBinaryExpr(TLA_LT, lexpr, rexpr)

def tla_le(lexpr, rexpr):
    return TlaBinaryExpr(TLA_LE, lexpr, rexpr)

def tla_concat(lexpr, rexpr):
    return TlaBinaryExpr(TLA_CONCAT, lexpr, rexpr)

def tla_union(lexpr, rexpr):
    return TlaBinaryExpr(TLA_UNION, lexpr, rexpr)

def tla_in(lexpr, rexpr):
    return TlaBinaryExpr(TLA_IN, lexpr, rexpr)

def tla_forall(predicate, expr):
    return TlaPredicateExpr(TLA_ALL, predicate, expr)

def tla_exists(predicate, expr):
    return TlaPredicateExpr(TLA_EXISTS, predicate, expr)

def tla_setsub(lexpr, rexpr):
    return TlaBinaryExpr(TLA_SETSUB, lexpr, rexpr)

def tla_and(exprs):
    return TlaAndOrExpr(TLA_AND, exprs)

def tla_or(exprs):
    return TlaAndOrExpr(TLA_OR, exprs)

def tla_append(*args):
    return TlaInstantiationExpr(_("Append"), list(args))

def apply_expr(a, b):
    return TlaApplyExpr(_(a), _(b))

def inst_expr(a, *args):
    return TlaInstantiationExpr(_(a), list(args))

def index_expr(a, b):
    return TlaIndexExpr(_(a), _(b))

def pc_expr():
    return apply_expr("pc", "self")

def pc_is_expr(label):
    if isinstance(label, str):
        label = TlaConstantExpr(label)
    assert(isinstance(label, TlaAST))
    return tla_eq(pc_expr(), label)

def except_expr_helper(var, expr):
    var = _(var)
    var_prime = TlaSymbol(var.name)
    var_prime.add_prime()
    return tla_eq(var_prime, TlaExceptExpr(var, [tla_eq(apply_expr("!", "self"), expr)]))

def clock_expr():
    return apply_expr("clock", "self")

def send_action(need_sent=True):
    msg = TlaTupleExpr([TlaConstantExpr('sent'), TlaTupleExpr([clock_expr(), _("self"), _("proc")]), _("content")])
    exprs = [tla_eq(_("msgQueue'"), TlaFunctionCompositionExpr(_("proc"), _("process"),
                                                               TlaIfExpr(tla_in(_("proc"), _("dest")),
                                                                         tla_append(apply_expr("msgQ", "proc"), msg),
                                                                         apply_expr("msgQ", "proc")))),
            ]
    if need_sent:
        msg = TlaTupleExpr([TlaConstantExpr('sent'), TlaTupleExpr([clock_expr(), _("proc"), _("self")]), _("content")])
        exprs.append(except_expr_helper("sent", tla_union(TlaApplyExpr(_("sent"), _("self")), TlaSetCompositionExpr(msg, None, tla_in(_("proc"), _("dest"))))))
    return TlaDefinitionStmt(_("Send"),
                             [_("self"), _("content"), _("dest"), _("msgQ")],
                             tla_and(exprs))


def yield_point_action(scope, expr, need_rcvd=True):
    timestamp = TlaIndexExpr(TlaIndexExpr(_("msg"), TlaConstantExpr(2)), TlaConstantExpr(1))
    exprs = [except_expr_helper("clock", TlaBinaryExpr("+",
                                                       TlaConstantExpr(1),
                                                       TlaIfExpr(tla_gt(timestamp, _("@")),
                                                                 timestamp,
                                                                 _("@")))),
             ]
    if need_rcvd:
        envelop = TlaIndexExpr(_("msg"), TlaConstantExpr(2))
        new_envelop = TlaTupleExpr([TlaIndexExpr(envelop, TlaConstantExpr(1)),
            TlaIndexExpr(envelop, TlaConstantExpr(3)),
            TlaIndexExpr(envelop, TlaConstantExpr(2))])

        rcvd_msg = TlaTupleExpr([TlaConstantExpr('rcvd'), new_envelop, TlaIndexExpr(_("msg"), TlaConstantExpr(3))])
        exprs.append(except_expr_helper("rcvd", tla_union(apply_expr("rcvd", "self"), TlaSetExpr([rcvd_msg]))))
    exprs.append(expr)
    return TlaDefinitionStmt(_(scope.gen_name("yield")),
                             [_("self")],
                             tla_and([pc_is_expr(scope.gen_name('yield')),
                                      tla_eq(TlaSymbol("atomic_barrier"), TlaConstantExpr(-1)),
                             TlaLetExpr(TlaDefinitionStmt(_("msg"), [],
                                                          inst_expr("Head", apply_expr("msgQueue", "self"))),
                                        TlaIfExpr(tla_neq(apply_expr("msgQueue", "self"), TlaTupleExpr([])),
                                                  tla_and(exprs),
                                                  tla_and([
                                                      tla_eq(TlaSymbol("atomic_barrier'"), TlaSymbol("self")),
                                                      except_expr_helper("pc", apply_expr(scope.gen_name("yield_ret_pc"), "self"))])))]))
