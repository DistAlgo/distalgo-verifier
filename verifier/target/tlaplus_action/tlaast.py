
TLA_AND = '''/\\'''
TLA_OR = '''\/'''
TLA_EQ = "="
TLA_NEQ = "#"
TLA_NOT = '''\\neg'''

TLA_GT = ">"
TLA_GE = ">="
TLA_LT = "<"
TLA_LE = "<="

TLA_MOD = '%'
TLA_MINUS = '-'
TLA_ADD = '+'
TLA_DIV = '\\div'

TLA_CONCAT = "\\o"

TLA_UNION = "\\cup"
TLA_SETSUB = "\\"

TLA_IN = "\\in"

TLA_ALL = "\\A"
TLA_EXISTS = "\\E"

# reference tla-plus page 268

class TlaAST(object):

    _fields = []
    _attributes = []

    def __init__(self):
        super().__init__()

    def to_tla(self, indent=0):
        print(self)
        raise NotImplementedError()

class TlaModule(TlaAST):
    _fields = ["statements"]
    _attributes = ["name"]

    def __init__(self, name, statements):
        super().__init__()
        self.name = name
        self.statements = statements

    def to_tla(self):
        lines = '''----------------------------- MODULE {0} -------------------\n'''.format(self.name)
        for statement in self.statements:
            lines += statement.to_tla(0)
            lines += '\n\n'
        lines += '\n'
        lines += '==============================================================\n'
        return lines
                 
class TlaSymbol(TlaAST):
    _attributes = ["name"]

    def __init__(self, name):
        super().__init__()
        self.name = name

    def add_prime(self):
        self.name += "'"

    def to_tla(self, indent=0):
        return self.name

class TlaExtendsStmt(TlaAST):
    _fields = ["extends"]

    def __init__(self, extends):
        super().__init__()
        self.extends = extends

    def to_tla(self, indent=0):
        return "EXTENDS {0}\n".format(", ".join(self.extends))

class TlaVariablesStmt(TlaAST):
    _fields = ["variables"]

    def __init__(self, variables):
        super().__init__()
        self.variables = variables

    def to_tla(self, indent=0):
        return "VARIABLES {0}\n".format(", ".join(self.variables))

class TlaConstantStmt(TlaAST):
    _fields = ["constants"]

    def __init__(self, constants):
        super().__init__()
        self.constants = constants

    def to_tla(self, indent=0):
        return "CONSTANTS {0}\n".format(", ".join(constant.to_tla() for constant in self.constants))

class TlaDefinitionStmt(TlaAST):
    _fields = ["name", "args", "expr"]

    def __init__(self, name, args, expr):
        super().__init__()
        self.name = name
        self.args = args
        self.expr = expr

    def to_tla(self, indent=0):
        indent_string = " " * indent
        start = ("""{1}{2} ==\n"""
                 """{0}    {3}""").format(indent_string,
                                          self.name.to_tla(),
                                          "" if len(self.args) == 0 else "({0})".format(", ".join([arg.to_tla() for arg in self.args])),
                                          self.expr.to_tla(indent + 4))
        return start

#===============================================
# logic and set
#===============================================
class TlaAndOrExpr(TlaAST):
    _fields = ["exprs"]
    _attributes = ["op"]

    def __init__(self, op, exprs):
        super().__init__()
        self.op = op
        self.exprs = exprs

    def to_tla(self, indent=0):
        exprs = self.exprs if self.exprs else [TlaConstantExpr(True)]
        if len(exprs) == 1:
            return ("\n" + " " * indent).join(["{0}".format(exprs[0].to_tla(indent + 1))]) #Why +1?
        else:
            return ("\n" + " " * indent).join(["{0} {1}".format(self.op, expr.to_tla(indent + len(self.op) + 1)) for expr in exprs])

class TlaBinaryExpr(TlaAST):
    _fields = ["lexpr", "rexpr"]
    _attributes = ["op"]

    def __init__(self, op, lexpr, rexpr):
        super().__init__()
        self.lexpr = lexpr
        self.rexpr = rexpr
        self.op = op

    def to_tla(self, indent=0):
        return "{0} {1} {2}".format(self.lexpr.to_tla(indent), self.op, self.rexpr.to_tla(indent))

class TlaUnaryExpr(TlaAST):
    _fields = ["expr"]
    _attributes = ["op"]

    def __init__(self, op, expr):
        super().__init__()
        self.expr = expr
        self.op = op

    def to_tla(self, indent=0):
        return "{0} {1}".format(self.op, self.expr.to_tla(indent))
class TlaPredicateExpr(TlaAST):
    _fields = ["predicate", "expr"]
    _attributes = ["quantifier"]

    def __init__(self, quantifier, predicate, expr):
        super().__init__()
        self.quantifier = quantifier
        self.predicate = predicate
        self.expr = expr

    def to_tla(self, indent=0):
        indent_string = " " * indent
        return ("""{1} {2}:\n"""
                """{0}    {3}""").format(indent_string,
                                         self.quantifier,
                                         self.predicate.to_tla(indent + len(self.quantifier)),
                                         self.expr.to_tla(indent + 4))

class TlaIfExpr(TlaAST):
    _fields = ["condition", "ifexpr", "elseexpr"]

    def __init__(self, condition, ifexpr, elseexpr):
        super().__init__()
        self.condition = condition
        self.ifexpr = ifexpr
        self.elseexpr = elseexpr

    def to_tla(self, indent=0):
        indent_string = " " * indent
        return ("""\n{0}IF   {1}\n"""
                """{0}THEN {2}\n"""
                """{0}ELSE {3}""").format(indent_string,
                                          self.condition.to_tla(indent + 5),
                                          self.ifexpr.to_tla(indent + 5),
                                          self.elseexpr.to_tla(indent + 5))

class TlaCase(TlaAST):
    _fields = ["caseexpr", "expr"]

    def __init__(self, caseexpr, expr):
        super().__init__()
        self.caseexpr = caseexpr
        self.expr = expr

    def to_tla(self, indent=0):
        return "{0} -> {1}".format(self.caseexpr.to_tla(indent), self.expr.to_tla(indent))

class TlaCaseExpr(TlaAST):
    _fields = ["cases"]

    def __init__(self, cases):
        super().__init__()
        self.cases = cases

    def to_tla(self, indent=0):
        return "CASE {0}".format(" [] ".join(case.to_tla(indent + 4) for case in self.cases))

class TlaInstantiationExpr(TlaAST):
    _fields = ["name", "arg"]

    def __init__(self, name, args):
        super().__init__()
        assert(isinstance(args, list))
        self.name = name
        self.args = args

    def to_tla(self, indent=0):
        return "{0}({1})".format(self.name.to_tla(indent), ", ".join([arg.to_tla(indent) for arg in self.args]))
 
class TlaSetExpr(TlaAST):
    _fields = ["exprs"]
    
    def __init__(self, exprs):
        super().__init__()
        self.exprs = exprs

    def to_tla(self, indent=0):
        return "{{{0}}}".format(", ".join([expr.to_tla() for expr in self.exprs]))

# {e \in S: expr}
class TlaSetCompositionExpr(TlaAST):
    _fields = ["element", "domain", "expr"]
    def __init__(self, element, domain, expr):
        self.element = element
        self.domain = domain
        self.expr = expr

    def to_tla(self, indent=0):
        if self.domain is not None:
            return ("""{{{1} \\in {2}:\n"""
                    """{0}    {3}}}""").format(" " * indent, self.element.to_tla(indent), self.domain.to_tla(indent), self.expr.to_tla(indent + 4))
        else:
            return ("""{{{0}: {1}}}""").format(self.element.to_tla(indent), self.expr.to_tla(indent + 4))

#===============================================
# Function operator
#=============================================== 
class TlaApplyExpr(TlaAST):
    _fields = ["func", "arg"]

    def __init__(self, func, arg):
        super().__init__()
        self.func = func
        self.arg = arg

    def to_tla(self, indent=0):
        return "{0}[{1}]".format(self.func.to_tla(), self.arg.to_tla())
    
# DOMAIN f
class TlaDomainExpr(TlaAST):
    _fields = ["expr"]

    def __init__(self, expr):
        super().__init__()
        self.expr = expr

    def to_tla(self, indent=0):
        return "DOMAIN {0}".format(self.expr.to_tla(indent + 7))

# [x \in S |-> e ]
class TlaFunctionCompositionExpr(TlaAST):
    _fields = ["iterator", "setexpr", "expr"]

    def __init__(self, iterator, setexpr, expr):
        super().__init__()
        self.iterator = iterator
        self.setexpr = setexpr
        self.expr = expr

    def to_tla(self, indent=0):
        indent_string = indent * " "
        return ("""[{1} \\in {2} |->\n"""
                """{0}    {3}]""").format(indent_string,
                                           self.iterator.to_tla(indent + 1),
                                           self.setexpr.to_tla(indent),
                                           self.expr.to_tla(indent + 4))
    
# [S -> T]

# [f EXCEPT ![e1] = e2]
class TlaExceptExpr(TlaAST):
    _fields = ["origin", "exprs"]
    
    def __init__(self, origin, exprs):
        super().__init__()
        self.origin = origin
        self.exprs = exprs
        
    def to_tla(self, indent=0):
        return "[{0} EXCEPT {1}]".format(self.origin.to_tla(), ", ".join([expr.to_tla(indent) for expr in self.exprs]))

class TlaLetExpr(TlaAST):
    _fields = ["definitions", "expr"]

    def __init__(self, definition, expr):
        super().__init__()
        if isinstance(definition, list):
            self.definitions = definition
        else:
            self.definitions = [definition]
        self.expr = expr

    def to_tla(self, indent=0):
        indent_string = " " * indent
        return ("\n{0}LET {1}\n"
                "{0}IN  {2}").format(indent_string,
                                     ("\n" + (" " * (indent + 4))).join([definition.to_tla(indent + 4) for definition in self.definitions]),
                                     self.expr.to_tla(indent + 4))

class TlaChooseExpr(TlaAST):
    _fields = ["predicate", "expr"]

    def __init__(self, predicate, expr):
        super().__init__()
        self.predicate = predicate
        self.expr = expr

    def to_tla(self, indent=0):
        return ("CHOOSE {0} : {1}").format(self.predicate.to_tla(indent), self.expr.to_tla(indent + 4))

#===============================================   
# Record operator
#===============================================
class TlaFieldExpr(TlaAST):
    _fields = ["record", "field"]

    def __init__(self, record, field):
        super().__init__()
        self.record = record
        self.field = field

    def to_tla(self, indent=0):
        return "{0}.{1}".format(self.record.to_tla(), self.field.to_tla())
    
class TlaMap(TlaAST):
    _fields = ["key", "value"]

    def __init__(self, key, value):
        super().__init__()
        self.key = key
        self.value = value

    def to_tla(self, indent=0):
        return "{0} |-> {1}".format(self.key.to_tla(), self.value.to_tla())

# [h1 |-> e1, ..., hn |-> en]
class TlaRecordCompositionExpr(TlaAST):
    _fields = ["maps"]

    def __init__(self, maps):
        super().__init__()
        self.maps = maps

    def to_tla(self, indent=0):
        return "[{0}]".format(", ".join([mapping.to_tla() for mapping in self.maps]))
    
# [h1 : S1, ..., hn : Sn ]
    
#===============================================
# Tuple operator
#===============================================
class TlaIndexExpr(TlaAST):
    _fields = ["value", "index"]

    def __init__(self, value, index):
        super().__init__()
        self.value = value
        self.index = index

    def to_tla(self, indent=0):
        return "{0}[{1}]".format(self.value.to_tla(), self.index.to_tla())
    
class TlaTupleExpr(TlaAST):
    _fields = ["exprs"]
    
    def __init__(self, exprs):
        super().__init__()
        self.exprs = exprs

    def to_tla(self, indent=0):
        return "<< {0} >>".format(", ".join([expr.to_tla(indent) if expr is not None else "NOOOONE" for expr in self.exprs]))

# S1 x S2 x  ... x Sn    
# class TlaTupleSetExpr

#===============================================
# Actions
#===============================================
class TlaUnchangedActionExpr(TlaAST):
    _fields = ["action", "state"]
    
    def __init__(self, action, state):
        super().__init__()
        self.action = action
        self.state = state

    def to_tla(self, indent=0):
        return "[{0}]_{1}".format(self.action.to_tla(), self.state.to_tla())
    
class TlaChangedActionExpr(TlaAST):
    _fields = ["action", "state"]
    
    def __init__(self, action, state):
        super().__init__()
        self.action = action
        self.state = state

    def to_tla(self, indent=0):
        return "<{0}>_{1}".format(self.action.to_tla(), self.state.to_tla())
    
class TlaUnchangedExpr(TlaAST):
    _fields = ["state"]
    
    def __init__(self, all_vars, changed):
        super().__init__()
        self.all_vars = all_vars
        self.changed = changed

    @property
    def state(self):
        return [var for var in (self.all_vars) if var not in self.changed]

    def to_tla(self, indent=0):
        return "UNCHANGED {0}".format(TlaTupleExpr(TlaSymbol(s) for s in self.state).to_tla())

#===============================================
# constant
#===============================================
class TlaConstantExpr(TlaAST):
    _attributes = ["value"]

    def __init__(self, value):
        super().__init__()
        self.value = value

    def to_tla(self, indent=0):
        if isinstance(self.value, str):
            return '"{0}"'.format(self.value)
        elif isinstance(self.value, bool):
            return "TRUE" if self.value else "FALSE"
        elif self.value is None:
            return "<<>>"
        return str(self.value)

class TlaIntegerSetExpr(TlaAST):
    _fields = ["start", "end"]

    def __init__(self, start, end):
        super().__init__()
        self.start = start
        self.end = end

    def to_tla(self, indent=0):
        return "{0}..{1}".format(self.start.to_tla(), self.end.to_tla())

#================================================
# dummy for debug purpose
#================================================
class TlaPlaceHolder(TlaAST):
    def __init__(self, node):
        super().__init__()
        self.node = node

    def to_tla(self,  indent=0):
        return "<place holder for: {0}".format(self.node)

if __name__ == "__main__":
    tlaast = TlaModule("TEST",
                       [TlaConstantStmt([TlaSymbol("N")]),
                        TlaDefinitionStmt(TlaSymbol("Send"),
                                          [TlaSymbol("type")],
                                          TlaAndOrExpr("/\\",
                                                       [TlaAssignExpr(TlaSymbol("reqc"), TlaConstantExpr("int", -1))]))])
    print(tlaast.to_tla())
    print(ast.dump(tlaast, include_attributes=True))
