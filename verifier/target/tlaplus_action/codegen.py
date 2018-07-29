from ... import opt, ir
from ...frontend import ScopeType
from da.compiler import dast
from .tlaast import *
from .tla_translator import *
import sys
import contextlib

@contextlib.contextmanager
def smart_open(filename=None):
    if filename and filename != '-':
        fh = open(filename, 'w')
    else:
        fh = sys.stdout

    try:
        yield fh
    finally:
        if fh is not sys.stdout:
            fh.close()

class Action(object):
    def __init__(self, pc):
        self.pc = pc

class CodeGen(object):
    def __init__(self, passmanager):
        self.vars = set()
        self.passmanager = passmanager
        self.translator = Translator(self)

        self.names = ["pc", "msgQueue", "clock", "atomic_barrier"]
        if self.need_sent():
            self.names.append("sent")
        if self.need_rcvd():
            self.names.append("rcvd")
    def need_sent(self):
        return self.passmanager.get_pass(GetVariablesPass).need_sent
    def need_rcvd(self):
        return self.passmanager.get_pass(GetVariablesPass).need_rcvd

    def run(self, modules, outfile):
        with smart_open(outfile) as out:
            gvpass = self.passmanager.get_pass(GetVariablesPass)
            for module in modules:
                self.defines = []
                self.tla_module = TlaModule(module.name, self.defines)

                names = set()
                for function in module.functions:
                    if function.scope.type == ScopeType.Process:
                        names.add(function.scope.gen_name("yield_ret_pc"))
                    if isinstance(function.ast_node, dast.Program):
                        continue
                    if isinstance(function.ast_node, dast.ClassStmt):
                        continue
                    if isinstance(function.ast_node, dast.Process):
                        continue
                    # skip main for now
                    if function.scope.type == ScopeType.Main:
                        continue
                    # add ret pc
                    if function.scope.type == ScopeType.General:
                        names.add(function.scope.gen_name("ret_pc"))

                    names |= gvpass.names[function]

                self.names += sorted(list(names))
                # only scan through
                self.defines.append(TlaExtendsStmt(["Integers", "Sequences", "FiniteSets", "TLC", "DistAlgoHelper"]))
                self.defines.append(TlaVariablesStmt(self.names))
                self.defines.append(send_action(self.need_sent()))
                for function in module.functions:
                    if isinstance(function.ast_node, dast.Program):
                        self.gen_program(function)
                    elif isinstance(function.ast_node, dast.ClassStmt):
                        self.gen_entry_function(function)
                    elif isinstance(function.ast_node, dast.Process):
                        self.gen_process(function, module)
                    elif function.scope.type == ScopeType.Main:
                        self.gen_main_function(function)

                out.write(self.tla_module.to_tla())

    def gen_program(self, function):
        if not CodeGen.is_simple_program(function):
            raise NotImplementedError()

    @staticmethod
    def is_simple_program(function : ir.Function):
        if len(function.basicblocks) != 2:
            return False
        for inst in function.basicblocks[0].ir:
            if isinstance(inst, ir.Call) and (isinstance(inst.func.ast_node, dast.ClassStmt) or isinstance(inst.func.ast_node, dast.Process)):
                continue
            elif isinstance(inst, ir.Assign) and inst.op == '=' and isinstance(inst.target, ir.IRName) and isinstance(inst.expr, ir.Function):
                continue
            return False

        return True

    @staticmethod
    def is_simple_process_class(process):
        return len(process.basicblocks) == 2 and \
            all(isinstance(i, ir.Assign) and \
                isinstance(i.expr, ir.Function) and \
                isinstance(i.target, ir.IRName) \
                for i in process.basicblocks[0].ir)

    def gen_process(self, process, module):
        assert(self.is_simple_process_class(process))

        for i in process.basicblocks[0].ir:
            if isinstance(i, ir.Assign) and i.expr.ast_node.name == "setup":
                pass # self.gen_init_function(i.expr)
        for i in process.basicblocks[0].ir:
            if isinstance(i, ir.Assign) and i.expr.scope.type == ScopeType.General:
                self.gen_entry_function(i.expr)

        message_handler = []

        for function in module.functions:
            if function.scope.parent is process.scope and function.scope.type == ScopeType.ReceiveHandler:
                message_handler.append(function)

        self.gen_message_handler(process, message_handler)

    def gen_main_function(self, func : ir.Function):
        pass

    def gen_init_function(self, func : ir.Function):
        self.translator.translate_function(func)

    def gen_entry_function(self, func : ir.Function):
        self.translator.translate_function(func)

    def gen_message_handler(self, process, func):
        self.translator.translate_message_handler(process, func)
