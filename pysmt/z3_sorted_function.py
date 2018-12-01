
from six.moves import cStringIO
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand
from pysmt.smtlib.script import smtlibscript_from_formula, evaluate_command
from pysmt.smtlib.parser import get_formula_strict, get_formula, SmtLibParser
from pysmt.shortcuts import Solver
smtlib_script = '\n'.join(['(declare-sort S0 0)', \
                           '(declare-sort S1 0)', \
                           '(declare-fun f (S0) S1)', \
                           '(declare-const s0 S0)', \
                           '(declare-const s1 S1)', \
                           '(declare-const n Int)', \
                           '(assert (= s1 (f s0)))', \
                           '(check-sat)', \
                           '(get-value ((f s0)))'
                           ])
parser = SmtLibParser()
outstream = cStringIO(smtlib_script)
script = parser.get_script(outstream)
solver = Solver("z3")
script.evaluate(solver)
exprs = []
for get_val_cmd in script.filter_by_command_name("get-value"):
    exprs.extend(get_val_cmd.args)
expr = exprs[0]
val = solver.get_value(expr)
print(val)
