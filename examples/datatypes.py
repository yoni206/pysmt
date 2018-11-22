from six.moves import cStringIO # Py2-Py3 Compatibility
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import Solver
DEMO_SMTLIB_1=\
"""
;like the smtlib 2.6 doc.
(declare-datatypes ((DNat 0) (Nat 0)) (((dnat (data Nat)))
                                       ((succ (pred DNat)) (zero)
)))
(declare-sort A 0)
(declare-fun a () A)
(declare-fun d () Nat)
(assert (= d d))
(check-sat)
"""

DEMO_SMTLIB_2=\
"""
(declare-datatypes ( (Tree 1) (TreeList 1) ) (
(par ( X ) ( ( node ( value X ) ( children ( TreeList X )) )))
(par ( Y ) ( ( empty ) ( insert ( head ( Tree Y )) ( tail ( TreeList Y ))) ))
))
"""

DEMO_SMTLIB_3=\
"""
(declare-fun b () Int)
(assert (= b b))
(check-sat)
(get-value (d))
"""

parser = SmtLibParser()
script = parser.get_script(cStringIO(DEMO_SMTLIB_1))
f = script.get_last_formula()
s = Solver("generic_cvc4")
s.add_assertion(f)
res = s.solve()
s.print_model()
print(res)
#script = parser.get_script(cStringIO(DEMO_SMTLIB_2))
