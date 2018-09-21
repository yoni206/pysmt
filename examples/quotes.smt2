from six.moves import cStringIO # Py2-Py3 Compatibility
from pysmt.smtlib.parser import SmtLibParser


DEMO_SMTLIB=\
"""
(set-logic QF_LIA)
(declare-fun p () Int)
(declare-fun |q q| () Int)
(assert (= p |q q|))
(check-sat)
"""
parser = SmtLibParser()

script = parser.get_script(cStringIO(DEMO_SMTLIB))

f = script.get_last_formula()
print(f)

print("*"*50)

buf_out = cStringIO()
script.serialize(buf_out, daggify=False)
print(buf_out.getvalue())
