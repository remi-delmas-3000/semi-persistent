# The replay gap

Written by `proofs/checker/scripts/check-replay.py --gap`. Each program's unproved
`check-eq` are assigned to one cause: that of its first event that fails, has no
witness in the stream, or gets no kernel step. A program's later failures can
follow from the merge that event did not apply.

29781 of 29808 `check-eq` proved; 27 not proved, in 18 programs.

| cause | programs | `check-eq` not proved | example |
| --- | --- | --- | --- |
| sequence rule: binding read, not checked | 6 | 10 | `egraph/tests/egg/collection_rules.egg` |
| rule: argument differs | 2 | 3 | `doc/book/examples/05-rhs-comprehensions.egg` |
| definition: unreadable | 3 | 3 | `egraph/tests/egg/mult_rhs_splice_rest.egg` |
| rule: unbound rest variable | 1 | 2 | `egraph/tests/egg/rhs_comprehensions.egg` |
| no kernel steps: m line | 1 | 2 | `egraph/tests/egg/rhs_empty_application_identity.egg` |
| unread rule: a multiplicity constraint other than >= | 1 | 2 | `egraph/tests/egg/rhs_mult_expr.egg` |
| rule: built node differs | 1 | 2 | `egraph/tests/egg/seq_flatten_rhs_nesting.egg` |
| no kernel steps: i line | 1 | 1 | `egraph/tests/egg/ac_minmono_cc1_0897.egg` |
| goal: its terms differ | 1 | 1 | `egraph/tests/egg/bench/until.native.egg` |
| no kernel steps: p line | 1 | 1 | `egraph/tests/egg/conform-cc-cert/cs1_0043.egg` |
| total | 18 | 27 | |

## Programs the reader does not read

Their `check-eq` are not in the total above.

| reason | programs | example |
| --- | --- | --- |
| an operator takes N arguments | 102 | `doc/book/examples/10-directional-flattening.egg` |
| push, pop and include are not supported | 8 | `doc/book/examples/07-push-pop.egg` |
| count N above N | 5 | `doc/book/examples/cost-models/25-exact.egg` |
| sort iN where RBig is expected | 2 | `egraph/tests/egg/bench/herbie.native.egg` |
