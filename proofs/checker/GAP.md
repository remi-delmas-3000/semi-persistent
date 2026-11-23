# The replay gap

Written by `proofs/checker/scripts/check-replay.py --gap`. Each program's unproved
`check-eq` are assigned to one cause: that of its first event that fails, has no
witness in the stream, or gets no kernel step. A program's later failures can
follow from the merge that event did not apply.

29727 of 29808 `check-eq` proved; 81 not proved, in 44 programs.

| cause | programs | `check-eq` not proved | example |
| --- | --- | --- | --- |
| no witness: rewrite:untraced-firing | 20 | 27 | `egraph/tests/egg/collection_rules.egg` |
| rule: unbound rest variable | 2 | 21 | `egraph/tests/egg/rhs_comprehensions.egg` |
| no witness: rewrite:outside-a-firing | 5 | 11 | `doc/book/examples/05-seq-except.egg` |
| no kernel steps: w line | 2 | 4 | `egraph/tests/egg/atomic_bit_inverse_after_splice.egg` |
| definition: unreadable | 4 | 4 | `egraph/tests/egg/seq_rhs_too_wide.egg` |
| rule: built node differs | 2 | 3 | `egraph/tests/egg/seq_flatten_rhs_nesting.egg` |
| no witness: ACInterReduction | 2 | 2 | `egraph/tests/egg/a_interreduction_lazy.egg` |
| no kernel steps: i line | 2 | 2 | `egraph/tests/egg/group_inverse_virtual_sum.egg` |
| no kernel steps: m line | 1 | 2 | `egraph/tests/egg/rhs_empty_application_identity.egg` |
| unread rule: a multiplicity constraint other than >= | 1 | 2 | `egraph/tests/egg/rhs_mult_expr.egg` |
| goal: its terms differ | 1 | 1 | `egraph/tests/egg/bench/until.native.egg` |
| rule: argument differs | 1 | 1 | `egraph/tests/egg/bench/until.rules.egg` |
| no kernel steps: p line | 1 | 1 | `egraph/tests/egg/conform-cc-cert/cs1_0043.egg` |
| total | 44 | 81 | |

## Programs the reader does not read

Their `check-eq` are not in the total above.

| reason | programs | example |
| --- | --- | --- |
| an operator takes N arguments | 102 | `doc/book/examples/10-directional-flattening.egg` |
| push, pop and include are not supported | 8 | `doc/book/examples/07-push-pop.egg` |
| count N above N | 5 | `doc/book/examples/cost-models/25-exact.egg` |
| sort iN where RBig is expected | 2 | `egraph/tests/egg/bench/herbie.native.egg` |
