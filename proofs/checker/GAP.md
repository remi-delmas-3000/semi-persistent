# The replay gap

Written by `proofs/checker/scripts/check-replay.py --gap`. Each program's unproved
`check-eq` are assigned to one cause: that of its first event that fails, has no
witness in the stream, or gets no kernel step. A program's later failures can
follow from the merge that event did not apply.

29682 of 29808 `check-eq` proved; 126 not proved, in 52 programs.

| cause | programs | `check-eq` not proved | example |
| --- | --- | --- | --- |
| rule: matched node differs | 3 | 31 | `egraph/tests/egg/conform-flatten/f2_0169.egg` |
| no witness: rewrite:untraced-firing | 20 | 27 | `egraph/tests/egg/collection_rules.egg` |
| rule: unbound rest variable | 2 | 21 | `egraph/tests/egg/rhs_comprehensions.egg` |
| no witness: Cancellative | 2 | 11 | `egraph/tests/egg/cancel_lattice.egg` |
| no witness: rewrite:outside-a-firing | 5 | 11 | `doc/book/examples/05-seq-except.egg` |
| no kernel steps: w line | 2 | 4 | `egraph/tests/egg/atomic_bit_inverse_after_splice.egg` |
| rule: built node differs | 3 | 4 | `egraph/tests/egg/seq_flatten_rhs_nesting.egg` |
| definition: unreadable | 4 | 4 | `egraph/tests/egg/seq_rhs_too_wide.egg` |
| no witness: ACInterReduction | 2 | 2 | `egraph/tests/egg/a_interreduction_lazy.egg` |
| no kernel steps: i line | 2 | 2 | `egraph/tests/egg/group_inverse_virtual_sum.egg` |
| rule: line for another application | 2 | 2 | `egraph/tests/egg/birewrite_both_directions.egg` |
| no kernel steps: m line | 1 | 2 | `egraph/tests/egg/rhs_empty_application_identity.egg` |
| unread rule: a multiplicity constraint other than >= | 1 | 2 | `egraph/tests/egg/rhs_mult_expr.egg` |
| goal: its terms differ | 1 | 1 | `egraph/tests/egg/bench/until.native.egg` |
| no kernel steps: p line | 1 | 1 | `egraph/tests/egg/conform-cc-cert/cs1_0043.egg` |
| rule: no line for a literal | 1 | 1 | `doc/book/examples/05-rewrite-rules.egg` |
| total | 52 | 126 | |

## Programs the reader does not read

Their `check-eq` are not in the total above.

| reason | programs | example |
| --- | --- | --- |
| an operator takes N arguments | 102 | `doc/book/examples/10-directional-flattening.egg` |
| push, pop and include are not supported | 8 | `doc/book/examples/07-push-pop.egg` |
| count N above N | 5 | `doc/book/examples/cost-models/25-exact.egg` |
| sort iN where RBig is expected | 2 | `egraph/tests/egg/bench/herbie.native.egg` |
