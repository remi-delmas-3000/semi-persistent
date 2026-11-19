# The replay gap

Written by `proofs/checker/scripts/check-replay.py --gap`. Each program's unproved
`check-eq` are assigned to one cause: that of its first event that fails, has no
witness in the stream, or gets no kernel step. A program's later failures can
follow from the merge that event did not apply.

26358 of 29808 `check-eq` proved; 3450 not proved, in 301 programs.

| cause | programs | `check-eq` not proved | example |
| --- | --- | --- | --- |
| no witness: rewrite:multiset-rest-variable | 122 | 1869 | `egraph/tests/egg/conform/c1_0059.egg` |
| no witness: rewrite:sequence-rest-variable | 67 | 1280 | `egraph/tests/egg/conform-flatten/f2_0050.egg` |
| unread rule: a primitive or undeclared operator | 22 | 128 | `egraph/tests/egg/bignum_all_ops.egg` |
| unread rule: a multiplicity | 25 | 53 | `egraph/tests/egg/conform-rounds/r1_0114.egg` |
| no witness: rewrite:multiplicity-variable | 11 | 36 | `egraph/tests/egg/conform-rounds/r1_0181.egg` |
| no witness: rewrite:untraced-firing | 20 | 27 | `egraph/tests/egg/collection_rules.egg` |
| no witness: rewrite:primitive-guard | 7 | 11 | `egraph/tests/egg/bench/typecheck.rules.egg` |
| no witness: Cancellative | 2 | 11 | `egraph/tests/egg/cancel_lattice.egg` |
| rule: matched node differs | 2 | 6 | `egraph/tests/egg/flatten_regroup_laws_drop_need.egg` |
| no kernel steps: w line | 2 | 4 | `egraph/tests/egg/atomic_bit_inverse_after_splice.egg` |
| rule: built node differs | 3 | 4 | `egraph/tests/egg/seq_flatten_rhs_nesting.egg` |
| no witness: rewrite:outside-a-firing | 2 | 4 | `doc/book/examples/05-seq-except.egg` |
| rule: line for another application | 3 | 3 | `egraph/tests/egg/birewrite_both_directions.egg` |
| no kernel steps: m line | 2 | 3 | `egraph/tests/egg/rhs_empty_application_identity.egg` |
| definition: unreadable | 3 | 3 | `egraph/tests/egg/mult_rhs_splice_rest.egg` |
| no witness: ACInterReduction | 2 | 2 | `egraph/tests/egg/a_interreduction_lazy.egg` |
| no kernel steps: i line | 2 | 2 | `egraph/tests/egg/group_inverse_virtual_sum.egg` |
| goal: its terms differ | 2 | 2 | `egraph/tests/egg/bench/math-add-ac.rules.egg` |
| no kernel steps: p line | 1 | 1 | `egraph/tests/egg/conform-cc-cert/cs1_0043.egg` |
| rule: no line for a literal | 1 | 1 | `doc/book/examples/05-rewrite-rules.egg` |
| total | 301 | 3450 | |

## Programs the reader does not read

Their `check-eq` are not in the total above.

| reason | programs | example |
| --- | --- | --- |
| an operator takes N arguments | 102 | `doc/book/examples/10-directional-flattening.egg` |
| push, pop and include are not supported | 8 | `doc/book/examples/07-push-pop.egg` |
| count N above N | 5 | `doc/book/examples/cost-models/25-exact.egg` |
| sort iN where RBig is expected | 2 | `egraph/tests/egg/bench/herbie.native.egg` |
