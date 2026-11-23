# The replay gap

Written by `proofs/checker/scripts/check-replay.py --gap`. Each program's unproved
`check-eq` are assigned to one cause: that of its first event that fails, has no
witness in the stream, or gets no kernel step. A program's later failures can
follow from the merge that event did not apply.

31097 of 31099 `check-eq` proved; 2 not proved, in 2 programs.

| cause | programs | `check-eq` not proved | example |
| --- | --- | --- | --- |
| law: not an application | 1 | 1 | `egraph/tests/egg/mult_build_flatten_product.egg` |
| rule: unreadable | 1 | 1 | `egraph/tests/egg/mult_rhs_splice_rest.egg` |
| total | 2 | 2 | |

## Programs the reader does not read

Their `check-eq` are not in the total above.

| reason | programs | example |
| --- | --- | --- |
| count N above N | 5 | `doc/book/examples/cost-models/25-exact.egg` |
