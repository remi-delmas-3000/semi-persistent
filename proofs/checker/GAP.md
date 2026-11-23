# The replay gap

Written by `proofs/checker/scripts/check-replay.py --gap`. Each program's unproved
`check-eq` are assigned to one cause: that of its first event that fails, has no
witness in the stream, or gets no kernel step. A program's later failures can
follow from the merge that event did not apply.

29876 of 29879 `check-eq` proved; 3 not proved, in 3 programs.

| cause | programs | `check-eq` not proved | example |
| --- | --- | --- | --- |
| definition: unreadable | 3 | 3 | `egraph/tests/egg/mult_rhs_splice_rest.egg` |
| total | 3 | 3 | |

## Programs the reader does not read

Their `check-eq` are not in the total above.

| reason | programs | example |
| --- | --- | --- |
| an operator takes N arguments | 102 | `doc/book/examples/10-directional-flattening.egg` |
| count N above N | 5 | `doc/book/examples/cost-models/25-exact.egg` |
