# The replay gap

Written by `proofs/checker/scripts/check-replay.py --gap`. Each program's unproved
`check-eq` are assigned to one cause: that of its first event that fails, has no
witness in the stream, or gets no kernel step. A program's later failures can
follow from the merge that event did not apply.

31078 of 31099 `check-eq` proved; 21 not proved, in 9 programs.

| cause | programs | `check-eq` not proved | example |
| --- | --- | --- | --- |
| no kernel steps: m line | 4 | 13 | `egraph/tests/egg/conform-flatten/f2_0159.egg` |
| law: arguments differ | 1 | 3 | `egraph/tests/egg/flatten_fold_binary_pattern.egg` |
| definition: unreadable | 3 | 3 | `egraph/tests/egg/mult_rhs_splice_rest.egg` |
| goal: its terms differ | 1 | 2 | `egraph/tests/egg/flatten_fold_spine.egg` |
| total | 9 | 21 | |

## Programs the reader does not read

Their `check-eq` are not in the total above.

| reason | programs | example |
| --- | --- | --- |
| count N above N | 5 | `doc/book/examples/cost-models/25-exact.egg` |
