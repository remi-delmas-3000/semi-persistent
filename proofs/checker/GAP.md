# The replay gap

Written by `proofs/checker/scripts/check-replay.py --gap`. Each program's unproved
`check-eq` are assigned to one cause: that of its first event that fails, has no
witness in the stream, or gets no kernel step. A program's later failures can
follow from the merge that event did not apply.

31101 of 31101 `check-eq` proved; 0 not proved, in 0 programs.

| cause | programs | `check-eq` not proved | example |
| --- | --- | --- | --- |
| total | 0 | 0 | |

## Programs the reader does not read

Their `check-eq` are not in the total above.

| reason | programs | example |
| --- | --- | --- |
