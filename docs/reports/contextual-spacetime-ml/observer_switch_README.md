# Online precision switch

`observer_switch.py` implements the fixed switch and exact experiments for
[ML observation companion §43](../../develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md).
It imports the delivered `rational_observer` constructor and verifier. Python
3.10 or later and its standard library suffice; no installation is needed.

From the repository root:

```sh
python3 -B docs/reports/contextual-spacetime-ml/observer_switch.py checks --out docs/reports/contextual-spacetime-ml/observer_switch_results.json
printf '0 1 0 0 0 0 0 0\n' | python3 -B docs/reports/contextual-spacetime-ml/observer_switch.py stream --old-label 23
```

The executable interface fixes `p=r=1/4`, the old ML main-volume §41 observer
at tolerance `1/16` (`m=28`), and the new grid at target `1/1024` (`m=526`). The old label
must come from a valid run of that old observer. The interface validates its
range, but an integer cannot establish the historical precondition. It accepts
no pre-switch clock, replay archive, or arbitrary target threshold.

Reset chooses the nearest new center to the old center, with lower-index ties,
and resets the counter to zero. Each report updates the new label and saturates
the counter at eight. Each JSON line contains `index`, `counter`, `certified`,
and the next-zero `prediction` as a numerator/positive-denominator string pair.
There is one line at reset and one after every report; post-report predictions
use the updated label. ASCII whitespace is ignored; other input is rejected.
`certified: false` carries no new-target guarantee. Certification concerns
prediction error, not membership in the new label's ML main-volume §41 interval.
A later switch needs its own valid initialization bound.

The mathematical state has 527 label values and nine counter values: ten label
bits plus four separately stored counter bits. The 4743 nominal pairs fit in
13 packed bits. Neither count is a reachable-state or minimum-memory claim.
Static tables, reset mapping, scratch, and output are additional costs; Python
objects and decimal JSON are not realizations of those abstract bit counts.

The retained exact results serve these comparisons:

- Two-component unnormalised `Fraction` recursion verifies the positive
  probabilities, posteriors, and displayed labels for `100`, `0100`, and `00`.
  The `m=28` trace of `0100` ends at 23. The two observation kernels are
  incomparable on actual histories.
- The shared old label 23 gives an immediate prediction lower bound `1/456`.
  Reset to label 432 predicts `1221/2104`; the errors on `00` and `0100` are
  `19/6312` and `55/39976`, both above `1/1024`.
- All 29 resets are compared with an independent full-grid nearest-point scan.
  Old labels 7 and 21 exercise both exact lower-index ties. Checks also cover
  counter reset/saturation, the stream certification boundary, invalid inputs,
  and reading the updated label.
- Both endpoints of each of the 29 old certificate intervals are propagated
  through every eight-report word: 14,848 endpoint/word cases. All nine prefix
  lengths are checked, with repetition across words. Their maximum final error
  is `14515/36216152`; the JSON retains an endpoint and word attaining it.
  These intervals may include unreachable points, so this is not the optimum
  over actual histories and does not determine the minimum delay.

The companion §43 proof, using ML main-volume §21.2 and Quantum §§153/155,
quantifies every old history and every future word at every length. Its bound is
`(8 + 785 * 2^(-n)) / 12624`, with strict residual `1/1578 < 1/1024` and
eight-step bound `2833/3231744 < 1/1024`. The finite experiment cross-checks
these constants; it does not prove the unlimited quantifiers. For the separate
`1/32` comparison the unchanged old observer already has bound `3/224`.
No actual-error ordering between the old and `m=32` observers is asserted.

Successful checks exit zero and emit `valid: true`, without an empty failures
field. Any unexpected check failure exits nonzero and reports its error; no
success results file is written by a failed check run. These are exact rational
experiments and paper mathematics, with no Lean certification or priority claim.
