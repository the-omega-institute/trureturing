# Rational observer certificates

`rational_observer.py` constructs and checks the finite interval certificates in
[ML §41](../../develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md) and the
table-free integer evaluator in ML §42.
It uses only the Python standard library. The model emits from the old hidden
bit and then flips it; the initial hidden bit is uniform. The output predicts
the **next zero report** after the supplied history.

From the repository root:

```sh
python3 docs/reports/contextual-spacetime-ml/rational_observer.py generate --p 1/4 --r 1/4 --eps 1/16 --out docs/reports/contextual-spacetime-ml/rational_observer_certificate.json
python3 docs/reports/contextual-spacetime-ml/rational_observer.py verify docs/reports/contextual-spacetime-ml/rational_observer_certificate.json
python3 docs/reports/contextual-spacetime-ml/rational_observer.py checks --out docs/reports/contextual-spacetime-ml/rational_observer_results.json
python3 docs/reports/contextual-spacetime-ml/rational_observer.py integer-checks --out docs/reports/contextual-spacetime-ml/integer_observer_results.json
printf '0 1 0\n' | python3 docs/reports/contextual-spacetime-ml/rational_observer.py stream --p 1/4 --r 1/4 --eps 1/16
```

`integer-checks` compares every grid readout and both successors against an
independent `fractions.Fraction` reference, the retained 29-state table, reduced
and unreduced inputs, the `k=1` saturation equality, both exact lower-index
ties, parameter boundaries, a 10,000-report stream, and the pinned full-interval
quotient counterexample. Its result is the registered
`integer_observer_results.json` file.

`stream` consumes one ASCII report bit at a time from standard input (whitespace
is ignored). It emits one compact JSON line for the empty history and one after
each report: `{"index": j, "prediction": ["numerator", "denominator"]}`.
The prediction is the exact current `V0(j)/(A*B*m)` pair; no old transition
denominator or report history is emitted or retained. The decimal JSON encoding
is a transport format; ML §42's `O(b)` space and `O(b²)` per-report bound is for
the explicitly charged binary fixed-buffer transducer, not for Python object
allocation, JSON bytes, or host timing.

The retained certificate has 29 states, initial index 14, and zero-report target
21 at that index. Complete verification performs 321 scalar comparisons:
`11 * 29 + 2`. Exit code 0 means acceptance; exit code 1 means rejection or
malformed input. A rejected certificate need not disprove accuracy on reachable
histories. Generation uses the uniform grid even when a smaller observer exists.

Successful verification outputs have `valid: true` and omit `failures`; state,
comparison, and integer/index bit counts remain present. Failed scalar checks
have `valid: false` and a nonempty `failures` list containing every failed check
label from the evaluated comparisons. The retained `checks` summaries use the
same sparse success shape and keep the exact expected corruption labels in
`corrupt_rejections`. An unexpected check failure raises before a report is
written and exits nonzero.

The JSON schema has `schema`, `parameters`, `initial`, and `states`. Each state
has `lo`, `hi`, `readout`, and two `targets` in report order 0, 1. Rational values
are pairs of decimal strings with positive denominators, such as `["1", "4"]`;
unreduced pairs are allowed. Decimal fractions, JSON floating point numbers,
Boolean indices, duplicate keys, and unknown fields are rejected. The verifier
uses the supplied endpoints, readouts, and targets directly and does not call
the constructor. Successful range checks account for `5N` comparisons; initial,
successor, and accuracy checks account for `6N+2`. Invalid ranges stop evaluation
before a Bayesian denominator could leave its declared positive domain.

The deterministic `checks` command includes 38 parameter triples with 3 to 5513
states, small mixing, the minimum grid size `m=2`, and tolerances on either side
of the `k=1` boundary. It rejects the three representative corruptions (target
21 changed to 0, readout at state 14 changed to 0, initial index changed to 0).
It accepts a changed readout `501/1000` at state 14 and a nongrid one-state
certificate. It also rejects malformed rational encodings. A separate
`fractions.Fraction` two-component Bayesian calculation checks all words of
length at most 8 for three parameter triples (1533 words including empty).
The ordering discriminator is `7/12` for emit-then-flip and `2/3` for
flip-then-emit. Finite replay is a cross-check; the interval induction in §41
supplies the all-history guarantee.

Generation and verification use unreduced integer pairs and fixed-depth
expressions for each row; only the bounded cross-check uses `Fraction`.
Nearest-index construction uses `divmod`, not a grid scan. The mathematical
bit costs in §41 concern binary, fixed-size records and explicitly charged
random access. This JSON encoding uses decimal strings, and Python lists,
objects, allocation, and integer algorithms are host details, so the JSON byte
count or Python timing is not the abstract cost. A verifier of arbitrary input
must use the actual operand and index lengths. The five-bit persistent label
of the sample is separate from its static table, certificate, and scratch space.

## Unknown fixed parameter

`unknown-checks` is the bounded paired-model consumer for
[observation companion §48](../../develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md).
It fixes `r=1/4`, keeps separate globally fixed `p=1/4` and `p=1/3` filters,
and gives both the same complete report word. The hidden-bit prior `1/2` is
not a prior over models. Each target is its own model's conditional probability
of the next zero report.

```sh
env -u PYTHONOPTIMIZE python3 -B docs/reports/contextual-spacetime-ml/rational_observer.py unknown-checks --out docs/reports/contextual-spacetime-ml/rational_observer_unknown_results.json
```

The check reuses `Q`, `update`, `output`, and the JSON writer. Separate
unnormalized emission-then-flip masses independently check both scalar filters,
readouts, and positive support on all 511 words through length 8 and the 65 zero
prefixes of lengths 0 through 64 (567 distinct paired histories). The result
retains exact samples, the rational invariant endpoint `59/92 < 9/14`, the
third iterate `19/28`, readout `33/56`, the `1/48` barrier, unequal two-report
probabilities `9/32` and `19/72`, and half-gaps `5/228`, `935/41328`, `145/6424`.
Rational square comparisons enclose the limiting expression
`(3*sqrt(3)-sqrt(17))/48`; no floating-point value is used as a premise.

This finite check does not prove the all-length invariant, convergence, or the
deterministic full-history and stopping statements. Those follow from the
recurrences and proofs in §48. Stopping there begins after `000` and requires
finite completion on every infinite continuation; the result does not exclude
almost-sure learning, average-risk bounds, or high-probability guarantees.
The limit is specific to the zero-word witness family, not a sharp global
minimax value. The command requires assertions enabled, emits no success result
if a check fails, and retains the failing parameter/history in comparison errors.
