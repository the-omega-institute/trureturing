# Rational observer certificates

`rational_observer.py` constructs and checks the finite interval certificates in
[ML §41](../../develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md).
It uses only the Python standard library. The model emits from the old hidden
bit and then flips it; the initial hidden bit is uniform. The output predicts
the **next zero report** after the supplied history.

From the repository root:

```sh
python3 docs/reports/contextual-spacetime-ml/rational_observer.py generate --p 1/4 --r 1/4 --eps 1/16 --out docs/reports/contextual-spacetime-ml/rational_observer_certificate.json
python3 docs/reports/contextual-spacetime-ml/rational_observer.py verify docs/reports/contextual-spacetime-ml/rational_observer_certificate.json
python3 docs/reports/contextual-spacetime-ml/rational_observer.py checks --out docs/reports/contextual-spacetime-ml/rational_observer_results.json
```

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
