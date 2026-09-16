# New reports needed after upgrading an old summary

`observer_delay.py` supplies exact finite comparisons for
[observation companion §45](../../develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md).
It reuses `rational_observer` for construction, ordinary verification, rational
updates and rounding, and `observer_capture` for strict margins, capture
thresholds and the independent unnormalized hidden-mass reference.
Python 3.10 or later and the standard library suffice. For example:

```sh
python3.12 -B docs/reports/contextual-spacetime-ml/observer_delay.py checks --out docs/reports/contextual-spacetime-ml/observer_delay_results.json
```

The old observer is fixed at `p=r=1/4`, `eps_old=1/16`, `m_old=28`, with
emit-then-flip order and lower-integer ties. At upgrade, only the old label and
old history length carry information about the past. Other memory is newly
initialized from these, the rational target and fixed public inputs. Internal
computation is finite, charged, and receives no hidden reports; the source
waits. The objective counts new reports until a deterministic stop and compares
the output with the **current** next-zero probability on every old history and
every continuation.

The retained results check:

- The same-length histories `0000` and `1000` both yield descriptor `(24,4)`.
  Their actual constructor paths, independent hidden masses, word probabilities,
  posteriors and next-zero predictions give an exact prediction gap `1/253`.
- All 511 common suffixes of lengths zero through eight. Each exact prediction
  gap is at least `6^-n/253`, and each conditional suffix probability is at least
  `4^-n` under both old histories. Per-length minima and witnesses are retained.
- Integer threshold equality and adjacent cases `1/506`, `1/507`, `1/3036`,
  `1/3037`, plus zero-report tracker, upper-bound equality and unreduced-rational
  cases. `report_bounds(Q(...))` computes `L`, `U`, `V` for
  `0 < eps <= 1/16`, using three integer loops and no floating-point logarithms.
- The existing ordinary certificate for the old grid and supplied-margin
  certificate for the target grid. The capture helper tests nine-report failure
  and ten-report success of its sufficient inequality. The conservative
  eleven-report posterior bound is strictly below `eps/9 <= mu`.
- The exact center tracker on all 29 old intervals, both endpoints, and all 64
  six-report words: 3,712 terminal comparisons. Actual trajectories use the
  independent hidden-mass recurrence; the tracker uses the existing scalar
  rational update from its old center.
- Named rejection of invalid threshold targets and of a corrupted ordinary
  readout certificate. The corrupted readout must be rejected with exactly
  `["accuracy:14:upper"]`. After both assertions pass, the successful
  negative-test summary saves the verifier's actual diagnostic list in
  `expected_readout_rejection`. The raw verifier response has `valid: false`
  and a `failures` list; that object is not embedded in the successful summary.
  Unexpected acceptance or different diagnostics raises before writing a
  report and exits nonzero. Successful verifier objects omit `failures`.

For `eps=1/1024`, the quantities have distinct meanings:

| Quantity | Reports | Meaning |
| --- | ---: | --- |
| `L` | 1 | Necessary worst-case stopping lower bound |
| Capture inequality | 10 | First successful §44 sufficient inequality for grid membership |
| `U` | 11 | Conservative uniform strict-capture upper bound |
| `V` | 6 | Sufficient current-prediction bound for an exact rational center tracker |

Here `m=526`, `E=793/1578`, and `mu=4/16641`. None of the four counts claims an
optimal constant or minimum actual capture time. The stopping optimum at this
target lies between 1 and 6 by the paper bounds.

The all-word lower bound is the paper argument using the persistent gap and the
scalar half-fiber inequality of ML §39.3. Determinism makes the two histories
share stopping decisions and outputs after a common prefix, even with arbitrary
new work or memory. Only finite prefixes need positive probability. The upper
bound directly uses Quantum §153's logit contraction and §44's whole-interval
inward margin, including clipped endpoints. Its exact reference is proof-only;
no contraction is asserted for rounded transitions.

The tracker comparison instead keeps a charged exact rational register.
Numerator and denominator lengths and operation costs can grow. It supplies a
point prediction, without certifying membership in the finite target grid.
These paper arguments give `Theta(log(1/eps))` for worst-case **new-report**
delay; the finite comparisons do not prove that asymptotic claim. There is no
Lean certification, expected-risk, high-probability, wall-clock, bit, time or
memory optimality claim.

The command writes results only after every check succeeds. An unexpected
failure emits `valid: false` with a named error on stderr and exits nonzero;
a pre-existing output file does not certify a failed run. `--out` resolves from
the invoking directory. Predecessor programs and results retain their separate
contracts.
