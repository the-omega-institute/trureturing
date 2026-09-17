# Exact finite ML checks

`finite_checks.py` is the standard-library entry point for the finite ML experiments.
Run a fresh Python 3.9+ process from the repository root, with assertions enabled:

```sh
env -u PYTHONOPTIMIZE python3 -B docs/reports/contextual-spacetime-ml/finite_checks.py --output docs/reports/contextual-spacetime-ml/finite_results.json
```

The command writes the result and prints the same JSON. An assertion or I/O error
exits nonzero; an existing result file does not establish that a later run passed.
Do not use `-O` or `-OO`. The top-level source digest binds `finite_checks.py`;
the `rro_retention` block separately binds the helper's actual bytes, byte count,
observation companion §46, and cited RRO geometry. The original main-volume
`theory` field, seed, check order, 23 count entries and mathematical subtrees
retain their existing meanings. The new consumer does not use the RNG.

`rro_retention.py` checks the prescribed marginal-histogram task of
[observation companion §46](../../develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md).
Its rational cycle-incidence model assumes RRO §§34.0–34.3: the boundary set,
side orientation, residual-coordinate product, and full-cycle constant kernel.
It does not derive RRO geometry or implement a general digit codec. Each depth's
off-boundary endpoint pair shares a conventional arc; these abstract inputs do
not assert a nested cylinder geometry. Four actual endpoint fixtures instead use
RRO §20.2's oriented words and §§25.9/25.12/28.7's deterministic endpoint kernel.

The recorded run checks all 84 schedules with horizons 0–2 and depths 0–3,
with maximum initial residual dimension 5, in two cycle orders each. One order
uses natural labels; the other uses `(2,1)`, `(3,1,2)`, `(3,1,4,2,5)` at sizes
2, 3, 5. Exact elimination gives 168 rank checks, including eight cases of zero
dimension. The 84 schedules split into 68 with future residual visibility,
12 with only current visibility, and four with none. The run also checks:

- Six cycle/order inputs and every single-edge deletion, including cancellation.
- 540 witnesses, one per insufficient prefix per schedule/order, and 336 tail columns.
- 14,168 probability-box grid points and matching decodes; 2,340 binary vertices
  and 54,096 ordered binary-pair kernel comparisons.
- Eight endpoint/sign fixtures and nine actual two-atom probability-box points.
- The `(0,0,2)` fixed-window loss and the `(1,0,1)` actual joint-record counterexample.

Matrix evaluation, repeated residual transport/scattering, direct nonnegative
endpoint-mass histograms, rational elimination and output-class enumeration
provide distinct finite contracts. The actual `(1,1)` example has next-marginal
probability TV `1/2` and signed variation `1`; the joint example has probability
TV `1` and signed variation `2`. The latter follows the actual endpoint paths,
not a freely selected coupling of marginals.

These checks supplement the paper proofs; they prove no universal theorem or
Lean status. The full phase measure remains stored and charged. Rank bounds
linear real encoders with arbitrary deterministic decoders on the stated box
or in the worst case; binary fixed-width labels are a separate cost. Initial
residuals require a charged clock or moving window. Joint/adaptive observation,
unplanned precision, unrestricted real encodings and total-memory optimality
are outside the marginal task. Runtime measurements are not correctness tests.
