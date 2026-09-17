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

`finite_checks.py` also calls `rro_reading.check_rro_reading()` after retention.
The `rro_reading` result block binds that helper's actual path, bytes, SHA256,
and observation companion §47. Its 14 `rro_reading_` count keys are disjoint
from all 38 preceding keys. The entry compares RNG state across the call without
restoring or reseeding it, and retains all preceding result subtrees and values.
Only the existing entry source digest is recomputed by its original writer.
Use the same command above; the helper has no CLI, owner import, RNG or writer.

The reading family uses RRO §§20.1–20.7 and 35.1's arithmetic successor and
block-cylinder clock. It recovers the **initial** positional prefix from strictly
increasing observations of one non-resettable trajectory. This is a deterministic,
noiseless task including both split endpoints; there is no position or phase oracle.
It differs from retention's endpoint transport and zero-dimensional convention:
here `G_0=1`, and depth zero returns an empty word without reading or a deadline.

The complete finite scope is depths 0–12 with all 985 `(depth, natural prefix)`
representatives, both oriented endpoints at each index 1–378, and every block
node of digit length less than 12. Integer square roots compute exact mechanical
floors and ceilings. Greedy natural words and the literal first-`00` successor
on exact eventually periodic states provide separate comparisons through all
380 indices 0–379, including the seam and every prescribed endpoint window.
Natural trajectories shared by several depths are checked once and reused.

The program checks actual-record compatibility against entire sampled cylinders,
both parity labels and child clock increments, adaptive and fixed decoding,
the forbidden words `11` and `000`, zero-path windows, all future endpoint labels
in the prescribed range, and deadline witnesses at every positive depth. It
enumerates all 4,247 fixed subsets at depths 0–5, compares hitting obligations
with transcript collisions on every prescribed state, and reconstructs omitted
centers for every successful subset. The obligation union includes `D_L+1`;
the exhaustive subset family itself ranges over positions `0..D_L`.

Counts measure concrete checks: `mechanical_successor_checks` counts one paired
orbit comparison per state/time; `forbidden_word_checks` counts two whole-word
exclusions per orbit; `candidate_set_checks` counts the parent and two child
compatibility comparisons per block. `clock_parity_checks` counts its two child
checks, `decoding_checks` counts one combined adaptive/fixed check per depth/state,
and `fixed_decoding_checks` counts one decode per successful subset/state.
`future_boundary_checks` counts endpoint pairs sharing the target prefix, including
all pairs at depth zero; `zero_window_checks` counts each positive-depth/window
obligation, and `seam_checks` counts one per positive depth. The remaining counts
enumerate the named representatives, endpoint states, blocks, subsets and witness.

The retained witness is the depth-five pair `01000` / `01010`: the zero-path
indices `0,1,3,6,11` miss both differences at `4,5` and read `00000` on each.
The zero initial state's own selected record is `01010`. Depths 5 and 12 have
adaptive/fixed/last-index triples `(5,7,11)` and `(12,189,375)`. These finite
checks supplement the paper proofs of the exact worst-case counts; they do not
prove the universal sequential lower bound or establish Lean status or novelty.
Read count and observation index are separate costs. Clock, representation,
computation, output and static program costs remain charged; no total optimum,
average-case, randomized, noisy or physical computation-deadline claim is made.
