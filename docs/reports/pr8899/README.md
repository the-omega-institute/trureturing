# PR8899: implementation coverage and execution record

## Current status, 2026-09-26

The original fourteen results are **not fully implemented or kernel-verified**.
This continuation adds four Lean proof-source candidates and four paired
Scribes to the thirteen earlier modules. Its 38 public theorem declarations
and 26 principal Scribe anchors are a source inventory, not verified results.

The first two continuation commits are `49a6fe8c609490e48bcb474302bce4333d8bf8a7`
and `d42d8b63d4df14822b6f74af2fc9b69fbfee0dc2`. The Gaussian source and executed
check report are delivered with this README. No existing frozen source, CI
configuration, proof gate, or admission criterion is changed.

The unique broader theory owner remains PR8891,
`docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md`. This directory is an
implementation report, not a new theory volume. PR8899 remains open and Draft.

## New proof-source content

### SpectralKlein

`D5/S3/Quantum/Divergence/SpectralKlein.lean` derives the Klein trace inequality
from two independently chosen actual spectral bases. Their squared overlap
weights are proved doubly stochastic from unitarity. Scalar log convexity
then gives `Re Tr(A(log A-log B)-A+B) >= 0` for positive semidefinite A and
positive definite B. Trace-one states give faithful-reference relative-entropy
nonnegativity. Singular A is allowed. Unsupported pairs and singular-reference
DPI/Pinsker are not inferred from this result.

### GibbsFreeEnergyStability

`D5/S3/Quantum/Thermal/GibbsFreeEnergyStability.lean` uses the existing
`GibbsVariationalIdentity` density, exponential, logarithm and entropy. Its
nonnegativity premise is discharged through `SpectralKlein`. The C-star/raw
matrix map is required to preserve CFC logs and the Euclidean operator norm.
The resulting pressure bound has constant one, the positive-temperature
physical equilibrium free-energy bound has constant one, and the uniform
nonequilibrium free-energy bound has constant two. The Hamiltonians need not
commute. Operator monotonicity of the matrix exponential is never assumed.

### GradedExponentialRemainder

`D5/S3/Observer/Linear/GradedExponentialRemainder.lean` uses the actual
Banach-algebra exponential power series, its infinite radius, and a uniform
remainder on the unit norm ball. If a continuous linear readout L annihilates
B^k for k<j, it derives, with a constructed constant K,

`norm(T^(-j) L(exp(T s B)) - s^j/j! L(B^j)) <= K T`

uniformly for s in [0,1] and T>0 with T norm(B)<1. The admissible radius
`1/(norm(B)+1)` is explicitly positive. A Taylor remainder, a Gramian envelope,
or the desired limiting coefficient is not supplied as an assumption.
The remaining projection assembly, integration, positivity and sorted
spectral comparisons are still needed for the full general Gramian theorem.

### GaussianObservationPrecision

`D5/S3/Observer/Linear/GaussianObservationPrecision.lean` constructs
`Q=beta I+tau M^T M`, its actual inverse and `m=Q^(-1) tau M^T y` for arbitrary
rectangular M, beta>0 and tau>=0. It derives positive definiteness, inverse
identities, completion of the actual prior/likelihood square, uniqueness of
the quadratic mode and a real-exponential factorization. An actual Mathlib
Gaussian probability measure is then constructed with mean m and covariance
Q^(-1), and those moments are proved. This candidate has not yet been identified
with the conditional law of the original observation experiment in Lean.
The mode proof is not claimed as Bayes optimality over all measurable estimators.

## Earlier source modules retained

The initial six-module source delivery is recorded in `initial_coverage.md`.
The subsequent seven candidates, all with paired Scribes, remain present:

- `CountableDiagonalGibbs`, `FiniteModeGibbsProduct` and `MetaplecticChirp`:
  actual l2 diagonal domains and Gibbs expansions, finite-mode occupation sums,
  and a genuine L2 chirp/shear implementation. Their global metaplectic,
  Schrodinger/occupation equivalence and basis-independent trace obligations
  are distinct and remain open.
- `UnitaryAverageLeakage` and `WeylPartialTraceLeakage`: constructed unitary
  averages, finite Weyl/partial-trace identification and corresponding
  operator-norm and square-sum identities. Full assembly with the paper's
  specific Hamiltonian decomposition remains to be completed and verified.
- `UnitaryDuhamelStability` and `MomentGramianStability`: actual unitary
  exponential interpolation/Duhamel estimates, and orthogonal moment
  compression with its exact discarded-Gramian and quadratic error identities.
  A general trace-norm channel theorem or concrete Legendre asymptotic is
  not claimed from those operator statements alone.

## Fourteen-result frontier

Every row remains open for kernel checking. The right column also lists
mathematical implementation obligations, beyond compilation.

| Original result | Relevant source progress | Remaining full-statement obligations |
| --- | --- | --- |
| 2.2 Energy, flow and Gibbs split | PredictiveEnergySplitting | Hidden orthonormal coordinate equivalence, Jacobian, Gaussian normalization/product law and concrete flow adapter. |
| 2.3 Classical recovery | ClassicalProductRecovery | Pointwise conditional-KL integral and the paper's specific Gaussian/flow correspondence. |
| 2.4 Canonical quantum split | Predictive Poisson nondegeneracy, MetaplecticChirp, CountableDiagonalGibbs, FiniteModeGibbsProduct | Full Darboux/Williamson and global metaplectic construction, Fourier/dilation composition and domain intertwiners, Schrodinger-to-occupation unitary and general trace-class adapter. |
| 3.2 Finite quantum leakage | WeylReconstruction, UnitaryAverageLeakage, WeylPartialTraceLeakage | Complete identification with the paper's H, H0, V and conditional expectation, then verification of the assembled full theorem. |
| 3.3 Dynamical/free-energy bounds | UnitaryDuhamelStability; new GibbsFreeEnergyStability | Trace-norm state/channel estimates, partial-trace contraction and full leakage-certificate adapter. |
| 3.4 Quantum thermal recovery | Existing support-aware divergence; new faithful-reference Klein nonnegativity | Supported singular-reference product logs, actual tensor recovery and entropy decomposition, equality case, measurement DPI and sharp quantum Pinsker. |
| 3.5 Two-qubit counterexample | Original written argument and earlier finite checks | Full Lean matrix dynamics, thermal state, exact norm certificate and opposite visible rotations. |
| 4.2 Hidden minimax risk | HiddenExperimentRisk | Complete physical instrument probability packaging and identification of the quantum entropy target range. |
| 4.3 Exact counting reduction | ExactPartitionCounting | Full quantum Hamiltonian/partition adapter and explicit polynomial-time/bit-complexity reduction. |
| 5.2 General graded Gramian | New actual graded exponential remainder | Construct and assemble all orthogonal derivative layers, integrate the uniform bound, prove positive limiting Gramian, ordered eigenvalue multiplicities and determinant asymptotic. |
| 5.3 Legendre moments | MomentGramianStability plus actual Taylor remainder | Actual normalized shifted Legendre L2 basis, concrete moment integrals and their full asymptotic connection. Pinned mathlib has polynomial Rodrigues/degree identities; those are not already the L2 orthogonality theorem. |
| 6.2 Gaussian information and risk | New GaussianObservationPrecision | Candidate-to-conditional-law identity, normalized densities, mutual information/log determinant, Bayes optimality for measurable estimators, mean conditional free energy and propagated risk. |
| 6.3 Noise thresholds | Written theorem; no new Lean threshold statement in this batch | Limits for arbitrary noise schedules and critical/noncritical exponents using the fully proved Gramian spectrum and actual posterior law. |
| 6.4 Oscillator comparison | OscillatorSensorJets and general derivative remainder | Complete exponential-trajectory determinant and information/risk limit transfer. |

## Tests actually executed for this four-module continuation

Run `python docs/reports/pr8899/continuation_checks.py`. It uses NumPy, SciPy
and mpmath and writes `continuation_checks.json` beside itself. It makes no
network requests or Git operations. The JSON records the exact versions,
seed, source SHA-256 hashes and counts. The present run passed **5,974 scoped
assertions**, consisting of repeated finite numerical cases plus source checks.
This is not a count of independent mathematical results.

The tests include 210 noncommuting spectral-pair cases (some with singular
first state), 140 Gibbs perturbation cases, actual matrix-exponential Taylor
checks, 560 normalized derivative-layer checks using 60-digit matrix
exponentials, and 252 rectangular Gaussian observation systems (including
zero/partially blind sensors). The Gaussian parameters are additionally
compared against independently calculated joint-covariance conditioning
formulas. A scalar shift tests sharpness of the pressure constant.

Counterexamples record why support inclusion, vanishing lower derivatives,
and positive prior precision cannot be dropped. Maximum finite identity
residual in this run was below `2e-13`. This diagnostic tolerance is not a
formal bound. The high-precision scaled-layer checks do not replace the
uniform analytic proof. Static checks find no placeholders or new axioms in
the four new Lean sources and resolve all 26 principal Scribe anchors.

## Verification limits and historical reports

No Lean or Lake executable is available in the local execution environment.
The four new files have **not been elaborated or kernel-checked**, and the
four Scribes have **not been compiled**. API, typeclass or tactic errors may
remain. Printed `#print axioms` commands are source instructions, not an
executed axiom audit. No freeze, admission, global formalization completion,
or independent mathematical review is claimed.

Earlier automatic runs failed before Lean at file/admission prerequisites;
this continuation does not change those gates or represent them as passing.
Historical initial reports and their checks remain byte-preserved as
`initial_coverage.md`, `research_legacy.py` and `initial_validation.json`.
Run `research.py` to adapt the old script to the current report directory;
its output is `initial_validation_rerun.json`, preserving the old record.
The earlier commit permalinks to `Evidence/PR8899` remain valid, but new
reports belong here. The single broader theory owner remains PR8891.
