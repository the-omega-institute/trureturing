# PR8899: implementation coverage and execution record

## Current continuation: conditional Gaussian laws and Bayes risk

The original fourteen results are **not fully implemented or kernel-verified**.
This continuation adds three Lean proof-source candidates and three paired
Scribes: 46 public theorem-source declarations and 32 principal Scribe anchors.
These counts are inventories, not a count of verified mathematical results.

The conditional-law sources were pushed first in
`6f8bff46ffc727e095cb0152ec10aa0e2b3477c4`. The following risk source, its Scribe,
this updated report and the executed check program/result complete this batch.
The starting revision was `18dcb45bb6c8448ed7c40ba9c7df10ff21a78db3`.
No existing frozen Lean source, CI configuration, proof gate or admission
criterion is changed. The broader unique theory owner remains PR8891,
`docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md`; this is an
implementation report, not another theory volume. PR8899 remains open and Draft.

## Actual probability model

The source starts with a multivariate Gaussian measure on the sum of state
and noise coordinates. Its covariance is

`D = diag(beta^-1 I_n, tau^-1 I_p)`, with **beta>0 and tau>0**.

The signal and noise marginal Gaussian laws and their independence are proved
from this measure. The actual observation is `Y=M X+epsilon`. Tau is noise
precision, so its variance is `tau^-1`; tau=0 is not a finite-noise experiment.
The matrix M is arbitrary and rectangular. No full-rank, injective-sensor or
nonzero-dimension hypothesis is imposed on the new statements.

Let `Sigma=(beta I+tau M^T M)^-1` and `K=tau Sigma M^T`. The previously
constructed inverse-precision candidate is now connected to the actual joint
law in source. This changes the source-level status of the Gaussian bridge
left open at the starting revision; it does not assert kernel verification.

## New source modules

### GaussianAffineDisintegration

`D5/S3/Observer/Linear/GaussianAffineDisintegration.lean` constructs actual
rectangular continuous linear maps between Euclidean spaces. Their adjoints
are identified with transposes. Gaussian pushforwards are proved from the
actual mean/covariance and Gaussian measure uniqueness. Joint Gaussianity and
zero cross covariance give independence.

The affine kernel is built from a deterministic data kernel, a constant
residual law, and a measurable affine map. It is proved Markov, with the
measure identity

`mu compProd translatedKernel(K,nu) = map (y,r)->(y,K y+r) (mu prod nu)`.

The general independent-residual helper is used only after the following
observation-specific module discharges its independence and residual-law premises.

### GaussianObservationDisintegration

`D5/S3/Observer/Linear/GaussianObservationDisintegration.lean` constructs the
input law, signal, noise, observation, innovation and posterior kernel.
For observation readout `B=[M,I]` and innovation `A=[beta Sigma,-K]`, the code
derives

`Xreadout=K B+A`, `A D B^T=0`, and `A D A^T=Sigma`.

It then derives independence of the innovation and data, identifies the
innovation law, and proves

`jointLaw(M,beta,tau) = dataLaw(M,beta,tau) compProd posteriorKernel(M,beta,tau)`.

The posterior kernel is identified pointwise with the earlier `candidateLaw`,
and satisfies the actual `Measure.IsCondKernel` predicate. No conditional-law
identity, residual independence or target covariance is assumed as a certificate.

### GaussianPosteriorRisk

`D5/S3/Observer/Linear/GaussianPosteriorRisk.lean` first proves the actual
Gaussian coordinate-square integrals and integrates their finite sum. The
energy loss is explicitly identified with `norm(x-a)^2/2`.
The global risk is a nonnegative integral in `ENNReal`, so an arbitrary
measurable estimator can have infinite risk. No global integrability or
finite-risk assumption on the competing estimator is made.

The identified posterior and Tonelli's theorem give the exact identity

`R(g) = trace(Sigma)/2 + E_Y [norm(K Y-g(Y))^2/2]`, in `[0,infinity]`.

The actual posterior mean attains the covariance term. Equality occurs exactly
when `g(Y)=K Y` almost everywhere under the data law. Risk is infinite exactly
when its deviation term is infinite. Thus totalized real integrals cannot
mistakenly give a nonintegrable estimator zero risk.

For any specified actual linear isometric equivalence U, every future-state
estimator has the loss-preserving pullback `U^-1 g`. This proves the same
lower bound for all measurable future estimators, attained by `U K Y`.
The theorem does not independently construct an orthogonal Hamiltonian flow;
that adapter remains a separate obligation.

## Executed finite checks

Run `python docs/reports/pr8899/posterior_checks.py`. It writes only
`posterior_checks.json` and makes no network request, Git operation or CI
change. The actual run passed **2,710 scoped assertions**. Repeated finite
checks are not independent theorem counts or proof of universal statements.
The report records package versions, seeds and exact Lean-source SHA-256 hashes.

The checks cover 132 rectangular systems with full, repeated-row, partially
blind and zero sensors, including zero-dimensional boundaries. They compare
block reconstruction, covariance and residual/data characteristic functions,
and check 396 normalized Bayes density identities. Ten rational matrix
systems are independently checked in SymPy. Eighteen scalar posterior laws
are integrated directly from the original joint density divided by the data
density, checking mass, mean and covariance.

The risk checks compare input-space Gaussian cubature against the posterior
risk expression for 56 polynomial estimators, including the mean and affine,
quadratic and cubic competitors. They test the attained minimum and orthogonal
propagation. Eighteen nonpolynomial sine-perturbed estimators are compared to
independent Gaussian characteristic-function moment formulas. Finite interval
lower bounds illustrate a concrete infinite-risk boundary; the numerical
program does not assert that finitely many tests prove divergence.

The largest recorded finite identity residual is below `4e-13`. This is a
floating-point diagnostic, not a formal error bound. Text scans found no
`sorry`, `admit`, `native_decide` or new axiom declaration in the three new
Lean sources. All 32 principal Scribe anchors resolve to declarations, and
string-stripped Scribe delimiter checks pass. Those are not C# compilation.

## Fourteen-result frontier

**Every row still requires actual Lean elaboration, kernel checking and the
applicable repository checks.** The table distinguishes source implementation
from still-missing mathematical constructions.

| Original result | Current source progress | Remaining full-statement obligations |
| --- | --- | --- |
| 2.2 Energy, flow and Gibbs split | PredictiveEnergySplitting | Hidden orthonormal coordinate equivalence, Gaussian Jacobian/normalization/product law and concrete flow adapter. |
| 2.3 Classical recovery | ClassicalProductRecovery | Pointwise conditional-KL integral and the specific Gaussian/flow correspondence. |
| 2.4 Canonical quantum split | Predictive Poisson form, MetaplecticChirp, CountableDiagonalGibbs, FiniteModeGibbsProduct | Full Darboux/Williamson, global metaplectic Fourier/dilation composition and domains, Schrodinger/occupation unitary and general trace-class adapter. |
| 3.2 Finite quantum leakage | WeylReconstruction, UnitaryAverageLeakage, WeylPartialTraceLeakage | Assembly with the paper's H, H0, V and conditional expectation. |
| 3.3 Dynamical/free-energy bounds | UnitaryDuhamelStability, GibbsFreeEnergyStability | Trace-norm state/channel and partial-trace estimates; physical leakage-certificate adapter. |
| 3.4 Quantum thermal recovery | Support-aware divergence and faithful-reference SpectralKlein | Supported singular-reference tensor logarithms/recovery, equality case, measurement DPI and sharp quantum Pinsker. |
| 3.5 Two-qubit counterexample | Written argument and earlier finite checks | Full Lean dynamics, thermal matrix, norm certificate and opposite visible rotations. |
| 4.2 Hidden minimax risk | HiddenExperimentRisk | Full physical instrument probability packaging and quantum entropy target range. |
| 4.3 Exact counting reduction | ExactPartitionCounting | Quantum Hamiltonian/partition adapter and polynomial-time/bit-complexity reduction. |
| 5.2 General graded Gramian | GradedExponentialRemainder | All-layer assembly, integration, positive limiting Gramian, sorted spectral multiplicities and determinant asymptotic. |
| 5.3 Legendre moments | MomentGramianStability and actual exponential remainder | Actual normalized Legendre L2 basis/moments and asymptotic connection. |
| 6.2 Gaussian information and risk | GaussianObservationPrecision plus the three new modules: actual conditional-law identity, all-measurable-estimator Bayes risk, a.e. uniqueness and specified orthogonal propagation | Mutual information/log determinant and mean conditional free-energy identity; construction of the specific trajectory observation/flow adapter. Posterior-law and Bayes-optimality source gaps are addressed by this batch, but remain unverified. |
| 6.3 Noise thresholds | Written theorem; finite-dimensional risk now has an actual probability-law source | General schedule and critical/noncritical limits from the fully assembled Gramian spectrum. |
| 6.4 Oscillator comparison | OscillatorSensorJets and actual exponential remainder | Full exponential-trajectory determinant and information/risk limit transfer. |

## Verification boundary and historical record

The local environment has no Lean or Lake executable, as recorded by the
executed script. The three new modules have **not been elaborated or checked
by the Lean kernel**, including their earlier import dependencies. The paired
Scribes have **not been compiled**. API, typeclass and tactic errors may remain.
No freeze, admission, global completion or independent mathematical review is
claimed. No proof gate or CI configuration has been changed to bypass this.

The preceding four-module continuation, with its 5,974 checks, remains at
[the starting revision's report](https://github.com/the-omega-institute/trureturing/blob/18dcb45bb6c8448ed7c40ba9c7df10ff21a78db3/docs/reports/pr8899/README.md).
Its `continuation_checks.py` and JSON are unchanged. Earlier initial reports
remain byte-preserved as `initial_coverage.md`, `research_legacy.py` and
`initial_validation.json`. The new Gaussian library provenance is
`Library/PredictiveReduction/mathlib433gaussianconditioning.md`.
The acceptance criterion for all fourteen results is unchanged.
