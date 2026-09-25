# PR8899 formalization coverage and validation boundary

**Status: source implementation in progress; NOT all fourteen results complete;
NOT Lean-elaborated or kernel-verified.**

This delivery adds six Lean proof-source candidates (71 public theorem
declarations) and six paired Scribes (41 principal theorem anchors). The count
is a source inventory, **not a count of verified mathematical results**.
No `sorry`, `admit`, `native_decide`, or new axiom declaration occurs in the
comment-stripped new Lean sources. No frozen registry, verification ledger,
CI configuration, or existing frozen truth source is changed.

The single broader theory owner remains PR8891,
`docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md`. This file is an
implementation/coverage report, not another competing theory volume.
The fourteen rows below refer to the original sections in PR8899's
`PREDICTIVE_THERMODYNAMIC_SUFFICIENCY.md`, pinned at
`e300b5df71f5ce08d857e8f2000a9e495813cdaf`.

## Source inventory

| Module | Main implemented content |
| --- | --- |
| `D5/S3/Observer/Linear/PredictiveEnergySplitting.lean` | Constructed minimum-energy lift; derived intertwining and energy cross-term cancellation; actual covariance inverses; invariant hidden projection; nondegenerate/even-dimensional visible Poisson form. |
| `D5/S3/Quantum/Thermal/ClassicalProductRecovery.lean` | Genuine measure KL chain; finite-defect guards; constructed standard Borel disintegration of arbitrary joint laws; attained and unique thermal product minimum; reversible observation-square invariance. |
| `D5/S3/Quantum/Thermal/ExactPartitionCounting.lean` | CNF syntax, violating-clause count, local commuting Boolean projections, actual Boltzmann/rational weight equality, exact floor recovery of the satisfying-assignment count, natural numerator/common denominator. |
| `D5/S3/Quantum/Thermal/HiddenExperimentRisk.lean` | Actual local Kraus tensor updates through arbitrary finite adaptive histories; hidden-state record-weight independence; randomized minimax absolute-risk lower bound and attained midpoint upper bound with nonnegative integrals. |
| `D5/S3/Quantum/Algebra/WeylReconstruction.lean` | Consume the existing Weyl trace pairing; prove linear independence and surjective synthesis; reconstruct arbitrary local matrices with explicit trace coefficients; extend linear zero-leakage tests from Weyl words to the full matrix algebra. |
| `D5/S3/Observer/Linear/OscillatorSensorJets.lean` | Compute derivative rows from the actual oscillator generator and sensors; equal gain; explicit inverse; exact Hilbert/polynomial determinant constants; exact polynomial-model time scaling. |

Every module has its path-matched `Blueprint/.../*.scribe.cs`. The library
search/provenance note is
`Library/PredictiveReduction/mathlib433thermalrecovery.md`.

## Fourteen-result correspondence -- no row is declared kernel-complete

| Original result | Implemented source correspondence | What remains for the full stated result |
| --- | --- | --- |
| 2.2 Classical symplectic/thermal split | `PredictiveEnergySplitting.canonical_lift_data`, `lift_intertwines`, `lift_energy_blocks`, `coordinate_hessian`, `hidden_projection`. Inverse witnesses are derived from positive definiteness and full row rank. | Construct the orthonormal hidden basis/coordinate equivalence; Gaussian product law, volume Jacobian, normalization integrals and partition factors; actual flow implementation. |
| 2.3 Classical recovery and unique minimum | `ClassicalProductRecovery.arbitrary_joint_recovery_chain`, `arbitrary_joint_recovery_defect`, `all_joint_laws_unique_minimum`, `predictive_defect_invariant`. The conditional kernel is constructed, not assumed. | The integral of pointwise conditional KL, the specific Gaussian coordinate pushforward, and connection to the constructed Hamiltonian flow. Abstract measure equality and uniqueness are source-implemented. |
| 2.4 Canonical quantum split | `PredictiveEnergySplitting.predictive_poisson_nondegenerate` proves the finite symplectic no-radical/even-dimension part. | Darboux/Williamson construction, actual infinite-dimensional Schrodinger tensor factorization, metaplectic unitary, unbounded Hamiltonian domains, trace-class Gibbs factors and oscillator partition formula. No finite-matrix CCR substitute is claimed. |
| 3.2 Finite quantum leakage theorem | `WeylReconstruction.coefficient_extraction`, `word_linearIndependent`, `weyl_reconstruction`, `linear_map_zero_iff_weyl` close the complete-local-algebra basis gap. | Actual bipartite conditional expectation/twirl, interaction decomposition, operator-norm lower and upper bounds, normalized Hilbert-Schmidt identity, and zero interaction equivalence. No entrywise matrix norm is silently substituted for the operator norm. |
| 3.3 Dynamical/free-energy stability | No new full statement yet. | Duhamel bound, trace-norm contraction, Gibbs variational/log-partition perturbation, all constants and the bounded time comparison. |
| 3.4 Quantum thermal recovery | Existing support-aware divergence is identified in the library note, but not treated as a proved recovery theorem. | Supported product logarithm/partial trace identities, mutual-information split, nonnegativity/equality case, quantum Pinsker, coupled-defect comparison. The legacy telescoping theorem is insufficient. |
| 3.5 Two-qubit counterexample | Not implemented in Lean in this delivery. | Explicit dynamics, actual thermal density, trace-norm leakage norm and the two opposite visible rotations; restricted versus full algebra distinction. |
| 4.2 Hidden adaptive identifiability and minimax | `HiddenExperimentRisk.hidden_states_indistinguishable` and `sharp_no_information_risk`; every finite path is constructed with its full history. | Density/instrument probability-law packaging, coarse-graining multiple Kraus branches where required, and quantum entropy range identifying the physical diameter `log(e)/beta`. The abstract arbitrary-randomized-output risk theorem is source-implemented. |
| 4.3 Exact counting obstruction | `ExactPartitionCounting.exact_cnf_counting_recovery`, `clause_three_local`, `clauseProjector_idempotent`, `clauseProjectors_commute`, `boltzmann_weight`, `penalty_sum`, `common_denominator`. | Full finite quantum Hamiltonian/partition adapter and polynomial Turing-reduction/bit-complexity proof. This is not a theorem about approximate free energy or arbitrary local lattice models. |
| 5.2 General short-window Gramian spectrum | No general asymptotic statement yet; only the concrete polynomial model below. | Construct graded orthogonal layers, prove the polynomial Gramian positive, uniform exponential remainder under anisotropic scaling, Loewner comparisons, eigenvalue multiplicities and determinant asymptotic. |
| 5.3 Finite Legendre moments | Not implemented in Lean in this delivery. | Construct actual normalized moment integrals, prove leading Gram equality and projection/noise bounds, and account for quadrature when approximated. |
| 6.2 Gaussian posterior, information and risk | Not implemented in Lean in this delivery. | Actual joint Gaussian observation law, conditional posterior, KL/mutual-information computation, optimality over measurable estimators, expected posterior free-energy identity and orthogonal propagation. |
| 6.3 Noise thresholds and small-time limits | Not implemented in Lean in this delivery. | Derive thresholds from the proved spectrum, treat critical exponents and arbitrary positive noise schedules, and prove the fixed-noise expansion. |
| 6.4 Two-oscillator comparison | `OscillatorSensorJets.sum_jet_table`, `separate_first_derivative`, `equal_initial_gain`, `sum_jets_observable`, determinant declarations and `scaled_sum_polynomial_determinant`. | Transfer the exact polynomial coefficients to the actual exponential-trajectory Gramian and prove the information/risk limits. The finite constants are not presented as the full asymptotic result. |

## Independent finite checks actually run

Run `python Evidence/PR8899/research.py` with the dependencies recorded in
`validation.json`. The script is deterministic with seed 8899 and makes no
network request or Git operation. It only overwrites its generated report next
to itself and scans the six explicitly listed modules, not unrelated repository files. The present run records 98,178 assertions, predominantly exhaustive
small-CNF arithmetic rather than 98,178 different mathematical results.

The exact checks cover 10,931 exhaustive formulas with zero, one or two
variables (including empty clauses, repeated literals and empty formulas),
plus 300 seeded larger formulas; 20 rational coordinate-change Hamiltonian
systems; 300 rational randomized estimator laws; and exact oscillator jet,
Hilbert and polynomial Gramian determinants. A non-positive-energy example
also verifies that dropping the positivity hypothesis breaks the Poisson
no-radical conclusion.

The numerical checks cover finite Weyl dimensions 1 through 8, adaptive
visible histories, genuine finite-distribution KL chains, and high-precision
full oscillator trajectories. For the full trajectory, the script prints
small-window diagnostics, **not certified asymptotic bounds**. Numeric matrix
errors in this run are below `5e-15`, and KL chain errors below `3e-16`.

`validation.json` also records a SHA-256 hash of each exact Lean source file,
checks that each module has its Scribe, and resolves all 41 principal Scribe
anchors against declared source names. These are text-level checks. They do
not establish Lean type correctness, elaboration success, or C# compilation.

## Verification not performed

- No Lean/Lake executable or project build cache was available in the execution
  environment. The available GitHub compiler-artifact download was attempted
  but rejected because its 1,462,041,028-byte archive exceeds the connector's
  536,870,912-byte limit. No compiler was obtained.
- Consequently **no new Lean file has been elaborated or kernel-checked in
  this delivery**. API/elaboration errors may remain in the source candidates.
- The paired Scribes were not compiled; no freeze, independent review, CI pass,
  or fourteen-result completion is asserted. `#print axioms` commands in source
  are pending audit instructions, not evidence that they have run.

The PR must remain open and Draft. Its acceptance criterion is unchanged:
faithful correspondence for all fourteen mathematical results, actual kernel
verification, applicable repository checks, and independent review. Remaining
results must not be renamed as completed subcases, replaced by their own
conclusions as hypotheses, or silently deleted from this coverage table.
