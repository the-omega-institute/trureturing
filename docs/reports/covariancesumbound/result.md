# Density-state covariance sum bound

Worker outcome: 成 (implementation stage). All four requested mathematical parts are proved. PR creation and merge
remain the orchestrator's work. This report does not claim a merged result.
Producer: Codex implementation worker using lean4; zero independent review seats,
single-agent self-check. The caller's 600-sample counts were input; the separate
reproduction below was run by this worker.

Formal module: D5/S3/Quantum/Information/CovarianceSumBound.
The density state is the existing positive trace-one CStarMatrix subtype. Observables
are arbitrary finite complex matrices, assumed Hermitian wherever positivity or
Cauchy–Schwarz is needed. Singular states and empty index sets Q are allowed.
No commutativity between observables, faithfulness of the state, or tensor factorization
is assumed. Δ is the interval HALF width, explicitly nonnegative; interval centers
may depend on x. Sparsity is the cardinality hypothesis for each x in Q.

The source atom's subsequent preparation-time corollary is outside this theorem.
No Lieb–Robinson or light-cone result is proved, and no atom coverage edge is added.

## Proof and search assessment

The live path is covariance_sum_le → covariance_sum_le_of_variance → abs_covariance_le
→ centered_pair, together with covariance_sum_le → variance_le_half_width_sq →
expect_mono → expect_nonneg. centered_pair identifies the actual weighted matrix
inner product with the trace covariance. covariance_self connects both public definitions.

The Cauchy–Schwarz proof directly applies Mathlib norm_inner_le_norm to the existing
Matrix.toMatrixInnerProductSpace, including semidegenerate states. The spectral proof
uses cfc_le_algebraMap_iff for (t−c)², applies the positive trace expectation, and
subtracts (E(A)−c)². It does not import or reprove classical probability Popoviciu.
The sparse sum is restricted to its actual nonzero row support, bounded entrywise
using Cauchy–Schwarz and the variance bounds, then counted.

Pre-registration v2 conservatively uses proof_shape: bind-only and
admission_basis: atom-required-bridge; escape_witness: none claimed. The typed edge
required by the source's three-step proof is the density trace/centered matrix pairing
and its application to spectral variance and sparse supports. The named consumer was
covariance_sum_le before any Lean probe. This classification does not claim that
Mathlib already had the complete density-state theorem. It avoids treating component
inequalities or their transport as an independently novel inequality.

All eight public theorems use this same module-level basis. Direct frozen mathematical
theorem dependencies: []; the one direct imported frozen definition is
D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState,
statement_id sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337.
The imported module is generality G, with frozen module statement_id
sha256:445d28204f4c839e9d5711f568c7f8a3259e36bcff54986168a827333cbdbb5d.
Mathlib is pinned by the repository to v4.33.0.

| Public theorem | proof_shape | Registered obligation and consumer → prerequisite edge |
| --- | --- | --- |
| covariance_symm | bind-only | task 1 covariance API → covariance_symm |
| covariance_add_right | bind-only | task 1 covariance API → covariance_add_right |
| covariance_self | bind-only | abs_covariance_le → covariance_self |
| variance_nonneg | bind-only | covariance_sum_le_of_variance → variance_nonneg |
| abs_covariance_le | bind-only | covariance_sum_le_of_variance → abs_covariance_le |
| variance_le_half_width_sq | bind-only | covariance_sum_le → variance_le_half_width_sq |
| covariance_sum_le_of_variance | bind-only | covariance_sum_le → covariance_sum_le_of_variance |
| covariance_sum_le | bind-only | source theorem 123.2: registered endpoint |

Symmetry and right additivity are the user's explicitly requested reusable API laws;
they are not asserted to occur in the final proof's constant closure. Each is tied to
task 1, rather than an invented numerical consumer. All declarations have utility none:
they quantify over arbitrary finite carriers and analytic data. No finite enumeration,
checker, numeric-reduction or certified-instance theorem is delivered.

Search correction: before adding this module, the requested lexical pattern
rg -l 'abs_cov|Covariance' D5 matched 22 files (72 lines), not zero. These contain
other notions of covariance/equivariance. Reading GNSMatrix, FiniteDimensional,
QuantumRelativeEntropyDefectComposition and the quantum covariance candidates found
no statistical covariance API. No claim of an exhaustive semantic search is made.
Authenticated GitHub code search returned 44 covariance+density Lean files and 22
PreInnerProductSpace+trace files; the latter identified Mathlib Matrix/Order.
The Mathlib Matrix/Order v4.33.0 public source URL was fetched with HTTP 200.

## Numerical diagnostic

Run: python3 docs/reports/covariancesumbound/random_probe.py.
NumPy 2.0.2; seed 12320911; 600 samples, dimensions 2 through 8; 120 singular states;
tolerance 1e-10. Cauchy–Schwarz, full-width and half-width tests each have 0/600
violations. Raw counts and signed residual maxima are in random_probe.json.
These are independent samples, not a replay of unknown orchestrator random seeds.
They are floating-point diagnostics, not kernel counterexample certificates or proofs.
The exact optimality/equality case of Popoviciu is not separately formalized here.

## Validation and failure record

The complete draft compiled with lake env lean on the already stamped hot tree;
#print axioms covariance_sum_le reported only propext, Classical.choice, Quot.sound.
No sorry or private axiom is present. Final gate receipts follow below.

One report invocation was accidentally started before serial-lean had finished filling
baseline caches. It was terminated immediately after discovery, along with its own
cwd-qualified descendants; exit 143 is intentionally not accepted as validation.
The final gate chain starts again only after the serial completion sentinel.
The remaining baseline cache at that point was RadiusThreeCertificates; the two
expensive modules named in the brief were not edited. No host-wide process kill was used.

Lean interface repairs: use map_nonneg as a function on the star algebra equivalence;
make the CStarMatrix-to-Matrix trace coercion explicit; use Matrix.mul_smul instead of
the similarly named generic rewrite; supply the self-adjoint predicate explicitly to
CFC rewrites. No statement was weakened to repair a failed proof.


## Final local gate receipts

Canonical source sha256:
ff5fbaa33a52c5f463f763824fed719ae33c39656726b0f8da3f92fc74bdba8f.
The source-bound report has 27 declarations (including private/generated auxiliaries),
with 8 public user-facing theorems. The union of all axiom closures is exactly
Classical.choice, Quot.sound, propext. declaration-audit.json contains the public
statement identities and the per-theorem assessment.

| Check | Result |
| --- | --- |
| Initial serial-lean | exit 0; status=complete built=6 failed=0 missing=6 |
| Final serial-lean after naming correction | exit 0; status=complete built=1 failed=0 missing=1 |
| make -C tools dotnet | exit 0; 0 warnings, 0 errors |
| Final make lean-report | exit 0; delta changed=1 added=0 removed=0 recheck=1 |
| make emit | exit 0; 1 changed Blueprint, rendered and read |
| CI-layer scribe-content-checks.sh | exit 0; status=classified red=0 |
| make deposit-uncovered | exit 0; added=1 changed=0 conflicts=0 |

The Scribe check used the exact merge-base
 dc78a77a24b7d3b5ad62e96ac30c1f05764c99a0.
Its summary was DESCRIBE_STATUS case=DESCRIBE-NODES status=classified nodes=11179
suspected_novel=0 formula_content_slots=68 formula_statements=32 red=0 observe=5012.
OPEN projection/OBSERVE lines were not treated as red findings.

The deposit used GID
D5/S3/Quantum/Information/CovarianceSumBound.covariance_sum_le
and that same immutable base SHA. It reused the valid report, passed
DEPOSIT_HEADER_CHECKED SL-012, emitted 0 further changes, and returned
PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED reason=NO_ATOM.
Frozen module statement_id:
sha256:764b4acecf70a4ec02895cc386fdc0627662f58d9db718aef3dff79b99818f44.
Freeze event:
6a36c5890c5bb4574f9595d6101930a9a562422f6c01ebe339af3f9e98487753.

Post-addition bucket counts: D5 Information=6, Blueprint Information non-md=6,
Library Quantum=25. Lean header order is canonical; all Lean lines are at most 100
characters. No governance vocabulary appears in Scribe prose.

No mathematical gap remains in the requested four parts. The row sparsity premise,
the preparation-time corollary, and a separate optimality/equality-case theorem are
not proved here. The first is intentionally assumed and the latter two are outside
this worker's requested scope. No theory volume or atom was created. No PR was opened;
remote CI and MERGED status remain the orchestrator's responsibility.

Full command logs, including the intentionally terminated premature report, are in
/var/folders/wv/ht3wzsj138b4sxl3q4t0xdr40000gn/T/consensus-rnd/sshx/covsum-1/attempt-1/.
The branch is lane/math/covariancesumbound. Final pushed HEAD is recorded in the
runner result.json rather than introducing a self-referential commit hash here.
