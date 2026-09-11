# Covariance sum bound: registration v2

Source: quantum-reality atom
094657db7847e44298e387e72270c382e49293e06aef70711eac88d383f1ce94,
theorem 123.2, its three-step proof (not the following preparation-time corollary).
Skill: lean4. Producer: Codex implementation worker; single-agent implementation,
no independent review. PR and merge belong to the caller.

Convention: real symmetrized covariance of finite-dimensional Hermitian matrices,
Covρ(A,B)=Re tr(ρ(AB+BA))/2−Re tr(ρA) Re tr(ρB).
Varρ(A)=Re tr(ρ A²)−(Re tr(ρA))². Δ is the interval HALF width:
spectrum(A) ⊆ [c−Δ,c+Δ], Δ≥0. General finite carriers and singular density states.
Sparsity is an input card(filter Q (Covρ(Rx,Ry)≠0))≤b for x∈Q.

v1 was the task's proposed escape-witness at the spectral variance estimate.
v2 conservatively downgrades: proof_shape bind-only for direct upstream inequalities;
admission_basis atom-required-bridge. Named downstream consumer (registered before
implementation): D5/S3/Quantum/Information/CovarianceSumBound.covariance_sum_le.
The required new typed edge connects the existing DensityState trace functional to
centered matrix semi-inner products, variance and the spectral interval estimate.
The consumer must actually use this edge and the sparse row cardinalities.
No declaration is admitted as a standalone rephrasing of its definition.

Search receipts: D5 has GNSMatrix.gns_matrix_identity and DensityState in
QuantumRelativeEntropyDefectComposition, but statistical covariance search found none.
Pinned Mathlib Analysis/Matrix/Order has toMatrixSeminormedAddCommGroup and
 toMatrixInnerProductSpace; InnerProductSpace/Defs has inner_mul_inner_self_le;
Probability/Moments/Variance has variance_le_sq_of_bounded (Popoviciu).
The classical probability theorem cannot be applied to a matrix without a spectral
probability transport; CFC is an alternative for the operator-valued interval step.
GitHub authenticated code search is available: covariance+density+language:Lean
returned 44 lexical files, with no exact theorem identified in that search.
PreInnerProductSpace+trace returned 22 files, pointing to the pinned Matrix/Order API.
These searches are bounded, not exhaustive claims about the ecosystem.

Location: registered Quantum domain, S3; Information bucket before addition:
D5=5, Blueprint counted non-md=5, Library/Quantum=24, all below 48.
All direct D5 imports must be G. utility: none: arbitrary finite-dimensional
analytic statements, no bounded enumeration/checker/numeric reduction/certified instance.

Completion: kernel proof without sorry/private axiom, serial-lean sentinel complete,
lean-report exit 0, emit exit 0, deposit-uncovered exit 0, Scribe content check red=0,
commits and push. If only infrastructure closes, deliver it with exact residual gaps.
Counterexamples require a kernel witness. No PR creation and no atom coverage mutation.
