---
slug: ahiable-kothakonda-winter-2026-appt-quadbit-sextit-maximum-purity
bibkey: ahiablekothakondawinter2026geometry
doi: 10.48550/arXiv.2608.03390
url: https://arxiv.org/abs/2608.03390v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity.result
---

# Known 4-by-6 APPT maximum as a formal interface application

## Problem

Ahiable, Kothakonda and Winter, arXiv:2608.03390v2, Conjecture 6.7,
page 29, asks whether the maximum APPT purity equals the
inscribed-polytope maximum and occurs at the spectra of Eq. (44).
Its $m=4,n=6$ instance is already a consequence of existing mathematics.
This dossier records a formal application, not an independent open-problem
resolution or a new problem count.

Every positive semidefinite complex matrix $\rho$ on
$\mathbb C^4\otimes\mathbb C^6$ with trace one and
$(U\rho U^\dagger)^\Gamma\succeq0$ for every global unitary $U$ satisfies
$\operatorname{Re}\operatorname{Tr}(\rho^2)\leq8/169$.
The real purity supremum is $8/169$, attained by the diagonal state with
one entry $3/26$ and twenty-three entries $1/26$. Partial transpose acts
on the second local factor. Repeated and zero eigenvalues are included.

## Motivation

Hildebrand, quant-ph/0502170, Theorem 2, PDF page 5, proves that at equal
total dimension $N=n_1m_1=n_2m_2$, APPT for the factorization with
$\min(n_1,m_1)\geq\min(n_2,m_2)$ implies APPT for the second factorization.
Thus APPT $4\times6$ implies APPT $3\times8$. A unitary identification
preserves positivity, trace and purity. The established qutrit
maximum $32/26^2=8/169$ gives the upper bound, and the known APPT ray
$(I+2|\psi\rangle\langle\psi|)/26$ attains it in $4\times6$.
The source and scope are recorded in the existing
[Hildebrand library note](../Library/QuantumStates/hildebrand2007pptspectra.md).

## Gap

The formal library interface needs the rank-three necessary boundary LMIs
for arbitrary finite products, while the baseline qutrit reduction fixes
one local dimension at three. `FiniteBellCorner.spectral_reduction`
supplies that structural inference directly. Its actual consumer is
`QuadbitSextitMaximumPurity.density_bound`, used by `result`.
Planned 4-by-5 and 4-by-7 applications are not present consumers.

[#17734](https://github.com/the-omega-institute/trureturing/issues/17734)
is research history for this application, not evidence of novelty or
an open-problem admission authority. The existing 4-by-4 result and its
proofs and successful Reg evidence remain associated with
[#17689](https://github.com/the-omega-institute/trureturing/issues/17689).

## Route

For all $m,n\geq3$, embed $\mathrm{Fin}\,3$ into each local factor and
let $c(i,j)=(a(i),b(j))$. Its range and finite complement partition the
full product. Cardinality identifies the complement with
$\mathrm{Fin}(mn-9)$. Extend the Bell unitary and its swapped partner by
identity on this complement. Product compression satisfies

$$ (M^\Gamma)|_c=(M|_c)^\Gamma, $$

because both entries at $(i,j),(k,l)$ equal $M(c(i,l),c(k,j))$.
The two Bell tests therefore yield both necessary PSD matrices for the
same actual full density and spectrum. Sorted diagonalization retains
the largest three, smallest six and all middle coordinates, preserving
trace and purity. An arbitrary global packing is used only as a unitary
change of eigenbasis, never as partial-transpose covariance.

At $mn=24$, the boundary selector is exactly
`QutritSpectralReduction.boundaryValues 5`. The unchanged
`QutritN8PurityBound.certificate_bound` yields the bound with no copied
arrays or new numerical certificate. For a computational-basis unit
vector $\psi$, the known low-rank separable ray proves the prescribed
state APPT after every unitary; its trace and purity are $1$ and
$(24+8)/26^2$. Bound and attainment give the real supremum.

## Falsifier

A literal APPT density in $4\times6$ with purity greater than $8/169$
would contradict the stated implication and qutrit bound. A failure of
product compression, the complement equivalence or the full-spectrum
trace/purity identities would invalidate the direct formal route.

## Evidence

The retained targets are `FiniteBellCorner.spectral_reduction` and
`QuadbitSextitMaximumPurity.result` in the owning AbsolutePPT namespace.
The latter includes the universal bound, real supremum and exact
prescribed diagonal attainment. Existing accepted compilation and Reg
data support the preceding mathematical source. Source-only prose and
provenance revisions supply no new kernel, emitted-Scribe or official-CI
evidence.

## Triage

Against immutable baseline `8a32282e7f57c3a751640623624ee9d1ac5b3a25`,
`result` has `proof_shape: content` and `admission_basis: escape-witness`.
Unfolding `density_bound` and the same-delivery `spectral_reduction` until
baseline-frozen prerequisites leaves the arbitrary-product Bell necessity
inference on the live path to the upper bound and supremum. The final
conjunction alone does not determine proof shape. The new construction
is neither the scalar conclusion nor a restatement of it, and the
baseline qutrit theorem cannot instantiate to a 4-by-6 product. The
attainment helpers are bind-only with actual consumers. No open-problem
exception is used.

`utility: none` describes the new structural inference for arbitrary
complex densities and all global unitaries. It introduces no bounded
enumeration, checker, new numerical premise or newly certified finite
instance as its main content. The pre-existing rational certificate
retains its checker classification; normalization of the attaining ray
is helper arithmetic. A finite matrix dimension does not turn the
continuum of densities into a finite computation. This is a source-owner
semantic judgment, not a new machine acceptance result.

Hildebrand's implication preserves total dimension. It gives no transfer
from dimension 20 to 18 or 21 and no dimension-28 result by the qutrit
dimension-24 bound. The 4-by-5 and 4-by-7 sectors, all remaining sectors,
maximizer classification, the full conjecture and APPT versus absolute
separability remain outside this application. The generic necessary-LMI
theorem asserts no APPT sufficiency or mathematical priority.

## ASSUMED-UNVERIFIED

Targeted validation of the corrected source, selected Scribe emission
and official required CI remain outstanding. This is sole-worker,
same-family Codex CLI work, with no Pro or model-diversity review.

Two faithful Reg bindings remain `declared_unresolved` under
[#17689](https://github.com/the-omega-institute/trureturing/issues/17689):
`FiniteBellCorner.spectral_reduction` has IE-C050 ClosedTruthReadout,
`reason=forbidden_dependency`, `rule=source.unsafe_or_external`,
`site="Nat.pow; source_operand=Nat.pow"`, with the same readout;
`QuadbitMaximumPurity.norm_of_dot_eq_one` has IE-C050 ClosedTruthReadout,
`reason=unclassified_form`, `rule=source.dictionary_or_proof_coordinate`,
`site=""`, `readout=""`, at its implicit `Fintype I` dictionary.
Their original telescopes and compiled Reg proofs are retained.
These audit gaps supply no `declared_validated` status and do not stop
the mathematical delivery. Successful Reg evidence remains unchanged.
