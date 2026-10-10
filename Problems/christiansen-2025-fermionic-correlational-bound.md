---
slug: christiansen-2025-fermionic-correlational-bound
bibkey: christiansen2025correlational
doi: null
url: https://arxiv.org/abs/2505.21167v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.result
---

# Christiansen's fermionic correlational bound

## Problem

Martin Ravn Christiansen, *A Correlational Bound for Eigenvalues of Fermionic
2-Body Operators*, arXiv:2505.21167v1, Section 1.1, Conjecture 3, asks for a
constant $C>0$, independent of the normalized canonical pair state
$\Phi=\sum_k\lambda_k u_k\wedge v_k$, such that every even $N\ge2$ with
$N\lambda_{\max}^2\le1$ and every normalized $N$-particle state satisfy

$$
\langle\Phi,\gamma_2^\Psi\Phi\rangle\le
N\left(1-\frac{N-2}{2}\sum_k\lambda_k^4+C(N\lambda_{\max}^2)^2\right).
$$

The [source note](../Library/QuantumBounds/christiansen2025correlational.md)
quotes the conjecture and the RDM definition. [Preregistration #14135](https://github.com/the-omega-institute/trureturing/issues/14135)
fixes CHR-3 with $C=5/8$ over every separable complex Hilbert space, including
infinite-dimensional spaces. The source conventions are $\lambda_k\ge0$,
$\sum_k\lambda_k^2=1$, mutual orthonormality of the pair modes,
$u\wedge v=(u\otimes v-v\otimes u)/\sqrt2$, and RDM trace $N(N-1)$.

## Motivation

`D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound.result`
proves CHR-3. Its particle-number parameter $N=2r+2$, $r\in\mathbb N$, covers
exactly the even particle numbers at least two. Its Hilbert-space assumptions
are `NormedAddCommGroup`, `InnerProductSpace ℂ`, `CompleteSpace` and
`TopologicalSpace.SeparableSpace`; no finite-dimensional assumption is present.
The canonical family is supplied as in the source, rather than assumed to span
the whole one-particle space.

## Gap

The preregistration records the source-version, author-listing, Semantic Scholar
citation and MathDB searches, with no settlement found in that searched scope.
Those literature readings are attributed to the orchestrator in the issue;
a bounded search is not a proof of exhaustive novelty. The supplied canonical
form is part of the statement, and a theorem constructing that form for every
normalized pair vector is not claimed here.

## Route

The particle carrier is the physically antisymmetric subspace of the actual
completed Hilbert tensor power. Slater coordinates identify this subspace with
occupation coordinates; tensor-head contractions are normalized by $\sqrt N$.
The Gram RDM transports through that identification with trace $N(N-1)$.
The canonical identity (2.4) is

$$
\langle\Phi,\gamma_2^\Psi\Phi\rangle=2\|B\Psi\|^2,
\qquad B=\sum_i\lambda_i c(v_i)c(u_i).
$$

Put $N=2m$, $p_i=\lambda_i^2$ and $\alpha=\lambda_{\max}^2$.
On a finite occupation sector, the weighted row estimate is

$$
\frac{(Kf)(D)}{f(D)}\le
m-m(m-1)\sum_{i<L}p_i^2+\frac52m^3\alpha^2,
\qquad K=B_L^*B_L.
$$

Finite pair operators converge on the countable occupation Hilbert space;
finite occupation embeddings are dense. The original coefficients are retained
at every cutoff. These facts yield the completed correlational estimate and its
transport to the source-space Rayleigh expression.

## Falsifier

The conclusion asserts the cap $N\lambda_{\max}^2\le1$, unit particle norm,
the supplied canonical series and the source's physical antisymmetry and RDM
normalization. A finite-dimensional-only coordinate estimate would not establish
this statement. Neither the source's unrestricted rational bound (1.5) nor an
optimal correction constant is asserted.

## Evidence

The six modules and their canonical Scribes are under
`D5/S3/Quantum/FermionicCorrelationalBound/` and
`Blueprint/D5/S3/Quantum/FermionicCorrelationalBound/`.
The settling declaration is `SourceCorrelationalBound.result : claim`.
Supporting results include `OccupationHilbertContractions.sum_pair_energies`,
`CanonicalRdmAndPadding.completed_identity_2_4`,
`CompletedTensorSlaterGeometry.antisymmetric_orthogonal_slaters_zero`,
`PhysicalContractionRdmBridge.antiHead_intertwining`,
`PhysicalContractionRdmBridge.sourceRayleigh_transport`,
`CompletedCorrelationalBound.actual_sector_bound` and
`CompletedCorrelationalBound.countable_finite_corrected_bound`.
The Scribe associates the frozen settling declaration with a Proved
`OpenProblemResolutionClaim` for this dossier. Lean is the mathematical source;
the classification and source-fidelity judgements remain semantic review duties.

## Triage

### What the settlement shows

- **Mechanism — proved (kernel-checked declarations).**
  `CanonicalRdmAndPadding.completed_identity_2_4` identifies the canonical
  Rayleigh expression with $2\|B\Psi\|^2$.
  `OccupationHilbertContractions.pairKernel_weighted_row` and
  `pairKernel_row_bound` use the Schur comparison product
  $f(D)=\prod_{i\in D}w_i$, where
  $w_i=\sqrt{p_i}/(1+(m-1)p_i)$ for $p_i>0$ and $w_i=1$ for $p_i=0$.
  The denominator estimate retains $\sum_i p_i^2=\sum_i\lambda_i^4$
  uniformly in the cutoff. `PhysicalContractionRdmBridge.sourceRayleigh_transport`
  connects the physical pair annihilator and RDM to this estimate.
- **Constant — proved (kernel-checked declaration).**
  `SourceCorrelationalBound.result` proves $C=5/8$.
  **Lower comparison — proved (literature reading and paper argument).**
  Christiansen's Theorem 2 supplies the lower expression
  $N(1-(N-2)\sum_k\lambda_k^4/2-\tfrac12(N\lambda_{\max}^2)^2)$.
  Comparing a uniform upper expression in the same form with this lower
  expression gives the necessary comparison $C\ge-1/2$ whenever
  $N\lambda_{\max}^2>0$. This comparison is not a new Lean theorem.
  **Optimal constant — open:** neither sharpness of $5/8$ nor the optimal
  universal correction constant is established.
- **Cap — proved (kernel-checked row estimate and assembly).**
  `OccupationHilbertContractions.pairKernel_row_bound` uses $2m\alpha\le1$
  to control the comparison denominators and the quadratic correction.
  `CompletedCorrelationalBound.completed_result` uses this cap at $N=2m$;
  the settling source statement applies it at $m=r+1$, $N=2r+2$.
  **Extension outside the cap — open:** no uniform estimate there is claimed.
- **Eigenvalue consequence — proved (kernel-checked universal Rayleigh
  conclusion; paper implication).** The bound applies to every normalized
  $\Phi$ with supplied canonical form satisfying the cap, without an
  eigenvector hypothesis. For such a $\Phi$ that is an eigenvector,
  its eigenvalue equals the Rayleigh expectation, hence obeys the same bound.
  This supplies the conjectured upper estimate for the source's question in
  the capped regime; it does not establish the stronger unrestricted rational
  bound (1.5), which the source refutes. Theorems 1 and 2 retain their stated
  hypotheses and conclusions; no further source theorem is asserted to follow.
- **Spectator modes — proved (kernel-checked construction and estimate).**
  `OccupationHilbertContractions.adapted_hilbert_basis` retains the orthogonal
  complement of the supplied pair modes. `CompletedCorrelationalBound.actual_sector_bound`
  allows spectator occupations. Pair modes need not span the space, so odd
  finite dimensions are included.
- **Zero coefficients — proved (kernel-checked declarations).**
  `OccupationHilbertContractions.comparisonVector_pos` uses weight $1$ at a zero
  coefficient; `pairKernel_weighted_row` handles its vanishing hopping terms.
  Strict positivity of the comparison vector does not require every coefficient
  to be positive.
- **Unrenormalized cutoffs — proved (kernel-checked declarations).**
  `CanonicalRdmAndPadding.finite_mass_le_one` retains square mass at most one.
  `countableBL_tendsto` and
  `CompletedCorrelationalBound.countable_finite_corrected_bound` take the limit
  with the original coefficients and cap. No rescaling of a truncated family
  is part of the estimate.

## ASSUMED-UNVERIFIED

The literature novelty conclusion is limited to the issue's recorded search
scope. The optimum constant and extensions beyond the cap are open. The
canonical-form existence theorem for arbitrary normalized pair vectors is
outside this delivered statement; the source supplies that representation.
Information-escape registration is paused under CLAUDE.md §3.9.
