---
slug: choi-kiem-kye-2020-maximal-birank-edge-states
bibkey: choikiemkye2020maximalbirank
doi: 10.1063/1.5122836
url: https://arxiv.org/abs/1903.10745v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/ChoiKiemKye/MaximalBirankEdgeStates.result
---

# Choi–Kiem–Kye maximal bi-rank edge states

## Problem

J. Choi, Y.-H. Kiem and S.-H. Kye, *Entangled edge states of corank one
with positive partial transposes*, J. Math. Phys. 61, 062202 (2020),
arXiv:1903.10745v2, Conjecture 6.4 ([Library note](../Library/QuantumBounds/choikiemkye2020maximalbirank.md)):

> For any $n\ge 3$, the open set of parameters
> $(\alpha_1,\ldots,\alpha_n,\beta_1,\ldots,\beta_n)$ which give PPT entangled
> edge states of bi-rank $(n^2-1,n^2-2n+3)$ is nonempty.

The binding statement in issue #13859 asks for the Section 6 construction
in every dimension $n\ge3$, with unit phases, $\alpha_1=\beta_n=1$,
$\alpha_i^{-1}\alpha_j\ne\beta_i^{-1}\beta_j$ for $i<j$, and $r$ the
largest real root of $\det D_n^{\alpha,\beta}(r)$. Partial transpose acts
on the first tensor factor. The operators are unnormalized. Entanglement
is expressed through the nonzero edge condition under that convention.

## Motivation

`D5/S3/Quantum/Entanglement/ChoiKiemKye/MaximalBirankEdgeStates.result`
proves this existence statement for every $n\ge3$. The two ranks are
exactly $(n^2-1,n^2-2n+3)$; the source identifies this as the maximal
possible edge-state bi-rank in an $n\otimes n$ system. The theorem supplies
examples in unbounded dimensions, beyond the source's finite numerical
verification.

## Gap

The preregistration #13859 classifies CKK-6.4 as Tier 1 by origin and
records its source and literature scope: the original Theorem 6.3 verifies
$3\le n\le1000$ numerically; Han–Kye arXiv:2606.16265v1 and Gulati
arXiv:2506.11346v4 do not provide the all-dimension settlement. These are
the issue's literature readings, rather than a claim that the literature
search proves no other solution exists.

## Route

`ConstructionReduction` gives the literal Section 6 matrices and the
first-factor partial transpose. Its `Draft.triangular_pivot` proves the
support reduction used by `proposition61`: the simple largest root and
the kernel-vector condition imply PPT and the edge and rank properties.

`UniformParameterAnchor.Anchor.actual_kernel` constructs the anchor
kernel. `UniformPerturbedParameters.Anchor.perturbed_kernel_stability`
transports its strict half-plane margins to the explicit admissible family;
`Anchor.n_ge_17` proves the complete conclusion for $n\ge17$. The spectral
estimate is the Weyl inequality in
`HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_norm`.

`MaximalBirankEdgeStates.Small.certificate_sound` proves soundness of the
Gaussian-integer checker. `Small.valid3` through `Small.valid16` discharge
the fourteen small dimensions. Its private
`Finite.root_and_kernel_enclosure` gives the certified root and kernel
estimates used by soundness. `Full.construction` combines both ranges, and
`Full.result` gives `Full.claim`.

## Falsifier

A counterexample to the formal conclusion would be a dimension $n\ge3$
in which every admissible pair fails one of the Section 6 PPT, nonzero
edge or exact rank requirements at the largest determinant root. The
kernel-checked theorem rules this out for the encoded statement. A
mismatch between a source clause and its encoding is a separate fidelity
question; the first-factor convention and the issue's source-consistent
Section 6 formulas specify that boundary.

## Evidence

The five Lean modules and their Scribes carry the construction, analytic
bounds and finite certificates. The settling Scribe's
`OpenProblemResolutionClaim` records Proved for this problem. The result
has no additional hypotheses: it quantifies over every natural $n\ge3$.
The axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

## Triage

### What the settlement shows

- **Proved — decisive mechanism.** Proposition 6.1 reduces the edge and
  rank properties to a triangular pivot condition on the kernel vector.
  The explicit phase family and perturbation estimate give a simple
  largest root $r>5$ with the required margins for every $n\ge17$.
  The proved checker and exact certificates cover $3\le n\le16$.
  Evidence: `ConstructionReduction.Draft.triangular_pivot`,
  `ConstructionReduction.proposition61`,
  `UniformParameterAnchor.Anchor.actual_kernel`,
  `UniformPerturbedParameters.Anchor.perturbed_kernel_stability`,
  `UniformPerturbedParameters.Anchor.n_ge_17`,
  `MaximalBirankEdgeStates.Small.certificate_sound`,
  `Small.valid3`–`Small.valid16`, and `Full.result`.
- **Computed — the large-dimension root bound fails at $n=3$.** For every
  admissible pair in dimension $3$, every real determinant root satisfies
  $r\le3$. Thus $r>5$ cannot be the uniform argument in that dimension.
  The checked scope is exactly $n=3$ and all admissible phases; no bound
  for other small dimensions is inferred. The source scratch check
  `CKKSmallBoundary.lean` has SHA-256
  `00b90e577d6add57c0b1aa8307482cd5bd908efcd61c8fc6dcde0d98fb75a046`.
  The portable source below uses the delivered names, has SHA-256
  `97ae487f45c887d66e1944557e327a814a8f742a2dd83b0bc8f238edf1758d27`, and is checked by
  `bash tools/scripts/worktree/lean-cache-run.sh lake env lean .lake/scratch/ckk-boundary.lean`, exit `0`.
  It is a scratch computation and is not a delivered Lean declaration.
- **Proved (paper argument) — normalization.** For $c>0$, multiplication by $c$
  preserves positivity; $(cA)^\Gamma=cA^\Gamma$, and both ranges and both
  ranks are unchanged because scalar multiplication is invertible.
  Therefore the forbidden pair of product vectors in the edge condition
  is unchanged. A nonzero positive semidefinite matrix has positive trace:
  its nonnegative eigenvalues cannot all vanish. Taking
  $c=1/\operatorname{tr}A$ consequently gives a trace-one PPT edge state
  with the same bi-rank. This is the stated paper argument, not an
  additional kernel-checked normalization theorem in this delivery.
- **Open — universality in parameters.** Whether every admissible
  $(\alpha,\beta)$ in the open parameter set has the maximal bi-rank is
  not established by an existence theorem. `Full.result` proves an
  explicit admissible family for each dimension; it makes no assertion
  about every admissible family.

The anchor phase $e^{\pi i/4}$ and the explicit small perturbation are
sufficient choices, as witnessed by the delivered construction. Their
necessity, alternative anchor phases, and maximal-rank edge states for
other bipartite systems remain **open** here. The settlement extends the
source's nonemptiness conclusion to all dimensions and supplies the
existence input to any argument conditional only on CKK-6.4; it does not
alter the classification of all PPT states or certify other parameter
families.

### Reproducible boundary check

Extract the following block as `.lake/scratch/ckk-boundary.lean` at the
repository root and run the command above. Strict diagonal dominance
makes $D(r)$ positive definite when $r>3$, contradicting a zero determinant.

```lean
import D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
open D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
noncomputable section
open Matrix
open scoped ComplexConjugate ComplexOrder
namespace CKKSmallBoundary
theorem n3_root_le_three (a b : Fin 3 → ℂ) (h : Admissible a b) (r : ℝ)
    (hr : (D a b r).det=0) : r≤3 := by
  by_contra hbad
  have h3 : 3<r := lt_of_not_ge hbad
  have hna : ∀ i, ‖a i‖=1 := fun i=>(h.1 i).1
  have hnb : ∀ i, ‖b i‖=1 := fun i=>(h.1 i).2
  have hpd : (D a b r).PosDef := by
    apply Path.scaled_dominance_posDef (D_hermitian (by norm_num) a b r) (fun _=>1) (by simp)
    intro i
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    have h22 : (⟨2, by decide⟩ : Fin 3) = 2 := by decide
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    fin_cases i <;> norm_num [Fin.sum_univ_succ,D,hna,hnb,norm_mul,Complex.norm_conj,h02,h12,h22,h20,h21] <;> linarith
  have hnz := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit)
  exact hnz hr
end CKKSmallBoundary
#print axioms CKKSmallBoundary.n3_root_le_three
```

## ASSUMED-UNVERIFIED

The settlement is relative to the issue's faithful-encoding conventions:
zero-based `Fin` indices, the first-factor partial transpose, the
source-consistent Section 6 expressions and entanglement through a nonzero
edge certificate. Openness of the successful parameter locus and the
convex-decomposition definition of entanglement are not separately
formalized here. The literature status is the preregistration's bounded
reading; it is not a completeness theorem about publications.
