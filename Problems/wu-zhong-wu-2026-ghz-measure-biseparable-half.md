---
slug: wu-zhong-wu-2026-ghz-measure-biseparable-half
bibkey: wuzhongwu2026ghzmeasure
doi: 10.48550/arXiv.2605.02876
url: https://arxiv.org/abs/2605.02876v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.result
---

# The exact A|BC constant of the GHZ measure

## Problem

S. Wu, K. Zhong and J. Wu, “A measure for genuine tripartite entanglement”,
arXiv:2605.02876v3, Section V.C, equation (37), state:

> Numerically maximising E_GHZ over all biseparable A|BC states we find the sharp value sup_{ρ ∈ A|BC} E_GHZ(ρ) = ½, (37) attained e.g. by |0⟩_A ⊗ |Φ⁺⟩_BC and coinciding with the product-state value (34); the analytic proof of the exact constant 1/2 remains open. The same 1/2 holds for the B|AC and C|AB partitions by symmetry.

Issue [#12719](https://github.com/the-omega-institute/trureturing/issues/12719)
preregisters the Tier 1 A|BC statement: every product of arbitrary density
matrices has E_GHZ at most one half, and some such product attains one half.
The specified class is exactly ρ_A tensor ρ_BC, including mixed factors.

## Motivation

For a real direction n, the spin is n_x X + n_y Y + n_z Z. The encoding
uses the existing Bloch matrix at trace parameter zero and vector 2n.
Each pair of directions is Mathlib `Orthonormal` in the three-dimensional
real Euclidean space. The observable is σ_a tensor (σ_b tensor σ_c), with
complex matrix indices Fin 2 × (Fin 2 × Fin 2); its expectation is the real
part of the matrix trace against ρ.

Equation (27) is
Istar = E(a1,b1,c1) − E(a1,b2,c2) E(a2,b1,c2) E(a2,b2,c1).
Equation (30) is one half the supremum of |Istar| over the three independent
orthonormal pairs. `claim` asserts its universal product-density upper bound
and existence of an attaining density product.

## Gap

The v3 source explicitly leaves the analytic proof of equation (37) open.
The literature check in #12719 covers the arXiv versions and INSPIRE;
Semantic Scholar and the mathematical conjecture corpora are search-seat
reports. No settlement was found in that searched scope. This is a bounded
literature reading, not an exhaustive priority claim.

Convexity, property (P6), is a separate assumption for bounds on mixtures
across partitions. It is not a hypothesis of this product-density result
and is not established by it.

## Route

Product expectations factor. Put u = E_A(a1), u′ = E_A(a2) and
f_jk = E_BC(bj,ck). Then Istar = u f11 − u u′² f22 f12 f21.
Variance of a real linear combination of anticommuting Hermitian
involutions gives the squared-expectation bound. It supplies
u² + u′² ≤ 1, f11² + f12² ≤ 1, f11² + f21² ≤ 1 and |f22| ≤ 1
on the same product state and the same BC density matrix.

With q = |u| and x = |f11|, these imply
|Istar| ≤ q[x + (1−q²)(1−x²)] ≤ 1.
When 1−q² ≤ 1/2 the bracket is at most one; otherwise q ≤ 3/4 and
the bracket is at most 5/4, so their product is at most 15/16.
The admissible-value set is nonempty and bounded, allowing `csSup_le`.

The existing zero-state and Bell density matrices, with frames
(z,x), (x,z), (x,z), give u = 1, u′ = 0 and f11 = 1.
`le_csSup` and the upper bound prove equality at one half.

## Falsifier

A density product and three orthonormal pairs with |Istar| > 1 would
contradict the upper bound. Absence of any attaining density product
would contradict the sharpness clause. Both clauses are proved together.

## Evidence

`D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.lean` exposes the
necessary definitions `IsDensity`, `expect`, `observable`, `E`, `Istar`,
`values`, `EGHZ`, `claim` and the sole theorem `result : claim`.
Its auxiliary facts are local proof terms, with no private theorem or
forwarding declaration. The result has `proof_shape: bind-only` and
`escape_witness: none`, under `admission_basis: open-problem-resolution`
(#12719; Proved), as specified in the issue's
[proof-shape v2](https://github.com/the-omega-institute/trureturing/issues/12719#issuecomment-5975741218).
The analytic bound and its exact attaining state have utility `none`:
this is not a bounded enumeration, checker, numerical reduction or
ordinary certified-instance delivery.

## Triage

Tier 1: an externally published, explicitly open analytic sharp-bound
question. There is no digestion atom or coverage operation.

### What the settlement shows

- **Proved within the result's derivation:** on arbitrary density factors,
  the triple product in Istar carries u′². The two overlapping anticommuting
  pairs on the same BC state constrain |f12 f21| by 1−x². The resulting
  estimate q[x + (1−q²)(1−x²)] ≤ 1 is the decisive mechanism. No purity
  hypothesis is required on either factor. These are proof-internal facts,
  not separately exposed theorems.
- **Proved in this module:** the bound is sharp and attained at
  |0⟩⟨0| tensor |Φ⁺⟩⟨Φ⁺|. The universal upper bound and the existential
  sharpness clause together give the A|BC supremum one half.
- **Open in this formalization:** transport of the conclusion to B|AC
  and C|AB. The paper states those partitions follow by symmetry; this
  module contains no permutation-transport theorem.
- **Open:** property (P6), convexity of E_GHZ, and the GME-witness use for
  mixtures across partitions. This product-density result does not
  discharge the source's conditional use of convexity.
- **Proved consequence for the source's estimate:** the exact bound in
  equation (37) supersedes the coarser triangle estimate (36) for the
  specified A|BC products. It gives an analytic justification of that
  sharp product-density constant; other source conclusions depending
  on convexity remain conditional.
- **Open:** E_GHZ ≤ 1/2 for all fully separable mixtures. A fully separable
  mixture need not be one A|BC density product, so that extension is not
  a consequence asserted by `result`.

## ASSUMED-UNVERIFIED

The search-seat citation counts and corpus checks are source-reported;
the searched scope is not an exhaustive proof of novelty.
Information-escape registration is paused under CLAUDE.md §3.9.
