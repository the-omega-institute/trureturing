---
slug: marin-conjecture-8-1
bibkey: marin2026twistedschur
doi: 10.48550/arXiv.2608.18302
url: https://arxiv.org/abs/2608.18302v2
triage: theorem
motivation_gids:
  - D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.result
---

# Marín Conjecture 8.1: a twisted Schur Newton polytope with competing maxima

## Problem

Carles Marín, *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*, arXiv:2608.18302v2, §8, Conjecture 8.1, p. 49, states:

> If $\Phi_{t,r}\neq0$ then $\{\mu:A_\mu\neq0\}$ has a unique maximal element $\mu_{\max}$ for the Weyl majorisation order $\mu\preceq\mu'\iff\mu\in\mathrm{conv}\bigl(W(C_r)\mu'\bigr)$; equivalently, $\mathrm{Newt}(\Phi_{t,r})$ is the orbit polytope $\mathrm{conv}\bigl(W(C_r)\mu_{\max}\bigr)$.

Here $t,r\ge1$, $N=t+2r$, $\beta\in\mathbb Z^N$ is strictly decreasing with final entry zero, $\delta=(N-1,\ldots,0)$, and the alphabet is $(1,\zeta,\ldots,\zeta^{t-1},z_1,z_1^{-1},\ldots,z_r,z_r^{-1})$ with $\zeta=\exp(2\pi i/t)$. The source defines $\Phi$ by the quotient of the alternants at $\beta$ and $\delta$. Its folded coefficient-support convention uses $W(C_r)$-dominant weights in both parity branches. This settlement addresses the source's explicitly equivalent Newton-polytope assertion.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $t,r\ge1$, $N=t+2r$ | `claim` quantifies natural `t,r` with both lower bounds; `N` | Same parameter range. |
| The ordered root orbit and reciprocal pairs | `sourceIndex`, `alphabetPower` on `Fin t ⊕ (Fin r ⊕ Fin r)` | The root exponential is literal; free inverse powers are negative Laurent exponents. |
| Strictly decreasing $\beta$, final entry zero; $\delta=(N-1,\ldots,0)$ | `NormalizedBeta`, `delta` | Integer subtraction; strict source-order comparison and explicit final-zero condition. |
| $\Phi=\det(x_i^{\beta_j})/\det(x_i^{\delta_j})$ | `numerator`, `denominator`, `IsPhi` | Nonzero formal denominator and cross-multiplied equality; the claim also asserts existence of the Laurent quotient. |
| $\Phi\ne0$ | The nonzero antecedent in `claim` | No empty-support counterexample. |
| Ordinary Newton polytope | `newtonPolytope` | Real convex hull of integer exponents with nonzero complex coefficient. |
| One $W(C_r)$ orbit hull with dominant integral generator | `signedOrbit`, `orbitPolytope`, `Dominant`; conclusion of `claim` | Every coordinate permutation and independent sign choice; nonnegative antitone integral generator. |
| Universal assertion is false | `result : ¬ claim` | Certified seed at $t=3,r=2$, with a nonzero quotient and denominator. |

The literal exponential in the public alphabet is connected inside the proof to the existing `D5.S3.Arith.InterlaceFan.Cyclotomic.zeta` by the private consumed `literal_zeta` equality. No replacement root convention is assumed. The additional quotient-existence conjunct expresses the source object and is satisfied by the refuting instance; the contradiction uses the geometric conjunct.

## Motivation

Signed-permutation symmetry alone allows several incomparable dominant vertices. A hull with two different maximizing vertices inside one Weyl chamber cannot be the hull of a single dominant orbit. The fixed rank-two seed suffices to refute the universal conjecture.

## Gap

The source explicitly labels the numerator and quotient single-orbit assertions as conjectural in §7. Its denominator proposition is a separate result. The literature screen in [#26737](https://github.com/the-omega-institute/trureturing/issues/26737) found no settlement within its inspected scope; global completeness remains ASSUMED-UNVERIFIED.

## Route

Use $t=3$, $r=2$ and $\beta=(10,9,5,4,2,1,0)$. The private declarations `base_normalized`, `denominator_ne`, `base_identity` and `base_isPhi` certify admissibility and the literal alternant quotient. `base_support` identifies its 33-element coefficient support. The proof reuses `Cyclotomic.zeta` through its direct D5 import. The private `zeta_cube` applies `Complex.isPrimitiveRoot_exp`; determinant and convex-hull operations use pinned Mathlib.

The exact coefficient polynomial has signed-orbit expansion

$$
F_1=m_{4,0}+m_{3,3}+2m_{3,1}+m_{3,0}+3m_{2,2}+4m_{2,0}+6m_{1,1}+10,
$$

where $m_{a,b}$ is the sum of distinct Laurent monomials at signed permutations of $(a,b)$. The complete coefficient table is represented by `basePolynomial`; this expansion is mathematical exposition of that table.

## Falsifier

The kernel-checked private `base_bounds` states that each $x$ in the seed Newton polytope satisfies

$$x_0\le4,\qquad x_0+x_1\le6,\qquad 3x_0+x_1\le12.$$

The kernel-checked private `base_vertices` places $(4,0)$ and $(3,3)$ in that polytope. If it were one dominant signed-permutation orbit hull, `dominant_mem` and `orbit_bounds` force its generator to be $\mu=(4,2)$. Its value at the third objective would be $3\cdot4+2=14>12$. The private `base_not_orbit` establishes the contradiction; public `result` applies it to the universal claim.

## Evidence

`D5.S3.Geometry.NewtonPolytopes.TwistedSchurSingleOrbitRefutation.result` refutes the closed proposition `claim`. Generality is `I`; admission is `open-problem-resolution (#26737; Refuted)`. All auxiliary proofs are private, consumed bind-only declarations, and no supporting module is first-frozen by this delivery. The only direct D5 import is `D5.S3.Arith.InterlaceFan.Cyclotomic`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact experiment

The independent checker is [the-omega-institute/trureturing-experiments at aa6761d8becd5bc2024b815be3802ffc7eb5672b](https://github.com/the-omega-institute/trureturing-experiments/tree/aa6761d8becd5bc2024b815be3802ffc7eb5672b/docs/reports/marin-2608.18302-conjecture-8.1), file `check.py`. Its SHA-256 is `b372928cfc6a6c660f1c2952be2af727dc66fde5da48d887608be4961573aa8f`. The command `python3 /Users/auric/.op-scratch/op/marin2608c81/stageb/check.py` executes the verified bytes of that immutable file with SymPy 1.14.0; exit 0 and `ALL_CHECKS_OK`.

The checker reconstructs the elementary coefficients and dual Jacobi–Trudi determinant, compares the 33-term Laurent expansion with the literal alternant product, computes the integer hull, checks signed-permutation invariance, and reproduces the denominator hull. For each of exactly $s=1,4,7$, it verifies the numerator dilation identity, three exact rational evaluations and 90 chamber directions. It does not quantify over all $s$.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Coordinate maximum $4$ and sum maximum $6$ force $\mu=(4,2)$, contradicting the bound $3\mu_0+\mu_1\le12$; support includes $(4,0),(3,3)$ | **Proved, kernel-checked:** private `base_support`, `base_bounds`, `base_vertices`, `base_not_orbit`, consumed by public `result`. |
| Eight-vertex hull $\mathrm{conv}(W(4,0)\cup W(3,3))$ and signed-permutation invariance | **Computed:** exact experiment above, exit 0, same script SHA-256; tested seed $s=1$. The full hull equality and symmetry are not separate Lean theorems. |
| Denominator hull $\mathrm{conv}W(6,4)$ | **Computed:** exact experiment above, exit 0, same script SHA-256. The source denominator proposition is not refuted. Lean certifies the seed denominator is nonzero, not its full hull equality. |
| Exposed pairs $(34,12),(30,24)$ for $s=4$ and $(64,24),(57,45)$ for $s=7$ | **Computed:** exact experiment above, exit 0, same script SHA-256; 90/90 chamber directions and 3/3 exact evaluations for each sampled $s$. |
| A Lean proof for every $s=3k+1$, with Newton additivity, dilation and cancellation | **Open:** no infinite-family Lean assertion is delivered. |
| Conjecture 8.2, sufficient extra conditions for one orbit, the full zero locus and an independent general justification of formula (26) | **Open:** the fixed seed does not settle these questions. |

The failure mechanism is disagreement between two maximization objectives inside one Weyl chamber. The finite computations preserve signed-permutation invariance and the denominator's orbit property, so those properties do not force the conjectured conclusion. The source's §7 deduction of a single dominant quotient vertex cannot be used generally through Conjecture 8.1; its independent denominator proposition is unaffected. Formula (26) requires a separate justification wherever its use depended on that conjecture.

### Literature status

The source and literature inventory is stated in the cited Library note and #26737. It includes the source version, rank-one companion, later author manuscript, classical Schur specializations, author Zenodo inventory, citation indices, MathOverflow and public Lean settlement indices. No settlement was found in those inspected sources. The classical hypotheses inspected there do not match the frozen $t=3$ root orbit plus two free reciprocal pairs. Global completeness is ASSUMED-UNVERIFIED: unindexed work, comprehensive global arXiv body-text coverage, general web/MathDB coverage and later index freshness are not established.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The exact experiment is finite evidence at $s=1,4,7$, separate from the kernel-checked seed refutation; it establishes no uniform infinite-family theorem. Automatic theorem-owner discovery is bounded and is not a completeness certificate. No originality claim beyond the inspected literature scope, no settlement of Conjecture 8.2 and no full zero-locus classification is made.
