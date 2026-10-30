---
slug: simic-2018-iterated-moment-minor-inequalities
bibkey: simic2018momentinequalities
doi: 10.1007/s10474-018-0848-1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/MomentMinors/Result.result
url: https://arxiv.org/abs/1509.08519v2
---

# Iterated moment minor inequalities

## Problem

Simić, *Moment inequalities of the second and third order*, §2:

> Conjecture 1 The inequality φ(r₁,s₁;u₁,v₁)φ(r₂,s₂;u₂,v₂) ≥ [(ξ((r₁+r₂)/2,(s₁+s₂)/2) − ξ((r₁+s₂)/2,(s₁+r₂)/2))(ξ((u₁+u₂)/2,(v₁+v₂)/2) − ξ((u₁+v₂)/2,(v₁+u₂)/2)) − (ξ((r₁+u₂)/2,(s₁+v₂)/2) − ξ((r₁+v₂)/2,(s₁+u₂)/2))(ξ((u₁+r₂)/2,(v₁+s₂)/2) − ξ((u₁+s₂)/2,(v₁+r₂)/2))]² holds for arbitrary r_i, s_i, u_i, v_i ∈ I, i ∈ {1, 2}?

With σ_a(x) := ξ(x, x+a) and
θ_a(x,y) := σ_a(x)σ_a(y) − σ_a²((x+y)/2):

> Conjecture 2 Is it true that θ_a(x,y)θ_a(z,v) ≥ [θ_a((x+z)/2,(y+v)/2) − θ_a((x+v)/2,(y+z)/2)]²?

For a positive random variable X with mean m, the definitions are

$$\lambda_s=\begin{cases}
\log m-\mathbb E\log X,&s=0,\\
\mathbb E(X\log X)-m\log m,&s=1,\\
\dfrac{\mathbb E X^s-m^s}{s(s-1)},&s\ne0,1,
\end{cases}\qquad
\xi(s,t)=\lambda_s\lambda_t-\lambda_{(s+t)/2}^2,$$

$$\varphi(s,t;u,v)=\xi(s,t)\xi(u,v)
-\left[\xi\!\left(\frac{s+u}{2},\frac{t+v}{2}\right)
-\xi\!\left(\frac{s+v}{2},\frac{t+u}{2}\right)\right]^2.$$

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.MomentMinors`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Positive probability law of X | `Defs.Admissible μ I` | A Borel probability measure on ℝ, positive almost everywhere, with integrable identity. |
| Moments exist for every s ∈ I | `Defs.Admissible.integrable_rpow` | Integrability of each real power; log X at 0 ∈ I and X log X at 1 ∈ I are separate conditions. |
| Interval I | `I.OrdConnected` | Any order-connected real set, with all needed midpoints still in I. |
| λ_s, including s = 0,1 | `Defs.lam`, `Defs.mean` | Exactly the displayed three-case definition, with m the integral of the identity. |
| ξ, φ | `Defs.xi`, `Defs.phi` | The displayed second and iterated second minors. |
| σ_a, θ_a | `Defs.sigma`, `Defs.theta` | The displaced pair and its midpoint second minor. |
| Conjecture 1 | `Defs.claim1` | All eight endpoint parameters independently range over I, in the quoted index order. |
| Conjecture 2 | `Defs.claim2` | Every real a,x,y,z,v such that x,y,z,v and x+a,y+a,z+a,v+a belong to I. No sign restriction on a. |
| Both assertions | `Defs.claim`, `Result.result` | The conjunction, for every interval and every admissible law. |

## Motivation

The settling declaration is `D5/S3/Analytic/MomentMinors/Result.result`.
The source note is `D5/L/Divergence/simic2018momentinequalities`.
Both inequalities refine the nonnegativity of moment minors by controlling
cross terms from independently chosen parameter pairs.

## Gap

Status: **Proved** for every admissible law and all parameters in the stated
interval. The logarithmic cases, repeated parameters, vanishing minors and
negative displacements are included.

## Route

Set K(s,t) = λ_{(s+t)/2}. For s different from zero and one, use

$$f_s(x)=\frac{x^s-sx+s-1}{s(s-1)}.$$

At zero and one use f_0(x) = x−1−log x and f_1(x) = x log x−x+1.
In every case f_s''(x) = x^{s−2} on x > 0 and
λ_s = E f_s(X)−f_s(E X). For any finite family t_i ∈ I and real c_i,

$$F(x)=\sum_{i,j}c_ic_jf_{(t_i+t_j)/2}(x),\qquad
F''(x)=\left(\sum_i c_i x^{t_i/2-1}\right)^2\ge0.$$

The mean m is positive. Integrating the supporting tangent inequality
F(m)+F'(m)(x−m) ≤ F(x) gives
Σ_{i,j} c_i c_j λ_{(t_i+t_j)/2} ≥ 0. All potentials are integrable
by the given moment assumptions; no derivative integrability is needed.
Thus every finite matrix of K is positive semidefinite.

For a finite positive semidefinite real matrix A and arbitrary ordered
index pairs (p(a),q(a)), put

$$C_{ab}=A_{p(a)p(b)}A_{q(a)q(b)}-A_{p(a)q(b)}A_{q(a)p(b)}.$$

Let T have column e_{(p(a),q(a))}−e_{(q(a),p(a))}. Then
C = Tᵀ(A⊗A)T/2, so C is positive semidefinite. For K this gives

$$B((r,s),(u,v))=
\xi\!\left(\frac{r+u}{2},\frac{s+v}{2}\right)
-\xi\!\left(\frac{r+v}{2},\frac{s+u}{2}\right).$$

The two central squared λ terms cancel because their arguments agree.
The diagonal is ξ(r,s). Applying the same construction to B on the four
pairs (r₁,s₁),(u₁,v₁),(r₂,s₂),(u₂,v₂), and taking its two by two determinant,
gives Conjecture 1. Restricting B to pairs (x,x+a) gives the midpoint
kernel σ_a((x+y)/2). Its second minors and their two by two determinant
give Conjecture 2; the two central squared σ terms again cancel.

The same construction continues to every finite depth in prose:
start with K_0 = K and define
K_{n+1}((r,s),(u,v)) = K_n(r,u)K_n(s,v)−K_n(r,v)K_n(s,u).
Induction gives positive semidefiniteness of every finite restriction:
at each stage collect the finitely many endpoints and apply the arbitrary-pair
lemma. Its principal two by two determinants give further inequalities.
This induction is not asserted as an additional Lean theorem.

For finite strictly positive probability vectors p and q, let X take p_i/q_i
with probability q_i. Then E X = 1, every real power and both logarithmic
moments are integrable, and

$$\lambda_s=\frac{\sum_i p_i^s q_i^{1-s}-1}{s(s-1)}\quad(s\ne0,1),\qquad
\lambda_0=D(q\Vert p),\quad\lambda_1=D(p\Vert q).$$

These are the f-divergences for generators f_s above, since the affine
terms have zero expectation. Substitution in the two inequalities gives
inequalities among these divergences, including the two relative entropies.
This discrete correspondence is a consequence in prose, not an additional
Lean theorem.

## Falsifier

An admissible law and eight parameters in its interval violating Conjecture 1,
or an admissible law and a,x,y,z,v satisfying all eight endpoint conditions
but violating Conjecture 2, would contradict the statement. Laws lacking
the specified integrability or positivity conditions are outside its scope.

## Evidence

`D5/S3/Analytic/MomentMinors/Result.result` proves exactly `Defs.claim`,
without additional premises. Its principal dependencies are
`MomentKernel.momentKernel_posSemidef` and `PairMinor.pairMinor_posSemidef`.
The former integrates a supporting tangent for a finite quadratic combination
of the normalized power potentials. The latter applies
`Matrix.PosSemidef.kronecker`,
`Matrix.PosSemidef.conjTranspose_mul_mul_same` and nonnegative scaling.
Successive specializations and `Matrix.PosSemidef.det_nonneg` with
`Matrix.det_fin_two` give the two conjuncts.
The axiom closure of `Result.result` is
`{propext, Classical.choice, Quot.sound}`.

The proof route was derived with the assistance of the ChatGPT Pro model.
The source proves φ ≥ 0, log-convexity of σ_a and restricted three- and
four-parameter cases of Conjecture 1. The journal version states the
eight-parameter refinement as an open problem. No settlement was found in
the supplied literature scope: the arXiv versions, the titles, identifier,
DOI and author in conjunction with conjecture, proof and counterexample,
and the OpenAlex citation record. The identified citing work by Sason
concerns lower-order f-divergence refinements. This scope does not establish
exhaustive citation-index coverage or priority.

## Triage

- **PROVED.** Conjectures 1 and 2 for every admissible law and all parameters
  in I, by `Result.result`.
- **PROVED.** The moment kernel (s,t) ↦ λ_{(s+t)/2} is positive semidefinite
  on every finite family in I, by `MomentKernel.momentKernel_posSemidef`.
- **PROVED.** Matrices of two by two minors of a positive semidefinite real
  matrix along arbitrary index pairs are positive semidefinite, by
  `PairMinor.pairMinor_posSemidef`.
- **PROVED in prose.** Iteration to every finite depth preserves positive
  semidefiniteness, by induction using the arbitrary-pair construction.
- **PROVED in prose.** The finite discrete specialization X = p_i/q_i under
  q gives inequalities among f-divergences, with λ_0 and λ_1 equal to the
  reverse and forward relative entropies, respectively, as derived above.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. Independent external-source confirmation of the supplied
bounded literature findings is unverified.
