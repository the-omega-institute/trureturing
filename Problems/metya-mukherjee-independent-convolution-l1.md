---
slug: metya-mukherjee-independent-convolution-l1
bibkey: metya2026uniformity
doi: 10.48550/arXiv.2609.38243
triage: theorem
motivation_gids:
  - D5/S3/TotalVariation/IndependentConvolutionL1Minimum.result
---

# Metya–Mukherjee's exact independent-convolution L1 minimum

## Problem

Nilava Metya and Satyaki Mukherjee, *Approximate Uniformity in Finite
Convolution Models*, arXiv:2609.38243v1, §4.3,
[Conjecture 4.7](https://arxiv.org/html/2609.38243v1#S4.Thmlemma7), states:

> The optimal value of (21) is (2n−1)⁻¹ for n≥3.

The source declares [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
The quotation and mathematical source correspondence here are attributed to
that version under the same license. The proof below is a repository
formalization of the sharp bound.

Equation (21) minimizes the full L1 norm of the deviation from uniform over
ordinary convolutions of two independent probability vectors. For every
natural n≥3 and real closed-simplex vectors p,q on Fin n, put

\[
r_k=\sum_{i,j<n,\ i+j=k}p_iq_j,\qquad t=\frac1{2n-1}.
\]

The exact target is that t is the least member of the set of all
\(\sum_{k=0}^{2n-2}|r_k-t|\) obtained from these legal pairs. Both factors
range over the whole real closed simplex. They may be unequal, asymmetric,
irrational or have zero entries. Addition is ordinary natural addition.

## Motivation

The source separates this L1 objective from its squared-L2, relative-entropy
and line-Wasserstein objectives. Equation (22) gives an attaining family,
but its matching universal L1 lower bound is stated as Conjecture 4.7.
The attaining family is a published supplier; its formal verification does
not by itself establish the minimum.

## Gap

[Preregistration #11735](https://github.com/the-omega-institute/trureturing/issues/11735)
records the original complete target, tier-one classification and bounded
source and literature readings before the mathematical probe. The recorded
readings include the primary v1 and Asgarli–Hartglass–Ostrov–Walden,
Kovačević and Klich at the versions identified there. Their inspected
conclusions were not the full sharp L1 result. The source's Theorem 4.6 is
about line-Wasserstein distance. No exact L1 resolution was identified in
those inspected surfaces; this does not assert worldwide absence or
publication priority. Inaccessible surfaces and uninspected cited dice
papers remain within the boundaries stated in the preregistration.

The concrete Lean supplier search found no matching sharp theorem in D5 or
the pinned Mathlib. The proof uses Mathlib's real simplex, finite sums,
trigonometric identities, power-order estimates and intermediate value
theorem. Its model does not use rational finite laws or descending-factorial
convolution coefficients.

## Route

Write m=n−1≥2 and θ=π/m. A zero actual output coefficient immediately gives
one deviation equal to t. In the remaining branch every r_k is positive.
For the actual generating product R=PQ, pairing indices j and m+j in
F(s)=Im R(s exp(iθ)) gives positive constants A,B and the bounds

\[
F(s)\ge s^m(A-Bs)\ (0<s\le1),\qquad
F(s)\le s^m(A-Bs)\ (s\ge1).
\]

The choices a=min(1,A/(2B)) and b=max(1,2A/B) give F(a)>0>F(b).
Continuity and the intermediate value theorem supply a positive crossing.
Nonnegative input coefficients give nonnegative imaginary parts of both
factors on this ray. Positivity of the actual r_1 forces a strictly positive
imaginary part of at least one factor. The complex product identity then
gives Re R≤0 at Im R=0. A crossing need not be a root.

At a crossing radius 0<ρ≤1 use

\[
b_k=\rho^k\left(\cos(k\theta)+
\frac{1-\rho\cos\theta}{\rho\sin\theta}\sin(k\theta)\right).
\]

The proof establishes |b_k|≤1, Σb_k≥1 and Σb_kr_k=Re R≤0. These imply
Σ|r_k−t|≥t. When ρ>1, reverse only the output coefficient vector at width
2m+1. Its evaluation at ρ⁻¹ exp(iθ) is
ρ⁻²ᵐ conjugate(R(ρ exp(iθ))), and the full L1 sum is preserved by the
fixed-width permutation. No degree-based reversal or replacement of the
product optimization is used.

For attainment take the parameter-one member of the source's equation (22):
p_0=p_m=1/2, all other p_j=0, q_0=t and q_j=2t for j>0. Both vectors are
legal simplex members. Their ordinary output is r_0=t/2, r_m=3t/2 and
r_k=t at all other output indices. Thus their full L1 value is t. This
membership and the universal bound are the two parts of the least-element
statement.

## Falsifier

A source-model mismatch, a legal pair whose exact full L1 error is less
than t, or a failure of simplex membership or the stated output of the
attaining pair would invalidate the claimed source-level resolution. An
arbitrary coefficient vector or arbitrary coupling with smaller error is
not a counterexample to this product-law target.

## Evidence

The single public resolution is
`D5/S3/TotalVariation/IndependentConvolutionL1Minimum.result`.
`ordinaryConvolution` and `fullL1` define its exact objective and indices.
Two local substantive proof blocks supply the actual-product crossing and
the nonpositive-real coefficient certificate; reversal and attainment are
local parts of the result proof. The canonical Lean sources use only the
accepted axioms `propext`, `Classical.choice` and `Quot.sound`.

The resolution's admission basis is `open-problem-resolution` under the
preregistered external named question. Proof shape, utility and literature
eligibility are separate obligations. The general real-parameter argument
is not a positive finite enumeration or a numerical reduction. The published
attainment family is credited to the source, and no equality classification
or global novelty claim is made.

## Triage

The full quantified least-element statement includes attainment and the
universal lower bound. The decisive lower-bound structure is a nonpositive
real crossing of the actual independent product followed by a finite dual
certificate. The certificate also applies conditionally to arbitrary real
coefficient vectors at the fixed width; that auxiliary observation does not
change the optimization domain of the resolution.

The theorem does not classify all minimizing pairs, cover n=2, treat
unequal input widths or minimize a different distance. Those are separate
questions. No source result depending on the conjecture is promoted beyond
the stated least-element conclusion.

## ASSUMED-UNVERIFIED

The bounded literature reading is not an exhaustive known-result exclusion.
Source fidelity and per-declaration admission require independent review.
Freeze, final admission checks and publication are separate from the Lean
proof. This dossier asserts no completed repository publication lifecycle.
