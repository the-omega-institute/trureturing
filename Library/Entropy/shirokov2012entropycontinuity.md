---
bibkey: shirokov2012entropycontinuity
authors: M. E. Shirokov
year: 2012
title: "On a conjectured property of the von Neumann entropy valid in the commutative case"
doi: null
url: https://arxiv.org/abs/1201.1093v1
claim: "Entropy continuity on a closed convex family is conjectured to imply an all-temperature Hamiltonian energy bound and a common continuous bounded relative entropy reference."
strata_touched:
  - D5/S3/Quantum/Analysis/OrliczCommonEnergy
  - D5/S3/Quantum/Analysis/TraceClass/EntropyMaximizer
  - D5/S3/Quantum/Analysis/TraceClass/ContinuousEnergyHamiltonian
  - D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy
license: citation-only
triage: anchor
---

# Entropy continuity and the scalar Orlicz sufficient condition

## Verified locator

Original conjectures: https://arxiv.org/abs/1201.1093v1

## Original entropy-continuity premises

Shirokov, arXiv:1201.1093v1, Section 3, Conjectures 1 and 2, asks about arbitrary
trace-norm closed convex families of quantum states with finite continuous von
Neumann entropy. Conjecture 1 asks for containment in an energy ball of a positive
Hamiltonian with finite partition function at every positive inverse temperature.
Conjecture 2 asks for a single state whose relative entropy is continuous and
bounded on the family. Neither conjecture assumes commutation of the states.

The related equivalence between continuous logarithmic reference energy and an
all-temperature energy bound is in Shirokov, *Entropic characteristics of subsets
of states*, arXiv:quant-ph/0510073v2, Proposition 4. This is a source for the
mathematical objective, not a claim that the scalar theorem below is stated in
either paper.

For a positive normalized reference sequence s and nonnegative normalized masses
d(x,n), the module uses the actual functions

$$
\Phi_p(t)=t(\log\max(1,t))^p,\qquad
\Psi_p(u)=\sup_{t\ge0}\{ut-\Phi_p(t)\}.
$$

A finite uniform extended Phi moment and finiteness of the actual extended dual
series at every positive scale imply uniform tails of (-log s(n))*d(x,n).
One common monotone natural weight, tending to infinity, preserves these tails
with arbitrarily small additive energy cost. For coordinatewise continuous d on
any topological space, the resulting scalar energy is finite and continuous,
and its Boltzmann series is summable at every positive inverse temperature.
The scalar implication uses p>0; nonvacuous faithful infinite-reference
applications of the every-scale condition use p>1.

This conditional sufficient criterion has stronger premises than entropy
continuity. No universal implication from the original entropy premise to a
fixed logarithmic-power moment is claimed. The spectral, noncommuting trace,
self-adjoint domain and actual heat-trace joins are separate mathematical
obligations. The scalar theorem does not resolve either original conjecture or
establish historical originality.

## Global entropy maximum from the original family premises

`D5/S3/Quantum/Analysis/TraceClass/EntropyMaximizer` works on the actual
trace-class Banach space of any complete complex Hilbert space. Its nonempty,
closed real-convex family consists of positive trace-one operators with finite
actual singular spectral entropy and relatively continuous actual real entropy.
It assumes no energy condition, compactness or entropy bound.

Every state has trace norm one. At a fixed state x, continuity of entropy
relative to the family gives a neighborhood where entropy is below S(x)+1. A single sufficiently small
positive t puts every mixture (1-t)x+ty in that neighborhood, since the state
family has diameter at most two. Nonnegative concavity gives t*S(y)<=S(x)+1
and hence a finite global upper bound. Strong entropy concavity with modulus
one half, completeness of the closed family and upper semicontinuity then
give an actual unique global maximizer gamma and

    norm(rho-gamma)^2/8 <= S(gamma)-S(rho).

The quantitative concavity supplier is attributed in
`Library/QuantumBounds/androulakis2023nussbaumszkola.md`; attainment uses the
standard maximizing-sequence argument in `StrongConcavityAttainment`.
This is a consequence used along the original entropy-continuity route,
not a theorem attributed verbatim to the conjecture paper. No originality,
common-reference energy conclusion or all-temperature Hamiltonian conclusion
is asserted. Separability, commutation and absence of kernel fibers are not
premises of this intermediate result.

## Thermal construction on the original complete Hilbert space

`D5/S3/Quantum/Analysis/TraceClass/ContinuousEnergyHamiltonian` constructs a
Hamiltonian on any supplied complete full spectral basis of a normalized
positive trace-class contraction sigma in a complete separable complex Hilbert
space. For a nonempty compact positive trace-one family A, the conditional
premises are finiteness of actual singular spectralEnergy(sigma,rho) and
continuity of its real value on A. Convexity is not required here.

An injective natural code retains all basis vectors. Set a(i)=-log(s(i)) when
s(i)>0 and a(i)=(code(i)+1)log(2) when s(i)=0. Finite singular energy forces
zero mass on every reference-kernel vector. Only scalar energy terms are
extended by zero to the natural numbers. Dini's theorem for real finite
prefixes supplies uniform extended tails. UniformTailAmplification gives a
natural monotone diverging weight w with both an additive cost bound and
uniform weighted tails. The generic real-series tail theorems in
OrliczCommonEnergy supply actual summability and continuity without their
unrelated stronger moment premises. The Hamiltonian coefficients are
h(i)=1+w(code(i))*a(i) on the original basis.

The dyadic code estimate makes exp(-a(i)) summable. For each beta>0, the
exceptional indices with beta*w(code(i))<1 form a finite set, so the same
Hamiltonian has summable heat coefficients at every positive inverse
temperature. DiagonalHeat and DiagonalEnergy supply its dense full-space
self-adjoint operator domain, full graph and weighted-l2 characterization,
positive trace-class heat and actual complex/real trace HasSum, full strong
generator graph equivalence and semigroup uniqueness, and the lower form
bound by the identity. The actual resolvent-cap mixed-state energy is finite
and continuous in both ENNReal and real values. It equals one plus the
amplified diagonal series and is at most 1+spectralEnergy(sigma,rho)+delta.
Actual trace-one diagonal summation supplies the constant one.

The same module derives the original-premise endpoint. A nonempty closed
real-convex family of positive trace-one states with finite continuous actual
entropy has an entropy maximizer gamma0. Its center-energy inequality embeds
the family in a compact full energy sublevel; closedness then gives
compactness. The existing fullCompactCommonReference yields gamma in A and
sigma in A with finite continuous reference energy bounded by
realEntropy(gamma)+log(2). Applying the new construction to sigma's native
full basis with delta=1 yields the strictly positive finite uniform bound
2+realEntropy(gamma)+log(2). No compactness, bounded entropy or common
reference is assumed in this original-premise endpoint. Separability of the
ambient H is explicit, as in the source conjecture. Singular references,
finite-dimensional H, infinite reference kernels and noncommuting families
are included. No genuine relative-entropy D or Conjecture 2 conclusion
follows merely from the energy continuity statement, and no historical
priority claim is made here.
## Normalized finite-entropy trace-log bridge

`FiniteEntropyRelativeEntropy` defines D only for actual positive trace-one
operators rho and sigma with finite actual spectral entropy of rho. On any
complete complex Hilbert space it uses the liminf of the real trace of
rho times the difference of the bounded CFC logarithms of rho+epsilon I and
sigma+epsilon I, followed by ENNReal.ofReal, at epsilon=1/(n+1).
The proved extended characterization is E_sigma(rho)-S(rho). Finite energy
gives the nonnegative unclamped real value and the lower bound
norm(rho-sigma)^2/4; infinite energy and failed kernel inclusion give infinity.
For arbitrary full spectral resolutions at finite energy, the signed double
logarithmic series is absolutely summable and has the same value. Zero
reference eigenvalues have zero weighted overlap before the real logarithm
convention is used.

The same unit derives a fixed normalized sigma in the original nonempty
closed real-convex family with finite continuous entropy. Entropy attainment
and the center energy bound put the family inside a compact energy sublevel;
closedness gives compactness. The existing compact common-reference theorem
then makes the actual D finite, continuous and bounded by S(gamma)+log(2).
The Hellinger and spectral-distribution suppliers retain the attribution in
`Library/QuantumBounds/androulakis2023nussbaumszkola.md`; the analytic
trace-class suppliers retain Tom Ole Diem's Physlib provenance and license.
This is a formal mathematical implication of the stated premises, without a
claim of historical novelty or present literature openness.
