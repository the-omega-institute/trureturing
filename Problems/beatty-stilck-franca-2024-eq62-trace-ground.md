---
slug: beatty-stilck-franca-2024-eq62-trace-ground
bibkey: beatty2025couplingwasserstein
doi: 10.1007/s00023-025-01557-z
url: https://arxiv.org/abs/2402.16477v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.result
---

# Equality in Beatty–Stilck França Eq. (62) for the order-one trace ground

## Problem

The paragraph after Eq. (62) in E. Beatty and D. Stilck França,
*Order p quantum Wasserstein distances from couplings* (arXiv:2402.16477v2),
asks when its dual-norm lower bound is attained. The
[preregistered specialization](https://github.com/the-omega-institute/trureturing/issues/35123)
uses order one, the pure-state trace ground of Eq. (81), and the infimum
over finite or countable plans from Definitions 8–9. Proposition 26 and
Eq. (82) identify the lower bound in this setting with half the trace
norm. Equation (62) poses a wider question for other grounds.

For every finite complex dimension $n\ge1$ and every pair of positive
semidefinite trace-one matrices $\rho,\sigma$, let $\Delta=\rho-\sigma$
and let $E_+,E_-$ be its strictly positive and strictly negative spectral
subspaces. Write $P_z=zz^*$ for a unit vector $z$. The equality
$W_1^d(\rho,\sigma)=\|\Delta\|_1/2$ holds exactly when there exist
one positive semidefinite matrix $R$, a natural $m$, and families
$w_i>0$, $0<t_i\le1$ and unit vectors $u_i\in E_+$ and $v_i\in E_-$
indexed by $\mathrm{Fin}\,m$ with both identities
$$
\rho=R+\sum_i w_iP_{a_i u_i+b_i v_i},
\qquad
\sigma=R+\sum_i w_iP_{b_i u_i+a_i v_i},
\quad
a_i=\sqrt{(1+t_i)/2},\quad b_i=\sqrt{(1-t_i)/2}.
$$
The square roots are real, and every amplitude and weight acts through its
complex embedding. Each moving pair shares its vectors between the two
projectors. Equal marginals admit $m=0$ and $R=\rho$.

## Motivation

Strictness at order one can depend on the two marginals even when their
difference stays fixed. The earlier qutrit triangle refutation supplies a
strict pair for Eq. (62), while its dephased pair attains the lower bound
with the same difference. The certificate describes equality by retaining
the two marginal equations together with a common spectral test. The
versioned source and locators are in the
[literature note](../Library/Convexity/beatty2025couplingwasserstein.md).

## Gap

The primary paper gives pure–pure equality in Proposition 24(2) and finite
attainment in Proposition 16. Borsoni (arXiv:2512.01722v5, §3.3.3 and
Proposition 3.10)
gives a convex-roof representation and a finite optimizer. The checked
sections of Miller (arXiv:2609.03769v2), Tóth–Pitrik
(arXiv:2605.03027v3) and Beatty's survey (arXiv:2506.09794v1)
address related choices of order and ground. The bounded source screen
found no all-pairs shared-phase classification for this specialization.

## Route

The formal ground uses the square root in Eq. (81) on unit-vector
representatives of pure rays. Plans retain both matrix-valued sums and
summable nonnegative weights. Removing zeros, or enumerating and padding
by zeros, preserves both marginals and the real cost sum. The trace of
one marginal gives the mass normalization. The cost infimum retains all
such countable plans. A spectral product plan gives nonemptiness.
Finite partial sums with the residual mass on a fixed pair put the joint
moment of each countable plan in the compact convex hull of pure-pair
moments. Minimizing the cost on its fixed-marginal slice yields a finitely
supported plan at the same infimum.

The Hermitian sign $H=\operatorname{sgn}(\Delta)$ supplies both positive
semidefinite tests $I-H$ and $I+H$ and attains the trace norm in
$\operatorname{Re}\operatorname{Tr}(H\Delta)$. The slack of a distinct
pure pair with ground $t$ splits as $t/2$ times the two quadratic forms
of these tests on orthonormal vectors. At equality the forms vanish,
forcing the vectors into the strict spectral subspaces with the same
amplitudes in swapped order. Summing the nonnegative slacks in a finite
optimizer forces saturation on each positive-weight entry. Combining its
stationary terms produces the same $R$ for both marginals. Conversely,
split $R$ into stationary spectral terms and append the moving pairs.
Their phase and amplitude conditions give exactly the required ground and
zero slack. Taking the trace of the first marginal gives total mass one.
The resulting plan attains the sign lower bound for the original infimum.

## Falsifier

A density pair that attains the bound and admits no such decomposition,
or a valid two-marginal decomposition with a strictly larger cost
infimum, refutes the equivalence. A fixed-phase test distinguishes the
conditions on the shared vectors. With $H=\operatorname{diag}(1,-1)$,
the source $(4/5,3i/5)$ and target $(3/5,4i/5)$ have ground and test
pairing $7/25$. Changing the target to $(3/5,-4i/5)$ changes the ground to
$1$ while keeping the pairing $7/25$.

## Evidence

The terminal declaration is
D5/S3/Quantum/QuantumChannels/CouplingWassersteinEquality.wasserstein_eq_traceNorm_iff.
It ranges over all finite dimensions at least one and both complex
positive semidefinite trace-one marginals. Its two sides use the original
countable-plan infimum and the predicate HasSpectralCertificate on the
two marginals with the Hermitian proof of their difference. The matching
Scribe displays the two marginal equations and their scalar embeddings.

## Triage

Tier 1 published equality question, specialized and preregistered in
[#35123](https://github.com/the-omega-institute/trureturing/issues/35123).
The classified scope is order one with the pure-state trace ground.

## ASSUMED-UNVERIFIED

The literature comparison is limited to the versions and sections cited
above and in the preregistration. Priority and the absence of an
equivalent result elsewhere remain unverified.

The source correspondence is checked at Definitions 8–9, Proposition 23
and Eq. (62), and Proposition 26 and Eqs. (81)–(82). The Lean result
uses the countable-plan encoding and the half trace norm in the
order-one trace-ground setting. A machine-checked link from the paper
text to those definitions is outside the evidence of the theorem.
Equality for other grounds or orders remains outside this classification.
