---
slug: cullinan-young-2026-krawtchouk-sign-leading-coefficient-remark-8
bibkey: cullinanyoung2026krawtchouk
doi: 10.1007/s10958-026-08499-9
url: https://arxiv.org/abs/2603.05408v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.result
---

# Cullinan–Young Remark 8 leading coefficient

## Problem

J. Cullinan and E. Young, *The Gibbs phenomenon for the Krawtchouk polynomials*,
arXiv:2603.05408v1, Remark 8, state that numerical experimentation suggests
that for even $N$ the leading coefficient of the sign interpolant $I_N$ is

$$(-1)^{(N-2)/2} C((N-2)/2)/(N-1)!,$$

where $C(n)$ is the $n$th Catalan number. Section 2 defines

$$I_N(x)=\sum_{i=0}^{N}\operatorname{sgn}(i-N/2)\ell_i(x),qquad
\ell_i(x)=\prod_{0\le j\le N,\,j\ne i}\frac{x-(j-N/2)}{i-j}.$$

The settling declaration is `D5.S1.Recurrence.Interpolation.CullinanYoungKrawtchouk.result`.

### Statement echo

The source nodes $j-N/2$, signs, products, sums, and the even case are literal
in `ell`, `I`, and `claim`. The Lean proposition quantifies $N\in\mathbb N$,
assumes $2\le N$ and `Even N`, and equates
`Polynomial.leadingCoeff (I N)` with the rational Catalan expression using
`Nat.div` and `Nat.factorial`. The source's Proposition 6 identification
$F_N=I_N$ is outside this claim.

## Motivation

The observation gives an exact degree-leading-term formula for the interpolant
used in the paper's Fourier–Krawtchouk approximation. A proof replaces the
source's numerical suggestion with a uniform result for every even $N\ge2$.

## Gap

Remark 8 labels the formula a numerical suggestion. The journal version is
paywalled; the accessible arXiv version, Section 2, Propositions 6–7 and
Remark 8 were read. Searches recorded in issue #19000 found no later proof or
refutation in the searched repository, arXiv, journal, MathDB, or
`google-deepmind/formal-conjectures` surfaces. Literature completeness is
`ASSUMED-UNVERIFIED`.

## Route

For $N=2m$, the denominator of the $i$th Lagrange basis is
$(-1)^{2m-i}i!(2m-i)!$. Reflection $i\mapsto2m-i$ cancels the coefficient of
$x^{2m}$. Since the centered nodes sum to zero, the next coefficient is the
signed sum of omitted nodes divided by those denominators. Pairing reflected
indices reduces it to a partial alternating binomial sum. The partial-sum
identity gives a central binomial coefficient, and
$C_{m-1}=\binom{2m-2}{m-1}/m$ gives the stated Catalan form.

## Falsifier

An even $N\ge2$ with a different leading coefficient, a nonzero top
coefficient, or a failure of the partial alternating sum identity would falsify
the settlement. Odd $N$ is outside Remark 8 and is not tested by this module.

## Evidence

The kernel-checked source is
`D5/S1/Recurrence/Interpolation/CullinanYoungKrawtchouk.lean`.
`result : claim` is the settling theorem; its proof uses the private denominator,
reflection, coefficient, alternating-sum, and Catalan helpers on its live path.
The module imports Mathlib's Lagrange interpolation, Catalan, sign, big-operator,
and linear-combination declarations and introduces no additional axiom.
The axiom closure is contained in `{propext, Classical.choice, Quot.sound}`.
The escape audit for the public settling theorem is unfinished under
[issue #19833](https://github.com/the-omega-institute/trureturing/issues/19833);
no `declared_validated` registration is claimed.

The independent exact computation is in
[`trureturing-experiments`](https://github.com/the-omega-institute/trureturing-experiments/tree/f00cf5ceabe4d97ff43ebc40a26e257d82b9818a/docs/reports/cullinan-young-2026-krawtchouk-leading-coefficient)
at commit `f00cf5ceabe4d97ff43ebc40a26e257d82b9818a`. Its `check.py` has
SHA-256 `f9de4a5469c851f9712117259ca851190a8fa55ccc121d3f71c0610a604b03c5`.
`python3 check.py` exits 0 with `RESULT PASS` for even $N=2,4,\ldots,40$,
checking degree $N-1$ and the stated leading coefficient.

## Triage

| item | status | evidence |
| --- | --- | --- |
| Settlement under the exact binding Lean conventions | proved | Lean `result` |
| Mechanism: Vieta next coefficient, reflection cancellation and pairing, partial alternating sums, central binomial and Catalan identities | proved | Lean `leading_even`, `I_pred_catalan`, `I_pred_sum`, `weighted_sum`, `I_top_zero` |
| Least case $N=2$ without negative binomial lower indices | proved | Lean `result` and `leading_even 0` |
| Degree $\operatorname{natDegree}(I_{2(m+1)})=2(m+1)-1$ | proved | Lean local `hd` in `leading_even`, using `I_degree_le`, `I_top_zero`, and the nonzero coefficient from `I_pred_catalan` |
| Equality $F_N=I_N$ from source Proposition 6 | open | source statement; not a theorem in this module |
| Odd $N$ | open | outside the even-$N$ source observation |

### What the settlement shows

The proved identity extends the numerical suggestion to all even $N\ge2$ and
also proves the exact degree $N-1$. Proposition 6 of the source then gives the
same coefficient for $F_N$ as a literature consequence; that identification is
not re-proved here. The proof depends on symmetry of the centered nodes and the
alternating binomial sum, and does not address the half-integer-node odd case.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain `ASSUMED-UNVERIFIED`; the paywalled
journal PDF was not read. The experiment covers only even $N\le40$ and is
supporting evidence rather than the uniform formal proof.
