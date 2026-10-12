---
slug: ghosh-ramachandran-2026-capacity-one-decay-rate
bibkey: ghosh2026erdos
doi: 10.1090/proc/17897
url: https://arxiv.org/abs/2604.03036v3
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.result
---

# Ghosh–Ramachandran's capacity-one area decay question

## Problem

S. Ghosh and K. Ramachandran, *A note on the Erdős minimal area problem*,
arXiv:2604.03036v3, beginning of Section 4:

> This shows that while $\vartheta(K)=0$ may hold for all compacts $K$ with $\mathrm{cap}(K)=1$, the decay rate of $A_n(K)$ is not universal. It will be interesting to determine whether $A_n(K)$ can only decay like $\frac1n$ or $\frac1{\log n}$, or whether other rates are possible.

For compact $K\subseteq\mathbb C$, let $P_n(K)$ consist of the monic
degree-$n$ polynomials whose zeros all lie in $K$. Write
$\Lambda_p=\{z:|p(z)|<1\}$ and
$A_n(K)=\inf_{p\in P_n(K)}m(\Lambda_p)$, where $m$ is planar Lebesgue
measure. The paper defines capacity as logarithmic capacity,
equivalently the transfinite diameter.

The Lean `claim` says that for every nonempty compact $K$ of transfinite
diameter one, the real-valued minimal-area sequence is either
$\Theta(1/n)$ or $\Theta(1/\log n)$ as $n\to\infty$.
Thus `result : ¬ claim` refutes the proposed two-rate restriction.

## Motivation

The closed unit disc and $I=[-2,2]$ both have capacity one. The text
preceding the question cites a lower bound of order $1/\log n$ for the
disc, whereas Theorem 4.1 proves $A_n(I)\leq c_1/n$.
Lemma 4.6 gives period-$d$ sets with upper bounds of order $n^{-1/d}$
along multiples of $d$, without claiming these bounds are sharp.
The declaration
`D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.result`
exhibits a capacity-one compact whose minimal area has neither of the
two proposed asymptotic orders.

## Gap

The literature readings identify arXiv:2609.06050 as treating
$\vartheta(K)=0$ for capacity-one sets and explicitly giving no rate
of decay. arXiv:2606.17097 concerns the disc and circle at order
$1/\log n$. arXiv:2503.18270 does not treat isolated points.
No answer to the Section 4 question was found in these readings.
The source note is `Library/Geometry/ghosh2026erdos.md`.

## Route

Take $K=\overline{\mathbb D}\cup\{4\}$. For $s\geq2$, roots of unity
in $K$ have Vandermonde product $s^{s/2}$. Every $s$-tuple in $K$ has
Vandermonde product at most $s!\,4^s\leq(4s)^s$: a repeated entry
gives zero, and for an injective tuple at most one entry is $4$, so
each term in the Vandermonde determinant has modulus at most $4^s$.
Consequently its $s$-point diameter satisfies

$$
1\leq d_s(K)\leq
\exp\!\left(\frac{2(\log4+\log s)}{s-1}\right)\longrightarrow1.
$$

Use the monic competitor
$p_{N,k}(z)=(z^N-1)(z-4)^k$, of degree $N+k$, with all roots in $K$.
For $k\geq2$ and $N\geq k(k-2)+1$, its unit lemniscate is contained in

$$
\{z:1-2^{-k}<|z|<1+2^{-k}\}
\ \cup\ \{z:|z-4|<2^{-(k-2)}\}.
$$

The annulus has area $4\pi2^{-k}$ and the disc has area
$16\pi2^{-2k}\leq16\pi2^{-k}$. Setting $N=k^2+1$ therefore gives
the exact Lean bound

$$
A_{k^2+k+1}(K)\leq20\pi2^{-k}\qquad(k\geq2).
$$

## Falsifier

The compact $K=\overline{\mathbb D}\cup\{4\}$ is nonempty and has
transfinite diameter one. Along $n=k^2+k+1$, the displayed area bound
gives $nA_n(K)\to0$. It rules out an eventual positive lower bound of
order $1/n$. Since $1/n=O(1/\log n)$, it also rules out an eventual
positive lower bound of order $1/\log n$. Hence neither proposed
$\Theta$ order holds. A subsequence bound suffices for this refutation;
an all-degree sharp estimate is not needed.

## Evidence

The committed Lean module defines `pointDiameter`,
`TransfiniteDiameterOne`, `minimalArea` and `claim`. Its only public
theorem is `result : ¬ claim`. The private proofs `pointDiameter_bounds`
and `diameter_one` establish the capacity condition; `competitor_mem`,
`competitor_cover`, `area_upper` and `subsequence_area_bound` establish
the admissible competitor and the bound $20\pi2^{-k}$.
`geometric_decay`, `no_reciprocal_bigO` and `reciprocal_nat_bigO_log`
give the asymptotic contradiction.
The accepted axiom closure is
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$;
there is no `sorry` or additional axiom.

## Triage

### What the settlement shows

1. **Proved (Lean) — capacity and the two-rate refutation.**
   $\overline{\mathbb D}\cup\{4\}$ has transfinite diameter one and
   $A_{k^2+k+1}(K)\leq20\pi2^{-k}$ for every $k\geq2$.
   Its area sequence is neither $\Theta(1/n)$ nor $\Theta(1/\log n)$.

2. **Open in Lean — all-degree stretched-exponential order.**
   An unformalized argument, which is not in the source paper and has not
   been independently checked, gives for all $n\geq4$

   $$
   \frac{\pi}{4n^2}\,36^{-\sqrt n}
   \leq A_n(K)\leq48\pi\,2^{-\sqrt n},
   \qquad -\log A_n(K)=\Theta(\sqrt n).
   $$

   The lower bound uses the pairing product inequality of Geng–Qiu,
   arXiv:2609.06461, Proposition 2.3. Neither that inequality nor these
   all-degree bounds is proved in this Lean module.

3. **Proved (Lean) — isolated-point mechanism at the certified scale.**
   Adding the isolated point preserves capacity one, but the resulting
   compact has neither proposed decay type. For $z$ in the unit lemniscate
   of the competitor, the $k$ roots at $4$ force
   $|z^N-1|<2^{-k}$ whenever $|z-4|\geq2$, yielding the annular cover.
   **Open in Lean — balanced-scale interpretation.** The same unformalized
   argument (not in the source paper) gives a component near $4$ of scale $2^{-N/k}$ and
   balances it with the unit-circle level $2^{-k}$ at $k\asymp\sqrt n$.
   The Lean cover uses the coarser radius $2^{-(k-2)}$ under
   $N\geq k(k-2)+1$; it does not prove this sharper scale description.

4. **Open — connected capacity-one sets.** Which rates occur if $K$
   is connected? The isolated-point example does not answer that
   restriction. Is every rate between stretched-exponential decay and
   $1/\log n$ realized by a capacity-one compact?

5. **Open — sharpness of existing upper bounds.** Are the interval's
   $1/n$ upper bound and the period-$d$ bounds $n^{-1/d}$ sharp?
   The present example determines neither of these orders.

## ASSUMED-UNVERIFIED

The literature readings do not establish an exhaustive forward-citation
list, so an answer outside those readings is not excluded. The
Geng–Qiu pairing product inequality and the all-degree two-sided estimate
are not formalized here. The balanced-scale interpretation and the
neighbouring rate-realization and sharpness questions remain open in
this Lean development.
