---
bibkey: axler2023robin
authors: Christian Axler
year: 2023
title: On Robin's inequality
doi: 10.1007/s11139-022-00683-0
url: https://arxiv.org/pdf/2110.13478v3
claim: The totient bound inside the proof gives a stronger joint prime-valuation stopping condition and an exact finite resolution for that condition.
strata_touched: []
license: citation-only
triage: anchor
---

# On Robin's inequality

The [published article](https://doi.org/10.1007/s11139-022-00683-0) is
Christian Axler, *The Ramanujan Journal* 61 (2023), 909–919. Formula numbers
below refer to the inspected [author version v3](https://arxiv.org/pdf/2110.13478v3).
Theorem 1.4 there corresponds to the published Theorem 3.

## The bound needed for joint prime observations

Write $N_k=\prod_{i=1}^k p_i$, $L=\log\log n$, and $a_0=0.0094243$.
Lemma 2.3 states Robin for $5041\le n\le N_K$, where

$$
K=999999476056,\qquad p_K=29996208012611.
$$

Equations (3.4)–(3.5), in the proof of Theorem 1.3, imply

$$
\frac n{\varphi(n)}<e^\gamma\left(L+\frac{a_0}{L^2}\right)
\qquad(n\ge N_K).
$$

The proof's analytic threshold is the smaller prime endpoint
$29996161880813$, so the displayed finite and analytic ranges overlap.
Retaining this bound on $n/\varphi(n)$ is essential: multiplying a bound
on $\sigma(n)/n$ itself by a local factor would not be justified.

The constant $\epsilon=3.15367\cdot10^{-7}$ used in Corollary 3.1 also
satisfies $a_0/L^3<\epsilon$ throughout $n\ge N_K$. An exact rational
check of the overlap uses equation (3.3)'s cited theta estimate

$$
\vartheta(x)>x\left(1-\frac{0.00033277}{(\log x)^2}\right).
$$

At $x=p_K$, rational logarithm enclosures give

$$
\log x>\frac{31032092090021}{10^{12}},\qquad
\log\vartheta(x)>\frac{31032091744463}{10^{12}},
$$

and $\epsilon(31032091744463/10^{12})^3-a_0>0$.
The [cutoff program](../../docs/reports/fib-robin-boundary/axler_cutoff.py)
certifies these arithmetic comparisons. It treats the published analytic
bounds and finite verification as inputs; it does not rerun or formally
verify them. The author version's reference to Lemma 2.2 for the small
range in this proof is not used here; the finite verification is Lemma 2.3.

For primes $P$ actually dividing the same integer $n>5040$, set

$$
\eta_P(n)=\prod_{p\in P}(1-p^{-(v_p(n)+1)}),\qquad
T_A=\frac{10^{12}}{10^{12}+315367}.
$$

Then $\eta_P(n)\le T_A$ implies strict Robin: above $N_K$, use

$$
Z(n)\le\eta_P(n)\frac n{\varphi(n)}
<(1+\epsilon)\eta_P(n)e^\gamma L\le e^\gamma L;
$$

below $N_K$, apply Lemma 2.3. An absent prime cannot contribute a factor.
This is a direct application of the published proof, stronger than the
[Hertlein cutoff](hertlein2018robin.md), with no new analytic theorem claim.

## Complete five-direction classification and its resolution

Keep $P=(2,3,5,7,11)$ and lower exponents $b=(21,13,9,7,6)$, forced for a
possible Robin counterexample by the previously cited individual stops.
The [exact report](../../docs/reports/fib-robin-boundary/valuation_slices_axler.json)
uses caps

$$
c=(31,21,13,11,9).
$$

The cap in each coordinate includes every greater exponent. All 9,900
cells are resolved: 1,144 have product supremum at most $T_A$ and 8,756
have product infimum greater than $T_A$. There are 42 minimal profiles
outside the condition and 45 maximal certified regions. These counts are
for this partition, not a density among natural numbers.

With $M=2^{21}3^{13}5^97^711^6$, the 42 minimal profiles correspond to
the following divisibility antichain:

```text
84, 210, 360, 378, 540, 882, 900, 1120, 1200, 1320, 1386,
1960, 1980, 2800, 3080, 3168, 3234, 3300, 3465, 4752, 7128,
7700, 10780, 14850, 15360, 16940, 17424, 26136, 33075, 35000,
59535, 138915, 294030, 385875, 1414875, 2223375, 3112725,
3189375, 5312384, 5740875, 66784256, 204526784
```

Thus a hypothetical counterexample must have $Mr\mid n$ for at least
one listed $r$. This union is strictly contained in the 12-region union
from the weaker cutoff, despite having more generators. For example,
the exact profile of $6M$ is outside the Hertlein condition and inside
the Axler condition. Membership in either remaining union does not imply
a Robin violation. For authenticated $n=5040F_j$, the existing valuation
transport gives $Dr\mid j$ for some listed $r$, where
$D=2^{15}3^{10}5^87^511^5$; this alone does not incorporate other prime stops.

The caps also describe exactly the resolution needed by this predicate.
Let $u_p=\min(v_p(n),c_p)$. The classifier is constant on every such cell,
so these five clipped valuations determine whether $\eta_P(n)\le T_A$
on the full orthant. Equivalently, residues modulo $p^{c_p}$ supply
sufficient data. This does not assert that the full residues are minimal
states or that they determine Robin's truth value in a rejected cell.

These caps are coordinatewise minimal among representations by clipped
valuations: the maximum of coordinate $p$ over the 42 minimal outside
profiles equals $c_p$. Pick a profile attaining it. That profile is outside,
but decreasing its $p$ coordinate by one gives a certified profile by
minimality. Any smaller cap in that coordinate identifies this pair, even
if all other valuations are known exactly. Both profiles are realized by
ordinary integers with those prime powers. This argument establishes the
resolution of the supplied sufficient condition, not of primality or RH.

The FIB window recurrence can accumulate these modular observations from
the same finite source. The contraction interval alone supplies no such
valuation certificate. The useful bridge is the authenticated common
integer plus its modular observations; neither the four-phase symmetry nor
interval length is used as an Euler-factor weight.

## A coupled new-prime slice on Fibonacci sources

The same bound also couples directions beyond the first five:

$$
T_A-(1-13^{-6})(1-23^{-5})
=\frac{1465648493004484688}{31067008116993059021656729}>0.
$$

Hence $1\le v_{13}(n)\le5$ together with $1\le v_{23}(n)\le4$
already suffices for Robin, independently of all other prime factors.
At the endpoint pair $(5,4)$, neither individual condition from Theorem
1.4 succeeds; the additional exclusion uses their joint product.

For the authenticated source $n=5040F_{Dk}$, the first divisibility ranks
of $13,17,19,23$ are respectively $7,9,18,24$. At those ranks the
Fibonacci values are $13,34,2584,46368$, each with prime valuation one.
All four ranks divide $D$, and none of these four primes divides $5040D$.
The rank/lifting formula cited in FIB §95 therefore gives

$$
v_p(n)=1+v_p(k)\qquad(p\in\{13,17,19,23\}).
$$

The individual stops force
$Q=13^4 17^4 19^4 23^3\mid k$. The new joint condition further forces
$13^5\mid k$ or $23^4\mid k$. Thus, writing $k=Qt$, a hypothetical
counterexample in this source family must have $13\mid t$ or $23\mid t$.
Combining this with the 42 old-prime profiles gives the necessary union

$$
DQrs\mid j\quad\text{for some listed }r
\text{ and some }s\in\{13,23\}.
$$

The 84 generators are pairwise incomparable for divisibility: the 42
old-prime multipliers form an antichain and have no factor 13 or 23.
This union is only an outer bound on candidates; multiplying all nine
actual local factors can certify additional members of it. The argument
uses one source $j$ for every direction, not separately selected local
extrema. It neither gives a counterexample nor proves every source safe.

In fact all 84 lowest corners of these regions pass the full nine-factor
product test. Their minimum rational slack is

$$
\frac{3969942702286084876494714681732864182853322051528}
{20579432895399995051033122675947739295611809721186640625}>0.
$$

It occurs at old-prime profile $(22,15,9,8,7)$ and new-prime profile
$(6,5,5,4)$. Holding these nine valuations exact permits arbitrary other
prime factors, since discarded local factors are at most one. This does
not certify the whole upper regions, where the nine valuations can grow.
The corner calculation exposes the loss from testing groups separately;
it is not evidence of simultaneous near-failure of Robin.

This note adds no Lean declaration, no new verified global Robin range,
and no claim that the remaining 42 regions exhaust all known stopping rules.
