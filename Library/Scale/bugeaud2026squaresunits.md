---
bibkey: bugeaud2026squaresunits
authors: Yann Bugeaud
year: 2026
title: "On the difference between squares and integral S-units"
doi: 10.4171/pm/2145
url: https://ems.press/journals/pm/articles/14298883
claim: "Theorem 1.4 applies to the actual CA golden norm, but its universal exponent exceeds 3 on every support containing 2 and 5; its literal power bound cannot exclude the dangerous arc, so a useful strengthening must restrict the solution family or change the bound."
strata_touched: []
license: citation-only
triage: anchor
---

# Absolute square gaps with their support dependence retained

Yann Bugeaud, *On the difference between squares and integral S-units*,
Portugaliae Mathematica **83**(3/4) (2026), 223–234,
[DOI:10.4171/PM/2145](https://doi.org/10.4171/PM/2145).
The [publisher page](https://ems.press/journals/pm/articles/14298883)
records online publication on 13 June 2025; 2026 is the printed volume year.
The inspected [publisher PDF](https://ems.press/content/serial-article-files/53394)
gives Theorem 1.2 on p.224 and Corollary 1.3 and Theorem 1.4 on p.225.
This note checks those statements and their parameter interface. Transient
Lean applications check the finite witness and exponent comparison below;
the analytic theorems and the full CA asymptotic bridge are not formalized here.

## Two different outputs of the same paper

For a fixed nonempty finite prime set $T=\{q_1,\ldots,q_t\}$,
Theorem 1.4 gives an effectively computable $c(T)>0$ such that every
integer solution of

$$
z^2-\prod_{i=1}^t q_i^{a_i}=M\ne0,
\qquad a_i\ge0,
$$

satisfies

$$
|z|\le |2M|^{c(T)}.
$$

Consequently it supplies the absolute lower bound
$|M|\ge |z|^{1/c(T)}/2$. The displayed statement does not add a
coprimality hypothesis on $z$. Its constant depends on $T$; effectiveness
for each fixed set is not uniformity as that set grows.

Theorem 1.2 has a different output. For disjoint nonempty finite prime sets $S,T$
and $z$ coprime with the product of the primes in $T$, it bounds
$[z^2-\prod q_i^{a_i}]_S$, first ineffectively by a constant times
$|M|^{1/2+\varepsilon}$ and then effectively by a constant times
$|M|^{1-\vartheta}$. Its (1.3) retains

$$
\vartheta=
\left[c(T)^{|S|}\log\log R
       \left(\prod_{p\in S}\log p\right)^2\right]^{-1},
\qquad R=\max S.
$$

This $c(T)$ is the constant in (1.3), not an identification with
Theorem 1.4's constant. No large prescribed $S$-part of the golden norm
is available merely because its denominator has smooth factors.

## Exact interface to the actual CA pair

Use [the FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§§331–332: $C$ is an actual CA host, $P=P^+(C)$, $n=Cq$, and $m$ is
nearest to $n\varphi$, where $\varphi=(1+\sqrt5)/2$.
For sufficiently large hosts, $n$ is even and $5\mid C$. Set

$$
z=m-n/2\in\mathbb Z,\qquad
Y=5(n/2)^2,\qquad
T=\{p:p\mid n\}.
$$

Then $Y$ is an integral $T$-unit and the same auxiliary norm is exactly

$$
K=m^2-mn-n^2=z^2-Y.
$$

Thus Theorem 1.4 applies to this actual pair, including common divisors,
with its own support $T$. Theorem 1.2 requires its additional
coprimality and disjoint-support hypotheses. The auxiliary pair is linked
to the same canonical unit-bit-zero source by the existing §331.2
interface; this note supplies no new source classification.

For the rational-obstruction denominator in §328, write

$$
L=\log C,\quad S_0=\sqrt P,\quad
q\asymp e^{\eta S_0},\quad \kappa>2\eta>0.
$$

Here $\log|z|=L+\eta S_0+O(1)$ and the bad arc permits
$|K|\le O(Ce^{-(\kappa-\eta)S_0})$.
To exclude that allowance using the absolute bound above would require
the quantitative comparison

$$
\frac{L+\eta S_0+O(1)}{c(T)}-\log2
>L-(\kappa-\eta)S_0+O(1).
$$

The left bound is a lower bound for the same $|K|$; the right is its
allowed upper bound. If the chosen constant is normalized to $c(T)\ge1$,
this comparison requires $1-1/c(T)=O(P^{-1/2})$, since $L\sim P$.
The literal universal exponent has a stronger obstruction than an unknown
dependence on the growing support. Every support here contains $2$ and $5$,
and Theorem 1.4's solution family therefore includes

$$
z=9,\qquad Y=2^4\cdot5=80,\qquad K=9^2-80=1.
$$

Thus $9\le2^{c(T)}$, which forces $c(T)>3$. This witness already has
squarefree part $5$, so keeping the quadratic field fixed does not remove it.
Consequently the lower bound furnished by this literal theorem satisfies

$$
\frac{\log|z|}{c(T)}-\log2
\le\frac{L+\eta S_0+O(1)}3-\log2,
$$

for the actual large pair, whereas the dangerous-arc upper allowance has
logarithm $L-(\kappa-\eta)S_0+O(1)$. Since $L\sim P$ and $S_0=\sqrt P$,
the latter exceeds this guaranteed lower bound by a quantity tending to
infinity. Optimizing the exponent in the quoted universal power bound cannot
make the required comparison hold.

The small witness belongs to the theorem's full solution family; it is not
an actual CA host pair or an instance of the dangerous arc. Restrictions on
the solution family, including complete CA valuations or coprimality with
the full support, can exclude that witness and must be assessed on the actual
pair, preserving any common divisors. Bounds with additional prefactors or
height thresholds must retain those parameters in the comparison. No
exclusion of such alternative arguments, and no actual CA incidence in
the arc, is claimed.

The prime $q$ here is the rational-obstruction denominator and a costly
multiplier in §328. It is not a member of §327's cheap family: that family
consists of products of distinct primes in $(P,P+P/\log P]$. Only the latter
has the proved $W(Ct)-W(C)=o(1)$ transport. The absolute norm bounds
provide no independent signed Robin reserve for either family.

## Publisher-available extension to variable perfect powers

The directly accessible [publisher PDF](https://msp.org/om/2027/4-1/om-v4-n1-p04-s.pdf)
of Bugeaud, *On the difference between perfect powers and integral S-units*,
Orbita Mathematicae **4**(1), 85–90,
[DOI:10.2140/om.2027.4.85](https://doi.org/10.2140/om.2027.4.85),
is labelled with the print issue year 2027. Its final page records receipt
on 5 January 2026 and revision on 27 April 2026. The online release date
was not established here; the quoted source is the available publisher
file, without a claim about its chronological priority.

Its Theorem 1.1 on p.86 is uniform over exponents $d\ge2$: for fixed $T$,
a $T$-unit $x>1$ and a perfect power $u=z^d$ with $z\ge2$ coprime with
all primes in $T$, it gives effective positive constants $\kappa_1(T)$,
$\kappa_2(T)$ and, with $X=\max(x,u)$,

$$
|x-u|\ge(\log^*\log X)^{\kappa_1(T)}.
$$

It also gives a greatest-prime-factor lower bound. Corollary 1.2 gives
effective finiteness for each fixed difference. The constants still
depend on the fixed prime set. In the present exponent-two problem,
§2's (2-1) directly reuses the preceding paper's Theorem 1.4 and provides
the stronger fixed-support power bound. Uniformity in $d$ does not
supply the missing uniformity in the growing actual CA support.
