---
bibkey: fibcomplement2026weightedresidues
authors: trureturing research synthesis
year: 2026
title: Local smooth-core estimates and weighted residues at a fixed Fibonacci modulus
doi: null
url: https://arxiv.org/abs/2609.10324v1
claim: "Gorodetsky's local smooth-number estimates supply a logarithmic-smoothness benchmark with explicit growing-weight errors. Exact divisor convolution retains the moving residue and short complementary factor; the cited Zeckendorf and fixed-modulus theorems do not yet control that joint weighted condition."
strata_touched: []
license: citation-only
triage: anchor
---

# Local smooth cores and fixed Fibonacci residues

This note records primary-source estimates and the precise interfaces they leave for the Fibonacci Robin problem. The finite identities and parameter comparisons are paper derivations; no Lean verification, complete literature-search claim, or originality claim is supplied. The growing-modulus baseline and the fixed-function-class obstruction are recorded separately in [fibaffine2026growingmoduli](fibaffine2026growingmoduli.md) and [shiuhenriot2026growingmoments](shiuhenriot2026growingmoments.md).

## The common integer and the two weights

Let

$$
V=F_r,\qquad r\ge7\text{ prime},\qquad
I_r=[\lceil V/10\rceil,\lfloor V/5\rfloor]\cap\mathbb Z,
\qquad N_g=1+gV.
$$

Write $A=\min_{g\in I_r}N_g$, $X=\max_{g\in I_r}N_g$, $y=\log A$, $\ell=\log y$, and $s=y\ell$. For the complete small-prime core at $Y=2r-2$, write

$$
C_Y(N)=\prod_{p\le Y}p^{v_p(N)},\qquad N=CH.
$$

The dangerous-core interface described in the preceding note has

$$
X\asymp V^2,\qquad Y\asymp\log X,\qquad
H\le B=\exp\!\left(O\left(\frac{\log X}{(\log\log X)^2}\right)\right),
\qquad CH-gV=1.
$$

It retains $P^+(C)\le Y<P^-(H)$, with $P^+(1)=1$ and $P^-(1)=+\infty$. In particular, $C\equiv H^{-1}\pmod V$ and both factors are units modulo $V$. For each permitted actual $H$, the core scale $x=X/H$ satisfies $\log x/\log V\to2$. In this particular choice $Y=2r-2$, one has $Y/\log x\to1/\log\phi>1$, where $\phi=(1+\sqrt5)/2$; hence $Y\ge\log x$ eventually. A general assumption $Y\asymp\log x$ alone does not give that last inequality.

A second, distinct object is the divisor-increment weight. For $Z(n)=\sigma(n)/n$ and any $s>0$, define the multiplicative function

$$
b_s(1)=1,\qquad b_s(p^a)=Z(p^a)^s-Z(p^{a-1})^s\quad(a\ge1).
$$

Then $b_s(d)\ge0$ and $Z(n)^s=\sum_{d\mid n}b_s(d)$. The associated weights are

$$
U(s)=\sum_{d\ge1}\frac{b_s(d)}d,\qquad
\mu_s(d)=\frac{b_s(d)}{dU(s)}.
$$

Here $d$ is an arbitrary divisor, not necessarily the complete core $C$, and its complementary factor $h=N/d$ need not be $Y$-rough. Any use of a short $h$ must preserve this distinction.

## Gorodetsky: local estimates at logarithmic smoothness

Ofir Gorodetsky, *Sharp local estimates for smooth numbers*, arXiv:2609.10324v1 (2026).

- Original text: https://arxiv.org/html/2609.10324v1
- Exact locations: equation (1), Corollaries 1.1, 1.7 and 1.9; the general weighted-sum notation is in §1.3.

For $x\ge Y\ge2$, write

$$
S(x,Y)=\{n\le x:P^+(n)\le Y\},\qquad \Psi(x,Y)=|S(x,Y)|,
$$

and define the saddle-point parameter $\alpha=\alpha(x,Y)>0$ by

$$
\sum_{p\le Y}\frac{\log p}{p^\alpha-1}=\log x.
$$

Corollary 1.1 gives, uniformly for $2\le d\le Y$,

$$
\frac{\Psi(x/d,Y)}{\Psi(x,Y)}
=d^{-\alpha}\left(1+O\left(\frac{\log d}{\log x}\right)\right).
\tag{G1}
$$

Equation (1) states

$$
\alpha=
\frac{\log(1+Y/\log x)}{\log Y}
\left(1+O\left(\frac{\log\log(2Y)}{\log Y}\right)\right).
\tag{G2}
$$

Consequently, if $Y\sim c\log x$ with fixed $c>0$, then $\alpha\sim\log(1+c)/\log\log x$. For an integer chosen uniformly from $S(x,Y)$, (G1) is the probability of divisibility by $d$. Fixed small primes have divisibility probability tending to one, while for a prime $p\sim Y$ the probability tends to $1/(1+c)$. These probabilities concern the unweighted smooth-number population. They are not probabilities conditioned on $C\equiv H^{-1}\pmod V$ or tilted by $Z(C)^s$.

### A size penalty that also retains large divisors

Corollary 1.7 states, uniformly for $x\ge Y\ge\log x$, $Y\ge2$, and $1\le d\le x$,

$$
\frac{\Psi(x/d,Y)}{\Psi(x,Y)}
=d^{-\alpha}\left(1+O\left(\frac{1+\log d}{\log x}\right)\right)
\left(1-\frac{(\log d)^2}{2(\log x)^2}\right)^{b u},
\quad u=\frac{\log x}{\log Y},
\tag{G3}
$$

where $b=b(x,Y,d)$ lies between positive absolute constants. In particular, for an absolute $c_0>0$,

$$
\frac{\Psi(x/d,Y)}{\Psi(x,Y)}
\ll d^{-\alpha}\exp\!\left(-c_0\frac{(\log d)^2}{\log x\log Y}\right).
\tag{G4}
$$

The nonnegative divisor expansion therefore gives the all-integer benchmark

$$
\sum_{C\in S(x,Y)}Z(C)^s
\ll\Psi(x,Y)
\sum_{d\in S(x,Y)}b_s(d)d^{-\alpha}
\exp\!\left(-c_0\frac{(\log d)^2}{\log x\log Y}\right).
\tag{G5}
$$

The constant in (G4) is independent of $s$, so this termwise step allows growing $s$. It keeps the fact that a large divisor leaves less room for the rest of the same core. It does not yield the required fixed-residue estimate. Moreover, $d^{-\alpha}$ differs from the $d^{-1}$ in $\mu_s$ by $d^{1-\alpha}$; the exponential penalty cannot be combined with the old $U(s)$ denominator while discarding this factor.

### Growing weights with explicit error sums

For an arithmetic function $f$, §1.3 defines $h=f*\mu$, where $\mu$ is the Möbius function, and

$$
M_j=\sum_{d\in S(x,Y)}\frac{|h(d)|(\log d)^j}{d^\alpha},
\qquad j=0,1,2,\qquad
\bar u=\min\left\{\frac{\log x}{\log Y},\frac Y{\log Y}\right\}.
$$

Corollary 1.9 removes the $M_0/u_Y$ error in the general arithmetic-function estimate reproduced there from La Bretèche–Tenenbaum. It gives

$$
\frac{\sum_{n\in S(x,Y)}f(n)}{\Psi(x,Y)}
=\sum_{d\in S(x,Y)}\frac{h(d)}{d^\alpha}
+O\left(\frac{M_1}{\log x}+
\frac{M_2\bar u}{(\log x)^2}\right).
\tag{G6}
$$

Taking $f=Z^s$ gives $h=b_s$. Thus the dependence on a growing $s$ remains in explicit finite sums rather than a suppressed function-class constant. The formula alone does not show that its error is smaller than its main term: the large-$d$ part can dominate $M_1$ or $M_2$. Neither (G5) nor (G6) has a congruence condition.

## The missing conditional estimate retains a moving residue

For a unit $a$ modulo $V$, define

$$
\Psi(x,Y;V,a)=\#\{C\in S(x,Y):C\equiv a\pmod V\}.
$$

Expanding $Z(C)^s$ before imposing any estimate gives the exact finite identity

$$
\sum_{\substack{C\in S(x,Y)\\C\equiv a\pmod V}}Z(C)^s
=
\sum_{\substack{d\in S(x,Y)\\(d,V)=1}}
 b_s(d)\,\Psi(x/d,Y;V,a\bar d),
\tag{R1}
$$

where $\bar d$ is the inverse of $d$ modulo $V$. Every divisor of a unit core is a unit, and writing $C=dm$ supplies the displayed scale and residue simultaneously.

For the actual complete-core problem, $a=\bar H$ and $x=X/H$, with the same rough $H$. The lower endpoint of the core interval is retained by taking the difference of two such sums. The needed estimate must control the shrinking scale $x/d$, the moving residue $a\bar d$, and the same $b_s(d)$ weights. An estimate for the unconditional ratio $\Psi(x/d,Y)/\Psi(x,Y)$ supplies a comparison population, not this conditional ratio.

The large-divisor hit problem has a complementary character interface. Let $I=[g_-,g_+]\cap\mathbb Z$ be a positive integer interval, $X=1+g_+V$, and $1\le D<X$ with $B_D=X/D<V$. Set

$$
\mathcal H_D=\{d>D:\exists g\in I,\ d\mid1+gV\},\qquad
J_d=\{h\in\mathbb N:1\le h\le B_D,\ g_-\le(dh-1)/V\le g_+\}.
$$

The inequalities defining $J_d$ are real size constraints; the congruence is imposed separately. Since $B_D<V$, a fixed unit $d$ has at most one $h\in J_d$ with $dh\equiv1\pmod V$. Finite character orthogonality then yields

$$
\mu_s(\mathcal H_D)
=\frac1{\varphi(V)U(s)}
\sum_{\chi\bmod V}
\sum_{\substack{D<d\le X\\(d,V)=1}}
\frac{b_s(d)}d\chi(d)
\sum_{h\in J_d}\chi(h).
\tag{R2}
$$

Dirichlet characters vanish on nonunits. The product is $\chi(d)\chi(h)$ because the target residue is one. The interval $J_d$ depends on $d$, so the two sums cannot be replaced by independent full-interval factors without controlling the resulting error. To use a complete-core version, one must additionally impose $P^-(h)>Y$ and replace the arbitrary-divisor weight by the appropriate complete-core weight. Formula (R2) does not make that change by itself.

## Classical abundance calibrates a different maximum

The source is the existing [Alaoglu–Erdős note](../Arith/alaoglu1944highly.md). The additional locator is §3, printed pp.454–455, especially Theorem 10 on p.455 (PDF p.9 including the cover). That theorem gives the prime exponents of the colossally abundant maximizer of $\sigma(n)/n^{1+\epsilon}$ for fixed $\epsilon>0$.

Putting $\epsilon=1/s$ identifies the classical comparison

$$
\max_{n\ge1}\frac{Z(n)^s}{n}
=\left(\max_{n\ge1}\frac{\sigma(n)}{n^{1+1/s}}\right)^s.
\tag{A1}
$$

For the increment weights, the additional local factors are

$$
\frac{b_s(n)}n
=\frac{Z(n)^s}{n}
\prod_{p^a\parallel n}
\left[1-\left(\frac{Z(p^{a-1})}{Z(p^a)}\right)^s\right].
\tag{A2}
$$

Thus the classical maximum gives an upper comparison. A matching maximum-atom asymptotic for $\mu_s$ requires control of the product in (A2), as well as the denominator and any imposed size, prime-power, or coprimality conditions. Theorem 10 is not a theorem about $b_s$, and no fixed Fibonacci residue hit follows from either a classical maximizer or a large increment-weight configuration. The moment-denominator source is recorded in [weingartner2010distribution](weingartner2010distribution.md).

## Bugeaud: a direct but restricted Zeckendorf bridge

Yann Bugeaud, *On the Zeckendorf representation of smooth numbers*, arXiv:1909.03863v1 (2019).

- Original text: https://arxiv.org/html/1909.03863v1
- Exact locations: Theorems 1.1 and 1.2; Theorem 1.4 gives a further digit-count bound for fixed integral $S$-units.

Let $F_j^{(k)}$ enumerate the positive integers with at most $k$ occupied Zeckendorf positions. For fixed $k\ge1$, fixed finite nonempty prime set $S$, and fixed $\varepsilon>0$, Theorem 1.1 gives

$$
[F_j^{(k)}]_S<(F_j^{(k)})^\varepsilon
$$

for sufficiently large $j$. Theorem 1.2 gives effective constants $c_1,j_1>0$, depending on $k,S$, with

$$
[F_j^{(k)}]_S\le(F_j^{(k)})^{1-c_1}\qquad(j\ge j_1),
$$

and the effective greatest-prime-factor bound

$$
P^+(F_j^{(k)})>
\left(\frac1k-\varepsilon\right)\log\log F_j^{(k)}
\frac{\log\log\log F_j^{(k)}}{\log\log\log\log F_j^{(k)}}
$$

for sufficiently large $j$, with $k,\varepsilon$ fixed.

These results connect actual Fibonacci occupancy to prime-factor restrictions. Grouping the digits into the five legal window modes preserves their applicability when the total occupied-position count is bounded. The current dangerous-core hypotheses provide no uniform bound on the digit count, and the relevant prime set $S=\{p\le Y\}$ grows with $r$. The displayed general greatest-prime-factor bound is also below $Y\asymp\log N$ and does not bound the product of the rough factors. Applying this route to all dangerous configurations therefore requires a new uniform parameter estimate or a proof that those configurations belong to a restricted address family. The special one-digit Fibonacci bounds mentioned separately in Bugeaud's introduction do not make $1+gF_r$ a one-digit integer.

## Klurman–Mangerel–Teräväinen: fixed good moduli with exclusions

Oleksiy Klurman, Alexander P. Mangerel and Joni Teräväinen, *Multiplicative functions in short arithmetic progressions*, arXiv:1909.12280v5 (2023 version).

- Original text: https://arxiv.org/html/1909.12280v5
- Exact locations: §1.2, Theorem 1.2; equation (4) defines the pretentious distance selecting the comparison character.

For fixed $\eta>0$, $x\ge10$,

$$
(\log x)^{-1/200}\le\varepsilon\le1,\qquad Q\le x^{1/2-100\eta},
$$

Theorem 1.2 supplies a good-modulus set $\mathcal Q_{x,\varepsilon}$ with

$$
|[1,Q]\setminus\mathcal Q_{x,\varepsilon}|\ll Qx^{-\varepsilon^{200}}.
$$

For each $q\in\mathcal Q_{x,\varepsilon}\cap[1,Q]$ and each multiplicative $f$ with $|f|\le1$ supported on $x^\eta$-smooth integers, it gives

$$
\max_{a\in(\mathbb Z/q\mathbb Z)^\times}
\left|
\sum_{\substack{n\le x\\n\equiv a\pmod q}}f(n)
-\frac{\chi_1(a)}{\varphi(q)}\sum_{n\le x}f(n)\overline{\chi_1(n)}
\right|
\ll\varepsilon\frac xq.
\tag{K1}
$$

Here $\chi_1$ minimizes the source's pretentious distance to $f$ after allowing twists $n^{it}$, $|t|\le\log x$; it is not silently replaced by the principal character. For any pairwise coprime set $\mathcal Q'\subseteq[1,Q]$, the exceptional intersection has size at most $O((\log x)^{\varepsilon^{-200}})$. Under GRH the source removes the exceptional moduli; that conditional assertion is not an unconditional input to the present Robin problem.

The maximum over residues in (K1) is useful: it really controls each residue for a good fixed modulus. Three distinct restrictions remain in the current application. First, $q=V=x^{1/2+o(1)}$ lies outside the range with fixed positive $\eta$; letting $\eta$ decrease requires uniformity the quoted theorem does not supply. Second, $Z^s$ is not bounded by one. A proposed normalization must preserve multiplicativity and control the large factor restored in the final error. Third, pairwise coprimality of the prime-index Fibonacci moduli does not remove exceptions. There are only $O(\log Q/\log\log Q)$ such moduli up to $Q$, so the stated polylogarithmic exception bound can include all of them. These restrictions are independent of the fact that logarithmic-smooth support is contained in $x^\eta$-smooth support for fixed $\eta$ and sufficiently large $x$.

## A geometric interface for a short complementary factor

J. Cilleruelo and M. Z. Garaev, *Concentration points on two and three dimensional modular hyperbolas and applications*, arXiv:1007.1526v2 (2010), [Theorem 1](https://arxiv.org/html/1007.1526v2), bounds the points of $uv\equiv a\pmod p$ in a translated square of side $M$, for prime $p$ and $a\not\equiv0\pmod p$, by

$$
M^{4/3+o(1)}p^{-1/3}+M^{o(1)}.
$$

This is a fixed-modulus, fixed-product result, and for $M<p^{1/4}$ it is $M^{o(1)}$. In the present problem only the complementary factor is known to lie in a short interval. The core residues need not occupy a single short interval, and $V$ need not be prime. Cutting all core residues into short intervals introduces their number as a loss. Using this interface requires an additional common-source concentration or weighted covering estimate and a suitable prime-modulus or composite-modulus bridge.

The remaining objective is a joint bound for the actual weighted relation $CH-gV=1$, with the core, the cofactor, and the source interval kept together. The cited local estimates refine its comparison models; they do not yet prove that the fixed Fibonacci residue contains no Robin violation.

## Complete support and ordered exponents do not fix the canonical window

The [weighted Beatty note](guloglunevans2008beatty.md) identifies the
actual canonical rotation $r_n=\{n\varphi\}$ and residual $E$ for the
same integer. A classical density theorem supplies a useful restriction
on attempts to control that window using prime support alone.
Frantzikinakis–Host–Kra, *Bohr recurrence and density of non-lacunary
semigroups of $\mathbb N$*, Proc. AMS **153** (2025), 181–192,
[DOI:10.1090/proc/17006](https://doi.org/10.1090/proc/17006),
[arXiv:2406.01353v3](https://arxiv.org/pdf/2406.01353v3), updated
2024-11-02, defines non-lacunarity on printed p.3 as containing two
multiplicatively independent integers. On p.4 it recalls Furstenberg's
irrational linear-orbit density theorem before stating the polynomial
extension in Theorem 3. The classical linear theorem is sufficient
here; the polynomial extension is not required.

Fix $P\ge3$, put $R=P\#$, and consider the actual integers

$$
n=R\,2^u6^v,\qquad u,v\in\mathbb Z_{\ge0}.
$$

They retain every prime through $P$ and have nonincreasing exponents:
$v_2(n)=1+u+v$, $v_3(n)=1+v$, and $v_p(n)=1$ for $5\le p\le P$.
The generators 2 and 6 are multiplicatively independent, even though
they are not coprime. For each integer $U\ge0$, the subfamily $u,v\ge U$ is
$R12^U\langle2,6\rangle$. Applying the recalled theorem with the
irrational coefficient $R12^U\varphi$ proves density of its rotations
in $\mathbb R/\mathbb Z$. This separate application controls arbitrarily
large exponent tails; deleting infinite edges from one dense orbit
would not justify it.

Choose an open arc strictly inside a canonical rotation branch where
$|E|$ is bounded below by a fixed positive constant. For arbitrarily
large members of the same fixed-$P$ family, the exact canonical
certificate

$$
D=5h^2+E\bigl(2\sqrt5(n-h)+E\bigr)
$$

then has $|D|\asymp n$. Consequently complete initial support and
ordered exponents **alone** do not force every canonical source into
the small-discriminant windows used by the nonresidue estimate.

The fixed-$P$ quantifier is essential. Here
$Z(n)\le\prod_{p\le P}(1-1/p)^{-1}$, so the Robin ratio tends to zero;
these are not asymptotic SA/CA candidates or a near-boundary family.
The density theorem provides no hitting-rate bound when $P$ grows,
and no assertion about the squarefree kernel or conductor of the
actual $D$. The extremal exponent heights and their size budget are
therefore additional joint conditions to retain, rather than optional
labels on the support. This is a classical-source application without
Lean verification or an originality claim.

## Support-conditioned discriminants and already covered norm branches

The [Baier square-sieve note](../Fourier/baier2016squaresieve.md) records a
different joint obstruction on the **same actual integer**. Its canonical
certificate $c^2-D=5n(n-2h)$ forces $(D/p)\in\{0,1\}$ at every odd support
prime. For a finite weighted population sharing $L$ such primes, the
ordered-pair correlation term is exactly

$$
\sum_n a_n\frac{k(n)(k(n)-1)}{L^2},
\qquad k(n)=\#\{p\text{ selected}:p\nmid D(n)\}.
$$

Thus preselecting full prime support does not leave independent quadratic
signs for a square sieve to cancel. Zeros retain the joint incidence of
the canonical lift and the support. For unit bit zero they are precisely
the selected odd primes dividing the composition gcd; for unit bit one
the zero locus is affine and this gcd identification fails. Neither a
support-only phase average nor the unconditional square-sieve statement
controls the remaining weighted incidence or the extremal exponent cost.

The primitive norm $\pm1$ branch with unit bit zero already has a uniform
Robin tail bound in [the FIB theory, §199.6 and §201.6](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
Those paper results allow the actual canonical composition gcd to grow;
they are not merely fixed-multiplier statements. A new safety proof for
this branch would not expand the covered Robin family. Remaining norm
and affine-unit branches still require estimates with their own actual
support, gcd, discriminant and price budget kept together.

## Actual CA prime-step chains cannot stay in raw small-discriminant windows

The fixed-support family above does not consist of asymptotic CA
candidates. A different application uses an unbounded chain of actual
CA integers and the exact canonical lift already recorded in the
[Beatty note](guloglunevans2008beatty.md). This is a paper derivation from
classical CA optimization and quadratic irrational separation, without
a Lean-verification or originality claim.

For the canonical source of each integer $n>1$, retain

$$
n=h+2A+3B,\quad h\in\{0,1\},\quad c=4A+7B,
\quad E(n)=c-\sqrt5(n-h),
\quad D(n)=5h^2-4(A^2+AB-B^2).
$$

The existing rotation branches give $|E(n)|<1$. Also $E(n)\ne0$,
because $n-h>0$ and $\sqrt5$ is irrational. The actual-source identity is

$$
D(n)=5h^2+E(n)\bigl(2\sqrt5(n-h)+E(n)\bigr).
\tag{A1}
$$

The classical local CA objective and tied-price convention, recalled
in [Nicolas's comparison note](nicolas2025comparison.md), permit an
unbounded chain $n_{j+1}=p_jn_j$ of actual CA maximizers, with each $p_j$
prime. To obtain it, order the prime-power activation prices
$\log[Z(p^a)/Z(p^{a-1})]/\log p$ decreasingly and include each activated
layer. At a tied price, include the tied layers one at a time. Every
intermediate product includes all layers having strictly positive gain
at that price and a subset having zero gain, so is still a global
maximizer. The activation prices strictly decrease at each fixed prime,
and only finitely many layers exceed any fixed positive price. Letting
the price tend to zero gives the unbounded chain. No bound on the number
of simultaneous ties is needed, and the chain need not contain every CA
integer.

Put $L_j=\log n_j$. Initial prime support gives
$\vartheta(p_j)\le\log n_{j+1}=L_j+\log p_j$. Ordinary PNT and
$\log p\le p/4$ for large $p$ imply $p_j\le4L_j$ eventually. Bounded
step primes also satisfy this bound once $L_j$ is large.

For integers $k,t$ with $t\ne0$, the elementary quadratic irrational
bound is

$$
|k+\sqrt5t|\ge\frac1{6|t|}.
\tag{A2}
$$

If the absolute value is at least one, the bound is immediate.
Otherwise $|k-\sqrt5t|\le1+2\sqrt5|t|<6|t|$, while the nonzero integer
$|k^2-5t^2|$ is at least one. Their product proves (A2).

Suppose that every sufficiently large actual CA integer satisfied
$|E(n)|\le1/[240(\log n)^2]$. Write $h_j,c_j$ for the two actual
canonical readouts. Their exact neighbor relation is

$$
E(n_{j+1})-p_jE(n_j)
=(c_{j+1}-p_jc_j)-\sqrt5(p_jh_j-h_{j+1}).
\tag{A3}
$$

On the late chain, its left side has absolute value at most
$(p_j+1)/(240L_j^2)\le1/(48L_j)$. If
$t=p_jh_j-h_{j+1}\ne0$, then $|t|\le p_j$ and (A2) instead gives
at least $1/(6p_j)\ge1/(24L_j)$. Hence $t=0$, which forces
$h_j=h_{j+1}=0$. The remaining integer $c_{j+1}-p_jc_j$ has absolute
value below one and is zero. Thus $E(n_{j+1})=p_jE(n_j)$ throughout
the late chain. At a fixed late index $J$, this gives
$E(n_j)=(n_j/n_J)E(n_J)$, unbounded in absolute value, contrary to the
canonical bound. Therefore arbitrarily large actual CA integers satisfy
$|E(n)|>1/[240(\log n)^2]$.

At those same integers, (A1) gives
$|D(n)|\ge2\sqrt5(n-1)|E(n)|-6$. Consequently an unbounded subset of
the CA test set satisfies

$$
\boxed{|D(n)|\ge\frac{n}{240(\log n)^2}.}
\tag{A4}
$$

For the last constant it suffices to take members large enough that
$3n-4\ge1440(\log n)^2$. In particular, for every fixed real $K$ and
$C>0$, an eventual upper bound $|D(n)|\le C(\log n)^K$ cannot hold
on the whole CA test set. This addresses actual extremal integers,
rather than only the non-CA fixed-support examples above.

The conclusion concerns the raw canonical discriminant. It gives no
lower bound for its radical, squarefree kernel, primitive conductor or
exception-adjusted modulus; large square factors and square $D$ remain
possible. It neither identifies these CA integers as Robin violations
nor excludes an independently justified RH-equivalent thinning whose
members have small discriminants. A small-discriminant bound restricted
to actual violations is also not refuted. The
[Pollack application](../Scale/pollack2017nonresidues.md) remains usable
under its same-source cutoff and exception hypotheses, while those
hypotheses cannot be supplied for every CA integer merely by assuming a
uniform raw-discriminant log-power bound. No signed Robin margin or RH
proof is obtained here.
