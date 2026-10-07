---
bibkey: alamoudi2026subradicallysifted
authors: Yazan Alamoudi
year: 2026
title: "On subradically sifted sums related to Alladi's higher order duality between prime factors"
doi: null
url: "https://arxiv.org/abs/2601.10636v2"
claim: "Theorem 1.1 gives quantitative least-prime-factor sifted Möbius estimates in a specified subpower range; it is not a theorem about the FIB signed cofactor Newton panel with a fixed positive power cutoff."
strata_touched: []
license: citation-only
triage: anchor
---

# Sifted Möbius sums and their cutoff range

The retained primary version is [arXiv:2601.10636v2](https://arxiv.org/abs/2601.10636v2),
updated 2026-09-03 after the initial 2026-01-15 submission. The original
PDF has 29 pages and SHA-256
470461bef7714c725d3fe1d131e6cbf476b7d2bb58af230dccaf1bad9fc60e1d.
The arXiv record supplies no DOI or journal reference. The abstract,
introduction and Theorem 1.1 on printed pages 2–3 were inspected.
The full proof and later general-range estimates were not independently
audited or formalized. No source text or PDF is vendored.

Use \(j\) for the source's order parameter to distinguish it from the FIB
Newton index. Its sums are

\[
M_{j,\omega}(x,y)=
\sum_{\substack{n\le x\\p_1(n)>y}}
\mu(n)\binom{\omega(n)-1}{j-1},
\]

where \(p_1(n)\) is the least prime factor. Theorem 1.1 fixes positive
\(Y_0,\mathscr p,\varepsilon\) and restricts its expansion to

\[
1.9\le y\le
\min\!\left\{
Y_0\exp\!\left[
\frac{\mathscr p\log x}{(\log\log(x+1))^{1+\varepsilon}}
\right],\ x^{1/j}
\right\}.
\]

The statement keeps a uniform error constant independent of \(x,y\)
within those conditions. For any fixed \(a>0\), the displayed subpower
threshold is eventually smaller than \(x^a\). The abstract also announces
preliminary bounds for a wider range; those are not treated here as a
verified replacement for the main theorem's expansion.

[The FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§396 uses \(n=mp\), \(m\le D<p\), with \(D\) a fixed positive power of its
Newton scale. The cofactor may contain small primes, so this is not the
least-prime-factor sieve condition \(p_1(n)>y\). Its coefficient
\(e_n=(\mu*\beta)_n\) and smooth Newton kernel also differ from the displayed
source sum. The current primary theorem therefore does not directly settle
the actual joint estimate. This scope comparison does not claim that all
results in the paper, its references, or the wider literature have been
excluded.

## The inspected general-range bounds do not supply the signed critical estimate

The additional primary scope is §5, Proposition 5.1 and its two proof
paragraphs, printed pp.24–26 of the same v2 PDF; the
[versioned HTML](https://arxiv.org/html/2601.10636v2#S5.count1)
agrees on the displayed quantities. This is statement and interface
inspection, not an independent certification of the full contour proof.
The author calls these bounds preliminary and leaves a fuller treatment
to subsequent work. No new sieve theorem or Lean result is asserted.

Use $X$ for the source's summation limit and retain $j$ for its order.
For the single curve

$$
y=Y_0\exp\!\left(\frac{\mathscr p\log X}{\log\log(X+1)}\right),
$$

with fixed $Y_0$ and $\mathscr p$, Proposition 5.1 prints

$$
m_{j,\omega}(X,y)\ll_j
\frac{X(\log\log(X+1))^j}{\log X}.
\tag{5.1, source}
$$

The displayed symbol is lowercase $m$, whereas the sums were defined
with uppercase $M$. No silent identification of the two is needed here.
Its other displayed bound is, for $1.9\le y\le X^{1/j}$,

$$
M_{j,\omega}(X,y)\le B_jX\log y\,
(\log\log(X+1))^{j-1}.
\tag{5.2, source}
$$

The statement prints no absolute-value bars in (5.2). Its proof uses
absolute contour and Perron estimates; this note neither strengthens
the displayed statement nor treats that proof as independently verified.
These source bounds must not be replaced by a signed square-root
estimate or by a main term with a smaller error.

### Compare the actual filter and rows

For the [actual growing FIB filter](alladi1982roughmobius.md), put
$y=z=P^+(N)$ and keep $x=A=\log N$ as the separate source clock.
Every row must use this same $z$. On a fixed power row $X=z^u$ with
fixed $u>1$, the curve in (5.1) obeys

$$
\frac{\log Y(X)}{\log z}
=\frac{\log Y_0}{\log z}
 +\frac{\mathscr p u}{\log\log(z^u+1)}\longrightarrow0.
$$

The actual filter instead has $\log y/\log z=1$. Thus (5.1) does not
cover these rows with fixed source parameters. Choosing $\mathscr p$
separately for each row does not establish one uniform same-filter
estimate for the full pairing. This is a scope check, not a claim that
all growing row ranges are outside the source.

Even granting the first-order substitution $j=1$ in (5.2), its right
side is $B_1X\log z$. For fixed positive $B_1$ and growing $z$, this is
weaker than the elementary $|M_z(X)|\le\lfloor X\rfloor$ for $X\ge1$.
It supplies no improved cancellation for the original Möbius prefix.
The higher orders also have different actual coefficients: for a prime
$p>z$ and $j\ge2$,

$$
\mu(p)\binom{\omega(p)-1}{j-1}=0,
\qquad \mu(p)=-1.
$$

Consequently higher-order bounds cannot stand in for the original
first-order prefix without restoring the prime contribution. The unit
is separately retained in $M_z$; the existing exact formula
$M_z(X)=1-\pi(X)+\pi(z)$ on $z\le X\le z^2$ already supplies this
first prime range and is reused rather than reproved.

The actual kernel changes sign, so an upper bound on a differently
weighted prefix is not a lower bound on its complete signed pairing.
The [existing complete upper row tail](alladi1982roughmobius.md#a-critical-scale-bound-for-the-complete-upper-row-tail)
is paid by the ordinary Mertens input. The remaining finite head keeps
the unit, lower rows and all intermediate scales; Proposition 5.1 does
not supply its required lower bound at the same selected source.
Neither the main subpower expansion nor these additional preliminary
bounds furnish an unconditional full signed Robin estimate or an RH
proof. This excludes the displayed bounds as direct suppliers of the
missing estimate, without excluding other arguments or uninspected work.
