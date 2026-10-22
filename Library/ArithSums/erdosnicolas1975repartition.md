---
bibkey: erdosnicolas1975repartition
authors: Paul Erdős; Jean-Louis Nicolas
year: 1975
title: Répartition des nombres superabondants
doi: 10.24033/bsmf.1793
url: https://www.numdam.org/item/BSMF_1975__103__65_0/
claim: The classical CA benefit has explicit arbitrary-host thin-layer capacity bounds and a same-host signed-tail application; the joint FIB Robin budget remains unproved.
strata_touched: []
license: citation-only
triage: anchor
---

# Répartition des nombres superabondants

Primary source: *Bulletin de la Société Mathématique de France* **103** (1975), 65–90, [Numdam article record](https://www.numdam.org/item/BSMF_1975__103__65_0/) and [original scan](https://www.numdam.org/item/10.24033/bsmf.1793.pdf). The relevant locators are Proposition 4(c)–(d) and its proof on printed pp.70–71, and §3, Proposition 5 and its proof on pp.73–74. This note records the definitions and their scope; it is not a verification of every proof in the paper or a Lean result.

Let $Z(n)=\sigma(n)/n$, and let $N$ maximize $Z(n)n^{-\epsilon}$ for a fixed $\epsilon>0$. On printed p.74, the authors define, for an arbitrary positive integer $m$,

$$
\operatorname{ben}_{N,\epsilon}(m)
=\epsilon\log(m/N)-\log\frac{Z(m)}{Z(N)}
\ge0.
$$

The nonnegativity follows from the defining optimality of the same $N$ and $\epsilon$. If $L=\log m$, $F=\log Z(m)$, $L_0=\log N$, $F_0=\log Z(N)$, then

$$
F_0-\epsilon L_0-F+\epsilon L
=\operatorname{ben}_{N,\epsilon}(m).
$$

Thus a “price loss” with the same reference optimizer and price is exactly the classical benefit, not a new FIB invariant. In particular, a separately justified choice $N=5040$, $\epsilon=1/25$ has this meaning; this card does not independently establish that optimizer choice.

Proposition 5 is a near-extremal structural application. Its additional hypotheses are that $n$ is **superabundant** and it lies between $N$ and $NP$, where $P$ is the prime after the largest prime factor of $N$. Its proof uses a small benefit to control displacement of prime-exponent thresholds. The arbitrary-integer definition of benefit must not be confused with those stronger hypotheses on the integer to which Proposition 5 applies. An arbitrary Robin violation in a prescribed residue class is not automatically superabundant.

The proof points back to Proposition 4, p.120, of [Nicolas's *Répartition des nombres hautement composés de Ramanujan*](nicolas1971repartition.md), *Canadian Journal of Mathematics* **23** (1971), 116–130. Its original benefit decomposition and quadratic threshold-cost calculations on pp.117–120 have been inspected. That source uses the divisor-count objective and assumes a highly composite target for Proposition 4; the 1975 transfer uses the divisor-sum ratio and a superabundant target. Neither structural conclusion applies to an arbitrary host merely because its benefit is defined.

For the FIB Robin analysis, the valuation-increment source

$$
w_s(d)=\frac{b_s(d)}d,
\qquad b_s(p^j)=Z(p^j)^s-Z(p^{j-1})^s,
\qquad J_s(d)=\log\frac{\max_e w_s(e)}{w_s(d)}
$$

has a different objective. The classical support-loss method motivates its decomposition, but Proposition 5 supplies neither its uniform editing bound nor its power-sum or complementary-moment estimates without an additional argument. Conversely, the **unweighted** assertion that a growing reduced residue class has at most one sufficiently large Robin violation follows by a short classical support-loss argument applied to $n/\varphi(n)$, combined with prime-number and Mertens estimates. That synthesis requires no Fibonacci encoding and must not be advertised as a FIB-specific method or historical novelty. The project's weighted residual statement remains a separate assertion.

## A finite resource certificate for the same arbitrary host

This application uses the classical benefit with its arbitrary-integer
domain, finite layer-cake summation, and the quantitative prime estimates
already cited in [Dusart 2010](../Weil/dusart2010estimates.md). It does not
apply Proposition 5's superabundant conclusion to the host. The following
is a paper derivation of a sufficient certificate, not a claim of a new
benefit method or a Lean-verified estimate.

Fix $s>0$ and choose the maximal CA optimizer $C=C_s$ of $Z(m)m^{-1/s}$:
include every zero-cost threshold layer. For the **same actual integer**
$N\ge1$, put $a_p=v_p(C)$, $e_p=v_p(N)$ and

$$
\ell_{p,j}=\log\frac{Z(p^j)}{Z(p^{j-1})},\qquad
c_{p,j}=s\ell_{p,j}-\log p,\qquad
D_s(N)=s\operatorname{Ben}_{C,1/s}(N).
$$

The accepted layers are exactly $j\le a_p$, with $c_{p,j}\ge0$; all later
layers have $c_{p,j}<0$. Telescoping the existing benefit over the actually
crossed layers gives

$$
\begin{aligned}
D_s(N)&=\sum_{p:e_p>a_p}\sum_{j=a_p+1}^{e_p}|c_{p,j}|
       +\sum_{p:e_p<a_p}\sum_{j=e_p+1}^{a_p}|c_{p,j}|,\\
E_+&=\sum_p(e_p-a_p)_+\log p,\qquad
E_-=\sum_p(a_p-e_p)_+\log p,\\
E_+-E_-&=\log(N/C).
\end{aligned}
$$

Thus $E_+=\log u$ and $E_-=\log v$ for the reduced whole-host ratio
$N/C=u/v$. In particular, with $g=\gcd(N,C_s)$,

$$
E_+=\log(N/g),\qquad E_-=\log(C_s/g).
$$

Once the same-price reference and the actual host have been obtained,
these two resource inputs need only their gcd; factoring the host's
remaining cofactor is unnecessary for this lower certificate. This
reference is $C_s$, not the increment reference $n_y$
in FIB equation (230.4); a reconstructed ratio to $n_y$ cannot silently
replace it. No exponent rearrangement or replacement of $N$ is allowed.

For $0\le h<1$, define the available weak-cost resources

$$
\begin{aligned}
A_+(h)&=\sum_{p}\sum_{\substack{j>a_p\\|c_{p,j}|\le h\log p}}\log p,\\
A_-(h)&=\sum_{p}\sum_{\substack{1\le j\le a_p\\|c_{p,j}|\le h\log p}}\log p.
\end{aligned}
$$

Both are finite. For each side, the actual crossed resource costing more
than $h$ per unit is at least $(E_\pm-A_\pm(h))_+$. The finite layer-cake
formula therefore supplies, for $0<h_0<1$,

$$
D_s(N)\ge
\int_0^{h_0}(E_+-A_+(h))_+\,dh
+\int_0^{h_0}(E_--A_-(h))_+\,dh.
$$

The two terms refer to the same exponent vector; they are not independently
chosen optimal hosts.

## Prime thresholds, higher layers, and endpoint costs

For $t>0$, let $x(t)>1$ be the unique root

$$
t\log(1+1/x(t))=\log x(t).
$$

Write $x_s=x(s)$, $x_-=x(s/(1+h))$ and $x_+=x(s/(1-h))$. The first-layer
part of $A_-$ is exactly the logarithmic prime mass in the **closed**
interval $[x_-,x_s]$; the first-layer part of $A_+$ is that in $(x_s,x_+]$.
In particular, deleting a tied first layer has zero cost and belongs to
$A_-(0)$. The left endpoint must not be subtracted with the convention
$\vartheta(x)=\sum_{p\le x}\log p$ when it is prime.

For higher layers use the existing geometric marginal bound
$\ell_{p,j}\le p^{-j}$; its repository statement is
`golden_layer_marginal_le_inv_pow` in
`D5/S3/Arith/GoldenLayerMarginalDecay.lean`, after multiplication by
$\log p$. There is also a direct separation check: with
$T_j=p+\cdots+p^j$,

$$
\ell_{p,j}=\log(1+1/T_j)>\frac1{T_j+1},\qquad
p\ell_{p,j+1}<\frac p{T_{j+1}}=\frac1{T_j+1}.
$$

Hence $\ell_{p,j}/\ell_{p,j+1}>p\ge2$. For $h\le1/3$, at most one layer
per prime can have $s\ell_{p,j}/\log p\in[1-h,1+h]$. Every weak layer
$j\ge2$ also satisfies

$$
p^2\log p\le\frac{s}{1-h}\le\frac{3s}{2}.
$$

Let $P_2>1$ solve $P_2^2\log P_2=3s/2$. The entire higher-layer resource
on either side is consequently at most $\vartheta(P_2)$, counting possible
ties as well as nonzero costs.

Take $y\ge6$, $s=y\log y$ and $0<h_0\le1/3$. Set

$$
\eta_y=\sup_{y/2\le u\le3y/2}|\vartheta(u)-u|,\qquad
B_y=\vartheta(P_2)+2\eta_y+\log(3y/2).
$$

The roots used for $0\le h\le h_0$ lie in $[y/2,3y/2]$. Indeed,
$x_s<y$, and the function $T(x)=\log x/\log(1+1/x)$ obeys
$T'(x)>T(x)/x$ for $x>1$. This follows from

$$
\frac{xT'(x)}{T(x)}
=\frac1{\log x}+\frac1{(x+1)\log(1+1/x)}
\ge\frac1{\log x}+\frac{x}{x+1}>1.
$$

It gives $x_+\le x_s/(1-h)$ and $x_-\ge x_s/(1+h)$.
The remaining lower endpoint follows from
$T(y/2)\le(y/2+1)\log(y/2)<3s/4$.
Combining the interval masses, both prime errors and the higher layers
gives the simultaneous finite bounds

$$
\boxed{
A_+(h)\le\frac{yh}{1-h}+B_y,\qquad
A_-(h)\le\frac{yh}{1+h}+B_y
\quad(0\le h\le h_0).
}
$$

The $\log(3y/2)$ term pays the possible closed left endpoint. The cited
prime estimates give $B_y=O(y/\log^2y+\sqrt y)$, since $P_2<2\sqrt y$.
These are bounds for every host at the same price; they do not assert a
favorable sign for the prime error.

For a fixed $h>0$, the first-layer prime masses are asymptotic to
$yh/(1-h)$ and $yh/(1+h)$ respectively. Thus a bound
$A_+(h)\le(1+o(1))yh+o(y)$ cannot hold uniformly on a fixed nonzero
$h$ interval. A common linear bound can use $y h/(1-h_0)+B_y$;
its coefficient approaches one only when $h_0\to0$.

## The source-preserving Robin consumer

Put $z_\pm=(E_\pm-B_y)_+$ and define

$$
\begin{aligned}
t_+(z)&=\min\{h_0,z/(y+z)\},\\
t_-(z)&=\begin{cases}
\min\{h_0,z/(y-z)\},&z<y,\\
h_0,&z\ge y,
\end{cases}\\
G_+(z)&=(z+y)t_+(z)+y\log(1-t_+(z)),\\
G_-(z)&=(z-y)t_-(z)+y\log(1+t_-(z)).
\end{aligned}
$$

Integration of the two resource bounds gives
$D_s(N)\ge G_+(z_+)+G_-(z_-)$. When
$z_+\le yh_0/(1-h_0)$ and $z_-\le yh_0/(1+h_0)$, these simplify to

$$
G_+(z_+)=z_+-y\log(1+z_+/y),\qquad
G_-(z_-)=-z_--y\log(1-z_-/y).
$$

In the unsaturated ranges displayed above, for $z_\pm=o(y)$ each has
leading term $z_\pm^2/(2y)$. This is an application of the classical
quadratic threshold mechanism; a positive
estimate requires actual edit resources beyond the endpoint and error
allowance $B_y$.

With $\mathcal Q_s=Z(C_s)^s/C_s$, the exact same-host identity in FIB
(234.10) shows that, for $N>5040$,

$$
\boxed{
G_+(z_+)+G_-(z_-)
>\log\mathcal Q_s+\log N
-s\log(e^\gamma\log\log N)
}
$$

is sufficient for Robin at that $N$. No superabundant property is needed.
For a same-price optimizer $N=C_s$, however, $E_+=E_-=D_s(N)=0$;
deleting a tied layer gives another zero-benefit optimizer. Consequently
this certificate cannot exclude all low-loss candidates without additional
same-host information. The FIB remainder, window and shared-divisor
conditions have not been shown to force the displayed strict budget.
The global RH objective remains unresolved.

## Low increment loss supplies a smaller reconstruction height

The same certificate can also be used in the reverse direction to bound
edit resources from an already known upper benefit. This application
combines the classical capacity calculation above with the existing
increment/benefit comparison in FIB (234.5)–(234.8); it makes no additional
prime-distribution assumption.

Fix $h_0=1/3$. The common capacity bound is
$A_\pm(h)\le(3y/2)h+B_y$. With $z_\pm=(E_\pm-B_y)_+$, layer-cake gives

$$
D_s(N)\ge F_y(z_+)+F_y(z_-),\qquad
F_y(z)=\begin{cases}
z^2/(3y),&0\le z\le y/2,\\
z/3-y/12,&z\ge y/2.
\end{cases}
$$

Consequently $D_s(N)<y/12$ forces both $z_\pm<y/2$ and gives the finite
resource bound

$$
E_++E_-\le2B_y+\sqrt{6yD_s(N)}.
$$

For a fixed $K>0$, put $\ell=\log y$, $R=y/\ell^2$ and take an arbitrary
positive integer $d$ with the existing increment loss $J_s(d)\le KR$.
Equation (234.5), with its nonnegative local correction, gives

$$
D_s(d)\le J_s(d)+\delta_s
\le KR+O(\log\ell)=o(y).
$$

Since $B_y=O(y/\ell^2+\sqrt y)=o(y/\ell)$, the preceding finite bound
therefore yields, uniformly for this same low-loss set,

$$
\sum_p|v_p(d)-v_p(C_s)|\log p=O_K(y/\ell).
$$

To transport this to the **unchanged** reference $n_y$ in FIB (230.4),
note first that $y-1<x_s<y$: the lower inequality follows from
$T(y-1)\le y\log(y-1)<s$. For primes above
$H=\sqrt{s/\log2}$, both references have exponent at most one, and they
can differ only for a prime in $(x_s,y]$, an interval of length less than
one. That resource is at most $\log y$. For $p\le H$, the geometric
marginal bound gives $v_p(C_s)\log p\le\log s+O(1)$, and definition
(230.4) gives $v_p(n_y)\log p=O(\log s)$. There are at most $H$ such
primes. Thus

$$
\sum_p|v_p(C_s)-v_p(n_y)|\log p
=O(\sqrt s\log s+\log y)=o(y/\ell).
$$

The triangle inequality for the same prime-exponent resource now gives

$$
\boxed{
\mathcal L(d,n_y)=O_K(y/\log y)
\quad\text{uniformly when }J_s(d)\le K y/(\log y)^2.
}
$$

This sharpens the $O_K(y/\sqrt{\log y})$ height input in FIB (230.7)
by reuse of the benefit comparison and quantitative capacity. For a
reduced ratio $d/n_y=\alpha/\beta$, it bounds both $\log\alpha$ and
$\log\beta$. The [whole-host reconstruction application](../Arith/monagan2004reconstruction.md)
retains its separate host-cofactor, integer-bound, unit, divisibility,
window and source checks. An asymptotic height improvement is not an
effective reconstruction threshold or a positive Robin margin. It does
not prove that the actual host's gcd resources satisfy the strict budget
in the preceding section.

## An explicit thin-layer capacity for the same arbitrary host

The existing [uniform inventory application CR40](../Estimation/trureturing2026pricegapconvexity.md#the-prime-interval-supplier-and-both-competitor-costs-control-actual-stock)
already has a square-root buffer for actual core activations. The
following is an explicit application to the arbitrary-integer benefit
above, using a uniform short-interval prime bound. It is not a new sieve,
quadratic-cost mechanism, or literature-priority claim. All conclusions
here are paper derivations, without Lean verification.

Let $a\ge16$, $s=a\log a$, and reuse the **maximal** reference $C=C_s$,
including every zero-cost tied layer. For the same positive integer $n$,
write

$$
\begin{aligned}
\lambda_{p,j}&=\ell_{p,j}/\log p,\qquad b_p=v_p(C),\\
\beta_a(n)&=\log Z(C)-\log Z(n)+\frac{\log n-\log C}{s},\\
E_a(n)&=\sum_p|v_p(n)-b_p|\log p
       =\log\frac{nC}{\gcd(n,C)^2}.
\end{aligned}
$$

Thus $s\beta_a(n)=D_s(n)$ is the existing benefit account. Define the
complete weak-layer capacity, including ties and all prime powers, by

$$
\mathfrak C_a(h)=
\sum_{\substack{p\ {\rm prime},\ j\ge1\\
                 |s\lambda_{p,j}-1|\le h}}\log p.
$$

The quantitative bound used below is

$$
\boxed{\mathfrak C_a(h)\le24ah+32\sqrt a}
\qquad(a\ge16,\ 0\le h\le1/4).
\tag{TC.1}
$$

Its prime input is [Yamada, arXiv:2312.16090v1](../Scale/yamada2023arbitraryintervals.md),
Theorem 2, p.3, with modulus one. It gives, for every real $x>0$ and
$y>1$,

$$
\pi(x+y)-\pi(x)<\frac{2y}{\log y+0.8601}<\frac{2y}{\log y}.
$$

This is used as a preprint input, not an independently verified sieve
proof. For the higher layers use the already cited
[Dusart bound](../Weil/dusart2010estimates.md#同一-robin-来源的有效素数幂修正)
$\vartheta(t)<2t$ for $t\ge1$.

To check the application, put $T_j=p+\cdots+p^j$. The exact marginal
already used above satisfies

$$
\ell_{p,j}>\frac1{T_j+1}>p\ell_{p,j+1},
\qquad T_{j+1}=p(T_j+1).
$$

Since $(1+h)/(1-h)\le5/3<2$, at most one weak layer occurs per prime.
A weak layer with $j\ge2$ has
$p^2\log p<(4/3)a\log a$, hence $p<2\sqrt a$. Its entire prime mass
is at most $\vartheta(2\sqrt a)<4\sqrt a$, in particular at most
$8\sqrt a$.

For $a^{-1/2}\le h\le1/4$, the first-layer inequalities

$$
\frac1{(p+1)\log p}<\lambda_{p,1}<\frac1{p\log p}
$$

place every weak first-layer prime strictly in
$((1-2h)a,(1+2h)a)$. On the left, $ha\ge\sqrt a\ge4$ gives
$p+1\le(1-h)a$, contradicting
$\lambda_{p,1}\le(1+h)/s$. On the right,
$1/(1+2h)<1-h$ contradicts the lower weak-layer threshold.
The interval has positive start, length $4ha\ge4\sqrt a$, and
$\log p\le(3/2)\log a$. Its weighted prime mass is consequently at most

$$
\frac{8ha}{\log(4ha)}\frac32\log a\le24ha.
$$

Add the higher-layer allowance. For $0\le h<a^{-1/2}$, monotonicity
bounds the entire capacity by its value at $a^{-1/2}$, which is at most
$32\sqrt a$. This proves (TC.1), including $h=0$ and $a=16$.

### A finite loss bound and the conditional near-extremal radius

Set

$$
H_a(z)=\begin{cases}
z^2/(48a),&0\le z\le6a,\\
z/4-3a/4,&z\ge6a.
\end{cases}
$$

For the actual layers crossed between $n$ and $C$, reuse the exact
benefit decomposition and the finite layer-cake argument. They give

$$
\begin{aligned}
s\beta_a(n)
&\ge\int_0^{1/4}(E_a(n)-\mathfrak C_a(h))_+\,dh\\
&\ge H_a\bigl((E_a(n)-32\sqrt a)_+\bigr).
\end{aligned}
\tag{TC.2}
$$

A tied removal contributes to $E_a(n)$ at cost zero and is already
counted in $\mathfrak C_a(0)$; no tie is discarded. This alternative
bound may be combined with the earlier capacity bound by taking their
maximum. Adding both would spend the same benefit twice.

For any $M>0$ and $a>\max\{16,(4M/3)^2\}$, it follows that

$$
\beta_a(n)\le\frac M{\sqrt a\log a}
\quad\Longrightarrow\quad
E_a(n)\le32\sqrt a+\sqrt{48M}\,a^{3/4}.
\tag{TC.3}
$$

Indeed $s\beta_a(n)\le M\sqrt a<3a/4=H_a(6a)$ forces the quadratic
branch in (TC.2). This is a conditional radius for every positive
integer at the same price. It does not assert that each Robin violation
has that benefit upper bound. At the larger increment-loss budget used
in the preceding reconstruction application, it only recovers the
already known $O(a/\log a)$ order; that order is not an additional result.
The new usable version here is the explicit buffer and the conditional
$a^{3/4}$ radius, rather than a uniform improvement of every old bound.

### Retain the full signed tail and the original FIB window

Use the logarithmic Robin margin
$\Delta_{\log}(n)=\gamma+\log\log\log n-\log Z(n)$, for $n>e$.
Let $I_\psi(a)$, $C_{\rm pp}(a)$ and $D^*(a)$ be exactly the
[independent full-support quantities in the Polak source note](../Analytic/polak2026finiterobinca.md#directly-reusable-effective-core):

$$
\begin{aligned}
I_\psi(a)&=\int_a^\infty(\psi(t)-t)
                    \frac{1+\log t}{t^2\log^2t}\,dt,\\
D^*(a)&=\sum_{p\le a}\min_{j\ge1}
 \left\{\frac{(j-1)\log p}{a\log a}
                   -\log(1-p^{-(j+1)})\right\}-C_{\rm pp}(a).
\end{aligned}
$$

There is a small correction between that full-support optimizer and
$C$. Define

$$
J(a)=\sum_{p\le a}
 \left(\frac{\log p}{a\log a}-\log(1+1/p)\right)_+.
$$

All primes of $C$ are less than $a$, and every $p\le a-1$ has its first
layer strictly accepted. The full-support optimizer $C^+$ therefore only
adds a possible first layer at one prime in $(a-1,a]$. Its price-objective
loss is exactly $J(a)$. The summand before its positive part increases
with $p$, so

$$
0\le J(a)\le\frac1a-\log(1+1/a)<\frac1{2a^2}.
$$

The cited full-support identity at $C^+$, followed by the exact benefit
of the unchanged integer $n$, gives, with $A=\log n$,

$$
\begin{aligned}
\Delta_{\log}(n)&=I_\psi(a)+D^*(a)-J(a)+\beta_a(n)+\kappa_a(A),\\
\kappa_a(A)&=\log\log A-\log\log a-\frac{A-a}{a\log a}.
\end{aligned}
\tag{TC.4}
$$

For the sign check, replacing $C^+$ by the unconstrained optimizer $C$
**decreases** the full-support account by $J(a)$. Explicitly the former
account is
$\gamma+\log\log a-\log Z(C^+)+(\log C^+-a)/s$;
then add $\beta_a(n)$ and the displayed tangent remainder. No CA
property of the actual $n$ is assumed.

For prime $r\ge7$, put $V=F_r$ and retain the exact original endpoints

$$
X_-=1+V\lceil V/10\rceil,\quad
X_+=1+V\lfloor V/5\rfloor,\quad
a=\log X_-\ge16,\quad w=\log(X_+/X_-)<\log2.
$$

Every original $N=1+Vg$ has $A\in[a,a+w]$. The decreasing positive
curvature $(1+\log a)/(a^2\log^2a)$ of $\log\log a$ gives

$$
-\frac{w^2(1+\log a)}{2a^2\log^2a}\le\kappa_a(A)\le0.
$$

Thus (TC.2) and (TC.4) yield the same-host lower certificate

$$
\Delta_{\log}(N)\ge I_\psi(a)+D^*(a)
+\frac{H_a((E_a(N)-32\sqrt a)_+)}{a\log a}-R(a,w),
\quad R(a,w)=\frac1{2a^2}+
              \frac{w^2(1+\log a)}{2a^2\log^2a}.
\tag{TC.5}
$$

The existing FIB bound $a<r$ and $p\mid V\Rightarrow p\ge2r-1$ give
$(C,V)=1$. Writing the actual reduced ratio $N/C=u/v$ retains precisely

$$
\begin{gathered}
u,v\in\mathbb N_{>0},\quad(u,v)=1,\quad v\mid C,\\
Cu\equiv v\pmod V,\qquad X_-v\le Cu\le X_+v,\\
E_a(N)=\log(uv).
\end{gathered}
\tag{TC.6}
$$

Conversely these conditions give the integer $N=Cu/v$ in exactly the
original progression and multiplier window. A lower certificate from
(TC.5) therefore has to hold on these **joint** pairs, not on separately
optimized numerator and denominator sets.

The sufficient inequality

$$
I_\psi(a)+D^*(a)+
\frac{H_a((\log(uv)-32\sqrt a)_+)}{a\log a}>R(a,w)
\tag{TC.7}
$$

is still unproved on the complete original candidate set. For a fixed
$K>0$ and sufficiently large $a$, an excess edit resource
$E_a(N)-32\sqrt a=Ka^{3/4}$ contributes
$K^2/(48\sqrt a\log a)$, the natural core scale. No uniform distance
of that size, signed-tail bound, or joint compensation is supplied here.
When the actual integer is $C$ itself, its benefit and edit resource
vanish, so this estimate adds no loss at all. It cannot replace the
unpaid same-source signed tail in the global CA route or prove RH.

### Congruence sparsity inside the conditional near-extremal set

The radius in (TC.3) also gives a discrete consequence that is useful for
future finite checks. It is a counting statement for the original source
window, not a replacement for the signed Robin estimate.

Let $V=F_r$ and keep the same $C=C_s$, $a$, and quotient conditions
(TC.6). If a candidate satisfies $E_a(N)\le L$, then

$$
uv\le e^L.
$$

The existing Fibonacci bounds give $(C,V)=1$. Fix a divisor $v\mid C$.
The congruence in (TC.6) determines one residue class

$$
u\equiv C^{-1}v\pmod V.
$$

Consequently, whenever $e^L<V$, the interval
$1\le u\le e^L/v<V$ contains at most one admissible numerator for this
fixed denominator. Therefore

$$
\boxed{
\#\{(u,v): uv\le e^L,\ v\mid C,\ Cu\equiv v\pmod V\}
\le \tau(C).
}
\tag{TC.8}
$$

This retains the denominator divisibility and the exact unit residue; it
does not count separately optimized numerators and denominators. Combining
(TC.3) with $a\asymp\log V$ shows that, for every fixed $M$, its conditional
radius

$$
L=32\sqrt a+\sqrt{48M}\,a^{3/4}
$$

satisfies $L=o(\log V)$ along the Fibonacci rank family. Hence $e^L<V$
eventually and the number of such near-extremal pairs is at most
$\tau(C)$. The needed size estimate is available from the existing CA
layer threshold. Every accepted prime layer has

$$
v_p(C)\log p\le\log s+O(1),
$$

as recorded in the preceding resource comparison; primes above the first
threshold have exponent at most one. Hence for $p>\sqrt a$,
$v_p(C)=O(1)$, while for $p\le\sqrt a$,
$\log(v_p(C)+1)=O(\log\log a)$. The standard prime-counting bound then
gives

$$
\log\tau(C)
=\sum_{p\mid C}\log(v_p(C)+1)
=O\!\left(\frac{a}{\log a}\right).
\tag{TC.9}
$$

Since $a=2\log V+O(1)$ for $X_-=1+V\lceil V/10\rceil$,

$$
\boxed{\tau(C)=\exp O\!\left(\frac{\log V}{\log\log V}\right)=V^{o(1)}.}
$$

Thus the subpolynomial conclusion uses an existing CA threshold and a
standard prime-counting estimate; it does not assume an unproved bound on
$\log C$.

### A sparse-exception reduction for the signed budget

The two estimates above combine into a useful quantifier split. Fix $M>0$
and take $a$ large enough that
$\sqrt{48M}\,a^{3/4}<6a$. Define

$$
L_M(a)=32\sqrt a+\sqrt{48M}\,a^{3/4}.
$$

For a candidate satisfying $E_a(N)>L_M(a)$, monotonicity of $H_a$ gives

$$
\frac{H_a((E_a(N)-32\sqrt a)_+)}{a\log a}
>\frac{M}{\sqrt a\log a}.
$$

Therefore (TC.5) implies the pointwise implication

$$
\boxed{
I_\psi(a)+D^*(a)+\frac{M}{\sqrt a\log a}>R(a,w)
\ \Longrightarrow
\Delta_{\log}(N)>0
}
\tag{TC.10}
$$

for every original-window candidate with $E_a(N)>L_M(a)$. The candidates
where this implication does not apply satisfy $E_a(N)\le L_M(a)$ and are
bounded in number by (TC.8)--(TC.9):

$$
\boxed{
\#\{N\text{ in the window}:E_a(N)\le L_M(a)\}
\le \tau(C)=F_r^{o(1)}.
}
\tag{TC.11}
$$

Thus a proof of the signed inequality in (TC.10), together with a direct
certificate for the exceptional set in (TC.11), would settle the complete
Fibonacci window at that rank. This is a genuine reduction of the joint
quantifiers: the signed input is needed uniformly for the bulk, while the
remaining exact arithmetic work is subpolynomial. Neither ingredient is
currently available, and the reduction concerns this Fibonacci family only;
it is not a reduction of all integers to the family and therefore is not by
itself a proof of RH.

The conclusion only sparsifies the candidates left by the benefit bound.
Each surviving pair still has to satisfy the window and the complete signed
tail in (TC.5), and (TC.8) supplies neither a positive Robin margin nor a
uniform way to verify all the remaining pairs. It is therefore a finite
or subpolynomial reduction of the unresolved joint problem, rather than an
RH proof.

### A same-source friable-core count

The large-friable-component estimate recorded in
[the Tenenbaum--Wang interface](../Scale/tenenbaumwang2026largefriablecomponent.md)
can be applied to the same reduced pair, rather than to a separately
optimized integer. Keep the original-window conditions (TC.6), put
$g_0=\gcd(N,C)=C/v$, and choose $y$ at least as large as every prime factor
of $C$. Since $g_0\mid N$ and $g_0$ is $y$-friable,

$$
N_y\ge g_0=\frac Cv.
$$

Therefore, for any $L\ge0$,

$$
E_a(N)=\log(uv)\le L
\quad\Longrightarrow\quad
v\le e^L
\quad\Longrightarrow\quad
N_y\ge Ce^{-L}.
$$

Let $z=Ce^{-L}$ and let $x$ satisfy $X_+\le x$ and $z\le x/2$.
Whenever

$$
\max\{2,\log z\}\le y\le z,
$$

Tenenbaum--Wang's Theorem 1 gives the independent population bound

$$
\boxed{
\#\{N\text{ in the original window}:E_a(N)\le L\}
\le
\min\{\tau(C),\Theta(x,y,z)\},
}
\tag{TC.12}
$$

where

$$
\Theta(x,y,z)
=x\exp\!\left(-\nu\log\!\bigl(\nu\log(3\nu)\bigr)+O(\nu)\right),
\qquad
\nu=\frac{\log z}{\log y}.
$$

The left-hand set still carries $Cu\equiv v\pmod V$ and the original
multiplier window; the friable estimate only supplies a second upper bound
on its cardinality. It does not bound the complete prime-power weight of
that same $N$, the CA defect $D^*(a)$, or the signed Robin tail. Thus
(TC.12) is a reusable sparse-counting refinement of (TC.11), while the
pointwise signed condition (TC.10) remains the unresolved step needed for
an all-candidate conclusion.

## Charge the actual removals before bounding additions

The classical layer identity also permits a stronger pointwise use of the
same gcd data. Put $g=\gcd(N,C_s)$ and $v=C_s/g$. The known factorization
of $C_s$ fixes every removed layer, with exact cost

$$
R_s(v)=\sum_{p\mid v}\sum_{j=a_p-v_p(v)+1}^{a_p}c_{p,j}
=s\log\frac{Z(C_s)}{Z(C_s/v)}-\log v\ge0.
$$

Under the same finite capacity assumptions above, the already established
addition bound and this exact removal cost give

$$
\boxed{
D_s(N)\ge R_s(v)+G_+(z_+)
\ge G_-(z_-)+G_+(z_+).
}
$$

The two terms in the first lower bound pay disjoint parts of the existing
layer decomposition: all actual removals and only the additions. The
removal-side capacity bound gives $R_s(v)\ge G_-(z_-)$, which proves the
second comparison. Thus the sharper certificate is
$R_s(v)+G_+(z_+)>T_s(N)$ for the same actual host. Whenever
$R_s(v)>G_-(z_-)$, its lower bound increases by that difference. No
factorization of $N/g$ is needed to evaluate either input.

This is a direct application of the classical layer decomposition and the
existing capacity bounds, not a new benefit theorem or a Lean result. It
does not assert that the improvement exceeds the actual budget on the FIB
residual set. Tied removals retain their exact zero costs.

## Exact zero-benefit exceptions use at most four branches

Proposition 4(c)–(d) and its proof, printed pp.70–71, already give the
complete tied-optimizer alternatives. The proof uses the six-exponentials
theorem, cited there through Lang, to exclude a common threshold for three
distinct primes. It retains both exponent choices at each tied prime.
This is a classical result to reuse, not a new tie theorem or a Lean result.

At the price $1/s$, keep the maximal optimizer $C_s$ and the layer notation
above, and define

$$
\mathcal T_s=\{p\mid C_s:c_{p,v_p(C_s)}=0\}.
$$

In these parameters the source's alternatives state

$$
|\mathcal T_s|\le2,\qquad
\{N\ge1:D_s(N)=0\}
=\left\{\frac{C_s}{\prod_{p\in S}p}:S\subseteq\mathcal T_s\right\}.
$$

Thus the exact zero-benefit set has one, two or four members at every
positive price. This conclusion concerns exact ties, not the number of
near-zero layers or a uniform lower bound for the next positive cost.

For the actual host, $g=\gcd(N,C_s)$ fixes the denominator $v=C_s/g$ and
therefore every removed layer. The zero-benefit alternative is precisely
that $v$ is a product of a subset of $\mathcal T_s$ and $N=g$; it cannot
become an unrestricted repetition of a free prime edit. One can retain the
source's at most four possibilities before computing the gcd, or use the
actual gcd to determine the removals directly.

Each of these integers still requires the original FIB window, residue and
qualifying-divisor checks. If an actual zero-benefit host has $T_s(N)<0$,
its budget is already paid. If it has $T_s(N)\ge0$, this classification
provides no positive loss: a source-preserving exclusion or a favourable
signed budget remains necessary. The [fixed-price screening application](axler2024primorialcounting.md)
keeps these ties when its endpoint budget is zero. Neither the finite
branch list nor the gcd determines a uniform Robin margin.

## Condition addition capacity on the actual removals

Keep the same $g=\gcd(N,C_s)$, $u=N/g$, $v=C_s/g$ and exact removal
cost $R_s(v)$. Since $(u,v)=1$, no prime dividing $v$ can occur among
the actual additions. The capacity calculation above can therefore
exclude these primes before integration. Define, for $0\le h\le h_0\le1/3$,

$$
\Delta_v(h)=
\sum_{p\mid v}\sum_{\substack{j>a_p\\-c_{p,j}\le h\log p}}\log p,
\qquad A_{+,v}(h)=A_+(h)-\Delta_v(h).
$$

Both sums defining $\Delta_v$ are determined by the known factorization
of $C_s$ and the actual gcd; factoring $u$ is unnecessary. Reuse
$A_+(h)\le U_y(h):=yh/(1-h)+B_y$ at $s=y\log y$, $y\ge6$.
The addition-only layer-cake bound gives the paper-level refinement

$$
\begin{aligned}
D_s(N)&\ge R_s(v)+I_v(E_+),\\
I_v(E)&:=\int_0^{h_0}(E-U_y(h)+\Delta_v(h))_+\,dh,\\
I_v(E_+)&\ge G_+((E_+-B_y)_+),\qquad E_+=\log u.
\end{aligned}
$$

The subtraction is valid because $A_{+,v}$ is exactly the weak-layer
capacity over primes eligible for the same host. It never removes a layer
actually used by $u$. Exact removals and this addition integral still pay
disjoint costs. This is an application of the existing finite layer-cake
bound, not a new benefit theorem or a Lean-verified estimate.

The gain has a useful ceiling. Write

$$
\tau_p=\frac{-c_{p,a_p+1}}{\log p}>0\qquad(p\mid v).
$$

The marginal separation $\ell_{p,j}/\ell_{p,j+1}>p$ proved above implies
that every layer after $a_p+1$ has normalized cost greater than $1/2$.
Thus only that first post-reference layer can contribute, and

$$
\int_0^{h_0}\Delta_v(h)\,dh
=\sum_{p\mid v}(h_0-\tau_p)_+\log p.
$$

For each nonzero summand, $a_p\ge1$ and the same marginal separation gives

$$
c_{p,a_p}>
\bigl(p(1-\tau_p)-1\bigr)\log p
\ge(1-2\tau_p)\log p.
$$

Since $h_0-\tau_p\le h_0(1-2\tau_p)$ for $h_0\le1/2$, and the
last accepted layer at every $p\mid v$ is actually removed, it follows that

$$
\boxed{
0\le I_v(E_+)-G_+((E_+-B_y)_+)
\le\int_0^{h_0}\Delta_v(h)\,dh
\le h_0R_s(v).
}
$$

The first upper bound uses the one-Lipschitz property of the positive part.
A tied removed layer has $c_{p,a_p}=0$ and forces
$\tau_p>1-1/p\ge1/2$, so it contributes nothing to this refinement.
Excluding an exactly free removal cannot create an artificial positive
gain.

Every contributing prime also satisfies
$p^2\log p\le s/(1-h_0)\le3s/2$, because $a_p+1\ge2$.
Consequently

$$
\Delta_v(h)\le\vartheta(P_2),\qquad
I_v(E_+)-G_+((E_+-B_y)_+)
\le h_0\vartheta(P_2)=O(\sqrt y).
$$

This removes part of the higher-layer allowance for the actual gcd. The
prime-error allowance $2\eta_y$ in $B_y$ is unaffected. The size bound
does not give a positive lower bound for the gain or rule out payment of
a smaller residual budget at a particular host. The remaining sufficient
test is $R_s(v)+I_v(\log u)>T_s(N)$ for that same $N$; no uniform
comparison on the original FIB residual sources has been established.

## A full-modulus Jacobi test for actual addition cost

The character input here is classical quadratic reciprocity and Fibonacci
modular periodicity, recorded with their primary locators in the
[Renault note](../notes/renault2013periodrankorder.md). The application
uses the benefit decomposition above; it supplies neither a new analytic
character estimate nor a Lean-verified theorem.

Let $r>3$ be prime and $V=F_r$, with $F_0=0$, $F_1=1$. The Fibonacci
pair modulo four has period six, and $r\equiv1,5\pmod6$, so $V\equiv1\pmod4$.
Define the full-denominator Jacobi character

$$
\chi_V(a)=\left(\frac aV\right).
$$

The denominator need not be prime or squarefree. For every odd prime $p$,
quadratic reciprocity gives

$$
\chi_V(p)=\left(\frac{F_r}{p}\right),
$$

including zero when $p\mid V$. The right-hand side reads $F_r\bmod p$
from the second coordinate of $M^r\alpha$, where
$M(a,b)=(b,a+b)$ and $\alpha=(1,0)$. This coordinate is different from
the quantity readout $2a+3b$. The existing golden/Fibonacci modular pair
in `D5/S3/Arith/GoldenApparition.lean` already supplies this interface;
its private `phi_pow_eq_fib_pair_mod` is not a missing theorem to reprove.
Neither the symbol evaluation nor the modular recurrence requires
factorization of $V$.

For the small primes, the finite pair recurrences modulo eight, three and
five have periods twelve, eight and twenty respectively. Together with
the supplementary law at two and reciprocity they give the familiar
specializations

$$
\begin{aligned}
\chi_V(2)&=\begin{cases}
1,&r\equiv1,11\pmod{12},\\
-1,&r\equiv5,7\pmod{12},
\end{cases}\\
\chi_V(3)&=\begin{cases}
1,&r\equiv1,7\pmod8,\\
-1,&r\equiv3,5\pmod8,
\end{cases}\\
\chi_V(5)&=\left(\frac r5\right)\quad(r>5),\qquad
\chi_{F_5}(5)=0.
\end{aligned}
$$

These symbol values are arithmetic observations, not the five containment
labels `[null,2,3,2 5,5]`. For instance $r\equiv1\pmod{120}$ gives all
three values $+1$; no fixed negative prime is forced by those three tests.
This says nothing about signs throughout the growing price-prime prefix.

Now retain the **same actual host** $N>5040$ and require $N\equiv1\pmod V$.
Use $C=C_s$, $g=\gcd(N,C)$, $u=N/g$ and $v=C/g$. Both $g$ and $u$
are units modulo $V$, since they divide $N$; this does not require
$\gcd(C,V)=1$. Multiplicativity gives

$$
\chi_V(g)\chi_V(u)=1,\qquad \chi_V(u)=\chi_V(g).
$$

In the branch $\chi_V(g)=-1$, some prime dividing the actual $u$ has
negative character and odd exponent in $u$. It is eligible for additions:
$p\nmid vV$. The negative endpoint also certifies nonprincipality, without
a separate nonsquare theorem for $V$. A positive full Jacobi symbol at a
composite denominator does not certify a square root; the branch
$\chi_V(g)=1$ remains outside this particular test.

For eligible primes define the first-entry cost

$$
b_s(p)=\log p-s\ell_{p,a_p+1}>0.
$$

Maximality of $C$ includes every tied layer, so every post-reference cost
is strictly positive. Its full addition block
$W_p(k)=-\sum_{j=a_p+1}^{a_p+k}c_{p,j}$ is increasing for $k\ge1$ and
$W_p(1)=b_s(p)$. Thus the negative-endpoint branch has the paper-level bound

$$
D_s(N)\ge R_s(v)+m_s(V,v),\qquad
m_s(V,v):=\min_{\substack{p\nmid vV\\\chi_V(p)=-1}}b_s(p)>0.
$$

The actual $u$ supplies an eligible negative prime. The minimum is
attained because $C$ has finite support and $b_s(p)\to\infty$ as
$p\to\infty$. This is a fixed-price positive bound, not a uniform gap
along growing prices and moduli.

Use the inherited budget normalization

$$
T_s(N)=\log\mathcal Q_s+\log N-s\log(e^\gamma\log\log N),
\qquad \mathcal Q_s=Z(C_s)^s/C_s,
$$

so $D_s(N)>T_s(N)$ is exactly strict Robin. Write
$B=T_s(N)-R_s(v)$. If $B<0$, removals already pay the budget.
For $B\ge0$, define

$$
\mathcal P_B=\{p\text{ prime}:p\nmid vV,\ b_s(p)\le B\}.
$$

A sufficient test for this same host is
$\chi_V(g)=-1$ and $\chi_V(p)=1$ for every $p\in\mathcal P_B$.
It gives $m_s(V,v)>B$ and hence $D_s(N)>T_s(N)$. Zeros cannot occur
on this eligible set.

The test has an explicit finite cutoff. Put $P=\max\{s,e^{B+1}\}$.
For $p>P$, one has $\log p>1$ and $p\log p>s$, so $a_p=0$ and

$$
b_s(p)=\log p-s\log(1+1/p)
\ge\log p-s/p>B.
$$

Only primes $p\le P$ can belong to $\mathcal P_B$. This finiteness is
not an efficiency bound at the actual source scale. Evaluating $g$, the
exact removals and the symbol tests requires no factorization of $u$.

In the common capacity range $s=y\log y$, $y\ge6$, $0<h_0\le1/3$, the
safe combination in the negative-endpoint branch is

$$
D_s(N)\ge R_s(v)+\max\{I_v(\log u),m_s(V,v)\}.
$$

Both lower bounds pay the same additions, so they cannot be summed
without a further allocation to disjoint costs. The missing joint input
is enough loss on each surviving actual source's legal additions,
compared with its own $B$. The one-bit sufficient test asks for a negative
actual gcd and positive symbols at all eligible cheap primes. Neither
modular periodicity nor the generic
[Pollack nonresidue bounds](../Scale/pollack2017nonresidues.md) supplies
that comparison at the source price. Failure of this sufficient test does
not imply failure of Robin. The original window, qualifying low-loss
divisor, cofactor and all-candidate coverage remain required; no uniform
strict-budget supplier or proof of RH is supplied here.

## The Fibonacci index prime limits the unrefined sign test

Use the actual family in FIB §§230–231, writing its multiplier as $k$
to distinguish it from the gcd:

$$
V=F_r,\quad
\lceil V/10\rceil\le k\le\lfloor V/5\rfloor,\quad N=1+Vk>5040,
\quad A=1+V\lceil V/10\rceil,\quad y=\log A,\quad s=y\log y,
$$

where $r>5$ is prime. Keep the same $C_s,g,u,v$ and signed budget $B$.
The ordinary Fibonacci bound $F_r<\varphi^{r-1}$, together with $A<V^2$
and $2\log\varphi<1$, gives $1<y<r$. Hence

$$
s\ell_{r,1}=y\log y\,\log(1+1/r)
<\frac{y\log y}{r}<\log r.
$$

Thus $a_r=0$, $r\nmid C_s$ and $r\nmid v$, with strictness unaffected
by tied layers. The already existing
`fibonacci_apparition_entry_point` in `D5/S3/Arith/GoldenApparition.lean`
supplies the classical congruence

$$
F_r\equiv\left(\frac5r\right)\pmod r.
$$

In particular $r\nmid V$. Reciprocity and the supplementary law at
minus one give

$$
\chi_V(r)=\left(\frac{F_r}{r}\right)
=\left(\frac{(5/r)}r\right)=-1
\quad\Longleftrightarrow\quad r\equiv3,7\pmod{20}.
$$

On these two classes the index prime is always eligible for the unrefined
minimum, at exact cost

$$
b_s(r)=\log r-s\log(1+1/r)>0,\qquad m_s(V,v)\le b_s(r).
$$

Therefore $B\ge b_s(r)$ prevents the unrefined negative-gcd test
$m_s(V,v)>B$ from succeeding. This is a limitation of that relaxation;
it is not a Robin counterexample or an assertion that $r\mid u$.
For the same actual host the congruence instead gives

$$
r\mid u\quad\Longleftrightarrow\quad r\mid N
\quad\Longleftrightarrow\quad k\equiv1\pmod r.
$$

The conditional threshold does not exhibit a surviving actual source
with $B\ge b_s(r)$. The [existing window budget](axler2024primorialcounting.md)
gives $B\le T_s(N)\le T_s(X)$, where $X=1+V\lfloor V/5\rfloor$.
If $T_s(X)<b_s(r)$, this index-prime obstruction never activates in
that window. If $T_s(X)<0$, the window is already paid by the nonnegative
benefit. Any claim of obstruction on the residual set requires an actual
source there, retaining its low-loss divisor and cofactor.

## Charge the actual index block before reading the remaining sign

On the same two negative-index classes, retain

$$
e=v_r(N)=v_r(u),\qquad u_0=u/r^e,\qquad
L_r=W_r(e)=e\log r-s\log Z(r^e),\qquad W_r(0)=0.
$$

This is the exact cost of all additions at $r$, since $a_r=0$.
The remaining factor has neither $r$ nor any prime dividing $vV$.
For every $j\ge1$, its required source resolution can be read as

$$
r^j\mid N
\quad\Longleftrightarrow\quad
k\equiv-F_r^{-1}\pmod{r^j}.
$$

The inverse exists because $r\nmid V$; $F_r\bmod r^j$ is the same
modular $M^r\alpha$ readout used above. These are actual valuation probes,
not a factorization of $V$ or an assumption about the unseen additions.

Multiplicativity transports the endpoint after charging that block:

$$
\chi_V(u_0)=\chi_V(g)(-1)^e.
$$

If this remaining sign is negative, the actual $u_0$ contains a distinct
eligible negative-character prime. Define, only in that branch,

$$
m_s^{[r]}(V,v)=
\min_{\substack{p\nmid vrV\\\chi_V(p)=-1}}b_s(p)>0.
$$

The actual factor ensures nonemptiness, and the same finite-tail argument
as above ensures attainment. The paper-level certificate is

$$
\begin{cases}
D_s(N)\ge R_s(v)+L_r+m_s^{[r]}(V,v),
 &\chi_V(g)(-1)^e=-1,\\
D_s(N)\ge R_s(v)+L_r,
 &\chi_V(g)(-1)^e=1.
\end{cases}
$$

The index block and the distinct residual prime pay disjoint costs.
If $\chi_V(g)=1$ and $e$ is odd, a second negative prime is forced,
although the original negative-gcd test was inactive. If $e=0$ and
$\chi_V(g)=-1$, the unused index prime disappears from the minimum.
For an originally negative gcd, this bound is never weaker than
$R_s(v)+m_s(V,v)$: when $e\ge1$, $L_r\ge b_s(r)\ge m_s(V,v)$;
when $e=0$, the new minimum ranges over a subset of the old one.

Put $B_r=T_s(N)-R_s(v)-L_r$. A negative $B_r$ is already paid.
Otherwise, in the negative remaining-sign branch, $m_s^{[r]}(V,v)>B_r$
is sufficient. The same cutoff $P_r=\max\{s,e^{B_r+1}\}$ applies to
this unrestricted cheap-prime test.

For pruning by the actual source, define a different minimum, only in
the negative remaining-sign branch:

$$
m_{s,\mathrm{act}}^{[r]}(N)=
\min_{\substack{p\nmid vrV,\ v_p(u_0)\ \mathrm{odd}\\
\chi_V(p)=-1}}b_s(p).
$$

The negative endpoint supplies a nonempty subset of the finite actual
prime support, so this minimum exists and is at least $m_s^{[r]}(V,v)$.
The same disjoint-cost argument gives

$$
D_s(N)\ge R_s(v)+L_r+m_{s,\mathrm{act}}^{[r]}(N).
$$

With $B_r\ge0$, actual probes may discard even $v_p(u_0)$, including
zero. If every eligible $p\le P_r$ with $b_s(p)\le B_r$ and odd
$v_p(u_0)$ has $\chi_V(p)=1$, the finite cutoff gives
$m_{s,\mathrm{act}}^{[r]}(N)>B_r$ and hence strict Robin for this host.
This need not imply $m_s^{[r]}(V,v)>B_r$: a cheap negative prime absent
from $u_0$ can keep that unrestricted minimum small. No efficiency or
uniform source correlation is asserted for the actual-support test.

When $y\ge6$ and $0<h_0\le1/3$, the previously established capacity
bound still applies to all additions. It can be combined with the new
bound by taking a maximum of their addition contributions. Summing that
full capacity bound with $L_r+m_s^{[r]}$ would count the same additions
twice. These are applications of the existing block decomposition,
reciprocity and modular readout, with no new analytic theorem or Lean
verification. A uniform estimate of the same actual remaining cost
against $B_r$, with the original low-loss incidence and window retained,
is still missing; existence of a second negative prime alone supplies
neither its required cost nor a proof of RH.

## Resolve the remaining arithmetic phase beyond its Jacobi sign

The additional character input is classical. Gao–Zhao,
*Value-distribution of quartic Hecke L-functions*,
[arXiv:1809.09822v2, §2.2, PDF p.3](https://arxiv.org/pdf/1809.09822v2),
defines the Gaussian quartic power-residue symbol at an odd Gaussian
prime and extends it multiplicatively to composite denominators. Only
that definition is used here; the paper's distribution theorem over
square-free Gaussian parameters is not applied to this Fibonacci modulus.
This is an application to the existing benefit certificate, not a new
quartic-character theorem or a Lean result.

Retain the same actual family $V=F_r$, $N=1+Vk$, price $s=y\log y$
and maximal reference $C_s$ above, with $r>5$ prime. The classical Cassini
identity gives $t=F_{r-1}$ with $t^2=-1\pmod V$. Every prime $q\mid V$
is odd and $q\equiv1\pmod4$. Orient its quartic character by this root:

$$
\psi_q(n)=i^j
\quad\Longleftrightarrow\quad
n^{(q-1)/4}\equiv t^j\pmod q,
\qquad (n,q)=1,\quad j\in\mathbb Z/4\mathbb Z.
$$

In the Gaussian definition this uses the prime ideal $(q,i-t)$, whose
residue field identifies $i$ with $t$. Retain all denominator exponents:

$$
\psi_V(n)=\prod_{q^E\parallel V}\psi_q(n)^E,
\qquad (n,V)=1,\qquad \psi_V(n)^2=\chi_V(n).
$$

Neither primality nor square-freeness of $V$ is assumed. The resulting
character can have order one, two or four, so four nonempty prime classes
are not presumed. Identifying the residue root $t$ with complex $i$ does
not assert $\psi_q(t)=i$. This arithmetic character is also different
from the active composition rotation $C=MJ$ and from the existing scalar
four-orbit analysis in [§7 of the Li note](../ArithUnits/li2026nonwieferich.md).
The factorization-free evaluation below uses a classical Gaussian
quartic-Jacobi algorithm with this same root orientation.

Use the actual $g=\gcd(N,C_s)$, $u=N/g$, $v=C_s/g$ and
$e=v_r(N)$, and set $u_0=u/r^e$. The existing $y<r$ argument gives
$a_r=0$, and the existing Fibonacci entry-point congruence gives
$r\nmid V$. These inputs hold on every prime-index residue class, not
only the two classes with negative index-prime Jacobi sign. Charge the
same exact block

$$
L_r=W_r(e)=e\log r-s\log Z(r^e).
$$

Since $g,u_0\mid N$ and $N\equiv1\pmod V$, both are units modulo
$V$, without requiring $C_s$ to be a unit. Multiplicativity transports
the remaining endpoint as

$$
\psi_V(u_0)=\psi_V(g)^{-1}\psi_V(r)^{-e}.
$$

This endpoint uses the same host and its actual index-prime valuation.
When $u_0=1$, its phase is one and no remaining phase cost is forced.

For $j=1,2,3$, use the existing positive first-entry cost $b_s(p)$ and
define

$$
\beta_j=\min_{\substack{p\text{ prime},\ p\nmid vrV\\
\psi_V(p)=i^j}}b_s(p),
$$

with value $+\infty$ for an empty class. Every nonempty class has a
positive attained minimum: maximality of $C_s$ includes all ties, and
$b_s(p)\to\infty$ at fixed price. This asserts no uniform gap as $s$
and $V$ grow.

The cheapest relaxed phase-word costs on $\mathbb Z/4\mathbb Z$ are

$$
\begin{aligned}
c_0&=0,\\
c_1&=\min\{\beta_1,\beta_2+\beta_3,3\beta_3\},\\
c_2&=\min\{\beta_2,2\beta_1,2\beta_3\},\\
c_3&=\min\{\beta_3,\beta_1+\beta_2,3\beta_1\}.
\end{aligned}
$$

To use this relaxation, retain the actual prime-power word of $u_0$.
The increasing post-reference marginal costs give $W_p(k)\ge k b_s(p)$,
so repeated occurrences of one prime are charged. Replace each actual
nonzero-phase occurrence by its class minimum. Phase-zero edges and
positive-cost loops can then be deleted. A shortest nonzero-endpoint path
visits at most the four states; its undominated increment words are
$1,23,333$ for endpoint one, $2,11,33$ for endpoint two, and
$3,12,111$ for endpoint three. This gives, for the actual endpoint
$\psi_V(u_0)=i^j$, the paper-level application

$$
\boxed{D_s(N)\ge R_s(v)+L_r+c_j.}
$$

An actual endpoint guarantees a finite route even if some classes are
empty. The relaxed minimizing word need not realize its class minima
simultaneously, the real size window or the low-loss incidence; these
facts are not required for a lower bound. They would be required to claim
an actual realizing candidate.

For odd $j$, the unrefined remaining Jacobi minimum is
$m_s^{[r]}(V,v)=\min\{\beta_1,\beta_3\}$ and $c_j$ is at least this
minimum. If $\beta_3<\beta_1$, then $c_1$ is strictly larger;
if $\beta_1<\beta_3$, then $c_3$ is strictly larger. The relevant
inequalities allow an empty opposite class. A reachable phase two has
$c_2>0$, although its remaining Jacobi sign is positive. These are
conditional improvements over the sign-only bound. There is no universal
ordering against $m_{s,\mathrm{act}}^{[r]}(N)$: cheap eligible primes
absent from the host can reduce $c_j$, whereas a required repeated phase
can force more cost than one actual negative-prime minimum. Complete
actual valuations already determine these phases.

With $y\ge6$ and $0<h_0\le1/3$, the safe capacity combination is

$$
D_s(N)\ge R_s(v)+\max\{I_v(\log u),\ L_r+c_j\}.
$$

In the negative remaining-sign branch one may also include
$L_r+m_{s,\mathrm{act}}^{[r]}(N)$ inside this maximum. These contributions
bound the same additions; summing the full capacity contribution with
$L_r+c_j$ would pay them twice.

For the same host put $B_r=T_s(N)-R_s(v)-L_r$. The condition $c_j>B_r$
is sufficient to pay its strict budget. No such comparison on every
qualifying host has been established, and failure of this sufficient
condition does not disprove Robin. Phase zero, $u_0=1$ and all zero-cost
tied removals remain in scope; the actual gcd fixes each removed layer
once, rather than licensing a repeatable free phase loop. The original
window and the complete low-loss divisor contribution in
[FIB §233.5](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
still require a joint estimate. This includes $h=1$, restoration-only and
small-prime cofactors with their actual merged valuations. This
character refinement alone supplies no uniform strict budget or RH proof.

## Reuse the Gaussian quartic-Jacobi evaluator

The algorithmic input is already available in Damgård–Frandsen,
*Efficient algorithms for gcd and cubic residuosity in the ring of
Eisenstein integers*,
[BRICS RS-03-8, §5, printed pp.9–10, PDF pp.11–12](https://www.brics.dk/RS/03/8/BRICS-RS-03-8.pdf).
Despite its title, that section treats Gaussian gcd and composite quartic
symbols, with quadratic bit complexity for its specified approximate-norm
method. Bach–Sandlund,
*On Euclidean Methods for Cubic and Quartic Jacobi Symbols*,
[arXiv:1807.07719v1, §7, pp.13–14](https://arxiv.org/pdf/1807.07719v1),
distinguishes the naive exact-norm Euclidean implementation, which has
cubic worst-case schoolbook complexity, from the improved quadratic
quotient treatment. These algorithms are reused; no arithmetic algorithm
or new analytic estimate is proposed here.

For the same $V=F_r$ and $t=F_{r-1}$, form the Gaussian ideal

$$
I=(V,i-t)=\ker\bigl(\mathbb Z[i]\longrightarrow\mathbb Z/V\mathbb Z,
\ a+bi\longmapsto a+bt\bigr).
$$

The map is well-defined because $t^2=-1\pmod V$, and it is surjective.
Thus $\mathbb Z[i]/I\simeq\mathbb Z/V\mathbb Z$ and $I$ has norm $V$.
Since $\mathbb Z[i]$ is Euclidean, a denominator is

$$
\eta=\operatorname{primary}\gcd_{\mathbb Z[i]}(V,t-i),
\qquad \operatorname{Nm}(\eta)=V.
$$

Here primary means $\eta=a+bi$ with $b$ even and $a+b\equiv1\pmod4$.
For each conceptual factor $q^E\parallel V$, only the selected prime
ideal $(q,i-t)$ divides $t-i$; the conjugate prime does not, since $2t$
is nonzero modulo $q$. Taking the gcd with $V$ retains exactly $E$
copies of the selected prime. Consequently the previously defined
full-denominator character is precisely

$$
\boxed{\psi_V(n)=\left(\frac n\eta\right)_4,\qquad (n,V)=1.}
$$

The factorization in this explanation verifies the input translation;
the gcd and quartic-Jacobi algorithms do not require it. They must not
replace the denominator by its radical or its primitive-character part.
Two useful input checks are $a^2+b^2=V$ and $a+bt\equiv0\pmod V$.

Multiplying $\eta$ by a Gaussian unit preserves its ideal and its symbol;
conjugating it reverses the chosen orientation. Using the rational
Gaussian integer $V$ as denominator instead includes both conjugate
factors and gives

$$
\left(\frac nV\right)_{4,\mathbb Z[i]}
=\psi_V(n)\overline{\psi_V(n)}=1\qquad (n,V)=1,
$$

so that substitution would erase the required phase.

Numerator normalization has a different rule. The supplementary laws
in the same Gao–Zhao §2.2 source give, for primary $\eta=a+bi$,

$$
\left(\frac i\eta\right)_4=i^{(1-a)/2},\qquad
\left(\frac{1+i}\eta\right)_4=i^{(a-b-b^2-1)/4}.
$$

If $z=i^j(1+i)^h z_0$ with $z_0$ primary, these removed numerator
factors contribute

$$
\left(\frac z\eta\right)_4
=i^{j(1-a)/2+h(a-b-b^2-1)/4}\left(\frac{z_0}\eta\right)_4.
$$

The full published algorithm already tracks them. A wrapper that makes
the numerator primary and discards the factors changes the answer,
including at the cheap prime two. Since $2=-i(1+i)^2$, one obtains

$$
\boxed{\psi_V(2)=i^{-b/2}.}
$$

With $L=\lceil\log_2 V\rceil$, the cited quadratic algorithms give
$O(L^2)$ bit operations for denominator construction and for each query
after reducing a rational numerator modulo $V$. Reading and reducing an
unreduced input is a separate cost. This bound is in the bit size of $V$,
not in the bit size of the Fibonacci index $r$, and does not apply to
arbitrary exact-norm Euclidean code.

For the actual endpoint, cache $\eta$ and evaluate $(g/\eta)_4$ and
$(r/\eta)_4$, then use

$$
\psi_V(u_0)=\left(\frac g\eta\right)_4^{-1}
\left(\frac r\eta\right)_4^{-e}.
$$

This step needs neither factorization of $V$ nor of $u_0$; the actual
valuation $e$ is still an input, with only $e\bmod4$ needed for this phase.
The same evaluator labels eligible cheap primes for the existing
$\beta_j$ minima. It supplies their phase labels, not their minimum cost,
their occurrence in the same actual host, or $c_j>B_r$. The full weighted
Robin budget in FIB §233.5 remains a separate unresolved estimate.

## The half-index Fibonacci pair already gives the denominator

For this particular modulus, even the generic Gaussian gcd preprocessing
can be omitted. The Fibonacci doubling and Cassini identities are
classical; the pinned Mathlib sources already contain
[`Nat.fib_two_mul_add_one` and `Nat.fib_two_mul`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Nat/Fib/Basic.lean)
and
[`Int.fib_succ_mul_fib_pred_sub_fib_sq`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Int/Fib/Lemmas.lean).
Their application here is a denominator recipe, not a new Fibonacci
identity or a compiled Lean bridge.

Write $r=2m+1$, $A=F_{m+1}$ and $B=F_m$. The same identities give

$$
V=A^2+B^2,\qquad t=B(2A-B),\qquad
A^2-AB-B^2=(-1)^m,
$$

and hence the exact integer relation

$$
tB+(-1)^m A=(A-B)V.
$$

Thus the explicitly oriented Gaussian integer

$$
\eta_0=A+(-1)^m iB
$$

has norm $V$ and belongs to $I=(V,i-t)$. Its principal ideal is contained
in $I$ and has the same index $V$, so $(\eta_0)=I$. Multiplying by the
unique unit that makes it primary yields the same $\eta$ as above.
No factorization or Gaussian gcd is needed for this Fibonacci recipe;
computing the half-index pair and preserving its sign and primary unit
are still necessary. Choosing an arbitrary sum-of-two-squares
representation, or imposing a positive imaginary part, need not retain
the prescribed root orientation.

At the cheap prime two the supplementary law now needs only this pair
modulo eight. Its pair recurrence returns to $(0,1)$ after twelve steps;
the sign $(-1)^m$ has the same period. Primary normalization depends
only on the coordinates modulo four, so $b\bmod8$ is determined by
$m\bmod12$. For every prime $r>5$ this gives

| $r\bmod24$ | $1$ | $5$ | $7$ | $11$ | $13$ | $17$ | $19$ | $23$ |
|---|---|---|---|---|---|---|---|---|
| $\psi_V(2)$ | $1$ | $-i$ | $i$ | $1$ | $1$ | $-i$ | $i$ | $1$ |

For example, $r=7$ gives $\eta=3-2i$, $\psi_{13}(2)=i$ and
$\psi_{13}(t)=\psi_{13}(8)=-i$. The root identifies $i$ with $t$ in
the quotient but does not require the character value at $t$ to be $i$.
For $r=19$ the modulus is composite, $V=4181=37\cdot113$; the same
recipe gives $\eta=55-34i$ and $\psi_V(2)=i$, with no prime-modulus
substitution in the evaluator.

This resolves one eligible prime's arithmetic phase from a finite
Fibonacci observation. It does not force two to occur in $u_0$: the
actual valuation must still be probed, and two is eligible only when
$2\nmid vrV$. In that case its known phase merely gives an upper bound
$\beta_j\le b_s(2)$ for the corresponding nonzero class minimum, not
the lower bound needed to pay $B_r$. A phase-zero label adds no cost
to the phase-word relaxation. The cheap-prime and actual-support
conditions therefore remain distinct, as does the full weighted budget.

## A pinned implementation reference and its interface limits

The archived MOVA arithmetic source contains an implementation attributed
to Yvonne Anne Oswald:
[`quarticb3` in `winter_04_05_oswald/tester/quartic2.c`](https://github.com/sduc/undeniable-signature/blob/c8277fa71be292890a6d6733aff392372e1be02f/winter_04_05_oswald/tester/quartic2.c#L489),
at commit `c8277fa71be292890a6d6733aff392372e1be02f`.
It returns a Gaussian fourth root, with zero for a common factor,
rather than a Boolean quartic-residuosity flag. The finite controls
below used this source unchanged, compiled with C/GMP and an external
`stdlib.h` include for its `abs` declaration.

| Input $V,t$ | Primary oriented denominator $\eta$ | Observed $(2/\eta)_4$ |
|---|---|---|
| $13,8$ | $3-2i$ | $i$ |
| $233,144$ | $13+8i$ | $1$ |
| $4181,2584$ | $55-34i$ | $i$ |
| $25,7$ | $-3+4i$ | $-1$ |

The last row is a generic repeated-denominator control, not a Fibonacci
modulus: the selected prime above five occurs twice. Removing that
multiplicity would change the phase at two. Unit associates leave each
symbol unchanged, conjugation reverses it, and the rational Gaussian
denominator $V$ gives one on the rational unit domain, as required by
the preceding source translation.

The upstream functions use mutable GMP storage inside structs passed
by value; those copies are not independent copies of their integer
buffers. In particular, `primaryExp` changes its inputs and returns the
removed unit exponent in $z=i^j z_{\mathrm{primary}}$. The interface
controls used fresh per-query processes, so they do not certify an
ownership-safe persistent cache or general software correctness. A
caller retaining $\eta$ must supply independently owned working inputs.
The implementation uses exact-norm Euclidean division; the cited
quadratic bit bound must not be attributed to it. Its code license has
not been verified, and no upstream code is vendored here. These controls
support reuse of the published arithmetic interface, not a new algorithm,
a Lean result, or a strict Robin budget.

## Price the resource and retain the residual phase

The optimization input is classical weak duality, not an independence
assumption between size and character. Boyd–Vandenberghe,
*Convex Optimization* (2004),
[§5.1.3, printed p.216, equation (5.2), and §5.2.2, p.225,
equation (5.23)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf),
gives a lower bound by pricing a constraint, including for nonconvex
problems. The repository's
[fractional-knapsack note](../../Blueprint/D5/S3/Analytic/Knapsack/FractionalKnapsackDual.md)
already records the box-price model; its continuous fill has no character
endpoint. The following is a paper application to the same existing
benefit and quartic interface, not a new duality theorem, a claim of
novelty, or a Lean-verified bridge.

Keep the same actual $N,C_s,g,u,v,e,u_0,R_s(v),L_r$ and phase
$\psi_V(u_0)=i^j$. Set $E_0=\log u_0$ and retain the eligible prime set

$$
\mathcal P=\{p\text{ prime}:p\nmid vrV\}.
$$

The actual residual exponent is $\nu_p=v_p(u_0)$. Its $k$-th
post-reference layer has resource $\log p$ and cost

$$
d_{p,k}=\log p-s\ell_{p,a_p+k}>0,
\qquad d_{p,1}=b_s(p),\qquad d_{p,k}\ge b_s(p).
$$

Every actual layer occurs once, so the residual addition cost and resource
are

$$
\mathcal A_s^{[r]}(N)=\sum_{p\mid u_0}\sum_{k=1}^{\nu_p}d_{p,k},
\qquad E_0=\sum_{p\mid u_0}\nu_p\log p.
$$

For a resource price $0\le h\le h_0<1$, define the complete eligible
weak-layer deficit

$$
K_{\mathcal P}(h)=
\sum_{p\in\mathcal P}\sum_{k\ge1}(h\log p-d_{p,k})_+.
$$

This sum is finite uniformly on the specified price interval. A nonzero
term requires

$$
(1-h_0)p\log p<s,
$$

by $\ell_{p,a_p+k}\le p^{-(a_p+k)}\le p^{-1}$. There are only
finitely many such primes, and for each one $d_{p,k}\to\log p$ makes
the contributing layers finite. The case $h_0=1$ is not covered.

For a nonzero phase $z$, define the residual edge minimum

$$
\beta_z(h)=
\min_{\substack{p\in\mathcal P\\\psi_V(p)=i^z}}
(b_s(p)-h\log p)_+,
$$

with $+\infty$ for an empty class. Let $c_j(h)$ be the nonnegative
phase-word cost from the preceding four-state formulas, replacing each
$\beta_z$ by $\beta_z(h)$; in particular $c_0(h)=0$. The residual
edges can be zero even for nonzero phases. No positive gap or four
nonempty classes is presumed. A nonempty class has an attained minimum,
since the residual first-layer cost tends to infinity with $p$ at fixed
$h<1$.

Split each actual layer by the exact identity

$$
d_{p,k}=h\log p-(h\log p-d_{p,k})_+
                   +(d_{p,k}-h\log p)_+.
$$

The sum of actual deficits is at most $K_{\mathcal P}(h)$. The sum of
actual positive residuals is at least $c_j(h)$: each occurrence has
residual cost at least $(b_s(p)-h\log p)_+$, and the same actual
prime-power word has endpoint $j$. Hence the paper-level certificate is

$$
\mathcal A_s^{[r]}(N)
\ge hE_0-K_{\mathcal P}(h)+c_j(h),
$$

$$
\boxed{
D_s(N)\ge R_s(v)+L_r+
\sup_{0\le h\le h_0}
\{h\log u_0-K_{\mathcal P}(h)+c_j(h)\}.
}
$$

The phase term prices only the positive residual cost. Adding the raw
$c_j(0)$ to an already complete capacity bound would still charge the
same layers twice. Likewise, negative raw edges $b_s(p)-h\log p$ do not
permit the nonnegative cycle-deletion argument used for the four-state
formulas. The actual layered supply, including the entire weak deficit,
is essential; a first-layer-only deficit need not pay repeated additions.

This allocation supplies a lower certificate for the same host. It does
not yet compare that certificate with its signed Robin budget, exclude
the original low-loss candidate, or control all five-window sources.

## Compare the joint certificate with the separate bounds

Write

$$
\mathcal L_s(N)=L_r+
\sup_{0\le h\le h_0}
\{h\log u_0-K_{\mathcal P}(h)+c_j(h)\}.
$$

At $h=0$, the deficit vanishes and the preceding phase certificate is
recovered: $\mathcal L_s(N)\ge L_r+c_j(0)$.

For the capacity comparison, let $K_v(h)$ be the same complete deficit
over all primes $p\nmid v$, and let $K_r(h)$ be its part at $r$. Their
exact weak-layer capacity is $A_{+,v}(h)$ from above, so finite
layer-cake summation gives

$$
K_v(h)=\int_0^h A_{+,v}(t)\,dt,
$$

$$
\sup_{0\le h\le h_0}\{hE-K_v(h)\}
=\int_0^{h_0}(E-A_{+,v}(t))_+\,dt.
$$

For the second equality, the integrand before taking its positive part
is nonincreasing. Choosing the price where it changes sign, or an
interval endpoint if there is no crossing, attains its positive-area
integral. Threshold ties change neither integral.

The exact index block already paid satisfies
$L_r\ge he\log r-K_r(h)$. Also
$K_v(h)\ge K_{\mathcal P}(h)+K_r(h)$: primes dividing $V$ cannot
occur among the actual additions, and $r\nmid vV$. Consequently

$$
L_r+h\log u_0-K_{\mathcal P}(h)+c_j(h)
\ge h\log u-K_v(h).
$$

When $y\ge6$ and $h_0\le1/3$, the already cited envelope
$A_{+,v}(t)\le U_y(t)-\Delta_v(t)$ therefore gives

$$
\boxed{
\mathcal L_s(N)\ge
\max\{I_v(\log u),\ L_r+c_j(0)\}.
}
$$

This comparison uses the complete exact eligible deficit. An upper
approximation to that deficit still yields a valid lower certificate,
but its resulting value need not retain this dominance comparison.
Exact deficits do not require factoring $u_0$: the finite prime prefix,
known reference exponents, and eligibility probes suffice. No bound on
the computational cost at the growing source scale is asserted.

For the same actual host and a chosen price $h$, put

$$
B_h=B_r-h\log u_0+K_{\mathcal P}(h),
\qquad B_r=T_s(N)-R_s(v)-L_r.
$$

Then $c_j(h)>B_h$ is sufficient for strict Robin at that host. If
$B_h<0$, nonnegativity already pays it. If $B_h\ge0$, every prime
capable of an edge of residual cost at most $B_h$ lies below the finite
cutoff

$$
P_h=\max\{s,\exp((B_h+1)/(1-h))\}.
$$

Indeed $p>P_h$ implies $\log p>1$, $a_p=0$, and

$$
b_s(p)-h\log p
\ge(1-h)\log p-s/p>B_h.
$$

Checking eligible prime phases and their residual costs in that prefix
can exclude every phase word costing at most $B_h$. Nonnegative edges
allow a cheapest path with at most three edges, including zero-cost
edges; an absent phase class is never presumed nonempty. For $j=0$
and $B_h\ge0$, the empty word remains an obstruction to this particular
strict test. The parameter $h$ here is a resource price, not the cofactor
in $N=dh$.

## A strict allocation gain and the remaining arithmetic obligation

A finite layered allocation illustrates the distinction from taking a
maximum. It is not an exhibited FIB residual candidate. Take three
available layers, each with resource one, with phases $0,0,1$ and costs
$1/20,1/20,4/5$, and consume all three. At $h_0=1/3$, the capacity
optimum, raw phase cost and residual phase cost are respectively

$$
K(h_0)=\frac{17}{30},\qquad
\sup_{0\le h\le h_0}\{3h-K(h)\}=\frac{13}{30},\qquad
c_1(0)=\frac45,\qquad c_1(h_0)=\frac7{15}.
$$

Thus the joint certificate gives

$$
\frac{13}{30}+\frac7{15}=\frac9{10}
>\max\left\{\frac{13}{30},\frac45\right\}=\frac45,
$$

equal to this allocation's actual cost. The separate capacity optimum
is attained at $h_0$: before $h=1/20$ its slope is three, and afterwards
its slope is one. Naively adding the raw phase cost instead would give
$37/30$, exceeding the actual $9/10$. This example shows a genuine
gain in the allocation model and why the positive residual is needed;
it establishes no gain on the qualifying low-loss arithmetic hosts.

For the original actual sources, the sufficient comparison is now

$$
\mathcal L_s(N)>T_s(N)-R_s(v),
$$

or a source-preserving exclusion of any candidate where it fails. Every
term still belongs to the same host: the resource is $\log u_0$, the
endpoint uses its actual gcd and index-prime valuation, and eligibility
comes from that same $v,r,V$. If $u_0=1$, its endpoint is zero and the
supremum contributes zero; restoration-only hosts do not acquire a
spurious phase loss. Tied removed layers stay in the exact removal cost.
For $N=dh$, valuations are $v_p(d)+v_p(h)$, including common primes;
this allocation never optimizes those two factors independently.

The exact deficit and finite phase-prefix certificate provide an
additional interface for the missing comparison. No uniform lower bound
paying that signed budget has been established. The original window,
residue, low-loss divisor incidence, cofactor $h=1$, small-prime cofactors
and all-candidate scope of FIB §233.5 remain obligations. A larger finite
search, a positive phase cost, or the abstract strict-gain example is not
a proof of the complete weighted Robin inequality or RH.

## Retain each prime's complete reduced-cost block

A stronger application keeps the layered supply and the phase endpoint
in one finite-state problem. The optimization algorithm is already
classical: Mohri, *Semiring Frameworks and Algorithms for Shortest-Distance
Problems*, [§4, Corollary 2, author-PDF p.17, with its proof on p.18;
§5.1, p.19](https://cs.nyu.edu/~mohri/pub/jalc.pdf), gives exact shortest
distances on finite acyclic weighted graphs over a semiring and explicitly
includes the real min-plus semiring. The prime-stage graph below is
acyclic; no new shortest-path algorithm is proposed. This is a paper
application, not a Lean-verified arithmetic bridge.

For $p\in\mathcal P$, define

$$
f_{p,h}(k)=W_p(k)-hk\log p,\qquad k\ge0,\qquad
K_p(h)=\sum_{\ell\ge1}(h\log p-d_{p,\ell})_+.
$$

The reduced marginals increase and eventually become positive for
$h<1$, so $\min_{k\ge0}f_{p,h}(k)=-K_p(h)$. For every local phase,
including zero, retain the table

$$
a_{p,z}(h)=K_p(h)+
\min_{\substack{k\ge0\\kj_p=z\pmod4}}f_{p,h}(k),
\qquad \psi_V(p)=i^{j_p},
$$

with $+\infty$ for an unreachable local phase. Every finite table entry
is nonnegative. Let

$$
\delta_j(h)=
\inf_{\substack{(k_p)\text{ finite support}\\
\sum_p k_pj_p=j\pmod4}}
\left\{K_{\mathcal P}(h)+\sum_p f_{p,h}(k_p)\right\}.
$$

Only finitely many $K_p(h)$ are nonzero. For any such word, its expression
inside braces equals

$$
\sum_{\text{omitted layers}}(h\log p-d_{p,\ell})_+
+\sum_{\text{selected layers}}(d_{p,\ell}-h\log p)_+.
$$

The omitted weak deficits retain which prefixes were not selected; they
cannot all be collected independently of the endpoint. The selected
positive residuals pay at least the earlier clipped phase cost, giving
$\delta_j(h)\ge c_j(h)$. The actual word is also allowed, hence

$$
\boxed{
D_s(N)\ge R_s(v)+L_r+
\sup_{0\le h\le h_0}
\{h\log u_0-K_{\mathcal P}(h)+\delta_j(h)\}
\ge R_s(v)+\mathcal L_s(N).
}
$$

This refinement can improve the zero-phase branch: the collection of
locally minimizing prefixes need not have total phase zero. No positive
improvement is guaranteed. When $u_0=1$, both optimized residual
certificates equal zero. The empty word bounds the block expression by
zero, and $h=0$ attains zero.

### Four local choices in the existing capacity range

For $h\le1/3$, the already established marginal separation gives
$d_{p,\ell}>\tfrac12\log p$ for $\ell\ge2$. Thus $f_{p,h}(k)$ is
strictly increasing for $k\ge1$, and

$$
f_{p,h}(4)>
\left[-h+3\left(\tfrac12-h\right)\right]\log p
\ge\tfrac16\log p>0.
$$

Every local phase minimum is therefore attained among $k=0,1,2,3$.
For an odd $j_p$, the zero phase prefers $k=0$ to $k=4$ and all later
representatives; each other phase uses its least positive representative.
For $j_p=2$, the zero phase compares $k=0,2$ and phase two uses $k=1$.
For $j_p=0$, only $k=0,1$ need be compared. This reduces the local
minimization; it does not assert that actual residual valuations are at
most three.

On a complete finite prime list, process each prime once:

$$
q_n(z)=\min_{t\in\mathbb Z_4}
\{q_{n-1}(z-t)+a_{p_n,t}(h)\},
\qquad q_0(0)=0,\quad q_0(z\ne0)=+\infty.
$$

The stage advances even for a zero phase, so a negative raw reduced block
could also be used safely on this acyclic graph. It cannot be repeatedly
reused as a subsidizing cycle. An arbitrary truncated prime list is not
complete for the infinite certificate: omitted weak deficits or cheap
phase blocks can raise the computed lower bound incorrectly. Tail
coverage remains required.

### A finite conditional test for the actual budget

Fix $B=B_r(N)\ge0$ and suppose the actual remaining cost were at most
$B$. Every used prime then has $b_s(p)\le B$ and lies below
$P_B=\max\{s,e^{B+1}\}$ by the existing first-entry cutoff. Every used
exponent belongs to the finite set

$$
\mathcal K_p(B)=\{k\ge0:W_p(k)\le B\},
$$

since $W_p(k)\ge k b_s(p)$ and $b_s(p)>0$. For all eligible primes
$p\le P_B$, and any real multiplier $\lambda$, compute by the same
acyclic recurrence

$$
Q_B(\lambda,j)=
\min_{\substack{k_p\in\mathcal K_p(B)\\
\sum_p k_pj_p=j\pmod4}}
\sum_p\{W_p(k_p)-\lambda k_p\log p\}.
$$

The hypothesized low-cost actual word is included, so

$$
\boxed{
\lambda\log u_0+Q_B(\lambda,j)>B
\quad\Longrightarrow\quad
\mathcal A_s^{[r]}(N)>B.
}
$$

An empty endpoint-feasible set also rejects the low-cost hypothesis.
This is a conditional rejection test, not an unconditional lower bound
from an unproved truncation. The finite formulation permits
$\lambda=1$; it does not extend the unrestricted deficit $K(1)$, whose
prime sum diverges. Real logarithmic resources are retained; integer
rounding of them would require an additional valid relaxation.

For an abstract zero-phase gain, take one prime block with resource one,
phase one per occurrence, first cost $1/20$, and later costs
$d_k=1-1/(k+2)$ for $k\ge2$. Consume four occurrences, so the endpoint
is zero and the actual cost is $73/30$. On $0\le h\le1/3$, only the
first layer can have a weak deficit, $f_{p,h}(4)>0$, and the local
zero-phase minimizer is $k=0$. Therefore the optimized clipped bound is
$21/20$, while the optimized block bound is $4/3$, a gain of $17/60$.
This is a layered allocation example, not an actual FIB low-loss host.

The phase endpoint is retained exactly within each relaxation; pricing
the resource gives a lower bound and supplies no strong-duality equality
with the original constrained arithmetic problem. Failure of a sufficient
rejection test does not imply failure of Robin.

The blockwise certificate and the finite conditional test still need to
pay the same host's $B_r(N)$ on the original qualifying sources, or
exclude the cases where they do not. They retain, rather than discharge,
the full window, residue, weighted divisor incidence, tied removals,
merged valuations and cofactor-$h=1$ obligations. The cited optimization
results supply no uniform weighted Robin estimate or proof of RH.

## The low-loss divisor condition can already be saturated

Before enlarging the residue graph with another constraint, check whether
that constraint removes any of the hypothesized low-cost hosts. Reuse
the actual increment source and finite comparison in FIB §234.1–§234.2;
no new source, benefit theorem or optimization algorithm is introduced.
This section is a paper application, with no Lean verification.

For $s\ge1$, keep the maximal tied-layer reference $C_s$ and put
$g=\gcd(N,C_s)$. Every exponent of $g$ is an accepted reference exponent.
The same local comparison used at $C_s$ therefore gives

$$
r_s(g)=\frac{b_s(g)}{Z(g)^s}\ge\frac{\varphi(g)}g,
\qquad D_s(g)=R_s(v),\qquad v=C_s/g.
$$

In particular, the existing identity
$J_s(g)=D_s(g)-\log r_s(g)-\delta_s$, with
$\delta_s=\log(\mathcal Q_s/M_s)\ge0$, supplies

$$
\boxed{
J_s(g)\le R_s(v)+\log\frac g{\varphi(g)}-\delta_s
\le R_s(v)+\log\frac{C_s}{\varphi(C_s)}.
}
$$

Thus whenever the last expression is at most $J_0$, the particular
divisor $g\mid N$ already witnesses the required low-loss incidence.
This holds for every host with that same gcd, regardless of its added
prime powers. It does not say $J_s(N)\le J_0$, and does not replace the
complete weighted sum over divisors by the weight of $g$.

For a hypothesized unpaid Robin budget, $D_s(N)\le T_s(N)$ and
$R_s(v)\le D_s(N)$. Hence the sufficient saturation condition is

$$
T_s(N)+\log\frac{C_s}{\varphi(C_s)}\le J_0.
$$

Under it, imposing existence of a low-loss divisor cannot exclude any
of those hypothesized hosts. In a fixed-gcd branch satisfying the sharper
$R_s(v)+\log(g/\varphi(g))-\delta_s\le J_0$, that incidence constraint
is redundant for the entire branch, including its relaxed residual words.
An extra multiplier for it cannot raise the exact constrained optimum
above the one without it; setting the multiplier to zero remains allowed.

### A finite condition in the original growing-price window

Keep $y=\log A$, $\ell=\log y$, $s=y\ell$, and $A\le N\le C_0A$
with fixed $C_0>1$. Write

$$
L_y=\sum_{p\le y}\log(1-1/p)^{-1},\qquad
\mathcal E_y=s(L_y-\gamma-\log\ell)+y-\vartheta(y-1).
$$

The reference first-prime threshold $x_s$, already defined by
$s\log(1+1/x_s)=\log x_s$, lies in $(y-1,y)$ for $y>2$.
For the lower endpoint use
$\log(1+1/(y-1))>1/y$ and $\log(y-1)<\log y$;
the upper endpoint follows from $\log(1+1/y)<1/y$.
Therefore $\log C_s\ge\vartheta(y-1)$, while every prime of $C_s$
is at most $y$ and $\log Z(C_s)\le L_y$. The actual Robin threshold
also satisfies $\log(e^\gamma\log\log N)\ge\gamma+\log\ell$.
Together these give the finite, signed upper bounds

$$
T_s(N)\le\mathcal E_y+\log C_0,\qquad
\log\frac{C_s}{\varphi(C_s)}\le L_y.
$$

Consequently

$$
\boxed{\mathcal E_y+\log C_0+L_y\le J_0}
$$

is a sufficient window-wide condition for the saturation above. A negative
$T_s(N)$ already makes $D_s(N)\le T_s(N)$ impossible; saturation never
requires manufacturing a positive remaining budget in that case.

The strong Mertens and prime-number inputs already used in
[Weingartner's pinned author text, equation (9), PDF p.6](https://arxiv.org/pdf/1011.4262v1)
give, for every fixed $K$, the classical remainders

$$
L_y=\gamma+\log\ell+O_K(\ell^{-K}),\qquad
\vartheta(y-1)=y-1+O_K(y\ell^{-K}).
$$

Taking $K>3$ shows $\mathcal E_y=o(y/\ell^2)$ and
$L_y=O(\log\ell)$. Thus the displayed condition holds eventually for
the original $J_0=8(\pi^2/6)y/\ell^2$. This uses the stronger classical
inputs, not only Dusart's previously quoted $O(\ell^{-2})$ Mertens
remainder. No effective onset follows here.

This identifies a redundant source filter in the dangerous budget range.
It leaves the actual congruence and strict signed budget untouched.
Existence of a low-loss divisor, including this explicit gcd witness,
does not establish FIB §233.5 or RH.

## Retain the actual unit residue and the original host window

The remaining arithmetic constraint is the product congruence itself.
Reuse the preceding budget-conditioned finite prime universe and Mohri's
finite acyclic min-plus method. Replace only its endpoint quotient:
each prime block acts by multiplication on $(\mathbb Z/V\mathbb Z)^\times$.
This is a classical algorithm applied to a stronger observation, not a
new shortest-path or residue-distribution theorem.

For the same actual $N$, $g$, $e$ and $u_0$, put $G=gr^e$. Actual
$N\equiv1\pmod V$ forces $(G,V)=1$ and

$$
\boxed{u_0\equiv\rho:=G^{-1}\pmod V.}
$$

There is no extra factor $u_0^{-1}$ in this endpoint. It belongs to the
residual product itself, rather than to a chosen divisor separately from
its cofactor. An inverse modulo a composite $V$ can be computed by the
extended Euclidean algorithm without assuming a factorization of $V$.

For $B=B_r(N)\ge0$, use **all** eligible primes $p\le P_B$ and every
$k\in\mathcal K_p(B)$ from the preceding conditional test. Define

$$
Q_B^{\mathrm{unit}}(\lambda,\rho)=
\min_{\substack{k_p\in\mathcal K_p(B)\\
\prod_p p^{k_p}\equiv\rho\pmod V}}
\sum_p\{W_p(k_p)-\lambda k_p\log p\}.
$$

The prime stage still advances once per block; negative reduced costs
are permitted on that acyclic graph. If the actual residual cost were
at most $B$, its exact word would be present. The existing weak-duality
test therefore becomes

$$
\boxed{\lambda\log u_0+Q_B^{\mathrm{unit}}(\lambda,\rho)>B
\quad\Longrightarrow\quad\mathcal A_s^{[r]}(N)>B.}
$$

For the same complete finite universe and the same multiplier,

$$
Q_B^{\mathrm{unit}}(\lambda,\rho)
\ge Q_B(\lambda,j),\qquad \psi_V(\rho)=i^j.
$$

Only a subset of the quartic-endpoint words reaches the actual unit
residue. No distribution theorem or independence of the prime labels is
used. Equality remains possible. An empty endpoint-feasible set excludes
the conditional low-cost host; the existence of a cheap path gives only
a relaxed lower bound and supplies no violating integer.

### A simultaneous fixed-gcd and fixed-index branch

One can retain the original window without choosing a separate host at
each optimum. Fix a divisor $g\mid C_s$ and an integer $e\ge0$, keep
$v=C_s/g$, $G=gr^e$, and consider only hosts with

$$
\gcd(N,C_s)=g,\qquad v_r(N)=e,\qquad
A\le N\le X,\qquad N\equiv1\pmod V.
$$

If $(G,V)>1$ or $X/G<1$, this branch is empty. Otherwise put

$$
U_{\min}=\max\{1,A/G\},\qquad U_{\max}=X/G.
$$

The eligible set $p\nmid vrV$ and the reference exponents $a_p$ ensure
that a residual word keeps the fixed gcd and exact index valuation:
primes removed from $C_s$ cannot be added back, other reference primes
can only increase from their full accepted exponent, and $r$ is not
reused. All zero-cost removals are retained in $R_s(v)$.

In the original price choice $s=y\log y$, $y=\log A$, write $L=\log N$.
The already defined threshold has derivative

$$
\frac{d}{dL}T_s(e^L)=1-\frac{s}{L\log L}\ge0
\qquad(L\ge y>1).
$$

Thus every hypothesized unpaid host in this branch has residual cost at
most the same ceiling

$$
B_0=T_s(X)-R_s(v)-L_r.
$$

If $B_0<0$, the removals and fixed index block already exclude that
hypothesis throughout the branch. For $B_0\ge0$, build the complete
finite universe using $B_0$, not an independently favorable host budget.
For any real multiplier define

$$
H(\lambda)=
\begin{cases}
\lambda\log U_{\min},&\lambda\ge0,\\
\lambda\log U_{\max},&\lambda<0.
\end{cases}
$$

Every actual residual resource in the original window obeys
$\lambda\log u_0\ge H(\lambda)$. Hence

$$
\boxed{H(\lambda)+Q_{B_0}^{\mathrm{unit}}(\lambda,G^{-1})>B_0}
$$

excludes every unpaid host in this **same** fixed-gcd/index/window branch.
Pricing the interval retains a lower relaxation, not exact arithmetic
attainability. Outside the low-loss saturation condition above, incidence
is still an additional source condition; using a larger set of words is
valid for exclusion but does not prove that any minimizing word has a
low-loss divisor.

Keep the resource and signed budget attached to the same integer to
obtain a sharper comparison. Put $N_{\min}=\max\{A,G\}$ and

$$
\Theta_\lambda(N)=\lambda\log(N/G)
-\{T_s(N)-R_s(v)-L_r\}.
$$

As a function of $L=\log N>1$, this is concave, since its second
derivative is $-s(\log L+1)/(L^2(\log L)^2)<0$. Its minimum on the
actual interval is therefore at an endpoint. Still use the **same**
complete universe defined by $B_0$; the stronger sufficient test is

$$
\boxed{
Q_{B_0}^{\mathrm{unit}}(\lambda,G^{-1})
+\min\{\Theta_\lambda(N_{\min}),\Theta_\lambda(X)\}>0.
}
$$

For every actual word under the unpaid hypothesis, the left-hand
expression is at most $D_s(N)-T_s(N)\le0$, yielding the contradiction.
Also $\Theta_\lambda(N)\ge H(\lambda)-B_0$ throughout the interval,
so this test retains every exclusion made by the separated window bound.
For $\lambda=1$, $\Theta_1$ is increasing and the improvement in the
lower certificate is exactly $T_s(X)-T_s(N_{\min})\ge0$. This is a
joint-window calculation, not a gain established on an unpaid FIB host.
Concavity supplies this endpoint comparison; it does not establish
strong duality or the strict positivity of the resulting certificate.

### Increase resolution only where a quotient loses a useful distinction

The same finite-word minimum can first keep $u_0\bmod m$ for any $m\mid V$.
For $m_1\mid m_2\mid V$, retaining the finer endpoint at the same budget,
prime universe and price cannot decrease the minimum. These are compatible
arithmetic observations of one residual product. A four-phase character
is another quotient observation; it need not distinguish two different
unit residues, even when both products have identical phase.

The empty residual word is retained. For an actual $u_0=1$, its full
residue is one and its cost is zero; no refinement can force a positive
residual cost for that host. Restoration-only branches, tied removals and
the divisor-cofactor $h=1$ branch are therefore not discarded. Keeping
$g,e$ fixed does not cap the actual higher valuations at three.

This application supplies a source-preserving **sufficient branch test**.
It claims neither a uniform gain over the quartic bound nor feasibility
of running a full $\varphi(V)$-state computation at arbitrary scale.
To finish FIB §233.5, the strict signed budget must still be paid for all
qualifying branches, or the unpaid branches excluded. A finite graph,
more residue information, and the redundant low-loss incidence condition
do not by themselves supply that estimate or a proof of RH.

## Actual strict CA products at their own-size price

This is an application of the classical CA benefit and existing project
capacity, not a new prime-distribution theorem. It continues the
[actual strict products and pressure account ACC1–ACC9](nicolas2025comparison.md#a-complete-pressure-balance-at-the-unchanged-observation).
The complete proofs of the external analytic suppliers are not audited
here. No literature priority or Lean certification is claimed.

For $n\ge1$ and $y>1$, use

$$
W(n)=\log\frac{\sigma(n)}n,\qquad
s_y=y\log y,\qquad \lambda(y)=s_y^{-1},
$$

$$
r_{p,j}=\frac1{\log p}
 \log\frac{1-p^{-j-1}}{1-p^{-j}},\qquad
M(q)=\max_{n\ge1}\{W(n)-q\log n\}\quad(q>0).
$$

The actual strict inventory and its own-size clock are

$$
N_x=\prod_p p^{a_p(x)},\qquad
 a_p(x)=\#\{j\ge1:r_{p,j}>\lambda(x)\},\qquad
 A_x=\log N_x.
$$

Every equality layer is excluded, and every positive prime-power layer
is retained. ACC3 gives
$W(N_x)=M(\lambda(x))+\lambda(x)A_x$. Define the full own-price defect

$$
d_A(n)=M(\lambda(A))-W(n)+\lambda(A)\log n\ge0,
\qquad T_A=\sqrt A\log A\quad(A>1).
$$

The existing effective PNT and complete higher inventory give, for
some fixed $a>0$,

$$
A_x=x+O(xe^{-a\sqrt{\log x}}),\qquad A_x\sim x.
\tag{NP0}
$$

Only the full strict integer $N_x$ is used below; no independently
optimized configurations are combined.

### A finite upper benefit bound at the same strict inventory's own price

The existing [arbitrary-host benefit and thin-layer capacity
TC.1](erdosnicolas1975repartition.md#an-explicit-thin-layer-capacity-for-the-same-arbitrary-host)
can bound the complete own-price defect of ACC's actual $N_x$.
This applies a classical benefit calculation to two specified prices;
it introduces no new capacity or prime-distribution theorem. The
capacity's Yamada and Dusart inputs remain external, and this
application has no Lean certification or literature-priority claim.

Use the same strict integer $N_x$, $A=\log N_x$, $s_y=y\log y$ and
$\lambda(y)=1/s_y$. Suppose $x>1$, $A\ge16$, and put

$$
h=\left|\frac{s_A}{s_x}-1\right|\le\frac14.
$$

Let $C_A$ be the **maximal** optimizer at $\lambda(A)$, so it includes
every layer with $r_{p,j}\ge\lambda(A)$. The source $N_x$ includes
exactly the layers with $r_{p,j}>\lambda(x)$. For each prime, let
$\mathscr J$ contain exactly the positive layers lying between these
two actual exponent counts:

$$
\mathscr J=
\{(p,j):p\text{ prime},\
 \min(v_p(C_A),v_p(N_x))<j\le
 \max(v_p(C_A),v_p(N_x))\}.
$$

This is finite. If a layer belongs to $\mathscr J$, its marginal
lies between $\lambda(A)$ and $\lambda(x)$, with the appropriate
endpoint inclusion. Therefore every crossed layer satisfies

$$
|s_A r_{p,j}-1|\le h,\qquad
|r_{p,j}-\lambda(A)|\le h/s_A.
$$

In particular a layer tied at $\lambda(A)$ has zero benefit cost,
while a layer tied at $\lambda(x)$ is still inside the same weak band.
The bound does not require $N_x$ to be superabundant, GA1, GA2,
or optimal at its own-size price.

The classical layerwise benefit identity at the **own-size** price is

$$
\begin{aligned}
d_A(N_x)
&=M(\lambda(A))-W(N_x)+\lambda(A)A\\
&=\sum_{(p,j)\in\mathscr J}
       \log p\,|r_{p,j}-\lambda(A)|.
\end{aligned}
$$

TC.1 with parameter $a=A$ bounds the full weak-band resource by
$24Ah+32\sqrt A$. Since $\mathscr J$ is a subset of that band,

$$
\boxed{
0\le d_A(N_x)
\le\frac{24Ah^2+32\sqrt A\,h}{A\log A},\qquad
T_A d_A(N_x)\le24\sqrt A\,h^2+32h.
}
\tag{NPC1}
$$

This is a finite bound with an explicit hypothesis on the two actual
prices. It accounts for every changed prime-power layer.

For ACC4's unconditional family, $A\sim x$ and the mean-value theorem
for $y\log y$ gives $h=O(e^{-a\sqrt{\log x}})$. Consequently (NPC1)
strengthens ACC5's linear PNT allowance to

$$
d_{A_x}(N_x)=O(e^{-2a\sqrt{\log x}}/\log x).
\tag{NPC1a}
$$

The first term of NPC1 is
$O(e^{-2a\sqrt{\log x}}/\log x)$, and the second is
$O(e^{-a\sqrt{\log x}}/(\sqrt x\log x))$, which is smaller.
The PNT and the constant $a$ are the same as in ACC4. The normalized
allowance still contains $O(\sqrt x e^{-2a\sqrt{\log x}})$;
its growth prevents this allowance from paying a root-scale defect
bound on the whole unconditional family. No lower bound on the
actual defect is inferred from that growth. The original signed
Robin integral remains unpaid.


#### A conditional root-scale transfer for the same actual integers

Let $x$ range over any unbounded family of real prices for which

$$
\delta_x:=|A_x-x|=o(x^{3/4}).
\tag{NPC2}
$$

This condition implies $A_x\sim x$. The mean-value theorem for
$y\log y$ on the interval with endpoints $x,A_x$ gives
$h_x=O(\delta_x/x)$, with one common constant once
$A_x\in[x/2,2x]$. In particular the finite hypotheses of (NPC1)
hold eventually along the entire specified family, and

$$
0\le T_{A_x}d_{A_x}(N_x)
=O\!\left(\frac{\delta_x^2}{x^{3/2}}+
                 \frac{\delta_x}{x}\right)=o(1).
\tag{NPC3}
$$

There is no substitution of $x$ for the source's own clock $A_x$ in
the defect or its normalization. The exponent $3/4$ here comes from
the quadratic capacity allowance; it is a sufficient condition, not
a necessity or an optimal exponent.

For $A=\log n>1$, write the logarithmic Robin margin as
$\Delta(n)=\gamma+\log\log A-W(n)$, and put

$$
I_\psi(A)=\int_A^\infty(\psi(u)-u)
 \frac{1+\log u}{u^2\log^2u}\,du.
$$

Use [KTO1's existing complete pressure identity and two-candidate
reserve](nicolas2025comparison.md#keep-the-two-response-kernels-distinct)
at $A=A_x$:

$$
M(\lambda(A))
=\gamma+\log\log A-\frac1{\log A}-I_\psi(A)-R(A),
\qquad
T_AR(A)=c_R+O(1/\log A),\quad c_R=2(\sqrt2-1).
$$

Since $\lambda(A)\log N_x=1/\log A$, the same integer has the
exact margin account

$$
\Delta(N_x)=d_A(N_x)+I_\psi(A)+R(A),\qquad A=A_x.
$$

Thus (NPC2), with the cited reserve and capacity inputs, gives

$$
\boxed{
T_{A_x}\Delta(N_x)
=T_{A_x}I_\psi(A_x)+c_R+o(1).
}
\tag{NPC4}
$$

For example, on such a family a lower bound
$\liminf T_{A_x}I_\psi(A_x)>-c_R$ would imply eventual strict
Robin there; an upper bound
$\limsup T_{A_x}I_\psi(A_x)<-c_R$ would imply eventual violations
there. Neither signed premise is supplied. An asymptotic comparison
at equality with $-c_R$ does not decide strict Robin.

ACC4's unconditional PNT allowance does not imply (NPC2): its ratio
to $x^{3/4}$ grows. The existing full-real inventory normal form
$A_x=\psi(x)+(\sqrt2-1)\sqrt x+o(\sqrt x)$, cited in
[the workload note](../Analytic/mantovanelli2026primeworkload.md#the-full-real-normal-form-also-controls-strict-inventory-at-events),
identifies (NPC2) with $\psi(x)-x=o(x^{3/4})$ on this same family.
This gives a checkable condition on the actual prime error; it does
not establish that condition at every large price or at the unknown
counterexample-selected prices.

The finite upper benefit estimate and this conditional transfer reuse
the classical CA benefit, the already derived thin-layer capacity,
and the existing reserve and inventory normal form. No new signed
prime estimate or assumption of RH is introduced. The full original
same-source signed budget, strict Robin for every integer above 5040,
and RH remain unresolved; this application has no Lean verification.


### The existing weighted prime count fixes the root-scale coefficient

The finite NPC1 uses only thin-layer capacity. The stronger conclusion
below additionally reuses the weighted short-interval PNT of
Thorner–Zaman, *Refinements to the prime number theorem for arithmetic
progressions*, [arXiv:2108.10878v2](https://arxiv.org/pdf/2108.10878v2),
Theorem 1.1. Its parameter correspondence is already recorded in
[the short-uniformity source note](../Analytic/shortuniformity2026robininterfaces.md#effective-weighted-prime-counts-in-short-intervals):
$q=2$, residue $1$, $\varepsilon=1/60$, no exceptional character.
It gives weighted prime mass $H(1+o(1))$ uniformly for terminal
scale $X$ and $X^{3/5}\le H\le X$. The two-price integration below
is an application to the same strict products; neither the generic
quadratic threshold mechanism nor that prime theorem is new.

#### Keep the exact inventory between both prices

Write $A(u)=\log N_u$ for every real $u>1$, including activation
events, and

$$
w(u)=-\lambda'(u)=\frac{1+\log u}{u^2\log^2u}.
$$

On any compact subinterval of $(1,\infty)$ only finitely many
prime-power layers can activate. The existing layerwise pressure
formula therefore gives a continuous, piecewise differentiable
$M(\lambda(u))$, with

$$
\frac{d}{du}M(\lambda(u))=A(u)w(u)
\quad\text{away from its finitely many events}.
$$

The strict choice at events changes neither this almost-everywhere
identity nor its integral. Keep $A=A(x)$ in the endpoint term.
ACC3 then gives the exact identity, for either ordering of $A,x$,

$$
\begin{aligned}
d_A(N_x)
&=\int_x^A [A(u)-A(x)]w(u)\,du\\
&=\int_{\min(x,A)}^{\max(x,A)}
       |A(u)-A(x)|w(u)\,du .
\end{aligned}
\tag{NPC5}
$$

The second equality uses monotonicity of the complete strict
inventory $A(u)$. All higher layers and both endpoint tie choices
remain accounted for. In particular $A=x$ gives zero.

#### Apply the existing prime increment on the actual price interval

Put $R=x^{2/3}$ and $\delta=|A(x)-x|=o(x)$, the latter supplied
unconditionally by NP0. On $[x/2,2x]$, ACC4's first-layer bracket
and complete higher inventory give

$$
A(u)=\vartheta(u)+O(\sqrt x).
\tag{NPC6}
$$

The bracket error is $O(\log x)$, since the first active mass lies
between $\vartheta(u-1)$ and $\vartheta(u)$. The full higher
active mass is $O(\sqrt x)$; no fixed exponent cutoff is imposed.

For $u$ between $x$ and $A(x)$ with $H=|u-x|\ge R$, apply the cited
prime theorem at terminal endpoint $\max(u,x)$ and length $H$.
Here both endpoints are comparable with $x$, $H=o(x)$ and
$H\ge x^{2/3}\ge\max(u,x)^{3/5}$ eventually. Its displayed error
tends to zero uniformly over this range. Subtract NPC6 at both
endpoints; its $O(\sqrt x)$ error divided by $H\ge R$ also tends
to zero. Thus

$$
|A(u)-A(x)|=H(1+o(1))
\quad(H\ge R),
\tag{NPC7}
$$

uniformly on the actual interval. For $|u-x|\le R$, monotonicity
instead bounds the increment by the increments to $x-R$ and
$x+R$. Apply the same prime theorem at length $R$ to these two
endpoints to obtain the common bound $O(R)$. This also covers
the entire integration interval when $\delta<R$.

Finally $w(u)=(1+o(1))/(x^2\log x)$ uniformly between $x$ and $A(x)$.
Integrate NPC7 on the part with $|u-x|\ge R$ and bound both the
actual and comparison integrals on the remaining part by
$O(R^2/(x^2\log x))$. There are a function $\epsilon(x)\to0$ and
a fixed constant $C$ such that, for all sufficiently large real $x$,

$$
\left|d_{A_x}(N_x)-\frac{\delta_x^2}{2x^2\log x}\right|
\le\epsilon(x)\frac{\delta_x^2}{x^2\log x}
  +C\frac{x^{-2/3}}{\log x}.
\tag{NPC8}
$$

The errors are absolute when $\delta_x$ is small, rather than an
unsupported relative asymptotic at an activation event.
Since $A_x\sim x$, multiplication by the unchanged own-clock
$T_{A_x}$ gives, with another $\epsilon_1(x)\to0$ and fixed $C_1$,

$$
\boxed{
\left|T_{A_x}d_{A_x}(N_x)
       -\frac{\delta_x^2}{2x^{3/2}}\right|
\le\epsilon_1(x)\frac{\delta_x^2}{x^{3/2}}
   +C_1x^{-1/6}.}
\tag{NPC9}
$$

The normalization has not been replaced by a different source's
clock; its ratio to $\sqrt x\log x$ tends to one.

#### What the coefficient does and does not settle

For every unbounded family of these actual strict price products,
NPC9 implies

$$
T_{A_x}d_{A_x}(N_x)\longrightarrow0
\quad\Longleftrightarrow\quad
|A_x-x|=o(x^{3/4}).
\tag{NPC10}
$$

For the reverse implication, NPC9 bounds the nonnegative
$\delta_x^2/x^{3/2}$ by the vanishing defect plus $C_1x^{-1/6}$,
after absorbing $\epsilon_1(x)<1/4$.
This upgrades NPC3's sufficient condition to an equivalence for
**root-smallness of this particular defect**, using the additional
weighted prime theorem. It is not a necessary condition for
strict Robin, which allows compensation in its complete account.

More generally, if on a specified unbounded family
$\delta_x/x^{3/4}\to\ell<\infty$, then

$$
T_{A_x}d_{A_x}(N_x)\longrightarrow\ell^2/2,
\qquad
T_{A_x}\Delta(N_x)
=T_{A_x}I_\psi(A_x)+c_R+\ell^2/2+o(1).
\tag{NPC11}
$$

The sign of the quadratic term is positive in this pressure-defect
account. A signed liminf greater than $-c_R-\ell^2/2$ would give
eventual strict Robin on that family; a signed limsup smaller than
that threshold would give eventual violations there. Neither
premise is established, and equality is undecided.

This coefficient calculation retains the same actual integer in
the inventory, price, pressure, reserve and signed integral. It
does not provide the signed prime estimate, establish the required
clock displacement at every large source, or prove RH. The
classical suppliers and elementary two-price integration are
reused as a paper application, without Lean certification or a
claim of literature priority.
