---
bibkey: erdosnicolas1975repartition
authors: Paul Erdős; Jean-Louis Nicolas
year: 1975
title: Répartition des nombres superabondants
doi: 10.24033/bsmf.1793
url: https://www.numdam.org/item/BSMF_1975__103__65_0/
claim: The classical benefit is the nonnegative loss relative to a colossally abundant optimizer; the FIB price-loss expression is exactly this existing quantity.
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
