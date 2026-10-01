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
