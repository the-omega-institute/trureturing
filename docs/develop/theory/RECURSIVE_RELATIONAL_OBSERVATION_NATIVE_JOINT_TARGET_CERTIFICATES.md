# Recursive relational observation: joint-target certificates and scaffold pressure

This volume records a finite all-correlated mass inequality for the native
late-target family. It keeps the complete block potential, the same joint
realization, arbitrary donor indices and cycles. The result is a sound finite
certificate family and a pressure transport identity. It does not supply the
cofinality required for an effective computation of the unrestricted native
rate.

## 1. The unchanged native task

**Definition 1.1 (stationary source and exact request family).** Let

$$
\mathcal T ::= \alpha\mid\beta\mid\langle u,v\rangle,
\qquad
\rho(\alpha)=\beta,
\quad \rho(\beta)=\langle\beta,\alpha\rangle,
\quad \rho\langle u,v\rangle=\langle\rho u,\rho v\rangle .
$$

Pairing is ordered. Every finite word over $L,R$, including $\varepsilon$, is
an original-root literal. Its reply is one of
$\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$, with traversal
past a leaf returning $\mathsf{absent}$. For $D\ge1$ use exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},
\qquad W_D=\{q:|q|\le D-1\},
\qquad \mathcal P_D=\{Rq:q\in W_D\}.
\tag{JTC.1}
$$

The one actual source remains stationary through preparation and later
acquisition. A deterministic source-blind preparation, not given the later
request, acquires all source dependence by charged literal Reads and exports a
finite code $E(t)$ containing every surviving accessible distinction, including
selectors, control, buffers, lengths, allocation and timing. A separately paid
handoff and access-isolation service is assumed. Only after export is a public
source-independent $p\in\mathcal P_D$ supplied. The reader uses $E(t),D,p$ and
common tables, chooses zero Reads or one fresh Read of the same stationary
source at an original-root literal before any authentic $k$ is supplied, and
then returns

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^k(t)}(p)
\quad(t\in\mathcal F_D,\ p\in\mathcal P_D,\ k\ge0),
\tag{JTC.2}
$$

with no later Reads. There is no subtree, equality, source-identity, age,
copying, reset, navigation or hidden advice port. Preparation cost, installed
code, workspace, final predictor, submitted address, authentication, handoff,
isolation and physical time are separate resources. The optimized quantity is
only the complete attained cardinality $M_1(D)=\min|E[\mathcal F_D]|$.

The temporal factor $\Gamma_q$ and its all-count decoder are the credited
[AAR] result, and canonicalization, paid literal realization and scaffold
transport are the credited [FMR] results. In particular, no statement below
changes the original late target or introduces a second observation port.

**Convention 1.2 (credited canonical representatives).** Write
$C_0=\langle\alpha,\alpha\rangle$,
$S_1=\{\alpha,\beta,C_0\}$ and
$S_{d+1}=\{\alpha,\beta\}\sqcup\{\langle x,y\rangle:x,y\in S_d\}$.
The [FMR] map $\pi_D$ preserves every constructor reply in $W_D$ and
replaces a branch at the depth-$(D-1)$ cutoff by $C_0$. It preserves
every permitted target factor, fixes $S_D$, and is computable from the
paid boundary scan. Every finite experiment on $S_D$ is a function of
one boundary reply in the same block or is constant. These are credited
canonicalization facts, not additional assumptions on competitors.
In particular $|S_3|=123$, $|S_4|=15131$ and $|S_5|=228947163$.
Every full-family canonical code constructed below exports a fixed-width
name, with public scan/control/allocation and padded finite computation;
all other acquired dependence is isolated under the service in
Definition 1.1. No private preparation transcript is later accessible.

## 2. A joint hard-target inequality

**Definition 2.1 (finite interface and hard targets).** Let $S$ be finite. Let
$g_q:S\to G_q$ be target maps and $r_a:S\to A_a$ be experiments, including a
constant experiment. For $P\subseteq S$, say that $r_a$ determines $g_q$ on
$P$ when equal $r_a$ values imply equal $g_q$ values on $P$. Put

$$
H(P)=\{q:\text{no own-coordinate experiment }r_a\text{ determines }g_q
\text{ on }P\}.
$$

For a nonnegative weight $w:S\to[0,\infty)$ define the joint hard-target map
$Y_P(x)=(g_q(x))_{q\in H(P)}$ and its cell masses

$$
 b_y(P)=\sum_{x\in P:Y_P(x)=y}w(x),
 \qquad
 \kappa_w(P)^2=\sum_y b_y(P)^2 .
\tag{JTC.3}
$$

The empty hard-target vector is constant. In the native interface take
$S=S_d$, $g_q=\Gamma_q$ and $r_a(x)=r_x(a)$ for $q,a\in W_d$. A subset is
range-feasible when every $g_q(P)$ has at most four values. Every coordinate
projection of a native complete template is range-feasible because each target
is either constant or factors through one four-valued reply.

**Theorem 2.2 (joint externally forced target mass inequality).** Let
$B\subseteq\prod_{i=1}^n S_i$ be nonempty and jointly admissible: every target
$g_q(x_i)$ is constant on $B$ or equals a decoder applied to one experiment
$r_a(x_j)$ on a coordinate with arbitrary index $j$, including $j=i$.
Different targets may have different donors, with arbitrary cycles. Let
$P_i$ be the projection of the positive-product-weight rows, and let $w_i$
be nonnegative weights. Then

$$
\sum_{x\in B}\prod_i w_i(x_i)
\;\le\;\prod_{i=1}^n\kappa_{w_i}(P_i).
\tag{JTC.4}
$$

Here all factors are whole-block weights; no constructor factorization is
assumed.

**Proof.** If the left side is zero there is nothing to prove. Otherwise put
$\Pr[X=x]=\prod_iw_i(x_i)/\Omega$ on the positive rows. For every
$q\in H(P_i)$, a constant or self donor would make $g_q$ determined by an
own experiment, so a chosen witness has a donor $j(i,q)\ne i$.

Fix an ordering of the hard targets in each coordinate. For a permutation
$\pi$ of the coordinates, let $T_i(\pi)$ contain those hard targets whose
chosen donor precedes $i$. The vector $Y_{i,T_i(\pi)}$ is a function of $X_i$
and also a function of the preceding coordinates. Therefore

```math
I(X_i;X_{\mathrm{pre}(i)})\ge H(Y_{i,T_i(\pi)}).
```

For any subset of an ordered list, chain rule and conditioning monotonicity
show

$$
H(Y_{i,T_i(\pi)})
\ge\sum_{q\in T_i(\pi)}H\bigl(Y_{i,q}\mid Y_{i,q'<q}\bigr).
$$
Each selected donor precedes $i$ in exactly half of all permutations. Averaging
and summing gives the total-correlation bound

$$
\sum_iH(X_i)-H(X)\ge\frac12\sum_iH(Y_{P_i}(X_i)).
\tag{JTC.5}
$$

For one coordinate write $p_y=\Pr[Y_{P_i}=y]$. Conditional Gibbs
inequality in each cell gives

$$
H(X_i)+\mathbb E\log_2w_i(X_i)-H(Y_{P_i})/2
\le \frac12H(p)+\sum_yp_y\log_2 b_y(P_i)
\le \log_2\kappa_{w_i}(P_i).
\tag{JTC.6}
$$

The last step is relative entropy against the distribution proportional to
$b_y(P_i)^2$. Adding (JTC.6) and using
$\log_2\Omega=H(X)+\sum_i\mathbb E\log_2w_i(X_i)$ together with (JTC.5)
proves (JTC.4). Repeated donors and directed cycles are included because the
averaging is over one common joint law, with no independence assumption.
$\square$

**Corollary 2.3 (finite total verifier).** For rational $\mu$ on $S_d$ and
rational $C>0$, define $V_{\mathrm{joint}}(d,\mu,C,\pi)$ as follows. The
finite certificate $\pi$ lists, for every nonempty range-feasible
$P\subseteq\operatorname{supp}(\mu)$, the hard-target cells of $Y_P$ and
rational values for their masses. The verifier recomputes all target tables,
checks that the list is complete, and accepts exactly when

$$
\kappa_\mu(P)^2\le C^2
\quad\text{for every listed }P.
\tag{JTC.7}
$$

Malformed or incomplete tables are rejected. There are finitely many subsets,
targets and rational comparisons, so this is a total computable predicate.
If it accepts, every length-$n$ complete arbitrary-donor native template has
mass at most $C^n$ for every $n$. Thus the accepted cap satisfies the universal
mass premise of [NPC, Definition 8.1], with full joint block weights and all
correlations retained.

The verifier is a pointwise soundness result. It does not assert that accepted
caps are cofinal in the optimizing pressure, and it does not provide the
uniform finite-length modulus absent from [NPC, Proposition 8.3].

**Corollary 2.4 (exact analytical grouping).** For $m\ge1$, use the finite
interface $S_d^m$ with targets $(i,q)\mapsto\Gamma_q(x_i)$ and experiments
$(j,a)\mapsto r_{x_j}(a)$, including a constant. Each experiment still
returns one constituent reply. Enumerate every nonempty range-feasible
$P\subseteq\operatorname{supp}(\mu^{\otimes m})$ in this interface. If

$$
\kappa_{\mu^{\otimes m}}(P)^2\le C^{2m}
\quad\text{for every such }P,
$$

then $\beta_d(\mu)\le C$. Taking $m$ as a finite certificate parameter
gives another total sound verifier.

**Proof.** For any original admissible $B\subseteq S_d^N$, take its
$m$-fold Cartesian product and regroup its $mN$ indexed coordinates into
$N$ consecutive $m$-tuples. Each old target and its single donor retain
their indices within a supercoordinate; this is a bijective regrouping of
the same tuples, with no equality forgotten and no new experiment. The
mass is $\Omega_\mu(B)^m$. Theorem 2.2 bounds it by $C^{mN}$.
Taking the $m$-th root proves the claim for every $N$. Products here are
analytical relations, not copying of an actual source or a supplied cut
descriptor. No cofinality of these grouped certificates is proved. $\square$

## 3. Finite fractional covers and an original-task consequence

**Definition 3.1 (fractional native cover).** Let $Z_d(m)$ be the fractional
cover optimum of $S_d^m$ by all nonempty admissible subsets, with the whole
joint interface and all donor topologies retained. Finite LP duality gives a
nonnegative point weight $w$ of total $Z_d(m)$ such that every admissible set
has $w$-mass at most one.

**Theorem 3.2 (square-root lifting).** For every $d,m\ge1$,

$$
Z_d(km)\ge Z_d(m)^{k/2}\quad(k\ge1),
\qquad
\sigma_d\ge\frac{\log_2Z_d(m)}{2m}.
\tag{JTC.8}
$$

Consequently, for $D\ge d$ and $N=2^{D-d}$,

$$
M_1(D)\ge
\left\lceil Z_d(m)^{\lfloor N/m\rfloor/2}\right\rceil.
\tag{JTC.9}
$$

**Proof.** For the dual weight $w$ on $S_d^m$, every cell of a joint hard-target
map is internally admissible: hard targets are fixed on the cell, while every
other target retains its own-coordinate witness. If $a_w$ is the maximum
weight of an internally admissible set and $W=\sum w=Z_d(m)$, then

$$
\kappa_w(P)^2=\sum_y b_y(P)^2
\le a_w\sum_yb_y(P)\le W.
$$

Apply Theorem 2.2 to an admissible relation on $k$ supercoordinates. Its
mass is at most $W^{k/2}$, whereas the whole universe has product mass
$W^k$. The dual point weight therefore forces
$Z_d(km)\ge W^{k/2}$. Since $Z_d(n)\le K_d(n)$ and [FMR] gives
$\sigma_d=\lim_n n^{-1}\log_2K_d(n)$, taking that limit along
$n=km$ proves the rate inequality. Restricting
to $\lfloor N/m\rfloor$ actual blocks of a perfect scaffold and fixing leftover
blocks to $\alpha$ gives (JTC.9); the fixed blocks only turn donor equations
into constants. This is an analytical restriction of an actual scaffold, not
independent child codes.
$\square$

The complementary bound is
$\sigma_d\le m^{-1}\log_2Z_d(m)$. Indeed products of a length-$m$
fractional cover give a cover of length $km$ with weight $Z_d(m)^k$;
harmonic rounding costs at most $1+km\ln|S_d|$. Divide its logarithm by
$km$ and let $k\to\infty$. Thus the finite LP gives the full comparison

$$
\frac{\log_2Z_d(m)}{2m}\le\sigma_d
\le\frac{\log_2Z_d(m)}m,
$$

with a factor-two lower loss, rather than a vanishing length error.

The factor $1/2$ is part of the theorem. It is not legitimate to replace it by
one, and (JTC.8) is not an exact formula for $\sigma_d$.

**Convention 3.3 (literature boundary).** Madiman--Tetali, *Information
Inequalities for Joint Distributions, with Interpretations and Applications*,
Proposition II, uses one common finite-entropy joint law for fractional entropy covering; that
is the only outside entropy principle used in the proof of Theorem 2.2. It
does not give a native all-length tail modulus. The monotone convex/concave
normalizations in Jakhar--Kurri--Chillara--Prabhakaran likewise supply no
native cofinality theorem. Finite-language counting results such as
Dyer--Richerby concern arbitrarily large instances and do not furnish a
uniform cutoff for the native templates. These hypotheses are why
$V_{\mathrm{joint}}$ is recorded as soundness only.

[MT]: https://arxiv.org/html/0901.0044v2
[JKCP]: https://arxiv.org/html/2601.15723v1
[DR]: https://arxiv.org/html/1003.3879v4

## 4. Exact pressure transport through a fixed actual scaffold

**Definition 4.1 (fixed scaffold lift).** For $h\ge0$ put $k=2^h$. Define
$T_0(x)=x$ and recursively

$$
T_{h+1}(x_1,\ldots,x_{2k})
=\left\langle T_h(x_1,\ldots,x_k),
T_h(x_{k+1},\ldots,x_{2k})\right\rangle .
$$

This is one fixed perfect ordered height-$h$ scaffold with the $k$ actual
$S_d$ blocks at its frontier. For $w:S_d\to[0,\infty)$ define the lifted
weight on $S_{d+h}$ by

$$
 w^{\uparrow}(T_h(x_1,\ldots,x_k))=\prod_{j=1}^kw(x_j),
 \qquad w^{\uparrow}(u)=0\text{ off the image of }T_h.
\tag{JTC.10}
$$

Let $A_n^{(d)}(w)$ be the maximum $w$-mass of an admissible subset of
$S_d^n$, and put $\beta_d(w)=\sup_{n\ge1}A_n^{(d)}(w)^{1/n}$.

**Theorem 4.2 (exact fixed-scaffold pressure identity).** For every $n\ge1$,

$$
A_n^{(d+h)}(w^{\uparrow})=A_{kn}^{(d)}(w),
\qquad
\beta_{d+h}(w^{\uparrow})=\beta_d(w)^k.
\tag{JTC.11}
$$

**Proof.** Restrict a positive-mass coarse relation to the image of $T_h$.
Every target above the frontier has a fixed branch value. Every other target is
one fine-block target, with its literal prefixed by the fixed frontier address.
Conversely, regroup any admissible relation on $kn$ fine blocks into $n$
coarse blocks. A fine donor literal is prefixed by its public module address;
if it stops above the frontier its value is a constant. These translations
preserve every chosen donor, decoder and cycle, and preserve each product
weight exactly once. They are inverse on tuples, so both maxima in (JTC.11)
are equal. Finally admissible products give
$A_{km}^{(d)}(w)\ge A_m^{(d)}(w)^k$; hence restricting the pressure supremum to
multiples of $k$ changes nothing. $\square$

This is an identity for one fixed present scaffold and the displayed product
potential. It is not an arbitrary reblocking theorem: a source-dependent cut
descriptor, variable-shape tag or new pairing would itself be part of the
retained code and would need a separate acquisition cost.

## 5. A bounded-bundle pointwise obstruction

**Definition 5.1 (bounded-bundle test).** For $P\subseteq S_d$, let
$\operatorname{Bad}(P)$ be the targets not determined on $P$ by any own
experiment or by a constant. Fix $b\ge1$. The finite verifier
$V_b(d,\mu,C,\pi)$ accepts when, for every range-feasible
$P\subseteq\operatorname{supp}(\mu)$ with $\mu(P)>C$, the certificate lists a
nonempty $J_P\subseteq\operatorname{Bad}(P)$ with $|J_P|\le b$ and

$$
\sum_z\left(\sum_{x\in P:Y_{P,J_P}(x)=z}\mu(x)\right)^2\le C^2.
\tag{JTC.12}
$$

Here $Y_{P,J}$ is the vector of the selected targets. Exhaustive finite
checking makes $V_b$ total. Theorem 2.2 proves its soundness for every length
and every correlated native template: the full hard-target partition refines
the selected bundle, so its squared cell mass cannot increase; on a light
support its norm is at most the total mass $\mu(P)\le C$.

**Proposition 5.2 (an explicit native loss for every fixed bundle width).**
Use the credited depth-three weights and pressure value from [NCE]

$$
 v(\alpha)=v(\beta)=4,
\quad v(x)=1\ (x\in S_2\setminus\{\alpha,\beta\}),
$$

$$
 w(\alpha)=88,
\quad w(\beta)=52,
\quad w(\langle x,y\rangle)=v(x)v(y),
$$

whose total is $429$. Put

$$
P_0=\{\alpha,\beta\}\cup
\{\langle x,y\rangle:x,y\in\{\alpha,\beta\}\}.
$$

The six weights on $P_0$ are $88,52,16,16,16,16$, so

$$
 w(P_0)=204,\qquad
 \sum_{x\in P_0}w(x)^2=11472.
\tag{JTC.13}
$$

The six nonroot targets in $W_3$ are range-feasible and are not own-determined
on $P_0$; the root target is own-determined and is not needed. The joint map
of all six nonroot targets is injective on $P_0$.

For an exact check, the target ranges on $P_0$, in the order
$\varepsilon,L,R,LL,LR,RL,RR$, have sizes $3,4,4,3,3,4,4$. The corresponding
single-target squared cell sums are
$14544,12496,12496,15824,15824,12496,12496$; the joint six-target sum is
$11472$. These integers use the weights in (JTC.13), and the root entry is
listed only to show why it is excluded from $\operatorname{Bad}(P_0)$.

For $k=2^h\ge4b$, let $P_h=T_h(P_0^k)$ and
$\mu_h=w^{\uparrow}/429^k$. The credited depth-three pressure is
$\beta_3(w)=169$, hence Theorem 4.2 gives

$$
\beta_{h+3}(\mu_h)=B=\left(\frac{169}{429}\right)^k.
$$

Every cap accepted by $V_b$ at $\mu_h$ satisfies

```math
 C\ge T_{k,b}:=
 \frac{204^{k-b}\,11472^{b/2}}{429^k}>B.
\tag{JTC.14}
```

**Proof.** A coarse target is constant above the scaffold or depends on one
frontier module. A bundle of at most $b$ targets touches at most $b$ modules.
On a touched module its partition is coarser than the injective six-target
partition, so its squared cell sum is at least $11472$. An untouched module
contributes $204$ to its cell-mass norm. If $t\le b$ modules are touched,
the product partition's norm is at least
$204^{k-t}11472^{t/2}/429^k\ge T_{k,b}$; its squared norm is at least
$204^{2(k-b)}11472^b/429^{2k}$. Every target of $P_h$ is constant or a
target of one $P_0$ module, so $P_h$ is range-feasible. If it is light, the cap
already obeys $C\ge\mu_h(P_h)\ge T_{k,b}$; if it is heavy, the required bundle
has the same lower bound. Finally

$$
\sqrt{11472}>107,\qquad
204^3\cdot107=908394048>815730721=169^4,
$$
so $T_{k,b}>B$ whenever $k\ge4b$. $\square$

The normalized loss obeys

$$
2^{-(h+3)}\log_2(C/B)\ge\frac18\left[
\log_2\frac{204}{169}-\frac bk\log_2\frac{204}{\sqrt{11472}}\right].
$$

It stays positive along this specified weight family when $b/k\to0$;
this is not an assertion about optimization over other weights.

Zeros are not essential. Use the rational lower bound
$R=204^{k-b}107^b/429^k>B$ and
$\delta=(R-B)/(4(2+R))$. For the uniform law $u$ on $S_{h+3}$ put
$\widetilde\mu=(1-\delta)\mu_h+\delta u$ and $\widetilde C=B+2\delta$.
The continuity estimate supplied in [NPC, Theorem 6.1] gives
$\beta(\widetilde\mu)\le B+\delta<\widetilde C$, while every bundle cell
norm on $P_h$ is at least $(1-\delta)R$ and

$$
(1-\delta)R-\widetilde C=\frac34(R-B)>0.
$$
Thus the same bounded-bundle test rejects a strictly positive valid cap.
Both $\delta$ and $\widetilde C$ are rational, $0<\delta<1$, and
$\operatorname{TV}(\widetilde\mu,\mu_h)\le\delta$.

At $b=1,h=2,d=5$, the smallest hard single-target squared cell mass on $P_0$ is
$12496$ (the other two hard targets give $15824$). Direct integer arithmetic
checks

$$
12496\cdot204^6=900641637831868416
>665416609183179841=169^8.
$$

For the stated rational slack the required comparison is the stronger one

$$
\begin{aligned}
10000\cdot12496\cdot204^6&=9006416378318684160000,\\
10201\cdot169^8&=6787914830277617558041,\\
10000\cdot12496\cdot204^6-10201\cdot169^8
&=2218501548041066601959>0.
\end{aligned}
$$

Thus $V_1$ rejects the valid cap
$C=(101/100)(169/429)^4$. The pressure of the lifted weight is already
attained at length one by the lifted product of the credited $169$-mass set;
length enumeration cannot repair this failure.

This is a pointwise-completeness obstruction for the specified fixed-width
bundle language. It does not refute the optimizer-cofinality requested by
[NPC, Definition 8.1], and it does not exclude unrestricted bundle widths,
global recoloring, lawful finer cuts, or another sound proof system.

## 6. Paid native realization and remaining obligation

For the explicit lower-witness construction at $D=h+3$, let
$A_h=T_h(P_H^k)$ where $P_H$ is the credited depth-three attaining set of
mass $169$ and cardinality $100$. Scan every $Rq$ with $q\in W_D$ before the
request and export one name for all canonical right subtrees in $A_h$ and a
distinct canonical-state name for every other state. The complete attained
alphabet is exactly

$$
1+|S_D|-100^k.
$$

The scan uses at most $2^D-1$ charged preparation Reads, maximum submitted
length $D$, and $(D-1)2^D+1$ submitted letters. The exported name is isolated
under the paid handoff. On the merged name, scaffold targets above the
frontier are constants and each remaining target uses its own actual-root
literal at the fixed module occurrence; singleton names need no Read. The
reader chooses this optional one original-root Read before any authentic $k$
and then applies the credited $\Gamma$ decoder for all counts. At $D=5$ this
has $31$ preparation Reads, $129$ submitted letters, and
$128947164$ attained names. These are explicit paid resources for a deliberately
nonoptimal code, not an optimum for $M_1(D)$.

The unresolved original requirement is unchanged: no accepted finite family
in this volume is proved cofinal in $\sigma_d$, and no uniform effective
length error is supplied. Consequently no terminating two-sided approximation
of the original $\lambda$, no sharp general $M_1(D)$, and no physical
space-time recovery theorem follows here. The credited bounds
$\log_2(33/13)/8\le\lambda<3/16$ remain the relevant numerical interval.

## 7. A joint depth-four profile and its smaller-support obstruction

**Proposition 7.1 (a genuinely joint whole-block potential).** Use the
five actual motif trees $u_0,\ldots,u_4$ of [SRP, Definition 3.1], credited
to [NCM, Proposition 6.1]. Put

$$
T=\{\langle u_s,u_t\rangle:0\le s,t<5\}\subset S_4,
\qquad w(\langle u_s,u_t\rangle)=1+\mathbf1_{s=t},
$$

and set $w=0$ elsewhere. Then $|T|=25$, $w(T)=30$, and
$H(T)=\{LLL,RLL\}$. The joint hard-target squared cell mass is $78$,
whereas either single hard target has squared cell mass $252$. Hence
every admissible $B\subseteq T^n$ whose positive coordinate projections
are all exactly $T$ satisfies $\Omega_w(B)\le78^{n/2}$.

**Proof.** On the motif, only $LL$ has no own witness; the other six
targets use respectively a constant, $L,R,L,RL,R$ for
$\varepsilon,L,R,LR,RL,RR$, as in [NCM, (NCM.27)--(NCM.30)].
Every experiment on a paired tree is constant at its root or enters just
one motif module. Since $T$ is the full paired support, an experiment in
the other module cannot determine a nonconstant target of this module.
Thus precisely $LLL,RLL$ are hard.
Every target has at most four values by those same motif tables, so
$T$ is range-feasible.

The motif $LL$ partition has index cells
$\{0,4\},\{1\},\{2\},\{3\}$. Their paired joint cell masses consist
of $6,2,2,2$ on the diagonal, six off-diagonal masses $2$ and six masses
$1$. Their squared sum is $36+12+24+6=78$. For one target the cell
masses are $12,6,6,6$, whose squared sum is $252$. Apply Theorem 2.2.
The potential does not factor across the two actual modules: its
$\{0,1\}\times\{0,1\}$ minor is
$\left(\begin{smallmatrix}2&1\\1&2\end{smallmatrix}\right)$, with
determinant $3$. It is owned once as a function on $S_4$. $\square$

**Proposition 7.2 (checking only the full support is unsound).** Let
$H=\{u_1,u_2,u_3,u_4\}$. The one-coordinate native set
$\{\langle x,y\rangle:x,y\in H\}\subset T$ is locally admissible
and has weight $20$. In particular $C=\sqrt{78}$ is not an all-length
cap for the weight in Proposition 7.1, since $20^2=400>78$.

**Proof.** The four $RL$ replies on $H$ are respectively absent, alpha,
beta and branch. They identify its states, so determine every motif
target. For a paired tree, prefix that one witness by the target module's
side; the paired root target is constant. All $W_4$ targets therefore
have one own-coordinate witness. There are sixteen paired states, four
with weight two and twelve with weight one, giving mass twenty. This is
a legal length-one counterexample to using the full-support value as a
universal cap. Corollaries 2.3--2.4 retain every range-feasible support,
and so include this smaller support. Explicitly, on the rational input
$\mu=w/30$, $C=1/3$, checking only $T$ would pass $78\le100$;
the smaller support fails $400\le100$ and the actual verifier rejects.
$\square$

**Proposition 7.3 (an attained paired joint-profile relation).** Let
$\tau$ swap $1,4$ and fix $0,2,3$. The 25-row relation

$$
B_{25}=\{(\langle u_s,u_t\rangle,
              \langle u_{\tau(s)},u_{\tau(t)}\rangle):0\le s,t<5\}
\subset S_4^2
$$

is jointly admissible, with both projections $T$ and product mass $40$.
For $n=2^h$, $h\ge1$, its disjoint products are actual admissible
relations on $n$ blocks, with $25^{n/2}$ rows and mass $40^{n/2}$.

**Proof.** In each side module use the credited paired motif witnesses
of [NCM, Proposition 6.1]: its $LL$ target reads $RL$ in the mate module
of the other block; all other targets use the own witnesses in the proof
of Proposition 7.1. Prefixing by the side preserves all thirty target
equations. The involution preserves equality of $s,t$, so five rows have
product weight four and twenty have product weight one, giving forty.
Products use the same witnesses within each pair.

For paid realization, place these $n$ actual blocks at the public
height-$h$ scaffold in the right subtree, with $D=h+4$. Merge exactly
this canonical relation into one name and give every other state of
$S_D$ its own name, extending by $\pi_D$ to the whole $\mathcal F_D$.
All names are attained; their complete number is
$|S_D|-25^{n/2}+1$. Acquire every $Rq$, $q\in W_D$, before the
request: $2^D-1$ Reads, maximum length $D$ and $(D-1)2^D+1$ letters.
Export only the fixed-width name and isolate the boundary and all other
source dependence under the declared paid service. Singleton names need
no Read; the special name uses the mate's fixed actual-root literal for
the hard target and its own literal for the other targets. Every literal
has length at most $D$ and is chosen before the authentic count.
The all-count factor law proves correctness on every canonicalization
fiber, including variable shapes and terminal-label variations. Tables,
membership work, control/allocation, workspace, predictor and physical
services remain separate resources. $\square$

## 8. A strict projection profile with an actual six-row realization

**Theorem 8.1 (strict original-code projection profile).** Retain $w,P_0$
from Proposition 5.2 and put $a=\sqrt{11472}/169<1$. For every admissible
$B\subseteq S_3^n$, let $r$ count its positive-weight coordinate
projections that equal $P_0$. Then

$$
\Omega_w(B)\le169^n a^r.
$$

For the actual depth-$D$ perfect-scaffold slice with $n=2^{D-3}$,
$D\ge3$, let $r_e$ be that count for each nonempty restricted fiber of
any original correct complete code. Then

$$
\sum_e a^{r_e}\ge(33/13)^n.
$$

In particular, if every such fiber has $r_e\ge r_*$, the complete
attained alphabet is at least $\lceil(33/13)^n a^{-r_*}\rceil$.

**Proof.** On $P_0$ the joint hard-target partition is injective and
has squared cell mass $11472$. Every other range-feasible projection
has joint cap at most $169$: a light support has norm at most its total
mass, while on a heavy support the joint partition refines the hard
target supplied by [NCE, Theorem 4.3], whose squared cell mass is below
$169^2$. Theorem 2.2 proves the first inequality. The original slice
has total mass $429^n$ and its unchanged code fibers are admissible by
[NPC, Theorem 7.1]. Sum their masses and divide by $169^n$. There is
no premise that every fiber has a $P_0$ projection in the summed
inequality. The last statement follows from $a<1$. $\square$

**Proposition 8.2 (six rows and all native target witnesses).** Put
$C=\langle A,A\rangle$, $J=\langle B,A\rangle$,
$Q=\langle C,A\rangle$ and $(t_0,t_1,t_2,t_3)=(A,C,J,Q)$,
where $A=\alpha$, $B=\beta$. For $s=L,R$ define on $P_0$

$$
\ell_s(A)=0,\quad\ell_s(B)=1,\quad
\ell_s(\langle x,y\rangle)=
\begin{cases}2,&\text{the }s\text{-child is }A,\\
3,&\text{the }s\text{-child is }B.\end{cases}
$$

The following six rows form an actual admissible $B_6\subset S_3^3$:

$$
\begin{array}{c|cc}
x&t_{\ell_L(x)}&t_{\ell_R(x)}\\\hline
A&A&A\\
B&C&C\\
\langle A,A\rangle&J&J\\
\langle A,B\rangle&J&Q\\
\langle B,A\rangle&Q&J\\
\langle B,B\rangle&Q&Q
\end{array}
$$

Its first projection is $P_0$, and both donor projections are
$\{A,C,J,Q\}$, of weight $124$ and with no hard targets. Its product
mass is $701184$, and its joint-profile squared upper bound is
$11472\cdot124^4=2712226025472$.

**Proof.** On $(t_0,t_1,t_2,t_3)$ the experiment $L$ gives respectively
absent, alpha, beta and branch. It identifies the four states and hence
determines each of their seven targets. For the first coordinate the
root target uses its own root reply. A nonroot target $sq$, $|q|\le1$,
depends only on $\ell_s(x)$: for indices zero and one its value is
$\Gamma_{sq}(A)$ and $\Gamma_{sq}(B)$; for indices two and three it
is $\Gamma_q(A)$ and $\Gamma_q(B)$. Read $L$ in the corresponding
donor coordinate and use these four values as the decoder. This gives
all 21 target witnesses on the same six tuples, including initially
absent targets and every authentic count via the factor law. The six
product weights sum to

$$
88^3+52\cdot16^2+16(16+4)^2=701184.
$$

The donor weights are $88,16,16,4$. Applying Theorem 2.2 to its three
projections gives the stated squared bound; equality is not asserted.
$\square$

**Proposition 8.3 (paid full-family realization at depth five).** In the
right subtree put the four actual blocks $(x,y,z,A)$ at scaffold
addresses $LL,LR,RL,RR$, where $(x,y,z)\in B_6$. These six canonical
states form one attained code fiber on the full $\mathcal F_5$, with
every other canonical state separately named. The complete attained
alphabet is $|S_5|-5=228947158$.

**Proof.** The trees are in $S_5$ and are distinct. Scan all $Rq$,
$q\in W_5$, using 31 charged preparation Reads, maximum length five
and 129 letters on every source. Compute $\pi_5(v)$ and its fixed-width
name. The actual special fiber is the inverse image of these six
states under $\pi_5$, not a restriction to exact terminal labels.
All other acquired distinctions are removed by the paid isolation.

After the request, a special-fiber target above the scaffold is
constant. Inside one of its first three blocks, implement Proposition
8.2's chosen witness by prefixing its donor literal with $R$ and that
donor block's public address. These words have length at most four.
The fourth block is constant $A$ and all its target factors are public.
Other names determine a canonical state and need no Read. All choices
precede the authentic count and the factor law answers every later
count without Reads. Every name is attained by an actual canonical
source. Common tables, membership computation, padded control and
buffers, post-request workspace, predictor size, authentication,
isolation and physical time remain separate resources. $\square$

## 9. A finite recursive certificate calculus

**Definition 9.1 (the calculus $V_{\mathrm{rec}}$).** A certificate is a
finite table of nodes in topological order, with each node labelled by
a positive depth $d$, a rational probability $\mu$ on the entire $S_d$
and a rational $C>0$. Its last label must equal the input $(d,\mu,C)$.
Every node has exactly one of the following justifications:

1. A joint-target leaf whose finite tables pass Corollary 2.3, its
   grouped version in Corollary 2.4, or the bounded-bundle test of
   Definition 5.1.
2. A scaffold node referring to an earlier label $(d_0,\nu,C_0)$ and
   an integer $h\ge0$. Check $d=d_0+h$, the exact full-table equality
   $\mu=\nu^{\uparrow}$ of Definition 4.1, and $C\ge C_0^{2^h}$.
3. A stability node referring to an earlier label $(d,\nu,C_0)$ at
   the same depth. Check
   $C\ge C_0+\frac12\sum_{x\in S_d}|\mu(x)-\nu(x)|$.

All referenced indices must be strictly earlier. Malformed labels,
nonprobabilities, incomplete tables and failed rational comparisons
are rejected. No node assumes an unverified all-length cap.

**Theorem 9.2 (totality, soundness and the rejected-width examples).**
$V_{\mathrm{rec}}$ is total computable and every acceptance implies
$\beta_d(\mu)\le C$. It accepts the lifted caps $(\mu_h,B)$ of
Proposition 5.2, the strict cap
$(\mu_2,(101/100)(169/429)^4)$ rejected there by $V_1$, and every
strictly positive perturbed cap $(\widetilde\mu,\widetilde C)$
specified there. No cofinality is asserted.

**Proof.** A finite table has finitely many finite state, target and
rational checks, each terminating; there is no search for an unknown
length cutoff. Induct along its node order. Leaves are sound by §2
and Definition 5.1. Scaffold nodes are sound by the exact pressure
identity of Theorem 4.2. Stability nodes are sound by the probability
total-variation estimate of [NPC, Theorem 6.1]. Thus the last cap is
valid at every length and for every complete native template.

For the examples, $\nu=w/429$ at depth three has a $V_1$ leaf with
$C_0=169/429$: [NCE, Theorem 4.3] supplies a suitable hard target on
every heavy range-feasible support, and light supports need no bundle.
This determines a finite exhaustive leaf table. A height-$h$ scaffold
node then proves $(\mu_h,B)$. Its cap may be enlarged to
$(101/100)B$ in that same scaffold check. For the positive perturbation,
append a stability node; its variation is at most $\delta$, so the
rational cap $B+2\delta$ passes. These acceptances cover the actual
fixed-width rejection examples without changing their weights or
claiming that arbitrary potentials admit this decomposition. $\square$

The missing optimizer-cofinality obligation is still exactly: for every
$d$ and rational $\epsilon>0$, obtain a $V_{\mathrm{rec}}$ acceptance
with $-\log_2C>\sigma_d-\epsilon$. None of the three rules proves
that assertion. The failure of fixed bundle width at specified weights
also does not refute it.

## 10. Supplier and representation boundaries

**Convention 10.1 (credited vocabulary and its scope).** The direct
native vocabulary is $S_d$, its replies $r_a$ and targets $\Gamma_q$,
constant factors, arbitrary single-reply donor factors, one full owned
potential per original block, and every finite length and topology.
[CBN, Theorems 2.2, 4.2 and 6.2] give its equality-aware constructor
presentation; [NDR, Theorems 2.2 and 2.4] give the whole-block template
and join suppliers. These are reused representations, not additional
theorems of this volume. The credited parity potential of [CBN,
Proposition 8.2] has parity-class products sixteen and one, which rules
out its unary/binary potential factorization. Its Proposition 8.1
rules out independent replicas of one shared reply. The cyclic motif
of [NCM, Proposition 6.1] requires off-coordinate donors; [NDR, §7]
gives the bounded-original-component obstruction, while its §9 gives
one lawful finer cut. None excludes all finer cuts, global recoloring
or every effective certificate.

**Proposition 10.2 (no direct identity handoff to predecessor recovery).**
The stationary family $\mathcal F_D$ is disjoint from the image of
$\rho$. Consequently the returned predecessor-row reader of [ERC]
cannot be applied by identifying its substituted source with an
original source in $\mathcal F_D$.

**Proof.** No substitution image is $\alpha$. A substituted leaf is
$\beta$ or $\langle\beta,\alpha\rangle$; a substituted pair has
left child another substitution image, hence never $\alpha$. Thus no
image is a pair with left child $\alpha$, as every member of
$\mathcal F_D$ is. The declaration `returned_native_reader` runs on
$\rho(u)$ and targets the complete predecessor row. Its assumptions
include a prefix-free cut, a complete row with nonempty `OriginFiber`,
$r\ge1$ and compatible acquired image values. The finite minimax in
[FRM] uses the attained three-reply class-root chart. These are valid
different endpoints and supply no all-length weighted-template cap
without an operation- and cardinality-preserving reduction. No such
reduction is used here. $\square$

**Convention 10.3 (attribution).** The joint donor-order inequality,
its finite-LP and projection consequences, the fixed-scaffold weighted
identity, the example profiles and the stated certificate boundaries
are repository-derived ordinary deductions. The finite entropy-cover
and Gibbs steps are the mature intermediates cited in §3. The
single-residual cycle theorem and its restricted all-length covers
are in [SRP]; the native graph-cover and Bethe counterexamples are in
[GCB]. All countable-length cap claims retain arbitrary complete
templates, common realization and one owned whole-block potential.
Finite LP computability, semantic minimizing weights from [NPC], and
soundness of $V_{\mathrm{rec}}$ leave the uniform effective tail and
cofinality open. Sharp $\lambda$, general $M_1(D)$ and the full
mutual-recovery programme retain their unchanged goals.

[NPC]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[FMR]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[AAR]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[NCE]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[NCM]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[NDR]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DONOR_NETWORKS_AND_REPAIR_COST.md
[CBN]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[SRP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SINGLE_RESIDUAL_PRESSURE.md
[GCB]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GRAPH_COVER_BETHE_BOUNDARIES.md
[ERC]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.lean
[FRM]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.lean

## 追加锚（本行以下为增补区）
