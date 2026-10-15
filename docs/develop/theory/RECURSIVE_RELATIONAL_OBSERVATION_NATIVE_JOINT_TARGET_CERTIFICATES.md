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
$r_a(x_j)$ on another coordinate, with arbitrary donor indices and cycles. Let
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

$$
I(X_i;X_{\mathrm{pre}(i)})\ge H(Y_{i,T_i(\pi)}).
$$
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
$\sigma_d=\inf_n n^{-1}\log_2K_d(n)$, the rate inequality follows. Restricting
to $\lfloor N/m\rfloor$ actual blocks of a perfect scaffold and fixing leftover
blocks to $\alpha$ gives (JTC.9); the fixed blocks only turn donor equations
into constants. This is an analytical restriction of an actual scaffold, not
independent child codes.
$\square$

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
V_\mathrm{joint} is recorded as soundness only.

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
and every correlated native template.

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
 w(P_0)=204,qquad
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

$$
 C\ge T_{k,b}:=
 \frac{204^{k-b}\,11472^{b/2}}{429^k}>B.
\tag{JTC.14}
$$

**Proof.** A coarse target is constant above the scaffold or depends on one
frontier module. A bundle of at most $b$ targets touches at most $b$ modules.
On a touched module its partition is coarser than the injective six-target
partition, so its squared cell sum is at least $11472$. An untouched module
contributes $204$. The product partition therefore has squared norm at least
the numerator in (JTC.14), divided by $429^k$. If $P_h$ is light, the cap
already obeys $C\ge\mu_h(P_h)\ge T_{k,b}$; if it is heavy, the required bundle
has the same lower bound. Finally

$$
\sqrt{11472}>107,qquad
204^3\cdot107=908394048>815730721=169^4,
$$
so $T_{k,b}>B$ whenever $k\ge4b$. $\square$

Zeros are not essential. Let $R=T_{k,b}$ and
$\delta=(R-B)/(4(2+R))$. For the uniform law $u$ on $S_{h+3}$ put
$\widetilde\mu=(1-\delta)\mu_h+\delta u$ and $\widetilde C=B+2\delta$.
The continuity estimate supplied in [NPC, Theorem 6.1] gives
$\beta(\widetilde\mu)\le B+\delta<\widetilde C$, while every bundle cell
norm on $P_h$ is at least $(1-\delta)R$ and

$$
(1-\delta)R-\widetilde C=\frac34(R-B)>0.
$$
Thus the same bounded-bundle test rejects a strictly positive valid cap.

At $b=1,h=2,d=5$, the smallest single-target squared cell mass on $P_0$ is
$12496$ (the two remaining targets give $15824$). Direct integer arithmetic
checks

$$
12496\cdot204^6=900641637831868416
>665416609183179841=169^8.
$$

Therefore $V_1$ rejects the valid cap
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

[NPC]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[FMR]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[AAR]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[NCE]: https://github.com/the-omega-institute/trureturing/blob/54970a4baa12394e603ff4fc76987d86e1879264/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md

## 追加锚（本行以下为增补区）
