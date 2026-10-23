# Late-contact rigidity of complete common-law flows

## 1. The complete boxed compatibility problem

**Assumption 1.1 (unchanged source and analytical domain).** Use the source
of [PAIR, Sections 2 and 11][PAIR], with $(m,d,\ell,n)=(2,1,2,4)$.
One depth $K$ is drawn before the first paid Read from a fixed finite or
countable prior $\mu$, with $\mu(1),\mu(2)>0$. Conditional on this same
$K=k$, the letters have alpha probability $r_k=F_{k+1}/F_{k+3}$,
where $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$. Every supported depth remains
a target. Both seeds, paid rejections, partial parses, all finite returns,
marker triples, held records, third write before latch, fourth completion
and matching Stop retain their original meaning. Acquired and synthetic
updates are the same. Configuration TV is taken before averaging.
COMPLETE charges the original control, installed program and numbers,
sampler states, selectors, workspace and persistent randomness.
The descriptor measures below are analytical objects, not extra accessible
registers or source operations.

**Definition 1.2 (carriers, regularity and endpoint boxes).** Put

$$
a=\frac13,\quad b=\frac25,\quad \lambda=\frac4{15},\qquad
z_r=r(1-r),\quad c_r=(1-r)^2\quad(r\in\{a,b\}).
\tag{1.1}
$$

Write $w_{j,0}=(\beta\alpha)^j\alpha$ and
$w_{j,1}=(\beta\alpha)^j\beta\beta$ for $j\ge0$. The countable complete
carriers and tails, including the noncompletion outcomes, are

$$
\begin{aligned}
\Omega_p&=\{w_{j,i}:j\ge0,\ i=0,1\}\cup\{\infty_p\},\\
\Omega_\beta&=\{\beta\}\cup\{\alpha w_{j,i}:j\ge0,\ i=0,1\}
                 \cup\{\infty_\beta\},\\
T_p(j)&=\{w_{k,i}:k\ge j,\ i=0,1\}\cup\{\infty_p\},\\
T_\beta(j)&=\{\alpha w_{k,i}:k\ge j,\ i=0,1\}\cup\{\infty_\beta\}.
\end{aligned}
\tag{1.2}
$$

All descriptors are normalized probability measures. The original
compact metric spaces, with complete-law TV, are

$$
\begin{aligned}
\mathcal K_p&=\{Q:a\le u(Q):=Q(\alpha)\le b,
                      \ Q(T_p(j))\le\lambda^j\ (j\ge0)\},\\
\mathcal K_\beta&=\{W:a\le v(W):=1-W(\beta)\le b,
                      \ W(T_\beta(j))\le b\lambda^j\ (j\ge0)\}.
\end{aligned}
\tag{1.3}
$$

Their compactness is [PAIR, Lemma 11.1]. These bounds force zero infinite
mass by letting $j\to\infty$; no conditioning on completion is performed.
The native laws have zero infinite masses and

$$
P_{p,r}(w_{j,0})=rz_r^j,\qquad P_{p,r}(w_{j,1})=c_rz_r^j,
\qquad P_{\beta,r}=(1-r)\delta_\beta+r\alpha P_{p,r}.
\tag{1.4}
$$

For all other supported $r_k$, use the same formula with
$z_r=r(1-r)$ and $c_r=(1-r)^2$. The full endpoint box at phase $s$ is

$$
\min\{P_{s,a}(e),P_{s,b}(e)\}\le D(e)\le
\max\{P_{s,a}(e),P_{s,b}(e)\}\qquad(e\in\Omega_s).
\tag{1.5}
$$

**Definition 1.3 (the original two flows).** A compatible pair consists
of Borel probabilities $\Gamma_B$ on $\mathcal K_p\times\mathcal K_\beta$
and $\Gamma_A$ on the reversed product, with common unweighted marginals

$$
(\Gamma_B)_1=(\Gamma_A)_2=\nu_p,\qquad
(\Gamma_B)_2=(\Gamma_A)_1=\nu_\beta.
\tag{1.6}
$$

Their regular conditional kernels $B(Q,dW)$ and $A(W,dQ')$ satisfy

$$
Q=u(Q)\delta_\alpha+(1-u(Q))\beta\!\int W B(Q,dW),\qquad
W=(1-v(W))\delta_\beta+v(W)\alpha\!\int Q'A(W,dQ').
\tag{1.7}
$$

Each equality holds almost surely for its input marginal as an equality
of complete measures. Prefixing includes the corresponding infinite
outcome. These are exactly the full-descriptor residual equations of
[PAIR, Definition 11.2]; conditioning is on the entire input law.
The factors $1-u$ and $v$ do not weight the marginals in (1.6).
The boxed compatible class further requires (1.5) almost surely at both
phases. Its marginals may have arbitrary Borel support.

## 2. One mean contact determines the original flows

**Theorem 2.1 (late-contact classification).** For every boxed compatible
pair, every integer $n\ge4$ and each $r\in\{a,b\}$, the following are
equivalent:

$$
\begin{gathered}
d_n:=\int Q(w_{n,1})\,d\nu_p(Q)=c_rz_r^n;\\[2pt]
\nu_p=\delta_{P_{p,r}},\qquad \nu_\beta=\delta_{P_{\beta,r}},\qquad
\Gamma_B=\delta_{(P_{p,r},P_{\beta,r})},\qquad
\Gamma_A=\delta_{(P_{\beta,r},P_{p,r})}.
\end{gathered}
\tag{2.1}
$$

No recurrence, finite support, reversibility or deterministic-successor
hypothesis is imposed. The classification concerns the original flows.

**Proof.** Disintegration is available on the compact metric descriptor
spaces. The common marginals give $\nu_pB=\nu_\beta$ and
$\nu_\beta A=\nu_p$. Thus $B,A$ act on bounded measurable functions
modulo their respective marginal null sets: for example, if
$f=0$ $\nu_p$-almost surely, then
$\int A|f|\,d\nu_\beta=\int|f|\,d\nu_p=0$.
Consequently all the following iterations are independent of conditional
versions and representatives. Countability of the complete carriers
makes (1.7) simultaneous on all coordinates outside one null set per
phase. No choice at a null input enters the argument.

On p functions define the Markov return operator $P$ and positive
weighted return operator $L$ by

$$
Pf=B(Af),\qquad Lf=(1-u)B(vAf),\qquad
g=(1-u)B(1-v).
\tag{2.2}
$$

The original unweighted balances and regular emissions give

$$
\nu_pP=\nu_p,\qquad \frac15Pf\le Lf\le\frac4{15}Pf\quad(f\ge0),
\qquad c_b\le g\le c_a.
\tag{2.3}
$$

Here the kernel weights $(1-u)v$ lie in $[1/5,4/15]$.
Evaluating the B recursion at $\beta\beta$ gives $q_0=g$, where
$q_j(Q)=Q(w_{j,1})$. Evaluating it at $\beta\alpha w_{j,1}$ and then using
the A equation gives $q_{j+1}=Lq_j$. Similarly, with
$p_j(Q)=Q(w_{j,0})$, one has

$$
q_j=L^jg,\qquad p_j=L^ju\qquad(j\ge0).
\tag{2.4}
$$

These are the supplied complete-word recursions [NATIVE, (2.3)--(2.5)][NATIVE].
They are conditional barycentric identities; no sampled successor is
replaced by its barycentre inside a nonlinear expression.

The ratio of native marker-one coordinates is

$$
\frac{c_bz_b^j}{c_az_a^j}
=\frac{81}{100}\left(\frac{27}{25}\right)^j.
\tag{2.5}
$$

It is below one at $j=2$, above one at $j=3$, and strictly increasing.
Thus $c_az_a^j\le q_j\le c_bz_b^j$ almost surely for every $j\ge3$.
If $d_n=c_rz_r^n$, a nonnegative endpoint difference has integral zero,
so $q_n=c_rz_r^n$ almost surely.

Put $c=c_r,z=z_r$. For $r=b$, the upper bounds at $n-1$ and $n+1$ give

$$
c z^n=q_n=Lq_{n-1}\le c z^{n-1}L\mathbf1,
\qquad c z^n L\mathbf1=Lq_n=q_{n+1}\le c z^{n+1}.
\tag{2.6}
$$

Hence $L\mathbf1=z\mathbf1$. For $r=a$ both inequalities reverse,
and the same equality follows. All three indices are in the fixed-order
region because $n\ge4$. Iteration in the null-set quotient gives
$L^n\mathbf1=z^n\mathbf1$.

For $r=a$ set $f=c_a-g$; for $r=b$ set $f=g-c_b$. In either case
$f\ge0$ by (2.3), and (2.4) gives $L^nf=0$. Positivity and (2.3)
imply $L^kf\ge5^{-k}P^kf$ for all $k$: the induction step applies
$L$ to the previous inequality and then uses $L(P^kf)\ge P^{k+1}f/5$.
Invariance of the same unweighted marginal now yields

$$
0=\int L^nf\,d\nu_p\ge5^{-n}\int P^nf\,d\nu_p
 =5^{-n}\int f\,d\nu_p\ge0.
\tag{2.7}
$$

Therefore $g=c_r$ almost surely. Both factors of
$g=(1-u)B(1-v)$ lie in $[1-b,1-a]$, whose lower endpoint is positive.
Equality with either extremal square forces both factors to that
endpoint. Thus $u=r$ almost surely and $B(v=r)=1$ almost surely.
The identity $\nu_pB=\nu_\beta$ gives $v=r$ $\nu_\beta$-almost surely.
It follows that $L=z_rP$, so (2.4) gives
$p_j=rz_r^j$ and $q_j=c_rz_r^j$ for every $j$. Their simultaneous
coordinate equalities and the zero infinite mass prove
$Q=P_{p,r}$ almost surely. The A equation then proves
$W=P_{\beta,r}$ almost surely, again on the entire carrier.
A probability measure whose two marginals are specified Dirac masses
is their Dirac pair, proving both flow identities in (2.1).
Conversely the native laws satisfy (1.7), have tails $z_r^j$ and
$rz_r^j$, and satisfy all boxes. Their Dirac flows are compatible and
have the stated mean. $\square$

## 3. Strict tails on the midpoint face

**Definition 3.1 (midpoints and original zero level).** Set

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\quad
C=\frac{11758471}{22781250},\quad \rho_p=\frac{1116529}{22781250},
\quad \rho_\beta=\frac{239}{6750}.
\tag{3.1}
$$

The original zero face consists of compatible pairs with

$$
\mathcal J=\max_{s\in\{p,\beta\}}
\left\{\sup_{k:\mu(k)>0}\int\operatorname{TV}(D,P_{s,r_k})\,d\nu_s(D)
-\rho_s\right\}=0.
\tag{3.2}
$$

Every supported target, the complete configuration law and the order of
TV and averaging are retained. [PAIR, (11.29)--(11.30)] supplies both
full boxes and $\int Q(E_p)\,d\nu_p=C$ at zero level. Indeed the two
endpoint losses have sum at least $2\rho_s$ and each is at most
$\rho_s$; equality in their integrated coordinate triangle inequality
forces the boxes simultaneously on the countable carrier. Inside the
boxes the endpoint-positive event identifies the midpoint mean.

**Corollary 3.2 (every late mean is strictly interior).** Every boxed
compatible pair satisfying the original p midpoint obeys

$$
c_az_a^n<d_n<c_bz_b^n\qquad(n\ge4).
\tag{3.3}
$$

In particular (3.3) holds on the original zero face for every allowed
finite or countable prior, including a prior supported only at the two
endpoints.

**Proof.** The boxes give the weak inequalities. Either equality invokes
Theorem 2.1. But the forced event value is
$P_{p,a}(E_p)=C+\rho_p$ or $P_{p,b}(E_p)=C-\rho_p$, neither of which
is $C$. $\square$

**Corollary 3.3 (one retained NULL155 tail mean prevents completion).**
The two p laws of [NULL155, Definition 2.1][NULL155] both have
$Q(w_{n,1})=c_az_a^n$ for every $n\ge5$. Any proposed compatible
original zero-face completion must strictly increase each of these
averaged coordinates, even if its descriptor support, weights, early
coordinates and conditional branching are all allowed to change.
Preserving even one such mean is impossible.

**Proof.** Every probability mixture of the two specified p descriptors
has the same displayed late means. Apply (3.3) separately at each
$n\ge5$ to any proposed completion. This is a necessary condition on a
completion, not its existence. The fixed null itself has unequal full
marginals and omitted nonzero residuals [NULL155, Proposition 5.1], so
it is not an input to Theorem 2.1. $\square$

## 4. The universal cutoff cannot be lowered

**Proposition 4.1 (boxed compatible contact at depth three).** There is
a nonnative compatible singleton pair satisfying both complete endpoint
boxes with $d_3=c_bz_b^3$. It fails both original midpoint equations,
and therefore is not a zero-level example.

**Proof.** Use the supplied singleton parametrization
[REV, (11.22)][REV], also used for depth-three contacts in
[NATIVE, Proposition 4.1]. Choose

$$
t=\frac{23}{100},\quad g=c_b(z_b/t)^3=\frac{124416}{304175},\quad
u=1-t-g=\frac{87839}{243340},\quad
v=\frac{t}{t+g}=\frac{279841}{777505}.
\tag{4.1}
$$

Take $Q(w_{j,0})=ut^j$, $Q(w_{j,1})=gt^j$ and
$W=(1-v)\delta_\beta+v\alpha Q$, with zero infinite masses and unit
flows on $(Q,W)$ and $(W,Q)$. Exact rational comparison gives
$a<u,v<b$ and $z_a<t<z_b<\lambda$.
The identities $(1-u)v=t$, $(1-u)(1-v)=g$ and $u+g=1-t$
prove normalization and both complete residual equations.

Here are all exceptional marker-one box inequalities as nonnegative
rational slacks. The two columns subtract the smaller endpoint from the
actual mass and the actual mass from the larger endpoint, respectively.

| Phase and depth | Lower slack | Upper slack |
| --- | ---: | ---: |
| p, 0 | $14913/304175$ | $96956/2737575$ |
| p, 1 | $2538/330625$ | $125576/26780625$ |
| p, 2 | $324/359375$ | $81296/261984375$ |
| p, 3 | $254584/2562890625$ | $0$ |
| suspended, 0 | $2502/777505$ | $488164/524815875$ |
| suspended, 1 | $110800888/118083571875$ | $340092/485940625$ |

Every entry is obtained by positive-denominator subtraction in (4.1).
For p the endpoint order is fixed from depth three by (2.5); for suspended
marker one its endpoint ratio is $(243/250)(27/25)^j$, above one for
$j\ge1$. From the last checked depth onward, actual masses multiply by
$t\in[z_a,z_b]$, while lower and upper endpoints multiply by $z_a,z_b$.
Induction proves all remaining marker-one bounds. The marker-zero bounds
at all depths follow from $a\le u,v\le b$ and $z_a\le t\le z_b$:
$a z_a^j\le ut^j\le b z_b^j$ and
$a^2z_a^j\le vut^j\le b^2z_b^j$. Standalone beta is boxed as well.
The exact complete tails are $t^j$ and $vt^j$, bounded by
$\lambda^j$ and $b\lambda^j$ for every $j$. They even lie between the
corresponding native endpoint tail masses. This accounts for every
finite atom and both retained infinite outcomes.

Finally,

$$
d_3=\frac{1944}{390625}=c_bz_b^3,\qquad
c_bz_b^4-d_4=\frac{486}{9765625}>0.
\tag{4.2}
$$

Thus the singleton is nonnative. With
$E_\beta=\{\beta,\alpha w_{0,1}\}$ and $H=5261/6750$, its exact mean
errors are

$$
Q(E_p)-C=\frac{95291623}{11087178750}>0,\qquad
W(E_\beta)-H=\frac{8280311}{1049631750}>0.
\tag{4.3}
$$

This proves sharpness in the boxed compatible class, independently of
midpoint or zero-level feasibility. $\square$

## 5. Mathematical correspondence and remaining scope

**Citation 5.1 (suppliers and the specific implication).** [PAIR,
Theorem 18.2] classifies finite-p-support flows from an eventual two-root
recurrence. [NATIVE, Theorem 3.1] already removes that support restriction
for its stated three-depth source, and Corollary 3.3 excludes preservation
of an entire eventual endpoint tail. Those results assume an eventual
sequence identity. Theorem 2.1 instead derives the original pure pair
from one mean equality and neighboring boxes, with arbitrary Borel
marginals and no recurrence premise. The present Corollary 3.3 excludes
retaining even one NULL155 late mean. The operator recursion, positive
kernel domination and stationary zero-integral argument are mature
suppliers, already present in [NATIVE]; no new general maximum principle
is claimed. Proposition 4.1 uses the existing singleton mechanism as a
sharpness witness, not a new family of generators.

The primary finite-matrix comparison is Li and Schneider,
*Applications of Perron--Frobenius Theory to Population Dynamics*,
[Theorem 2.1(a)][LS]: positive Perron vectors for an irreducible nonnegative
finite matrix. Their normalized-power convergence in Theorem 2.3 needs
primitivity. Neither finite-dimensional assumption is imposed here;
(2.7) uses the original invariant probability directly.
Leskelä and Vihola, *Conditional convex orders and measurable martingale
couplings*, [Theorems 1.2(i) and 1.3(i)][LV], concern finite-first-moment
vectors and parameterized probability kernels on $\mathbb R^d$.
Bounded complete-word projections meet that integrability condition;
[PAIR, Theorem 20.2] supplies the full-marginal compatibility criterion.
Those coupling results do not supply the one-contact classification.
The present implication is a source-specific deduction, with no global
originality claim.

**Definition 5.2 (unresolved simultaneous feasibility).** The remaining
original question is the existence of one compatible pair with both
midpoint means and every supported complete configuration-loss budget.
The strict inequalities (3.3) are necessary, with no positive uniform
gap asserted. They establish neither $j_c=0$ nor $j_c>0$ for the
unrestricted problem. Analytical existence, finite representation,
original-source installation, data or witness acquisition, training
attainment and generalization remain separate obligations. Neither the
analysis kernels nor the sharpness singleton supply these bridges.

[PAIR]: RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md
[NULL155]: RECURSIVE_RELATIONAL_OBSERVATION_FIXED_FULL_RESIDUAL_NULL.md
[NATIVE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_TAIL_ATOMS_AND_BOREL_RECURRENCE.md
[REV]: RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md
[LS]: https://arxiv.org/html/math/0109008v1
[LV]: https://arxiv.org/html/1404.0999v3

## 追加锚（本行以下为增补区）

## 6. A quantitative bound from one late mean

**Theorem 6.1 (complete configuration-law stability).** Let
$(\Gamma_B,\Gamma_A)$ be any boxed compatible pair of Definitions
1.2--1.3, with its original common unweighted marginals and both full
residual equations. Retain Assumption 1.1. For every integer $n\ge4$ put

$$
\begin{aligned}
d_n&=\int Q(w_{n,1})\,d\nu_p(Q),\\
e_{a,n}&=d_n-c_az_a^n,& e_{b,n}&=c_bz_b^n-d_n,\\
\kappa&=\frac15,&
M_r&=1+z_r+z_r^2+(1+z_r)\lambda+\lambda^2,\\
C_{r,n}&=M_r\kappa^{-n}
             \sum_{j=1}^{n-1}\left(\frac\lambda{z_r}\right)^j,
&M_a&=\frac{3379}{2025},\qquad M_b=\frac{9559}{5625}.
\end{aligned}
\tag{6.1}
$$

Then $e_{r,n}\ge0$ and, for both $r\in\{a,b\}$,

$$
\max_{s\in\{p,\beta\}}
  \int\operatorname{TV}(D,P_{s,r})\,d\nu_s(D)
\le C_{r,n}e_{r,n}.
\tag{6.2}
$$

Here $\operatorname{TV}(D,P)=\frac12\sum_{e\in\Omega_s}|D(e)-P(e)|$
is evaluated on each normalized complete configuration law before
integration, including the noncompletion coordinate. The marginal
supports may be arbitrary Borel sets. There is no finite-support,
recurrence, reversibility, deterministic-successor, irreducibility or
ergodicity assumption. The index $n$ in (6.1) is the word-return index;
the original source parameter $n=4$ in Assumption 1.1 is unchanged.

**Proof.** Work throughout with the original disintegrations $B,A$.
For bounded Borel functions on the respective phase spaces, marginal
transport gives

$$
\int B|f|\,d\nu_p=\int|f|\,d\nu_\beta,\qquad
\int A|h|\,d\nu_\beta=\int|h|\,d\nu_p.
\tag{6.3}
$$

Thus a marginal-null exceptional set is assigned zero conditional mass
at almost every input of the opposite phase. Both kernels act on the
almost-sure quotients, and their positive weighted compositions do too.
The countable complete carriers allow one null set per phase for all
coordinate residual equations and boxes. Iterated identities below
hold in these quotients; a countable union also makes all indices
simultaneous. No conditional version at a null input is used. The
tail bounds of (1.3) imply zero mass at both infinite outcomes by
continuity from above, while retaining those outcomes in the laws.

Reuse (2.2)--(2.4), writing $w=L\mathbf1$ and $q_j(Q)=Q(w_{j,1})$:

$$
\begin{gathered}
P=BA,\qquad Lf=(1-u)B(vAf),\qquad g=(1-u)B(1-v),\\
\nu_pP=\nu_p,\qquad q_j=L^jg,\qquad
c_b\le g\le c_a,\qquad w=1-u-g,\\
\kappa Pf\le Lf\le\lambda Pf\quad(f\ge0).
\end{gathered}
\tag{6.4}
$$

Positivity gives, for every nonnegative bounded $f$ and integer $m\ge0$,

$$
\kappa^mP^mf\le L^mf\le\lambda^mP^mf,
\qquad
\kappa^m\int f\,d\nu_p
\le\int L^mf\,d\nu_p
\le\lambda^m\int f\,d\nu_p.
\tag{6.5}
$$

For the induction, apply $L$ to the preceding inequalities and then
apply its one-step comparison to $P^mf$. Integration uses the original
stationarity $\nu_pP=\nu_p$. No commutation of $L,P$, invariant law for
$L$, or weighting of either marginal is asserted.

Fix $r$, abbreviate $c=c_r,z=z_r,e=e_{r,n}$, and set $\sigma=1$ at
$r=a$ and $\sigma=-1$ at $r=b$. Define

$$
F=\sigma(c-g),\qquad \Phi=\int F\,d\nu_p,\qquad
h=\sigma(q_n-cz^n),\qquad V=\sigma(w-z).
\tag{6.6}
$$

The ratio (2.5) is less than one for $j=0,1,2$ and greater than one
for every $j\ge3$. Hence $F,h\ge0$ and $\int h\,d\nu_p=e$.
Since $n-1\ge3$, the predecessor box and $q_n=Lq_{n-1}$ imply

$$
0\le\sigma(q_n-cz^{n-1}w)=h-cz^{n-1}V,
\qquad V\le\frac{h}{cz^{n-1}}.
\tag{6.7}
$$

Finite telescoping of $L^n\mathbf1-z^n\mathbf1$, followed by (6.7),
now gives

$$
\begin{aligned}
L^nF
 &=c\sum_{j=0}^{n-1}z^{n-1-j}L^jV-h\\
 &\le\sum_{j=1}^{n-1}z^{-j}L^jh.
\end{aligned}
\tag{6.8}
$$

Indeed the $j=0$ term minus $h$ is nonpositive, and positivity of
$L^j$ applies (6.7) to each remaining term. The signed function $V$
is used only in this order comparison. Apply (6.5) to the nonnegative
functions $F,h$, obtaining the source-specific defect estimate

$$
\kappa^n\Phi\le\int L^nF\,d\nu_p
\le\sum_{j=1}^{n-1}\left(\frac\lambda z\right)^j e.
\tag{6.9}
$$

It remains to control TV on every complete coordinate. The endpoint
b-to-a ratios at phase p are $(6/5)(27/25)^j$ on marker zero and
$(81/100)(27/25)^j$ on marker one. At suspension they are $9/10$ on
standalone beta, $(36/25)(27/25)^j$ on prefixed marker zero, and
$(243/250)(27/25)^j$ on prefixed marker one. Thus the complete events
where endpoint a exceeds endpoint b are exactly

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad
E_\beta=\{\beta,\alpha w_{0,1}\}.
\tag{6.10}
$$

Every other finite coordinate has the reverse sign, and both infinite
coordinates have difference zero. Inside the boxes these signs also
fix the signs of the difference from either endpoint. Normalization
then identifies the half-$\ell^1$ distance with the signed event
difference. This uses the whole carrier, not a finite truncation.

Put $x=|u-r|=\sigma(u-r)$ and $y=|v-r|=\sigma(v-r)$. Directly from
the endpoint product in (6.4), both decompositions hold:

$$
F=(1-r)x+(1-u)By
  =(1-r)By+B(1-v)x.
\tag{6.11}
$$

Consequently $F\ge(1-r)x$ and $F\ge(1-r)By$.
For $j=0,1,2$ let $f_j=\sigma(cz^j-q_j)\ge0$, so $f_0=F$.
The p sign computation and (6.4) give

$$
\operatorname{TV}(Q,P_{p,r})=f_0+f_1+f_2,\qquad
f_{j+1}=Lf_j+cz^j(x-F)\quad(j=0,1).
\tag{6.12}
$$

Since $c(x-F)\le zF$ by $F\ge(1-r)x$, it follows that
$f_1\le LF+zF$ and
$f_2\le L^2F+zLF+z^2F$. Integration using (6.5) yields

$$
\int\operatorname{TV}(Q,P_{p,r})\,d\nu_p
\le[1+z+z^2+(1+z)\lambda+\lambda^2]\Phi=M_r\Phi.
\tag{6.13}
$$

At suspension the complete residual equation gives
$W(E_\beta)=1-v+vAg$. By (6.10), its signed difference from
$1-r+rc$ is precisely TV. Therefore

$$
\operatorname{TV}(W,P_{\beta,r})=(1-c)y+vAF.
\tag{6.14}
$$

Transport (6.11) with the same B marginal to get
$\Phi\ge(1-r)\int y\,d\nu_\beta$. The A marginal and $v\le b$ give

$$
\int\operatorname{TV}(W,P_{\beta,r})\,d\nu_\beta
\le\left(\frac{1-c}{1-r}+b\right)\Phi\le M_r\Phi.
\tag{6.15}
$$

The middle coefficient is $37/30$ for a and $22/15$ for b;
$M_r$ minus that coefficient is respectively $1763/4050$ and
$1309/5625$. Equations (6.9), (6.13) and (6.15) prove (6.2).
All nonlinear TV expressions were reduced by their actual coordinate
signs before any integration. In particular no sampled successor was
replaced by a conditional barycentre inside TV, and neither
$\operatorname{TV}(\nu_s,\delta_{P_{s,r}})$ nor TV of an averaged
configuration law appears. $\square$

## 7. The original configuration-risk consumer

**Corollary 7.1 (risk, midpoint and necessary tail corrections).** Use
exactly the functional $\mathcal J$ of [PAIR, (11.9)], equivalently
(3.2), with its supremum over every $k$ with $\mu(k)>0$ and its
configuration-before-integration losses. For every boxed compatible
pair, every $n\ge4$ and $r\in\{a,b\}$,

$$
\mathcal J+C_{r,n}e_{r,n}\ge\rho_p,
\qquad \rho_p=\frac{1116529}{22781250}.
\tag{7.1}
$$

For a compatible pair with $\mathcal J=0$, or for a boxed compatible
pair with the exact p midpoint $\int Q(E_p)\,d\nu_p=C$ of (3.1),

$$
e_{r,n}\ge\delta_{r,n}:=\frac{\rho_p}{C_{r,n}}>0,
\qquad
c_az_a^n+\delta_{a,n}\le d_n\le c_bz_b^n-\delta_{b,n}.
\tag{7.2}
$$

Thus any genuinely compatible completion satisfying either of these
face conditions must increase the retained NULL155 a-tail mean by at
least $\delta_{a,n}$ at every $n\ge5$. This is a necessary minimum
correction bound, with no assertion that the bound is sharp or attained.

**Proof.** Let $r^{\mathrm{opp}}$ be the other endpoint. It is a
supported target because $\mu(1),\mu(2)>0$. The exact definition
[PAIR, (11.9)] and the integrated complete-law triangle inequality give

$$
\begin{aligned}
\mathcal J
 &\ge\int\operatorname{TV}(Q,P_{p,r^{\mathrm{opp}}})\,d\nu_p-\rho_p\\
 &\ge\rho_p-\int\operatorname{TV}(Q,P_{p,r})\,d\nu_p\\
 &\ge\rho_p-C_{r,n}e_{r,n}.
\end{aligned}
\tag{7.3}
$$

Here $\operatorname{TV}(P_{p,a},P_{p,b})=2\rho_p$, as follows
from (6.10) or [PAIR, Section 2]. The supremum in $\mathcal J$ was
bounded below by one supported target, not replaced by the two-endpoint
supremum. In particular every supported nonendpoint loss remains
required in the zero-level assertion.

At $\mathcal J=0$, [PAIR, (11.29)--(11.30)] supplies the full boxes
and both midpoint means, so (7.1) applies. For the separate boxed
p-midpoint hypothesis, the signs in (6.10) give directly

$$
\int\operatorname{TV}(Q,P_{p,a})\,d\nu_p=C+\rho_p-C=\rho_p,
\qquad
\int\operatorname{TV}(Q,P_{p,b})\,d\nu_p=C-(C-\rho_p)=\rho_p.
\tag{7.4}
$$

Apply (6.2) to each equality and substitute the two definitions of
$e_{r,n}$ to obtain (7.2). This second route requires neither the
suspended midpoint nor the supported-target budgets; it does not
assert them.

Both p descriptors in [NULL155, Definition 2.1] have
$Q(w_{n,1})=(4/9)(2/9)^n=c_az_a^n$ for $n\ge5$, so every mixture
of them has that mean. Any proposed completion on the stated face,
even with different support, weights, earlier coordinates and
conditional branching, must instead satisfy
$d_n-c_az_a^n\ge\delta_{a,n}$. The incompatible NULL155 object itself
has unequal full marginals and nonzero omitted residuals
[NULL155, Proposition 5.1]; it is not an input to (6.2) or (7.1).
Changing its tail means by these amounts alone is not sufficient
for compatibility or for any of the other face conditions. $\square$

**Exact substitution 7.2 (word index five).** Ordinary rational
substitution in (6.1) gives

$$
\begin{aligned}
\sum_{j=1}^4(\lambda/z_a)^j&=\frac{4026}{625},&
C_{a,5}&=\frac{4534618}{135},&
\delta_{a,5}&=\frac{1116529}{765216787500},\\
\sum_{j=1}^4(\lambda/z_b)^j&=\frac{34390}{6561},&
C_{b,5}&=\frac{1643670050}{59049},&
\delta_{b,5}&=\frac{90438849}{51364689062500}.
\end{aligned}
\tag{7.5}
$$

Under either face hypothesis of Corollary 7.1, its interval becomes

$$
\frac{128}{531441}+\frac{1116529}{765216787500}
\le d_5\le
\frac{69984}{244140625}-\frac{90438849}{51364689062500}.
\tag{7.6}
$$

These are substitutions into the universal proof, not independent
mathematical claims or evidence for its Borel quantifiers.

## 8. Endpoint, mixture and depth-boundary controls

**Proposition 8.1 (consistency with the supplied controls).** The
native endpoint flows, their diagonal half-native mixture and the
nonnative contact of Proposition 4.1 retain their stated scopes under
Theorem 6.1. In particular the theorem cannot be extended to $n=3$
for both endpoints with any finite coefficient multiplying $e_{r,3}$.

**Proof.** At either native r Dirac pair, $g=c_r$, $L=z_rP$ and
$e_{r,n}=0$; both r losses vanish. These are the complete native laws
and original unit flows in Theorem 2.1, with tails $z_r^j,rz_r^j$.

For the mixture, take the original flows

$$
\begin{aligned}
\Gamma_B&=\tfrac12\delta_{(P_{p,a},P_{\beta,a})}
          +\tfrac12\delta_{(P_{p,b},P_{\beta,b})},\\
\Gamma_A&=\tfrac12\delta_{(P_{\beta,a},P_{p,a})}
          +\tfrac12\delta_{(P_{\beta,b},P_{p,b})}.
\end{aligned}
\tag{8.1}
$$

Each conditional stays at its matching native endpoint, so both full
residual equations and unweighted marginals hold. Its means are both
midpoints, and for $n\ge4$

$$
e_{a,n}=e_{b,n}=\tfrac12(c_bz_b^n-c_az_a^n)>0,
\qquad
\int\operatorname{TV}(D,P_{s,r})\,d\nu_s=\rho_s.
\tag{8.2}
$$

Thus (6.2) applies and (7.2) is consistent. This is a mixture of
original native flows, not a singleton at the barycentric descriptor.
As [PAIR, Corollary 12.3] shows, it has $\mathcal J=0$ when the
supported depths are exactly 1 and 2, whereas any supported depth
$k\ge3$ violates its p budget. The latter loss is still part of (11.9).

For the nonnative singleton of Proposition 4.1, the complete-coordinate
signs in (6.10) and its displayed rational parameters give

$$
e_{b,3}=0,\qquad
\operatorname{TV}(Q,P_{p,b})=\frac{10951371}{190109375}>0,
\qquad
\operatorname{TV}(W,P_{\beta,b})=\frac{33663}{777505}>0.
\tag{8.3}
$$

It is boxed and compatible, but has
$e_{b,4}=486/9765625>0$ and fails both midpoint means. The proposed
extension to index three would have a zero right side and a positive
left side. In the proof of Theorem 6.1 the precise obstruction is the
reversed predecessor order at $j=2$, so (6.7) is unavailable at $n=3$.
The all-coordinate and complete-tail verification remains the one in
Proposition 4.1. These supplied controls do not replace the universal
proof over arbitrary Borel marginals. $\square$

## 9. Quantitative correspondence and limits

**Mathematical citation 9.1 (scope of reuse).** The source-specific
addition is the positive-slack implication (6.9), followed on the same
flows by the full-law estimates (6.13)--(6.15) and the consumer (7.1).
Theorem 2.1 supplies only the zero-slack classification. [NATIVE,
Theorem 3.1] supplies Borel rigidity under an exact eventual recurrence;
[PAIR, Theorem 18.2] additionally assumes finite p support. Neither
recurrence is assumed here. [PAIR, Theorem 20.2] characterizes existence
of full compatible flows for prescribed entire marginals by all finite
convex-order tests; it supplies no positive-slack modulus. The full-word
recursion and stationary positive-kernel comparisons in Section 2 and
[NATIVE, (2.3)--(2.5)] are reused directly. Endpoint TV decomposition,
positivity, marginal transport and finite telescoping are mature tools,
not separate new general theorems. Corollary 7.1 and substitution 7.2
are applications of (6.2), not additional independent mathematical
content.

Proposition 8.1 reuses the supplied endpoint flows, endpoint-tag mixture
and depth-three witness as controls; it introduces no new generator.

The primary comparisons of Citation 5.1 retain their exact boundaries:
[Li--Schneider, Theorem 2.1(a)][LS] assumes a finite irreducible
nonnegative matrix, and its Theorem 2.3 assumes primitivity;
[Leskelä--Vihola, Theorems 1.2(i) and 1.3(i)][LV] concerns
finite-first-moment vectors and measurable families of martingale
couplings. Bounded word projections satisfy the first-moment
condition, but those results supply neither (6.9) on these two
stationary full-law flows nor the all-coordinate TV conversion.
This is a repo-derived ordinary deduction relative to the named
suppliers, with no global originality claim or Lean certification.

The deterministic whole-fiber read/update/address budget classification
in [SERIAL-JOINT] has a different source and operation contract.
The iid unused-suffix and adaptive serial execution results in
[FreshServiceRestart][RESTART] and [RarePriorSerialExecution][SERIAL]
likewise do not supply the boxed Borel positive-slack estimate or a
global COMPLETE/full-transcript/minimax closure. Reusing their local
results would require their own source and operation correspondence.

**Convention 9.2 (unchanged source and unresolved obligations).** One
depth $K$ is still sampled once from the original finite or countable
prior before the first paid Read; no step resamples it. Both seeds,
every supported depth, every positive finite paid rejection, partial
parse and return history, all marker triples, held records, third
write before latch, fourth completion and matching Stop remain in
the source and risk domains. The original renderer of [PAIR, Section
2] retains the complete records and operations and preserves TV.
The operators here supply analytical identities, not a posterior port,
new source operation, exact sampler or paid installation. Acquired
and synthetic updates remain identical, and all original program,
number, control, selector, workspace and persistent-randomness charges
remain part of COMPLETE.

The coefficient $C_{r,n}$ is not optimized. It is finite at each fixed
index and grows with $n$: since $\lambda/z_a=6/5$ and
$\lambda/z_b=10/9$, (6.1) gives $C_{r,n+1}>5C_{r,n}$.
Thus the guaranteed lower corrections $\delta_{r,n}$ tend to zero.
No uniform-depth positive gap follows. The bounds neither evaluate
$j_c$ nor decide simultaneous zero-face feasibility for the original
supported targets. They supply no new actual feasibility, attainment,
finite representation, exact sampling, paid installation or COMPLETE
optimality conclusion. The supported-depth budgets, both midpoint
means, both full residual equations, common source and any operational
realization must still be met together by any proposed solution.

[SERIAL-JOINT]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[RESTART]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart.lean
[SERIAL]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.lean

## 追加锚（本行以下为增补区）
