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
