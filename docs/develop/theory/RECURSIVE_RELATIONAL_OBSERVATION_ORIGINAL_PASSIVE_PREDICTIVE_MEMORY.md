# Original passive words and their exact predictive boundary

## 1. The fixed source and representation questions

**Assumption 1.1 (the original endpoint and passive law).** Fix any
original finite $a,\eta,d>0$. Retain [RRO, Definitions 1.1, 7.1 and
8.1][RRO]: the group $G=H^1\times\mathbb R$, identity $e$, Haar
measure $\mu$, unit-source Green field and original $S_{\min}$, with
the original product

$$
(x,y,z,w)(x',y',z',w')
 =(x+x',y+y',z+z',w+w'+xy').
$$

Retain the entire complex self-adjoint endpoint, including the
normalization of its maximal-domain coefficients:

$$
\begin{gathered}
h=\frac{w_*}{\|w_*\|_{L^2(\mu)}},\qquad
\rho=\frac{A(h)}{C(h)},\qquad
D(H_{\rm end})=\{u\in D(S_{\min}^*):A(u)=\rho C(u)\},\\
H_{\rm end}u=S_{\min}^*u,\qquad
m=h^2\mu,\quad m(G)=1,\qquad J_hv=hv,\\
K=J_h^{-1}H_{\rm end}J_h\ge0,\qquad
\ker K=\mathbb C1,\qquad T_t=e^{-tK},\qquad P=T_d=P^*.
\end{gathered}
\tag{1.1}
$$

The inherited source process starts at $Z_0=e$, is conservative, and
has positive-time densities
$\mathbb P_e(Z_t\in dx)=g_t(x)m(dx)$, with
$g_{t+s}=T_sg_t$, $\int g_t\,dm=1$ and $P1=1$.
Write $g=g_{2d}=Pg_d$. These are the owning endpoint and density
supplies, not conclusions about an arbitrary diffusion.

For every permitted repaired bounded Borel representative $b$ of
$g_d$, use exactly

$$
\begin{gathered}
c=\frac1{4(1+\|g_d\|_\infty)},\qquad [b]=g_d,\qquad
0<b\le1+\|g_d\|_\infty,\\
\mathcal L=\{0,1,3,B\},\qquad
f_3=cb,\qquad f_B=\frac14,\qquad
f_0=f_1=\frac{3/4-f_3}{2},\\
X_j=Z_{(j+2)d},\qquad
\mathbb P(Y_j=y\mid (Z_t)_{t\ge0})=f_y(X_j)\quad(j\ge0).
\end{gathered}
\tag{1.2}
$$

The read noise is fresh and conditionally independent given the source
path, and leaves its evolution unchanged. Thus the lead-in is $2d$,
every subsequent gap is $d$, and all four original outcomes remain.
All pairings below are in the real $L^2(m)$ unless stated otherwise;
function identities are $m$-class identities. The full complex
endpoint in (1.1) is unchanged by using real pairings.

**Definition 1.2 (words, residuals and clock cuts).** For finite words,
including the empty word $\varepsilon$, retain the original recursion
and cylinder law [RRO, (8.4)]:

$$
F_\varepsilon=1,\qquad F_{yv}=f_yPF_v,\qquad
p(w)=\mathbb P_e(Y_0\cdots Y_{|w|-1}=w)=\langle g,F_w\rangle_m,
\qquad p(\varepsilon)=1.
\tag{1.3}
$$

Here $uv$ is chronological concatenation. Define

$$
H_p(u,v)=p(uv),\qquad R_u(v)=\frac{p(uv)}{p(u)},\qquad
\mathcal R_p=\operatorname{span}_{\mathbb R}\{H_p(u,\cdot):u\in\mathcal L^*\}.
\tag{1.4}
$$

Every $p(u)>0$: conditional on each source path its finitely many
specified emissions have a strictly positive product. The algebraic
rank of $H_p$ is the supremum of the ranks of its finite evaluation
blocks. A cut $t$ is after $t$ labels and before $Y_t$, whose physical
read time remains $(t+2)d$. Same-cut blocks restrict all histories
to length $t$. No empirical matrix or bounded Hankel operator is part
of this definition.

**Definition 1.3 (the distinct finite representation requirements).**
An autonomous $r$-dimensional linear realization over
$\mathbb F=\mathbb R$ or $\mathbb C$ consists of fixed vectors and
label matrices with

$$
p(w)=\alpha A_{w_0}\cdots A_{w_{n-1}}\beta
\quad\text{for every }w\in\mathcal L^n\text{ and every }n\ge0.
\tag{1.5}
$$

An $r$-state autonomous HMM is the nonnegative subclass with an
initial probability row, nonnegative label kernels $M_y$, stochastic
sum $\sum_yM_y$, and terminal column $\mathbf1$. Emission followed by
transition is an equivalent convention since the last stochastic
transition acts on $\mathbf1$.

A clock-assisted linear boundary of dimension at most $r$ is allowed
arbitrary time-dependent updates and readouts, but at every cut $t$
its unnormalized future responses must factor as

$$
p(uv)=a_t(u)b_t(v),\qquad
a_t(u)\in\mathbb F^{1\times r_t},\quad
b_t(v)\in\mathbb F^{r_t\times1},\quad r_t\le r,
\quad |u|=t.
\tag{1.6}
$$

The same future column at that cut serves every history. This includes
time-inhomogeneous HMMs with uniformly at most $r$ hidden states and
time-dependent finite linear generators. It even permits the dimension
to vary with the clock subject to the stated bound.

A deterministic exact predictive memory assigns a reached state
$s(u)$, updates it after each observed label, and determines every
$R_u(v)$. An autonomous memory has state-dependent rules; a
clock-assisted memory may additionally use the cut $t$. Its cardinality
is distinct from the dimension of the linear span of responses. A
nonlinear state in $\mathbb R^r$ with unlimited precision is a further,
different requirement. A state stored in at most $b$ bits has at most
$2^b$ possible retained values at a given clock cut.
All history-dependent retained context belongs to the state; only the
supplied clock is exempt in the clock-assisted versions.

The generic linear notions are those of
[WordHankelRealization, `residualSpace`, `MatrixRealization` and
`finite_hankel_realization`][WORD]. The corresponding classical
finite-rank equivalence is [Balle--Panangaden--Precup, Theorem 2][WFA],
for arbitrary functions on finite-alphabet words. Its later
absolute-summability and Hankel-SVD hypotheses are not used here:
$\sum_{|w|=n}p(w)=1$ at every length, so $p$ is not summable over
all finite words. The conditional-history matrix is also the
uncontrolled system-dynamics matrix of [Singh--James--Rudary,
§§2--3][PSR], with observation alphabet $\mathcal L$ and no actions.

## 2. The actual observation-to-residual correspondence

**Theorem 2.1 (reachable source densities and the passive predictive
quotient).** Under Assumption 1.1, put

$$
z_\varepsilon=g,\qquad L_yz=P(f_yz),\qquad z_{uy}=L_yz_u.
\tag{2.1}
$$

Then the $z_u$ are nonnegative bounded $L^2(m)$ classes and

$$
p(uv)=\langle z_u,F_v\rangle_m,\qquad
\int z_u\,dm=p(u),\qquad
R_u(v)=\langle \pi_u,F_v\rangle_m,
\quad\pi_u=\frac{z_u}{p(u)}.
\tag{2.2}
$$

The density $\pi_u$ is the conditional density of the same source
at the next read time $(|u|+2)d$ after the original observed history
$u$. If $\mathcal Z=\operatorname{span}_{\mathbb R}\{z_u\}$ and
$\mathcal O(z)(v)=\langle z,F_v\rangle_m$, then

$$
\mathcal O(\mathcal Z)=\mathcal R_p,\qquad
\mathcal Z/\ker(\mathcal O|_{\mathcal Z})\simeq\mathcal R_p,
\qquad \mathcal O(L_yz)(v)=\mathcal O(z)(yv).
\tag{2.3}
$$

In particular the kernel in (2.3) is invariant under each $L_y$;
the quotient retains exactly the reachable linear future responses.

*Proof.* Multiplication by $f_y$ and the Markov operator preserve
nonnegativity and boundedness. The original Markov/read contract,
self-adjointness, and (1.3) give

$$
\langle L_yz,F_v\rangle_m
 =\langle z,f_yPF_v\rangle_m
 =\langle z,F_{yv}\rangle_m.
\tag{2.4}
$$

Starting from $z_\varepsilon=g$, induction on $u$ proves the first
identity in (2.2); $v=\varepsilon$ gives its mass. More specifically,
for every bounded real test $\phi$, the joint integral for a read $y$
and the next hidden state is $\langle\pi_u f_y,P\phi\rangle_m$.
It equals $\langle P(f_y\pi_u),\phi\rangle_m$. Its normalizing
mass is

$$
a_y(\pi_u)=\int f_y\pi_u\,dm=R_u(y)>0,\qquad
\pi_{uy}=\frac{P(f_y\pi_u)}{a_y(\pi_u)}.
\tag{2.5}
$$

This proves the asserted conditional-density meaning and all future
identities without changing the preparation. Equation (2.4) proves
the intertwining in (2.3); the image and quotient identities follow
by linearity and the first isomorphism theorem. The kernel statement
uses $\mathcal O(z)(yv)=0$ for all $v$ whenever $\mathcal O(z)=0$.
This is the original-source correspondence to the existing residual
and shift constructions [WORD], including their private factorization
helpers; it does not assert injectivity on the hidden Hilbert space.
$\square$

## 3. Explicit visible Gram blocks

**Theorem 3.1 (original one-marker words have unbounded Hankel rank).**
For every integer $N\ge1$ and $0\le i,j<N$, the actual original
word block with rows $B^i$ and columns $B^{j+1}3$ satisfies

$$
\begin{aligned}
C_N(i,j)&=p(B^{i+j+1}3)
 =\frac c4\,4^{-i-j}\langle P^ig,P^jg\rangle_m,\\
C_N&=\frac c4D_NG_ND_N,\qquad
D_N=\operatorname{diag}_{0\le i<N}(4^{-i}),\qquad
G_N(i,j)=\langle P^ig,P^jg\rangle_m,\\
\det C_N&=(c/4)^N4^{-N(N-1)}\det G_N>0.
\end{aligned}
\tag{3.1}
$$

Thus $H_p$ has infinite algebraic rank over both $\mathbb R$ and
$\mathbb C$, and $\mathcal R_p$ has countably infinite algebraic
dimension. The original law admits neither a finite autonomous linear
realization nor a finite autonomous HMM.

*Proof.* The constant original emission gives, for every $n\ge0$,

$$
z_{B^n}=4^{-n}P^ng,\qquad
F_{B^n3}=c4^{-n}P^ng_d,\qquad p(B^n)=4^{-n}.
\tag{3.2}
$$

In particular $F_{B^{j+1}3}=c4^{-(j+1)}P^jg$ because
$Pg_d=g$. Substitution into (2.2) proves (3.1). The one additional
$B$ in the suffix is the precise original-time alignment; no
fractional read epoch is introduced.

Reuse [RRO, Theorem 7.2] or [FIB, Lemma 169.1][FIB]:
$g,Pg,\ldots,P^{N-1}g$ are independent. The usual Gram criterion
therefore makes $G_N$ positive definite. Its hypotheses are a finite
independent family in the real Hilbert space $L^2(m)$; the pinned
Mathlib supplier is `Matrix.posDef_gram_of_linearIndependent` in
[GramMatrix][GRAM]. The diagonal factors in (3.1) are invertible.
Real independence also implies complex independence by separating
real and imaginary coefficients, and these real determinants stay
nonzero over $\mathbb C$.

Every finite linear realization factors each such block into an
$N\times r$ forward matrix and an $r\times N$ future matrix, so
its rank is at most $r$. This is the necessary direction of [WORD]
with field $\mathbb F$, alphabet $\mathcal L$ and word function
$p$; taking $N=r+1$ contradicts (3.1). An HMM is a subclass of these
linear realizations, so no positive-realization converse is needed.
The residual span is generated by the countable set of finite words,
and (3.1) supplies arbitrarily large independent subsets. Its
algebraic dimension is consequently exactly countable infinity.

For the unary [SequenceHankelRealization][SEQ] interface, take
$U=Y=\mathbb R$ and the linear map

$$
\mathfrak m(n)(x)=x\,\frac{4^{n+1}}c p(B^{n+1}3)
                =x\langle g,P^ng\rangle_m.
\tag{3.3}
$$

Its scalar Hankel blocks are $G_N$. Thus its existing
`finite_tailSpace_iff_exists_realization` equivalence has an
infinite-dimensional tail space here. Neither that equivalence nor
the hidden-orbit independence is a new claim of this theorem; the
new interface is their identification with the original words in
(3.1)--(3.3). $\square$

## 4. Same-clock histories, including a common retained suffix

**Theorem 4.1 (unbounded original cut rank even after a common finite
suffix).** Fix any integers $k\ge0$ and $N\ge1$. For $0\le i,j<N$
and $\ell\ge0$, use the actual words

$$
u_i^{(\ell)}=B^{\ell+N-1-i}3B^{i+k},\qquad
v_j=B^{j+k+1}3B^{N-1-j}.
\tag{4.1}
$$

Every history has length $t=\ell+N+k$ and ends in the same $k$
labels $B$; every future has length $N+k+1$. Put
$J_{\ell,N,k}(i,j)=p(u_i^{(\ell)}v_j)$ and
$G_{N,k}(i,j)=\langle P^{i+k}g,P^{j+k}g\rangle_m$. Then

$$
4^\ell J_{\ell,N,k}
 \longrightarrow c^2 4^{-(2N+2k-1)}G_{N,k}
\quad\text{entrywise as }\ell\longrightarrow\infty.
\tag{4.2}
$$

The limit is positive definite. There exists a finite
$\ell_0=\ell_0(a,\eta,d,N,k)$ such that for every
$\ell\ge\ell_0$,

$$
\det J_{\ell,N,k}>0,\qquad
\operatorname{rank}\bigl[R_{u_i^{(\ell)}}(v_j)\bigr]_{i,j<N}=N.
\tag{4.3}
$$

Consequently the original law has no uniformly finite-dimensional
clock-assisted linear boundary, no clock-assisted HMM with a
uniformly finite hidden set, and no uniformly finite-cardinality
deterministic exact predictive memory with a supplied clock. It is
not an order-$k$ observed Markov law for any finite $k$, even with
arbitrary clock-dependent transition rules.

*Proof.* Use $q(w)=\int F_w\,dm$ from [RRO, Definition 8.1] only as
a comparison coefficient. The original word recursion gives the
exact bridge, for every fixed word $w$,

$$
4^\ell p(B^\ell w)=\langle P^\ell g,F_w\rangle_m,
\qquad
\bigl|4^\ell p(B^\ell w)-q(w)\bigr|
 \le\|P^\ell g-1\|_2\longrightarrow0.
\tag{4.4}
$$

Here $0\le F_w\le1$, $m(G)=1$, and the strong limit is precisely
[RRO, (8.9)] with $\int g\,dm=1$. Its supplied hypotheses are
$K\ge0$, self-adjointness and $\ker K=\mathbb C1$; no spectral
gap or uniform convergence rate is needed.

For nonnegative integers $a,s,b$, invariance of $m$, (3.2), and
$F_{wB^b}=4^{-b}F_w$ give

$$
q(B^a3B^s3B^b)
 =c^2 4^{-(a+s+b)}\langle g_d,P^{s+1}g_d\rangle_m.
\tag{4.5}
$$

The terminal identity follows first for $w=\varepsilon$ from
$P1=1$, and then for all $w$ by (1.3). In (4.5), set
$a=N-1-i$, $s=i+j+2k+1$, $b=N-1-j$. Then
$a+s+b=2N+2k-1$ and

$$
\langle g_d,P^{i+j+2k+2}g_d\rangle_m
 =\langle P^{i+k}g,P^{j+k}g\rangle_m.
\tag{4.6}
$$

Equations (4.4)--(4.6) prove (4.2). In the actual word the two
specified $3$ reads occur at indices $\ell+N-1-i$ and
$\ell+N+2k+j+1$, hence at the original physical times
$(\ell+N+1-i)d$ and $(\ell+N+2k+j+3)d$. Their gap is exactly
$(i+j+2k+2)d$, as in (4.6).

The family $P^kg,\ldots,P^{k+N-1}g$ is independent by the same
supplied no-polynomial-relation result (or Lemma 169.1 at source time
$(k+2)d$). Thus $G_{N,k}$ is positive definite. Continuity of the
finite determinant makes $\det(4^\ell J_{\ell,N,k})$ positive for
every sufficiently large finite $\ell$. Since its scaling factor is
$4^{\ell N}>0$, the original determinant is positive as well.
The finite-$\ell$ matrix need not be symmetric; no positive-definiteness
claim is made about it. Dividing row $i$ by the positive
$p(u_i^{(\ell)})$ proves the normalized rank assertion.

At this common cut a boundary satisfying (1.6) factors the displayed
block through $r_t$ coordinates. Choosing $N=r+1$ excludes a uniform
bound $r$. For an inhomogeneous HMM these coordinates are the
unnormalized hidden-state probabilities after the prefix, and the
columns are the future word laws from each state at that same clock.
For a deterministic predictor with $r$ states the rows factor through
$p(u)\mathbf1_{\{s(u)=s\}}$ and the $r$ future profiles at that clock.
Both factorizations obey the same rank bound.

Finally an order-$k$ law at a known clock makes all future profiles
equal for histories with the same last $k$ labels, by iterating its
one-step rule. The histories in (4.1) share that suffix. Taking $N=2$
in (4.3) contradicts equality of their future profiles. $\square$

## 5. The economical exact boundary and its resource scope

**Theorem 5.1 (the original predictive quotient and representation
separations).** For this fixed original law, identify histories by
$u\sim u'$ exactly when $R_u=R_{u'}$ on all finite future words.
The coarsest reached autonomous deterministic predictive boundary is

$$
\mathcal B_p=\{R_u:u\in\mathcal L^*\},\qquad
\text{initial state }R_\varepsilon,\qquad
\operatorname{out}_y(R)=R(y),\qquad
U_y(R)(v)=\frac{R(yv)}{R(y)}.
\tag{5.1}
$$

It has exactly countably infinitely many reached states. Every exact
autonomous deterministic sufficient statistic maps uniquely on its
reached image onto this boundary. The normalized filter (2.5) realizes
it through $\pi_u\mapsto(v\mapsto\langle\pi_u,F_v\rangle_m)$.
Even with a supplied clock, the number and the linear span dimension
of reached conditional future profiles are eventually at least $N$
for every fixed finite $N$.

This excludes exact all-word prediction with any fixed bit bound, but
does not exclude a one-real nonlinear encoding with unlimited
precision. For every fixed finite horizon there is a finite exact
history-table representation of the same law. If an autonomous linear
model matches all original words through horizon $H\ge2$, its
dimension is at least $\lfloor H/2\rfloor$.

*Proof.* Positivity and cylinder consistency of the original law give
$\sum_yR(y)=1$, and direct cancellation gives
$R_{uy}(v)=R_u(yv)/R_u(y)$. Thus (5.1) is well defined on reached
profiles. The product of its successive readouts along any word $w$
telescopes to $p(w)$. The source filter supplies the same profiles
by Theorem 2.1. The factorization and uniqueness are the existing
predictive-sufficiency universal property [MIN], with
$\mathrm{Past}=\mathcal L^*$ and
$\mathrm{futureLaw}(u)=R_u$; equality of cylinder coordinates is
equality of the entire future measure on the finite-alphabet sequence
space. The positive-symbol update is the specialization of [UPDATE].
These generic quotient properties are reused here.

There are countably many finite words. For each $N$, dividing row
$i$ in (3.1) by $p(B^i)=4^{-i}$ preserves independence. Hence the
profiles $R_{B^i}$ are infinitely many distinct reached states, proving
the cardinality claim. Similarly (4.3) supplies $N$ independent
normalized profiles at every cut $t\ge\ell_0+N+k$. It supplies
neither an effective threshold nor their exact growth with $t$.
The equality $f_0=f_1$ also gives $R_{u0}=R_{u1}$ from (2.5), so
the quotient already discards genuine redundant history while
retaining the infinite family just exhibited.

For the nonlinear distinction, assign digits
$\delta(0)=1$, $\delta(1)=2$, $\delta(3)=3$, $\delta(B)=4$ and
code each finite history by

$$
x_\varepsilon=1,\qquad x_{uy}=5x_u+\delta(y).
\tag{5.2}
$$

Its base-five representation is a leading sentinel $1$ followed by
the nonzero history digits, so it is injective. On the countable
reached subset of $\mathbb R$, use update (5.2) and readout
$R_{\operatorname{decode}(x)}(y)$. These are Borel maps on that
subset and reproduce all original words by the same telescoping
identity. The readout uses the exact source-defined law and an
unrestricted lookup; no finite description, evaluation algorithm,
finite precision or bounded storage is asserted. Infinite linear
rank therefore does not supply a nonlinear real-coordinate lower
bound beyond excluding a single constant state.

For a horizon $H$, retain the finite prefix tree through depth $H$
and use $R_u(y)$ for $|u|<H$. It reproduces precisely the required
cylinders, with exact real probability entries rather than a promised
finite-precision table, and no assertion about later predictions. Conversely the
block (3.1) uses only words of length at most $2N$; choose
$N=\lfloor H/2\rfloor$ to obtain the finite-horizon linear lower
bound. This is a bound for exact coefficient equality, not for
estimated coefficients or approximation. $\square$

**Definition 5.2 (recovery and unresolved quantitative conditions).**
For the fixed mathematical source, the complete word law determines
all reached profiles by (1.4); the boundary (5.1), its initial state,
updates and readouts recover the complete word law by the proof of
Theorem 5.1. Equation (2.3) identifies this operational boundary's
linear span with a quotient of reachable source densities. It does
not invert that quotient to a hidden point, $G$, $H_{\rm end}$,
$h$, $\rho$ or $d$. Such a spatial, endpoint or clock inverse needs
a separately proved identifiability correspondence for those objects.
The original space and boundary enter the displayed memory through
$P$ and $g$; chronological continuation enters through label append
and their indexed heat moments.

All words in (3.1) and (4.1) are unconditional cylinder coordinates
of the original four-outcome law. They require no reset, selected
outcome, extra label, hidden-coordinate probe or stationary preparation.
The invariant comparison in (4.4) is joined to actual $e$-start words
by that exact identity and its proved limit. Cylinder coordinates,
rare histories, $c$, Gram entries and exact future laws are not new
observation or evaluation ports for the actual observer. In particular
the existence of $\ell_0$ does not provide its numerical value or a
way to force the witnessing histories.

No determinant margin, parameter-uniform bound, finite-data rank
certificate, sampling lower bound, error tolerance or stopping rule
is implied. Exact infinite rank is compatible with finite-horizon
approximation; the latter needs its own error and access assumptions.
[RRO, §§8--9] retains its fixed-word acquisition and conditional
quantitative bounds. Those do not evaluate all reached profiles with
uniform finite resources. Recovery of space, time, boundary and
usable memory under such resources remains an additional problem.

**Definition 5.3 (supplier scopes).** The source-specific deductions
(2.2)--(4.6) and their consequences are `repo-derived` ordinary
mathematics under Assumption 1.1. The thermal independence of [RRO,
Theorems 7.2--7.3] and [FIB, Lemma 169.1], the marked-word identity
[RRO, Theorem 8.2], generic Gram positivity, finite linear realization
equivalences [WORD, SEQ, WFA], and predictive quotient/update properties
[MIN, UPDATE, PSR] are reused suppliers. The rotation-odd kernel of
[FIB, §170] concerns its specified linear successor stack; it is not
used as a theorem about the whole passive-word law. [FIB, §171]
concerns compensation and residual approximation, not all-word
equality. None of these mathematical source correspondences asserts
physical acquisition or literature priority for the displayed application.

[RRO]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md
[FIB]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_IV.md
[WORD]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/D5/S3/Observer/Hankel/WordHankelRealization.lean
[SEQ]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/D5/S3/Observer/Hankel/SequenceHankelRealization.lean
[MIN]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality.lean
[UPDATE]: https://github.com/the-omega-institute/trureturing/blob/02054502fd2c15d3046b26c38182b80a75c8b558/D5/S3/ObserverMemory/ContextUpdates/PredictiveStateUnifilarUpdate.lean
[GRAM]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean
[WFA]: https://arxiv.org/html/1501.06841v3
[PSR]: https://arxiv.org/pdf/1207.4167

## 追加锚（本行以下为增补区）

## 6. First actual B-blocks and simultaneous moving-cut prediction

**Definition 6.1 (one original source and the stopped window).** Retain
Assumption 1.1 in its entirety, for every finite $a,\eta,d>0$ and every
permitted Borel repair. In particular retain $G=H^1\times\mathbb R$,
the normalized $h$, the complete complex non-Friedrichs endpoint
$A=\rho C$ distinct from $C=0$, the operator and form domains and source
trace, and the conservative original process from $e$. Its first read
is at $2d$, subsequent gaps are $d$, and its only emissions remain
$0,1,3,B$ with fresh conditionally independent noise. No operation on
the source is added. Write $\mathscr F_t=\sigma(Y_0,\ldots,Y_{t-1})$.
A cut $t$ is after $t$ labels; the next read is still at $(t+2)d$.

Use $P=T_d$, $g=g_{2d}=Pg_d$ and the original $F_u,p(u)$ of (1.3).
The stationary mathematical comparison has the same transition and
read kernels, with coefficients

$$
 q(u)=\int F_u\,dm,\qquad q(\varepsilon)=1,\qquad
 Q_w^H(v)=\frac{q(wv)}{q(w)}\quad(|v|=H).
 \tag{6.1}
$$

It is [OWGR, Definition 15.1]'s comparison law, not an available
stationary preparation. All $q(u)$ and $p(u)$ are positive by the
original strictly positive finite emission products. Both coefficient
families are consistent under summing extensions.

Fix deterministic integers $S\ge0$, $H\ge1$, $r\ge1$, $L\ge1$.
For $k\ge1$ define

$$
 \begin{aligned}
 U_k&=S+(k-1)L,\\
 C_k&=\{Y_{U_k}\cdots Y_{U_k+L-1}=B^L\},\\
 J&=\inf\{k\ge1:C_k\},\qquad T=S+LJ,\\
 W_j&=Y_T\cdots Y_{T+j-1}\quad(0\le j\le r),\qquad W_0=\varepsilon.
 \end{aligned}
 \tag{6.2}
$$

For any actual cut, the target vector is

$$
 {\bf R}_t^H(v)=R_{Y_{<t}}(v)
   =\frac{p(Y_{<t}v)}{p(Y_{<t})}\quad(|v|=H),\qquad
 Y_{<t}=Y_0\cdots Y_{t-1}.
 \tag{6.3}
$$

At $T+j$ this conditions on the entire prefix through that cut,
including every actual label in $W_j$. The gate and its index are
determined by that prefix. They supply no extra future conditioning.

**Lemma 6.2 (the original word square).** Put $N=H+r$, let
$z^{\mathsf R}$ denote word reversal, and set

$$
 \begin{aligned}
 h_z&=P^L(F_z-q(z)),\\
 A_N(L)&=\frac12\sum_{|z|=N}\|h_z\|_2\\
 &=\frac12\sum_{|z|=N}
 \sqrt{\,4^{2L-1}q(z^{\mathsf R}B^{2L-1}z)-q(z)^2\,}.
 \end{aligned}
 \tag{6.4}
$$

Every radicand is nonnegative. With the full-source defect
$\Theta(\lambda)=(1-d_\lambda)/d_\lambda$ of [DPCR, Definition 9.1],

$$
 A_N(L)\le\frac{4^N}{2}
       \sqrt{\Theta\!\left(\frac1{2Ld}\right)}.
 \tag{6.5}
$$

*Proof.* Self-adjointness of $P$ and the original constant $f_B=1/4$
give, for every integer $b\ge0$,

$$
 q(z^{\mathsf R}B^bz)=4^{-b}\langle F_z,P^{b+1}F_z\rangle_m.
 \tag{6.6}
$$

Indeed, write the cylinder integral as successive multiplication by
$f_y$ and application of $P$. Moving the factors of the reversed left
word across the pairing leaves $F_z$ on the left; the $b$ constant
multipliers leave $P^{b+1}$ between the two copies of $F_z$.
For $b=2L-1$, conservation and $\int F_z\,dm=q(z)$ give

$$
 \|h_z\|_2^2
 =\langle F_z-q(z),P^{2L}(F_z-q(z))\rangle_m
 =4^{2L-1}q(z^{\mathsf R}B^{2L-1}z)-q(z)^2.
 \tag{6.7}
$$

Since $0\le F_z\le1$, the centered function has sup norm at most one.
Apply the supplied centered heat estimate [DPCR, Theorem 9.2] at
$s=2Ld$ to (6.7), then sum over the $4^N$ words. This uses the
full original endpoint defect, with neither a spectral gap nor an
effective uniform rate. $\square$

**Lemma 6.3 (the stopped gate in the actual law).** For any
$M\ge\|g_d\|_\infty$ and any integer $N\ge1$,

$$
 \mathbb E_e\operatorname{TV}({\bf R}_T^N,q|_{\mathcal L^N})
 \le\sqrt M\,A_N(L).
 \tag{6.8}
$$

Here $A_N(L)$ is (6.4) with that $N$, and $S$ is any deterministic
nonnegative cut.

*Proof.* Put $b_L=4^{-L}$ and $E_{k-1}=\bigcap_{i<k}C_i^c$.
A prefix $u$ of length $U_k$ satisfying $E_{k-1}$ has, after the
successful block, precisely the actual posterior

$$
 \pi_{uB^L}=P^L\pi_u,\qquad
 p(uB^L)=b_Lp(u),\qquad
 {\bf R}_{U_k+L}^N(z)-q(z)=\langle\pi_u,h_z\rangle_m,
 \tag{6.9}
$$

by (2.5). Thus $|\langle\pi_u,h_z\rangle|
\le\langle\pi_u,|h_z|\rangle$. Theorem 2.1 identifies $\pi_u$ as
the conditional density of $X_{U_k}=Z_{(U_k+2)d}$ given $u$.
Summing the last inequality over all such prefixes, and then over
the mutually disjoint gate events $\{J=k\}$, bounds the expectation
in (6.8) by

$$
 \frac12\sum_{|z|=N}\sum_{k\ge1}
 b_L\,\mathbb E_e[
       \mathbf1_{E_{k-1}}|h_z(X_{U_k})|].
 \tag{6.10}
$$

Conditional on the entire hidden path, the disjoint blocks have
independent all-$B$ indicators of constant probability $b_L$.
Consequently $E_{k-1}$ has conditional probability
$(1-b_L)^{k-1}$, independent of that path, and (6.10) equals

$$
 \frac12\sum_{|z|=N}\sum_{k\ge1}
 b_L(1-b_L)^{k-1}
 \langle g_{(U_k+2)d},|h_z|\rangle_m.
 \tag{6.11}
$$

The actual, unconditioned density at this read epoch satisfies

$$
 \int g_{(U_k+2)d}\,dm=1,\qquad
 \|g_{(U_k+2)d}\|_\infty\le\|g_d\|_\infty\le M,\qquad
 \|g_{(U_k+2)d}\|_2\le\sqrt M.
 \tag{6.12}
$$

These follow by the original propagation and Markov contraction.
Cauchy--Schwarz bounds each pairing in (6.11) by
$\sqrt M\|h_z\|_2$. The geometric weights sum to one, proving (6.8).
This argument averages the full actual posteriors. It never replaces
them by stationary posteriors, bounds each history's posterior
density by $M$, or conditions the result on a chosen $J$. $\square$

**Lemma 6.4 (consuming the actual suffix).** For strictly positive
joint probability vectors $a(w,v),b(w,v)$, with marginals $a_w,b_w$,

$$
 \sum_w a_w\operatorname{TV}(a(\cdot\mid w),b(\cdot\mid w))
 \le\operatorname{TV}(a,b)+\operatorname{TV}(a_w,b_w)
 \le2\operatorname{TV}(a,b).
 \tag{6.13}
$$

*Proof.* For each coordinate,
$|a(w,v)-a_wb(w,v)/b_w|
\le|a(w,v)-b(w,v)|+|b_w-a_w|b(w,v)/b_w$.
Sum over $v,w$ and divide by two. Marginalization contracts TV,
giving the second inequality. The bound has no inverse minimum
marginal: rare suffixes are weighted by their actual probability.
$\square$

**Theorem 6.5 (simultaneous full-history prediction in the stopped
window).** For every source in Definition 6.1, every deterministic
$S,H,r,L$ as there, every $\epsilon>0$, and $M\ge\|g_d\|_\infty$,

$$
 \begin{aligned}
 &\mathbb P_e\left\{
   \max_{0\le j\le r}
   \operatorname{TV}({\bf R}_{T+j}^H,Q_{W_j}^H)>\epsilon\right\}\\
 &\quad\le
 \min\left\{1,\frac{2(r+1)\sqrt M\,A_{H+r}(L)}{\epsilon}\right\}\\
 &\quad\le
 \min\left\{1,
 \frac{(r+1)4^{H+r}\sqrt{M\Theta(1/(2Ld))}}{\epsilon}\right\}.
 \end{aligned}
 \tag{6.14}
$$

The event is unconditional in the original law. The same numerical
bound holds for each deterministic $S$, without asserting one event
simultaneously over all $S$. It is simultaneous for all $r+1$ cuts and
therefore covers any causal selection among them. It is not a
history-by-history, gate-value-conditional, or selected-branch
conditional guarantee.

*Proof.* Fix any stopped history $u=Y_{<T}$. For $j\le r$ apply
(6.13) to

$$
 a(w,v)=R_u(wv),\qquad b(w,v)=q(wv),\qquad |w|=j,\quad |v|=H.
 \tag{6.15}
$$

Conditioning $a$ on its actual $w$ gives exactly $R_{uw}(v)$,
the full-history target at $T+j$. The comparison conditional is
exactly $Q_w^H(v)$. The two joint vectors are marginals of the
length-$N=H+r$ vectors, so their TV is at most
$e_N(u)=\operatorname{TV}(R_u|_{\mathcal L^N},q|_{\mathcal L^N})$.
It follows that

$$
 \mathbb E_e[
 \operatorname{TV}({\bf R}_{T+j}^H,Q_{W_j}^H)\mid\mathscr F_T]
 \le2e_N(Y_{<T})\qquad(0\le j\le r).
 \tag{6.16}
$$

For $j=0$ even the factor one suffices. Taking expectations in
(6.16), using (6.8), and bounding the maximum by the sum gives

$$
 \mathbb E_e\max_{0\le j\le r}
 \operatorname{TV}({\bf R}_{T+j}^H,Q_{W_j}^H)
 \le2(r+1)\sqrt M\,A_N(L).
 \tag{6.17}
$$

Markov's inequality proves the first bound in (6.14); (6.5) proves
the second. Every conditioning in (6.15)--(6.16) is under the same
actual law, and includes the labels actually consumed after $T$.
$\square$

**Proposition 6.6 (the exact disjoint-block waiting law).** For the
deterministic $S,L$ of Definition 6.1, $T<\infty$ almost surely and

$$
 \begin{gathered}
 \mathbb P_e(T-S>kL)=(1-4^{-L})^k\quad(k\ge0),\\
 \mathbb P_e(J=k)=(1-4^{-L})^{k-1}4^{-L}\quad(k\ge1),\qquad
 \mathbb E_e(T-S)=L4^L.
 \end{gathered}
 \tag{6.18}
$$

*Proof.* Conditional on the hidden path the block indicators are
independent Bernoulli variables with constant parameter $4^{-L}$,
so they have that same joint law unconditionally. The geometric
tail and expectation give (6.18). Positivity of the tail at every
finite $k$ excludes a finite worst-case Read bound. The formula
does not assert the same conditional waiting law after a
data-selected calibration, $S$, or $L$. $\square$

## 7. Acquired rational rows and a computable dynamic certificate

**Definition 7.1 (the finite original-word packet).** Write
$\tau=a^2d/\eta$ only in the analysis; its value and the original
$a,\eta,d$ are not supplied as exact names. Use the earned positive
rational lower clock bound $l=\tau_-\le\tau$ of [SRO, Theorems 21.2--22.1]
and the total, paid fixed-reference computation there. Denote its
defect by

$$
 D_v(l)=d^{\mathrm{ref}}_{1/(vl)}.
 \tag{7.1}
$$

The exact full-domain source scaling gives
$d^{\mathrm{orig}}_{1/(vd)}=D_v(\tau)$. Its retained properties
[SRO, (SRO.150)--(SRO.151)] are

$$
 0<D_v(l)<1,\qquad l\le\tau\Longrightarrow D_v(l)\le D_v(\tau),
 \qquad D_v(l)\longrightarrow1\quad(v\longrightarrow\infty).
 \tag{7.2}
$$

These are mathematical/reference computations, not specimen actions.

For $N=H+r$, choose deterministic $n\ge1$ and rational $t,\beta>0$,
and compute rational lower enclosures

$$
 0<D_0^-\le D_4(l),\qquad 0<D_n^-\le D_n(l),\qquad
 V_{n,N}^+=\frac{2N-1}{4n}
                   +2\frac{1-D_n^-}{D_n^-}.
 \tag{7.3}
$$

Require the rational input test

$$
 4^{2N}V_{n,N}^+\le4\beta^2t^2D_0^-.
 \tag{7.4}
$$

Use all actual length-$N$ original-word counters from [DPCR,
Definition 9.3], with $n$ overlapping windows. They use exactly
$n+N-1$ labels, $Y_0$ through $Y_{n+N-2}$, ending at
$(n+N)d$. Put

$$
 a(x)=\sum_{\substack{|z|=N\\z\text{ starts with }x}}
       \frac{A_{n,N}(z)}n\quad(|x|\le N),\qquad a(\varepsilon)=1.
 \tag{7.5}
$$

All $a(x)$ are rational and consistent prefix marginals of one
probability vector. They are calculated from the retained original
initial record; a later suffix is never reinterpreted as a fresh
$e$-start.

**Lemma 7.2 (the existing sampler on one simultaneous event).**
For a valid deterministic branch $l\le\tau$, the packet in
Definition 7.1 has an event $\mathcal E$ satisfying

$$
 \begin{gathered}
 \mathbb P_e(\mathcal E)\ge1-\beta,\qquad
 \mathcal E=\{\operatorname{TV}(a|_{\mathcal L^N},q|_{\mathcal L^N})
                    \le t\},\\
 \mathcal E\Longrightarrow
 |a(x)-q(x)|\le t\quad(|x|\le N),\qquad |a(3)-c|\le t.
 \end{gathered}
 \tag{7.6}
$$

*Proof.* This is the original nonstationary-start bound [DPCR,
Theorem 9.4, (9.13)] at word length $N$ and window count $n$.
The upper bound (7.3) dominates its variance envelope and $D_0^-$
is a valid lower bound for $d^{\mathrm{orig}}_{1/(4d)}$ by
(7.2). Its failure bound is at most

$$
 \frac{4^N}{2t}\sqrt{\frac{V_{n,N}^+}{D_0^-}}\le\beta
 \tag{7.7}
$$

by (7.4). Every prefix event is an event of the same length-$N$
vector, so its probability error is at most TV, simultaneously.
Finally $q(3)=\int cg_d\,dm=c$. This uses the existing dependent,
overlapping-window estimate, not independent samples or the
transient raw frequency as a new exact law. $\square$

**Proposition 7.3 (generated normalization and row-TV errors).**
Let $\mathcal W_r=\bigcup_{j=0}^r\mathcal L^j$, and define

$$
 \ell_x=\max\{0,a(x)-t\},\qquad u_x=\min\{1,a(x)+t\}
 \quad(x\ne\varepsilon),\qquad
 \ell_\varepsilon=u_\varepsilon=1.
 \tag{7.8}
$$

Check $\ell_w>0$ for every $w\in\mathcal W_r$. When these guards
pass, form the rational probability rows

$$
 \widehat Q_w^H(v)=\frac{a(wv)}{a(w)}\quad(|v|=H),\qquad
 I_{w,v}=\left[\frac{\ell_{wv}}{u_w},
                       \frac{u_{wv}}{\ell_w}\right].
 \tag{7.9}
$$

No guard on a numerator is needed. Generate the rational error

$$
 \zeta_w^{\mathrm{gen}}
 =\frac12\sum_{|v|=H}
 \max\left\{\left|\widehat Q_w^H(v)-\frac{\ell_{wv}}{u_w}\right|,
             \left|\widehat Q_w^H(v)-\frac{u_{wv}}{\ell_w}\right|\right\},
 \qquad \zeta^{\mathrm{gen}}=\max_{w\in\mathcal W_r}
                         \zeta_w^{\mathrm{gen}}.
 \tag{7.10}
$$

On the single event $\mathcal E$ of (7.6), these rows satisfy

$$
 \operatorname{TV}(Q_w^H,\widehat Q_w^H)
 \le\zeta_w^{\mathrm{gen}}\quad(w\in\mathcal W_r).
 \tag{7.11}
$$

For fixed finite $H,r$ and a refining sequence of these packets
with $t_s\to0$, all the guards and any prescribed rational
$\zeta^{\mathrm{gen}}\le\zeta$ with $\zeta>0$ eventually pass on
their common event.

*Proof.* Prefix consistency gives
$\sum_{|v|=H}a(wv)=a(w)>0$ and nonnegative entries, so each row in
(7.9) is exactly a rational probability row. In particular the
normalization uses the acquired marginal, not a rounded or
inconsistently fitted denominator. On $\mathcal E$, both true
coefficients lie in (7.8), so $Q_w^H(v)\in I_{w,v}$; summing the
endpoint bounds gives (7.11). For the final claim, (7.6) implies
$a_s(x)\to q(x)$ on the common event. Every one of the finitely
many $q(w)$ is strictly positive. Thus their lower bounds are
eventually positive, both endpoints of every $I_{w,v}$ converge
to $Q_w^H(v)$, and $\widehat Q_w^H(v)$ has the same limit.
The finite sum and maximum in (7.10) tend to zero. $\square$

**Proposition 7.4 (an earned rational dynamic guard).** For a fixed
deterministic branch, let positive rationals $c_-,l$ satisfy
$c_-\le c$, $l\le\tau$, and set $M_0=1/(4c_-)$. For an integer $L\ge1$
compute a rational enclosure

$$
 0<D_L^-\le D_{2L}(l)
        =d^{\mathrm{ref}}_{1/(2Ll)}.
 \tag{7.12}
$$

For positive rational $\epsilon,\delta_0$, the wholly rational
test

$$
 M_0\frac{1-D_L^-}{D_L^-}
 <\left[\frac{\epsilon\delta_0}
                    {(r+1)4^{H+r}}\right]^2
 \tag{7.13}
$$

implies that the second failure bound in (6.14) is at most
$\delta_0$. For every fixed positive $c_-,l,H,r,\epsilon,\delta_0$
the reference computation finds finite $L$ and precision for which
(7.12)--(7.13) pass.

*Proof.* The original exact calibration gives

$$
 \|g_d\|_\infty=\frac1{4c}-1\le M_0,\qquad
 \Theta(1/(2Ld))\le\frac{1-D_L^-}{D_L^-}.
 \tag{7.14}
$$

The second inequality follows from the original-domain scaling
and (7.2), since $(1-x)/x$ decreases for $x>0$. Substitution in
(6.14) proves sufficiency. For termination, $D_{2L}(l)\to1$;
the reference algorithm supplies arbitrarily close lower
enclosures. Enumerating $L$ and refining the enclosures therefore
crosses the strictly positive right side of (7.13) at finite
values. Each reference call and rational test is finite; fair
finite-precision interleaving avoids an unresolved equality
blocking the search. This proves finite success, without a
numerical name of an original parameter or an exact-law query.
$\square$

## 8. Selection, finite stopping and the actual execution boundary

**Theorem 8.1 (common-event composition, including selected starts).**
Predeclare an effectively enumerated countable family of deterministic
candidate descriptions $\kappa$. Each description specifies rational branch bounds
$l_\kappa,c_\kappa>0$, integers $S_\kappa,H_\kappa,r_\kappa$ in
the ranges of Definition 6.1, positive rational tolerances
$\epsilon_\kappa,\zeta_\kappa$, and an allowance $\delta_\kappa>0$.
Generate $L_\kappa$ from (7.12)--(7.13) with these deterministic
values and $\delta_0=\delta_\kappa$. Require
$\sum_\kappa\delta_\kappa\le\delta$.

Use predeclared acquisition/refinement packets, including startup,
whose common validity event $\mathcal A_\tau$ has probability
at least $1-\alpha$. On it, every selected description has
$l_\kappa\le\tau$, $c_\kappa\le c$ certified by its acquired
outputs, and its rows pass Proposition 7.3 with
$\zeta^{\mathrm{gen}}\le\zeta_\kappa$. Packets for the branch
$l_\kappa$ have deterministic inputs and summable allowances as
in [SRO, Theorem 22.1]. Then one original-law event of probability
at least $1-\alpha-\delta$ covers all selected descriptions and,
within each, all their actual cuts:

$$
 \operatorname{TV}({\bf R}_{T_\kappa+j}^{H_\kappa},
                  \widehat Q_{W_{\kappa,j}}^{H_\kappa})
 \le\epsilon_\kappa+\zeta_\kappa
 \qquad(0\le j\le r_\kappa).
 \tag{8.1}
$$

Selection may use the acquired record, and may include the start cut
or tolerances, provided it is from this predeclared family with its
generated lengths and common budgets. It does not require statistical
independence between calibration, acquisition and the gates.

*Proof.* Fix the true source for the proof, without supplying its
parameters to the program. For every deterministic candidate satisfying
$l_\kappa\le\tau$ and $c_\kappa\le c$, Proposition 7.4 and Theorem 6.5
give an unconditional event $\mathcal D_\kappa$ on which all its
dynamic errors are at most $\epsilon_\kappa$, with failure at most
$\delta_\kappa$. Form on this same record

$$
 \mathcal G_\tau=\mathcal A_\tau\cap
  \bigcap_{\kappa:\ l_\kappa\le\tau,\ c_\kappa\le c}
                      \mathcal D_\kappa.
 \qquad
 \mathbb P_e(\mathcal G_\tau)\ge1-\alpha-\delta.
 \tag{8.2}
$$

The union bound needs only deterministic candidate events. Invalid
branches are absent from the intersection. On $\mathcal A_\tau$
every actually selected branch is valid, so on $\mathcal G_\tau$
its dynamic error and its row error (7.11) hold together.
Their triangle inequality proves (8.1). The maximum over cuts
already covers any causal choice of $j$.

This constructs a common event before selection. Conditioning (6.14)
on the observed branch, or simply substituting a random $S,L$ into it,
would not be this argument. If an arbitrary finite-precision start
or tolerance is to be selected, enumerate its possible integer or
rational values in the candidate family and allocate its allowance
there. Unselected descriptions need not be computed. No conclusion
here bounds failure conditional on each selected history, calibration
output, or gate value. $\square$

**Theorem 8.2 (finite successful certification with the existing
suppliers).** Fix a deterministic $S$, finite $H,r\ge1$, rational
$\epsilon,\zeta>0$, and rational $\alpha,\delta>0$ with
$\alpha+\delta<1$. In the paid retained-record and finite-computation
setting of [SRO, Definition 21.1], the original earned startup,
reference defect and finite-word suppliers suffice for a finite
successful certificate as in (8.1), on an event of probability at
least $1-\alpha-\delta$. The certificate includes a generated finite
$L$, every rational row (7.9), all positive normalization guards,
the row error (7.10), the dynamic test (7.13), and all $r$ actual
labels after the reached gate. No exact original parameter or
stationary-law oracle is input.

*Proof.* Split $\alpha=\alpha_{\rm st}+\alpha_{\rm acq}$ positively.
Run [SRO, Theorem 21.2]'s startup. Its possible returned positive
clock bounds $l_i$, $i\ge1$, form a deterministic list. For every
branch $i$, predeclare packets of Definition 7.1 at the fixed
$N=H+r$, with $t_s=2^{-s}$ and allowances
$\beta_{i,s}=\alpha_{\rm acq}2^{-i-s}$, $i,s\ge1$.
Choose $D_{0,i}^->0$ below $D_4(l_i)$ once. The other reference
names and (7.2) allow deterministic increasing $n_{i,s}$ and
refined $D_{n_{i,s}}^-$ satisfying (7.4). Indeed both terms of
$V_{n,N}^+$ tend to zero as $n$ and reference precision grow.
Each search terminates with any prescribed lower bound on $n$.
This is the same packet-generation argument as [SRO,
(SRO.152)], now using the existing unmarked word-vector bound.

Intersect startup's common validity/termination event with every
packet event in the deterministic branches for which $l_i\le\tau$.
The probability is at least $1-\alpha$. Execute only the selected
branch. On this event its packet marginals converge to $q$ by
(7.6), and $a_s(3)-t_s\to c>0$. Proposition 7.3 therefore gives
a finite stage with every normalization guard positive and
$\zeta^{\mathrm{gen}}\le\zeta$. Stop the packet search at its
first such stage with $a_s(3)-t_s>0$. Choose a dyadic
$c_m=2^{-m}$, $m\ge1$, with $c_m\le a_s(3)-t_s$ by a finite
integer search. This is an earned $c_-=c_m>0$ on the same event.

For every deterministic pair $(i,m)$, predeclare
$\delta_{i,m}=\delta2^{-i-m}$. Generate $L_{i,m}$ and its reference
enclosure using Proposition 7.4 with $l_i,c_m,\epsilon,\delta_{i,m}$.
This terminates for every positive rational branch input.
Theorem 8.1 applies to these candidates, with the fixed $S,H,r$
and tolerances and the total dynamic allowance at most $\delta$.
Thus the data selection of $(i,m)$ does not consume an unbudgeted
conditional use of (6.14).

For the selected finite $L$, scan the retained original labels from
$S$ in the prescribed disjoint blocks, extending the same record
as needed. Proposition 6.6 makes its gate finite almost surely.
The countable collection of candidate gates is simultaneously finite
on a probability-one event, so selecting a candidate does not change
this finiteness statement. Obtain and retain every next label through
cut $T+r$ without discarding any intervening labels. Only finitely
many reached finite computations and reads are needed on the common
event. All strict guards above have positive slack eventually,
so this is finite successful certification, not just a limiting
statistical assertion.

The certificate can finish after a tested prefix or even after the
forecast cuts: the retained original record is used throughout.
Actual completion includes every intervening read and its storage.
No assertion that computation finishes by $T$ or catches up during
$[T,T+r]$ is used in the finite-stopping proof. $\square$

**Definition 8.3 (the complete paid bill).** The forecast catalogue has

$$
 R_r=\sum_{j=0}^r4^j=\frac{4^{r+1}-1}{3}
 \quad\hbox{rows, and}\quad
 R_r4^H\quad\hbox{rational forecast entries}.
 \tag{8.3}
$$

Each packet actually retains or computes its $4^{H+r}$ full counters
of width $\lceil\log_2(n+1)\rceil$, the length-$H+r$ word buffer,
and its requested prefix marginals. Startup, all reached packets
and refinements, their complete original prefixes, reference lower
defect names, rational precisions, powers and comparisons are paid.
The normalizations and error certificates cost all
$R_r4^H$ divisions/endpoint comparisons and sums in their actual
rational bit widths; neither arithmetic nor real scalars receive
unit or zero cost. The gate scanner pays for every read, block
counter, failed block, comparison, lookup, suffix update and output.
For fixed deterministic $S,L$ its source waiting bill is exactly
(6.18), followed by $r$ Reads. There is no finite worst-case waiting,
no source-uniform expected bill, and no inference of the same expected
bill for a selected branch.

A full retained archive through a completed cut $C$ contains $C$
original labels, hence $2C$ label bits under the two-bit coding,
in addition to addresses, handles, counters, tables and other records.
Scanning may reuse that archive; it does not delete existing acquired
rows, permissions, legal menus or records. All observations arriving
during reference or processor work, their buffering, retained prefixes,
working space, rescan work and real completion latency remain charged
as in [SRO, Definition 21.1] and [OWGR, §21]. Only finitely many
branches are actually executed, but every reached unsuccessful or
inconclusive finite test is included. No practical efficiency,
throughput, processor deadline, or finite expected total work follows
from the sourcewise finite certificate.

**Definition 8.4 (the reduced interface and the residual bridges).**
The new relation is the simultaneous finite-window forecast after the
first actually observed disjoint $B$ block, with the whole prefix
conditioned at each moving cut. The comparison word square (6.7)
and its actual stopped averaging (6.10)--(6.17) reduce the quantitative
prediction error side of the live continuation interface. The
finite rows in §7 are acquired coordinates for this comparison.
They do not reconstruct the exact filter, hidden point, source
space, endpoint, clock or full future law.

An actual-current consumer still needs a lawful executor that
processes and retains every label through its actual completion
$C$, generates any accumulated additional error, pays its work and
storage, and proves a completion/catch-up condition putting
$C\in\{T,\ldots,T+r\}$ for the chosen certificate. Neither the
finite tables nor the $L4^L$ waiting expectation supplies this
condition. No physical Return, reset, point-feature supplier,
control, extra sensor, native/diffusion/AURIC correspondence, or
infinite-horizon all-law forecast is established. In particular the
unbounded family of finite ordered native trees and its actual
$\rho$ and root/address reads retain their own contracts; these
rows supply no executor for that source. Any use of AURIC still
requires its original $E$, positive evaluations, exact cone,
A1--A3, all P2/PB and original domain, with no map furnished here.

**Definition 8.5 (mathematical attribution).** Reversible word
pairings, conditional probability, positive-form Cauchy--Schwarz,
TV contraction, interval arithmetic and countable union bounds
are mature intermediates. The reused original-source suppliers
are (2.2)--(2.5), [DPCR, §§8--9], the static B-prefix/complete-future
comparisons [OWGR, §§15--16], the earned startup, reference names
and common-event composition [SRO, §§21--22], and the paid
retention/completion boundaries [OWGR, §§20--21] and
[FEA, Definitions 16.2 and 18.3]. The stopped, actual-label,
full-history finite-window relation and its generated finite
certificate are a repo-derived composite of those suppliers.
These are conditional mathematical statements in prose, with no
fresh Lean verification or independently checked worldwide
novelty claim.

[OWGR]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_WORD_GEOMETRY_RECOVERY.md
[DPCR]: RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md
[SRO]: RECURSIVE_RELATIONAL_OBSERVATION_SOURCE_RELATIVE_ORDER.md
[FEA]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_FINITE_ENERGY_ACQUISITION.md

## 追加锚（本行以下为增补区）

## 9. Effective original-source contact certificates at every later cut

**Definition 9.1 (the retained source, complete future and gate).**
Retain Assumption 1.1 and Definitions 6.1 and 7.1 in full, for every
original finite $a,\eta,d>0$ and every permitted repaired Borel
emission. In particular the group, unit-source normalization,
complete complex non-Friedrichs endpoint, operator and form domains,
source trace, $e$-start, first read at $2d$, subsequent gaps $d$,
four labels and fresh conditional noise are unchanged. Write
$P_t=T_t$, so that the discrete operator remains $P=P_d$.
Use exactly the properly associated conservative process of
[CONTACT, Theorem 116.3][CONTACT], with its properly exceptional
set $\mathcal N$ satisfying $e\notin\mathcal N$; $m(\mathcal N)=0$.
Its contact time is $\tau_e=\inf\{s\ge0:Z_s=e\}$.
Contact is an analytic stopping time of this process, not a
detectable label, sensor, available Return or operation on the source.

On $\Omega=\mathcal L^{\mathbb N}$ use the whole product sigma algebra
$\mathscr Y=\bigotimes_{n\ge0}2^{\mathcal L}$. For a word $v$ let
$[v]$ be its initial cylinder. Reuse the common future kernel
$\mathcal K(x,E)$ of [OWGR, Definition 15.1]: it starts at the
next hidden read state $x$, emits with the original $f_y$, then
repeats $P_d$ and the original independent conditional noise.
It is a probability kernel on all of $\mathscr Y$, with
$\mathcal K(x,[v])=F_v(x)$ as $m$-classes. For every history $u$
put

$$
\begin{gathered}
R_u^\infty(E)=\int_G\pi_u(x)\mathcal K(x,E)m(dx),\qquad
Q_\emptyset^\infty(E)=\int_G\mathcal K(x,E)m(dx),\\
R_u^\infty([v])=\frac{p(uv)}{p(u)},\qquad
Q_\emptyset^\infty([v])=q(v),\\
Q_w^\infty(E)=
 \frac{Q_\emptyset^\infty([w]\cap\theta^{-|w|}E)}{q(w)},\qquad
R_t^\infty=R_{Y_{<t}}^\infty .
\end{gathered}
\tag{9.1}
$$

Here $\theta$ is the left shift and $\pi_u$ is the actual next-read
posterior of (2.2), conditioned on the entire history $u$.
All $p(u),q(u)>0$ by Definition 6.1, so every finite conditioning
in (9.1) is defined. Cylinder uniqueness extends the identities
from (2.2) to the full product law. The superscript $H$ below
denotes the marginal on the first $H$ future labels, agreeing with
(6.1)--(6.3). The comparison $Q_\emptyset^\infty$ is mathematical;
it supplies no stationary specimen preparation or exact-law query.

Fix deterministic integers $S\ge0$ and $k\ge2$. Take precisely the
disjoint-block gate (6.2) with $L=2k$:

$$
\begin{gathered}
U_i=S+(i-1)2k,\qquad
C_i=\{Y_{[U_i,U_i+2k)}=B^{2k}\},\\
J=\inf\{i\ge1:C_i\},\qquad T=S+2kJ,\qquad
W_j=Y_{[T,T+j)}\quad(j\ge0).
\end{gathered}
\tag{9.2}
$$

In particular $W_0=\emptyset$. The cut $T+j$ remains immediately
before the read at physical time $(T+j+2)d$.

**Theorem 9.2 (contact envelope and one complete-future event for all
later actual cuts).** For every source and deterministic $S,k$ of
Definition 9.1, every $M\ge\|g_d\|_\infty$ and every $\epsilon>0$,
let $d_\lambda$ be the original defect of [DPCR, Definition 9.1]
and put

$$
\eta_k=M\left[
 \frac{1-d_{1/(kd)}}{1-\exp(-1)}
 +\frac12\sqrt{
       \frac{1-d_{1/[2(k-1)d]}}{d_{1/[2(k-1)d]}}}\right].
\tag{9.3}
$$

Then $T<\infty$ almost surely and

$$
\mathbb E_e\operatorname{TV}(\pi_{Y_{<T}}m,m)\le\eta_k,
\tag{9.4}
$$

where $\operatorname{TV}(\pi m,m)=\tfrac12\int|\pi-1|\,dm$.
On the full product sigma algebra of (9.1),

$$
\mathbb P_e\left\{
 \sup_{j\ge0}\operatorname{TV}
       (R_{T+j}^\infty,Q_{W_j}^\infty)>\epsilon\right\}
 \le\min\{1,2\eta_k/\epsilon\}.
\tag{9.5}
$$

On the complement of the failure event in (9.5),
$\operatorname{TV}({\bf R}_{T+j}^H,Q_{W_j}^H)\le\epsilon$
holds for every integer $j\ge0$ and every finite $H\ge1$ simultaneously.
This is an unconditional event in the original law, not a bound
conditional on each reached history, gate index, calibration
output or selected branch.

*Proof.* First obtain an original-clock transition estimate using
the actual contact law. Since $g_d$ is a nonnegative probability
density, $\|g_d\|_\infty\ge1$. Thus $u=g_d-1$ has mean zero and
$\|u\|_\infty\le M$. For every $t\ge kd$, propagation and
$L^2$ contraction, followed by [DPCR, Theorem 9.2, (9.3)], give

$$
\begin{aligned}
\operatorname{TV}(g_t m,m)
 &\le\frac12\|g_t-1\|_2
 \le\frac12\|P_{(k-1)d}u\|_2\\
 &=\frac12\sqrt{\langle u,P_{2(k-1)d}u\rangle_m}\\
 &\le\frac M2\sqrt{\Theta(1/[2(k-1)d])}
 =:\gamma_k .
\end{aligned}
\tag{9.6}
$$

The offset is $k-1$, because the positive-time density used at the
start of this estimate is $g_d$. No zero-time density or numerical
physical time name is assumed.

For legitimate starting points $x$ put
$a_k(x)=\mathbb P_x(\tau_e>kd)=P_{kd}^01(x)$, using the killed
transition version of [CONTACT, (116.9)] and any Borel extension
on the exceptional null set. The hitting transform and its integral in
[CONTACT, (116.9), (116.14)] imply

$$
\begin{aligned}
(1-\exp(-1))\int a_k\,dm
 &\le\int_G\mathbb E_x[1-\exp(-\tau_e/(kd))]m(dx)\\
 &=1-d_{1/(kd)}.
\end{aligned}
\tag{9.7}
$$

For this inequality $\exp(-\infty)=0$; it also follows directly
on $\{\tau_e>kd\}$. The integral identity is precisely
$\int b_\lambda\,dm=d_\lambda$, with the original clock and
the full source trace. It is not the contact transform of a
different process with a similar differential expression.

At time $2kd$, split the transition from $x$ into
$\{\tau_e>kd\}$ and $\{\tau_e\le kd\}$. The first piece has mass
$a_k(x)$. By the strong Markov property, the second is a mixture
of source-start laws $g_{2kd-s}m$, $0\le s\le kd$.
Every such remaining time is at least $kd$ and satisfies (9.6).
Subtract the corresponding masses of $m$ from both pieces.
The first signed piece has TV at most $a_k(x)$; the second has
TV at most $\gamma_k(1-a_k(x))$. Therefore, for every probability
density $\pi$ relative to $m$,

$$
\begin{aligned}
\operatorname{TV}(P_{2kd}(x,\cdot),m)&\le a_k(x)+\gamma_k
                   \quad(x\notin\mathcal N),\\
\operatorname{TV}((P_{2kd}\pi)m,m)
 &\le \langle\pi,a_k\rangle_m+\gamma_k .
\end{aligned}
\tag{9.8}
$$

Symmetry identifies the propagated measure's density with
$P_{2kd}\pi$. The mixtures are Borel transition mixtures of the
properly associated process. TV can be taken over a countable
generating algebra of the standard Borel state space $G$, so its
kernel supremum is measurable. No observation of $\tau_e$ is
made. All posterior densities are absolutely continuous with
respect to $m$ and hence avoid $\mathcal N$.

We next average at the actual first successful block. Let
$b_L=4^{-L}$, $L=2k$, and
$E_{i-1}=\bigcap_{h<i}C_h^c$. For a prefix $u$ of length $U_i$
satisfying $E_{i-1}$, (2.5) gives exactly

$$
p(uB^L)=b_Lp(u),\qquad
\pi_{uB^L}=P^L\pi_u=P_{2kd}\pi_u .
\tag{9.9}
$$

These are full-history posteriors; the failed blocks and every
other preceding label remain in $u$. Theorem 2.1 identifies
$\langle\pi_{Y_{<U_i}},a_k\rangle_m$ with
$\mathbb E_e[a_k(X_{U_i})\mid\mathscr F_{U_i}]$.
Summing (9.8)--(9.9) over these prefixes yields

$$
\begin{aligned}
\mathbb E_e\operatorname{TV}(\pi_{Y_{<T}}m,m)
 &\le\sum_{i\ge1}b_L
       \mathbb E_e[\mathbf1_{E_{i-1}}a_k(X_{U_i})]
       +\gamma_k .
\end{aligned}
\tag{9.10}
$$

Here Proposition 6.6 supplies $J<\infty$ almost surely, so the
weights multiplying the constant $\gamma_k$ sum to one.
Conditional on the entire hidden path, each disjoint all-$B$
block has probability $b_L$, and their indicators are independent.
Thus the sum in (9.10) is

$$
\begin{aligned}
&\sum_{i\ge1}b_L(1-b_L)^{i-1}
       \int g_{(U_i+2)d}(x)a_k(x)m(dx)\\
&\hspace{2em}\le M\int a_k\,dm ,
\end{aligned}
\tag{9.11}
$$

because $\|g_{(U_i+2)d}\|_\infty\le\|g_d\|_\infty\le M$
and the geometric weights sum to one. Nonnegativity justifies the
countable sums. Equations (9.6)--(9.7) now prove (9.4).
Only the contact-tail integral in (9.11) uses this density bound;
$\gamma_k$ was integrated against probability measures in (9.8).
Consequently (9.3) has a single factor $M$, not a second density
factor multiplying its square-root term. No individual posterior
$\pi_u$ has been bounded by $M$.

For completeness, the passage to all later cuts uses a finite
measure on the entire future space, rather than a horizon-by-horizon
union bound. Fix one possible stopped history $u=Y_{<T}$. Put
$A=R_u^\infty$, $B=Q_\emptyset^\infty$ and
$e(u)=\operatorname{TV}(A,B)$. The common kernel in (9.1) contracts
TV on the full product sigma algebra, giving

$$
e(u)\le\operatorname{TV}(\pi_u m,m).
\tag{9.12}
$$

Let $\nu=|A-B|$ be the Jordan total-variation measure of the signed
measure $A-B$, so $\nu(\Omega)=2e(u)$. For a word $w$ of length
$j$, write $a_w=A([w])>0$, $b_w=B([w])>0$, and define the
conditional tail probabilities

$$
A_w(E)=A([w]\cap\theta^{-j}E)/a_w,\qquad
B_w(E)=B([w]\cap\theta^{-j}E)/b_w .
\tag{9.13}
$$

The map taking a sequence in $[w]$ to its tail is a measurable
bijection with measurable inverse (prefixing by $w$). Restrict
$A-B$ to $[w]$, normalize first by $a_w$, and then correct the
$B$ normalization from $a_w$ to $b_w$. The triangle inequality
for the total mass of a signed measure's variation gives

$$
\begin{aligned}
2\operatorname{TV}(A_w,B_w)
 &\le\frac{\nu([w])+|b_w-a_w|}{a_w}
 \le\frac{2\nu([w])}{a_w}.
\end{aligned}
\tag{9.14}
$$

The factor two on the left is valid because the two normalized
conditional measures have equal mass one. This derivation
does not assume absolute continuity between their infinite
future laws.

Under $A$, let $\omega_{<j}$ be the first $j$ future labels and set

$$
N_j(\omega)=\frac{\nu([\omega_{<j}])}
                       {A([\omega_{<j}])},\qquad N_0=2e(u).
\tag{9.15}
$$

This is a finite nonnegative martingale for the increasing
finite-prefix sigma algebras. Indeed, on $[w]$ its conditional
next-step expectation is

$$
\sum_{y\in\mathcal L}
 \frac{a_{wy}}{a_w}\frac{\nu([wy])}{a_{wy}}
 =\frac{\nu([w])}{a_w}.
\tag{9.16}
$$

All denominators are positive and the child cylinders partition
$[w]$. No Radon--Nikodym derivative on $\mathscr Y$ is needed:
the ratios in (9.15) are only at finite positive cylinders.
In particular positivity of cylinders is not being used to infer
absolute continuity of full product measures, which does not
follow from that positivity alone.

Ville's nonnegative-martingale maximal inequality, as stated by
Howard--Ramdas--McAuliffe--Sekhon in *Exponential line-crossing
inequalities* [VILLE, §2.3, Lemma 1, (18)][VILLE], and (9.14) imply

$$
A\left\{\sup_{j\ge0}
  \operatorname{TV}(A_{\omega_{<j}},B_{\omega_{<j}})
       >\epsilon\right\}
 \le\min\{1,2e(u)/\epsilon\}.
\tag{9.17}
$$

This use of Ville can also be obtained by stopping $N_j$ at its
first crossing of $\epsilon$ up to a finite index $n$:
nonnegativity and bounded stopping give crossing probability at
most $N_0/\epsilon$; increasing $n$ covers all $j$. The martingale
and its variation measure are mathematical proof objects, not
supplied numerical services.

The event in (9.17) is measurable on the full product. For any two
probabilities on $\Omega$, their event-TV is the supremum of their
finite-prefix TVs. This is the finite-alphabet specialization of
[THREAD, total_variation_eq_iSup_level][THREAD]: take levels
$\mathcal L^n$, truncation bonding maps and one thread.
The measurable identification with $\Omega$ preserves the product
sigma algebra. Equivalently, finite cylinder unions approximate
every product-measurable event in the sum of the two finite
measures. Thus every TV in (9.17) is a countable supremum of
finite sums of cylinder probabilities. The supremum over $j$
is countable too. There is no extension to a larger sigma algebra
or inference from convergence on each individual cylinder alone.

Given $\mathscr F_T$, the conditional law of the actual future is
$A=R_u^\infty$, and after its actual prefix $w=W_j$ its tail law
$A_w$ is precisely $R_{uw}^\infty=R_{T+j}^\infty$.
The comparison conditional is $B_w=Q_w^\infty$. The gate value
is already determined by $u$ and adds no future conditioning.
The countably many stopped histories therefore allow (9.17)
to be averaged in the original law. Using (9.12) and (9.4),

$$
\mathbb P_e\left\{\sup_{j\ge0}
 \operatorname{TV}(R_{T+j}^\infty,Q_{W_j}^\infty)>\epsilon\right\}
 \le\frac2\epsilon\,\mathbb E_e e(Y_{<T})
 \le\frac{2\eta_k}{\epsilon}.
\tag{9.18}
$$

The bound by one gives (9.5). Projection contracts TV and proves
the simultaneous assertion for every finite $H$. In particular
neither $H$ nor an advance expiry $r$ appears in this event.
$\square$

**Proposition 9.3 (a finite rational guard from earned bounds and
the fixed reference).** Let earned positive rationals $c_-,l$
satisfy $c_-\le c$ and $l\le\tau=a^2d/\eta$, and put
$M_0=1/(4c_-)$. Use only the paid fixed-reference defect service
at coefficients $1,1$ in [SRO, §§21--22] and (7.1).
For $k\ge2$ obtain rational lower enclosures and a rational $u\ge0$
such that

$$
\begin{gathered}
0<A^-\le D_k(l),\qquad 0<B^-\le D_{2(k-1)}(l),\qquad
A^-,B^-<1,\\
u^2\ge(1-B^-)/B^-,\qquad
\eta_k^+=M_0[\,2(1-A^-)+u/2\,].
\end{gathered}
\tag{9.19}
$$

Then (9.4)--(9.5) hold with $\eta_k$ replaced by $\eta_k^+$.
For any positive rational $\epsilon,\delta$, fair search over
$k$ and reference precision, with rational upper-square-root
refinement, terminates with

$$
2\eta_k^+<\epsilon\delta.
\tag{9.20}
$$

The resulting all-cut failure bound is strictly smaller than
$\delta$. The generated certificate is (9.19)--(9.20), not an
algorithm evaluating any of the complete future laws.

*Proof.* From the original calibration and (7.2),

$$
\begin{gathered}
\|g_d\|_\infty=\frac1{4c}-1\le M_0,\qquad
d_{1/(kd)}=D_k(\tau)\ge A^-,\\
d_{1/[2(k-1)d]}=D_{2(k-1)}(\tau)\ge B^- .
\end{gathered}
\tag{9.21}
$$

The function $(1-x)/x$ decreases on $(0,1]$ and
$(1-\exp(-1))^{-1}<2$. Apply Theorem 9.2 with $M=M_0$:
its $\eta_k$ is at most the rational expression $\eta_k^+$.
This proves sufficiency, including the strict failure assertion
under (9.20).

Here is a finite search using exactly the authorized names.
For each integer $k\ge2$ and precision index $s\ge1$, request
certified rational intervals of width tending to zero with $s$
for $D_k(l)$ and $D_{2(k-1)}(l)$. These are the total
[DPCR, (11.30)] reference calls described in
[SRO, (SRO.150)--(SRO.151)], at rational discounts $1/(kl)$
and $1/[2(k-1)l]$. If either lower endpoint is nonpositive,
this pair $(k,s)$ is inconclusive. Otherwise lower it, if necessary,
to at most $1-2^{-s}$ to obtain $A^-,B^-$ in (9.19).
For each fixed $k$, these lower enclosures converge to the strictly
positive values $D_k(l),D_{2(k-1)}(l)$ and remain below one.

For the rational $x=(1-B^-)/B^-\ge0$, rational bisection on
$[0,1+x]$, comparing squares to $x$, gives a rational upper
endpoint $u$ with
$0\le u-\sqrt x\le2^{-s}$ after finitely many comparisons.
The initial interval is valid since $(1+x)^2\ge x$.
Thus every tested pair uses finitely many reference operations
and rational operations. Enumerating the pairs in increasing
$k+s$ is fair and never waits for an equality test to resolve.

For fixed $k$, the values $\eta_k^+$ along increasing precision
converge to

$$
M_0\left[2(1-D_k(l))+
 \frac12\sqrt{\frac{1-D_{2(k-1)}(l)}{D_{2(k-1)}(l)}}\right].
\tag{9.22}
$$

By (7.2), this expression tends to zero as $k\to\infty$.
Choose a finite $k$ for which twice (9.22) is strictly below
$\epsilon\delta$, and then a finite precision preserving that
strict slack. Fair search reaches such a pair and terminates.
This uses no numerical name of the physical $a,\eta,d$.
In particular [DPCR, Theorem 12.4] cannot be called at those
unknown coefficients: its total coefficient/time names remain
required there. The selected route needs no global heat-norm
call, even at the reference; the original centered heat bound
and the two paid reference defects suffice. $\square$

**Corollary 9.4 (selection on one event and the conditional
actual-current consumer).** Predeclare a countable effectively
enumerated family of deterministic descriptions $\kappa$,
specifying positive rational $c_\kappa,l_\kappa,
\epsilon_\kappa,\delta_\kappa$ and integer $S_\kappa\ge0$.
Let $\sum_\kappa\delta_\kappa<\infty$. Generate a deterministic
$k_\kappa$ and guard (9.19)--(9.20) from each description.
Use the inherited predeclared acquisition packets and their
common event $\mathcal A_\tau$ of probability at least $1-\alpha$,
as in Theorem 8.1 and [SRO, Theorem 22.1]. On this event,
each selected description has earned
$c_\kappa\le c$ and $l_\kappa\le\tau$; every row/certificate
actually supplied by those packets retains its original finite
domain and validity.

There is an original-law event $\mathcal G$ with

$$
\mathbb P_e(\mathcal G)\ge1-\alpha-\sum_\kappa\delta_\kappa
\tag{9.23}
$$

on which every selected description obeys the dynamic comparison
of Theorem 9.2 at every later integer cut and every finite horizon.
Suppose a lawful executor for one such description actually
completes at a finite causal cut $C\ge T_\kappa$, retains and
processes every actual label through $C$, and genuinely supplies
a probability row $\rho_C$ at a finite horizon $H$ with a
same-event generated error certificate

$$
\operatorname{TV}(\rho_C,Q_{W_{\kappa,C-T_\kappa}}^H)
 \le\zeta_C+\xi_C .
\tag{9.24}
$$

Here $\zeta_C,\xi_C\ge0$ include the acquired row error and all
additional update, rounding and output error, respectively.
On $\mathcal G$, wherever these executor conditions hold,

$$
\operatorname{TV}({\bf R}_C^H,\rho_C)
 \le\epsilon_\kappa+\zeta_C+\xi_C .
\tag{9.25}
$$

An extra row supplier with its own confidence event must have
that event included in $\mathcal A_\tau$ and its failure charged
to $\alpha$; (9.24) is not automatically a new acquired row.

*Proof.* Fix the original source only for the analysis. For each
deterministic description with $c_\kappa\le c,l_\kappa\le\tau$,
Theorem 9.2 and Proposition 9.3 give an unconditional dynamic
event $\mathcal D_\kappa$, with failure less than
$\delta_\kappa$, covering all $j$ and $H$. Define

$$
\mathcal G=\mathcal A_\tau\cap
 \bigcap_{\kappa:\ c_\kappa\le c,\ l_\kappa\le\tau}
                  \mathcal D_\kappa .
\tag{9.26}
$$

The intersection is over the deterministic valid descriptions,
not a random list after calibration. A countable union bound
proves (9.23); the intersection of their almost-sure finite-gate
events costs no probability. On $\mathcal A_\tau$ every selected
description belongs to this intersection. No independence of
calibration, gates, row acquisition or branch selection is used.
Data-selected integer starts and rational tolerances are handled
by their predeclared descriptions, as in Theorem 8.1, not by
substituting random values into a deterministic probability bound.
There is no further union budget over $j$ or $H$.

On $\mathcal G$, substitute the actual finite index
$j=C-T_\kappa$ into its pathwise all-cut event, project to $H$,
and apply the triangle inequality with (9.24).
This proves (9.25), including selection of a horizon from an
actually available certified menu. Causality and actual availability
are executor premises, not consequences of this substitution.
If an executor never completes, this argument supplies no row
and makes no finiteness claim about its completion. $\square$

**Definition 9.5 (paid domain, execution boundary and recovery
scope).** The dynamic comparison in Definition 8.4 can now use
(9.25) without its advance restriction $C\le T+r$. This removes
only that restriction from analytic comparison validity.
The acquired catalogue of Proposition 7.3 still has exactly its
finite domain $\bigcup_{j=0}^r\mathcal L^j$ and finite horizons.
An actual suffix $W_{C-T}$ can exceed every acquired catalogue.
Neither (9.5) nor a short description of a mathematical law
supplies its numerical row, the legality of a new query, a
generated error certificate for it, or its completed output.

The guard alone uses two fixed-reference defect enclosures per
tested $k$ and precision, rational upper-square-root refinement,
integer search and exact rational comparisons. Charge every
reached call, refinement, failed or inconclusive test, rational
bit width and working bit. This guard does not enumerate
$4^{H+r}$ words; all existing word acquisition, counting,
normalization, row and certificate work remains charged under
Definition 8.3. No measured speed advantage, numerical runtime
bound or finite expected total work follows.

For a fixed deterministic description its source waiting bill,
by Proposition 6.6, is

$$
\mathbb E_e(T-S)=2k\,4^{2k},\qquad
\mathbb P_e(T-S>2kn)=(1-4^{-2k})^n\quad(n\ge0).
\tag{9.27}
$$

There is no finite worst-case gate bound. This expectation is
not transferred to a data-selected description. The rational
guard search is finite at every positive rational branch input,
and each fixed gate is almost surely finite. These facts do not
establish a finite actual end-to-end executor completion, a
capture/write service or a processor that catches up.

A retained archive through $C$ contains all $C$ actual labels,
hence $2C$ payload bits in the inherited coding, plus addresses,
gate registers, counters, reference descriptions and replies,
precision data and working storage. Preserve all previously
acquired rows, permissions, legal menus and records. Count shared
backing once and every distinct buffer, queue and copy.
All arrivals during reference computation, row updates and output
are included through the actual completion cut $C$; output for
an earlier cut is not relabelled as current. Storage, write
bandwidth, buffering, arithmetic, reference work, rescan work
and elapsed completion latency remain separate paid coordinates.
No bounded storage, installed throughput, deadline, atomic output,
or accepted pointer/backing interface is supplied. Actual
serialization of requested entries, or an already accepted backed
representation with its full contract, remains required.

The unpaid executor bridges are lossless capture during all work,
assimilation of the entire growing suffix, an actually available
current row and generated accumulated error, lawful output, and
finite actual completion. The contact time used in the proof
does not add point detection, reset, source delay, control,
extra read, physical Return or a new specimen. Exact filtering,
the hidden current point, original space and endpoint recovery,
and physical clock/parameter identification remain outside this
certificate. The event gives high-probability approximate
future comparison; it gives neither exact all-law recovery nor
an effective complete-future-law service.

The original unbounded finite ordered native $\alpha/\beta$ trees,
actual $\rho$ replacements, literal root/address reads, acquired
rows and service rights retain their own domains. The later
access and actual $S$-to-$C$ assimilation exclusions of
[NCO, Definition 10.6][NCO] remain. No native/diffusion/AURIC
identification is supplied. Any AURIC correspondence still owes
the same $E$, positive evaluations, accurate cone, A1--A3, every
P2/PB and original domain; a preselected bottom space or standard
matrix example does not supply the original native source.
Mutual recovery and minimality of space, lawful continuation,
boundary and memory therefore retain these distinct gaps.

**Definition 9.6 (source correspondence and attribution).**
The analytic contact and clock inputs are
[CONTACT, Theorems 116.3--116.4, (116.8)--(116.14)] for this
properly associated process, and its positive-time source law
[CONTACT, Theorem 117.2, (117.2)--(117.3)].
The full-versus-killed domain distinction (116.11) is retained:
the hitting argument uses the full non-Friedrichs process, whose
killed part is the original Friedrichs operator, not a replacement
full source. [DPCR, Definition 9.1 and Theorem 9.2] supplies the
defect and centered heat estimate in (9.6). The actual posterior
and B updates are (2.2)--(2.5); stopped weighting and waiting use
§6 without changing its full-history meaning.

The complete product future kernel and static tail/past distinction
are [OWGR, Definitions 15.1 and Proposition 16.3]; its Theorem 5.2,
(5.2)--(5.3), transports the entire endpoint, source, domains
and clock used in (9.21).
[SRO, Definition 21.1 and Theorem 22.1,
(SRO.150)--(SRO.151)] authorizes only the paid fixed-reference
calls and the common-event branch argument; [DPCR, (11.30)]
supplies their certified defects. [DPCR, Definition 12.1 and
Theorem 12.4] retains its stronger total-name requirements.
No unknown-source heat evaluator has been inferred from an
abstract parameter name. The resource and actual-return boundaries
of [FEA, Definitions 16.2 and 18.3] persist.

Strong Markov conditioning, signed-measure variation, kernel
contraction, finite-prefix martingales, Ville's maximal inequality
[VILLE], rational interval arithmetic and countable union bounds
are established intermediates, not new general theorems here.
[THREAD] supplies the existing level/event-TV framework; citing
its statement does not assert a fresh application compiled in
Lean. The source-specific composition (9.3)--(9.5), its earned
finite guard (9.19)--(9.20), and the conditional consumer
(9.23)--(9.25) are repo-derived ordinary mathematical deductions.
They do not claim fresh Lean verification or worldwide novelty.

[CONTACT]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md
[THREAD]: ../../../D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation.lean
[VILLE]: https://arxiv.org/html/1808.03204v5#S2.SS3
[NCO]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATION_ORDER_ACQUISITION.md

## 追加锚（本行以下为增补区）
