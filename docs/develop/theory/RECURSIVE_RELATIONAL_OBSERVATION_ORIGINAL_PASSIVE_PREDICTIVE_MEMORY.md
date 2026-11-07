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
