# AURIC FIB approximate online recovery memory

## 1. Scope and source boundary

**Convention 1.1 (Ordinary mathematical scope).** All spaces in this volume are
finite-dimensional complex Hilbert spaces unless a compact metric space is
explicitly named. A channel is a complex-linear completely positive
trace-preserving map. The diamond norm includes arbitrary finite reference
systems. The assertions below concern the measured five-window instrument
restricted to its three-dimensional image, approximate recovery in the
ensemble diamond norm, and classical persistent memory.

**Convention 1.2 (Reused model facts).** The matrices, the five-dimensional
unitary dilation, the two measurement bases, the fair binary outcomes on the
image, and the common phase at $θ=π/6$ are the model-specific results of
[OWN, Definitions 1.3–2.2 and Theorem 6.1][OWN], read at commit
`ffe9d1fcaadbfd8e0fd8aa1d5dace5862b9173c6`. The five-window supplier is
[FIVE, Definitions 2.1–2.3][FIVE]. This volume adds the approximate
offline/online distinction, its constructive upper bound, and its qualitative
fixed-width obstruction. The standard facts used in the proofs are elementary
finite-dimensional norm, compactness, and Taylor estimates; no external
asymptotic recovery theorem is being transferred.

**Convention 1.3 (Literature boundary).** The source records above are the
relevant repository references for the actual instrument; [FIVE] is the
five-window supplier at the pinned baseline
`c594d14a077b19f24f306cfdccc999879054b02a`. A search of the
repository's theory, D5, and Library material found no statement with the
present finite-state online, approximate-diamond conclusion. This is a scope
assessment, not a priority claim. The exact quantitative lower growth and the
intrinsic dimension of the generated subgroup remain open.

## 2. Instrument, products, and resources

**Definition 2.1 (Image coordinates).** Put $H=\mathbb C^5$ with ordered basis
$(e_0,e_1,e_2,e_3,e_4)$ and

$$
u=\frac{e_0+e_3}{\sqrt2},\qquad
v=\frac{e_1+e_4}{\sqrt2},\qquad z=e_2,qquad
R=\operatorname{span}\{u,v,z\}.
$$

Let $B:\mathbb C^3\to H$ be the isometry
$B(x_0,x_1,x_2)=x_0u+x_1v+x_2z$, let $P_R=BB^\dagger$, and write
$\iota(X)=BXB^\dagger$. Set

$$
\xi=\frac{(1,1,1)^{\mathsf T}}{\sqrt3},\qquad
T=\xi^\perp\subset\mathbb C^3,qquad
t_1=\frac{(1,-1,0)^{\mathsf T}}{\sqrt2},\quad
t_2=\frac{(1,1,-2)^{\mathsf T}}{\sqrt6}.
$$

**Definition 2.2 (The fixed-angle branches).** Let

$$
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},\qquad
W=U_0^\dagger U_1=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix}.
$$

At $\theta=\pi/6$, put

$$
V_0=\frac{\sqrt3}{2}U_0+\frac{i}{2}U_1=U_0e^{i(\pi/6)W},\qquad
V_1=\frac{i}{2}U_0+\frac{\sqrt3}{2}U_1=V_0W.
$$

Both are unitary, $V_j\xi=\lambda\xi$ with
$\lambda=e^{i\pi/6}$, and $T$ is reducing for both. Write
$g_j=V_j|_T$. Then $g_0,g_1\in U(2)$,
$\det g_0=-1$, and $\det g_1=1$.

For a label history $h=(h_1,\ldots,h_n)\in\{0,1\}^n$, use chronological
products

$$
Q_h=V_{h_n}\cdots V_{h_1},\qquad
G_h=g_{h_n}\cdots g_{h_1}.
$$

Thus $Q_h=\lambda^nP_\xi+G_h$ on
$\mathbb C\xi\oplus T$. Every step prepares a fresh pure environment,
measures the fixed binary basis, supplies the actual fair label, and discards
the environment. There is no feedback, postselection, retained environment,
reference access, or adaptive instrument change.

**Definition 2.3 (Counted persistent state).** A complete persistent classical
state contains every private persistent variable, history-dependent control,
clock-dependent table entry, and decoder input. Moving information between
buffers does not change its cardinality. A finite or standard-Borel seed $S$
may be shared independently by controller and decoder; its value is not
charged to the finite state, but all state transitions and decoders are
conditioned on it. Seeds correlated with labels are excluded.

The known horizon, fixed transition-table descriptions, control precision,
and label-acquisition and communication costs are separate resources. They
may depend on $n$ and $ε$ and are not counted as width bits. A table can be
chosen nonuniformly at every time and for every horizon.

**Definition 2.4 (Offline and online memory).** Fix $0<\varepsilon<1/4$. The
offline terminal memory $M_n(\varepsilon)$ is the least cardinality of a
terminal state obtained after unrestricted intermediate processing of the
labels, with a decoder selected by that state. The online peak width
$W_n(\varepsilon)$ is the least $W$ for which a controller has at most $W$
complete persistent states at every time, for every seed, and a terminal
decoder whose average channel is within diamond distance $\varepsilon$ of
the identity on the encoded qutrit. The minimum is over all finite stochastic
updates, all horizon-dependent tables, all independent seeds, and all CPTP
terminal decoders.

The target is uniform over every qutrit input entangled with an untouched
finite reference $Z$. The error is the diamond norm of the averaged corrected
channel minus the identity; no per-history success claim is imposed.

## 3. Full-space and qutrit-space bridge

**Lemma 3.1 (Typed retraction).** Define

$$
C(X)=B^\dagger XB+\operatorname{Tr}((I_5-P_R)X)|0\rangle\langle0|,
\qquad X\in M_5(\mathbb C),
$$

where $|0\rangle$ is the first qutrit basis vector. Then $C:M_5\to M_3$
is CPTP and $C\circ\iota=\operatorname{id}_{M_3}$. For every reference $Z$,
$\iota\otimes\operatorname{id}_Z$ is a trace-norm isometry.

**Proof.** The first summand of $C$ has Kraus operator $B^\dagger$ and the
second is the preparation map with positive effect $I_5-P_R$. Their effects
sum to $I_5$, so $C$ is CPTP. Since $B^\dagger B=I_3$, $C(BYB^\dagger)=Y$.
The map $Y\mapsto(B\otimes I_Z)Y(B^\dagger\otimes I_Z)$ preserves the nonzero
singular values, proving the isometry. $\square$

**Theorem 3.2 (Equivalent recovery formulations).** For a full decoder
$D_H:M_5\to M_5$ define

$$
D_3=C\circ D_H\circ\iota.
$$

For every qutrit unitary $Q$,

$$
\|D_3\circ\operatorname{Ad}_Q-\operatorname{id}_3\|_\diamond
\le
\|D_H\circ\iota\circ\operatorname{Ad}_Q-\iota\|_\diamond.
$$

Conversely, for a qutrit decoder $D_3$ define
$D_H=\iota\circ D_3\circ C$. Then

$$
\|D_H\circ\iota\circ\operatorname{Ad}_Q-\iota\|_\diamond
=
\|D_3\circ\operatorname{Ad}_Q-\operatorname{id}_3\|_\diamond.
$$

**Proof.** The first inequality is diamond contractivity of the CPTP map $C$
applied to
$D_H\iota\operatorname{Ad}_Q-C\iota=D_H\iota\operatorname{Ad}_Q-\iota$.
For the second identity, compose the difference on the left by the isometric
embedding $\iota$ and use $C\iota=\operatorname{id}_3$; the diamond norm is
unchanged by that embedding, including every reference. $\square$

**Corollary 3.3 (Phase-correct full decoder).** If $x\in L$ is a unitary on
$T$, set

$$
\widehat x=\lambda^nP_\xi+x|_T,\qquad
\widetilde x=B\widehat xB^\dagger+(I_5-P_R).
$$

Then $\widetilde x$ is a unitary on $H$, and
$\operatorname{Ad}_{\widetilde x^\dagger}$ is a legal full decoder. The factor
$\lambda^n$ is retained; it is a relative phase between $\xi$ and $T$ and is
not a removable global phase.

## 4. Explicit compact mesh

**Definition 4.1 (The ambient group).** Let

$$
L=\{U\in U(2):\det U\in\{+1,-1\}\}=SU(2)\sqcup g_0SU(2).
$$

The quaternion parametrization identifies $SU(2)$ with the unit sphere
$S^3\subset\mathbb R^4$ by

$$
\mathsf q(a,b,c,d)=
\begin{pmatrix}a+ib&c+id\\-c+id&a-ib\end{pmatrix},
\qquad a^2+b^2+c^2+d^2=1.
$$

The subgroup generated by $g_0,g_1$ is contained in $L$; let
$K=\overline{\langle g_0,g_1\rangle}\subseteq L$.

**Lemma 4.2 (Cross-polytope mesh).** There are finite sets
$\mathcal N_m\subset L$ and a deterministic choice of a finite probability
law $\nu_z^{(m)}$ on $\mathcal N_m$ for every $z\in L$ such that, with
$h_m\le c_*/m$, every $z$ has a mesh point within $h_m$,

$$
\left\|\mathbb E_{\nu_z^{(m)}}Y-z\right\|_F\le c_0h_m^2,qquad
\mathbb E_{\nu_z^{(m)}}\|Y-z\|_F^2\le c_1h_m^2,qquad
|\mathcal N_m|\le C_0(1+m^3).
$$

The identity $I_2$ is included in every $\mathcal N_m$.

**Proof.** In $\mathbb R^4$ take the cross-polytope
$P=\{p:\|p\|_1\le1\}$. Its sixteen facets are the tetrahedra
$\sigma\cdot p\ge0$ with $\sum_i\sigma_ip_i=1$, indexed by
$\sigma\in\{\pm1\}^4$. Subdivide each facet by barycentric points with
integer coordinates summing to $m$, and triangulate each small lattice cube
by the standard finite Kuhn subdivision. A facet has
$\binom{m+3}{3}$ vertices. Every point of $\partial P$ is in a facet and a
simplex; on common faces choose the lexicographically first pair.

For $p\in\partial P$, $\|p\|_2\ge1/2$ because
$\|p\|_1\le2\|p\|_2$. Hence the radial map
$r(p)=p/\|p\|_2$ has uniformly bounded first and second derivatives on every
facet. If $p=\sum_a\alpha_ap_a$ is the chosen simplex decomposition and
$Y=r(p_a)$ with probability $\alpha_a$, Taylor's formula gives

$$
\left\|\mathbb EY-r(p)\right\|_2\le c'_0m^{-2},\qquad
\mathbb E\|Y-r(p)\|_2^2\le c'_1m^{-2}.
$$

The first estimate is the cancellation of the affine term
$\sum_a\alpha_a(p_a-p)=0$; the second follows from the bounded first
derivative and simplex diameter $O(m^{-1})$. The quaternion map is linear and
the Frobenius norm is a fixed multiple of the Euclidean norm, so the same
bounds hold in $SU(2)$. Left multiplication by $g_0$ is an isometry and gives
the second component. The union of the two component meshes has at most
$32\binom{m+3}{3}$ points; adding $I_2$ changes this by one. Duplicate points
are merged. The facet and simplex tie rule makes $\nu_z^{(m)}$ a single
well-defined finite table, including points with zero coordinates. $\square$

## 5. Offline terminal bound and online construction

**Theorem 5.1 (Offline memory).** There is a constant $C_K$ such that

$$
M_n(\varepsilon)\le C_K(1+\varepsilon^{-3})
$$

for every $n$ and $0<\varepsilon<1/4$.

**Proof.** Use the mesh of Lemma 4.2 with $h_m\le\varepsilon/4$ and, after
observing the full label history, store an index $x$ whose mesh point satisfies
$\|x-G_h\|_{\mathrm{op}}\le\varepsilon/4$. The terminal decoder is
$\operatorname{Ad}_{\widetilde x^\dagger}$ from Corollary 3.3. Since
$\widehat x^\dagger Q_h-I$ is zero on $\xi$ and equals $x^\dagger G_h-I$
on $T$,

$$
\|\operatorname{Ad}_{\widehat x^\dagger Q_h}-\operatorname{id}\|_\diamond
\le2\|x-G_h\|_{\mathrm{op}}\le\varepsilon/2.
$$

The averaged error obeys the same bound. The mesh cardinality is
$O(1+h_m^{-3})=O(1+\varepsilon^{-3})$. Enlarging the constant gives the
stated form. $\square$

**Theorem 5.2 (Online polynomial upper bound).** There is a constant $C_K$
and a finite constant $L_K$ such that

$$
W_n(\varepsilon)\le
\min\left\{2^n,\ C_K\left(1+\left(\frac{n}{\varepsilon}\right)^{3/2}\right)\right\}.
$$

**Proof.** Fix $m$ and let $\mathcal N_m$ be the mesh. The controller starts
at $X_0=I_2$. Given state $x$ and label $j$, put $z=g_jx$ and sample
$X_{t+1}=Y$ from the barycentric table $\nu_z^{(m)}$. This is a legal finite
row-stochastic update table; it is allowed to be time- and horizon-dependent,
although this table is homogeneous. The exact product obeys
$G_{t+1}=g_jG_t$. For a history and rounding realization set
$E_t=X_t^\dagger G_t$. Then

$$
E_{t+1}=Y^\dagger zE_t,
\qquad z=g_jX_t.
$$

Let $A=Y^\dagger z-I_2$. Adjoint is linear, so Lemma 4.2 gives uniformly

$$
\|\mathbb EA\|_{\mathrm{op}}\le c_0h_m^2,qquad
\mathbb E\|A\|_{\mathrm{op}}^2\le c_1h_m^2.
$$

For every reference and every operator $R$,

$$
\mathbb E\bigl[\operatorname{Ad}_{I+A}(R)-R\bigr]
 =(\mathbb EA)R+R(\mathbb EA)^\dagger+\mathbb E[ARA^\dagger].
$$

The induced diamond norm is therefore at most
$L_Kh_m^2$ with $L_K=2c_0+c_1$ (using the standard completely bounded
operator norm estimate for left and right multiplication). This estimate is
uniform in $x$ and $j$.

Each relative operator is extended to the qutrit by acting as the identity on
$\mathbb C\xi$. It therefore preserves the known phase block, and the same
diamond estimate applies to the encoded qutrit and every untouched reference.

For completeness, let $\Gamma_{t,x}$ be the positive subchannel obtained by
conditioning on $X_t=x$ after the relative error has been formed. Its diamond
norm is the probability $p_t(x)$, and $\sum_xp_t(x)=1$. The update gives

$$
\Gamma_{t+1}=\frac12\sum_{x,j} 
 \left(\sum_y\nu_{g_jx}^{(m)}(y)\operatorname{Ad}_{y^\dagger g_jx}\right)
 \circ\Gamma_{t,x},
$$

where $\Gamma_t=\sum_x\Gamma_{t,x}$. Comparing the parenthesized channel
with the identity and summing $p_t(x)/2$ yields

$$
\|\Gamma_{t+1}-\Gamma_t\|_\diamond\le L_Kh_m^2.
$$

Since $\Gamma_0=\operatorname{id}$, telescoping gives
$\|\Gamma_n-\operatorname{id}\|_\diamond\le nL_Kh_m^2$. Choose
$h_m\le\sqrt{\varepsilon/(nL_K)}$ (with the trivial exact choice for
$n=0$). Lemma 4.2 then gives
$|\mathcal N_m|\le C_K(1+(n/\varepsilon)^{3/2})$.

The alternative $2^n$ construction stores the full binary history and uses
the exact inverse $Q_h^\dagger$, extended to $H$ by Corollary 3.3. Taking the
smaller width proves the result. $\square$

## 6. Qualitative lower bound for every fixed online width

**Definition 6.1 (Vector contraction).** Put
$U_j=\lambda^{-1}g_j$ on $T$. For a fixed width $W$, a fixed seed $s$, and
row-stochastic transition kernels $T_{k,j,s}(r'\mid r)$ on
$\{1,\ldots,W\}$, define

$$
x_{k,r'}=\frac12\sum_{r,j}T_{k,j,s}(r'\mid r)U_jx_{k-1,r},qquad
N_k=\sum_r\|x_{k,r}\|_2.
$$

The initial tuple is any finite tuple with $\sum_r\|x_{0,r}\|_2=1$; this
relaxation contains every genuine initial state distribution acting on a unit
vector. Define $a_W(k)$ as the maximum of $N_k$ over all such tuples and all
time-inhomogeneous kernels.

**Lemma 6.2 (Compact contraction sequence).** The maximum defining $a_W(k)$
is attained, $a_W(k+1)\le a_W(k)$, and

$$
a_W(k+\ell)\le a_W(k)a_W(\ell).
$$

**Proof.** The normalized vector tuples form a compact set and each transition
simplex is compact; $N_k$ is continuous. The triangle inequality and
unitarity give

$$
N_{k+1}\le\frac12\sum_{r,j}T_{k,j}(r'\mid r)\|x_{k,r}\|_2=N_k.
$$

For concatenation, write the tuple at time $k$ as $y$, with
$\sum_r\|y_r\|=q$. The remaining $ell$ steps give at most
$a_W(\ell)q$ after normalizing $y$ when $q>0$. Maximizing the first block
gives the product bound. $\square$

**Lemma 6.3 (Finite equality trajectories are impossible).** For every finite
$W$ there is $L_W$ with $a_W(L_W)<1$.

**Proof.** Suppose $a_W(k)=1$ for all $k$. Choose length-$N$ maximizers and
pass to a diagonal subsequence in the compact initial tuples and the finite
transition simplices. The limit is an infinite trajectory with $N_k=1$ for
every $k$. Equality in each Euclidean triangle inequality says that all
nonzero summands arriving at one state lie on one positive complex ray.

Let $F_k$ be the finite set of nonzero support rays among the $x_{k,r}$. Every
source has a positive outgoing edge for each label, hence

$$
F_{k+1}=U_0F_k\cup U_1F_k.
$$

The cardinalities are nondecreasing and bounded by $W$, so from some index
$k_0$ they are constant. At the plateau,
$U_0F_k=U_1F_k=F_{k+1}$. Since scalar phases do not change rays,
$U_0$ and $U_1$ may be replaced by $A=g_0$ and $AW_T=g_1$, where
$W_T=W|_T$. Therefore $WF_k=F_k$ and $F_{k+1}=AF_k$. With
$F=F_{k_0}$, induction gives

$$
A^{-k}W_TA^kF=F\qquad(k\ge0). \tag{6.1}
$$

We now rule out a nonempty finite $F$. In the orthonormal basis $(t_1,t_2)$,

$$
A=\frac14\begin{pmatrix}\sqrt3-i&3+i\sqrt3\\3-i\sqrt3&-\sqrt3-i\end{pmatrix},
\quad W_T=\begin{pmatrix}-1&0\\0&1\end{pmatrix}.
$$

Here $\det A=-1$, $\operatorname{tr}A=-i/2$, and the eigenvalues are
$\alpha_\pm=(\pm\sqrt{15}-i)/4$. Their ratio $q=\alpha_+/\alpha_-$
satisfies

$$
q+q^{-1}=-\frac74.
$$

If $q$ were a root of unity, this rational number would be an algebraic
integer and hence an integer, a contradiction. Thus $q^k$ takes infinitely
many values. In an orthonormal $A$-eigenbasis write
$W_T=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)$. Distinct
eigenvalues and noncommutation imply $b,c\ne0$ (a triangular unitary is
diagonal). Also $d=-a$ because $\operatorname{tr}W_T=0$, and direct
multiplication gives $\operatorname{tr}(AW_T)=-\sqrt3/2\ne0$, so
$a,d\ne0$. Every matrix entry is therefore nonzero.

For a finite ray $(1,z)$, the ray of $A^{-k}W_TA^k(1,z)$ has coordinate

$$
f_z(q^k)=q^k\frac{cq^k+dz}{aq^k+bz},
$$

with the evident projective interpretation when the denominator vanishes.
For $z=\infty$ the coordinate is $(d/b)q^k$, and the same formula at
$z=0$ is $(c/a)q^k$. For finite nonzero $z$, comparison of coefficients
shows $f_z$ is nonconstant; otherwise the $q^2$, $q$, and constant
coefficients would force one of $a,b,c,d$ to vanish. A nonconstant rational
map has finite fibers, so its values on the infinite set $\{q^k:k\ge0\}$
are infinite (with at most one pole). Every ray consequently has an infinite
orbit under the conjugates in (6.1), contradicting finite invariance of $F$.
Hence $a_W(L_W)<1$. $\square$

**Theorem 6.4 (Fixed-width impossibility).** For every finite $W$,
$a_W(n)\to0$. Consequently, for every $0<\varepsilon<1/4$,

$$
W_n(\varepsilon)\longrightarrow\infty.
$$

This remains true for arbitrary horizon-dependent and time-dependent updates,
private persistent state, rare bad histories, and independent finite or
standard-Borel shared seeds.

**Proof.** Let $\rho_W=a_W(L_W)<1$. Lemma 6.2 gives
$a_W(n)\le\rho_W^{\lfloor n/L_W\rfloor}\to0$. For a unit vector $t\in T$ put
$A_t=|t\rangle\langle\xi|$, which has trace norm one. A branch product sends
$A_t$ to a scalar phase times $|U_h t\rangle\langle\xi|$. For a fixed seed,
grouping histories by the complete final state and applying arbitrary CPTP
terminal decoders, trace-norm contraction gives

$$
\|\mathcal C_{n,s}(A_t)\|_1\le N_n\le a_W(n).
$$

The estimate is pointwise in $s$, so integrating over any independent
standard-Borel seed preserves it. If the averaged corrected channel were
within diamond distance $\varepsilon$ of the identity, then

$$
\|\mathcal C_n(A_t)\|_1\ge
\|A_t\|_1-\|\mathcal C_n(A_t)-A_t\|_1\ge1-\varepsilon.
$$

For sufficiently large $n$, $a_W(n)<1-\varepsilon$, a contradiction. The
argument uses no exact word count and no per-history estimate. $\square$

## 7. Consequences and open quantitative boundary

**Theorem 7.1 (Approximate memory separation).** Under the fixed-angle actual
instrument and the permissions above,

$$
M_n(\varepsilon)\le C_K(1+\varepsilon^{-3}),\qquad
W_n(\varepsilon)\to\infty,qquad
W_n(\varepsilon)\le
\min\left\{2^n,C_K\left(1+(n/\varepsilon)^{3/2}\right)\right\}.
$$

**Proof.** Combine Theorems 5.1, 5.2, and 6.4. $\square$

**Convention 7.2 (What the theorem does not settle).** The lower proof is
qualitative and supplies no effective uniform formula for $L_W$ or $\rho_W$.
It therefore proves neither $\Omega(\log n)$ nor a polynomial lower bound,
and it does not match the displayed polynomial upper bound. No conclusion is
drawn about exact positive word growth, physical or native realizations, QFT,
capacity, priority, or whole-research completion. Determining an effective
lower function, and deciding whether the exponent $3/2$ can be reduced to the
intrinsic dimension of $K$, are precise open questions.

[OWN]: AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[FIVE]: AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md

## 追加锚（本行以下为增补区）
