# FIB-ATOM recursive holographic boundary geometry · Continuation III Appendix IV: energy-collapse boundary

This appendix continues the original source, operator, measure and common-readout telescope of Appendix III §§134–160. It records the full-kernel energy-collapse boundary left open by §§159–160. All statements retain the original finite parameters, the whole group $G$, the probability $m$, the density $g=g_{2d}$, the heat operator $P=T_d$, the first-order map $\Lambda_{134}$ and its exact kernel $V=\ker\Lambda_{134}$. The appendix adds no new physical, Lean/kernel or exact full-law claim.

## 161. Energy collapse on the full infinite-dimensional kernel

**Proposition 161.1 (unit kernel directions with vanishing heat energy).** Retain the complete telescope of Appendix III Definition 134.1, including the finite linear map

$$
\Lambda:L^\infty(G,m;\mathbb R)\longrightarrow\mathbb R^{64},
\qquad V=\ker\Lambda,
$$

and write

$$
q(v)=c\langle gv,P(gv)\rangle_m
    =c\|T_{d/2}(gv)\|_{L^2(m)}^2.
\tag{161.1}
$$

For every fixed original finite $a,\eta,d>0$, there are bounded real Borel functions $v_n$ and Borel sets $E_n\subset G$ such that

$$
v_n\in V,\qquad \|v_n\|_\infty=1,
\qquad \operatorname{supp}(v_n)\subset E_n,
\qquad m(E_n)\longrightarrow0,
\qquad q(v_n)\longrightarrow0.
\tag{161.2}
$$

Each $v_n$ is nonzero, so Appendix III Proposition 134.2 still gives $q(v_n)>0$ for every finite $n$. Thus the unit sphere of the full infinite-dimensional kernel has zero heat-energy infimum, although the positive form has no nonzero zero vector.

*Proof.* Let

$$
\nu(A)=\int_Ag^2\,dm
$$

for Borel $A$. Since $g\in L^2(m)$, $\nu$ is a finite measure absolutely continuous with respect to the nonatomic probability $m$. Choose Borel sets $B_n$ with $0<m(B_n)<1/n$. Absolute continuity then gives

$$
\nu(B_n)\longrightarrow0.
\tag{161.3}
$$

By nonatomicity, each $B_n$ contains $65$ pairwise disjoint Borel subsets $A_{n,1},\ldots,A_{n,65}$ of positive $m$-measure. Their indicators are linearly independent. Put

$$
F_n=\operatorname{span}_{\mathbb R}
 \{\mathbf1_{A_{n,1}},\ldots,\mathbf1_{A_{n,65}}\}.
$$

The restriction $\Lambda|_{F_n}$ has codomain $\mathbb R^{64}$, so rank-nullity supplies a nonzero vector

$$
v_n=\sum_{j=1}^{65}a_{n,j}\mathbf1_{A_{n,j}}
 \in F_n\cap V.
$$

Scale its coefficients so that $\max_j|a_{n,j}|=1$. Disjointness gives $\|v_n\|_\infty=1$, and with $E_n=\bigcup_jA_{n,j}\subset B_n$ one has

$$
\begin{aligned}
0<q(v_n)
 &=c\|T_{d/2}(gv_n)\|_2^2
 \le c\|gv_n\|_2^2 \\
 &\le c\int_{E_n}g^2\,dm
 \le c\nu(B_n)\longrightarrow0.
\end{aligned}
\tag{161.4}
$$

The first strict inequality is Appendix III Proposition 134.2, the middle inequality is the $L^2$ contraction of $T_{d/2}$, and the last one uses $|v_n|\le1$. This proves (161.2). $\square$

**Corollary 161.2 (what the collapse does and does not provide).** The energy-collapse alternative in Appendix III Corollary 159.4 is nonempty for the full exact linear kernel: it occurs through normalized directions concentrating on sets of vanishing $m$-measure. Appendix III Proposition 160.2 prevents such a sequence from lying in any one fixed finite-dimensional injective reservoir, so the directions necessarily leave every fixed finite-dimensional reservoir. The construction imposes all $64$ first-order constraints, but it does not make any nonlinear residual vanish, produce a legal two-label family, supply a terminal compensator, establish an exact H43 partition, or settle SRS-20 or $F_{64}$.

The source-specific statements (161.1)–(161.4) use only the finite-codimension of $V$, nonatomicity of the retained probability $m$, $g\in L^2(m)$, and the Markov $L^2$ contraction. They are a function-level boundary for the energy-collapse escape and do not assert a spectral gap failure for any fixed finite-dimensional subspace, a zero-energy nonzero vector, a nonlinear completion, a physical realization or a Lean/kernel theorem.

## 追加锚（本行以下为增补区）

## 162. Finite linear observations do not restore energy coercivity

**Definition 162.1 (a finite observation augmentation of the exact kernel).** Retain the complete telescope of Appendix III §§134–161. In particular, let

$$
V=\ker\Lambda_{134}\subset L^\infty(G,m;\mathbb R),
\qquad
q(v)=c\langle gv,P(gv)\rangle_m,
$$

and let $\mathscr R:L^\infty(G,m;\mathbb R)\to\mathbb R^r$ be any finite-dimensional real-linear observation map, with $r\ge0$. Define

$$
W_{\mathscr R}=V\cap\ker\mathscr R.
\tag{162.1}
$$

No continuity, $L^1$ representation or positivity is assumed for $\mathscr R$; it is only a finite list of linear constraints on the same $L^\infty$ classes. The original 64 first-order coordinates are already included in $V$.

**Proposition 162.2 (small-support directions survive every finite linear augmentation).** Let $B_n\subset G$ be Borel sets with $m(B_n)>0$ and

$$
\int_{B_n}g^2\,dm\longrightarrow0.
\tag{162.2}
$$

Then there are bounded real Borel functions $v_n$ such that

$$
 v_n\in W_{\mathscr R},
 \qquad \|v_n\|_\infty=1,
 \qquad \operatorname{supp}(v_n)\subset B_n,
 \qquad 0<q(v_n)\le c\int_{B_n}g^2\,dm\longrightarrow0.
\tag{162.3}
$$

*Proof.* Put $N=64+r+1$. By nonatomicity, each positive-measure $B_n$ contains $N$ pairwise disjoint Borel subsets $A_{n,1},\ldots,A_{n,N}$ of positive measure. Their indicators are linearly independent in $L^\infty(m;\mathbb R)$. Let

$$
F_n=\operatorname{span}_{\mathbb R}
\{\mathbf1_{A_{n,1}},\ldots,\mathbf1_{A_{n,N}}\}.
$$

The combined linear map

$$
(\Lambda_{134},\mathscr R):F_n\longrightarrow\mathbb R^{64+r}
$$

has a nonzero kernel by rank-nullity. Choose a nonzero $v_n$ in that kernel and scale its coefficients so that their maximum absolute value is one. Disjointness then gives $\|v_n\|_\infty=1$, and $v_n$ is a bounded real Borel function supported in $B_n$. It belongs to $V$ and is annihilated by $\mathscr R$, hence to $W_{\mathscr R}$. Proposition 134.2 gives strict positivity for every nonzero such class. Since $|v_n|\le1$,

$$
0<q(v_n)=c\|T_{d/2}(gv_n)\|_2^2
\le c\|gv_n\|_2^2
\le c\int_{B_n}g^2\,dm.
$$

The last quantity tends to zero by (162.2). $\square$

**Corollary 162.3 (finite readouts have zero coercivity infimum).** For every finite-dimensional real-linear $\mathscr R$,

$$
\inf\left\{q(v):v\in W_{\mathscr R},\ \|v\|_\infty=1\right\}=0.
\tag{162.4}
$$

In particular, adjoining any finite list of additional linear marginals, probes or calibration coordinates to all 64 first-order equations cannot produce a positive lower bound for the weighted heat energy on the full calibrated kernel. The conclusion is algebraic and does not depend on whether the added functionals are represented by $L^1$ kernels.

If $m(B_n)\to0$, then the same sequence can be chosen weak-star null in $L^\infty(m)$. Indeed, for every $h\in L^1(m)$, absolute continuity of the integral gives

$$
\left|\int_Gh v_n\,dm\right|
\le\int_{B_n}|h|\,dm\longrightarrow0.
\tag{162.5}
$$

Thus the escape can simultaneously satisfy any fixed finite linear observation list exactly and become invisible to every fixed integrable probe in the limit.

The result is a finite-dimensional boundary only. It does not supply an infinite family of constraints, a nonlinear residual-zero tuple, pointwise simplex legality, an exact H43 partition, a terminal compensator, an SRS-20 construction, an $F_{64}$ witness, a physical realization or a Lean/kernel theorem. It also does not assert that an arbitrary nonlinear or discontinuous infinite-dimensional readout fails to control the energy. The source-specific statements (162.1)–(162.5) use only the original finite-codimension map, nonatomicity, rank-nullity, the $L^2$ contraction of $T_{d/2}$ and the strict positivity in Proposition 134.2.

## 追加锚（本行以下为增补区）

## 163. Finite-horizon successor closure remains non-coercive

The R5-007 distinction between a current readout, a well-defined successor and a static state can be stated directly on the calibrated function space. The next result adds a finite successor horizon to the observation map of §162; it does not choose a physical successor operation.

**Definition 163.1 (finite-horizon successor readout).** Let

$$
\mathcal X=L^\infty(G,m;\mathbb R),
$$

let $\mathscr R:\mathcal X\to\mathbb R^r$ be a finite-dimensional real-linear readout, and let

$$
T:\mathcal X\to\mathcal X
$$

be a specified real-linear successor operation. Write $T^0=\operatorname{id}$ and, for an integer horizon $H\ge0$, define

$$
\mathscr R^{[H]}(v)
 =\bigl(\mathscr R(v),\mathscr R(Tv),\ldots,\mathscr R(T^Hv)\bigr)
 \in(\mathbb R^r)^{H+1}.
\tag{163.1}
$$

The corresponding finite-horizon calibrated kernel is

$$
W_{\mathscr R,T}^{(H)}
 =V\cap\ker\mathscr R^{[H]}
 =V\cap\bigcap_{j=0}^{H}\ker(\mathscr R\circ T^j).
\tag{163.2}
$$

No continuity, positivity or physical realizability of $T$ is assumed; only its stated linear action on the same $L^\infty$ classes is used.

**Proposition 163.2 (successor coordinates through any finite horizon still admit energy collapse).** Let $B_n\subset G$ be Borel sets with $m(B_n)>0$ and

$$
\int_{B_n}g^2\,dm\longrightarrow0.
\tag{163.3}
$$

For every finite $H$ there are bounded real Borel functions $v_n$ such that

$$
 v_n\in W_{\mathscr R,T}^{(H)},
 \qquad \|v_n\|_\infty=1,
 \qquad \operatorname{supp}(v_n)\subset B_n,
 \qquad
 0<q(v_n)\le c\int_{B_n}g^2\,dm\longrightarrow0.
\tag{163.4}
$$

*Proof.* The target of the combined linear map

$$
\Phi_H
 =\bigl(\Lambda_{134},\mathscr R,\mathscr R\circ T,\ldots,\mathscr R\circ T^H\bigr)
$$

has dimension $64+r(H+1)$. Put

$$
N=64+r(H+1)+1.
$$

By nonatomicity, each positive-measure $B_n$ contains $N$ pairwise disjoint Borel subsets $A_{n,1},\ldots,A_{n,N}$ of positive measure. Their indicators span an $N$-dimensional space $F_n$. Rank-nullity gives a nonzero $v_n\in\ker(\Phi_H|_{F_n})$. Scale its coefficients so that their maximum absolute value is one. Disjointness gives $\|v_n\|_\infty=1$, and $v_n$ is supported in $B_n$. The kernel equations put it in $V$ and annihilate every $\mathscr R\circ T^j$ for $0\le j\le H$. Proposition 134.2 gives $q(v_n)>0$, while the $L^2$ contraction of $T_{d/2}$ and $|v_n|\le1$ give

$$
0<q(v_n)
 =c\|T_{d/2}(gv_n)\|_2^2
 \le c\|gv_n\|_2^2
 \le c\int_{B_n}g^2\,dm.
$$

This proves (163.4). $\square$

**Corollary 163.3 (finite-horizon successor data have zero coercivity infimum).** For every finite-dimensional $\mathscr R$ and every finite $H$,

$$
\inf\left\{q(v):v\in W_{\mathscr R,T}^{(H)},\ \|v\|_\infty=1\right\}=0.
\tag{163.5}
$$

Thus adjoining the current readout and any prescribed finite list of its successor readouts cannot create a positive lower bound for the weighted heat energy on the full calibrated kernel. If $m(B_n)\to0$, the sequence in Proposition 163.2 is also weak-star null in $L^\infty(m)$ by the argument of (162.5). This is a finite-horizon statement; it does not control an infinite or nonlinear readout.

**Proposition 163.4 (the successor-factorization fibre test).** Let $X\subseteq\mathcal X$ be a linear source domain with $T(X)\subseteq X$, and let $S=\mathscr R(X)$. There exists a map

$$
\overline T:S\to S,
\qquad
\mathscr R\circ T=\overline T\circ\mathscr R\quad\text{on }X,
\tag{163.6}
$$

if and only if

$$
\mathscr R(x)=\mathscr R(x')
\ \Longrightarrow\
\mathscr R(Tx)=\mathscr R(Tx')
\qquad(x,x'\in X).
\tag{163.7}
$$

*Proof.* The implication is immediate from (163.6). Conversely, define $\overline T(\mathscr R(x))=\mathscr R(Tx)$. Condition (163.7) makes this definition independent of the chosen representative, and $T(X)\subseteq X$ puts its value in $S$. $\square$

When $X=V$ and $T(V)\subseteq V$, (163.7) is exactly the calibrated-kernel version of the R5-007 successor-closure criterion. If it fails, $x,x'$ are a same-current, different-successor witness. More concretely, it is enough to find

$$
 v\in V\cap\ker\mathscr R
 \quad\text{with}\quad
 \mathscr R(Tv)\ne0;
\tag{163.8}
$$

then $0$ and $v$ have identical current readout and different next readout. If $T$ does not preserve $V$, the same witness still certifies failure of factorization on the calibrated domain, with the successor readout regarded as taking values in $\mathbb R^r$ rather than in $\mathscr R(V)$.

**Corollary 163.5 (closure is not staticity).** Even when (163.7) holds and $\overline T$ is well-defined, it only says that the specified successor readout descends to the current summary. It does not say $\overline T$ is the identity, that $T$ fixes any state, or that a derivative vanishes. Conversely, failure of (163.7) is an information-fibre failure, not a proof that no larger summary or memory variable can close the successor. Proposition 163.2 shows that, for every fixed finite horizon, adding the missing successor coordinates still leaves normalized directions with arbitrarily small positive $q$.

The source-specific statements (163.1)–(163.8) use only finite-dimensionality of the appended readout, real linearity of the specified successor, nonatomicity, rank-nullity, the $L^2$ contraction of $T_{d/2}$ and Proposition 134.2. They do not construct a nonlinear residual-zero tuple, a legal simplex family, an exact H43 partition, a terminal compensator, an SRS-20 or $F_{64}$ witness, a physical successor operation or a Lean/kernel theorem.

## 追加锚（本行以下为增补区）

## 164. Countable successor stacks: prefix escape and the exact-kernel boundary

Section 163 treats one finite successor horizon at a time. A countable stack of successor coordinates has a stricter exact kernel, so the finite-horizon argument must be diagonalized with its quantifiers kept visible. The next statements give the diagonal finite-prefix escape and record why it does not by itself produce a vector silent to every coordinate.

**Definition 164.1 (finite prefixes of a countable readout stack).** Let

$$
\mathcal X=L^\infty(G,m;\mathbb R),
\qquad V=\ker\Lambda_{134},
$$

and let $(\mathscr R_j)_{j\ge0}$ be a countable family of real-linear maps

$$
\mathscr R_j:\mathcal X\longrightarrow\mathbb R^{r_j},
\qquad r_j<\infty.
$$

Define

$$
W_{\le n}=V\cap\bigcap_{j=0}^{n}\ker\mathscr R_j,
\qquad
W_\infty=V\cap\bigcap_{j=0}^{\infty}\ker\mathscr R_j.
\tag{164.1}
$$

When a specified real-linear successor $T$ is available, the successor stack is the special case $\mathscr R_j=\mathscr R\circ T^j$ whenever these compositions are defined on $\mathcal X$.

**Proposition 164.2 (finite-prefix diagonal escape).** Let $B_n\subset G$ be Borel sets with $m(B_n)>0$ and

$$
\int_{B_n}g^2\,dm\longrightarrow0.
\tag{164.2}
$$

Then there are bounded real Borel functions $v_n$ such that

$$
\begin{gathered}
v_n\in W_{\le n},
\qquad \|v_n\|_\infty=1,
\qquad \operatorname{supp}(v_n)\subset B_n,\\
0<q(v_n)\le c\int_{B_n}g^2\,dm\longrightarrow0.
\end{gathered}
\tag{164.3}
$$

Moreover, for every fixed $j$, $\mathscr R_j(v_n)=0$ for all $n\ge j$. If $m(B_n)\to0$, the sequence is weak-star null in $L^\infty(m)$.

*Proof.* Put

$$
N_n=64+\sum_{j=0}^{n}r_j+1
$$

and choose $N_n$ pairwise disjoint Borel subsets $A_{n,1},\ldots,A_{n,N_n}$ of positive measure inside $B_n$. Their indicators span an $N_n$-dimensional subspace $F_n$ of $\mathcal X$. The combined map

$$
\Phi_n=(\Lambda_{134},\mathscr R_0,\ldots,\mathscr R_n):
F_n\longrightarrow
\mathbb R^{64+\sum_{j=0}^{n}r_j}
$$

has a nonzero kernel by rank-nullity. Choose a nonzero $v_n$ in that kernel and scale its indicator coefficients so that their maximum absolute value is one. Disjointness gives $\|v_n\|_\infty=1$ and $\operatorname{supp}(v_n)\subset B_n$; the kernel equations give $v_n\in W_{\le n}$ and the eventual vanishing of each fixed coordinate. Proposition 134.2 gives $q(v_n)>0$. Since $|v_n|\le1$, the Markov $L^2$ contraction gives

$$
0<q(v_n)=c\|T_{d/2}(gv_n)\|_2^2
\le c\|gv_n\|_2^2
\le c\int_{B_n}g^2\,dm,
$$

which proves (164.3). When $m(B_n)\to0$, for every $h\in L^1(m)$,

$$
\left|\int_G h v_n\,dm\right|
\le\int_{B_n}|h|\,dm\longrightarrow0
$$

by absolute continuity of the integral. $\square$

**Corollary 164.3 (finite-prefix coercivity remains zero).** For every $n$,

$$
\inf\left\{q(v):v\in W_{\le n},\ \|v\|_\infty=1\right\}=0.
\tag{164.4}
$$

Indeed, for a fixed $n$ repeat the rank-nullity construction with the finite map $(\Lambda_{134},\mathscr R_0,\ldots,\mathscr R_n)$ on a sequence of positive-measure sets whose $g^2$-mass tends to zero. The same estimate as in (164.3) gives arbitrarily small positive values of $q$ in $W_{\le n}$. The diagonal sequence from Proposition 164.2 is eventually invisible to every fixed finite subset of the countable stack, while retaining unit $L^\infty$ norm and positive energy at each finite index. If $\mathscr R_j=\mathscr R\circ T^j$, this says that every fixed finite list of successor coordinates vanishes along the sequence after a finite stage. It does not say that any $v_n$ belongs to $W_\infty$.

**Proposition 164.4 (finite-prefix escape does not imply a common infinite escape).** There is an abstract positive quadratic form and a countable readout stack for which every finite-prefix unit sphere has zero infimum, while the exact infinite kernel has a positive coercivity infimum. Take

$$
\mathcal Y=\ell^\infty(\mathbb N_0),
\qquad
Q(x)=x_0^2+\sum_{k=1}^{\infty}2^{-k}x_k^2,
$$

and let $\mathscr S_j(x)=x_{j+1}$. Then

$$
Y_{\le n}=\bigcap_{j=0}^{n}\ker\mathscr S_j
$$

contains every unit vector $e_k$ with $k\ge n+2$. Hence

$$
\inf\{Q(x):x\in Y_{\le n},\ \|x\|_\infty=1\}=0,
$$

and the particular choice $e_{n+2}$ gives the displayed diagonal bound

$$
Q(e_{n+2})=2^{-(n+2)}\longrightarrow0.
$$

On the other hand,

$$
Y_\infty=\bigcap_{j=0}^{\infty}\ker\mathscr S_j
 =\operatorname{span}\{e_0\},
$$

and every unit vector in $Y_\infty$ has $Q(x)=1$. Thus

$$
\inf\{Q(x):x\in Y_\infty,\ \|x\|_\infty=1\}=1.
\tag{164.5}
$$

This is a logical separation example, not a model of the FIB heat form. It shows that the passage from all finite prefixes to the common infinite kernel requires an additional compactness, correction, or exact-common-kernel argument.

**Corollary 164.5 (the remaining infinite-horizon obligation).** Proposition 164.2 proves coordinatewise finite-prefix escape for any countable family of finite-dimensional successor readouts. To obtain a genuine FIB infinite-horizon energy-collapse statement, one must additionally construct either

1. a sequence in $W_\infty$ with unit norm and shrinking $g^2$-mass, or
2. an exact correction procedure that converts the prefix sequence into $W_\infty$ while preserving nonzero norm and the energy estimate.

Neither condition follows from rank-nullity applied separately to the finite prefixes. Consequently, a countable successor stack may still control the full calibrated kernel even though every finite horizon has zero coercivity infimum. The statements (164.1)--(164.5) do not construct a physical successor, a nonlinear residual-zero tuple, a legal simplex family, an exact H43 partition, a terminal compensator, an SRS-20 or $F_{64}$ witness, or a Lean/kernel theorem.

## 165. The orbit-closure criterion for a countable successor stack

Section 164 leaves the exact common kernel as the missing infinite-horizon object. A useful distinction is available when the successor readout extends to $L^2(m)$ and its coordinates have Hilbert-space representers. In that case the countable stack is governed by the closed heat orbit of those representers; finite-prefix rank-nullity does not have to be used as a proxy for the exact intersection.

**Definition 165.1 (an $L^2$-representable successor stack).** Retain the original probability space $(G,m)$, the calibrated bounded kernel

$$
V=\ker\Lambda_{134}\subset L^\infty(G,m;\mathbb R),
$$

and put $H=L^2(G,m;\mathbb R)$. Let $P=T_d$ be the original self-adjoint contraction on $H$. Suppose a finite-dimensional readout $R$ has scalar coordinates

$$
R_k(v)=\langle v,\psi_k\rangle_H,
\qquad 1\le k\le r,
$$

for fixed $\psi_k\in H$, and define the specified successor stack by

$$
R_j=R\circ P^j,\qquad j\ge0.
$$

Let

$$
\mathcal C=\overline{\operatorname{span}_{\mathbb R}
 \{P^j\psi_k:j\ge0,\ 1\le k\le r\}}^{\,H}.
\tag{165.1}
$$

The closure is in $H$; no density or cyclicity assumption is built into the definition.

**Proposition 165.2 (exact common-kernel/orbit-closure equivalence).** For every $v\in V$, viewed as its $H$-class,

$$
\bigl(\forall j\ge0,\ R_j(v)=0\bigr)
\quad\Longleftrightarrow\quad
v\in\mathcal C^\perp.
\tag{165.2}
$$

Consequently the exact common infinite kernel of the bounded calibrated classes is

$$
W_\infty
=V\cap L^\infty(G,m;\mathbb R)\cap\mathcal C^\perp,
\tag{165.3}
$$

with the first intersection understood in the original $m$-class sense.

*Proof.* For $v\in V$ and every $j,k$, self-adjointness of $P$ gives

$$
R_j(v)_k
 =\langle P^jv,\psi_k\rangle_H
 =\langle v,P^j\psi_k\rangle_H.
\tag{165.4}
$$

Thus all successor coordinates vanish exactly when $v$ is orthogonal to every generator in (165.1). Orthogonality is preserved under real linear combinations and $H$-limits, so this is equivalent to $v\in\mathcal C^\perp$. Intersecting with the original bounded calibrated domain gives (165.3). The argument uses no compactness of the unit sphere and no assertion that the stack is physically realized. $\square$

**Corollary 165.3 (the cyclicity boundary).** Let

$$
H_{\mathrm{cal}}=\overline{\operatorname{span}_{\mathbb R}V}^{\,H}.
$$

If $H_{\mathrm{cal}}\subseteq\mathcal C$, equivalently the successor readout orbit is dense in the $L^2$ calibration subspace, then $W_\infty=\{0\}$ as a space of $m$-classes. Hence no normalized exact infinite-horizon escape direction exists for that stack. This is a conditional observability statement: it does not assert the required density for the original FIB readout.

Conversely, if $\mathcal C^\perp\cap V$ contains bounded classes supported on Borel sets $B_n$ with

$$
\|v_n\|_\infty=1,
\qquad
\int_{B_n}g^2\,dm\longrightarrow0,
$$

then Proposition 134.2 and the Markov contraction give

$$
0<q(v_n)\le c\int_{B_n}g^2\,dm\longrightarrow0,
$$

and every $v_n$ is silent to the entire countable stack. The corollary identifies the exact remaining construction: it does not manufacture a localized sequence from nonzeroity of $\mathcal C^\perp$ alone.

**Corollary 165.4 (finite prefixes and their limit).** Define

$$
\mathcal C_n=\operatorname{span}_{\mathbb R}
 \{P^j\psi_k:0\le j\le n,\ 1\le k\le r\}.
$$

Then

$$
W_{\le n}=V\cap L^\infty(G,m;\mathbb R)\cap\mathcal C_n^\perp,
\qquad
W_\infty=\bigcap_{n\ge0}W_{\le n},
\tag{165.5}
$$

and $\overline{\bigcup_n\mathcal C_n}=\mathcal C$. The finite-prefix escape of Proposition 164.2 therefore says only that each $\mathcal C_n^\perp$ contains normalized low-energy classes. It supplies no nonzero element of the limiting orthogonal complement $\mathcal C^\perp$ unless an additional orbit-complement or correction argument is proved.

If the readout coordinates are initially given only as real-linear maps on $L^\infty$, the representer hypothesis in Definition 165.1 is an additional bridge: an arbitrary algebraic functional need not extend continuously to $L^2$. In the complex formulation, real and imaginary coordinates must be split before applying the real inner-product calculation above.

The statements (165.1)--(165.5) are an exact functional-analytic boundary for the countable successor question. They do not establish orbit density, a nonzero orbit complement, a physical successor, a nonlinear residual-zero tuple, a legal simplex family, an exact H43 partition, a terminal compensator, an SRS-20 or $F_{64}$ witness, or a Lean/kernel theorem.

## 追加锚（本行以下为增补区）

## 166. The finite $L^2$ representer bridge for the calibrated kernel

Section 165 treats the original first-order kernel $V$ as a bounded-function constraint while the successor orbit is described in $L^2(m)$. For the actual equal-gap readout of Appendix III, the first-order constraints have explicit $L^2(m)$ representers. This identifies the finite calibration plane that must be added to any later successor orbit, without asserting that the orbit preserves $V$ or that a physical successor exists.

**Definition 166.1 (the first-order representer plane).** Retain the complete telescope of Appendix III Definition 134.1 and the real labels $\mathcal L=\{0,1,3,B\}$. Write $H=L^2(G,m;\mathbb R)$, $P=T_d$, and use pointwise multiplication for products of functions. For $\alpha=(y,z,w)\in\mathcal L^3$, define

$$
\begin{aligned}
A_{yzw}&=g\,P(f_z\,P f_w),\\
B_{yzw}&=P(g f_y)\,P f_w,\\
C_{yzw}&=P\!\bigl(f_z\,P(g f_y)\bigr),\\
\psi_{yzw}&=\sigma_y A_{yzw}+\sigma_z B_{yzw}+\sigma_w C_{yzw}.
\end{aligned}
\tag{166.1}
$$

Let

$$
W=\operatorname{span}_{\mathbb R}
\{\psi_{yzw}: (y,z,w)\in\mathcal L^3\}\subset H.
\tag{166.2}
$$

The span is finite-dimensional, with dimension at most $64$. Orthogonal complements below are taken in $H$, while bounded functions are understood as their $m$-classes.

**Proposition 166.2 (explicit representers for all first-order constraints).** For every $\alpha=(y,z,w)\in\mathcal L^3$, the function $\psi_{yzw}$ has a bounded Borel representative and belongs to $H$. For every bounded real Borel $v$,

$$
\ell_{yzw}(v)=\langle v,\psi_{yzw}\rangle_H.
\tag{166.3}
$$

Consequently, with $V=\ker\Lambda$ as in Appendix III Definition 134.1,

$$
V=L^\infty(G,m;\mathbb R)\cap W^\perp.
\tag{166.4}
$$

*Proof.* The inherited source estimate in Appendix III (134.4) gives $g=P g_d$, while Theorem 133.2 gives $g_d\in L^\infty(m)$. The Markov $L^\infty$-contraction of $P$ therefore gives $g\in L^\infty(m)$. Equation (134.8) gives $f_y\in L^\infty(m)$ for every label. Applying the same contraction to the products in (166.1) shows that $A_{yzw}$, $B_{yzw}$, and $C_{yzw}$ are bounded Borel $m$-classes, hence belong to $H$. Their displayed Borel representatives may be chosen simultaneously for the finite set of labels.

For the first term of (134.11), self-adjointness of $P$ gives

$$
\mathcal C(v,f_z,f_w)
 =\langle g v,P(f_z P f_w)\rangle_H
 =\langle v,A_{yzw}\rangle_H.
\tag{166.5}
$$

For the second term, move $P$ across the pairing once:

$$
\mathcal C(f_y,v,f_w)
 =\langle g f_y,P(v P f_w)\rangle_H
 =\langle P(g f_y),v P f_w\rangle_H
 =\langle v,B_{yzw}\rangle_H.
\tag{166.6}
$$

For the third term, move $P$ across the pairing twice:

$$
\begin{aligned}
\mathcal C(f_y,f_z,v)
 &=\langle g f_y,P(f_z P v)\rangle_H\\
 &=\langle P(g f_y),f_z P v\rangle_H\\
 &=\langle P(f_z P(g f_y)),v\rangle_H
 =\langle v,C_{yzw}\rangle_H.
\end{aligned}
\tag{166.7}
$$

Substitution of (166.5)--(166.7) into the definition of $\ell_{yzw}$ in (134.11) proves (166.3). All pairings are legitimate because $m$ is a probability and every displayed factor is bounded. The simultaneous vanishing of the $64$ coordinates is therefore exactly orthogonality to $W$, which proves (166.4). $\square$

**Corollary 166.3 (the calibrated plane and a successor orbit).** Let

$$
H_{\mathrm{cal}}=\overline{\operatorname{span}_{\mathbb R}V}^{\,H}.
\tag{166.8}
$$

Then $H_{\mathrm{cal}}\subseteq W^\perp$. Equality requires an additional density statement and is not supplied by the finite representer calculation. If a finite $L^2(m)$-representable readout has representers $\psi_1,\ldots,\psi_r$ and its specified successor stack is $R_j=R\circ P^j$, put

$$
\mathcal C_R=\overline{\operatorname{span}_{\mathbb R}
\{P^j\psi_k:j\ge0, 1\le k\le r\}}^{\,H}.
\tag{166.9}
$$

Then the exact common kernel from Section 165 can be written as

$$
W_\infty
 =L^\infty(G,m;\mathbb R)\cap
 \overline{W+\mathcal C_R}^{\,H\,\perp}.
\tag{166.10}
$$

Indeed, (166.4) supplies the condition $v\perp W$, while Proposition 165.2 supplies $v\perp\mathcal C_R$; orthogonality to both closed subspaces is equivalent to orthogonality to the closure of their algebraic sum. Formula (166.10) is an interface identity only. It does not prove that $\mathcal C_R$ is dense in $H_{\mathrm{cal}}$, that $\mathcal C_R$ has a nonzero bounded localized complement, or that the successor action maps $V$ into $V$. It also does not construct a physical successor, a nonlinear residual-zero family, a legal simplex partition, an exact $H43$ partition, a terminal compensator, an $SRS\text{-}20$ or $F_{64}$ witness, or a Lean/kernel theorem.

The deductions (166.1)--(166.10) are source-specific consequences of the original bounded equal-gap readout and the self-adjoint heat contraction. They are not a claim that the representer bridge, the successor orbit, or its physical realization is present in the original model beyond the hypotheses displayed here.

## 追加锚（本行以下为增补区）

## 167. Bounded calibration closure and the finite residual test

Section 166 identifies the first-order calibration plane through bounded $L^2(m)$ representers, but leaves two different questions separate: whether bounded calibrated classes are dense in the Hilbert orthogonal complement, and whether the heat operator preserves that bounded calibrated class. The next propositions close the first logical bridge and reduce the second to a finite residual Gram matrix. They do not evaluate that matrix for the actual 64 representers.

**Definition 167.1 (the bounded calibration space).** Retain all hypotheses and notation of Section 166. Thus $H=L^2(G,m;\mathbb R)$, $W\subset H$ is the finite span of the bounded representers from (166.1), and put

$$
V_\infty=L^\infty(G,m;\mathbb R)\cap W^\perp.
\tag{167.1}
$$

All functions and orthogonality relations are understood as $m$-classes. The finite-dimensionality of $W$ implies that it has a bounded $m$-class basis after removing linear dependencies from the at most $64$ generators.

**Proposition 167.2 (bounded calibrated classes are Hilbert-dense).** With the notation of Definition 167.1,

$$
\overline{V_\infty}^{\,H}=W^\perp.
\tag{167.2}
$$

*Proof.* Let $x\in W^\perp$. Since $m(G)=1$, bounded truncations

$$
x_n=\max(-n,\min(x,n))
$$

belong to $L^\infty(G,m;\mathbb R)$ and converge to $x$ in $H$. Let $\Pi_W$ be the orthogonal projection onto $W$. Choose a bounded basis $w_1,\ldots,w_r$ of $W$. The coefficients of $\Pi_Wx_n$ are finite linear combinations of the pairings $\langle x_n,w_i\rangle_H$, so $\Pi_Wx_n\in W\subset L^\infty$. Hence

$$
v_n=x_n-\Pi_Wx_n\in V_\infty.
$$

Because $\Pi_Wx=0$ and $\Pi_W$ is a contraction,

$$
\|v_n-x\|_H
\le \|x_n-x\|_H+\|\Pi_W(x_n-x)\|_H
\le 2\|x_n-x\|_H\longrightarrow0.
$$

Thus $W^\perp\subseteq\overline{V_\infty}^{\,H}$; the reverse inclusion follows from $V_\infty\subseteq W^\perp$. $\square$

**Proposition 167.3 (successor preservation and calibration-plane invariance).** Let $P:H\to H$ be bounded and self-adjoint, and suppose $P(L^\infty(G,m;\mathbb R))\subseteq L^\infty(G,m;\mathbb R)$. Then

$$
P(V_\infty)\subseteq V_\infty
\quad\Longleftrightarrow\quad
P(W)\subseteq W.
\tag{167.3}
$$

*Proof.* Assume first that $P(V_\infty)\subseteq V_\infty$. Proposition 167.2 and boundedness of $P$ give $P(W^\perp)\subseteq W^\perp$. If $w\in W$ and $u\in W^\perp$, then self-adjointness gives

$$
\langle Pw,u\rangle_H=\langle w,Pu\rangle_H=0.
$$

Therefore $Pw\in(W^\perp)^\perp=W$, proving $P(W)\subseteq W$.

Conversely, let $v\in V_\infty$. The $L^\infty$-preservation hypothesis gives $Pv\in L^\infty$. For $w\in W$, self-adjointness and $P(W)\subseteq W$ give

$$
\langle Pv,w\rangle_H=\langle v,Pw\rangle_H=0.
$$

Thus $Pv\in W^\perp$, and hence $Pv\in V_\infty$. $\square$

For the original heat operator, the hypotheses of Proposition 167.3 are inherited: $P=T_d=e^{-dK}$ is bounded self-adjoint on $H$, and the Markov semigroup preserves bounded real functions. Proposition 167.3 is therefore a conditional closure equivalence, not a claim that the actual Section 166 plane is already $P$-invariant.

**Proposition 167.4 (finite residual Gram criterion).** Let $w_1,\ldots,w_r$ be an $H$-independent bounded basis of $W$, and define

$$
G_{ij}=\langle w_i,w_j\rangle_H,qquad
K_{ij}=\langle w_i,Pw_j\rangle_H,qquad
D_{ij}=\langle Pw_i,Pw_j\rangle_H.
\tag{167.4}
$$

Then $G$ is positive definite and

$$
P(W)\subseteq W
\quad\Longleftrightarrow\quad
D-K^{\mathsf T}G^{-1}K=0.
\tag{167.5}
$$

*Proof.* Let $S:\mathbb R^r\to H$ be the synthesis map $Se_j=w_j$. Then $G=S^*S$, $K=S^*PS$, and $D=(PS)^*PS$. Self-adjointness of $P$ makes $K$ symmetric. The orthogonal projection onto $W$ is

$$
\Pi_W=SG^{-1}S^*.
$$

Consequently the matrix on the right of (167.5) is the Gram matrix of the projection residuals:

$$
D-K^{\mathsf T}G^{-1}K
 =(PS)^*(I-\Pi_W)PS.
\tag{167.6}
$$

It vanishes exactly when every $(I-\Pi_W)Pw_j$ vanishes, which is equivalent to $P w_j\in W$ for each basis vector and hence to $P(W)\subseteq W$. For the original 64 generators one must first pass to an $H$-independent basis (or use the corresponding Moore--Penrose projection); the possibly singular raw 64-by-64 Gram matrix cannot be inverted. $\square$

## 168. Closure boundary and applicability

The density and residual statements above are ordinary Hilbert-space consequences of the inherited probability, bounded representers, self-adjoint heat operator and Markov boundedness. The residual matrix uses exact $m$-pairings; a numerical approximation, the compressed matrix $K$ alone, or the existence of the representer formula does not establish its vanishing.

The current result does not assert $P(W)\subseteq W$ for the concrete Section 166 plane, $P(V_\infty)=V_\infty$, orbit density, a nonzero bounded common-kernel sequence, a physical successor, a nonlinear residual-zero family, a legal simplex or $H43$ partition, a terminal compensator, $SRS\text{-}20$, $F_{64}$, or a Lean/kernel theorem. Those questions require their own exact calculations and realization bridges.



## 169. The concrete representer plane is not heat-invariant

Section 168 reduces the actual closure question to a finite residual Gram matrix. The source-start law supplies an exact obstruction to that closure: the first-order representer plane already contains a positive-time source density, and no such density can have a finite-dimensional heat orbit.

**Lemma 169.1 (a positive-time source density has no polynomial relation).** Let $t,d>0$ and let $g_t$ be the source-start density of Appendix III Theorem 117.2. There is no nonzero real polynomial $q$ such that

$$
q(T_d)g_t=0\quad\text{in }L^2(G,m).
\tag{169.1}
$$

*Proof.* Write $T_s=e^{-sK}$ and let $E_K$ be the spectral resolution of the nonnegative self-adjoint $K$. If (169.1) held, then the spectral measure of $g_t$ would be supported on

$$
\Lambda=\{\lambda\ge0:q(e^{-d\lambda})=0\}.
\tag{169.2}
$$

This set is finite: the nonzero polynomial $q$ has finitely many roots, and $\lambda\mapsto e^{-d\lambda}$ is one-to-one; a possible root at zero is not attained at a finite $\lambda$. Thus

$$
g_t=\sum_{\lambda\in\Lambda}g_{t,\lambda},
\qquad g_{t,\lambda}=E_K(\{\lambda\})g_t.
\tag{169.3}
$$

For $0<s<t$, the source propagation identity gives $g_t=T_{t-s}g_s$. Since $T_{t-s}$ is injective and commutes with $q(T_d)$,

$$
0=q(T_d)g_t=T_{t-s}q(T_d)g_s
\quad\Longrightarrow\quad q(T_d)g_s=0.
\tag{169.4}
$$

The same finite spectral decomposition therefore holds for every $g_s$. On the $\lambda$-eigenspace, $T_{t-s}$ is multiplication by $e^{-(t-s)\lambda}$, so

$$
g_s=\sum_{\lambda\in\Lambda}e^{(t-s)\lambda}g_{t,\lambda}
\longrightarrow
r:=\sum_{\lambda\in\Lambda}e^{t\lambda}g_{t,\lambda}
\quad\text{in }L^2(m)\quad(s\downarrow0).
\tag{169.5}
$$

For every $\psi\in C_c(G)$, the $L^2$ convergence and $m(G)=1$ give

$$
\int_G\psi r\,dm
=\lim_{s\downarrow0}\int_G\psi g_s\,dm.
\tag{169.6}
$$

The right side is $\lim_{s\downarrow0}\mathbb E_e[\psi(Z_s)]=\psi(e)$, because the retained diffusion starts at $e$ and has continuous paths. Hence the finite measure $r\,m$ equals $\delta_e$ on $C_c(G)$. This is impossible: $r\in L^2(m)\subset L^1(m)$ while $m(\{e\})=0$, so $r\,m$ is absolutely continuous with respect to $m$ and cannot be the point mass $\delta_e$. $\square$

**Proposition 169.2 (the actual Section 166 plane is not $P$-invariant).** For every original finite $a,\eta,d>0$, with $P=T_d$, $g=g_{2d}$ and $W$ the concrete representer span of Section 166,

$$
P(W)\not\subseteq W.
\tag{169.7}
$$

*Proof.* In the fixed readout of Appendix III Definition 134.1, $f_B=1/4$, $P1=1$, $\sigma_0=1$ and $\sigma_B=0$. Therefore the representer formula (166.1) gives the exact identity

$$
\psi_{0BB}=g\,P(f_B P f_B)=\frac{g}{16}.
\tag{169.8}
$$

In particular $g/16\in W$. If $P(W)\subseteq W$, finite-dimensionality of $W$ would make the orbit $(P^ng)_{n\ge0}$ linearly dependent. Equivalently, some nonzero polynomial $q$ would satisfy $q(P)g=0$, contradicting Lemma 169.1 with $t=2d$. Thus (169.7) holds. $\square$

**Corollary 169.3 (nonzero actual residual and failure of bounded calibrated closure).** Let $w_1,\ldots,w_r$ be any $L^2(m)$-independent bounded basis of the concrete Section 166 plane, and let $G,K,D$ be the exact matrices of (167.4). Then

$$
D-K^{\mathsf T}G^{-1}K\ne0,
\tag{169.9}
$$

and, for $V_\infty=L^\infty(G,m;\mathbb R)\cap W^\perp$,

$$
P(V_\infty)\not\subseteq V_\infty.
\tag{169.10}
$$

Indeed, (169.9) is the contrapositive of the exact residual criterion (167.5), while (169.10) follows from the closure equivalence (167.3). The conclusion is an exact non-invariance statement for the concrete calibration plane; it does not evaluate individual residual entries, construct a physical successor, prove orbit density, or supply a nonlinear residual-zero family, a legal simplex or $H43$ partition, a terminal compensator, $SRS\text{-}20$, $F_{64}$, or a Lean/kernel theorem.

The proof uses only the original source-start density and path law, the injective self-adjoint heat semigroup, the fixed Section 166 readout identities and finite-dimensionality of $W$. It resolves the actual closure boundary left open in Section 168 without a numerical approximation.

## 170. A rotation-odd exact common kernel for the full successor stack

Section 169 rules out finite-dimensional closure of the concrete representer plane, but it does not by itself produce a nonzero bounded class satisfying every successor readout. The original half-turn symmetry supplies such a class family. It acts on the actual source, measure and heat operator, so the construction remains inside the retained model.

**Proposition 170.1 (rotation-odd classes annihilate the full linear successor stack).** Let $J=R_\pi$ be the half-turn in the $(x,y)$ coordinates, and let $J^*$ denote pullback on functions. Use the pointwise rotation-invariant representative $\beta$ of $g_d$ supplied by Appendix III Proposition 136.2 in the formulas (134.7). Since $[\beta]=[b]$, this replacement leaves the $L^2(m)$ classes of all $f_y$, and hence the plane $W$ of (166.2), unchanged. Define

$$
V_-:=\{v\in L^\infty(G,m;\mathbb R):J^*v=-v\ \text{$m$-a.e.}\}.
\tag{170.1}
$$

Then

$$
V_-\subseteq W_\infty
 =L^\infty(G,m;\mathbb R)\cap
 \overline{W+\mathcal C_R}^{\,H\,\perp},
\qquad
\mathcal C_R=\overline{\operatorname{span}_{\mathbb R}
 \{P^j\psi_{yzw}:j\ge0,\ (y,z,w)\in\mathcal L^3\}}^{\,H}.
\tag{170.2}
$$

In particular, every rotation-odd class satisfies all first-order constraints and all their specified heat-successor constraints.

*Proof.* Appendix III §136 gives that $m$, $g_s$ and $T_s$ are invariant under the circle action and that $T_s$ commutes with its pullbacks. With the invariant representative $\beta$, the functions $g$ and $f_y$ are $J^*$-invariant. Each representer in (166.1) is obtained from these functions by multiplication and by $P=T_d$, so

$$
J^*\psi_{yzw}=\psi_{yzw}.
\tag{170.3}
$$

Commutation gives $J^*P^j\psi_{yzw}=P^j\psi_{yzw}$ for every $j$. If $v\in V_-$ and $\psi$ is any one of these invariant classes, invariance of $m$ and the change of variables $x\mapsto Jx$ give

$$
\langle v,\psi\rangle_H
 =\langle J^*v,J^*\psi\rangle_H
 =-\langle v,\psi\rangle_H,
$$

so the pairing is zero. Thus $v$ is orthogonal to $W$ and to $\mathcal C_R$, hence to their closed sum, proving (170.2). The identity (166.4) and the successor-kernel formula (166.10) give the stated interpretation. $\square$

**Corollary 170.2 (an infinite-dimensional common kernel with collapsing heat energy).** The space $V_-$, and therefore $W_\infty$, is infinite-dimensional. More explicitly, there are linearly independent bounded real Borel functions $v_n$ such that

$$
v_n\in W_\infty,\qquad \|v_n\|_\infty=1,
\qquad 0<q_{003}(v_n)
 \le c\int_{B_n}g^2\,dm\longrightarrow0,
\tag{170.4}
$$

where each $B_n$ is the support of $v_n$ up to an $m$-null set.

*Proof.* Choose a Borel set $U\subset G\setminus N$ with $m(U)>0$ and $U\cap J U=\varnothing$; such a set exists in a sufficiently small neighborhood of any point off the rotation axis, using the full local support of $m$ from Appendix III §136. Choose pairwise disjoint Borel subsets $A_n\subset U$ with $m(A_n)>0$ and $m(A_n)\to0$, and put

$$
B_n=A_n\cup J A_n,
\qquad v_n=\mathbf1_{A_n}-\mathbf1_{J A_n}.
\tag{170.5}
$$

The sets in (170.5) are disjoint in each pair, $J^*v_n=-v_n$, and $\|v_n\|_\infty=1$. The pairwise disjointness of the $A_n$ and of their images makes the $v_n$ linearly independent. Since $m$ is $J$-invariant, $m(B_n)\to0$; since $g\in L^2(m)$, absolute continuity gives $\int_{B_n}g^2\,dm\to0$. Proposition 170.1 puts every $v_n$ in $W_\infty$. Finally Proposition 134.2 and the $L^2$ contraction of $T_{d/2}$ give

$$
0<q_{003}(v_n)=c\|T_{d/2}(gv_n)\|_2^2
\le c\|gv_n\|_2^2
 =c\int_{B_n}g^2\,dm\longrightarrow0.
$$

Thus the full infinite-horizon common kernel contains nonzero bounded directions of unit sup norm with vanishing heat-energy infimum. This does not construct a physical successor, prove density of the successor orbit, produce a nonlinear residual-zero family, a legal simplex or $H43$ partition, or settle $SRS\text{-}20$, $F_{64}$ or a Lean/kernel theorem. $\square$

By Proposition 167.2, $H_{\mathrm{cal}}=W^\perp$ for the concrete first-order kernel. The functions above lie in $W^\perp\cap\mathcal C_R^\perp$ and are nonzero, so

$$
\overline{\mathcal C_R}^{\,H}\ne H_{\mathrm{cal}}.
\tag{170.6}
$$

Thus the concrete rotation-invariant successor stack is not dense in the calibrated Hilbert space; this conclusion is specific to the stated Section 166 readout and does not extend to an arbitrary successor or a physical realization.

## 171. Exact compensation of one nonlinear residual coordinate

The rotation-odd common kernel from Section 170 makes every specified linear successor readout vanish, but Proposition 158.2 leaves a strictly positive quadratic $(0,0,3)$ term. That term can be cancelled exactly by a legal terminal correction on a positive-measure invariant set. The construction records the compensator cost and makes no claim about the remaining residual coordinates.

**Proposition 171.1 (a legal terminal compensator for the $003$ coordinate).** Replace the representative $b$ in (134.7) by the pointwise rotation-invariant representative $\beta$ of Appendix III Proposition 136.2; all $m$-classes and residual coordinates are unchanged. Let $0\ne v\in V=\ker\Lambda_{134}$ be bounded and real. Then there are a Borel set $E\subset G$ invariant under the circle action, a number $\varepsilon>0$, and positive scalars $s_t$ for $0<|t|<\varepsilon$ such that, with

$$
w_t=-s_t\mathbf 1_E
\tag{171.1}
$$

the tuple $u^{(t;v,w_t)}$ of (158.1) is a pointwise legal simplex tuple on all of $G$ and

$$
\Delta\bigl(u^{(t;v,w_t)}\bigr)_{003}=0.
\tag{171.2}
$$

Moreover, if

$$
A=q_{003}(v),\quad
B=\mathcal C(f_0,f_0,\mathbf 1_E),\quad
L=\mathcal C(v,f_0,\mathbf 1_E)+\mathcal C(f_0,v,\mathbf 1_E),\quad
C=\mathcal C(v,v,\mathbf 1_E),
\tag{171.3}
$$

then $A>0$, $B>0$, and one may choose

$$
s_t=\frac{A}{B+tL+t^2C},
\qquad
s_t\longrightarrow\frac AB>0\quad(t\to0).
\tag{171.4}
$$

Thus the actual perturbation $t^2w_t$ tends to zero in $L^\infty$, while the compensator coefficient itself has a strictly positive limiting cost.

*Proof.* Since $f_3=c\beta>0$ everywhere and $m(G)=1$, there is a $\delta>0$ for which the invariant Borel set

$$
E=\{x:f_3(x)\ge\delta\}
\tag{171.5}
$$

has positive $m$-measure. Let

$$
\psi_0=P\bigl(f_0P(gf_0)\bigr).
$$

The positivity-improvement argument in Proposition 158.3 gives $\psi_0>0$ almost everywhere, so

$$
B=\int_E\psi_0\,dm>0.
\tag{171.6}
$$

Proposition 134.2 gives $A=q_{003}(v)>0$. The boundedness of $v$, $f_0$, $g$ and the $L^2$ contraction of $P$ makes $L$ and $C$ finite. Hence for all sufficiently small $|t|$,

$$
B+tL+t^2C>B/2.
\tag{171.7}
$$

Define $s_t$ by (171.4). Substitution of (171.1) into the exact expansion (158.2) gives

$$
\begin{aligned}
\Delta\bigl(u^{(t;v,w_t)}\bigr)_{003}
 &=t^2\left[A-s_tB\right]
   -t^3s_tL-t^4s_tC\\
 &=t^2\left[A-s_t(B+tL+t^2C)\right]=0.
\end{aligned}
\tag{171.8}
$$

Because $s_t\to A/B$, reduce $\varepsilon$ so that

$$
|t|\,\|v\|_\infty\le\frac14,
\qquad
t^2s_t\le\min\left\{\delta,\frac14\right\}
\tag{171.9}
$$

for $0<|t|<\varepsilon$. Equation (134.8) then gives $u_0,u_1\ge0$. On $E$, $u_3=f_3-t^2s_t\ge0$, and off $E$ it equals $f_3>0$. Finally $u_B=1/4+t^2s_t$ lies between $0$ and $1$; all four coordinates sum to one by (158.1). Thus the tuple is legal on all of $G$. The limit in (171.4) is immediate. This proves (171.2) and the stated cost. $\square$

In particular, every nonzero rotation-odd class supplied by Proposition 170.1 admits this exact one-coordinate compensation. The result cancels only the $003$ coordinate; it does not cancel the other $63$ coordinates, establish a full-law partition, produce an $H43$ witness, or settle SRS$\text{-}20$, $F_{64}$, a physical successor or a Lean/kernel theorem.

**Corollary 171.2 (variable-ray sharpness along the rotation-odd escape).** Let $(v_n)$ be the sequence of Corollary 170.2, with supports $B_n$ and $A_n=q_{003}(v_n)$. There is one fixed sufficiently small nonzero $t$ and legal tuples

$$
u^{(n)}=u^{(t;v_n,w_n)},
\qquad w_n=-s_n\mathbf1_E,
\tag{171.10}
$$

such that

$$
\Delta(u^{(n)})_{003}=0,
\qquad \|\Delta(u^{(n)})\|_{\max}\longrightarrow0,
\qquad \|w_n\|_\infty\longrightarrow0.
\tag{171.11}
$$

Thus the full residual map has infimum zero on legal simplex tuples with the entire countable linear successor stack still exactly silent. This is an approximation statement; it does not produce a tuple with all sixty-four residuals equal to zero.

*Proof.* Put $G_0=\|g\|_\infty$ and $F=\max_y\|f_y\|_\infty$. Choose $E$ and $\delta$ as in Proposition 171.1, and write

$$
B=\mathcal C(f_0,f_0,\mathbf1_E)>0,
\quad L_n=\mathcal C(v_n,f_0,\mathbf1_E)+\mathcal C(f_0,v_n,\mathbf1_E),
\quad C_n=\mathcal C(v_n,v_n,\mathbf1_E).
\tag{171.12}
$$

The bounds $\|v_n\|_\infty=1$, the Markov contraction and $g,f_y\in L^\infty$ give uniform finite bounds on $|L_n|$ and $|C_n|$. Choose one nonzero $t$ small enough that

$$
D_n:=B+tL_n+t^2C_n\ge B/2
\tag{171.13}
$$

for all $n$, and that the legality bounds (171.9) hold for $s_n=A_n/D_n$. Set $s_n=A_n/D_n$. Then $s_n\le2A_n/B$ and $s_n\to0$ because

$$
0<A_n=c\|T_{d/2}(gv_n)\|_2^2
\le cG_0^2m(B_n)\longrightarrow0.
\tag{171.14}
$$

Equation (171.8) gives the first equality in (171.11), and the legality argument of Proposition 171.1 applies uniformly.

It remains to bound the other coordinates. Every linear term vanishes because $v_n\in V$. Every cubic term in $v_n$ vanishes by half-turn parity: $g$, $f_y$ and $P$ are $J$-even, while $v_n$ is $J$-odd. Each of the three quadratic terms has absolute value at most $G_0F\,m(B_n). For the term with the last occurrence of $v_n$, move $P$ across the pairing once; the remaining factor $v_n$ is then supported in $B_n$. Consequently

$$
\bigl\|\Delta(f+t\sigma v_n)-\Delta(f)\bigr\|_{\max}
\le 3G_0F\,t^2m(B_n).
\tag{171.15}
$$

Write $r_n=t^2s_n$. After the terminal correction, each coordinate changes by replacing one bounded factor by a factor differing by at most $r_n$. With $|t|$ chosen so that $\|f_y+t\sigma_yv_n\|_\infty\le1$ and $r_n\le1$, multilinearity and $|\mathcal C(a,b,c)|\le\|a\|_\infty\|b\|_\infty\|c\|_\infty$ give

$$
\bigl\|\Delta(u^{(n)})-\Delta(f+t\sigma v_n)\bigr\|_{\max}
\le (1+r_n)^3-1\le7r_n.
\tag{171.16}
$$

Since $r_n=t^2s_n\to0$, (171.15)–(171.16) prove the second limit in (171.11); the third is already $s_n\to0$. The construction keeps $\Lambda_{134}(P^jv_n)=0$ for every $j\ge0$ by Corollary 170.2. The result leaves exact full-law attainment, deterministic partition realization, $H43$, SRS$\text{-}20$, $F_{64}$, physical succession and Lean/kernel formalization open. $\square$

## 追加锚（本行以下为增补区）


## 172. A paired-coordinate boundary for the invariant terminal family

The compensator in Section 171 is chosen to cancel one coordinate. On the rotation-odd directions from Section 170, half-turn parity fixes the companion coordinates as well, so the same one-dimensional terminal family cannot cancel the off-diagonal pair at the same time.

**Proposition 172.1 (exact paired-coordinate obstruction).** Let $v\in V_-$ be nonzero, let $E$ and $s_t>0$ be supplied by Proposition 171.1, and put

$$
F=f_0=f_1,
\qquad q=f_3,
\qquad w_t=-s_t\mathbf 1_E,
\qquad B_E=\mathcal C(F,F,\mathbf 1_E)>0.
\tag{172.1}
$$

For the legal tuple $u^{(t;v,w_t)}$ of (158.1), write

$$
A=\mathcal C(v,v,q)=q_{003}(v)>0,
\qquad C_E=\mathcal C(v,v,\mathbf 1_E).
\tag{172.2}
$$

Then, for every sufficiently small nonzero $t$,

$$
\begin{aligned}
\Delta(u^{(t;v,w_t)})_{003}
 &=t^2(A-s_tB_E)-t^4s_tC_E,\\
\Delta(u^{(t;v,w_t)})_{013}
 =\Delta(u^{(t;v,w_t)})_{103}
 &=-t^2(A+s_tB_E)+t^4s_tC_E,\\
\Delta(u^{(t;v,w_t)})_{113}
 &=\Delta(u^{(t;v,w_t)})_{003}.
\end{aligned}
\tag{172.3}
$$

Consequently,

$$
\Delta(u^{(t;v,w_t)})_{013}
 =\Delta(u^{(t;v,w_t)})_{103}
 =-2t^2s_tB_E-\Delta(u^{(t;v,w_t)})_{003}.
\tag{172.4}
$$

In particular, the exact compensation from Proposition 171.1 satisfies

$$
\Delta(u^{(t;v,w_t)})_{003}=0
\quad\Longrightarrow\quad
\Delta(u^{(t;v,w_t)})_{013}
 =\Delta(u^{(t;v,w_t)})_{103}
 =-2t^2s_tB_E<0.
\tag{172.5}
$$

*Proof.* The half-turn $J$ preserves $P$, $g$, $F$, $q$ and the invariant set $E$, while $J^*v=-v$. Hence every trilinear term with exactly one occurrence of $v$ vanishes. Expanding (158.1) in the $003$ coordinate gives

$$
\Delta_{003}
 =t^2\bigl[\mathcal C(v,v,q)+\mathcal C(F,F,w_t)\bigr]
   +t^4\mathcal C(v,v,w_t),
\tag{172.6}
$$

and expanding the $013$ coordinate gives

$$
\Delta_{013}
 =t^2\bigl[-\mathcal C(v,v,q)+\mathcal C(F,F,w_t)\bigr]
   -t^4\mathcal C(v,v,w_t).
\tag{172.7}
$$

The same-sign pair $(1,1)$ has the even quadratic terms of $(0,0)$, while the mixed pairs $(0,1)$ and $(1,0)$ have the expression (172.7). Substituting $w_t=-s_t\mathbf1_E$ yields (172.3), and adding the first two displayed expressions gives (172.4). Proposition 171.1 gives $B_E>0$, $s_t>0$, and the exact $003$ cancellation, so (172.5) follows. $\square$

Thus the Section 171 family has an exact one-coordinate zero but no simultaneous zero of the three coordinates $003$, $013$ and $103$ at nonzero amplitude. The obstruction is specific to a rotation-odd first-order direction and a single rotation-invariant terminal compensator; multi-direction corrections, non-invariant compensators, and the remaining full-law, partition, $H43$, $SRS\text{-}20$, $F_{64}$, physical-succession and Lean/kernel questions remain open.

## 173. Positive B-companion residuals on the invariant terminal family

The paired-coordinate obstruction of Section 172 already prevents the single invariant compensator from cancelling the mixed $0$--$1$ coordinates. The same family has an independent sign obstruction on the coordinates whose two terminal labels are $B$.

**Proposition 173.1 (strict positive $0BB$ and $1BB$ residuals).** Let $v\in V_-$ be nonzero, let $E$ and $s_t>0$ be supplied by Proposition 171.1, and put

$$
F=f_0=f_1,
\qquad p=f_B=\frac14,
\qquad e=\mathbf1_E,
\qquad w_t=-s_t e.
\tag{173.1}
$$

Define

$$
H_E=\mathcal C(F,e,p)+\mathcal C(F,p,e),
\qquad
J_E=\mathcal C(F,e,e).
\tag{173.2}
$$

Then

$$
H_E
=p\int_G gF\bigl(Pe+P^2e\bigr)\,dm>0,
\qquad
J_E=\int_G gF\,P(ePe)\,dm\ge0.
\tag{173.3}
$$

For every sufficiently small nonzero $t$ for which the tuple $u^{(t;v,w_t)}$ is legal,

$$
\Delta\bigl(u^{(t;v,w_t)}\bigr)_{0BB}
 =\Delta\bigl(u^{(t;v,w_t)}\bigr)_{1BB}
 =t^2s_tH_E+t^4s_t^2J_E>0.
\tag{173.4}
$$

*Proof.* Put $r=t^2s_t$, so that the two $B$ coordinates in (158.1) equal $p+re$. Expanding the $0BB$ coefficient around $(F,p,p)$ gives

$$
\begin{aligned}
\Delta_{0BB}
={}&t\mathcal C(v,p,p)
+r\bigl[\mathcal C(F,e,p)+\mathcal C(F,p,e)\bigr]\\
&+tr\bigl[\mathcal C(v,e,p)+\mathcal C(v,p,e)\bigr]
+r^2\mathcal C(F,e,e)
+tr^2\mathcal C(v,e,e).
\end{aligned}
\tag{173.5}
$$

The half-turn preserves $P$, $g$, $F$, $p$ and $e$, while $J^*v=-v$. Every term in (173.5) containing exactly one $v$ therefore vanishes. The remaining terms give the first equality in (173.4). Replacing $u_0=F+tv$ by $u_1=F-tv$ changes only the terms containing one $v$, so the same formula holds for $1BB$.

For (173.3), positivity preservation, self-adjointness and $P1=1$ give $Pe,P^2e\ge0$ and

$$
\int_G Pe\,dm=\int_G P^2e\,dm=\int_G e\,dm>0.
$$

Since $gF>0$ almost everywhere, the first integral in (173.3) is strictly positive. Also $ePe\ge0$ and positivity preservation gives $P(ePe)\ge0$, proving $J_E\ge0$. Finally $t\ne0$ and $s_t>0$ imply $t^2s_tH_E>0$, so (173.4) is strict. $\square$

Thus the invariant single-compensator family carries simultaneous strict signs: Section 172 gives negative $013$ and $103$ after exact $003$ cancellation, while (173.4) gives positive $0BB$ and $1BB$ for every nonzero amplitude. These are pointwise obstructions for this ansatz, not a uniform positive lower bound: the displayed quantities can tend to zero under the shrinking variable-ray constructions of Section 171. Multi-direction or non-invariant corrections, full-law partition realization, $H43$, $SRS\text{-}20$, $F_{64}$, physical succession and Lean/kernel formalization remain open.

## 174. Sign-changing necessity for invariant terminal corrections

The indicator correction in Sections 172--173 is a special case of a one-sided terminal correction. The parity calculation extends to every bounded rotation-invariant terminal function and identifies the sign change required by any simultaneous mixed-coordinate cancellation.

**Proposition 174.1 (the invariant pair identity and one-sided no-go).** Let $v\in V_-$ be nonzero, let $w$ be a bounded real Borel function with $J^*w=w$ almost everywhere, and suppose the tuple $u^{(t;v,w)}$ of (158.1) is legal for a nonzero $t$. Put

$$
F=f_0=f_1,
\qquad q=f_3,
\qquad p=f_B=\frac14,
\tag{174.1}
$$

and define

$$
A=\mathcal C(v,v,q)=q_{003}(v)>0,
\qquad B_w=\mathcal C(F,F,w),
\qquad C_w=\mathcal C(v,v,w).
\tag{174.2}
$$

Then

$$
\begin{aligned}
\Delta\bigl(u^{(t;v,w)}\bigr)_{003}
 &=t^2(A+B_w)+t^4C_w,\\
\Delta\bigl(u^{(t;v,w)}\bigr)_{013}
 =\Delta\bigl(u^{(t;v,w)}\bigr)_{103}
 &=-t^2A+t^2B_w-t^4C_w,\\
\Delta\bigl(u^{(t;v,w)}\bigr)_{113}
 &=\Delta\bigl(u^{(t;v,w)}\bigr)_{003},
\end{aligned}
\tag{174.3}
$$

and therefore

$$
\Delta\bigl(u^{(t;v,w)}\bigr)_{003}
+\Delta\bigl(u^{(t;v,w)}\bigr)_{013}
=\Delta\bigl(u^{(t;v,w)}\bigr)_{003}
+\Delta\bigl(u^{(t;v,w)}\bigr)_{103}
=2t^2B_w.
\tag{174.4}
$$

If $w\le0$ almost everywhere and $w$ is nonzero as an $m$-class, then

$$
B_w=\int_Gw\,\psi_0\,dm<0,
\qquad
\psi_0=P\bigl(FP(gF)\bigr)>0\quad m\text{-a.e.},
\tag{174.5}
$$

so the two mixed coordinates in (174.3) cannot both vanish. In the same one-sided case, with $h=-w\ge0$,

$$
\begin{aligned}
\Delta\bigl(u^{(t;v,w)}\bigr)_{0BB}
=\Delta\bigl(u^{(t;v,w)}\bigr)_{1BB}
={}&t^2\bigl[\mathcal C(F,h,p)+\mathcal C(F,p,h)\bigr]\\
&+t^4\mathcal C(F,h,h)>0.
\end{aligned}
\tag{174.6}
$$

Finally, if both $003$ and $013$ vanish (or both $003$ and $103$ vanish), then $B_w=0$. This forces $w$ to have nonzero positive and negative parts: $w$ cannot be zero by $A>0$, and a one-signed nonzero $w$ has a nonzero pairing in (174.5).

*Proof.* The functions $g,F,q,p,w$ are $J$-even and $J^*v=-v$. Thus every trilinear term with exactly one occurrence of $v$ vanishes. Expanding the four first-label pairs in (158.1) leaves the even terms

$$
\Delta_{003}=t^2\bigl[\mathcal C(v,v,q)+\mathcal C(F,F,w)\bigr]+t^4\mathcal C(v,v,w),
$$

$$
\Delta_{013}=\Delta_{103}
=t^2\bigl[-\mathcal C(v,v,q)+\mathcal C(F,F,w)\bigr]-t^4\mathcal C(v,v,w),
$$

with the same-sign $(1,1)$ expression equal to the $(0,0)$ expression. This proves (174.3)--(174.4).

Self-adjointness of $P$ moves the two occurrences of $P$ in $\mathcal C(F,F,w)$ onto $w$, giving $B_w=\langle w,\psi_0\rangle$. Proposition 158.3 supplies $\psi_0>0$ almost everywhere, so (174.5) follows for a nonzero one-sided $w$.

For (174.6), the two $B$ coordinates equal $p+t^2h$. Expanding their two slots gives the two terms linear in $h$, the quadratic term $t^4\mathcal C(F,h,h)$, and terms with exactly one $v$, which vanish by parity. Positivity preservation, self-adjointness and $P1=1$ give

$$
\mathcal C(F,h,p)+\mathcal C(F,p,h)
=p\int_GgF\bigl(Ph+P^2h\bigr)\,dm>0,
\qquad
\mathcal C(F,h,h)\ge0
$$

when $h\ge0$ is nonzero. Thus (174.6) is strict. The final sign-changing conclusion follows from (174.4)--(174.5). $\square$

The result turns the next exact-cancellation route into a structural requirement: an invariant terminal correction that cancels both mixed coordinates must change sign. The one-sided families of Sections 171--173 are therefore exhausted by a sign obstruction, while sign-changing corrections, multiple first-order directions, full-law partition realization, $H43$, $SRS\text{-}20$, $F_{64}$, physical succession and Lean/kernel formalization remain open.


## 175. A compensator-independent obstruction for the complete two-label family

**Definition 175.1 (the original family and a preserved terminal channel).** Retain the entire original telescope of [Appendix III Definition 155.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md#155-positive-bb3-inputs-finite-coupled-improvement-and-source-ratio-selection), including Definitions 134.1, 135.1 and 154.1 and all their endpoint, source and analytic suppliers. Thus $\theta=(a,\eta,d,b)$ ranges over every original finite $a,\eta,d>0$ and every permitted everywhere Borel representative $b$ of $g_d$ with $0<b\le M$. The group $G=H^1\times\mathbb R$, its product and raw Haar measure $\mu$, source $e$, unit-source field $\Gamma$, coefficient-one $w_*$, coefficient-positive normalized $h$, actual selector $A_{\rm src}=\rho C_{\rm src}$, full conservative source-inclusive $K$, original units and clock are unchanged. Keep

$$
\begin{gathered}
m=h^2\mu,\qquad T_s=e^{-sK},\qquad P=T_d,\qquad g=g_{2d},\\
M=1+\|g_d\|_\infty,\qquad c=(4M)^{-1},\\
q=f_3=cb,\qquad p=f_B=\tfrac14,\qquad
F=f_0=f_1=(\tfrac34-q)/2,\\
\mathcal C(a_0,a_1,a_2)=\int_Gg\,a_0P(a_1Pa_2)\,dm,\qquad
\Delta(u)_{yzk}=\mathcal C(u_y,u_z,u_k)-\mathcal C(f_y,f_z,f_k),
\quad \mathcal L=\{0,1,3,B\}.
\end{gathered}
\tag{175.1}
$$

The original source-start law and the three observation epochs $2d,3d,4d$ are retained, with the same readout at each epoch and the original conditionally independent fresh read noises. Here $q$ denotes the scalar function $f_3$. Let $V=\ker\Lambda_{134}$ be the full first-order kernel in Appendix III (134.11)–(134.12), with all sixty-four constraints and signs $\sigma=(1,-1,0,0)$.

For bounded real Borel representatives $v,w$ and $t\in\mathbb R\setminus\{0\}$, use precisely (158.1):

$$
u_0=F+tv,\qquad u_1=F-tv,\qquad
u_3=q+t^2w,\qquad u_B=p-t^2w.
\tag{175.2}
$$

Legality means that this tuple belongs to the pointwise simplex at every $x\in G$; equivalently,

$$
|t v(x)|\le F(x),\qquad
-q(x)\le t^2w(x)\le p\qquad(x\in G).
\tag{175.3}
$$

Indeed, these are exactly the four nonnegativity inequalities, and the four coordinates sum to one. No rotation condition or sign condition is imposed on either function, and $w$ may depend on $t$, $v$ and $\theta$. Every coordinate of $\Delta(u)$ uses this tuple's own terminal $Pu_k$. Put

$$
\begin{gathered}
\alpha=(-p,-p,1-p,1-p)
       =(-\tfrac14,-\tfrac14,\tfrac34,\tfrac34)
       \quad\text{in the order }(0,1,3,B),\\
A_\theta(v)=q_{003}(v)
          =\mathcal C(v,v,q)
          =c\|T_{d/2}(gv)\|_2^2,\qquad
\|\Delta(u)\|_{\max}=\max_{y,z,k\in\mathcal L}|\Delta(u)_{yzk}|.
\end{gathered}
\tag{175.4}
$$

The equality defining $A_\theta$ is the existing source-specific identity (134.13)–(134.16), including $Pq=cg$.

**Theorem 175.2 (full-family exclusion and a directional residual bound).** For every original $\theta$, every bounded real Borel $v$ with $[v]\in V\setminus\{0\}$, every real $t\ne0$, and every bounded real Borel $w$ for which (175.2) is legal on the whole $G$, the exact identity and bound are

$$
\frac34\bigl(\Delta(u)_{003}+\Delta(u)_{00B}\bigr)
-\frac14\bigl(\Delta(u)_{000}+\Delta(u)_{001}\bigr)
=t^2 A_\theta(v),
\tag{175.5}
$$

$$
\|\Delta(u)\|_{\max}
\ge \frac{t^2}{2}q_{003}(v)
=\frac{t^2c}{2}\|T_{d/2}(gv)\|_2^2>0.
\tag{175.6}
$$

Consequently all sixty-four original residuals cannot vanish simultaneously anywhere in this nonzero family. The quantifiers include every legal real amplitude and all legal compensators, including sign-changing, non-invariant and amplitude-dependent ones.

*Proof.* The prescribed affine readout and the exact cancellations in (175.2) give, pointwise on the original whole $G$,

$$
\begin{aligned}
\sum_{k\in\mathcal L}\alpha_k u_k
&=u_3+u_B-p\sum_{k\in\mathcal L}u_k
=q+p-p=q,\\
\sum_{k\in\mathcal L}\alpha_k f_k&=q.
\end{aligned}
\tag{175.7}
$$

Apply the existing joint-law multilinearity (134.10), (155.1) to these finite linear combinations of terminal labels:

$$
\begin{aligned}
\sum_{k\in\mathcal L}\alpha_k\Delta(u)_{00k}
&=\mathcal C(F+tv,F+tv,q)-\mathcal C(F,F,q)\\
&=t\bigl[\mathcal C(v,F,q)+\mathcal C(F,v,q)\bigr]
  +t^2\mathcal C(v,v,q)\\
&=t\ell_{003}(v)+t^2q_{003}(v)
=t^2A_\theta(v).
\end{aligned}
\tag{175.8}
$$

The identification of the linear term is exactly (134.11), since $\sigma_3=0$, and it vanishes because $[v]\in V$. The quadratic term is exactly the already supplied positive energy (134.13); its strictness requires $[v]\ne0$, $g>0$ almost everywhere, and the original full heat operator. No new spectral assertion is needed.

In the first line of (175.8), the sum on the left contains the four actual factors $Pu_k$. Only their linear combination is simplified: $\sum_k\alpha_kPu_k=Pq=cg$. No individual perturbed terminal is identified with $cg$, and the first observation density remains $g=g_{2d}$. Thus the calculation retains each tuple's own terminal in every residual.

Writing out the four coefficients yields (175.5). Finally,

$$
t^2A_\theta(v)
\le\sum_{k\in\mathcal L}|\alpha_k|\,|\Delta(u)_{00k}|
\le\bigl(2p+2(1-p)\bigr)\|\Delta(u)\|_{\max}
=2\|\Delta(u)\|_{\max}.
\tag{175.9}
$$

This proves (175.6). The proof uses no small-amplitude expansion with a remainder, parity restriction, invariant representative replacement, or restriction on $w$ beyond the stated boundedness and whole-$G$ legality. $\square$

**Corollary 175.3 (exact compensation, degeneracies and the remaining target).** Inside the unchanged family (158.1), with $[v]\in V\setminus\{0\}$ and $t\ne0$, varying the terminal compensator cannot attain the full law. For fixed $\theta,t,v$ the positive lower bound (175.6) is independent of $w$. For fixed $\theta$, every sequence of such legal tuples with $\|\Delta(u^{(n)})\|_{\max}\to0$ necessarily satisfies

$$
t_n^2q_{003}(v_n)\longrightarrow0.
\tag{175.10}
$$

Exact cancellation of $003$ alone, including Proposition 171.1, remains compatible with this obstruction. The selected-coordinate sign-changing necessities of Proposition 174.1 remain necessary in their stated invariant domain; satisfying them does not give a full-law zero. The variable-direction approximation in Corollary 171.2 remains compatible with (175.6), and the bound is not coercive over varying directions.

*Proof.* The exclusion and (175.10) follow directly from (175.6). If $003$ vanishes, (175.5) still has the strictly positive right side, so its other three residual coordinates cannot all vanish. This leaves the one-coordinate conclusion of Proposition 171.1 intact, independently of the additional parity calculations in Sections 172–174. Corollary 170.2 supplies directions of unit essential-supremum norm with $q_{003}(v_n)\to0$, and Corollary 171.2 supplies legal compensated tuples with full residual tending to zero. Thus these existing approximations do not contradict the pointwise bound.

At $t=0$, (175.2) reduces to $u=f$, so every residual is zero. If $[v]=0$, then $A_\theta(v)=0$ and there is no strict conclusion from (175.6); in particular $w=0$ gives $[u_y]=[f_y]$ and every residual zero whenever the representatives are pointwise legal. A function nonzero only on an $m$-null set is not a nonzero direction in the theorem. The original positive-time slot laws are absolutely continuous with respect to $m$, so their joint coefficients depend only on these classes, while legality is still imposed at every point of $G$. $\square$

The source-specific application is repo-derived: (175.7)–(175.8) use the original affine readout (134.7), the full first-order kernel (134.11)–(134.12), the existing positive source energy (134.13)–(134.16), and the joint-law and residual definitions (155.1) on exactly the family (158.1). Multilinearity and the finite coefficient estimate in (175.9) are standard intermediates; no historical novelty is claimed for them or for heat positivity. The additional conclusion is the all-compensator exclusion and its explicit directional bound for this original source family, rather than a new generic positivity theorem.

The universal partition target (155.3) retains all original $\theta$ and all whole-$G$ pointwise Borel partitions. This theorem excludes only the nonzero family (158.1); it neither excludes arbitrary partitions or other families nor settles $F_{64}$, $H43$ or SRS$\text{-}20$. It supplies no native AURIC realization, physical successor, common reference or joint-operation transport, or correspondence for all legal futures. Complete quantum origin remains unresolved. These are paper deductions conditional on the retained suppliers, with no Lean/kernel certification asserted.

## 176. First-order leakage required outside the calibrated kernel

Section 175 used the full first-order kernel to turn the preserved terminal channel into a strict quadratic obstruction. Removing that kernel assumption leaves an exact scalar compatibility condition rather than an unrestricted escape.

**Definition 176.1 (the $003$ leakage functional).** Retain the complete telescope and the legal family (175.1)--(175.3). For a bounded real Borel function $v$, define

$$
\ell_{003}(v)
=\mathcal C(v,F,q)+\mathcal C(F,v,q),
\qquad
A_\theta(v)=\mathcal C(v,v,q).
\tag{176.1}
$$

The first quantity is the $003$ component of the original first-order map, and $A_\theta(v)>0$ for every nonzero $m$-class by Appendix III Proposition 134.2.

**Proposition 176.2 (exact leakage identity for arbitrary directions).** For every original $\theta$, every bounded real Borel $v,w$, and every nonzero real $t$ for which (175.2) is legal, one has

$$
\frac34\bigl(\Delta(u)_{003}+\Delta(u)_{00B}\bigr)
-\frac14\bigl(\Delta(u)_{000}+\Delta(u)_{001}\bigr)
=t\,\ell_{003}(v)+t^2A_\theta(v).
\tag{176.2}
$$

Consequently,

$$
\|\Delta(u)\|_{\max}
\ge
\frac{|t|}{2}\,\bigl|\ell_{003}(v)+tA_\theta(v)\bigr|.
\tag{176.3}
$$

*Proof.* The affine terminal combination in (175.7) remains $q$ for every $v$ and $w$. The same multilinearity calculation as (175.8), without setting the first-order term to zero, gives

$$
\sum_{k\in\mathcal L}\alpha_k\Delta(u)_{00k}
=t\bigl[\mathcal C(v,F,q)+\mathcal C(F,v,q)\bigr]
 +t^2\mathcal C(v,v,q),
$$

which is (176.2). The sum of absolute coefficients is $2p+2(1-p)=2$, so the triangle inequality gives (176.3). The calculation never uses a sign, rotation, or invariance condition on $w$. $\square$

**Corollary 176.3 (the only scalar escape from the preserved channel).** Let $v$ be nonzero as an $m$-class. If a legal tuple of the family (175.2) has all sixty-four residuals equal to zero, then

$$
\ell_{003}(v)+tA_\theta(v)=0,
\qquad
t=-\frac{\ell_{003}(v)}{A_\theta(v)}.
\tag{176.4}
$$

In particular, $\ell_{003}(v)\ne0$; every nonzero direction in the $003$ kernel, including every nonzero $v\in V$, is excluded by Proposition 176.2. The terminal compensator cannot alter either side of (176.4).

For any sequence of legal tuples in this family with $t_n\ne0$ and $\|\Delta(u^{(n)})\|_{\max}\to0$,

$$
\ell_{003}(v_n)+t_nA_{\theta_n}(v_n)\longrightarrow0.
\tag{176.5}
$$

Thus a prospective full-law escape outside $V$ must carry nonzero first-order leakage and tune its amplitude against the positive quadratic energy; changing only the terminal correction cannot supply that tuning.

*Proof.* If every residual is zero, the left side of (176.2) is zero. For nonzero $v$, Proposition 134.2 gives $A_\theta(v)>0$, yielding (176.4). If $\ell_{003}(v)=0$, then (176.4) would give $tA_\theta(v)=0$, contradicting $t\ne0$. The sequence statement follows from (176.3). $\square$

This result narrows the remaining multi-direction and non-kernel routes to a coupled first-order leakage problem. It does not prove that the tuned scalar relation is sufficient, that the resulting tuple is legal for any prescribed $\theta$, or that the other $63$ coordinates can vanish. Arbitrary partitions, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization remain open.

## 177. The paired preserved channels close the symmetric escape

The scalar condition in Corollary 176.3 comes from the $00$ first-label pair. The same terminal combination is preserved for the $11$ pair, and its first-order leakage has the opposite sign. The two channels therefore eliminate the apparent tuning route before any of the remaining coordinates are considered.

**Proposition 177.1 (paired-channel identity and uniform two-sided bound).** Retain the original telescope and the legal family (175.1)--(175.3), with bounded real Borel $v,w$ and $t\ne0$. Define

$$
\begin{aligned}
S_0&=\frac34\bigl(\Delta(u)_{003}+\Delta(u)_{00B}\bigr)
 -\frac14\bigl(\Delta(u)_{000}+\Delta(u)_{001}\bigr),\\
S_1&=\frac34\bigl(\Delta(u)_{113}+\Delta(u)_{11B}\bigr)
 -\frac14\bigl(\Delta(u)_{110}+\Delta(u)_{111}\bigr).
\end{aligned}
$$

Then

$$
S_0=t\,\ell_{003}(v)+t^2A_\theta(v),
\qquad
S_1=-t\,\ell_{003}(v)+t^2A_\theta(v).
\tag{177.1}
$$

Consequently,

$$
\|\Delta(u)\|_{\max}
\ge \frac{t^2}{2}A_\theta(v)
 =\frac{t^2}{2}q_{003}(v).
\tag{177.2}
$$

If $[v]\ne0$, the right side is strictly positive. Hence no nonzero legal member of the entire symmetric family (175.2) can have all sixty-four residuals equal to zero, whether or not $v$ belongs to the first-order kernel and regardless of the terminal compensator.

*Proof.* The affine terminal combination used in (175.7) is also $q$ for the $11$ pair. Applying joint-law multilinearity gives

$$
\begin{aligned}
S_0
 &=\mathcal C(F+tv,F+tv,q)-\mathcal C(F,F,q),\\
S_1
 &=\mathcal C(F-tv,F-tv,q)-\mathcal C(F,F,q).
\end{aligned}
$$

Expanding the two expressions and using Definition 176.1 yields (177.1). Each $S_i$ is a linear combination of four residuals whose coefficient absolute values sum to $2$, so

$$
2\|\Delta(u)\|_{\max}\ge\max\{|S_0|,|S_1|\}.
$$

For real $x,y$, $\max\{|x+y|,|-x+y|\}\ge|y|$. Taking $x=t\ell_{003}(v)$ and $y=t^2A_\theta(v)$ proves (177.2). Strictness for a nonzero $m$-class is the positivity of $A_\theta(v)$ from Appendix III Proposition 134.2. The computation does not use any property of $w$ beyond legality. $\square$

**Corollary 177.2 (closure of the symmetric family).** For every sequence of legal tuples of the form (175.2) with $t_n\ne0$ and $\|\Delta(u^{(n)})\|_{\max}\to0$,

$$
t_n^2q_{003}(v_n)\longrightarrow0.
\tag{177.3}
$$

Thus the non-kernel leakage tuning suggested by (176.4) cannot produce an exact full-law zero. For any fixed nonzero direction and nonzero amplitude, (177.2) supplies a positive residual bound. Any remaining escape must leave the symmetric first-label family itself; the bound says nothing about arbitrary partitions, independently normalized first labels, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession or Lean/kernel formalization.

*Proof.* Apply (177.2) to each tuple. $\square$

The new conclusion is a paired-channel consequence for the original source family. It uses the existing affine readout, positivity identity and joint-law multilinearity; it adds no native AURIC realization or physical transport and makes no Lean/kernel certification claim.

## 178. Terminal-pair preservation rigidifies arbitrary partitions

The preceding sections treated the symmetric first-label family. A general pointwise partition can still be considered if its terminal pair preserves the same affine channel. That single preservation condition is enough to turn the baseline's two independent label relations into quantitative obstructions.

**Proposition 178.1 (preserved-channel contrast bound).** Let $u=(u_0,u_1,u_3,u_B)$ be any bounded nonnegative Borel partition with

$$
u_0+u_1+u_3+u_B=1,
\qquad
u_3+u_B=q+p
$$

on the original whole $G$. Retain the residual tensor $\Delta(u)$ and set

$$
\lambda=(-p,-p,1-p,1-p),
\qquad
|a|_1=\sum_{y\in\mathcal L}|a_y|,
\qquad
H_a=\sum_{y\in\mathcal L}a_yu_y.
$$

For every real label vector $a$ satisfying $\sum_y a_yf_y=0$, one has

$$
\sum_{y,z,k\in\mathcal L}a_ya_z\lambda_k\Delta(u)_{yzk}
=\mathcal C(H_a,H_a,q)
=q_{003}(H_a),
\tag{178.1}
$$

and therefore

$$
\|\Delta(u)\|_{\max}
\ge \frac{q_{003}(H_a)}{2|a|_1^2}.
\tag{178.2}
$$

The right side is strictly positive whenever $[H_a]\ne0$ as an $m$-class.

*Proof.* The terminal assumptions and the partition identity give

$$
\sum_{k\in\mathcal L}\lambda_ku_k
=(1-p)(u_3+u_B)-p(u_0+u_1)
=u_3+u_B-p=q.
$$

The same calculation for the baseline labels gives $\sum_k\lambda_kf_k=q$. The condition on $a$ gives $\sum_ya_yf_y=0$. Applying trilinearity to the left side of (178.1) therefore leaves exactly $\mathcal C(H_a,H_a,q)$. Its positivity identity is the existing

$$
q_{003}(H_a)=c\,\|T_{d/2}(gH_a)\|_2^2,
$$

so it is strict on every nonzero $m$-class. The absolute sum of the displayed coefficients is
$|a|_1^2|\lambda|_1=2|a|_1^2$; the triangle inequality gives (178.2). $\square$

**Corollary 178.2 (exact rigidity in the preserved terminal plane).** Under the hypotheses of Proposition 178.1, if all sixty-four residuals vanish, then

$$
u_0=u_1=F,
\qquad
u_3=q,
\qquad
u_B=p
$$

as $m$-classes. Thus the preserved terminal-pair slice of the arbitrary-partition fibre contains only the original partition.

*Proof.* Use Proposition 178.1 first with

$$
a^{(01)}=(1,-1,0,0),
$$

and then with

$$
a^{(3B)}=(2,0,1,-3).
$$

The baseline identities $f_0-f_1=0$ and $2f_0+f_3-3f_B=2F+q-3p=0$ show that both vectors are admissible. Vanishing of all residuals and (178.1) force

$$
u_0-u_1=0,
\qquad
2u_0+u_3-3u_B=0
$$

as $m$-classes. Since $u_3+u_B=q+p$ and the four labels sum to one,

$$
2u_0=1-q-p=2F,
$$

so $u_0=u_1=F$. Substitution into the second relation and $u_3+u_B=q+p$ gives $u_B=p$ and $u_3=q$. $\square$

This closes the exact-zero question on the preserved terminal-pair slice, including arbitrary first-label partitions and arbitrary pointwise representatives. It does not prove that a full zero outside the symmetric family must preserve $u_3+u_B=q+p$; establishing or refuting that implication is the next arbitrary-partition gap. The result also leaves $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization open.

## 179. Radical boundary for arbitrary full-zero partitions

The terminal-pair hypothesis in Section 178 is a direct positive witness. Without it, the exact tensor equations still force every baseline linear relation into the three-slot radical of the candidate partition's function span.

**Definition 179.1 (the three slot radicals).** For a bounded partition $u$, let

$$
\mathcal W_u=\operatorname{span}_{\mathbb R}\{u_y:y\in\mathcal L\}\subset L^\infty(m;\mathbb R)
$$

and define

$$
\begin{aligned}
\operatorname{Rad}_1(\mathcal W_u)
 &=\{h:\mathcal C(h,x,y)=0\ \text{for all }x,y\in\mathcal W_u\},\\
\operatorname{Rad}_2(\mathcal W_u)
 &=\{h:\mathcal C(x,h,y)=0\ \text{for all }x,y\in\mathcal W_u\},\\
\operatorname{Rad}_3(\mathcal W_u)
 &=\{h:\mathcal C(x,y,h)=0\ \text{for all }x,y\in\mathcal W_u\}.
\end{aligned}
$$

**Proposition 179.2 (full-zero radical containment).** Suppose a bounded pointwise partition $u$ has all sixty-four residuals equal to zero. If a real label vector $a$ satisfies

$$
F_a=\sum_{y\in\mathcal L}a_yf_y=0,
$$

then its candidate combination

$$
H_a=\sum_{y\in\mathcal L}a_yu_y
$$

belongs to

$$
\operatorname{Rad}_1(\mathcal W_u)
\cap\operatorname{Rad}_2(\mathcal W_u)
\cap\operatorname{Rad}_3(\mathcal W_u).
\tag{179.1}
$$

*Proof.* Let $b,c$ be arbitrary real label vectors and put $U_b=\sum_yb_yu_y$ and $U_c=\sum_kc_ku_k$, with the analogous baseline combination $F_b,F_c$. Contracting the zero residual tensor with $a_yb_zc_k$ gives

$$
\mathcal C(H_a,U_b,U_c)=\mathcal C(F_a,F_b,F_c)=0.
$$

As $b,c$ range over all label vectors, $U_b,U_c$ range over $\mathcal W_u$, which proves the first radical inclusion. Placing $a$ in the middle or terminal label contracts the same zero tensor to the other two inclusions. $\square$

**Corollary 179.3 (conditional reduction to a common-first slice).** Under the hypotheses of Proposition 179.2, assume additionally that the common intersection in (179.1) contains no nonzero element. Then every full-zero partition has

$$
u_0=u_1=F+v,
\qquad
u_3=q-2v,
\qquad
u_B=p
$$

for one bounded real Borel $m$-class $v$ for which the pointwise simplex inequalities hold.

*Proof.* Apply the radical hypothesis to the two baseline relations

$$
a^{(01)}=(1,-1,0,0),
\qquad
a^{(3B)}=(2,0,1,-3),
$$

which satisfy $f_0-f_1=0$ and $2f_0+f_3-3f_B=0$. Equation (179.1) forces

$$
u_0-u_1=0,
\qquad
2u_0+u_3-3u_B=0
$$

as $m$-classes. Together with $u_0+u_1+u_3+u_B=1$, subtraction gives $u_B=1/4=p$. Writing $u_0=u_1=F+v$ then gives $u_3=3/4-2(F+v)=q-2v$. $\square$

This isolates the unconditional algebraic boundary: an arbitrary full-zero partition either supplies a nonzero common radical element for one of the two baseline relations, or lies in the one-function slice above. Section 178 proves that the radical escape is impossible on the preserved terminal-pair slice. It remains open whether the full source hypotheses force triviality of the candidate radical in general, and whether the common-first slice admits any exact zero beyond $v=0$; $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization remain open.

## 180. The common-first slice has a seven-equation boundary

The conditional reduction in Corollary 179.3 has an additional exact algebraic simplification. Its two repeated first labels and its fixed $B$ label make every residual a linear combination of the coordinates whose labels are only $0$ and $3$.

**Proposition 180.1 (seven coordinates generate the common-first residual).** Let

$$
u_0=u_1=F+v,\qquad u_3=q-2v,\qquad u_B=p
$$

with the pointwise simplex inequalities, and let $\Delta(u)$ be the residual tensor. Put

$$
R_{ijk}=\Delta(u)_{ijk}
\qquad (i,j,k\in\{0,3\}).
$$

Then all sixty-four residuals vanish if and only if the following seven coordinates vanish:

$$
R_{000}=R_{003}=R_{030}=R_{033}=R_{300}=R_{303}=R_{330}=0.
\tag{180.1}
$$

The omitted eighth coordinate satisfies the identity

$$
8R_{000}+4R_{003}+4R_{030}+2R_{033}
 +4R_{300}+2R_{303}+2R_{330}+R_{333}=0.
\tag{180.2}
$$

*Proof.* Both the candidate and the prescribed tuple satisfy

$$
u_1=u_0,
\qquad
u_B=\frac{2u_0+u_3}{3},
$$

because $2F+q=3p$ and $2(F+v)+(q-2v)=3p$. Trilinearity therefore expresses every residual with a $1$ or $B$ label as a fixed linear combination of residuals with labels in $\{0,3\}$, in the same slot. Thus the eight $R_{ijk}$ are sufficient for all sixty-four coordinates.

The coefficient vector $(2,1)$ in the $\{0,3\}$ labels gives, by three-slot trilinearity,

$$
\sum_{i,j,k\in\{0,3\}}2^{\mathbf1_{i=0}+\mathbf1_{j=0}+\mathbf1_{k=0}}R_{ijk}
=\mathcal C(2u_0+u_3,2u_0+u_3,2u_0+u_3)
 -\mathcal C(2f_0+f_3,2f_0+f_3,2f_0+f_3)=0,
$$

which is exactly (180.2). If the seven coordinates in (180.1) vanish, (180.2) gives $R_{333}=0$, and the preceding span argument gives all sixty-four residuals. The converse is immediate. $\square$

This is a complete equation-count reduction for the common-first slice, not a positivity or nonattainment result. The seven remaining equations are cubic conditions in $v$ with the actual terminal convention; no claim is made that they have only the solution $v=0$. The radical-triviality hypothesis of Corollary 179.3, the general terminal-pair implication, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization remain open.

## 追加锚（本行以下为增补区）

## 181. Sign-definite directions are excluded in the common-first slice

The seven-equation system has a simple one-sided obstruction. It uses only positivity of the actual joint-law form, so it applies before solving the genuinely sign-changing cubic system.

**Proposition 181.1 (one-sided common-first obstruction).** Let

$$
u_0=u_1=F+v,\qquad u_3=q-2v,\qquad u_B=p
$$

be a pointwise legal common-first tuple, with $v$ a bounded real Borel representative. If $[v]\ne0$ as an $m$-class, then

$$
v\ge0\quad m\text{-a.e.}
\Longrightarrow
R_{000}>0,
\tag{181.1}
$$

and

$$
v\le0\quad m\text{-a.e.}
\Longrightarrow
R_{333}>0.
\tag{181.2}
$$

Consequently, a full-zero tuple in the common-first slice is either the baseline $v=0$ as an $m$-class or has both a positive and a negative part of positive $m$-measure.

*Proof.* The retained source suppliers give $g>0$, $F>0$ and $q>0$ $m$-almost everywhere, while $P$ preserves nonnegativity and is positivity improving. Hence, for every bounded nonnegative $h$ with $[h]\ne0$ and every two strictly positive bounded factors $a,b$,

$$
\mathcal C(h,a,b)
 =\int_G gh\,P(aPb)\,dm>0.
\tag{181.3}
$$

Indeed, $Pb>0$ almost everywhere, so $aPb>0$ almost everywhere and then $P(aPb)>0$ almost everywhere; the integral is strict on the positive set of $h$.

If $v\ge0$, multilinearity gives

$$
\begin{aligned}
R_{000}
={}&\mathcal C(F+v,F+v,F+v)-\mathcal C(F,F,F)\\
={}&\mathcal C(v,F,F)+\mathcal C(F,v,F)+\mathcal C(F,F,v)\\
&+\mathcal C(v,v,F)+\mathcal C(v,F,v)+\mathcal C(F,v,v)
 +\mathcal C(v,v,v).
\end{aligned}
\tag{181.4}
$$

Every term on the right is nonnegative, and the first term is strictly positive by (181.3), proving (181.1).

If $v\le0$, put $h=-v\ge0$. Then $u_3=q+2h$, and the same expansion gives

$$
R_{333}
 =\mathcal C(q+2h,q+2h,q+2h)-\mathcal C(q,q,q).
\tag{181.5}
$$

All terms after subtraction are nonnegative, and the term $2\mathcal C(h,q,q)$ is strictly positive by (181.3), proving (181.2). Thus an exact zero with $[v]\ne0$ cannot be one-signed. For a real measurable representative, failure of both one-sided alternatives is exactly the assertion that its positive and negative parts each have positive $m$-measure. $\square$

This removes constant shifts and every other sign-definite displacement from the conditional common-first search. It does not solve the remaining sign-changing seven-equation system, remove the radical-triviality hypothesis in Corollary 179.3, or settle arbitrary partitions, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession or Lean/kernel formalization.

## 182. Weighted lower bounds for one-sided common-first escapes

The sign obstruction of Section 181 has a quantitative form. The first positive term in each multilinear expansion already gives a source-dependent residual lower bound.

**Proposition 182.1 (strict weighted one-sided bounds).** Retain the legal common-first tuple and notation of Proposition 181.1, and put

$$
\psi_F=P(FPF),
\qquad
\psi_q=P(qPq).
$$

Then

$$
 v\ge0
\quad\Longrightarrow\quad
R_{000}\ge \mathcal C(v,F,F)
 =\int_G gv\,\psi_F\,dm,
\tag{182.1}
$$

and

$$
 v\le0
\quad\Longrightarrow\quad
R_{333}\ge 2\mathcal C(-v,q,q)
 =2\int_G g(-v)\,\psi_q\,dm.
\tag{182.2}
$$

If $[v]\ne0$, the corresponding right-hand side is strictly positive.

*Proof.* For $v\ge0$, equation (181.4) writes $R_{000}$ as the sum of seven nonnegative terms. Retaining its first term gives (182.1), and self-adjointness of $P$ in the definition of $\mathcal C$ gives the displayed integral. For $v\le0$, write $h=-v\ge0$. Expanding $\mathcal C(q+2h,q+2h,q+2h)-\mathcal C(q,q,q)$, every term is nonnegative and the term with exactly one $h$ in the first slot is $2\mathcal C(h,q,q)$, which gives (182.2). The strict positivity follows from (181.3), applied with $(a,b)=(F,F)$ or $(q,q)$. $\square$

These bounds quantify the distance from the full-zero fibre for every one-sided displacement. They leave the genuinely sign-changing seven-equation system, the radical-triviality implication in Corollary 179.3, arbitrary partitions, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization open.

## 183. Two-sided balance required by common-first full zeros

A sign-changing candidate has two nonnegative parts whose effects can be separated using the two diagonal coordinates. Pointwise legality makes the relevant bases nonnegative, so positivity of the trilinear form gives exact compensation inequalities.

**Proposition 183.1 (positive-negative balance inequalities).** Retain the common-first tuple of Proposition 181.1. Write

$$
 h=v^+=\max\{v,0\},
 \qquad
 k=v^- =\max\{-v,0\},
 \qquad
 D(a)=\mathcal C(a,a,a).
$$

Then $hk=0$ pointwise, and legality implies

$$
F-k\ge0,
\qquad
q-2h\ge0.
\tag{183.1}
$$

If $R_{000}=R_{333}=0$, the positive and negative parts satisfy

$$
D(F)-D(F-k)
 =D(F-k+h)-D(F-k)
 \ge \mathcal C(h,F-k,F-k),
\tag{183.2}
$$

and

$$
D(q)-D(q-2h)
 =D(q-2h+2k)-D(q-2h)
 \ge 2\mathcal C(k,q-2h,q-2h).
\tag{183.3}
$$

*Proof.* Since $h$ and $k$ have disjoint supports, on the support of $k$ one has $h=0$ and the legality of $u_0=F+h-k$ gives $F-k\ge0$; off that support $F-k=F\ge0$. The same argument with $u_3=q-2h+2k$ gives $q-2h\ge0$, proving (183.1).

For nonnegative $a,r$, trilinearity and positivity preservation give

$$
D(a+r)-D(a)
=\mathcal C(r,a,a)+\mathcal C(a,r,a)+\mathcal C(a,a,r)
 +\mathcal C(r,r,a)+\mathcal C(r,a,r)
 +\mathcal C(a,r,r)+\mathcal C(r,r,r)\ge \mathcal C(r,a,a).
\tag{183.4}
$$

The first diagonal residual being zero is

$$
D(F-k+h)=D(F),
$$
so applying (183.4) with $(a,r)=(F-k,h)$ yields (183.2). The third diagonal residual being zero is

$$
D(q-2h+2k)=D(q).
$$

Applying (183.4) with $(a,r)=(q-2h,2k)$ gives (183.3), since the first term is $2\mathcal C(k,q-2h,q-2h)$. $\square$

These are necessary balance conditions for a common-first full zero. Together with Section 181 they require both sign parts as measured classes; the inequalities do not assert that a sign-changing pair is sufficient, and the remaining five equations, the radical alternative, arbitrary partitions, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization remain open.

## 184. Tensor-lift criterion for the common-first slice

The remaining common-first equations can be expressed without choosing a preferred list of coordinates. The four labels are images of a two-dimensional coefficient space, and a full zero is exactly preservation of the induced trilinear tensor.

**Proposition 184.1 (coefficient-space tensor equivalence).** Let $A=\mathbb R^2$, and for $(a,b)\in A$ define

$$
\Phi_f(a,b)=ap+bF,
\qquad
\Phi_v(a,b)=ap+b(F+v).
$$

Set

$$
\mathfrak T_f(r,s,t)=\mathcal C(\Phi_f(r),\Phi_f(s),\Phi_f(t)),
\qquad
\mathfrak T_v(r,s,t)=\mathcal C(\Phi_v(r),\Phi_v(s),\Phi_v(t)).
$$

For the coefficient vectors

$$
 c_B=(1,0),
 \qquad c_0=c_1=(0,1),
 \qquad c_3=(3,-2),
\tag{184.1}
$$

one has $f_y=\Phi_f(c_y)$ and $u_y=\Phi_v(c_y)$ for every $y\in\{0,1,3,B\}$. Consequently,

$$
\Delta(u)_{yzk}=0\ \text{for all }y,z,k
\quad\Longleftrightarrow\quad
\mathfrak T_v=\mathfrak T_f\ \text{on }A^3.
\tag{184.2}
$$

*Proof.* The identities for $c_B,c_0,c_1$ are immediate. Since $2F+q=3p$ and $2(F+v)+(q-2v)=3p$, one has $q=3p-2F$ and $q-2v=3p-2(F+v)$, giving the identity for $c_3$.

For every label triple $(y,z,k)$, the residual is

$$
\Delta(u)_{yzk}
 =\mathfrak T_v(c_y,c_z,c_k)-\mathfrak T_f(c_y,c_z,c_k).
$$

If all residuals vanish, the two trilinear forms agree on the four displayed coefficient vectors. The vectors $c_B$ and $c_0$ form a basis of $A$, so trilinearity extends this equality to every $(r,s,t)\in A^3$. The converse follows by evaluating (184.2) at the coefficient vectors of every label triple. $\square$

**Corollary 184.2 (the common-first problem as a tensor-preserving lift).** If $p$ and $F$ are linearly independent as $m$-classes, let $E=\operatorname{span}_{\mathbb R}\{p,F\}$ and define

$$
S_v(ap+bF)=ap+b(F+v).
$$

Then a legal common-first tuple has all residuals zero if and only if

$$
\mathcal C(S_vx,S_vy,S_vz)=\mathcal C(x,y,z)
\qquad(x,y,z\in E).
\tag{184.3}
$$

Thus the only remaining exact-zero route in this slice is a tensor-preserving lift of the two-dimensional baseline span. The coefficient-space statement (184.2) remains valid without the independence assumption; no rigidity or positivity of such a lift is asserted here.

This criterion is equivalent to the seven-coordinate reduction of Section 180, while making the remaining algebraic target explicit. It does not solve the tensor-stabilizer problem, the radical alternative, arbitrary partitions, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession or Lean/kernel formalization.

## 185. The in-span tensor stabilizer has a scalar dichotomy

The tensor-lift criterion gives an immediate test for directions that remain inside the baseline span. The asymmetry of the actual ordered joint law is measured by one scalar pair of coefficients.

**Proposition 185.1 (in-span stabilizer dichotomy).** Assume that $p$ and $F$ are linearly independent as $m$-classes, and let a common-first displacement have the form

$$
[v]=r[p]+(s-1)[F]
$$

for real $r,s$, so that $[F+v]=r[p]+s[F]$. Put

$$
 a=\mathcal C(p,p,p),
 \qquad
 b=\mathcal C(p,p,F)=\mathcal C(p,F,p),
 \qquad
 d=\mathcal C(F,p,p).
\tag{185.1}
$$

If all common-first residuals vanish, then

$$
 r a+s d=d,
 \qquad
 r a+s b=b,
\tag{185.2}
$$

and hence

$$
(s-1)(d-b)=0.
\tag{185.3}
$$

In particular, if $d\ne b$, the only in-span full-zero displacement is $v=0$ as an $m$-class. If $d=b$, the displayed tensor slots leave the single relation $ra+(s-1)b=0$; the remaining tensor components are the exact residual test for that exceptional scalar case.

*Proof.* Since $p=f_B=1/4$ is constant and $Pp=p$, direct use of the ordered form gives

$$
\mathcal C(p,p,F)=p^2\int_G g\,PF\,dm
 =\mathcal C(p,F,p),
$$

so $b$ is well-defined. Positivity of $g,p$ gives $a>0$.

If all residuals vanish, Corollary 184.2 says that the lift $S_v$ preserves the trilinear tensor on $\operatorname{span}\{p,F\}$. Evaluating it at $(F,p,p)$ gives

$$
\mathcal C(F+v,p,p)=d,
$$

which is the first equation in (185.2) after substituting $F+v=rp+sF$. Evaluating at $(p,F,p)$ gives the second equation, using the definition of $b$. Subtracting yields (185.3). If $d\ne b$, then $s=1$, and either equation in (185.2) gives $ra=0$; since $a>0$, $r=0$, hence $v=0$. When $d=b$, both equations reduce to the stated single relation, and no conclusion about the other tensor components follows from these two slots alone. $\square$

The scalar $d-b=p^2\langle F,(I-P)g\rangle_m$ is an actual ordered-source coefficient; its vanishing is a concrete exceptional case, not an automatic symmetry. This proposition only treats displacements inside the baseline span. Tensor-preserving lifts with an out-of-span component, the radical alternative, arbitrary partitions, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization remain open.

## 186. The exceptional in-span branch is a one-parameter shear test

When the ordered coefficient in Section 185 is exceptional, the first tensor slots determine the direction of every possible in-span lift. The remaining slots then reduce to four polynomial equations in one scalar amplitude.

**Proposition 186.1 (exceptional shear criterion).** Retain the notation and hypotheses of Proposition 185.1, and assume $d=b$. Set

$$
\kappa=\frac{b}{a},
\qquad
w=F-\kappa p,
\qquad
\alpha=s-1.
\tag{186.1}
$$

Then $w$ is nonzero as an $m$-class. An in-span tensor-preserving lift with parameter $(r,s)$ is either the baseline $(r,s)=(0,1)$, or it has

$$
r=-\alpha\kappa,
\qquad
[v]=\alpha[w],
\qquad
S_vF=F+\alpha w,
\tag{186.2}
$$

with $\alpha\ne0$ satisfying all four equations

$$
\begin{aligned}
0={}&\alpha\bigl[\mathcal C(p,w,F)+\mathcal C(p,F,w)\bigr]
      +\alpha^2\mathcal C(p,w,w),\\
0={}&\alpha\bigl[\mathcal C(w,p,F)+\mathcal C(F,p,w)\bigr]
      +\alpha^2\mathcal C(w,p,w),\\
0={}&\alpha\bigl[\mathcal C(w,F,p)+\mathcal C(F,w,p)\bigr]
      +\alpha^2\mathcal C(w,w,p),\\
0={}&\alpha\bigl[\mathcal C(w,F,F)+\mathcal C(F,w,F)+\mathcal C(F,F,w)\bigr]\\
&+\alpha^2\bigl[\mathcal C(w,w,F)+\mathcal C(w,F,w)+\mathcal C(F,w,w)\bigr]
      +\alpha^3\mathcal C(w,w,w).
\end{aligned}
\tag{186.3}
$$

Conversely, if a nonzero $\alpha$ satisfies (186.3) and the resulting $F+\alpha w$ and $q-2\alpha w$ obey the pointwise legality inequalities, then the corresponding in-span lift preserves the full common-first tensor.

*Proof.* The first two equations of (185.2), with $d=b$, give $ra+(s-1)b=0$. Hence $r=-\alpha\kappa$, and

$$
[v]=r[p]+\alpha[F]=\alpha[F-\kappa p]=\alpha[w].
$$

Linear independence of $[p]$ and $[F]$ makes $[w]\ne0$. The lift fixes $p$ and sends $F$ to $F+\alpha w$. The tensor slots containing at most one copy of $F$ are already preserved by the defining relation $\mathcal C(p,p,w)=\mathcal C(p,w,p)=\mathcal C(w,p,p)=0$. Expanding the slots $(p,F,F)$, $(F,p,F)$, $(F,F,p)$ and $(F,F,F)$ by trilinearity gives exactly (186.3). These four slots, together with the slots containing at most one $F$, form all of the two-dimensional tensor basis, so they are necessary and sufficient for tensor preservation. The legality conditions are precisely the pointwise simplex conditions for the resulting common-first tuple. $\square$

Thus the exceptional scalar branch is a shear problem along the fixed nonzero class $[w]$, with no remaining freedom in the direction. Equation (186.3) does not by itself rule out a nonzero amplitude: it supplies the exact compatibility test for that case. Out-of-span tensor-preserving lifts, the radical alternative, arbitrary partitions, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization remain open.

## 187. The ordered source makes the exceptional scalar impossible

The source propagation identity gives a strict sign to the scalar that remained exceptional in Section 185. This removes the $d=b$ branch for the retained heat source.

**Proposition 187.1 (strict ordered coefficient gap).** Retain Definition 175.1 and the coefficient notation of Proposition 185.1. Then

$$
d-b
=-\frac{p^2}{2}\,\langle q,(I-P)g\rangle_m
=-\frac{p^2}{2c}\,\langle q,(P-P^2)q\rangle_m
<0.
\tag{187.1}
$$

Consequently, the exceptional condition $d=b$ cannot occur for any allowed original source parameters or permitted representative, and every in-span common-first tensor-preserving lift is the baseline $v=0$ as an $m$-class.

*Proof.* From $Pp=p$ and the definition of the ordered form,

$$
a=p^3\int_Gg\,dm=p^3,
\qquad
b=p^2\langle Pg,F\rangle_m,
\qquad
d=p^2\langle g,F\rangle_m.
$$

Since $P1=1$ and $P$ is self-adjoint, $\langle1,(I-P)g\rangle_m=0$. Using $F=(3/4-q)/2$ therefore gives the first equality in (187.1). The source propagation identity is $Pq=cg$. Hence $g=c^{-1}Pq$, and self-adjointness gives

$$
\langle q,(I-P)g\rangle_m
=\frac1c\langle q,(P-P^2)q\rangle_m,
$$

which proves the second equality.

Write $b_{\mathrm{src}}$ for the representative called $b$ in (175.1), so $q=cb_{\mathrm{src}}$. The retained source-start nonconstancy result makes $b_{\mathrm{src}}$, and hence $q$, nonconstant. The full conservative generator has $\ker K=\mathbb C1$, while $P=T_d=e^{-dK}$. Spectral calculus thus yields

$$
\langle q,(P-P^2)q\rangle_m
=\int_{[0,\infty)}e^{-d\lambda}(1-e^{-d\lambda})\,d\langle q,E_K(\lambda)q\rangle_m>0,
$$

because the nonconstant $q$ has nonzero spectral mass on $(0,\infty)$ and the displayed multiplier is strictly positive there. This proves the strict inequality in (187.1). The final claim follows from Proposition 185.1: its alternative $d\ne b$ forces $r=0$ and $s=1$, hence $[v]=0$. $\square$

The common-first in-span slice is therefore fully rigid for the retained source: its only exact tensor-preserving displacement is the baseline class. Out-of-span tensor-preserving lifts, the radical alternative, arbitrary partitions, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization remain open.

## 188. A source-span witness removes the radical alternative

The radical alternative of Section 179 can be tested using the source label itself. This requires no pointwise preservation of the terminal pair and no chosen representation of the candidate partition beyond its span.

**Proposition 188.1 (source-span radical triviality).** Retain Definition 175.1 and Definition 179.1. Let $u$ be a bounded pointwise partition whose sixty-four residuals all vanish. Suppose that there are real coefficients $(\gamma_y)_{y\in\mathcal L}$ such that

$$
q=\sum_{y\in\mathcal L}\gamma_yu_y
$$

as an $m$-class. Then

$$
\operatorname{Rad}_1(\mathcal W_u)
\cap\operatorname{Rad}_2(\mathcal W_u)
\cap\operatorname{Rad}_3(\mathcal W_u)=\{0\}
$$

as $m$-classes. Consequently, every such full-zero partition has the common-first form

$$
u_0=u_1=F+v,
\qquad
u_3=q-2v,
\qquad
u_B=p
$$

for a bounded real Borel $m$-class $v$ satisfying the pointwise simplex inequalities.

*Proof.* Let $h$ belong to the displayed intersection. By the coefficient hypothesis, both $h$ and $q$ belong to $\mathcal W_u$. The first radical condition, with its two arguments chosen as $h$ and $q$, gives

$$
0=\mathcal C(h,h,q)=q_{003}(h).
$$

The source-specific energy identity retained in (175.4) gives

$$
q_{003}(h)=c\,\|T_{d/2}(gh)\|_2^2.
$$

Since $c>0$, this vanishes only when $h=0$ as an $m$-class. The common intersection is therefore trivial, and Corollary 179.3 gives the stated common-first representation. $\square$

The span hypothesis is weaker than a prescribed pointwise identity for $u_3+u_B$: the latter, together with the partition sum, supplies $q$ in $\mathcal W_u$, while Proposition 188.1 uses only the resulting $m$-class witness. Thus any full-zero partition with a source-span witness has no radical escape, even when its terminal labels have no retained affine channel.

## 189. Three source-propagation modes exclude a class of out-of-span lifts

Once the source-span witness has reduced a full-zero partition to the common-first slice, the three slots containing two constant labels impose orthogonality to the first three source-propagation modes. The source density lemma makes those modes linearly independent.

**Proposition 189.1 (three-mode source-orbit exclusion).** Retain Definition 175.1. Let

$$
u_0=u_1=F+v,
\qquad
u_3=q-2v,
\qquad
u_B=p
$$

be a pointwise legal common-first tuple with bounded real Borel representative $v$. If all sixty-four residuals vanish and

$$
[v]\in
\operatorname{span}_{\mathbb R}
\{Pq,P^2q,P^3q\}
$$

as an $m$-class, then $[v]=0$.

*Proof.* The three residuals with two $B$ labels give

$$
\begin{aligned}
0=\Delta(u)_{0BB}&=\mathcal C(v,p,p),\\
0=\Delta(u)_{B0B}&=\mathcal C(p,v,p),\\
0=\Delta(u)_{BB0}&=\mathcal C(p,p,v).
\end{aligned}
$$

Because $p$ is constant and $Pp=p$, self-adjointness of $P$ rewrites these equations as

$$
\langle g,v\rangle_m=0,
\qquad
\langle Pg,v\rangle_m=0,
\qquad
\langle P^2g,v\rangle_m=0.
\tag{189.1}
$$

The source propagation identity $Pq=cg$ changes (189.1) into

$$
\langle Pq,v\rangle_m
=\langle P^2q,v\rangle_m
=\langle P^3q,v\rangle_m
=0.
\tag{189.2}
$$

The three vectors in (189.2) are linearly independent. Indeed, a linear relation among them would, after substituting $Pq=cg$, give a nonzero polynomial relation $r(P)g=0$ of degree at most two, contradicting Lemma 169.1. Since $v$ lies in their span and is orthogonal to each of them, its Gram matrix is positive definite and $[v]=0$. $\square$

This excludes every common-first displacement in the three-mode source orbit, including any such displacement outside $\operatorname{span}\{p,F\}$. The remaining out-of-span directions lie outside this finite source-mode plane and still require the full nonlinear common-first equations; the radical alternative without a source-span witness, arbitrary partitions, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization remain open.

## 190. The candidate source anchor identifies the radical image

Even when the candidate span does not contain the original source label $q$, the full-zero tensor transports a canonical source anchor into that span. Its positive quadratic form gives an exact description of the radical alternative.

**Proposition 190.1 (candidate source anchor and radical exactness).** Retain Definition 175.1 and Definition 179.1. Let $u$ be a bounded pointwise partition whose sixty-four residuals all vanish. For a real label vector $a=(a_y)_{y\in\mathcal L}$ write

$$
F_a=\sum_{y\in\mathcal L}a_yf_y,
\qquad
H_a=\sum_{y\in\mathcal L}a_yu_y,
$$

and define the candidate source anchor

$$
Q_u=-2u_0+3u_B.
\tag{190.1}
$$

Then, for all real label vectors $a,b$,

$$
\mathcal C(H_a,H_b,Q_u)
=\mathcal C(F_a,F_b,q),
\tag{190.2}
$$

and in particular

$$
\mathcal C(H_a,H_a,Q_u)
=c\,\|T_{d/2}(gF_a)\|_2^2.
\tag{190.3}
$$

Consequently,

$$
\ker(a\mapsto H_a)\subseteq\ker(a\mapsto F_a),
\tag{190.4}
$$

and the common radical is exactly the image of the baseline relation space:

$$
\operatorname{Rad}_1(\mathcal W_u)
\cap\operatorname{Rad}_2(\mathcal W_u)
\cap\operatorname{Rad}_3(\mathcal W_u)
=\{H_a:F_a=0\}.
\tag{190.5}
$$

*Proof.* The baseline coefficient vector $\gamma=(-2,0,0,3)$ satisfies

$$
F_\gamma=-2F+3p=q,
$$

so $H_\gamma=Q_u$. Contracting the zero residual tensor with the three coefficient vectors $a,b,\gamma$ gives (190.2). Taking $a=b$ and applying the source-specific identity in (175.4) to the bounded class $F_a$ gives (190.3).

If $H_a=0$, then (190.3) is zero. The strictness of the same source energy for a nonzero $m$-class forces $F_a=0$, proving (190.4).

For the inclusion from right to left in (190.5), Proposition 179.2 applies to every $a$ with $F_a=0$. Conversely, let $h$ belong to the common radical. Since $h\in\mathcal W_u$, choose $a$ with $h=H_a$. The anchor $Q_u$ belongs to $\mathcal W_u$, so the first radical condition gives $\mathcal C(h,h,Q_u)=0$. Equation (190.3) then forces $F_a=0$, placing $h$ in the right-hand side of (190.5). $\square$

Thus the radical alternative is not an unstructured loss of rank: it is precisely the image, under the candidate label map, of the two baseline linear relations. Proposition 188.1 is recovered whenever $q$ itself belongs to $\mathcal W_u$, because the positive source form can then be evaluated with $q$ as the third radical argument. Without that span witness, (190.5) is the exact remaining algebraic boundary; arbitrary partitions, the out-of-span directions outside the source-mode plane, $F_{64}$, $H43$, SRS$\text{-}20$, physical succession and Lean/kernel formalization remain open.

## 191. The candidate span has a rank--radical trichotomy

The exact radical description in Section 190 also fixes the possible dimensions of the candidate span. The baseline labels have a two-dimensional image, and the candidate label map cannot identify more relations than the baseline map. Thus a full-zero partition can have only ranks two, three or four, with the radical dimension recording the excess rank.

**Definition 191.1 (baseline and candidate label maps).** For a bounded partition $u$ as in Proposition 190.1, define

$$
\Phi_f:\mathbb R^{\mathcal L}\longrightarrow L^\infty(m;\mathbb R),
\qquad
\Phi_f(a)=F_a,
$$

and

$$
\Phi_u:\mathbb R^{\mathcal L}\longrightarrow \mathcal W_u,
\qquad
\Phi_u(a)=H_a.
\tag{191.1}
$$

Write $r_u=\dim\mathcal W_u=\operatorname{rank}\Phi_u$, and let

$$
\mathcal R_u=\mathcal W_u\cap
\operatorname{Rad}_1(\mathcal W_u)\cap
\operatorname{Rad}_2(\mathcal W_u)\cap
\operatorname{Rad}_3(\mathcal W_u).
\tag{191.2}
$$

Here the intersection with $\mathcal W_u$ records the common radical inside the candidate span.

**Proposition 191.2 (rank--radical trichotomy).** Suppose that $u$ is a bounded pointwise partition whose sixty-four residuals all vanish. Then

$$
\ker\Phi_u\subseteq\ker\Phi_f,
\qquad
\dim\ker\Phi_f=2,
\qquad
\mathcal R_u=\Phi_u(\ker\Phi_f),
\tag{191.3}
$$

and therefore

$$
\dim\mathcal R_u
=2-\dim\ker\Phi_u
=r_u-2,
\qquad
r_u\in\{2,3,4\}.
\tag{191.4}
$$

In particular,

$$
\begin{array}{c|c|c}
 r_u & \dim\mathcal R_u & \text{equivalent condition}\\
\hline
 2 & 0 & \ker\Phi_u=\ker\Phi_f\\
 3 & 1 & \dim\mathcal R_u=1\\
 4 & 2 & \dim\mathcal R_u=2
\end{array}
\tag{191.5}
$$

The rank-two case is exactly the radical-free case; hence it reduces to the common-first form of Corollary 179.3.

*Proof.* The baseline identities are

$$
F_0=F_1=F,
\qquad
F_3=q,
\qquad
F_B=p,
\qquad
2F+q=3p.
\tag{191.6}
$$

The source nonconstancy retained in Proposition 187.1 says that $q$ is nonconstant, while $p=1/4$ is constant and $F=(3/4-q)/2$. Hence

$$
\operatorname{im}\Phi_f=\operatorname{span}_{\mathbb R}\{1,q\}
$$

has dimension two. Since $\mathbb R^{\mathcal L}$ has dimension four,

$$
\dim\ker\Phi_f=2.
\tag{191.7}
$$

The kernel inclusion in (191.3) is (190.4), and the radical identity in (191.3) is (190.5), with the ambient intersection in (191.2) made explicit. Rank--nullity gives

$$
\dim\ker\Phi_u=4-r_u.
\tag{191.8}
$$

Because $\ker\Phi_u\subseteq\ker\Phi_f$ and the latter has dimension two, (191.8) gives $r_u\ge2$; the four labels give $r_u\le4$. Finally, restricting $\Phi_u$ to the two-dimensional space $\ker\Phi_f$ and using $\ker\Phi_u\subseteq\ker\Phi_f$ yields

$$
\dim\Phi_u(\ker\Phi_f)
=\dim\ker\Phi_f-\dim\ker\Phi_u
=2-(4-r_u)=r_u-2.
\tag{191.9}
$$

This proves (191.4) and the table. If $r_u=2$, then $\dim\ker\Phi_u=2$ and the inclusion between two-dimensional kernels is equality, so $\mathcal R_u=0$. The converse follows from (191.4). Corollary 179.3 then supplies the common-first representation. $\square$

Thus the radical alternative has no untracked intermediate size: rank three carries exactly one radical direction and rank four carries exactly two. The rank-two branch is the only branch on which the radical reduction is automatic, while rank-three and rank-four branches are the precise remaining arbitrary-partition cases. This classification does not rule out either of those branches, nor does it settle the out-of-span nonlinear equations, $F_{64}$, $H43$, SRS\text{-}20, physical succession or Lean/kernel formalization.

## 192. The radical is transverse to the first three source modes

The rank-three and rank-four branches from Section 191 cannot hide their radical directions inside the source orbit already controlled by the constant label. The partition identity puts $1$ in the candidate span, and the three radical slots with that constant label force orthogonality to the first three propagated source modes.

**Definition 192.1 (the three-mode source plane).** Retain the source operator $P$ and source label $q$ of Definition 175.1, and set

$$
\mathcal S_q=\operatorname{span}_{\mathbb R}\{Pq,P^2q,P^3q\}
\subset L^2(m;\mathbb R).
\tag{192.1}
$$

For a full-zero partition, let $\mathcal R_u$ be the common radical inside $\mathcal W_u$ from Definition 191.1.

**Proposition 192.2 (source-mode transversality).** If $u$ is a bounded pointwise partition whose sixty-four residuals all vanish, then every $h\in\mathcal R_u$ satisfies

$$
\langle g,h\rangle_m
=\langle Pg,h\rangle_m
=\langle P^2g,h\rangle_m
=0,
\tag{192.2}
$$

and therefore

$$
\langle Pq,h\rangle_m
=\langle P^2q,h\rangle_m
=\langle P^3q,h\rangle_m
=0.
\tag{192.3}
$$

Consequently,

$$
\mathcal R_u\cap\mathcal S_q=\{0\},
\qquad
\mathcal R_u\subseteq\mathcal S_q^{\perp_m}.
\tag{192.4}
$$

Combined with Proposition 191.2, a rank-three full-zero partition has a one-dimensional radical outside $\mathcal S_q$, and a rank-four full-zero partition has a two-dimensional radical outside $\mathcal S_q$.

*Proof.* The partition identity gives

$$
1=u_0+u_1+u_3+u_B\in\mathcal W_u.
\tag{192.5}
$$

Let $h\in\mathcal R_u$. Since $h$ lies in each of the three slot radicals and $1$ is an allowed argument in $\mathcal W_u$, the three choices of the slot occupied by $h$ give

$$
\mathcal C(h,1,1)=0,
\qquad
\mathcal C(1,h,1)=0,
\qquad
\mathcal C(1,1,h)=0.
\tag{192.6}
$$

Using $P1=1$ and self-adjointness of $P$, these identities are respectively

$$
\langle g,h\rangle_m=0,
\qquad
\langle Pg,h\rangle_m=0,
\qquad
\langle P^2g,h\rangle_m=0,
$$

which proves (192.2). The source propagation identity $Pq=cg$ with $c>0$ gives

$$
Pq=cg,
\qquad
P^2q=cPg,
\qquad
P^3q=cP^2g.
$$

Substitution into (192.2) proves (192.3).

By Lemma 169.1, the three vectors $Pq,P^2q,P^3q$ are linearly independent. Their Gram matrix in the positive $L^2(m)$ inner product is therefore positive definite. If $h\in\mathcal R_u\cap\mathcal S_q$, (192.3) says that $h$ is orthogonal to every vector in $\mathcal S_q$; taking the inner product with $h$ itself gives $\|h\|_2^2=0$. Thus $h=0$ as an $m$-class, proving (192.4). The dimension statements follow from (191.4). $\square$

Hence any nontrivial rank-three or rank-four radical must be sought in the complement of the first three source-propagation modes. This is a necessary geometric condition, not a nonexistence proof: the out-of-plane radical, the remaining nonlinear common-first equations, arbitrary partitions beyond the rank trichotomy, $F_{64}$, $H43$, SRS\text{-}20, physical succession and Lean/kernel formalization remain open.

## 193. The radical obeys a weighted candidate-span barrier

The constant-label calculation in Section 192 is the first member of a larger family. Every candidate-span function can be inserted beside a radical element, producing two weighted mode-annihilation spaces. These spaces give an exact finite-dimensional barrier for any rank-three or rank-four escape.

**Definition 193.1 (weighted candidate-span mode spaces).** For a bounded full-zero partition $u$, define

$$
\begin{aligned}
\mathcal M_u
  &=\operatorname{span}_{\mathbb R}
    \{P(gw),P^2(gw):w\in\mathcal W_u\},\\
\mathcal N_u
  &=\operatorname{span}_{\mathbb R}
    \{Pw,P^2w:w\in\mathcal W_u\}
    \subset L^2(m;\mathbb R).
\end{aligned}
\tag{193.1}
$$

Here products such as $gw$ are pointwise products of bounded representatives, and the heat contraction places all displayed functions in $L^2(m)$.

**Proposition 193.2 (weighted radical annihilation).** If $u$ has all sixty-four residuals equal to zero and $h\in\mathcal R_u$, then

$$
\langle h,\phi\rangle_m=0
\quad(\phi\in\mathcal M_u),
\qquad
\langle gh,\psi\rangle_m=0
\quad(\psi\in\mathcal N_u).
\tag{193.2}
$$

Equivalently,

$$
\mathcal R_u\subseteq\mathcal M_u^{\perp_m},
\qquad
g\mathcal R_u\subseteq\mathcal N_u^{\perp_m}.
\tag{193.3}
$$

In particular, since $1\in\mathcal W_u$, every radical element is orthogonal to $Pg$ and $P^2g$ and its $g$-weighted class is orthogonal to $P1=P^21=1$; together with Section 192 this gives the first three source-mode constraints for every radical direction.

*Proof.* Let $w\in\mathcal W_u$. Because $h$ lies in the first, middle and terminal slot radicals, the four contractions with the constant candidate function $1\in\mathcal W_u$ vanish:

$$
\mathcal C(w,h,1)=0,
\qquad
\mathcal C(w,1,h)=0,
\qquad
\mathcal C(h,w,1)=0,
\qquad
\mathcal C(h,1,w)=0.
\tag{193.4}
$$

Using $P1=1$ and self-adjointness of $P$, these equations become

$$
\begin{aligned}
0=\mathcal C(w,h,1)
  &=\int_Ggw\,P h\,dm
   =\langle P(gw),h\rangle_m,\\
0=\mathcal C(w,1,h)
  &=\int_Ggw\,P^2h\,dm
   =\langle P^2(gw),h\rangle_m,\\
0=\mathcal C(h,w,1)
  &=\int_Ggh\,Pw\,dm
   =\langle gh,Pw\rangle_m,\\
0=\mathcal C(h,1,w)
  &=\int_Ggh\,P^2w\,dm
   =\langle gh,P^2w\rangle_m.
\end{aligned}
\tag{193.5}
$$

As $w$ ranges over $\mathcal W_u$, (193.5) is exactly (193.2)--(193.3). Taking $w=1$ shows that $Pg$ and $P^2g$ belong to $\mathcal M_u$ and that $gh$ is orthogonal to $1$; the missing $g$ mode is supplied by $\mathcal C(h,1,1)=0$ in Section 192. $\square$

Thus a rank-three radical must satisfy one weighted annihilation system and a rank-four radical must satisfy two independent directions in the same system, in addition to lying in $\mathcal S_q^{\perp_m}$. This is a necessary barrier for the remaining out-of-plane branches, not a nonexistence proof: the dimensions of $\mathcal M_u$ and $\mathcal N_u$ may collapse, and the residual-zero partition, $F_{64}$, $H43$, SRS\text{-}20, physical succession and Lean/kernel formalization remain open.

## 194. A rank-deficit detector for the radical branches

The annihilation spaces of Section 193 give a finite-dimensional test before solving the remaining nonlinear equations. Their left nullities must be large enough to contain the radical dimensions forced by the rank trichotomy.

**Definition 194.1 (weighted mode matrices).** Let $u$ be a full-zero bounded partition, put $r_u=\dim\mathcal W_u$, and choose a basis $(w_1,\ldots,w_{r_u})$ of $\mathcal W_u$. Define linear maps

$$
\begin{aligned}
\mathsf L_u:\mathcal W_u&\longrightarrow\mathbb R^{2r_u},
&\mathsf L_u(h)
  &=\bigl(\langle h,P(gw_j)\rangle_m,
          \langle h,P^2(gw_j)\rangle_m\bigr)_{j=1}^{r_u},\\
\mathsf K_u:\mathcal W_u&\longrightarrow\mathbb R^{2r_u},
&\mathsf K_u(h)
  &=\bigl(\langle gh,Pw_j\rangle_m,
          \langle gh,P^2w_j\rangle_m\bigr)_{j=1}^{r_u}.
\end{aligned}
\tag{194.1}
$$

Changing the basis of $\mathcal W_u$ only applies an invertible change of coordinates to the displayed families, so their kernels are intrinsic.

**Proposition 194.2 (forced nullity).** If all sixty-four residuals of $u$ vanish, then

$$
\mathcal R_u\subseteq\ker\mathsf L_u\cap\ker\mathsf K_u,
\tag{194.2}
$$

and consequently

$$
\dim\ker\mathsf L_u\ge r_u-2,
\qquad
\dim\ker\mathsf K_u\ge r_u-2.
\tag{194.3}
$$

Thus a rank-three full-zero partition requires each map in (194.1) to have a nonzero kernel, while a rank-four full-zero partition requires each to have nullity at least two. If either nullity is smaller than $r_u-2$, that rank branch is impossible.

*Proof.* Proposition 193.2 gives, for every $h\in\mathcal R_u$ and every basis element $w_j$,

$$
\langle h,P(gw_j)\rangle_m
=\langle h,P^2(gw_j)\rangle_m
=0,
$$

and

$$
\langle gh,Pw_j\rangle_m
=\langle gh,P^2w_j\rangle_m
=0.
$$

These are exactly the two coordinate families in (194.1), proving (194.2). Proposition 191.2 gives

$$
\dim\mathcal R_u=r_u-2.
$$

The inclusion (194.2) then gives both nullity inequalities in (194.3). The final exclusion statement is the contrapositive of either inequality. $\square$

The test is finite-dimensional and basis-independent: a proposed rank-three or rank-four fibre must first exhibit the required nullity in both weighted mode matrices before its nonlinear residual equations can be solved. This is a necessary filter, not a nonexistence theorem; nullity may occur accidentally, and arbitrary partition realization, $F_{64}$, $H43$, SRS\text{-}20, physical succession and Lean/kernel formalization remain open.

## 195. Saturated weighted kernels identify the radical

The nullity inequalities of Section 194 become an exact identification whenever one of the weighted mode maps is saturated. This separates the finite-dimensional radical calculation from the remaining nonlinear residual equations.

**Proposition 195.1 (saturated-kernel identification).** Let $u$ be a full-zero bounded partition and put $r_u=\dim\mathcal W_u$. If

$$
\dim\ker\mathsf L_u=r_u-2,
\tag{195.1}
$$

then

$$
\ker\mathsf L_u=\mathcal R_u.
\tag{195.2}
$$

Likewise,

$$
\dim\ker\mathsf K_u=r_u-2
\quad\Longrightarrow\quad
\ker\mathsf K_u=\mathcal R_u.
\tag{195.3}
$$

If both equalities in (195.1) and (195.3) hold, then

$$
\ker\mathsf L_u=\ker\mathsf K_u=\mathcal R_u,
\tag{195.4}
$$

so the common radical is obtained by solving either finite-dimensional weighted kernel system.

*Proof.* Proposition 194.2 gives the inclusions

$$
\mathcal R_u\subseteq\ker\mathsf L_u,
\qquad
\mathcal R_u\subseteq\ker\mathsf K_u,
$$

while Proposition 191.2 gives $\dim\mathcal R_u=r_u-2$. Under (195.1), the two subspaces $\mathcal R_u$ and $\ker\mathsf L_u$ have the same finite dimension, so the first inclusion is equality. The proof for $\mathsf K_u$ is identical, and (195.4) follows when both maps are saturated. $\square$

**Corollary 195.2 (conditional closure of the radical branch).** Under the hypotheses of Proposition 195.1, if either weighted map is saturated and its kernel is zero, then $r_u=2$ and the partition lies in the radical-free common-first branch of Corollary 179.3. More generally, for a rank-three or rank-four candidate, any additional independent weighted-mode equation that reduces the corresponding kernel below $r_u-2$ rules out that rank immediately.

*Proof.* If a saturated map has zero kernel, then (195.1) gives $r_u-2=0$, hence $r_u=2$. Proposition 191.2 then gives $\mathcal R_u=0$, and Corollary 179.3 supplies the common-first reduction. The final statement is the exclusion direction of Proposition 194.2. $\square$

The saturated case supplies a concrete finite-dimensional route: first compute the two weighted kernels, then either identify the radical exactly or exclude the proposed rank. Saturation is not known for every candidate, so the unsaturated rank-three and rank-four branches, the nonlinear residual equations, arbitrary partition realization, $F_{64}$, $H43$, SRS\text{-}20, physical succession and Lean/kernel formalization remain open.

## 196. The joint weighted map has a two-dimensional visible quotient

Section 195 tests the two weighted mode maps separately. Their information can be combined before imposing either individual saturation hypothesis. The resulting map sees at most the two dimensions left after the radical has been removed.

**Definition 196.1 (joint weighted mode map).** With the notation of Definition 194.1, define

$$
\mathsf J_u:
\mathcal W_u\longrightarrow\mathbb R^{4r_u},
\qquad
\mathsf J_u(h)=\bigl(\mathsf L_u(h),\mathsf K_u(h)\bigr).
\tag{196.1}
$$

Changing the basis of $\mathcal W_u$ changes the coordinate presentation of $\mathsf J_u$ by invertible transformations on its source and target, so its rank and kernel are intrinsic.

**Proposition 196.2 (joint rank bound and exact-kernel criterion).** If $u$ is a full-zero bounded partition, then

$$
\mathcal R_u\subseteq\ker\mathsf J_u,
\qquad
\operatorname{rank}\mathsf J_u\le2.
\tag{196.2}
$$

More precisely,

$$
\dim\bigl(\ker\mathsf J_u/\mathcal R_u\bigr)
 =2-\operatorname{rank}\mathsf J_u,
\tag{196.3}
$$

and therefore

$$
\operatorname{rank}\mathsf J_u=2
\quad\Longleftrightarrow\quad
\ker\mathsf J_u=\mathcal R_u.
\tag{196.4}
$$

In particular, a rank-three candidate has a one-dimensional joint kernel at the saturation value $2$, and a rank-four candidate has a two-dimensional joint kernel at that value. A computed joint rank greater than $2$ rules out a full-zero partition before the nonlinear residual equations are solved.

*Proof.* Proposition 194.2 gives

$$
\mathcal R_u\subseteq\ker\mathsf L_u
\cap\ker\mathsf K_u
=\ker\mathsf J_u.
$$

Proposition 191.2 gives $\dim\mathcal R_u=r_u-2$. Rank--nullity applied to $\mathsf J_u$ therefore yields

$$
\operatorname{rank}\mathsf J_u
 =r_u-\dim\ker\mathsf J_u
\le r_u-(r_u-2)=2,
$$

which is (196.2). Since $\mathcal R_u$ is a subspace of $\ker\mathsf J_u$, the quotient in (196.3) is defined, and

$$
\dim(\ker\mathsf J_u/\mathcal R_u)
 =\dim\ker\mathsf J_u-\dim\mathcal R_u
 =(r_u-\operatorname{rank}\mathsf J_u)-(r_u-2)
 =2-\operatorname{rank}\mathsf J_u.
$$

This proves (196.3). The equality of kernels in (196.4) is equivalent to the quotient dimension being zero, which by (196.3) is equivalent to joint rank $2$. The rank-three and rank-four statements use $\dim\mathcal R_u=r_u-2$ from Proposition 191.2. The contrapositive of the rank bound gives the exclusion test. $\square$

**Corollary 196.3 (the unsaturated residual boundary).** For a full-zero rank-three or rank-four candidate, the joint weighted probes have exactly three possible outcomes:

$$
\begin{array}{c|c}
\operatorname{rank}\mathsf J_u & \dim(\ker\mathsf J_u/\mathcal R_u)\\
\hline
2&0\\
1&1\\
0&2
\end{array}
$$

The first row identifies the radical without requiring $\mathsf L_u$ or $\mathsf K_u$ to be saturated separately. In the other two rows, the weighted equations leave respectively one or two quotient directions beyond the forced radical; those directions must still satisfy the original nonlinear residual equations. Thus individual unsaturation is not itself an escape, while joint rank at most one records the exact remaining finite-dimensional ambiguity.

The joint rank test is a necessary filter for the unsaturated branches. It does not evaluate the rank for an actual arbitrary partition, construct a residual-zero rank-three or rank-four partition, settle $F_{64}$, $H43$, SRS\text{-}20, physical succession or Lean/kernel formalization.

## 197. The radical quotient is canonically the baseline tensor

The rank bound in Section 196 can be sharpened from a dimension statement to a canonical quotient construction. Every full-zero candidate has a linear projection onto the two-dimensional baseline span, and the only directions lost by that projection are exactly the common radical directions.

**Definition 197.1 (the baseline target and the quotient map).** Let

$$
E_f=\operatorname{im}\Phi_f
 =\operatorname{span}_{\mathbb R}\{p,q\}
$$

for the baseline label map of Definition 191.1. For a full-zero bounded partition $u$, define on the candidate span

$$
T_u:\mathcal W_u\longrightarrow E_f,
\qquad
T_u(H_a)=F_a.
\tag{197.1}
$$

Here $a$ is any real label vector with $H_a\in\mathcal W_u$.

**Proposition 197.2 (canonical quotient reconstruction).** If all sixty-four residuals of $u$ vanish, then $T_u$ is a well-defined surjective linear map and

$$
\ker T_u=\mathcal R_u,
\qquad
\mathcal W_u/\mathcal R_u\ \cong\ E_f.
\tag{197.2}
$$

More precisely, the induced map

$$
\overline T_u:\mathcal W_u/\mathcal R_u\longrightarrow E_f,
\qquad
\overline T_u([x])=T_u(x),
\tag{197.3}
$$

is an isomorphism, and for every $x,y,z\in\mathcal W_u$,

$$
\mathcal C(x,y,z)
 =\mathcal C\bigl(T_u x,T_u y,T_u z\bigr).
\tag{197.4}
$$

Thus the trilinear form induced by $\mathcal C$ on the quotient is exactly the restriction of the baseline form to $E_f$.

*Proof.* Suppose that $H_a=H_b$. Then $a-b\in\ker\Phi_u$, and Proposition 191.2 gives $\ker\Phi_u\subseteq\ker\Phi_f$. Hence $F_a=F_b$, so (197.1) is independent of the representing label vector. Linearity is immediate from the definitions of $H_a$ and $F_a$.

For every $F_a\in E_f$, the element $H_a\in\mathcal W_u$ satisfies $T_u(H_a)=F_a$, proving surjectivity. Moreover,

$$
T_u(H_a)=0
\quad\Longleftrightarrow\quad
F_a=0.
$$

Proposition 190.1 identifies the set of such $H_a$ with the common radical, so $\ker T_u=\mathcal R_u$. The first isomorphism theorem gives (197.2)--(197.3).

For $x=H_a$, $y=H_b$ and $z=H_c$, the full-zero residual identity gives

$$
\mathcal C(x,y,z)
 =\mathcal C(F_a,F_b,F_c)
 =\mathcal C(T_ux,T_uy,T_uz).
$$

Every element of $\mathcal W_u$ has this form, so (197.4) follows. Since each element of $\mathcal R_u$ is a radical in every slot, the left-hand side of (197.4) is independent of the representatives of the quotient classes; consequently it is precisely the quotient trilinear form, and (197.4) identifies that form with the baseline restriction. $\square$

**Corollary 197.3 (what the rank branches mean).** For a full-zero partition,

$$
\dim(\mathcal W_u/\mathcal R_u)=2,
$$

and the three rank branches have the following canonical interpretation:

$$
\begin{array}{c|c|c}
\dim\mathcal W_u & \dim\mathcal R_u & \text{quotient description}\\
\hline
2&0& T_u\text{ is an isomorphism},\\
3&1& \text{one invisible radical extension of }E_f,\\
4&2& \text{two invisible radical extensions of }E_f.
\end{array}
\tag{197.5}
$$

Any linear complement of $\mathcal R_u$ in $\mathcal W_u$ therefore carries a copy of the baseline tensor through $T_u$, but the complement is not canonical and need not respect the pointwise simplex constraints. In particular, (197.5) does not construct a rank-three or rank-four partition and does not eliminate the out-of-plane lift problem. The arbitrary-partition realization, the residual-zero search beyond the quotient, $F_{64}$, $H43$, SRS\text{-}20, physical succession and Lean/kernel formalization remain open.

## 198. The full-zero fibre is an affine radical lift

The quotient reconstruction makes the remaining radical freedom explicit. Once one full-zero candidate is fixed, every other legal label family in the same candidate span with the same quotient labels differs from it by finitely many common-radical functions, and the residual tensor cannot see those differences.

**Definition 198.1 (a normalized quotient section).** Retain the notation of Section 197 for a full-zero bounded partition $u$. Since

$$
1=u_0+u_1+u_3+u_B\in\mathcal W_u,
\qquad
T_u(1)=1,
$$

choose a linear section

$$
S_u:E_f\longrightarrow\mathcal W_u,
\qquad
T_u\circ S_u=\operatorname{id}_{E_f},
\qquad
S_u(1)=1.
\tag{198.1}
$$

For each label $y\in\mathcal L$, put

$$
\rho_y=u_y-S_u(f_y).
\tag{198.2}
$$

**Proposition 198.2 (radical-fibre normal form).** The corrections in (198.2) satisfy

$$
\rho_y\in\mathcal R_u,
\qquad
\sum_{y\in\mathcal L}\rho_y=0,
\qquad
\mathcal R_u=\operatorname{span}_{\mathbb R}\{\rho_y:y\in\mathcal L\}.
\tag{198.3}
$$

Let $(\widetilde\rho_y)_{y\in\mathcal L}$ be any family of elements of $\mathcal R_u$ with

$$
\sum_{y\in\mathcal L}\widetilde\rho_y=0,
\tag{198.4}
$$

and define

$$
\widetilde u_y=S_u(f_y)+\widetilde\rho_y.
\tag{198.5}
$$

If the four functions in (198.5) are pointwise nonnegative and sum to one, then their sixty-four residuals vanish. Consequently, inside the fixed span and quotient data, the full-zero families are exactly the intersection of the affine radical fibre

$$
\left\{\bigl(S_u(f_y)+\widetilde\rho_y\bigr)_{y\in\mathcal L}:
\widetilde\rho_y\in\mathcal R_u,\ \sum_y\widetilde\rho_y=0\right\}
\tag{198.6}
$$

with the pointwise simplex constraints.

*Proof.* By (197.1),

$$
T_u(\rho_y)=T_u(u_y)-T_u(S_u(f_y))=f_y-f_y=0,
$$

so $\rho_y\in\ker T_u=\mathcal R_u$ by Proposition 197.2. The baseline labels satisfy $\sum_yf_y=1$, and (198.1) gives

$$
\sum_y\rho_y=\sum_yu_y-S_u\left(\sum_yf_y\right)=1-S_u(1)=0.
$$

To prove the spanning assertion, let $r\in\mathcal R_u$. Choose $x\in\mathcal W_u$ with $T_u(x)=0$ and write $x=\sum_y a_yu_y$. Then

$$
r=x-S_u(T_u x)=\sum_y a_y\bigl(u_y-S_u(f_y)\bigr)=\sum_y a_y\rho_y,
$$

which proves (198.3).

For the converse, every $\widetilde u_y$ belongs to $\mathcal W_u$, and (198.4) together with (198.1) gives $\sum_y\widetilde u_y=1$. The pointwise hypotheses therefore make it a legal bounded partition. Since each $\widetilde\rho_y$ is in the common radical, multilinearity removes every term containing a correction from

$$
\mathcal C(\widetilde u_y,\widetilde u_z,\widetilde u_k).
$$

The remaining term is

$$
\mathcal C(S_u(f_y),S_u(f_z),S_u(f_k))
 =\mathcal C(f_y,f_z,f_k)
$$

by (197.4). Thus every residual is zero. Conversely, any full-zero family in the fixed $\mathcal W_u$ with the same quotient labels is recovered by (198.2), so it lies in (198.6). $\square$

**Corollary 198.3 (the residual search becomes a fibre-feasibility search).** For a rank-three or rank-four full-zero candidate, the nonlinear residual equations impose no additional conditions after the quotient identity: all remaining freedom is respectively a one- or two-dimensional radical correction subject to (198.4) and the pointwise simplex inequalities. In the rank-two branch, $\mathcal R_u=0$, so the normalized quotient section determines the label family uniquely inside its candidate span.

This is an exact closure statement for a fixed candidate span, not an existence theorem. It does not produce a nonzero radical, guarantee that any correction satisfies the pointwise inequalities, or settle arbitrary partition realization, $F_{64}$, $H43$, SRS\text{-}20, physical succession or Lean/kernel formalization.

## 199. The radical fibre has a finite coefficient feasibility body

The affine description in Section 198 can be made finite-dimensional after choosing a basis of the radical. The residual equations disappear, while legality becomes an intersection of pointwise affine half-spaces in the coefficient matrix.

**Definition 199.1 (radical coefficient set).** Let

$$
d_u=\dim\mathcal R_u=r_u-2,
$$

choose a basis $(r_1,\ldots,r_{d_u})$ of $\mathcal R_u$, and use the label order $(0,1,3,B)$. For a real $4\times d_u$ matrix $A=(a_{y\ell})$, set

$$
\rho_y(A)=\sum_{\ell=1}^{d_u}a_{y\ell}r_\ell,
\qquad
u_y(A)=S_u(f_y)+\rho_y(A).
\tag{199.1}
$$

Define $\mathscr P_u$ to be the set of matrices satisfying

$$
\sum_{y\in\mathcal L}a_{y\ell}=0
\quad(1\le\ell\le d_u),
\tag{199.2}
$$

and for which the four bounded representatives $u_y(A)$ are pointwise nonnegative. The zero-column convention gives the rank-two case $d_u=0$.

**Proposition 199.2 (convex feasibility and exact residual closure).** The set $\mathscr P_u$ is convex. Every $A\in\mathscr P_u$ gives a pointwise legal partition with

$$
\sum_yu_y(A)=1,
\qquad
T_u(u_y(A))=f_y,
\qquad
\Delta(u(A))_{yzk}=0
\quad\text{for all }y,z,k.
\tag{199.3}
$$

Conversely, every pointwise legal label family in $\mathcal W_u$ with quotient labels $T_u(\widetilde u_y)=f_y$ has a unique coefficient matrix $A\in\mathscr P_u$ and is given by (199.1). Its radical corrections span all of $\mathcal R_u$ exactly when

$$
\operatorname{rank}A=d_u.
\tag{199.4}
$$

*Proof.* For each label $y$ and each point in the chosen representatives, the inequality

$$
S_u(f_y)+\sum_{\ell=1}^{d_u}a_{y\ell}r_\ell\ge0
$$

is an affine half-space condition on the entries of $A$. Intersecting these conditions with the affine linear subspace (199.2) proves convexity.

Because $\sum_yf_y=1$ and $S_u(1)=1$, equation (199.2) gives

$$
\sum_yu_y(A)=S_u\left(\sum_yf_y\right)+\sum_y\rho_y(A)=1.
$$

Each $\rho_y(A)$ lies in $\mathcal R_u$, so Proposition 198.2 applies: the pointwise simplex conditions imply that all residuals vanish. The identity for $T_u$ follows from $T_uS_u=\operatorname{id}$ and $T_u(\mathcal R_u)=0$.

Conversely, let $(\widetilde u_y)$ be as stated. Then

$$
\widetilde\rho_y=\widetilde u_y-S_u(f_y)\in\ker T_u=\mathcal R_u,
$$

and the basis of $\mathcal R_u$ gives unique coefficients $a_{y\ell}$. Summing the family and using $S_u(1)=1$ gives (199.2), while pointwise legality gives the defining inequalities of $\mathscr P_u$. The corrections span $\mathcal R_u$ exactly when their coefficient row vectors span $\mathbb R^{d_u}$, which is equivalent to the column-rank condition (199.4). $\square$

**Corollary 199.3 (rank-three and rank-four search interfaces).** In the rank-three branch, $d_u=1$: the radical fibre is described by one zero-sum coefficient column, and a genuine rank-three correction requires that column to be nonzero. In the rank-four branch, $d_u=2$: it is described by two zero-sum columns, and a genuine rank-four correction requires them to be linearly independent. A proposed fixed quotient lift with no feasible matrix of the required column rank cannot realize that rank branch.

The feasible set can be convex even when its full-rank stratum is empty; convex feasibility alone therefore does not produce a radical of the desired dimension. This reduction removes the nonlinear residual equations only after the quotient identity is established and leaves arbitrary partition realization, $F_{64}$, $H43$, SRS\text{-}20, physical succession and Lean/kernel formalization open.

## 200. Full radical rank meets a pointwise boundary

The coefficient body in Section 199 separates residual closure from pointwise legality, but its full-column-rank stratum can still be empty. The relevant distinction is between a uniformly interior lift and a lift that is forced onto the boundary of one or more pointwise simplex inequalities.

**Definition 200.1 (uniformly interior coefficient lift).** Retain Definition 199.1 and write

$$
\mathscr A_u
 =\left\{A\in\mathbb R^{4\times d_u}:
   \sum_{y\in\mathcal L}a_{y\ell}=0
   \text{ for every }\ell\right\}.
\tag{200.1}
$$

For a chosen bounded Borel representative and $x\in G$, put

$$
\lambda_{y,x}(A)
 =S_u(f_y)(x)+\sum_{\ell=1}^{d_u}a_{y\ell}r_\ell(x).
\tag{200.2}
$$

Thus $\mathscr P_u$ is the intersection of $\mathscr A_u$ with the half-spaces $\lambda_{y,x}(A)\ge0$. Define its uniformly interior part by

$$
\mathscr P_u^{\mathrm{ui}}
 =\left\{A\in\mathscr P_u:
   \text{there is an }\varepsilon>0\text{ with }
   \lambda_{y,x}(A)\ge\varepsilon
   \text{ for every }y\in\mathcal L,\ x\in G\right\}.
\tag{200.3}
$$

This is a uniform pointwise condition; positivity merely almost everywhere does not by itself imply (200.3).

**Proposition 200.2 (uniform interior produces the required radical rank).** Suppose $d_u\le2$ and $\mathscr P_u^{\mathrm{ui}}$ is nonempty. Then

$$
\mathscr P_u^{\mathrm{full}}
 :=\{A\in\mathscr P_u:\operatorname{rank}A=d_u\}
\ne\varnothing.
\tag{200.4}
$$

More explicitly, if $A_0\in\mathscr P_u^{\mathrm{ui}}$, then every $D\in\mathscr A_u$ has $A_0+tD\in\mathscr P_u$ for all sufficiently small $|t|$. One may choose $D$ with column rank $d_u$, and then choose such a $t$ for which $A_0+tD$ also has column rank $d_u$.

*Proof.* Let $\varepsilon$ witness (200.3). For $D\in\mathscr A_u$, boundedness of the chosen $r_\ell$ gives a finite constant

$$
C_D=\sup_{y\in\mathcal L,\ x\in G}
\left|\sum_{\ell=1}^{d_u}d_{y\ell}r_\ell(x)\right|.
$$

Whenever $|t|C_D\le\varepsilon$, equation (200.2) gives

$$
\lambda_{y,x}(A_0+tD)
\ge \lambda_{y,x}(A_0)-|t|C_D\ge0,
$$

so $A_0+tD$ remains in $\mathscr P_u$. For $d_u=1$, take any nonzero zero-sum column; only at most one value of $t$ can make that column vanish. For $d_u=2$, take, for example, the two zero-sum columns

$$
(1,-1,0,0)^{\mathsf T},
\qquad
(0,0,1,-1)^{\mathsf T}.
$$

The $2\times2$ minors of $A_0+tD$ are polynomials in $t$, and the coefficient of $t^2$ in at least one of them is a nonzero $2\times2$ minor of $D$. Hence these minors are not all identically zero, so arbitrarily small admissible $t$ can be chosen with rank two. The case $d_u=0$ is vacuous. \(\square\)

**Corollary 200.3 (a necessary boundary condition for rank obstruction).** If $\mathscr P_u^{\mathrm{full}}=\varnothing$, then

$$
\inf_{y\in\mathcal L,\ x\in G}\lambda_{y,x}(A)=0
\qquad\text{for every }A\in\mathscr P_u.
\tag{200.5}
$$

Thus a rank-three or rank-four obstruction cannot be certified by inspecting a single feasible matrix that happens to lie on a boundary. Every feasible matrix must fail the uniform interior condition, either through an attained pointwise zero or through a sequence of positive values tending to zero. The latter asymptotic boundary is distinct from an exact active constraint.

*Proof.* If the infimum in (200.5) were positive for some feasible $A$, that $A$ would belong to $\mathscr P_u^{\mathrm{ui}}$, and Proposition 200.2 would produce a full-column-rank feasible matrix. \(\square\)

**Definition 200.4 (persistent active boundary).** Assume $\mathscr P_u$ is nonempty. Let

$$
\mathcal I_u
 =\left\{(y,x):
   \lambda_{y,x}(A)=0\text{ for every }A\in\mathscr P_u\right\}
\tag{200.6}
$$

be the set of inequalities active throughout the whole coefficient body, and define its direction space by

$$
\mathscr V_u
 =\left\{D\in\mathscr A_u:
   \sum_{\ell=1}^{d_u}d_{y\ell}r_\ell(x)=0
   \text{ for every }(y,x)\in\mathcal I_u\right\}.
\tag{200.7}
$$

The set $\mathcal I_u$ records constraints that are forced by the entire feasible body, rather than zeros that occur only at one selected lift.

**Proposition 200.5 (persistent-boundary rank certificate).** For any $A_0\in\mathscr P_u$,

$$
\mathscr P_u\subseteq A_0+\mathscr V_u.
\tag{200.8}
$$

If every $d_u\times d_u$ minor vanishes on the affine space $A_0+\mathscr V_u$, then

$$
\mathscr P_u^{\mathrm{full}}=\varnothing.
\tag{200.9}
$$

Conversely, a full-column-rank feasible lift requires at least one such minor to be nonzero on $A_0+\mathscr V_u$. In the rank-three case this means that the persistent active equations must not force the unique coefficient column to vanish; in the rank-four case they must not force the two coefficient columns to remain linearly dependent.

*Proof.* Let $A\in\mathscr P_u$. For every $(y,x)\in\mathcal I_u$, both $\lambda_{y,x}(A)$ and $\lambda_{y,x}(A_0)$ are zero. Subtracting (200.2) gives

$$
\sum_{\ell=1}^{d_u}(a_{y\ell}-a_{0,y\ell})r_\ell(x)=0,
$$

so $A-A_0\in\mathscr V_u$, proving (200.8). If all maximal minors vanish on $A_0+\mathscr V_u$, every matrix in $\mathscr P_u$ has column rank strictly below $d_u$, which is (200.9). The converse is the definition of full column rank. \(\square\)

Sections 199 and 200 therefore give a two-stage finite-dimensional interface. First, the affine equations and pointwise inequalities define $\mathscr P_u$ and automatically close all sixty-four residuals. Second, a target rank requires either a uniformly interior coefficient lift or a direct nonvanishing maximal minor that survives every persistent active boundary. Failure of the first route does not prove failure of the second, and an active boundary at one lift does not constrain the whole body. The existence of a rank-three or rank-four arbitrary partition, the evaluation of these boundary conditions for concrete candidates, $F_{64}$, $H43$, SRS\text{-}20, physical succession and Lean/kernel formalization remain open.

## 201. Convex rank-one rigidity in the two radical branches

The boundary criterion of Section 200 becomes exact in the two nontrivial radical dimensions. Convexity leaves no intermediate geometry once every feasible coefficient matrix has deficient column rank.

**Definition 201.1 (the zero-sum coefficient space).** Put

$$
\mathsf H
 =\left\{c\in\mathbb R^4:
   \sum_{y\in\mathcal L}c_y=0\right\}.
\tag{201.1}
$$

For $d_u=1$, a coefficient matrix is a single column in $\mathsf H$. For $d_u=2$, it is a $4\times2$ matrix whose two columns lie in $\mathsf H$.

**Proposition 201.2 (rank-one ruling dichotomy).** Assume that $\mathscr P_u$ is nonempty.

1. If $d_u=1$, then

$$
\mathscr P_u^{\mathrm{full}}\ne\varnothing
\quad\Longleftrightarrow\quad
\mathscr P_u\not\subseteq\{0\}.
\tag{201.2}
$$

2. If $d_u=2$ and $\mathscr P_u^{\mathrm{full}}=\varnothing$, then one of the following two alternatives holds:

$$
\mathscr P_u
 \subseteq
 \{c z^{\mathsf T}:z\in\mathbb R^2\}
 \quad\text{for some }0\ne c\in\mathsf H,
\tag{201.3}
$$

or

$$
\mathscr P_u
 \subseteq
 \{v w^{\mathsf T}:v\in\mathsf H\}
 \quad\text{for some }0\ne w\in\mathbb R^2.
\tag{201.4}
$$

The first alternative fixes a common column direction, while the second fixes a common row direction. Conversely, either inclusion in (201.3) or (201.4) implies $\mathscr P_u^{\mathrm{full}}=\varnothing$.

*Proof.* The first assertion is the definition of column rank for a single column. For the second, let $\mathscr C$ be the positive cone generated by $\mathscr P_u$. Since $\mathscr P_u$ is convex and every one of its matrices has rank at most one, every nonzero element of $\mathscr C$ is a positive scalar multiple of a convex combination of feasible matrices and therefore also has rank at most one.

If $X,Y\in\mathscr C$, every $2\times2$ minor of $X+tY$ vanishes for $t\ge0$, because $X+tY\in\mathscr C$. Each minor is a polynomial in $t$, so it vanishes identically. Splitting arbitrary coefficients into positive and negative parts now shows that every matrix in the linear space

$$
\mathscr L=\operatorname{span}_{\mathbb R}\mathscr P_u
\tag{201.5}
$$

has rank at most one.

If $\mathscr P_u=\{0\}$, both alternatives are vacuous and the conclusion is immediate. Otherwise choose a nonzero $A_0\in\mathscr L$ and write $A_0=uv^{\mathsf T}$. For any $B\in\mathscr L$, the pencil $A_0+tB$ has rank at most one for every real $t$. The $2\times2$ minors of this pencil then imply that either every column of $B$ is proportional to $u$, or every row of $B$ is proportional to $v$. If the first alternative holds for every $B$, (201.3) follows. Otherwise choose $B$ of the second type whose columns are not all proportional to $u$. For an arbitrary $C\in\mathscr L$, a first-type $C$ whose rows were not proportional to $v$ would make $B+C$ have rank two, contradicting the rank-one property of $\mathscr L$. Hence every $C$ is of the second type, which gives (201.4). The converse is immediate because every matrix in either displayed family has rank at most one. \(\square\)

**Corollary 201.3 (a direct rank-four feasibility test).** In the rank-three branch, one nonzero feasible coefficient column is sufficient to realize the full radical dimension. In the rank-four branch, a full-rank lift exists if and only if the feasible body escapes both fixed-factor rulings (201.3) and (201.4). In particular, it is enough to find $A,B\in\mathscr P_u$ such that one $2\times2$ minor of

$$
\frac{A+B}{2}
\tag{201.6}
$$

is nonzero; convexity then makes the midpoint itself a rank-four feasible lift. Conversely, if every feasible midpoint has all $2\times2$ minors zero, Proposition 201.2 places the entire body in one of the two rank-one rulings.

This dichotomy sharpens the boundary interface without solving the pointwise inequalities: rank-three exclusion requires the one-column body to collapse to zero, while rank-four exclusion requires a fixed-factor identity across the whole convex body. It does not evaluate those identities for an arbitrary partition or settle $F_{64}$, $H43$, SRS\text{-}20, physical succession or Lean/kernel formalization.

## 202. A transverse pair is a rank-four witness

The ruling dichotomy of Section 201 can be tested pairwise. Two rank-one coefficient lifts generate a rank-two lift exactly when both their label directions and their radical-coordinate directions are independent.

**Definition 202.1 (transverse rank-one pair).** Let $A$ and $B$ be nonzero rank-one $4\times2$ matrices in $\mathscr A_u$. Choose factorizations

$$
A=u v^{\mathsf T},
\qquad
B=s t^{\mathsf T},
\qquad
u,s\in\mathsf H,\quad v,t\in\mathbb R^2.
\tag{202.1}
$$

Call $(A,B)$ transverse when

$$
 u\wedge s\ne0
\quad\text{and}\quad
 v\wedge t\ne0.
\tag{202.2}
$$

The condition is independent of the nonzero rescalings in the two rank-one factorizations.

**Proposition 202.2 (wedge formula for convex combinations).** For every $0<\theta<1$, every two-row set $I=\{i,k\}\subseteq\mathcal L$ and the two column indices $J=\{j,\ell\}\subseteq\{1,2\}$, one has

$$
\det\!\left(\bigl(\theta A+(1-\theta)B\bigr)_{I,J}\right)
 =\theta(1-\theta)
   (u_i s_k-u_k s_i)
   (v_j t_\ell-v_\ell t_j).
\tag{202.3}
$$

Consequently,

$$
\operatorname{rank}\bigl(\theta A+(1-\theta)B\bigr)=2
\quad\Longleftrightarrow\quad
(A,B)\text{ is transverse}.
\tag{202.4}
$$

*Proof.* Expand the determinant of the $2\times2$ submatrix in (202.3). The terms quadratic in $A$ and in $B$ vanish because both matrices have rank one. The two cross terms factor as

$$
\theta(1-\theta)
 (u_i s_k-u_k s_i)(v_j t_\ell-v_\ell t_j),
$$

which proves (202.3). All maximal minors of the convex combination vanish exactly when one of the two exterior products in (202.2) vanishes, proving (202.4). \(\square\)

**Corollary 202.3 (pairwise search interface for rank four).** Assume $d_u=2$ and let $A,B\in\mathscr P_u$ be nonzero rank-one matrices. If $(A,B)$ is transverse, then every strict convex combination in (202.3) belongs to $\mathscr P_u$ and has column rank two. Hence a single transverse pair is a rank-four feasible witness.

Assume every matrix in $\mathscr P_u$ has rank at most one. Then $\mathscr P_u$ contains a rank-two lift obtained from a strict convex combination exactly when it contains a transverse pair. If it contains no transverse pair, Proposition 201.2 puts the whole body in one of the two fixed-factor rulings. Thus the rank-four search can be organized as a pairwise test: either find two feasible rank-one lifts with both wedge factors nonzero, or certify a common ruling by showing that one wedge factor vanishes for every pair.

*Proof.* Convexity gives the first assertion, and Proposition 202.2 gives its rank. The converse is Proposition 201.2 together with the definition of a transverse pair. \(\square\)

The wedge formula makes the rank-four boundary computationally concrete while keeping the pointwise constraints unchanged: the only new data are one feasible pair and two nonvanishing $2\times2$ minors. It does not construct such a pair for an arbitrary partition, evaluate the ruling identities in a concrete candidate, or settle $F_{64}$, $H43$, SRS\text{-}20, physical succession or Lean/kernel formalization.

## 203. Rank-one rulings scalarize the pointwise fibre

The two fixed-factor alternatives of Section 201 have an exact pointwise description. They replace a $4\times2$ coefficient matrix by either one label profile or one radical profile, while retaining all simplex inequalities.

**Definition 203.1 (the two scalarized ruling bodies).** Assume $d_u=2$, write

$$
 s_y=S_u(f_y),
 \qquad
 E_u=\operatorname{span}_{\mathbb R}\{r_1,r_2\},
\tag{203.1}
$$

and retain the zero-sum space $\mathsf H$ from Definition 201.1. For a nonzero $c\in\mathsf H$ and $z=(z_1,z_2)\in\mathbb R^2$, put

$$
 h_z=z_1r_1+z_2r_2,
 \qquad
 \widetilde u_y^{\,c,z}=s_y+c_yh_z.
\tag{203.2}
$$

Define

$$
 \mathscr Z_c
 =\left\{z\in\mathbb R^2:
   \widetilde u_y^{\,c,z}(x)\ge0
   \text{ for every }y\in\mathcal L,\ x\in G\right\}.
\tag{203.3}
$$

For a nonzero $w=(w_1,w_2)\in\mathbb R^2$, put

$$
 h_w=w_1r_1+w_2r_2,
 \qquad
 \widetilde u_y^{\,v,w}=s_y+v_yh_w
\tag{203.4}
$$

for $v\in\mathsf H$, and define

$$
 \mathscr V_w
 =\left\{v\in\mathsf H:
   \widetilde u_y^{\,v,w}(x)\ge0
   \text{ for every }y\in\mathcal L,\ x\in G\right\}.
\tag{203.5}
$$

**Proposition 203.2 (exact scalarization of the two rulings).** With the notation above,

$$
 \mathscr P_u\cap
 \{c z^{\mathsf T}:z\in\mathbb R^2\}
 =\{c z^{\mathsf T}:z\in\mathscr Z_c\},
\tag{203.6}
$$

and

$$
 \mathscr P_u\cap
 \{v w^{\mathsf T}:v\in\mathsf H\}
 =\{v w^{\mathsf T}:v\in\mathscr V_w\}.
\tag{203.7}
$$

Both parameter sets are convex. For every parameter in either set, the corresponding family in (203.2) or (203.4) satisfies

$$
 \sum_{y\in\mathcal L}\widetilde u_y=1,
 \qquad
 T_u(\widetilde u_y)=f_y,
 \qquad
 \Delta(\widetilde u)_{yzk}=0
 \quad(y,z,k\in\mathcal L).
\tag{203.8}
$$

*Proof.* If $A=c z^{\mathsf T}$, then its $y$-th row is $(c_yz_1,c_yz_2)$, so (199.1) is exactly (203.2). The column-sum equations in (199.2) hold because $c\in\mathsf H$, and the remaining condition $A\in\mathscr P_u$ is precisely the pointwise inequality in (203.3). This proves (203.6), including uniqueness of $z$ because $c\ne0$. The proof of (203.7) is identical: the rows of $A=v w^{\mathsf T}$ give (203.4), and $v\in\mathsf H$ supplies the column-sum equations.

The inequalities in (203.3) and (203.5) are affine in their parameters, so the two parameter sets are convex. Finally, the zero-sum condition gives the first identity in (203.8), the section identity and $T_u(r_\ell)=0$ give the second, and Proposition 199.2 gives the residual identity. \(\square\)

**Corollary 203.3 (a ruling cannot realize candidate rank four).** Every family arising from either scalarized ruling satisfies

$$
 \operatorname{span}_{\mathbb R}\{\widetilde u_y:y\in\mathcal L\}
 \subseteq S_u(E_f)+\mathbb R h
\tag{203.9}
$$

for one radical function $h\in E_u$. Consequently its label span has dimension at most three. If $h=0$, the dimension is at most two. Thus a rank-four candidate family must escape both fixed-factor rulings, even though every point in those rulings already has all sixty-four residuals equal to zero.

*Proof.* In the first ruling take $h=h_z$ and in the second take $h=h_w$. Equation (203.2) or (203.4) writes every label as an element of $S_u(E_f)+\mathbb Rh$. The section $S_u$ is injective on $E_f$ because $T_uS_u=\operatorname{id}_{E_f}$, so $\dim S_u(E_f)=2$. The dimension bound follows. \(\square\)

The scalarization is an exact search interface for a fixed ruling: the column ruling leaves two radical coefficients and a fixed label profile, while the row ruling leaves a three-dimensional zero-sum label profile and a fixed radical direction. It removes the residual equations only after the quotient identity and pointwise inequalities are imposed; it does not show that either ruling is nonempty or settle arbitrary partition realization, $F_{64}$, $H43$, SRS\text{-}20, physical succession or Lean/kernel formalization.

## 204. Pointwise envelopes decide ruling feasibility

The scalarized bodies of Section 203 can be tested without carrying all label inequalities separately. For a fixed ruling factor, the pointwise simplex constraints become upper and lower envelopes for one scalar function or one scalar label coordinate.

**Definition 204.1 (the fixed-column envelope).** Retain $s_y=S_u(f_y)$ and let $0\ne c\in\mathsf H$. Since $c$ is nonzero and has zero sum, both sign sets

$$
\mathcal L_c^+=\{y:c_y>0\},
\qquad
\mathcal L_c^- =\{y:c_y<0\}
\tag{204.1}
$$

are nonempty. Define the pointwise envelopes

$$
 L_c(x)=\max_{y\in\mathcal L_c^+}\frac{-s_y(x)}{c_y},
\qquad
 U_c(x)=\min_{y\in\mathcal L_c^-}\frac{-s_y(x)}{c_y}.
\tag{204.2}
$$

Put

$$
\mathscr Z_c^{\mathrm{env}}
 =\left\{z\in\mathbb R^2:
 \begin{array}{l}
 s_y(x)\ge0\text{ for every }y\text{ with }c_y=0\text{ and every }x,\\[2pt]
 L_c(x)\le h_z(x)\le U_c(x)\text{ for every }x
 \end{array}\right\}.
\tag{204.3}
$$

**Definition 204.2 (the fixed-row interval body).** Let $0\ne w\in\mathbb R^2$ and write $h=h_w$. For each label $y$, define extended-real bounds

$$
 \ell_y(h)=\sup_{x:h(x)>0}\frac{-s_y(x)}{h(x)},
 \qquad
 u_y(h)=\inf_{x:h(x)<0}\frac{-s_y(x)}{h(x)},
\tag{204.4}
$$

with the conventions $\sup\varnothing=-\infty$ and $\inf\varnothing=+\infty$. Define

$$
\mathscr V_w^{\mathrm{env}}
 =\left\{v\in\mathsf H:
 \begin{array}{l}
 s_y(x)\ge0\text{ whenever }h(x)=0,\\[2pt]
 \ell_y(h)\le v_y\le u_y(h)\text{ for every }y\in\mathcal L
 \end{array}\right\}.
\tag{204.5}
$$

All pointwise quantifiers range over the fixed representative domain $G$. The bounds in (204.4) lie in $[-\infty,+\infty]$, whereas every $v_y$ is real. Thus $\ell_y(h)=+\infty$ or $u_y(h)=-\infty$ excludes every real value of that coordinate, even if the two extended bounds are equal. No quotient is taken where its denominator is zero, and no subtraction of infinite bounds is used.

**Proposition 204.3 (exact envelope characterizations).** The parameter bodies of Section 203 satisfy

$$
\mathscr Z_c=\mathscr Z_c^{\mathrm{env}},
\tag{204.6}
$$

and

$$
\mathscr V_w=\mathscr V_w^{\mathrm{env}}.
\tag{204.7}
$$

Consequently, a fixed-column ruling is feasible exactly when its two-dimensional coefficient vector $z$ satisfies the envelope inequalities (204.3), and a fixed-row ruling is feasible exactly when the interval box (204.5) intersects the zero-sum hyperplane $\mathsf H$.

*Proof.* For the fixed-column ruling, the inequality in (203.2) is

$$
 s_y(x)+c_yh_z(x)\ge0.
$$

If $c_y>0$, division by $c_y$ gives $h_z(x)\ge-s_y(x)/c_y$; if $c_y<0$, it gives $h_z(x)\le-s_y(x)/c_y$; and if $c_y=0$, it gives $s_y(x)\ge0$. Taking the maximum over the positive labels and the minimum over the negative labels gives exactly (204.3). For the fixed-row ruling, the same inequality is

$$
 s_y(x)+v_yh(x)\ge0.
$$

On the set where $h>0$ it gives $v_y\ge-s_y/h$, on the set where $h<0$ it gives $v_y\le-s_y/h$, and on the zero set it gives $s_y\ge0$. Taking the supremum and infimum over the corresponding point sets gives (204.4)--(204.5), with the stated empty-set conventions. \(\square\)

**Corollary 204.4 (the remaining ruling search is an envelope problem).** After the quotient identity is fixed, the fixed-column branch requires only the intersection of the two-dimensional plane $\{h_z:z\in\mathbb R^2\}$ with the pointwise strip

$$
L_c\le h\le U_c,
\tag{204.8}
$$

along with the zero-profile conditions. The fixed-row branch requires only an interval-box intersection with $\mathsf H$. Every point found by either test yields a legal full-zero family by Proposition 203.2, while failure of the corresponding envelope intersection rules out that entire ruling factor. These are characterizations of fixed coefficient rulings; the label-span rank of their families is determined by Proposition 205.2. Neither characterization supplies an original full-zero seed in a prescribed rank branch.

## 追加锚（本行以下为增补区）

## 205. Baseline relations determine the actual lifted label rank

**Definition 205.1 (the relation-restricted coefficient matrix).** Fix one original full-zero partition $u$, its host space $\mathcal W_u$, quotient $T_u$, normalized section $S_u$ and radical basis as in Sections 197--199. All spans below are spans of real $m$-classes. Use one coherent linear choice of bounded Borel representatives on $\mathcal W_u$, with $1$ represented by the constant one and the seed represented by a pointwise legal partition; a common $m$-null-set adjustment is allowed in choosing these representatives. Keep this choice fixed for all pointwise inequalities. Write $d=d_u$ and let

$$
j:\mathbb R^d\longrightarrow\mathcal R_u,
\qquad j(z)=\sum_{\ell=1}^d z_\ell r_\ell.
$$

In label order $(0,1,3,B)$, put

$$
b_1=(1,-1,0,0)^{\mathsf T},\qquad
b_2=(1,1,1,-3)^{\mathsf T},\qquad
\mathsf B=(b_1\ b_2),\qquad K=\ker\Phi_f.
\tag{205.1}
$$

The baseline identities (191.6), together with $\dim K=2$, give $K=\operatorname{im}\mathsf B$. For $A\in\mathscr A_u$, define

$$
M(A)=\mathsf B^{\mathsf T}A
=\begin{pmatrix}
a_{0\bullet}-a_{1\bullet}\\
a_{0\bullet}+a_{1\bullet}+a_{3\bullet}-3a_{B\bullet}
\end{pmatrix},
\qquad
W(A)=\operatorname{span}_{\mathbb R}\{u_y(A):y\in\mathcal L\}.
\tag{205.2}
$$

Here $M(A)$ is $2\times d$, including the zero-column matrix when $d=0$.

**Proposition 205.2 (exact FIB label-rank criterion).** For every feasible $A\in\mathscr P_u$,

$$
\begin{aligned}
W(A)\cap\mathcal R_u&=j\bigl(\operatorname{im}M(A)^{\mathsf T}\bigr),\\
\ker(a\mapsto\textstyle\sum_y a_yu_y(A))&=K\cap\ker A^{\mathsf T},\\
\dim W(A)&=2+\operatorname{rank}M(A).
\end{aligned}
\tag{205.3}
$$

The first space in (205.3) is also the common radical of the tensor restricted to $W(A)$. In particular,

$$
W(A)=\mathcal W_u
\quad\Longleftrightarrow\quad
\operatorname{rank}M(A)=d.
\tag{205.4}
$$

Thus $\operatorname{rank}A=d$ in (199.4) is necessary for (205.4), but measures the span of the corrections, rather than the actual excess label rank. If $d=0$, both ranks are zero and every feasible family has label rank two.

*Proof.* Such coherent representatives exist: choose bounded representatives of a host basis containing $1$. Outside a common null set the seed's finitely many linear identities hold. On that null set assign every basis function its value at one fixed point outside it. Extending linearly then preserves $1$ and represents the seed by a legal partition everywhere. For these fixed representatives the lifted label map is

$$
\Phi_A(a)=S_u(\Phi_f(a))+j(A^{\mathsf T}a),
\qquad T_u\Phi_A=\Phi_f.
\tag{205.5}
$$

Consequently $T_u:W(A)\to E_f$ is onto, and a label combination belongs to its kernel exactly when its coefficient vector is in $K$. Writing that vector as $\mathsf Bz$ gives

$$
\ker(T_u|_{W(A)})=\Phi_A(K)
=j\bigl(\operatorname{im}(A^{\mathsf T}\mathsf B)\bigr).
$$

Injectivity of $j$ also gives the second identity in (205.3). Since $\ker T_u=\mathcal R_u$ and $\dim E_f=2$, rank--nullity gives the last identity. The standard principle used here is Axler, *Linear Algebra Done Right*, fourth edition, [Theorem 3.21](https://LADR.plus/x3nullspace.html#x3nullspace-4); its application is to the lifted FIB label map and its baseline relation restriction. The family is full-zero by Proposition 199.2, so Proposition 190.1 identifies $\Phi_A(K)$ with its common radical. Finally $W(A)\subseteq\mathcal W_u$ and $\dim\mathcal W_u=2+d$, proving (205.4). The inequality $\operatorname{rank}M(A)\le\operatorname{rank}A$ proves necessity. $\square$

**Proposition 205.3 (section and basis invariance for the same family).** Let $S'_u=S_u+jL$ be another normalized section, where $L:E_f\to\mathbb R^d$ is linear and $L(1)=0$. Let $D_L$ be the matrix whose $y$-th row is $L(f_y)^{\mathsf T}$. The same lifted functions have coefficient matrix

$$
A'=A-D_L,\qquad \mathsf B^{\mathsf T}D_L=0,
\qquad M(A')=M(A).
\tag{205.6}
$$

If the relation basis becomes $\mathsf BQ$ with $Q\in\operatorname{GL}_2(\mathbb R)$, and the radical coordinate map becomes $j'=jC$ with $C\in\operatorname{GL}_d(\mathbb R)$, then the matrix for this same restriction becomes

$$
Q^{\mathsf T}M(A)C^{-\mathsf T}.
\tag{205.7}
$$

Hence the actual rank criterion is independent of all three choices. Pointwise feasibility is also preserved when the new representatives are chosen to give the same lifted functions.

*Proof.* Substituting $S'_u$ into (205.5) gives $A'=A-D_L$. For each $b\in K$,

$$
D_L^{\mathsf T}b=L\left(\sum_y b_yf_y\right)=0,
$$

which proves (205.6). A change $j'=jC$ changes the coefficient matrix to $A'C^{-\mathsf T}$; a relation basis change multiplies its restriction on the left by $Q^{\mathsf T}$. These factors are invertible, giving (205.7), including the empty-coordinate convention for $d=0$. The equalities of functions give the assertion about pointwise inequalities. This compares representations of the same lifted family, with its section and coefficients changed together. $\square$

**Proposition 205.4 (algebraic failures of the unrestricted rank inference).** The zero-sum column and two-column matrix

$$
\kappa=(-1,-1,2,0)^{\mathsf T},\qquad
A_2=\begin{pmatrix}1&0\\1&0\\0&1\\-2&-1\end{pmatrix}
\tag{205.8}
$$

satisfy

$$
\operatorname{rank}\kappa=1,\quad M(\kappa)=0,
\qquad
\operatorname{rank}A_2=2,\quad
M(A_2)=\begin{pmatrix}0&0\\8&4\end{pmatrix}.
\tag{205.9}
$$

Thus a feasible occurrence of the first matrix would have actual label rank two, and a feasible occurrence of the second would have actual label rank three. Unrestricted coefficient transversality likewise does not suffice for actual rank four. These examples assert algebraic ranks only; membership in an original FIB feasibility body is an additional hypothesis.

*Proof.* Each displayed column sums to zero, and direct multiplication by $\mathsf B^{\mathsf T}$ gives (205.9). The vector $\kappa$ is nonzero, and the rows $(1,0)$ and $(0,1)$ of $A_2$ prove its rank two. Write its columns as $c=(1,1,0,-2)^{\mathsf T}$ and $e=(0,0,1,-1)^{\mathsf T}$. The rank-one endpoints $c(2,0)$ and $e(0,2)$ are transverse in Definition 202.1 and have midpoint $A_2$, but their restricted column factors $(0,8)^{\mathsf T}$ and $(0,4)^{\mathsf T}$ are dependent. Finally, for $d=1$, a section change with $L(q)=2$ and $L(1)=0$ gives $D_L=\kappa$ because $f_0=f_1=3/8-q/2$, $f_3=q$ and $f_B=1/4$. It changes the coefficient representation $\kappa$ into zero for the same family. This also shows why coefficient correction rank itself is not a section invariant. $\square$

## 206. The projected feasibility body and its boundary consequences

**Proposition 206.1 (exact projected-body interpretation and the seed point).** Put

$$
\mathscr Q_u=M(\mathscr P_u)\subseteq\mathbb R^{2\times d},
\qquad
N=\mathsf B(\mathsf B^{\mathsf T}\mathsf B)^{-1}
=\left(\frac{b_1}{2}\ \frac{b_2}{12}\right).
\tag{206.1}
$$

Every zero-sum coefficient matrix has a unique decomposition

$$
A=NM(A)+\kappa z^{\mathsf T},\qquad z\in\mathbb R^d.
\tag{206.2}
$$

Consequently $M_0\in\mathscr Q_u$ exactly when some $z\in\mathbb R^d$ makes $NM_0+\kappa z^{\mathsf T}$ satisfy all the pointwise inequalities of Definition 199.1. The body $\mathscr Q_u$ is convex, and it records actual label ranks by

$$
\mathscr P_u^{\mathrm{act}}
:=\{A\in\mathscr P_u:W(A)=\mathcal W_u\}
=\{A\in\mathscr P_u:\operatorname{rank}M(A)=d\}.
\tag{206.3}
$$

For the fixed full-zero seed $u$ assumed in Definition 205.1, this set is nonempty: the coefficient matrix $A_*$ representing $u$ itself belongs to it. This is a conditional statement about the seed's own body, without an existence assertion for an original seed of rank three or four.

*Proof.* Both $b_1,b_2$ have zero sum, are orthogonal, and have squared norms $2,12$. Thus $\mathsf B^{\mathsf T}N=I_2$, so the map $M:\mathscr A_u\to\mathbb R^{2\times d}$ is onto. Its kernel consists of columns in $\mathsf H\cap K^\perp=\mathbb R\kappa$: this intersection has dimension one and contains the nonzero vector $\kappa$. Subtracting $NM(A)$ proves (206.2) and uniqueness. Substitution into the defining inequalities proves the membership characterization. Linear images preserve convexity, and Proposition 205.2 proves (206.3). Proposition 199.2 supplies $A_*$, and $W(A_*)=\mathcal W_u$ by definition of the seed, so $\operatorname{rank}M(A_*)=d$. Projection retains the relation-image data needed for rank; distinct matrices in a fibre of $M$ can still give distinct lifted families. $\square$

**Proposition 206.2 (corrected interior and persistent-boundary criteria).** A uniformly interior point of $\mathscr P_u$ has feasible matrices of actual label rank $2+d$ arbitrarily close to it. Consequently, if $\mathscr P_u^{\mathrm{act}}=\varnothing$, then

$$
\inf_{y,x}\lambda_{y,x}(A)=0\qquad(A\in\mathscr P_u).
\tag{206.4}
$$

For $A_0\in\mathscr P_u$, retain the persistent direction space $\mathscr V_u$ of (200.7). Then

$$
\mathscr Q_u\subseteq M(A_0)+M(\mathscr V_u).
\tag{206.5}
$$

If all $d\times d$ minors vanish throughout the affine space on the right, there is no feasible family of actual rank $2+d$. A nonzero such minor somewhere on that affine space is necessary for such a family, but does not by itself establish pointwise feasibility. For $d=0$, the empty minor equals one and every feasible family already has the required rank.

*Proof.* The perturbation bound in Proposition 200.2 applies to every zero-sum direction. For $d=1$, take $D=N(1,0)^{\mathsf T}$; the first entry of $M(A_0+tD)$ has nonzero linear coefficient. For $d=2$, take $D=N$; then $M(A_0+tD)=M(A_0)+tI_2$, whose determinant is a monic quadratic in $t$. Avoiding the finitely many roots gives arbitrarily small feasible perturbations of full restricted rank, and (205.3) gives their actual label rank. The case $d=0$ needs no perturbation. This proves (206.4) by contraposition, since a positive infimum is uniform interior. Applying $M$ to (200.8) gives (206.5); maximal minors and (206.3) give the remaining assertions. For an actual host fixed by a spanning seed, Proposition 206.1 makes the emptiness premise impossible. Thus these obstruction criteria constrain proposed host or boundary data; they do not construct a missing seed. $\square$

## 207. Corrected rank consumers and the scope of ruling searches

**Proposition 207.1 (the ruling test belongs to the projected body).** For $d=1$, a feasible family of actual rank three exists exactly when $\mathscr Q_u\not\subseteq\{0\}$. For $d=2$, absence of a feasible family of actual rank four is equivalent to at least one of

$$
\mathscr Q_u\subseteq\{\alpha v^{\mathsf T}:v\in\mathbb R^2\}
\quad\text{for some }0\ne\alpha\in\mathbb R^2,
\tag{207.1}
$$

or

$$
\mathscr Q_u\subseteq\{v\beta^{\mathsf T}:v\in\mathbb R^2\}
\quad\text{for some }0\ne\beta\in\mathbb R^2.
\tag{207.2}
$$

In particular, actual rank four requires escape from both kinds of projected ruling, rather than only from the coefficient rulings (201.3)--(201.4).

*Proof.* Proposition 205.2 proves the one-column assertion. In the two-column case the failure condition is $\det M=0$ for all $M\in\mathscr Q_u$. A nonempty convex set has a nonempty relative interior in its affine hull, so this polynomial then vanishes on the entire affine hull. Apply the classification of real affine spaces of rank at most one in de Seguins Pazzis, *Large spaces of bounded rank matrices revisited*, [Proposition 2.3](https://arxiv.org/html/1507.05375v2): all nonzero matrices have a common image or a common kernel. Over $\mathbb R$ its exceptional two-element-field alternative is excluded. In $2\times2$ dimensions these are precisely (207.1) and (207.2); for the zero space either containment holds. Conversely either containment forces rank at most one. $\square$

**Proposition 207.2 (valid transverse-pair scope).** Suppose $d=2$ and $A,D\in\mathscr P_u$ have nonzero rank-one restrictions

$$
M(A)=\alpha v^{\mathsf T},\qquad M(D)=\gamma t^{\mathsf T}.
$$

For $0<\theta<1$, their feasible mixture has actual label rank four exactly when

$$
\det(\alpha\ \gamma)\det(v\ t)\ne0,
\tag{207.3}
$$

because

$$
\det M\bigl(\theta A+(1-\theta)D\bigr)
=\theta(1-\theta)\det(\alpha\ \gamma)\det(v\ t).
\tag{207.4}
$$

For rank-one coefficient endpoints $A=c v^{\mathsf T}$ and $D=e t^{\mathsf T}$, the column factors to use are $\alpha=\mathsf B^{\mathsf T}c$ and $\gamma=\mathsf B^{\mathsf T}e$. If either is zero, the mixture cannot have actual rank four. Independence of $c,e$ alone does not suffice.

*Proof.* Apply the determinant expansion of Proposition 202.2 to the two restricted $2\times2$ matrices. Convexity gives feasibility, and Proposition 205.2 converts determinant nonvanishing into actual label rank four. The endpoint formula follows by multiplying the coefficient factorizations by $\mathsf B^{\mathsf T}$. In particular, the premise that every matrix of the whole feasible body has coefficient rank at most one forbids a rank-two coefficient mixture; the premise that every projected matrix has rank at most one forbids (207.3). Neither global premise supplies a route to a rank-four family.

Convexity alone also gives no converse requiring rank-one endpoints: the abstract convex matrix body $\{I_2\}$ has full-rank points and no rank-one points. This is not asserted to be a realizable FIB body. It shows that a rank-one endpoint search requires an additional property of the particular body to be exhaustive. $\square$

**Proposition 207.3 (retained statements and replaced candidate-rank conclusions).** Under the fixed-host hypotheses of Definition 205.1, the quotient and fibre descriptions in Sections 197--198, the feasibility and residual closure in Proposition 199.2, and its correction-span equality (199.4) are retained. The coefficient-rank requirements in Corollary 199.3 remain necessary; the exact actual-rank requirement is (205.4). The literal coefficient-rank strata and certificates of Section 200 and Proposition 201.2 retain their coefficient meaning; their candidate-rank interpretations use Propositions 206.2 and 207.1. The candidate-rank sufficiency claims of Corollaries 201.3 and 202.3 are replaced respectively by Propositions 207.1 and 207.2. Proposition 202.2 remains a coefficient-minor identity.

The scalarized feasibility equalities (203.6)--(203.8), the dimension bound of Corollary 203.3, and the envelope equivalences (204.6)--(204.7) are retained. More precisely, in the fixed-column ruling the actual rank is

$$
2+\operatorname{rank}\bigl((\mathsf B^{\mathsf T}c)z^{\mathsf T}\bigr),
\tag{207.5}
$$

and in the fixed-row ruling it is $2+\operatorname{rank}((\mathsf B^{\mathsf T}v)w^{\mathsf T})$. Each is at most three. A projected ruling in (207.1) or (207.2) means its entire inverse image in $\mathscr P_u$; it need not be one of the fixed coefficient rulings tested by Sections 203--204.

*Proof.* Feasibility and tensor closure do not require the lifted labels to span their host, so Proposition 199.2 retains precisely those conclusions. Proposition 205.2 separates its correction-span assertion from the actual rank. Propositions 206.2, 207.1 and 207.2 give the stated replacements, including the impossibility of the global rank-at-most-one route in Corollary 202.3. Substituting $A=c z^{\mathsf T}$ or $A=v w^{\mathsf T}$ into (205.3) proves the ruling ranks, while Sections 203--204 solve exactly their original pointwise inequalities. Finally (206.2) exhibits the additional kernel freedom in a projected ruling's inverse image; (205.9) shows algebraically that this freedom can coexist with coefficient rank two.

All these conclusions presuppose the original full-zero seed and its fixed host. They neither establish pointwise legality of the algebraic examples (205.8) nor construct an original rank-three or rank-four seed. Arbitrary-partition realization, the concrete pointwise evaluation of the host bodies, $F_{64}$, $H43$, SRS$\text{-}20$ and physical succession retain their separate unresolved boundaries. $\square$

## 追加锚（本行以下为增补区）


## 208. Cellwise source-reversal variance budgets for hard partitions

**Definition 208.1 (the original pair-calibrated hard fiber and its middle-cell laws).** Retain the entire original telescope of Definition 175.1 and [Appendix III Definition 155.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md#155-positive-bb3-inputs-finite-coupled-improvement-and-source-ratio-selection). In particular, $\theta=(a,\eta,d,b)$ ranges over every original finite $a,\eta,d>0$ and every permitted representative $b$. The group $G=H^1\times\mathbb R$, its product and raw Haar measure $\mu$, source $e$, unit-source field $L\Gamma=\delta_e$, coefficient-one $w_*$, coefficient-positive normalized $h$, actual selector $A_{\rm src}=\rho C_{\rm src}$, full source-inclusive conservative self-adjoint $K$, measure $m=h^2\mu$, clock and epochs $2d,3d,4d$ remain unchanged. Keep $P=T_d$, $g=g_{2d}$, $q=f_3=cb$, $f_B=p=1/4$ and $f_0=f_1=(3/4-q)/2$. Let $D=(D_i)_{i\in\mathcal L}$ be one whole-$G$ deterministic Borel partition, with $u_i=\mathbf1_{D_i}$, satisfying

$$
\begin{gathered}
\int_G(P^\ell g)u_i\,dm=\int_G(P^\ell g)f_i\,dm
\quad(\ell=0,1,2;\ i\in\mathcal L),\\
Q_r(u_i,u_k)=Q_r(f_i,f_k)
\quad(r=12,13,23;\ i,k\in\mathcal L).
\end{gathered}
\tag{208.1}
$$

Here $Q_r$ are precisely the ordered pair forms of Appendix III (150.2). Thus (208.1) holds for every $D\in\mathscr F_{154}(\theta)$; no full-zero hypothesis is imposed. Write

$$
\begin{gathered}
v=Pg=g_{3d},\qquad G_0=\|g\|_\infty<\infty,\\
\pi_j=\int_{D_j}v\,dm=\int_Gvf_j\,dm>0,
\qquad d\nu_j=\frac{u_jv}{\pi_j}\,dm
\quad(j\in\mathcal L).
\end{gathered}
\tag{208.2}
$$

Positivity of $v$ and of each $f_j$ almost everywhere gives the strict inequality. The measure $\nu_j$ is the actual middle-time law conditioned on $Z_{3d}\in D_j$. All ratios and conditional expectations below are defined almost everywhere under the unchanged middle-time law $v\,m$; since $v>0$ almost everywhere, this has the same null sets as $m$. Put

$$
\begin{gathered}
t=Pu_B,\qquad s=\frac{P(gu_B)}{v},\qquad
\chi=\frac{P(g^2)}{v^2}-1,\\
A_j=\mathbb E_{\nu_j}(t-p)^2,\qquad
B_j=\mathbb E_{\nu_j}(s-p)^2,\qquad
H_j=\mathbb E_{\nu_j}\bigl[\chi t(1-t)\bigr].
\end{gathered}
\tag{208.3}
$$

The functions $s$ and $t$ are, respectively, the conditional probabilities of the first and last $B$ labels given the original middle state. In particular, $t$ is this same partition's own propagated terminal indicator. For the conditional refinement only, write $k_j=\operatorname*{ess\,sup}_{D_j}\chi$ with respect to $v\,m$ and assume $k_j<\infty$.

**Proposition 208.2 (a finite native-source budget for each $BjB$ residual).** Under Definition 208.1, all terms in (208.3) are finite, and

$$
0\le\chi,\qquad
0\le v\chi\le G_0-v
\quad\text{almost everywhere}.
\tag{208.4}
$$

For every $j\in\mathcal L$ the exact residual identity and lower bound are

$$
\frac{\Delta(D)_{BjB}}{\pi_j}
=\mathbb E_{\nu_j}\bigl[(s-p)(t-p)\bigr],
\qquad
\Delta(D)_{BjB}\ge\frac{\pi_j}{2}(A_j+B_j-H_j).
\tag{208.5}
$$

If $k_j<\infty$, then also

$$
\Delta(D)_{BjB}\ge
\frac{\pi_j}{2}\left[(1+k_j)A_j+B_j-\frac3{16}k_j\right].
\tag{208.6}
$$

*Proof.* Let $\mathsf P(x,dy)$ be the actual gap-$d$ Markov kernel of $P$. Conservation gives $\mathsf P(x,G)=1$. Self-adjointness makes $m(dx)\mathsf P(x,dy)$ symmetric, so the original conditional law of $Z_{2d}$ given $Z_{3d}=x$ is

$$
\frac{g(y)}{v(x)}\mathsf P(x,dy).
\tag{208.7}
$$

Its total mass is one. This is the reversal of the original source-start law, while the conditional law of $Z_{4d}$ given $Z_{3d}=x$ is $\mathsf P(x,dy)$. Both statements use the original $g$ and $P$.

Cauchy–Schwarz for $\mathsf P(x,dy)$ gives $v^2=(Pg)^2\le P(g^2)$, and $g^2\le G_0g$ gives $P(g^2)\le G_0v$. These prove (208.4). Also $0\le s,t\le1$, and

$$
\pi_j\mathbb E_{\nu_j}\chi
=\int_{D_j}v\chi\,dm
\le G_0m(D_j)-\pi_j<\infty.
\tag{208.8}
$$

Consequently $A_j,B_j$ are finite, and $0\le H_j\le\mathbb E_{\nu_j}\chi/4<\infty$. No lower bound on $v$ over $G$ is used.

The pair calibrations give the two exact conditional means

$$
\begin{aligned}
\pi_j\mathbb E_{\nu_j}s
 &=Q_{12}(u_B,u_j)=Q_{12}(p,f_j)=p\pi_j,\\
\pi_j\mathbb E_{\nu_j}t
 &=Q_{23}(u_j,u_B)=Q_{23}(f_j,p)=p\pi_j.
\end{aligned}
\tag{208.9}
$$

Self-adjointness in the first step of the actual triple gives

$$
\mathcal C(u_B,u_j,u_B)
=\int_G P(gu_B)u_jPu_B\,dm
=\pi_j\mathbb E_{\nu_j}st.
\tag{208.10}
$$

The baseline is $\mathcal C(p,f_j,p)=p^2\pi_j$. Subtraction and (208.9) prove the identity in (208.5).

For almost every $x$, put $R_x(y)=g(y)/v(x)$. Its mean under $\mathsf P(x,dy)$ is one and its centered second moment is $\chi(x)$. The elementary covariance Cauchy–Schwarz estimate yields

$$
\begin{aligned}
s(x)-t(x)
 &=\int_G(R_x(y)-1)(u_B(y)-t(x))\,\mathsf P(x,dy),\\
(s(x)-t(x))^2&\le\chi(x)t(x)(1-t(x)).
\end{aligned}
\tag{208.11}
$$

This classical conditional covariance inequality is an intermediate estimate. Combining it with the exact algebraic identity

$$
2\mathbb E_{\nu_j}[(s-p)(t-p)]
=A_j+B_j-\mathbb E_{\nu_j}(s-t)^2
\tag{208.12}
$$

proves the lower bound in (208.5). Finally (208.9) implies

$$
\mathbb E_{\nu_j}t(1-t)=p(1-p)-A_j=\frac3{16}-A_j.
\tag{208.13}
$$

When $k_j<\infty$, this gives $H_j\le k_j(3/16-A_j)$, proving (208.6). The weighted estimate (208.8), rather than any global bounded likelihood ratio, supplies integrability. $\square$

**Definition 208.3 (hard relation forms).** In the coefficient space $\mathbb R^{\mathcal L}$ put

$$
\begin{gathered}
F_a=\sum_i a_if_i,\qquad K_{\rm rel}=\ker\Phi_f=\{a:F_a=0\},\\
h_a=\sum_i a_iu_i,\qquad
(a\odot b)_i=a_ib_i,\qquad
h_ah_b=h_{a\odot b},\\
s_a=\frac{P(gh_a)}v,\qquad t_a=Ph_a.
\end{gathered}
\tag{208.14}
$$

The product identity is the hard-indicator algebra of this actual partition. For $a,b\in K_{\rm rel}$ define the bilinear forms

$$
\begin{aligned}
M_j(a,b)&=\mathbb E_{\nu_j}[s_at_b],\\
G_j^+(a,b)&=\mathbb E_{\nu_j}[t_at_b],
& G_j^-(a,b)&=\mathbb E_{\nu_j}[s_as_b],\\
V_j(a,b)&=\mathbb E_{\nu_j}[P(h_ah_b)],\\
H_{\chi,j}(a,b)&=\mathbb E_{\nu_j}
 \bigl[\chi\bigl(P(h_ah_b)-t_at_b\bigr)\bigr].
\end{aligned}
\tag{208.15}
$$

Write $\operatorname{Sym}M_j(a,b)=(M_j(a,b)+M_j(b,a))/2$. The order $A\succeq B$ for symmetric forms on $K_{\rm rel}$ means $(A-B)(a,a)\ge0$ for every $a\in K_{\rm rel}$.

**Proposition 208.4 (Loewner budgets with an exact hard-product consumer).** All forms in (208.15) are finite. Their exact pair-calibrated budget and residual contraction are

$$
V_j(a,b)=\frac{Q_{23}(f_j,F_{a\odot b})}{\pi_j},
\qquad
M_j(a,b)=\frac1{\pi_j}\sum_{i,k}a_ib_k\Delta(D)_{ijk}.
\tag{208.16}
$$

They obey

$$
2\operatorname{Sym}M_j
\succeq G_j^++G_j^- -H_{\chi,j}.
\tag{208.17}
$$

If $k_j<\infty$, then also

$$
2\operatorname{Sym}M_j
\succeq(1+k_j)G_j^++G_j^- -k_jV_j.
\tag{208.18}
$$

In particular, full equality of the original sixty-four coordinates forces $M_j=0$ for every $j$ and hence the necessary budgets

$$
G_j^++G_j^-\preceq H_{\chi,j},\qquad
(1+k_j)G_j^++G_j^-\preceq k_jV_j
\quad\text{when }k_j<\infty.
\tag{208.19}
$$

*Proof.* For each bounded real $h$, the same conditional covariance calculation as (208.11) gives

$$
\left(\frac{P(gh)}v-Ph\right)^2
\le\chi\bigl(P(h^2)-(Ph)^2\bigr).
\tag{208.20}
$$

Both conditional means have absolute value at most $\|h\|_\infty$. The unweighted conditional variance is nonnegative and at most $\|h\|_\infty^2$. Thus (208.8) proves finiteness of its $\chi$-weighted integral. Conditional covariance Cauchy–Schwarz also bounds the absolute cross covariance for $h_a,h_b$ by $\|h_a\|_\infty\|h_b\|_\infty$, proving finiteness of every entry of $H_{\chi,j}$. All other forms have bounded integrands.

The hard product and the ordered pair calibration give

$$
\begin{aligned}
\pi_jV_j(a,b)
 &=Q_{23}(u_j,h_{a\odot b})\\
 &=\sum_i a_ib_iQ_{23}(f_j,f_i)
 =Q_{23}(f_j,F_{a\odot b}).
\end{aligned}
\tag{208.21}
$$

The baseline function here is $F_{a\odot b}$, not $F_aF_b$. It need not vanish when both $a$ and $b$ are baseline relations. Furthermore

$$
\begin{aligned}
\pi_jM_j(a,b)
 &=\mathcal C(h_a,u_j,h_b),\\
\mathcal C(F_a,f_j,F_b)&=0.
\end{aligned}
\tag{208.22}
$$

Multilinearity and subtraction prove the residual contraction in (208.16). The pair equations also give $\mathbb E_{\nu_j}s_a=\mathbb E_{\nu_j}t_a=0$ on $K_{\rm rel}$, so $G_j^\pm$ are the actual conditional covariance forms there.

Let $L_j(a,b)=\mathbb E_{\nu_j}[(s_a-t_a)(s_b-t_b)]$. The exact form identity and (208.20) give

$$
2\operatorname{Sym}M_j=G_j^++G_j^--L_j,
\qquad L_j\preceq H_{\chi,j},
\tag{208.23}
$$

which proves (208.17). If $k_j<\infty$, positivity of the conditional variance gives

$$
H_{\chi,j}\preceq k_j(V_j-G_j^+).
\tag{208.24}
$$

Substitution in (208.17) proves (208.18). If $\Delta(D)=0$, (208.16) forces the whole form $M_j$ to vanish, which proves (208.19). This implication uses all required triple contractions; vanishing of the symmetric part alone would be weaker. $\square$

**Corollary 208.5 (the unpaid $B3B$ direction and the full-zero boundary).** Let $\mathbf1_{\mathcal L}$ denote the all-one coefficient vector and set $\beta=e_B-p\mathbf1_{\mathcal L}$. Then $\beta\in K_{\rm rel}$ and

$$
\begin{gathered}
h_\beta=u_B-p,\qquad s_\beta=s-p,\qquad t_\beta=t-p,\\
G_j^+(\beta,\beta)=A_j,\qquad
G_j^-(\beta,\beta)=B_j,\qquad
H_{\chi,j}(\beta,\beta)=H_j,\\
V_j(\beta,\beta)=\frac3{16},\qquad
M_j(\beta,\beta)=\frac{\Delta(D)_{BjB}}{\pi_j}.
\end{gathered}
\tag{208.25}
$$

Thus every full-zero hard candidate must satisfy, for each $j$,

$$
A_j+B_j\le H_j,
\qquad
(1+k_j)A_j+B_j\le\frac3{16}k_j
\quad\text{if }k_j<\infty.
\tag{208.26}
$$

For $D\in\mathscr F_{154}(\theta)$ the case $j=B$ is already necessary from the imposed BBB equality. The case $j=3$ bounds the actual unpaid residual $\Delta(D)_{B3B}$, and a strict positive right-hand side in (208.5) or (208.6) excludes that particular $D$ from full-zero attainment. These are conditional exclusion criteria for a given partition; no positive margin over all original pair-calibrated partitions is asserted.

*Proof.* Since $\sum_i f_i=1$ and $f_B=p$, one has $F_\beta=0$. Hard multiplication gives

$$
h_\beta^2=(1-2p)u_B+p^2,
\qquad
F_{\beta\odot\beta}=(1-2p)f_B+p^2=p(1-p)=\frac3{16}.
\tag{208.27}
$$

Consequently (208.16) gives $V_j(\beta,\beta)=3/16$. Also
$P(h_\beta^2)-(Ph_\beta)^2=t(1-t)$, proving the asserted equality for $H_{\chi,j}$. The other form identifications follow from (208.3), (208.5) and (208.14). In particular, the scalar bounds are precisely the $\beta$ direction of the hard-algebra matrix bounds, with the same original source and the same actual terminals.

Appendix III (154.3), (154.32) and Definition 155.1 fix all ordered pairs, the six permutations of $013$ and BBB. They do not impose $B3B$. Pair-sum cancellation expresses that remaining coordinate as

$$
\Delta(D)_{B3B}=\sum_{i,k\in\{0,1,3\}}\Delta(D)_{i3k},
\tag{208.28}
$$

which includes repeated-label entries not individually fixed by (154.32). The two contrast channels in Appendix III (157.2) include exactly $h_\beta=u_B-p$; (208.25) constrains its first-and-third-slot contraction with the actual middle indicator $u_3$. Hence the budget has a consumer beyond the already paid binary BBB coordinate. Applying (208.5) and (208.6) gives (208.26) and the exclusion criterion.

The covariance estimate used in (208.11) and (208.20) is classical Cauchy–Schwarz. The source-specific deduction here combines it with the original reversed law (208.7), the finite weighted bound (208.8), the exact pair calibration and the hard product budget (208.21). Finite linear-moment purification, as in A. Dvoretzky, A. Wald and J. Wolfowitz, *Relations among certain ranges of vector measures*, [doi:10.2140/pjm.1951.1.59](https://doi.org/10.2140/pjm.1951.1.59), Theorem 4, does not by itself preserve the cubic same-partition law with its own propagated terminals.

These necessary inequalities neither construct a full-zero partition nor give a fixed-start successor. They assume no globally bounded or small $\chi$, no source label $q$ in the hard label span, no ideal property of a tensor radical, no positivity of $\mathcal C(r,r,1)$ and no local forward Gram definiteness. Coefficient correction rank, coarse moment rank and actual label-span rank retain their separate meanings; none is identified by this budget. The universal original $F_{64}$ target and the original physical succession question remain unresolved. $\square$

## 追加锚（本行以下为增补区）

## 209. Strict asymptotic slack of the native-source hard-partition budgets

**Definition 209.1 (a weak-star calibrated sequence).** Retain Definition 208.1, all of the original telescope of Appendix III Definitions 154.1 and 155.1, and the original source, clock, measure, operator and own-terminal convention. Fix one original $\theta$. Let $D_n=(D_{n,i})_{i\in\mathcal L}$ be deterministic whole-$G$ Borel partitions satisfying exactly (208.1), and write $u_{n,i}=\mathbf1_{D_{n,i}}$. Assume only

$$
u_{n,i}\overset{*}{\rightharpoonup}f_i\quad\text{in }L^\infty(G,m)
\qquad(i\in\mathcal L).
\tag{209.1}
$$

For $a\in\mathbb R^{\mathcal L}$ put

$$
h_{n,a}=\sum_i a_i u_{n,i},\qquad
t_{n,a}=Ph_{n,a},\qquad
s_{n,a}=\frac{P(gh_{n,a})}{v},
\tag{209.2}
$$

and define $G_{j,n}^\pm$, $H_{\chi,j,n}$ and $M_{j,n}$ from (208.15) with $u_j$ replaced by $u_{n,j}$. Thus $\pi_j$ remains the fixed number in (208.2), because (208.1) preserves the middle marginal. Put

$$
w=v\chi,\qquad
\xi_j=\frac1{\pi_j}\int_G f_jw\,dm,\qquad
\Lambda_j(a,b)=\frac1{\pi_j}\int_G f_jw\,P(F_{a\odot b})\,dm
\quad(a,b\in K_{\rm rel}).
\tag{209.3}
$$

No bounded global likelihood ratio, compact $L^2$ heat operator, source-span witness or parameter-uniform constant is included in this definition.

**Proposition 209.2 (the limiting relation budgets).** For every original $\theta$, the function $w$ is integrable and strictly positive almost everywhere. Each $\xi_j$ is finite and positive, each $\Lambda_j$ is a finite positive-definite symmetric form on $K_{\rm rel}$, and

$$
G_{j,n}^+\longrightarrow0,\qquad
G_{j,n}^-\longrightarrow0,\qquad
H_{\chi,j,n}\longrightarrow\Lambda_j
\quad\text{in matrix norm on }K_{\rm rel}.
\tag{209.4}
$$

Consequently, with

$$
S_{j,n}=G_{j,n}^++G_{j,n}^--H_{\chi,j,n},
\tag{209.5}
$$

one has $S_{j,n}\to-\Lambda_j$. There is one index after which all four $S_{j,n}$ are strictly negative definite, simultaneously for every nonzero relation direction.

*Proof.* The reversed conditional law (208.7) gives

$$
0\le w=v\chi=\frac{P(g^2)}{v}-v\le G_0-v,
\tag{209.6}
$$

so $w\in L^1(m)$. The original positive heat kernel and the source-start nonconstancy supplier imply that the conditional variance of $g$ in (208.7) is strictly positive at almost every middle state; hence $w>0$ almost everywhere. Since every $f_j$ is positive and bounded, this proves $0<\xi_j<\infty$.

For $a\in K_{\rm rel}$, (209.1) gives $h_{n,a}\overset{*}{\rightharpoonup}0$. The forward and reversed three-time kernels are integrable probability kernels: the forward one is the density used in Appendix II §123, and the reversed one is obtained from (208.7). Rectangular-tensor approximation in their respective $L^1$ spaces therefore makes their bounded multilinear integrals continuous under componentwise weak-star convergence. Applying this to (209.2) gives

$$
G_{j,n}^+(a,b)\to0,\qquad G_{j,n}^-(a,b)\to0
\quad(a,b\in K_{\rm rel}).
\tag{209.7}
$$

For the weighted term, $h_{n,a\odot b}\overset{*}{\rightharpoonup}F_{a\odot b}$, while $w\in L^1(m)$. The same two-variable tensor approximation, now for the kernel $w(x)P(x,dy)$, yields

$$
\frac1{\pi_j}\int_Gu_{n,j}wP(h_{n,a\odot b})\,dm
\longrightarrow
\frac1{\pi_j}\int_Gf_jwP(F_{a\odot b})\,dm.
\tag{209.8}
$$

The subtracted term in $H_{\chi,j,n}$ is $\mathbb E_{\nu_{j,n}}[\chi t_{n,a}t_{n,b}]$. To control this weighted term, use the original transition density $p_d(x,y)$ of $P$ from Appendix II Definition 123.1. For almost every $x$, its row $p_d(x,\cdot)$ belongs to $L^1(m)$ and has integral one. Thus weak-star convergence gives, for every $a\in K_{\rm rel}$,

$$
t_{n,a}(x)=\int_Gp_d(x,y)h_{n,a}(y)\,m(dy)
\longrightarrow\int_Gp_d(x,y)F_a(y)\,m(dy)=0
\quad\text{for almost every }x.
$$

Because the $u_{n,i}$ form a hard partition, $|h_{n,a}|\le\|a\|_\infty$, and the Markov property gives $|t_{n,a}|\le\|a\|_\infty$. Since $0\le u_{n,j}\le1$ and $w\in L^1(m)$, dominated convergence with dominator $\|a\|_\infty\|b\|_\infty w$ yields

$$
\left|\mathbb E_{\nu_{j,n}}[\chi t_{n,a}t_{n,b}]\right|
=\left|\frac1{\pi_j}\int_Gu_{n,j}w\,t_{n,a}t_{n,b}\,dm\right|
\le\frac1{\pi_j}\int_Gw\,|t_{n,a}t_{n,b}|\,dm
\longrightarrow0.
$$

Combining this with (209.8) and the exact definition (208.15) proves the third limit in (209.4). The coefficient space $K_{\rm rel}$ is finite-dimensional, hence entrywise convergence is matrix-norm convergence.

For $a\ne0$,

$$
F_{a\odot a}=\sum_i a_i^2f_i>0\quad\text{almost everywhere}.
\tag{209.9}
$$

Positivity improvement of $P$ gives $P(F_{a\odot a})>0$ almost everywhere. Thus (209.3) gives $\Lambda_j(a,a)>0$. Symmetry follows from $a\odot b=b\odot a$. Positive definiteness on the unit sphere of the finite-dimensional $K_{\rm rel}$ gives a positive minimum eigenvalue for each $j$; taking the minimum over the four labels and using (209.4) proves the final assertion. The only analytic inputs here are the original positive kernel, the bounded native source and the tensor-continuity mechanism already used for the actual path density; no global likelihood-ratio or compactness assumption has been added. $\square$

**Proposition 209.3 (finite-$k$ refinement and its eventual sign).** Let

$$
k_{j,n}=\operatorname*{ess\,sup}_{D_{n,j}}\chi
$$

with respect to $v\,m$. Whenever $k_{j,n}<\infty$,

$$
k_{j,n}\ge\frac{\xi_j}{2}
\tag{209.10}
$$

for all sufficiently large $n$. For those indices, the refined form

$$
R_{j,n}=\left(1+\frac1{k_{j,n}}\right)G_{j,n}^+
       +\frac1{k_{j,n}}G_{j,n}^- -V_{j,n}
\tag{209.11}
$$

is strictly negative definite on $K_{\rm rel}$ once $n$ is sufficiently large. If $k_{j,n}=\infty$, this refinement is inapplicable.

*Proof.* Since $w\in L^1(m)$, (209.1) gives

$$
\frac1{\pi_j}\int_Gu_{n,j}w\,dm\longrightarrow\xi_j.
\tag{209.12}
$$

The left side is the $\nu_{j,n}$-mean of $\chi$ and is at most $k_{j,n}$ whenever that essential supremum is finite. This proves (209.10). The conditional-variance estimate (208.24), with the current partition, gives

$$
H_{\chi,j,n}\preceq k_{j,n}(V_{j,n}-G_{j,n}^+).
\tag{209.13}
$$

Rearranging (209.13) yields

$$
R_{j,n}\preceq\frac1{k_{j,n}}S_{j,n}.
\tag{209.14}
$$

By Proposition 209.2, $S_{j,n}$ is eventually strictly negative definite, and (209.10) makes the scalar factor positive. Equation (209.14) therefore makes $R_{j,n}$ strictly negative definite as well. Infinite $k_{j,n}$ supplies no expression of the form (209.11). $\square$

**Corollary 209.4 (the unpaid $B3B$ coordinate has zero actual limit).** Let $\beta=e_B-\frac14\mathbf1_{\mathcal L}$. For each $j\in\mathcal L$, the unrefined lower-bound expression from (208.5) satisfies

$$
\frac{\pi_j}{2}\bigl(A_{j,n}+B_{j,n}-H_{j,n}\bigr)
\longrightarrow
-\frac3{32}\int_G f_jv\chi\,dm<0,
\tag{209.15}
$$

where $A_{j,n}=G_{j,n}^+(\beta,\beta)$, $B_{j,n}=G_{j,n}^-(\beta,\beta)$ and $H_{j,n}=H_{\chi,j,n}(\beta,\beta)$. At the same time,

$$
\Delta(D_n)_{BjB}\longrightarrow0,
\qquad
\|\Delta(D_n)\|_{\max}\longrightarrow0.
\tag{209.16}
$$

*Proof.* The hard product identity in (208.27) gives $F_{\beta\odot\beta}=3/16$. Therefore (209.3) gives

$$
\Lambda_j(\beta,\beta)=\frac3{16\pi_j}\int_Gf_jv\chi\,dm.
\tag{209.17}
$$

The first limit in (209.15) follows from Proposition 209.2 and (209.17), and its strict sign follows from $f_jw>0$ almost everywhere. The inequality (208.5) still holds for each $D_n$, but its right side has the negative limit (209.15).

For (209.16), approximate the original three-time density by finite sums of rectangular $L^1(m^3)$ tensors as in Appendix II §123.2. Every coefficient

$$
\mathcal C(u_{n,y},u_{n,z},u_{n,k})
$$

then converges to $\mathcal C(f_y,f_z,f_k)$, with the third factor interpreted through the same partition's actual $P u_{n,k}$. Hence all sixty-four residuals converge to zero, including the displayed $BjB$ coordinate. The negative limit in (209.15) is therefore a lower-bound slack, not a residual obstruction. $\square$

**Theorem 209.5 (a source-specific co-selected sequence realizing the slack).** For every original $\theta$, there exists a sequence of deterministic whole-$G$ Borel partitions

$$
D_n\in\mathscr F_{154}(\theta)
$$

whose own terminals are used in every coordinate, such that (208.1) holds, $u_{n,i}\overset{*}{\rightharpoonup}f_i$ for every $i$, and

$$
\Delta(D_n)_{BB3}>0,\qquad
\|\Delta(D_n)\|_{\max}\longrightarrow0.
\tag{209.18}
$$

*Proof.* Use the actual finite construction of Appendix III §§154.E and 155.2. For its fixed original $\theta$, write $\kappa=R_{BB3}>0$ and $J=\|R\|_\infty>0$ as in (155.4). Choose $t_n\downarrow0$ with $t_n<t_0$ and set, for example,

$$
\varepsilon=\frac12,\qquad
\delta_n=\frac{t_n^2}{32}\min\{\kappa,J\}.
\tag{209.19}
$$

Then the strict restriction in (155.5) holds for $(t,t',\delta)=(t_n,t_n/2,\delta_n)$. Theorem 155.2 supplies co-selected actual partitions $D_n,D_n'\in\mathscr F_{154}(\theta)$ from one common finite-cell quantile construction. Retain the first endpoint. Its estimates give

$$
\Delta(D_n)_{BB3}>t_n^2\kappa-\delta_n>0,\qquad
\|\Delta(D_n)\|_{\max}\le t_n^2J+\delta_n\longrightarrow0.
\tag{209.20}
$$

It remains to make the weak-star quantifier explicit. Fix a countable $L^1(m)$-dense family of tests. In the quantile construction of 154.E, refine the finite coordinate partition far enough at the $n$th step to match the center $u^{(t_n)}$ on the first $n$ tests to error $<1/n$; the cell-mass identities and density of the refining partitions give this uniformly for the finitely many tests. Since $u^{(t_n)}\to f$ in $L^\infty$ as $t_n\downarrow0$, choose $t_n$ recursively so that its first $n$ test pairings differ from those of $f$ by $<1/n$. The diagonal sequence of indicators therefore converges componentwise weak-star to $f$. The same refinement is allowed in the Brouwer step because the approximation estimates in (154.30) and (155.15) improve along the refining partitions. The exact $\mathcal H_{43}$ roots give (208.1), and every coefficient in (209.20) is evaluated with the corresponding partition's own propagated terminals. No endpoint is held fixed and no physical successor is asserted. $\square$

Theorem 209.5 consumes the finite calibrated endpoints of §155.2 to realize the sequence hypothesis of Propositions 209.2–209.4 for every original parameter. It shows that the particular exclusion mechanism of Section 208 loses its sign margin on actual original hard approximants: the matrix budgets converge to the strictly negative source form $-\Lambda_j$, the refined finite-$k$ budgets are eventually negative where defined, and the unrefined $B3B$ lower bound converges to a negative number while the actual residual converges to zero. This does not construct an original $F_{64}$ witness, prove nonattainment, or provide a successor from an arbitrary fixed endpoint; the fixed-start summable chain of (155.31), the universal $F_{64}$ question and the physical succession question remain open.

## 追加锚（本行以下为增补区）
## 210. One actual common partition with both cubic contrast channels zero

**Definition 210.1 (the unchanged source and fifty coordinates).** Retain exactly the complete original telescope of Appendix III Definitions 134.1, 154.1 and 155.1, including every inherited endpoint, source, analytic and readout supplier of Appendix II §§115–117, 123–125 and 133. Thus $\theta=(a,\eta,d,b)$ ranges over every original finite $a,\eta,d>0$ and every permitted whole-$G$ Borel representative $b$ of $g_d$ with $0<b\le M$. Keep the original group product on $G=H^1\times\mathbb R$, raw Haar measure $\mu$, source $e$, unit-source field $L\Gamma=\delta_e$, coefficient-one $w_*$, coefficient-positive normalized $h$, selector $A_{\rm src}=\rho C_{\rm src}$, full conservative source-inclusive $K$, measure $m=h^2\mu$, semigroup $T_s$, $P=T_d$, $g=g_{2d}$, clock and units. The source starts at $e$ at time zero, the epochs remain $2d,3d,4d$, and the original common stochastic readout $f$ uses its original conditionally independent fresh noises. In particular,

$$
\begin{gathered}
p=\tfrac14,\quad c=(4M)^{-1},\quad
f_3=cb,\quad f_B=p,\quad f_0=f_1=(\tfrac34-cb)/2,\\
\mathcal C(v,w,z)=\int_GgvP(wPz)\,dm,\qquad
\eta_1(u)=u_0-u_1,\quad\eta_2(u)=u_B-p,\\
\mathcal G_{\alpha\beta\gamma}(u)
 =\mathcal C(\eta_\alpha(u),\eta_\beta(u),\eta_\gamma(u))
 \quad(\alpha,\beta,\gamma\in\{1,2\}).
\end{gathered}
\tag{210.1}
$$

Let $\mathcal H_{36}$ denote the first thirty-six coordinates of (154.2), and put

$$
\mathcal H_{50}(u)=\left(
 \mathcal H_{36}(u),\
 (\mathcal C(u_y,u_z,u_w))_{yzw\in\mathcal T_6},\
 (\mathcal G_{\alpha\beta\gamma}(u))_{\alpha,\beta,\gamma\in\{1,2\}}
 \right).
\tag{210.2}
$$

Here $u$ is one pointwise simplex tuple, $u_B=1-u_0-u_1-u_3$, and $\mathcal T_6$ is the six permutations of $013$. The last eight target coordinates are zero since $\eta_\alpha(f)=0$. On the exact $\mathcal H_{36}$ fiber the complement identities give all ordered pair laws and all marginals, so expansion of $u_B=p+\eta_2(u)$ gives

$$
\mathcal G_{222}(u)=\mathcal C(u_B,u_B,u_B)-p^3.
\tag{210.3}
$$

Indeed the linear terms are its three zero marginal contrasts, and each quadratic term is a zero pair contrast. Thus exact $\mathcal H_{50}$ means exact $\mathcal H_{43}$ and the seven other contrast equations, with the same tuple throughout.

**Theorem 210.2 (universal actual hard coattainment of the seven contrast obligations).** Under exactly Definition 210.1, for every original $\theta$ there exists one deterministic pointwise Borel partition $D=(D_0,D_1,D_3,D_B)$ of the whole original $G$ such that

$$
\begin{gathered}
D\in\mathscr F_{154}(\theta),\qquad
\mathcal G_{\alpha\beta\gamma}(\mathbf1_D)=0
 \quad(\alpha,\beta,\gamma\in\{1,2\}),\\
\Delta(D)\in\mathcal W_{13}\text{ of (157.6)},\qquad
\Delta(D)_{BB3}>0.
\end{gathered}
\tag{210.4}
$$

All coefficients use $D$ itself in every slot and its own propagated terminal $P\mathbf1_{D_w}$. No rank, inverse, trace-regularity, full-zero seed or physical realization hypothesis is added. Containment in $\mathcal W_{13}$ asserts no realization of every direction in that space. The strict last inequality makes this particular $D$ fail the full $F_{64}$ equality.

*Proof.* Fix an arbitrary original $\theta$. Use the quotient $\mathcal Q$, angular coordinate, measure $\nu$, orbit $q_\circ$, neighborhood $U$, invariant slack set $E$ and invariant representatives $b^0,f^0$ of (153.5)–(153.6). Thus $f_3^0\ge c\tau$ on $E$, whereas $f_0^0,f_1^0,f_B^0\ge1/4$ on $G$. All target integrals for $f^0$ equal those for the prescribed $f$.

### 210.A. Two separated self-frequency pairs from the actual source

Use the actual orbit coefficients $a_j$ of (153.7)–(153.10):
$a_j=a_{-j}>0$ and $a_j\to0$. First choose $n_0,n_1,m_*$ exactly as in (154.5), and write $L_0=m_*$. For every fixed positive odd integer $p$, there are arbitrarily large odd $q$ with

$$
a_{q+p}\ne a_{q-p}.
\tag{210.5}
$$

Otherwise $a_{k+2p}=a_k$ for all sufficiently large even $k$. Iteration along one such progression contradicts both $a_k>0$ and $a_k\to0$. Choose positive odd integers successively so that

$$
\begin{gathered}
p_0>10L_0,\quad q_0>10p_0,\quad
p_1>10q_0,\quad q_1>10p_1,\\
a_{q_i+p_i}\ne a_{q_i-p_i}\quad(i=0,1),\qquad L=q_1.
\end{gathered}
\tag{210.6}
$$

These choices exist by (210.5) and impose no restriction on $\theta$. In the seed frequency set

$$
\mathcal M=\{1,n_0,n_1,m_*,p_0,q_0,p_1,q_1\},
\qquad k_i^\pm=q_i\pm p_i,
\tag{210.7}
$$

each $k_i^\pm$ has just one unordered representation as a positive absolute signed sum of two members of $\mathcal M$: the pair $p_i,q_i$ with the indicated sign. To check this, a later, larger new frequency paired with a different frequency has difference greater than $9$ times its predecessor and hence greater than $k_i^+$. Its double is larger still. Among frequencies up to $q_i$, a pair not using $q_i$ has sum at most $2p_i<q_i-p_i$. A pair using $q_i$ must therefore use $p_i$. Equal-frequency differences are zero. The same argument covers pairs involving the original four modes, all at most $L_0$.

Use $\mathcal K_j$, $\kappa_j$ and the cosine evaluation $\mathfrak c_j^q$ from (154.6). Each of the finitely many relevant $\kappa_j$ is continuous and has $\kappa_j(q_\circ)=a_j>0$. Nonconstancy and analytic uniqueness for the original $g$, as in 154.A, supply one $q_\diamond\in U$ with

$$
\begin{gathered}
g_1:=g(q_\diamond)\ne g_0:=g(q_\circ),\\
\kappa_{n_1+1}(q_\diamond),\quad
\kappa_{n_1+m_*}(q_\diamond),\quad
\kappa_{n_0+1}(q_\diamond),\quad
\kappa_{k_0^+}(q_\diamond),\quad
\kappa_{k_1^+}(q_\diamond)>0.
\end{gathered}
\tag{210.8}
$$

Take the nonnegative normalized bumps $\phi_\epsilon$ of (154.8), and write $V_j=\phi_\epsilon(q)\cos(j\vartheta)$. Set

$$
\begin{aligned}
z_i&=V_{p_i}+V_{q_i}\quad(i=0,1),\\
v_0&=V_{n_0}+z_0,\qquad
v_1=V_{n_1}+z_1,\qquad v_3=V_1+V_{m_*}.
\end{aligned}
\tag{210.9}
$$

They are bounded Borel, supported in $E$, odd under the half-turn and have disjoint positive spectra. The parameter $\epsilon>0$ will be fixed below.

### 210.B. Actual three-slot separation at each self-frequency pair

Use $\mathsf A,\mathsf B,\mathsf T$ of (154.9), and consider the three scalar densities

$$
A_i=\mathsf A(z_i,z_i),\qquad
B_i=\mathsf B(z_i,z_i),\qquad
T_i=\mathsf T(z_i,z_i).
\tag{210.10}
$$

For each $i$, evaluate these three columns by the three rows
$\mathfrak c_{k_i^+}^{q_\circ}$,
$\mathfrak c_{k_i^-}^{q_\circ}$ and
$\mathfrak c_{k_i^+}^{q_\diamond}$.
Put $H_i=(a_{p_i}+a_{q_i})/2$, $a_i^\pm=a_{k_i^\pm}$ and $\kappa_i=\kappa_{k_i^+}(q_\diamond)$. The localization identities (154.12), applied to both orders of $p_i,q_i$, give the limiting evaluation matrix

$$
M_i=
\begin{pmatrix}
g_0H_i a_i^+&g_0a_{p_i}a_{q_i}&g_0H_i a_i^+\\
g_0H_i a_i^-&g_0a_{p_i}a_{q_i}&g_0H_i a_i^-\\
g_1H_i\kappa_i&b_i&g_0H_i\kappa_i
\end{pmatrix}.
\tag{210.11}
$$

Here $b_i=\mathfrak c_{k_i^+}^{q_\diamond}
[g_0(\mathcal K_{p_i}+\mathcal K_{q_i})^2]$ is finite; its value is immaterial. At $q_\circ$ the mixed product in $B_i$ has coefficient $g_0a_{p_i}a_{q_i}$ at each of the two frequencies. The self products have frequencies $0,2p_i,2q_i$ and contribute to neither row. In $A_i,T_i$ the two mixed orders contribute $H_i$ times the corresponding heat character. At $q_\diamond$ their difference is $(g_1-g_0)H_i\kappa_i$. Consequently, subtracting the third column from the first gives

$$
\det M_i=(g_1-g_0)g_0^2a_{p_i}a_{q_i}
 H_i^2\kappa_i(a_i^- -a_i^+)\ne0.
\tag{210.12}
$$

Every nonzero factor is supplied by (210.5)–(210.8) and the actual orbit positivity. The localization is uniform on both output orbits by (154.12), including the equal-frequency terms in the expansions. Thus both actual three-by-three determinants are nonzero for all sufficiently small fixed $\epsilon>0$.

The six two-component densities $\mathbf R_\sigma[v]$, $\sigma\in\mathcal T_6$, of (154.10) also retain the six-column rank certificate of (154.13)–(154.16). Indeed their component $0$ contains products of $v_1,v_3$ only, and component $1$ products of $v_0,v_3$ only. Every new contribution has frequency at least $p_0-L_0>2L_0$, whereas all seven evaluations in that certificate have frequency at most $2L_0$. Those evaluations are therefore exactly the original ones. Fix one sufficiently small $\epsilon$ for these six columns and both determinants in (210.12). All subsequent inputs are actual bounded functions for this fixed choice.

### 210.C. Exact pair corrections preserving every protected evaluation

Choose an odd $N>10L$ and precisely the infinite sector sets $S_0,S_1,S_3$ of (154.18). Apply 152.A–C and (154.19) to the enlarged $v_a$ in (210.9). In detail, choose $y_a,h_{a,1},\ldots,h_{a,6}\in X_{E,S_a}$ with $\ell_j(y_a)(h_{a,k})=\delta_{jk}$, and choose $w_a\in X_{E,S_a}$ satisfying

$$
\begin{gathered}
\ell_j(w_a)(h_{a,k})=0,\qquad B_r(y_a,w_a)=0,\\
q(w_a)=-q(v_a)-q(y_a),\qquad x_a=v_a+y_a+w_a.
\end{gathered}
\tag{210.13}
$$

There are only finitely many homogeneous constraints, so the exact three-quadratic surjectivity (152.29) applies. Low and high sectors are disjoint. Hence

$$
q_r(x_a)=0,\quad
Q_r(x_a,x_b)=0\ (a\ne b),\quad
\ell_j(x_a)(h_{a,k})=\delta_{jk}.
\tag{210.14}
$$

The $x_a$ remain bounded, $E$-supported, odd and of finite disjoint spectra. Every positive protected frequency above is at most $2L$. A low/high product has frequency at least $N-L>2L$; a high/high product has frequency a multiple of $N$, either zero or at least $N$. Multiplication by invariant $g$ and application of $P$ preserve characters. Thus every protected coefficient of every quadratic density $\mathsf A,\mathsf B,\mathsf T$ is unchanged on both output orbits. In particular the old six-column certificate and both self-frequency determinants survive these exact corrections.

Put

$$
s=x_0+x_1+x_3,\qquad
Z_1=x_0-x_1,\quad Z_2=-s,\qquad
v^{[0]}=(1,-1),\quad v^{[1]}=(-1,-1),\quad v^{[3]}=(0,-1).
\tag{210.15}
$$

Thus $Z=\sum_{i\in I}v^{[i]}x_i$. For variations of components $0,1$ alone, compensated in $B$, their contrast variations are $\delta\eta=v^{[0]}h_0+v^{[1]}h_1$. Let $\mathsf Z$ remove the angular mean, componentwise. For each $\alpha,\beta,\gamma\in\{1,2\}$ define a two-component density by

$$
R_{\alpha\beta\gamma}^{(j)}=
\mathsf Z\left[
 v^{[j]}_\alpha\mathsf A(Z_\beta,Z_\gamma)
 +v^{[j]}_\beta\mathsf B(Z_\alpha,Z_\gamma)
 +v^{[j]}_\gamma\mathsf T(Z_\beta,Z_\alpha)
\right],\qquad j=0,1.
\tag{210.16}
$$

The order in the last term is fixed by self-adjointness:
$\mathcal C(Z_\alpha,Z_\beta,h)=\langle h,P(Z_\beta P(gZ_\alpha))\rangle_m$.
Together with the six $\mathbf R_\sigma[x]$, these are fourteen bounded continuous two-component densities on $\Omega$, even and with zero angular mean.

They are linearly independent. Suppose a combination of the six old rows and eight rows (210.16) vanishes. Write the latter coefficients as a trilinear functional $\lambda$ on $(\mathbb R^2)^3$. At the protected frequencies $k_i^\pm$, the old six rows vanish by (210.7): each uses one input from $x_3$ and one from a different component. Among the new rows only the mixed $p_i,q_i$ terms in $x_i,x_i$ survive. For component $j=0,1$, its three protected evaluations are consequently the evaluations of

$$
\lambda(v^{[j]},v^{[i]},v^{[i]})A_i
 +\lambda(v^{[i]},v^{[j]},v^{[i]})B_i
 +\lambda(v^{[i]},v^{[i]},v^{[j]})T_i.
\tag{210.17}
$$

Equations (210.12)–(210.14) force all three coefficients to vanish, for each $i,j\in\{0,1\}$. The vectors $v^{[0]},v^{[1]}$ form a basis of $\mathbb R^2$. Every length-three word in a two-element basis repeats one basis element at least twice. Thus (210.17) makes $\lambda$ zero on every basis tensor, and $\lambda=0$. The remaining six coefficients vanish by the retained six-column certificate. This proves independence for the actual corrected functions.

Index the fourteen rows by $\rho$, and write them as $\mathbf R_\rho$. Their Gram matrix

$$
\mathsf G_{\rho\sigma}
 =\int_G\left(R_\rho^{(0)}R_\sigma^{(0)}
             +R_\rho^{(1)}R_\sigma^{(1)}\right)dm
\tag{210.18}
$$

is positive definite: a zero quadratic form gives an almost-everywhere zero combination, hence a pointwise zero combination on $\Omega$ by continuity and full support, contrary to the protected evaluations.

### 210.D. An exact stochastic zero, fifty legal directions and a positive margin

Choose sufficiently small $t>0$ and put

$$
u_a^*=f_a^0+t x_a\quad(a\in I),\qquad u_B^*=p-ts.
\tag{210.19}
$$

The tuple has positive slack in all components on $E$, and uniform global slack in $0,1,B$. Equations (210.14), parity and disjoint spectra give the exact lower laws and all six distinct-label equations exactly as in 154.D. Both contrasts at $u^*$ are $tZ_\alpha$, so their cubic coefficients vanish by simultaneous half-turn oddness. Therefore

$$
\mathcal H_{50}(u^*)=\mathcal H_{50}(f).
\tag{210.20}
$$

For the lower thirty-six rows use the nine invariant and twenty-seven odd directions of 154.D, now with (210.14). The invariant source Gram matrix is positive definite by Lemma 147.2 and quotient analytic uniqueness. The six ordered functionals in each correction sector give the three diagonal and six off-diagonal pair directions for each corresponding label or unordered pair. Their lower thirty-six-row matrix is invertible by (152.34)–(152.36). All component-$3$ variations are supported in $E$.

For each of the fourteen rows add the direction

$$
\delta_\rho u_0=R_\rho^{(0)},\quad
\delta_\rho u_1=R_\rho^{(1)},\quad
\delta_\rho u_3=0,\quad
\delta_\rho u_B=-R_\rho^{(0)}-R_\rho^{(1)}.
\tag{210.21}
$$

For any even, zero-angular-mean direction $h=(h_0,h_1)$ of this form, the lower thirty-six differentials vanish: invariant pairings vanish by zero angular mean and odd pairings by parity. The six triple differentials are (154.26). For the eight contrast coordinates the three-slot derivative at $\eta(u^*)=tZ$ is exactly $t^2$ times pairing with (210.16). Angular-mean removal changes no such pairing. Thus the last fourteen rows on these directions have matrix $t^2\mathsf G$. The full fifty-direction matrix is block triangular, with invertible diagonal blocks of sizes $36$ and $14$.

Choose bounded Borel representatives with the finite character expressions on $\Omega$, and repair a common Borel null set as in 154.D. The first thirty-six directions vary component $3$ only on $E$; the last fourteen keep it fixed and vary the globally positive components $0,1,B$. Consequently a positive-radius closed Euclidean ball in these fifty directions consists of pointwise simplex tuples on all of $G$.

The same center has a strictly positive BB3 residual. Its low frequency $n_0$ occurs in $s$ with nonzero coefficient and in no other component, so $s\ne0$. Using $Pf_3^0=cg$, (210.14), parity and source propagation, precisely the computation (155.11) gives

$$
\Delta(u^*)_{BB3}=t^2\kappa,\qquad
\kappa=c\langle gs,P(gs)\rangle_m
       =c\|T_{d/2}(gs)\|_2^2>0.
\tag{210.22}
$$

The last step uses the original $g>0$ almost everywhere and injectivity of the full self-adjoint heat semigroup. No quantitative coercivity is required.

### 210.E. One finite hard root for all fifty coordinates

Write the fifty directions as $e_1,\ldots,e_{50}$, including their compensating $B$ components, and set

$$
u(z)=u^*+\sum_{k=1}^{50}z_ke_k,\qquad
F(z)=\mathcal H_{50}(u(z))-\mathcal H_{50}(f),\qquad A=DF(0).
\tag{210.23}
$$

The polynomial map has $F(0)=0$ and invertible $A$. Choose a legal closed radius-$r$ ball, with $r>0$, sufficiently small that

$$
\sup_{\|z\|\le r}\|z-A^{-1}F(z)\|<r/3,\qquad
\sup_{\|z\|\le r}|\Delta(u(z))_{BB3}-t^2\kappa|
 <t^2\kappa/3.
\tag{210.24}
$$

The first estimate follows from $F(z)=Az+O(\|z\|^2)$; the second from continuity at the fixed positive $t$.

Apply the common finite coordinate-quantile construction of 154.E to this entire ball. On each positive-mass cell of the increasing finite Borel partitions $\mathcal P_n$, consecutive nested quantile slices of masses $\int_{A_0}u_y(z)\,dm$, in order $0,1,3,B$, define one partition $D_n(z)$. Such cuts exist because $m\ll\mu$ makes every first-coordinate hyperplane null. Assign the zero-mass cells to $B$. The result is a deterministic whole-$G$ pointwise Borel partition and satisfies (154.29).

Keep exactly the original path density

$$
W(x_1,x_2,x_3)=g(x_1)p_d(x_1,x_2)p_d(x_2,x_3),\qquad
W_n=\mathbb E[W\mid\mathcal P_n^{\otimes3}],\qquad
\|W-W_n\|_1\longrightarrow0.
\tag{210.25}
$$

Every coordinate of $\mathcal H_{50}$ is an integral against $W$ of three slot factors of absolute value at most one. This includes the signed factors $\eta_1,\eta_2$. Their cell integrals agree for $u(z)$ and $\mathbf1_{D_n(z)}$ because they are affine combinations of the four channels and the constant function. With $W_n$ all products factor cellwise, so the integrals agree exactly. It follows that

$$
\begin{gathered}
F_n(z)=\mathcal H_{50}(\mathbf1_{D_n(z)})-\mathcal H_{50}(f),\\
\sup_{\|z\|\le r}\|F_n(z)-F(z)\|
 \le2\sqrt{50}\,\|W-W_n\|_1,\\
\sup_{\|z\|\le r}
 |\Delta(D_n(z))_{BB3}-\Delta(u(z))_{BB3}|
 \le2\|W-W_n\|_1.
\end{gathered}
\tag{210.26}
$$

Each $F_n$ is continuous. Telescope its slot products; signed contrasts change by sums of the changed indicators. Integration against the bounded original slot marginals $g,Pg,P^2g$, followed by (154.29), proves continuity. Thus no differentiation of moving quantile boundaries is used.

Choose one finite $n$ with

$$
2\sqrt{50}\|A^{-1}\|\|W-W_n\|_1<r/3,\qquad
2\|W-W_n\|_1<t^2\kappa/3.
\tag{210.27}
$$

By (210.24), the continuous map $z\mapsto z-A^{-1}F_n(z)$ sends the closed radius-$r$ ball into its radius-$2r/3$ ball. Brouwer's finite-dimensional closed-ball theorem gives a fixed point $z_n$. Therefore the single actual partition

$$
D=D_n(z_n),\qquad
\mathcal H_{50}(\mathbf1_D)=\mathcal H_{50}(f),\qquad
\Delta(D)_{BB3}>t^2\kappa/3>0
\tag{210.28}
$$

exists at one finite $n$. The last inequality follows by subtracting the two errors in (210.24) and (210.26) from (210.22).

### 210.F. Exact residual containment and the completion boundary

The first thirty-six equations and the complement identities recover every original marginal and every ordered pair law. Equation (210.3) recovers BBB from $\mathcal G_{222}=0$, so (210.28) gives $D\in\mathscr F_{154}(\theta)$. For this actual partition, the pair contractions give $\Delta(D)\in H^{\otimes3}$. The exact identity (157.8) and the eight zero contrasts give

$$
\pi^{\otimes3}\Delta(D)=0.
\tag{210.29}
$$

The kernel identity in the proof of Proposition 157.2 now gives $\Delta(D)\in\mathcal W$, without a limiting or small-amplitude assumption on $\mathbf1_D-f$. The six distinct-label equations then give $\Delta(D)\in\mathcal W_{13}$. This proves (210.4). Every coefficient was evaluated against (210.25), which uses precisely this partition's own terminal. Replacing $b^0$ by the prescribed $b$ changes no target integral because all three positive-time slot laws are absolutely continuous with respect to $m$.

The construction settles the seven actual cubic obligations identified after (157.12), within the finite common-partition completion problem of §156.4. The remaining residual lies in a thirteen-dimensional containing space and is nonzero by (210.28). No zero of those remaining equations, universal $F_{64}$ attainment or exclusion, fixed-start summable successor, or physical succession follows.

The new source-specific deduction is the simultaneous separation (210.6)–(210.18) and its use in the finite hard root (210.28); it is repo-derived relative to the retained suppliers. The exact sector corrections are those of 152.A–C, with B. S. Mityagin, *The zero set of a real analytic function*, [arXiv:1512.07276v1](https://arxiv.org/abs/1512.07276v1), Proposition 0, and R. Meshulam and P. Šemrl, *Locally linearly dependent operators*, [doi:10.2140/pjm.2002.203.441](https://doi.org/10.2140/pjm.2002.203.441), Theorem 2.2, consumed there under their stated hypotheses. The finite fixed-point step is L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), in the closed-ball form already consumed in 154.E. These classical intermediates are not new general splitting or purification theorems, and no historical novelty claim is attached to them or their source-specific use. $\square$

## 追加锚（本行以下为增补区）
