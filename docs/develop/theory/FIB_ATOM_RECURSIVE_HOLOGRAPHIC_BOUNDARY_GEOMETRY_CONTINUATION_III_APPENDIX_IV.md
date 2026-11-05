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

## 166. The finite (L^2) representer bridge for the calibrated kernel

Section 165 treats the original first-order kernel (V) as a bounded-function constraint while the successor orbit is described in (L^2(m)). For the actual equal-gap readout of Appendix III, the first-order constraints have explicit (L^2(m)) representers. This identifies the finite calibration plane that must be added to any later successor orbit, without asserting that the orbit preserves (V) or that a physical successor exists.

**Definition 166.1 (the first-order representer plane).** Retain the complete telescope of Appendix III Definition 134.1 and the real labels (mathcal L={0,1,3,B}). Write (H=L^2(G,m;mathbb R)), (P=T_d), and use pointwise multiplication for products of functions. For (alpha=(y,z,w)inmathcal L^3), define

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

The span is finite-dimensional, with dimension at most (64). Orthogonal complements below are taken in (H), while bounded functions are understood as their (m)-classes.

**Proposition 166.2 (explicit representers for all first-order constraints).** For every (alpha=(y,z,w)inmathcal L^3), the function (psi_{yzw}) has a bounded Borel representative and belongs to (H). For every bounded real Borel (v),

$$
\ell_{yzw}(v)=\langle v,\psi_{yzw}\rangle_H.
\tag{166.3}
$$

Consequently, with (V=\ker\Lambda) as in Appendix III Definition 134.1,

$$
V=L^\infty(G,m;\mathbb R)\cap W^\perp.
\tag{166.4}
$$

*Proof.* The inherited source estimate in Appendix III (134.4) gives (g=P g_d), while Theorem 133.2 gives (g_din L^\infty(m)). The Markov (L^\infty)-contraction of (P) therefore gives (g\in L^\infty(m)). Equation (134.8) gives (f_y\in L^\infty(m)) for every label. Applying the same contraction to the products in (166.1) shows that (A_{yzw}), (B_{yzw}), and (C_{yzw}) are bounded Borel (m)-classes, hence belong to (H). Their displayed Borel representatives may be chosen simultaneously for the finite set of labels.

For the first term of (134.11), self-adjointness of (P) gives

$$
\mathcal C(v,f_z,f_w)
 =\langle g v,P(f_z P f_w)\rangle_H
 =\langle v,A_{yzw}\rangle_H.
\tag{166.5}
$$

For the second term, move (P) across the pairing once:

$$
\mathcal C(f_y,v,f_w)
 =\langle g f_y,P(v P f_w)\rangle_H
 =\langle P(g f_y),v P f_w\rangle_H
 =\langle v,B_{yzw}\rangle_H.
\tag{166.6}
$$

For the third term, move (P) across the pairing twice:

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

Substitution of (166.5)--(166.7) into the definition of (ell_{yzw}) in (134.11) proves (166.3). All pairings are legitimate because (m) is a probability and every displayed factor is bounded. The simultaneous vanishing of the (64) coordinates is therefore exactly orthogonality to (W), which proves (166.4). (square)

**Corollary 166.3 (the calibrated plane and a successor orbit).** Let

$$
H_{\mathrm{cal}}=\overline{\operatorname{span}_{\mathbb R}V}^{\,H}.
\tag{166.8}
$$

Then (H_{\mathrm{cal}}subseteq W^\perp). Equality requires an additional density statement and is not supplied by the finite representer calculation. If a finite (L^2(m))-representable readout has representers (psi_1,ldots,psi_r) and its specified successor stack is (R_j=R\circ P^j), put

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

Indeed, (166.4) supplies the condition (v\perp W), while Proposition 165.2 supplies (v\perp\mathcal C_R); orthogonality to both closed subspaces is equivalent to orthogonality to the closure of their algebraic sum. Formula (166.10) is an interface identity only. It does not prove that (mathcal C_R) is dense in (H_{\mathrm{cal}}), that (mathcal C_R) has a nonzero bounded localized complement, or that the successor action maps (V) into (V). It also does not construct a physical successor, a nonlinear residual-zero family, a legal simplex partition, an exact (H43) partition, a terminal compensator, an (SRS	ext{-}20) or (F_{64}) witness, or a Lean/kernel theorem.

The deductions (166.1)--(166.10) are source-specific consequences of the original bounded equal-gap readout and the self-adjoint heat contraction. They are not a claim that the representer bridge, the successor orbit, or its physical realization is present in the original model beyond the hypotheses displayed here.

## 追加锚（本行以下为增补区）
