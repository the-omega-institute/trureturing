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
