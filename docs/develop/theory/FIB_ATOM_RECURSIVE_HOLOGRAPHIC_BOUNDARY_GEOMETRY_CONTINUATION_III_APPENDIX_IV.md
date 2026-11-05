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
