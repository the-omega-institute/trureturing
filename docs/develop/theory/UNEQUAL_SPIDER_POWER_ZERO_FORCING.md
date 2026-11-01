# Ordinary powers of spiders with independently chosen leg lengths

## 1. The graph and its invariants

**定义 1.1（spider and ordinary power）。** Fix integers $m\ge 2$ and $k\ge 1$, and choose integers

$$
\ell_1,\ldots,\ell_m\ge k+1.
$$

Let

$$
V=\{c\}\,\cup\,\{(i,d):1\le i\le m,\ 1\le d\le \ell_i\},
\qquad
N=|V|=1+\sum_{i=1}^m\ell_i.
$$

The spider $T$ has center $c$ and the $i$th leg $(i,1),\ldots,(i,\ell_i)$, with consecutive vertices joined. Its distance is

$$
\delta(c,(i,d))=d,
$$

and, for leg vertices,

$$
\delta((i,d),(j,e))=
\begin{cases}
|d-e|,&i=j,\\
d+e,&i\ne j.
\end{cases}
$$

The ordinary distance-at-most-$k$ power $G=T^k$ has the same vertex set and has an edge between distinct vertices precisely when their $T$-distance is at most $k$.

**定义 1.2（forcing and symmetric minimum rank）。** In ordinary zero forcing a set of initially black vertices is enlarged by the rule

$$
\text{a black vertex with exactly one white neighbor forces that neighbor black}.
$$

Write $Z(G)$ for the least size of an initial black set that colors every vertex. Let $\mathcal S(G)$ be the real symmetric $N\times N$ matrices $A$ such that, for distinct $u,v\in V$,

$$
A_{uv}\ne0\quad\Longleftrightarrow\quad uv\in E(G).
$$

Set

$$
M_{\mathbb R}(G)=\max_{A\in\mathcal S(G)}\dim\ker A,
\qquad
mr_{\mathbb R}(G)=\min_{A\in\mathcal S(G)}\operatorname{rank}A.
$$

## 2. A common $k$-dimensional recurrence

**定义 2.1（sliding-window space）。** Let $W_k$ be the real vector space of one-sided sequences $x=(x_d)_{d\ge1}$ satisfying

$$
\sum_{t=0}^{k}x_{s+t}=0\qquad(s\ge1).
\tag{2.1}
$$

For $L\ge k+1$, let $D_L$ be the $(L-k)\times L$ matrix

$$
(D_L)_{s,d}=\begin{cases}
1,&s\le d\le s+k,\\
0,&\text{otherwise},
\end{cases}
\qquad 1\le s\le L-k,\quad 1\le d\le L.
\tag{2.2}
$$

**引理 2.2（window kernel and band support）。** The initial values $x_1,\ldots,x_k$ determine a unique member of $W_k$ by

$$
x_{s+k}=-\sum_{t=0}^{k-1}x_{s+t}\qquad(s\ge1).
$$

Consequently $\dim W_k=k$. Every truncation $(x_1,\ldots,x_L)^{\mathsf T}$ lies in $\ker D_L$, and, for $d\ne e$,

$$
(D_L^{\mathsf T}D_L)_{d,e}>0
\quad\Longleftrightarrow\quad
|d-e|\le k.
\tag{2.3}
$$

**证明。** The displayed recursion constructs and uniquely determines all later terms, so evaluation on the first $k$ coordinates is a linear isomorphism $W_k\cong\mathbb R^k$. Equation (2.1) is exactly $D_Lx=0$ after truncation. For $d<e$, the $(d,e)$ entry of $D_L^{\mathsf T}D_L$ counts window starts $s$ for which one window contains both positions. Such a start exists when $e-d\le k$: the interval

$$
[\max(1,e-k),\ \min(d,L-k)]
$$

of possible starts is then nonempty because $1\le d<e\le L$. If $e-d>k$, no window contains both positions. Every contributing summand is $1$, so the count is positive, proving (2.3); symmetry handles $d>e$. $\square$

## 3. The independent-length theorem

**定理 3.1（unequal-leg spider powers）。** For every choice of $m,k,\ell_1,\ldots,\ell_m$ in Definition 1.1, put

$$
q=(m-1)k.
$$

Then

$$
Z(G)=M_{\mathbb R}(G)=q,
\qquad
mr_{\mathbb R}(G)=N-q.
\tag{3.1}
$$

Moreover, the proof gives one explicit real symmetric matrix $A\in\mathcal S(G)$ with $\dim\ker A=q$.

**证明。** We first give the forcing set. Let

$$
S=\{(i,d):1\le i\le m-1,\ \ell_i-k+1\le d\le \ell_i\}.
\tag{3.2}
$$

It has $|S|=(m-1)k=q$. On each of the first $m-1$ legs, force in the order

$$
(i,t+k)\longrightarrow(i,t)
\qquad(t=\ell_i-k,\ell_i-k-1,\ldots,1).
\tag{3.3}
$$

At the indicated step all depths greater than $t$ on that leg are black. The source has no neighbor on another leg, since $(t+k)+e>k$ for every $e\ge1$, and it has no center neighbor. Its same-leg neighbors have depths between $t$ and $t+2k$; hence the only white neighbor is $(i,t)$.

After these legs are black, $(1,k)$ forces the center: its same-leg neighbors are black and it has no other-leg neighbor, while $\delta((1,k),c)=k$. On the last leg, for $j=1,\ldots,k-1$, use

$$
(1,k-j)\longrightarrow(m,j).
\tag{3.4}
$$

The source and the center are black, every other leg is black, and its last-leg neighbors have depths $e\le j$; the depths $e<j$ have already been forced. Thus $(m,j)$ is its unique white neighbor. (When $k=1$, this middle list is empty.) The center then forces $(m,k)$, because its last-leg neighbors have depths at most $k$ and the first $k-1$ are black. Finally, for $t=k+1,\ldots,\ell_m$, use

$$
(m,t-k)\longrightarrow(m,t).
\tag{3.5}
$$

All depths below $t$ are black, and the source has no same-leg neighbor deeper than $t$; any center or other-leg neighbors are among those already black vertices. Therefore (3.5) is legal. This proves $Z(G)\le q$.

We now construct the symmetric matrix. Put $r=k-1$ and define, for positive integers $d,e$,

$$
C_{d,e}=\begin{cases}
1,&d\le r,\ e\le r,\ d+e\le k,\\
0,&\text{otherwise},
\end{cases}
\qquad
b_d=\begin{cases}1,&d\le k,\\0,&d>k.\end{cases}
\tag{3.6}
$$

Thus $C$ is empty when $k=1$, and in all cases $C_{d,e}=1$ exactly for the possible cross-leg edges at depths $d,e$. For each leg $i$, let $D_i=D_{\ell_i}$ and define the symmetric $\ell_i\times\ell_i$ matrix

$$
B_i(d,e)=(D_i^{\mathsf T}D_i)_{d,e}+C_{d,e}
\qquad(1\le d,e\le\ell_i).
\tag{3.7}
$$

Define $A$ on $V$ by

$$
\begin{aligned}
A_{c,c}&=0,\\
A_{c,(i,d)}=A_{(i,d),c}&=b_d,\\
A_{(i,d),(i,e)}&=B_i(d,e),\\
A_{(i,d),(j,e)}&=C_{d,e}\qquad(i\ne j).
\end{aligned}
\tag{3.8}
$$

All entries are real and $A$ is symmetric. By (2.3), the same-leg off-diagonal entry in (3.8) is positive exactly when $0<|d-e|\le k$, because the added $C_{d,e}$ is nonnegative and is itself supported within that band. For distinct legs, (3.6) gives a nonzero entry exactly when $d+e\le k$, and the center entries are nonzero exactly when $d\le k$. These are precisely the three cases $\delta\le k$ in Definition 1.1. Thus $A\in\mathcal S(G)$.

Let

$$
U=\left\{(x^{(1)},\ldots,x^{(m)})\in W_k^m:
\sum_{i=1}^m x^{(i)}=0\text{ as one-sided sequences}\right\}.
\tag{3.9}
$$

The sum map $W_k^m\to W_k$ is onto, so $\dim U=(m-1)k=q$. For $x\in U$, define a vector $z_x\in\mathbb R^V$ by

$$
z_x(c)=0,
\qquad z_x(i,d)=x^{(i)}_d.
\tag{3.10}
$$

At the center row, (3.8) gives

$$
(Az_x)(c)=\sum_{d=1}^{k}b_d\sum_{i=1}^m x^{(i)}_d=0.
$$

At a leg row $(i,d)$, the $D_i^{\mathsf T}D_i$ part vanishes because $D_i x^{(i)}=0$. The remaining $C$-part is

$$
\sum_{e}C_{d,e}x^{(i)}_e+\sum_{j\ne i}\sum_e C_{d,e}x^{(j)}_e
=\sum_e C_{d,e}\sum_{j=1}^m x^{(j)}_e=0.
$$

Hence $Az_x=0$. The map $x\mapsto z_x$ is injective, since every leg coordinate of each sequence is retained; therefore $\dim\ker A\ge q$.

For completeness, the standard zero-forcing kernel restriction gives the opposite inequality for every $H\in\mathcal S(G)$. If a vector $y\in\ker H$ vanishes on an initial black set, then it vanishes at every later black vertex by induction. Indeed, when a black $u$ forces its unique white neighbor $w$, the $u$-row equation has the form

$$
0=\sum_v H_{u,v}y_v=H_{u,w}y_w,
$$

because $y_u=0$, all other neighbors of $u$ are already black, and nonneighbors have zero matrix entries. Exact support gives $H_{u,w}\ne0$, so $y_w=0$. Restriction to the initial set is consequently injective on $\ker H$, and

$$
\dim\ker H\le |S|=q.
\tag{3.11}
$$

Applying (3.11) to the matrix $A$ and combining it with the forcing construction yields

$$
q\le\dim\ker A\le Z(G)\le q.
$$

Thus $\dim\ker A=Z(G)=q$. Equation (3.11) for all $H\in\mathcal S(G)$ gives $M_{\mathbb R}(G)=q$, and rank-nullity gives $mr_{\mathbb R}(G)=N-q$. $\square$

## 4. Boundary and source correspondence

The construction uses ordinary powers, with a black source required at every force. It remains valid when some or all legs have the boundary length $k+1$; it also includes $m=2$ and $k=1$. For $k=1$, $C$ is empty and the recurrence consists of consecutive two-term windows, while (3.8) still has the exact tree support. No strict-distance power, positive-semidefinite requirement, multiple-center extension, or equal-length restriction is used.

The equal-leg statement in Abiad, Flagg, Ghasemi Nezhad and Zeijlemaker, *The Zero Forcing Number of Graph Powers*, arXiv:2610.03892v1, §3, Proposition 9 and Conjecture 10, is the supplied equal-length case. The repository source `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing` and its problem record `Problems/abiad-equal-legged-spider-power-zero-forcing.md` correspond to that case and its nonsymmetric matrix argument; they are used here as the original source correspondence, while (3.6)--(3.10) give the independent-length symmetric construction. The row-kernel restriction argument is the classical propagation lemma in Alon, *A propagation process on Cayley graphs*, Theorem 2.1. Path-power and tree-power minimum-rank facts are classical intermediate supplies in DeAlba et al., *Minimum rank of powers of trees*, ELA 23 (2012), DOI 10.13001/1081-3810.1511; no separate equal-leg, path, or tree theorem is asserted here.

The theorem settles the stated independently varying-length family. It makes no claim about hypotheses outside Definition 1.1 or about a broader external mixed-length problem.

## 追加锚（本行以下为增补区）
