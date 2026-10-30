# Adjacency average-mixing trace: bipartite extremum and rank separation

## 1. Graphs, spectral weights and comparison domains

**Definition 1.1 (Adjacency average-mixing trace).** Let $G=(V,E)$ be a finite simple undirected unweighted graph, let $n=|V|$, and let $A=A(G)$ be its real adjacency matrix. Write

$$
A=\sum_{\theta\in\operatorname{spec}(A)}\theta E_\theta,
\qquad
\widehat M_A(G)=\sum_{\theta\in\operatorname{spec}(A)}E_\theta\circ E_\theta,
\qquad
T_A(G)=\operatorname{tr}\widehat M_A(G)
      =\sum_{v\in V}\sum_{\theta\in\operatorname{spec}(A)}(E_\theta)_{vv}^{,2}.
\tag{1.1}
$$

Here the spectrum indexes distinct eigenvalues, $E_\theta$ is the orthogonal projection onto the entire $\theta$-eigenspace, and $\circ$ is the entrywise product. In particular, a repeated eigenvalue contributes one projection, rather than separate summands for an eigenbasis. Set $E_0=0$ when zero is not an eigenvalue.

The spectral expression (1.1) is the classical average-mixing formula: see Godsil–Guo–Sobchuk, *Diagonal entries of the average mixing matrix*, [arXiv:1910.02039v1, §2](https://arxiv.org/html/1910.02039v1#S2), and Coutinho–Godsil, *Graph Spectra and Continuous Quantum Walks*, [Theorem 15.1.1](https://www.math.uwaterloo.ca/~cgodsil/quagmire/QuantumWalks/pdfs/GrfSpc3.pdf). Indeed, with $U(t)=\exp(itA)$, expansion in the spectral projections gives

$$
U(t)\circ\overline{U(t)}
 =\sum_{\theta,\phi}e^{it(\theta-\phi)}E_\theta\circ E_\phi.
$$

The time average of $e^{it(\theta-\phi)}$ over $[0,R]$ tends to zero for $\theta\ne\phi$ and equals one for $\theta=\phi$. The sum is finite, so (1.1) is precisely the Cesàro average of the original adjacency walk.

**Definition 1.2 (Bipartition and support projection).** For a bipartite graph with nonempty parts $X,Y$, put $p=|X|$, $q=|Y|$, and write

$$
A=\begin{pmatrix}0&B\\ B^{\mathsf T}&0\end{pmatrix},
\qquad
J=\begin{pmatrix}I_p&0\\0&-I_q\end{pmatrix},
\qquad
r=\operatorname{rank}B,
\qquad
S=I-E_0,
\qquad s_v=S_{vv}.
\tag{1.2}
$$

The matrix $B$ is the binary biadjacency matrix. The projection $S$ is onto $\operatorname{im}A$. For a connected graph of order at least two, $B$ has no zero row or zero column and $r\ge1$. All ranks are over $\mathbb R$.

**Definition 1.3 (Independent vertex classes).** Replacing each vertex $i$ of a path $P_k$ by a nonempty independent set $C_i$ of size $t_i$, and replacing each edge $i(i+1)$ by all edges between $C_i$ and $C_{i+1}$, gives an independent blow-up of $P_k$. Vertices in the same $C_i$ have the same open neighborhood. Coalescing equal rows and equal columns of a biadjacency matrix means retaining one representative of each distinct row and column; the class sizes remain attached to those representatives.

**Definition 1.4 (The star comparison).** Write $S_n=K_{1,n-1}$ for $n\ge2$. The adjacency part of Mohan–Tamon–Xu–Zhan, *Laziness of Quantum Walks on Graphs*, [arXiv:2608.20739v1, §8(v)](https://arxiv.org/html/2608.20739v1#S8), asks whether $S_n$ is the second laziest connected graph, with laziness measured by $T_A$. Its comparison domain is the connected noncomplete graphs of order $n$. The bipartite subdomain consists of every connected bipartite graph of order $n\ge3$; at order two its only graph is $K_2=S_2$.

For comparison, the unsigned Laplacian and normalized Laplacian use the Hamiltonians $D+A$ and $I-D^{-1/2}AD^{-1/2}$, where $D$ is the degree matrix. These are separate spectral observables from (1.1).

## 2. Separation when the adjacency rank is at least four

**Theorem 2.1 (Strict rank separation).** For every finite connected simple undirected unweighted bipartite graph $G$ of order $n\ge2$, if $\operatorname{rank}A(G)\ge4$, then

$$
T_A(G)<n-\frac52.
\tag{2.1}
$$

**Proof.** Use Definition 1.2. The kernel of $A$ is $\ker B^{\mathsf T}\oplus\ker B$, so

$$
\operatorname{rank}A=2r,
\qquad
S=\begin{pmatrix}P&0\\0&Q\end{pmatrix},
\tag{2.2}
$$

where $P$ projects onto $\operatorname{im}B$ and $Q$ onto $\operatorname{im}B^{\mathsf T}$. Consequently

$$
0\le s_v\le1,
\qquad
\sum_{v\in X}s_v=\sum_{v\in Y}s_v=r.
\tag{2.3}
$$

The identity $JAJ=-A$ sends the entire $\theta$-eigenspace isometrically onto the entire $-\theta$-eigenspace. Hence $E_{-\theta}=JE_\theta J$, including all multiplicities, and their diagonal entries agree. Orthogonal projections are positive semidefinite, so these entries are nonnegative. Summing the paired nonzero projections gives, at each vertex,

$$
\sum_{\theta>0}(E_\theta)_{vv}=\frac{s_v}{2},
\qquad
\sum_{\theta\ne0}(E_\theta)_{vv}^{,2}
 =2\sum_{\theta>0}(E_\theta)_{vv}^{,2}
 \le2\left(\sum_{\theta>0}(E_\theta)_{vv}\right)^2
 =\frac{s_v^2}{2}.
\tag{2.4}
$$

Only distinct positive eigenvalues are summed. Since $(E_0)_{vv}=1-s_v$, the diagonal deficit $d_v=1-(\widehat M_A)_{vv}$ therefore satisfies

$$
d_v\ge 2s_v-\frac32s_v^2\ge\frac12s_v.
\tag{2.5}
$$

By (2.3), this yields

$$
n-T_A(G)=\sum_vd_v\ge r.
\tag{2.6}
$$

If $r\ge3$, (2.6) gives $T_A(G)\le n-3<n-5/2$. It remains to treat $r=2$.

First determine the possible equal-neighborhood classes directly from the binary matrix $B$. Choose independent rows $u,w$. Divide the columns into their three possible nonzero types relative to these rows:

$$
X_0=\{j:(u_j,w_j)=(1,0)\},\qquad
Y_0=\{j:(u_j,w_j)=(0,1)\},\qquad
Z_0=\{j:(u_j,w_j)=(1,1)\}.
\tag{2.7}
$$

A column with $(u_j,w_j)=(0,0)$ would vanish on every row, since every row is in the span of $u,w$; it is excluded by connectivity. Independence ensures that at least two of $X_0,Y_0,Z_0$ are nonempty. Any row has the form $\alpha u+\beta w$, with values $\alpha,\beta,\alpha+\beta$ on the respective nonempty sets in (2.7), and each such value must be zero or one. No row is zero.

If all three sets are nonempty, the only possibilities are $u,w$: the pair $(\alpha,\beta)=(1,1)$ is forbidden by $Z_0$. Coalescing the columns gives types $(1,0),(0,1),(1,1)$, which form a path on five vertices.

If $X_0,Y_0$ are nonempty and $Z_0$ is empty, the possible rows are $u,w,u+w$. The row $u+w$ must occur, since otherwise the graph splits into the two nonempty components supported on $X_0$ and $Y_0$. After coalescence the two column types join the third row to each of the first two, again giving a path on five vertices.

If $X_0,Z_0$ are nonempty and $Y_0$ is empty, the possible nonzero pairs $(\alpha,\alpha+\beta)$ are $(1,1),(0,1),(1,0)$. Thus the possible rows are $u,w,u-w$. If $u-w$ is absent, the two row types and two column types give a path on four vertices; if it is present, they give a path on five vertices. Interchanging $u,w$ treats the remaining case $Y_0,Z_0\ne\varnothing$, $X_0=\varnothing$.

This exhausts the possibilities. Coalescing rows cannot create new distinctions between columns, and conversely, so the resulting graph is exactly $P_4$ or $P_5$. Thus $G$ is an independent blow-up of one of these two paths. This elementary classification is used only as an intermediate step in the trace estimate.

For either path let

$$
f_i=\frac{\mathbf 1_{C_i}}{\sqrt{t_i}},\qquad
W=\operatorname{span}\{f_1,\ldots,f_k\}.
\tag{2.8}
$$

The $f_i$ are orthonormal. The matrix $A$ kills $W^\perp$, since a vector in $W^\perp$ sums to zero on every class. Its matrix on $W$ is the symmetric weighted path matrix $H$ with

$$
H_{i,i+1}=H_{i+1,i}=\sqrt{t_it_{i+1}},
\qquad H_{ij}=0\quad\text{otherwise}.
\tag{2.9}
$$

These conclusions follow by multiplying $A$ by each $f_i$; no eigenspace-refinement assertion for general equitable partitions is needed.

Suppose first that $k=4$. The determinant of $H$ is $(t_1t_2)(t_3t_4)>0$, so $\operatorname{im}A=W$. Therefore $s_v=1/t_i$ for $v\in C_i$. Summing the first inequality in (2.5) gives

$$
n-T_A(G)\ge\sum_{i=1}^4\left(2-\frac{3}{2t_i}\right)
 =8-\frac32\sum_{i=1}^4\frac1{t_i}.
\tag{2.10}
$$

If any $t_i\ge2$, then $\sum_i1/t_i\le7/2$, and (2.10) is at least $11/4>5/2$.

The only remaining four-class case has every $t_i=1$, hence $G=P_4$. Here its two-by-two biadjacency matrix can be taken as

$$
B=\begin{pmatrix}1&0\\1&1\end{pmatrix},
\quad
BB^{\mathsf T}=\begin{pmatrix}1&1\\1&2\end{pmatrix},
\quad
B^{\mathsf T}B=\begin{pmatrix}2&1\\1&1\end{pmatrix}.
\tag{2.11}
$$

The two squared singular values are $\mu_\pm=(3\pm\sqrt5)/2$. For either of the last two matrices $C$, the projections are $(C-\mu_\mp I)/(\mu_\pm-\mu_\mp)$. At each coordinate their diagonal entries are $(1+1/\sqrt5)/2$ and $(1-1/\sqrt5)/2$, in some order. The $\pm\sqrt{\mu_\pm}$ adjacency projections have half these entries on the corresponding part: this follows from the normalized adjacency eigenvectors $(x,\pm B^{\mathsf T}x/\sqrt\mu)/\sqrt2$ for a unit $\mu$-eigenvector $x$ of $BB^{\mathsf T}$. There is no zero eigenspace. Each vertex consequently contributes

$$
\frac12\left[\left(\frac{1+1/\sqrt5}{2}\right)^2
                  +\left(\frac{1-1/\sqrt5}{2}\right)^2\right]
 =\frac3{10},
\qquad T_A(P_4)=\frac65<\frac32.
\tag{2.12}
$$

This is an explicit specialization of the classical spectral/path formulas, not an additional path theorem.

Finally suppose that $k=5$, and write the class sizes in path order as $(a,b,c,d,e)$. The odd classes lie in one bipartition part. On their normalized coordinates the column space of $B$ is spanned by

$$
(\sqrt a,\sqrt c,0)^{\mathsf T},
\qquad (0,\sqrt c,\sqrt e)^{\mathsf T};
\tag{2.13}
$$

multipliers $\sqrt b,\sqrt d$ do not change this span. Its unit perpendicular vector is

$$
z=\frac{(\sqrt{ce},-\sqrt{ae},\sqrt{ac})^{\mathsf T}}{\sqrt L},
\qquad L=ac+ae+ce.
\tag{2.14}
$$

Projecting onto the span in (2.13), and then converting from normalized class coordinates back to vertices, gives

$$
s_v=
\begin{cases}
(c+e)/L,&v\in C_1,\\
(a+e)/L,&v\in C_3,\\
(a+c)/L,&v\in C_5.
\end{cases}
\tag{2.15}
$$

For example $(1-z_1^2)/a=(L-ce)/(aL)=(c+e)/L$. Because all class sizes are positive integers,

$$
L=a(c+e)+ce\ge c+e+ce\ge\frac32(c+e),
\tag{2.16}
$$

where $2ce\ge c+e$ follows from $(c-1)e+(e-1)c\ge0$. The cyclic versions of (2.16) give $s_v\le2/3$ at every vertex in the odd classes. Their $s_v$ sum is two by (2.3), so (2.5) gives a total deficit at least

$$
\sum_{v\in C_1\cup C_3\cup C_5}
       \left(2-\frac32s_v\right)s_v
 \ge\sum_{v\in C_1\cup C_3\cup C_5}s_v=2.
\tag{2.17}
$$

On the other part $s_v\le1$ and the sum is again two. Its deficit is at least one by the second inequality in (2.5). Thus $n-T_A(G)\ge3>5/2$ for every five-class case. Together with (2.6), (2.10) and (2.12), this proves (2.1) for every possible rank and order under its hypotheses. $\square$

## 3. The extremum, all equalities and the nonstar gap

**Theorem 3.1 (Exact bipartite maximum and separation).** For every finite connected simple undirected unweighted bipartite graph $G$ of order $n\ge2$, with the observable (1.1),

$$
T_A(G)\le n-\frac52+\frac{3}{2(n-1)},
\tag{3.1}
$$

with equality if and only if $G\cong K_{1,n-1}$.

If $G$ is a nonstar, then necessarily $n\ge4$, and

$$
T_A(G)\le n-\frac52,
\tag{3.2}
$$

with equality if and only if $n=4$ and $G\cong C_4$. In particular, every such nonstar satisfies

$$
T_A(K_{1,n-1})-T_A(G)\ge\frac{3}{2(n-1)},
\tag{3.3}
$$

with equality if and only if $G\cong C_4$.

**Proof.** Connectivity gives $r\ge1$ in Definition 1.2. If $r\ge2$, Theorem 2.1 gives the strict form of (3.2). In particular (3.1) is then strict, since $3/[2(n-1)]>0$.

Suppose $r=1$. Every row of $B$ is a nonzero scalar multiple of a chosen nonzero binary row. At a position where that row equals one, another nonzero binary row must also equal one; its scalar is therefore one. All rows coincide. No column is zero, so that common row is all ones. Thus $B=\mathbf1_p\mathbf1_q^{\mathsf T}$ and $G=K_{p,q}$, with $p,q\ge1$, $p+q=n$.

For clarity the exact trace of this family follows directly from the cited spectral formula (1.1). The two nonzero eigenvalues are $\pm\sqrt{pq}$, with respective unit eigenvectors

$$
u_+=\frac1{\sqrt2}
       \begin{pmatrix}\mathbf1_p/\sqrt p\\\mathbf1_q/\sqrt q\end{pmatrix},
\qquad
u_-=\frac1{\sqrt2}
       \begin{pmatrix}\mathbf1_p/\sqrt p\\-\mathbf1_q/\sqrt q\end{pmatrix}.
\tag{3.4}
$$

Hence $(E_\pm)_{vv}=1/(2p)$ on $X$ and $1/(2q)$ on $Y$, while

$$
E_0=\operatorname{diag}\left(I_p-\frac1p\mathbf1_p\mathbf1_p^{\mathsf T},
                           I_q-\frac1q\mathbf1_q\mathbf1_q^{\mathsf T}\right).
\tag{3.5}
$$

Formula (3.5) includes its zero blocks when $p=1$ or $q=1$, and it vanishes entirely when $p=q=1$. There is therefore no exceptional multiplicity case in the calculation

$$
\begin{aligned}
T_A(K_{p,q})
 &=p\left[\left(1-\frac1p\right)^2+\frac1{2p^2}\right]
  +q\left[\left(1-\frac1q\right)^2+\frac1{2q^2}\right]\\
 &=n-4+\frac32\left(\frac1p+\frac1q\right).
\end{aligned}
\tag{3.6}
$$

In particular the star trace is the published value of Godsil–Guo–Sinkovic, *Average mixing matrix of trees*, Electronic Journal of Linear Algebra **34**, 269–282, [DOI:10.13001/1081-3810.3746, Lemma 2.2](https://journals.uwyo.edu/index.php/ela/article/download/1877/1877): for $K_{1,m}$ it is $(2m^2-3m+3)/(2m)$. With $m=n-1$, this equals

$$
T_A(K_{1,n-1})=n-\frac52+\frac{3}{2(n-1)}.
\tag{3.7}
$$

Only the trace formula from that lemma is used; no assertion about the rank of a star's average mixing matrix enters the proof.

If one of $p,q$ equals one, $G$ is a star and (3.7) gives equality in (3.1). Otherwise $p,q\ge2$, so $n\ge4$ and

$$
\frac1p+\frac1q\le\frac12+\frac12=1,
\tag{3.8}
$$

with equality exactly when $p=q=2$. By (3.6), these nonstar rank-two graphs satisfy (3.2), with equality exactly at $K_{2,2}\cong C_4$. All ranks at least four have strict inequality by Theorem 2.1. This proves (3.2) and its full equality classification, and also excludes every nonstar from equality in (3.1).

At order two connectivity forces the single edge $K_2=K_{1,1}$, for which (3.6) gives $T_A=1$; the right side of (3.1) is one. At order three a connected bipartite graph has part sizes one and two and is $K_{1,2}$, for which $T_A=5/4$ by (3.6). Thus every nonstar does indeed have order at least four, and every smaller order in the stated domain has been included.

Finally subtract (3.2) from (3.7) to obtain (3.3). Equality in the subtraction is equivalent to equality in (3.2), already classified as $C_4$. Its trace is $3/2$, the order-four star trace is two, and their difference is $1/2=3/[2(4-1)]$. $\square$

## 4. Exact comparison domain and remaining extremal quantities

**Definition 4.1 (Extremal quantities beyond the star comparison).** For $n\ge4$, let $\mathcal B_n$ be the connected simple undirected unweighted bipartite nonstar graphs of order $n$, and define

$$
\beta_n=\max_{G\in\mathcal B_n}T_A(G).
\tag{4.1}
$$

The set is finite up to isomorphism and nonempty, since it contains $P_n$. Theorem 3.1 gives $\beta_4=3/2$, uniquely at $C_4$, and $\beta_n<n-5/2$ for each $n\ge5$. The latter strict bound does not specify the value of $\beta_n$.

For $n\ge4$, let $\mathcal N_n$ be the connected nonbipartite noncomplete graphs of order $n$. The additional adjacency comparison required outside the bipartite subdomain of [Mohan–Tamon–Xu–Zhan, §8(v)](https://arxiv.org/html/2608.20739v1#S8) is

$$
T_A(G)\le T_A(K_{1,n-1})\quad(G\in\mathcal N_n).
\tag{4.2}
$$

The complete-graph maximum is a separate supplied comparison, $T_A(G)\le T_A(K_n)=n-2+2/n$, as in [the repository's complete-graph result](../../../D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.lean) and its [mathematical exposition](../../../Blueprint/D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.md). Its spectral and complete-graph inputs are attributed in that exposition to Godsil–Guo–Sobchuk; the same maximum and its equality analysis are discussed by Kang, *On Entries of Spectral Decompositions and Applications*, [arXiv:2610.27498v1, §3](https://arxiv.org/html/2610.27498v1#S3). Neither that supplied comparison nor (3.1) is a bound for all of $\mathcal N_n$ by the star value.

The results here establish the star comparison for the entire bipartite adjacency subdomain. Determining $\beta_n$ for $n\ge5$, establishing (4.2), and obtaining the corresponding extremal comparisons for the two different Laplacian Hamiltonians in Definition 1.4 are distinct additional mathematical problems.

## 追加锚（本行以下为增补区）
