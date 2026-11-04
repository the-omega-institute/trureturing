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

## 5. Strict star comparison for the whole pineapple family

For integers $m\ge2$ and $b\ge1$, put

$$
G(m,b)=K_1\vee(K_m\sqcup bK_1),\qquad n=m+b+1.
\tag{5.1}
$$

Here $\vee$ is the graph join: a hub $h$ is adjacent to every vertex of a clique $C$ of size $m$ and an independent set $L$ of size $b$, and there are no edges between $C$ and $L$. These graphs are finite, simple, undirected, unweighted, connected, nonbipartite and noncomplete: the hub and two clique vertices form a triangle, whereas a leaf and a clique vertex are nonadjacent. They are the pineapple graphs $K_p^q$ with $p=m+1$, $q=b$ in Topcu–Sorgun–Haemers, *On the spectral characterization of pineapple graphs*, [arXiv:1511.08674v3, Proposition 1.1](https://arxiv.org/abs/1511.08674v3).

Use the adjacency observable (1.1),

$$
T_A(G)=\sum_{v\in V(G)}\sum_{\theta\in\operatorname{spec}(A(G))}(E_\theta)_{vv}^{\,2},
\tag{5.2}
$$

where distinct eigenvalues index projections onto entire eigenspaces; there is no division by $n$.

**Theorem 5.1 (Strict pineapple comparison).** For every pair of integers $m\ge2$, $b\ge1$, with $n=m+b+1$,

$$
T_A(G(m,b))<T_A(K_{1,n-1})
             =n-\frac52+\frac{3}{2(n-1)}.
\tag{5.3}
$$

There is no equality in this parameter domain.

**Proof.** The spectral formula (1.1) and the same-order star value (3.7) are the supplied inputs. Set $d=m-1>0$ and $M=m+b=n-1$. The characteristic polynomial below is the polynomial in the cited Proposition 1.1 under $p=m+1$, $q=b$; the direct orthogonal decomposition is also needed to determine the spectral weights.

Let $U_C$ consist of the vectors supported on $C$ whose coordinates sum to zero, and define $U_L$ similarly. Then $A$ acts as $-I$ on $U_C$ and as zero on $U_L$. Their orthogonal complement $W$ has orthonormal basis

$$
e_h,\qquad \frac{\mathbf1_C}{\sqrt m},\qquad
\frac{\mathbf1_L}{\sqrt b}.
$$

Multiplication by $A$ shows that $W$ is invariant and that its restriction is

$$
H=\begin{pmatrix}
0&\sqrt m&\sqrt b\\
\sqrt m&d&0\\
\sqrt b&0&0
\end{pmatrix},\qquad
f(x)=\det(xI-H)=x^3-dx^2-Mx+bd.
\tag{5.4}
$$

The values $f(0)=bd$, $f(d)=-md$ and $f(-1)=bm$ are nonzero. For an eigenvector $(u,v,w)$ of $H$ with eigenvalue $\lambda$, the second and third equations give

$$
v=\frac{\sqrt m}{\lambda-d}u,\qquad
w=\frac{\sqrt b}{\lambda}u.
\tag{5.5}
$$

Thus $u=0$ forces the vector to vanish, and each eigenspace has dimension one. Since $H$ is real symmetric, its three eigenvalues $\lambda_1,\lambda_2,\lambda_3$ are real and distinct. None equals $0$ or $-1$. Consequently the full $-1$-projection of $A$ is the projection onto $U_C$, with diagonal $1-1/m$ on $C$, and the full zero-projection is the projection onto $U_L$, with diagonal $1-1/b$ on $L$. When $b=1$, $U_L=0$ and zero is absent from the spectrum; the same formula contributes zero. All other projections are the lifts of the three rank-one projections $P_r$ of $H$.

Define the symmetric matrix

$$
F_{ij}=\sum_{r=1}^3(P_r)_{ij}^{\,2}\quad(1\le i,j\le3).
$$

Its entries are nonnegative and its row sums equal one, because

$$
\sum_jF_{ij}=\sum_r(P_r^2)_{ii}=\sum_r(P_r)_{ii}=1.
\tag{5.6}
$$

On a clique vertex the lifted $P_r$ has diagonal $(P_r)_{22}/m$, and on a leaf it has diagonal $(P_r)_{33}/b$. Accounting for the two full repeated-eigenvalue projections therefore gives

$$
\begin{aligned}
T_A(G(m,b))
 &=m\left(1-\frac1m\right)^2
   +b\left(1-\frac1b\right)^2
   +F_{11}+\frac{F_{22}}m+\frac{F_{33}}b\\
 &=n-5+\frac1m+\frac1b
   +F_{11}+\frac{F_{22}}m+\frac{F_{33}}b\\
 &=n-4+\frac2m+\frac2b-R,
\end{aligned}
\tag{5.7}
$$

where the last equality uses (5.6) and

$$
R=\left(1+\frac1m\right)F_{12}
 +\left(1+\frac1b\right)F_{13}
 +\left(\frac1m+\frac1b\right)F_{23}\ge0.
\tag{5.8}
$$

In particular, if $g(m,b)$ denotes the star trace minus the pineapple trace, then

$$
g(m,b)=\frac32+\frac{3}{2M}-\frac2m-\frac2b+R.
\tag{5.9}
$$

First suppose $b\ge2$. If $m,b\ge3$, the part of (5.9) preceding $R$ is at least $1/6+3/(2M)>0$. If one parameter is two and the other is $k\ge3$, that part is

$$
\frac12+\frac{3}{2(k+2)}-\frac2k.
\tag{5.10}
$$

For $k=3$ this is $2/15>0$, and for $k\ge4$ it is positive because $1/2-2/k\ge0$. Thus (5.8) proves all cases with $b\ge2$ except $(m,b)=(2,2)$.

It remains to evaluate (5.8) for that pair and for the entire strip $b=1$. The following calculation is a specialization of the root-deleted-polynomial cancellation described in [the discriminant exposition](../../../Blueprint/D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.md). Put

$$
\Delta=\prod_{r<s}(\lambda_r-\lambda_s)^2>0,\qquad
S_j=\sum_{r=1}^3\frac{\lambda_r^j}{f'(\lambda_r)^2}
\quad(j=0,1,2).
\tag{5.11}
$$

The projector identity $P_r=\operatorname{adj}(\lambda_r I-H)/f'(\lambda_r)$ follows by writing

$$
\operatorname{adj}(xI-H)
 =\sum_r\left(\prod_{s\ne r}(x-\lambda_s)\right)P_r
$$

for $x$ outside the spectrum and then evaluating the polynomial identity at $x=\lambda_r$. The off-diagonal cofactors of $xI-H$ are respectively $\sqrt m\,x$, $\sqrt b\,(x-d)$ and $\sqrt{mb}$. Hence

$$
F_{12}=mS_2,\qquad
F_{13}=b(S_2-2dS_1+d^2S_0),\qquad
F_{23}=mbS_0.
\tag{5.12}
$$

For $\{r,s,t\}=\{1,2,3\}$, cancellation of the two squared factors in $f'(\lambda_r)^2$ gives

$$
\frac{\Delta}{f'(\lambda_r)^2}
 =(\lambda_s-\lambda_t)^2
 =(d-\lambda_r)^2-4(-M-d\lambda_r+\lambda_r^2)
 =d^2+4M+2d\lambda_r-3\lambda_r^2.
\tag{5.13}
$$

Here Vieta gives $\lambda_s+\lambda_t=d-\lambda_r$ and $\lambda_s\lambda_t=-M-d\lambda_r+\lambda_r^2$. The power sums $p_j=\sum_r\lambda_r^j$ are

$$
\begin{aligned}
p_0&=3,&p_1&=d,&p_2&=d^2+2M,\\
p_3&=d^3+3dM-3bd,&
p_4&=d^4+4d^2M+2M^2-4bd^2.
\end{aligned}
\tag{5.14}
$$

Indeed $p_2$ follows from Vieta, and $f(\lambda_r)=0$ gives $p_3=dp_2+Mp_1-bdp_0$ and $p_4=dp_3+Mp_2-bdp_1$. Multiplying (5.13) by $\lambda_r^j$ and summing now yields

$$
\begin{aligned}
\Delta S_0&=2(d^2+3M),\\
\Delta S_1&=d(9b-M),\\
\Delta S_2&=2(M^2+3bd^2).
\end{aligned}
\tag{5.15}
$$

Substitution into (5.8) and (5.12) gives the explicit identity

$$
R=\frac{2\left[(M+5)M^2+(b+1)d^4
                   +(7mb+5m+2b-2b^2)d^2\right]}{\Delta}.
\tag{5.16}
$$

For example, before collecting coefficients its numerator divided by two is

$$
(m+1)(M^2+3bd^2)
 +(b+1)\left[M^2+d^4+(4m-2b)d^2\right]
 +M(d^2+3M),
$$

which expands to the numerator in brackets in (5.16). Expanding the root-difference product in (5.11), or the cubic discriminant, gives

$$
\Delta=d^2M^2+4M^3+4bd^4-27b^2d^2+18bMd^2.
\tag{5.17}
$$

In detail, for a monic cubic $x^3+ax^2+cx+e$ the root-difference product is $a^2c^2-4c^3-4a^3e-27e^2+18ace$; taking $a=-d$, $c=-M$, $e=bd$ gives (5.17).

At $(m,b)=(2,2)$ we have $d=1$, $M=4$, so (5.17) gives $\Delta=16+256+8-108+144=316$. The numerator in (5.16) is $2(144+3+34)=362$. Thus $R=181/158$, and (5.9) gives

$$
g(2,2)=-\frac18+\frac{181}{158}
       =\frac{645}{632}>0.
\tag{5.18}
$$

Finally let $b=1$ and keep every integer $m\ge2$. Equations (5.16)–(5.17), with $d=m-1$ and $M=m+1$, become

$$
\begin{aligned}
\Delta&=mD,\qquad D=5m^3+6m^2-11m+32>0,\\
R&=\frac{N}{mD},\qquad
N=4m^4+10m^3-8m^2+34m+16.
\end{aligned}
\tag{5.19}
$$

The sign of $D$ follows already from $m>0$, $\Delta>0$; directly, $D=m(5m^2-11)+6m^2+32>0$ for $m\ge2$. The part of (5.9) preceding $R$ equals $-(m^2+2m+4)/(2m(m+1))$. Consequently

$$
\begin{aligned}
g(m,1)
 &=\frac{2(m+1)N-(m^2+2m+4)D}{2m(m+1)D}\\
 &=\frac{3m^5+12m^4-17m^3+18m^2+80m-96}
         {2m(m+1)(5m^3+6m^2-11m+32)}.
\end{aligned}
\tag{5.20}
$$

For completeness the two products in the first numerator expand to

$$
\begin{aligned}
2(m+1)N&=8m^5+28m^4+4m^3+52m^2+100m+32,\\
(m^2+2m+4)D&=5m^5+16m^4+21m^3+34m^2+20m+128.
\end{aligned}
$$

The numerator of the second fraction in (5.20) is

$$
m^3(3m^2+12m-17)+(18m^2+80m-96)>0,
\tag{5.21}
$$

since $3m^2+12m-17\ge19$ and $18m^2+80m-96\ge136$ for every $m\ge2$. Its denominator is positive by (5.19). This proves strict positivity on the entire strip $b=1$, including $m=2$. Together with (5.10) and (5.18), it exhausts all allowed integer pairs and proves (5.3), with no equality. $\square$

The excluded boundary $m=1$ gives $G(1,b)=K_{1,b+1}$, so equality with the same-order star holds there. The boundary $b=0$ gives the complete graph $K_{m+1}$ and is outside the comparison domain. The theorem concerns the adjacency Hamiltonian $A$ alone.

Mohan–Tamon–Xu–Zhan, [arXiv:2608.20739v1, §8(v)](https://arxiv.org/abs/2608.20739v1), ask: “Is $S_n$ the second laziest connected graph on $n$ vertices for the adjacency matrix, unsigned Laplacian matrix and normalized Laplacian matrix?” The family restriction (5.1) belongs to Theorem 5.1, not to that published question. The theorem supplies its strict adjacency comparison on this nonbipartite noncomplete family; the comparison for arbitrary graphs in $\mathcal N_n$, equality outside this family, a reduction of that global problem to this family, and the comparisons for $D+A$ and $I-D^{-1/2}AD^{-1/2}$ remain separate mathematical questions.

## 追加锚（本行以下为增补区）
