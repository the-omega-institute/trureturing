# Component parity for odd uniform reflection arrays

## 1. Actual fibre connectivity

**Theorem 1.1 (connectivity of the indexed fibre graph).** Let $n\ge3$ be odd, let $X=\{0,\ldots,n-1\}$ and $R=\{0,\ldots,2n-1\}$, and fix one array $A:R\times X\to X$. Suppose each row $\rho_i(x)=A(i,x)$ is a permutation, every actual fibre $F_{x,p}=\{i: A(i,x)=p\}$ has cardinality two, and, for all distinct columns $x,y$ and distinct symbols $p,q$, the actual counts $|\{i:A(i,x)=p, A(i,y)=q\}|$ and $|\{i:A(i,x)=q,A(i,y)=p\}|$ are equal. The simple graph on the original row indices with an edge between distinct $i,j$ precisely when $A(i,x)=A(j,x)$ for some $x$ is connected. In particular this holds when the first row is the identity and the rows are sorted lexicographically on their original labels. No reordering or relabeling is required. The row, fibre and reflection hypotheses are the uniform frequency-two case of Iurlano and Raidl, *Pairwise Reflection Symmetry in Generalized Latin Rectangles*, arXiv:2606.28315v1, Definitions 2--4.

Proof. Let $S$ be a proper set of row indices closed under fibre edges, and choose an actual row $i$ outside $S$. Every fibre meeting $S$ is wholly contained in $S$. For each column $x$, put $P_x=\{A(j,x):j\in S\}$. Partitioning $S$ by its two-element fibres gives $|S|=2|P_x|$ for every $x$. Thus all the $P_x$ have one cardinality $s$. On the actual column set define $K(x,y)$ to hold when $A(i,y)\in P_x$. Its diagonal is empty because $i\notin S$. If $K(x,y)$ holds, then $x\ne y$ and $p=A(i,x)$, $q=A(i,y)$ are distinct. The actual row $i$ makes the count of pattern $(p,q)$ positive. Reflection supplies an actual row $j$ realizing $(q,p)$. Since $q\in P_x$, fibre closure forces $j\in S$, and hence $p\in P_y$. Therefore $K$ is symmetric. The permutation $A(i,-)$ identifies the neighbors of each $x$ with $P_x$, so $K$ is an $s$-regular simple graph on $n$ vertices. Its degree sum $ns$ is even by the degree-sum formula. Oddness of $n$ forces $s$ even, and consequently $4$ divides $|S|$. If the fibre graph were disconnected, the component of any row and its nonempty complement would both be proper closed sets. Their cardinalities would each be divisible by four, forcing $4$ to divide $2n$, contrary to oddness of $n$. $\square$

## Addition anchor


## 2. Nonsingularity under actual cross-Gram commutation

**Theorem 2.1 (conditional nonsingularity on the original symbol set).** Let $n\ge3$ be odd, $X=\{0,\ldots,n-1\}$, $R=\{0,\ldots,2n-1\}$, and $A:R\times X\to X$ be one indexed array. Assume every row $A(i,-)$ is a permutation, every fibre $\{i:A(i,x)=p\}$ has cardinality two, and the joint counts satisfy reflection symmetry for distinct columns and distinct symbols, as in Theorem 1.1. Define real indicator matrices $B_x(i,p)=1$ if $A(i,x)=p$ and zero otherwise, and put $H_{xy}=B_x^{\mathsf T}B_y$. Assume additionally

$$
H_{xy}H_{ab}=H_{ab}H_{xy}\qquad(x,y,a,b\in X).
$$

For every pair $u\ne v$ of original columns and every $z\in\mathbb R^X$, $H_{uv}z=0$ implies $z=0$.

Proof. All joint counts below use the same rows of $A$. Their entries are nonnegative integers. Reflection and the row-permutation condition make every $H_{xy}$ symmetric; each row sum is two. For $u\ne v$, row injectivity also gives $H_{uv}(p,p)=0$. For every fixed $x,p,q$, row bijectivity and fibre cardinality two give

$$
\sum_{y\in X}H_{xy}(p,q)=2.
$$

Write $D=H_{uv}$ and form its simple support graph on $X$, joining distinct symbols $p,q$ exactly when $D(p,q)>0$. Its components partition $X$. If $Q$ is one component, then $D1_Q=2\,1_Q$. Commutation gives $D(H_{xy}1_Q)=2H_{xy}1_Q$. A vector $w$ with $Dw=2w$ is constant on every support component: symmetry and row sum two give

$$
\sum_{p,q\in X}D(p,q)(w(p)-w(q))^2
=2\sum_{p\in X}w(p)\sum_{q\in X}D(p,q)(w(p)-w(q))=0,
$$

and every summand is nonnegative. Thus the row sums of the actual block $H_{xy}|_{P\times Q}$ are constant on $P$, and its column sums are constant on $Q$. If this block has a positive entry, these constants $r,s$ are positive integers at most two. Counting its entries in both orders gives $|P|r=|Q|s$.

Because $|X|=n$ is odd, some component $P$ has odd cardinality $d$. Every component contains at least two vertices, since the diagonal of $D$ is zero and its row sums are two; hence $d\ge3$. For any component $Q$, choose $p\in P$, $q\in Q$ and any original column $x$. The displayed sum over $y$ supplies an actual block $H_{xy}|_{P\times Q}$ with a positive entry. Its constants $r,s\in\{1,2\}$ give $dr=|Q|s$. The possibility $d=2|Q|$ is excluded by oddness, so $|Q|$ is $d$ or $2d$. In particular no support component has size divisible by four.

An entry $D(p,q)=2$ would, by symmetry and row sum two, make $p,q$ each other's only neighbors. Their component would have two vertices, contradicting the component-size conclusion. Consequently every positive entry is one, and every support vertex has degree two. The standard finite degree-two graph theorem makes each connected component a cycle, of length $L$ not divisible by four.

On such an actual cycle write $t_j$ for the coordinate of $z$ at position $j$. The equation $Dz=0$ gives $t_{j+2}=-t_j$, with indices modulo $L$. The resulting four-periodic pattern is $(t_0,t_1,-t_0,-t_1)$. For $L$ congruent to one, two or three modulo four, identifying both $t_L=t_0$ and $t_{L+1}=t_1$ forces $t_0=t_1=0$. Thus every coordinate on every component vanishes, proving $z=0$. $\square$

The array and joint-count definitions are the frequency-two, row-permutation case of Iurlano and Raidl, *Pairwise Reflection Symmetry in Generalized Latin Rectangles*, arXiv:2606.28315v1, Definitions 3--4. The component-size and kernel argument is repository-derived; the finite degree-two cycle theorem is standard. Pairwise commutation is an additional hypothesis here. No implication from fibre size and reflection alone to commutation is asserted.

## Addition anchor

## 3. Invariant partitions of relative moved support

**Theorem 3.1 (actual invariant moved-support bound).** Let $n\ge3$ be odd, let $X=\{0,\ldots,n-1\}$ and $R=\{0,\ldots,2n-1\}$, and let $\rho:R\to\operatorname{Perm}(X)$ be one indexed row family. Assume every actual fibre $F_{x,p}=\{t:\rho_t(x)=p\}$ has cardinality two. For distinct columns $x,y$ and distinct symbols $p,q$, assume

$$
|\{t:\rho_t(x)=p,\ \rho_t(y)=q\}|
=|\{t:\rho_t(x)=q,\ \rho_t(y)=p\}|.
$$

Choose distinct row indices $r,s$. Put $\sigma=\rho_r^{-1}\circ\rho_s$, $D=\{x:\sigma(x)\ne x\}$, and let $U\subseteq D$ satisfy $\sigma(U)=U$. Put $V=D\setminus U$, $a=|U|$, $b=|V|$ and $d=|D|$. Then

$$
n+d\le a^2+b^2+1.
$$

Either block may be empty. The hypotheses concern actual row indices and joint counts of the same array; they require no commutation, row sorting, identity first row, or additional distinctness of row permutations.

Proof. Write $S=X\setminus D$ and, for each row $t$, $\tau_t=\rho_r^{-1}\circ\rho_t$. Fix $t\notin\{r,s\}$ and abbreviate $\tau=\tau_t$. At any $x\in S$, rows $r$ and $s$ exhaust $F_{x,\rho_r(x)}$. Thus $\tau(x)\ne x$. If $x,y\in S$ and $\tau(x)=y$, then $x\ne y$. Rows $r,s$ both realize the pattern $(\rho_r(x),\rho_r(y))$ in columns $(x,y)$, and the fibre bound makes its count exactly two. Reflection gives exactly two occurrences of the reversed pattern. These exhaust $F_{x,\rho_r(y)}$, which contains $t$. Consequently $\tau(y)=x$. Thus all $S$-to-$S$ entries of $\tau$ form disjoint fixed-point-free transpositions.

Let $A=\{x\in S:\tau(x)\in S\}$, and let $\ell$ be the number of $D$-to-$S$ entries of $\tau$. Bijectivity gives the same number of $S$-to-$D$ entries. The transpositions make $|A|$ even. If $k=|\{u\in D:\tau(u)\in D\}|$, then

$$
n=|A|+2\ell+k.
$$

Therefore $k$ is odd.

For $u\in D$ with $x=\tau(u)\in S$, reflection also forces

$$
\tau(x)\in\{u,\sigma(u)\}.
$$

Indeed, at columns $(x,u)$, rows $r$ and $s$ realize respectively $(\rho_r(x),\rho_r(u))$ and $(\rho_r(x),\rho_s(u))$. The pairs differ because $u\in D$. Each reflected pattern has a positive count, and the two reflected row sets are disjoint subsets of the actual two-element fibre $F_{u,\rho_r(x)}$. Their union is therefore that entire fibre. Row $t$ lies in the union, giving the displayed alternative.

Define on $D$

$$
h(u)=\begin{cases}
\tau(u),&\tau(u)\in D,\\
\tau(\tau(u)),&\tau(u)\in S.
\end{cases}
$$

This is a genuine permutation of $D$. For the two-step case, $\tau(\tau(u))$ cannot lie in $S$: the internal transposition rule would imply $\tau(\tau(u))=u$, contradicting $u\in D$. To check injectivity, two one-step images cancel through $\tau$, and two two-step images cancel twice. Equality between a one-step image and a two-step image would make one input equal to the other input's first image in $S$, contradicting that both inputs lie in $D$. Finite injectivity yields bijectivity.

Each contracted edge $u\mapsto h(u)$ lies within the $\sigma$-invariant block containing $u$, since its endpoint is $u$ or $\sigma(u)$. Hence every edge of $h$ between $U$ and $V$ is an actual, uncontracted entry of $\tau$. The two directions have equal cardinality, say $c$ each: a permutation sends as many elements out of a finite subset as into it. If $w_t$ counts the actual entries of row $t$ in $(U\times\rho_r(U))\cup(V\times\rho_r(V))$, then

$$
k=w_t+2c.
$$

Thus $w_t$ is odd and at least one.

Finally, summing the actual block counts over all row indices gives $2(a^2+b^2)$, because each column-symbol fibre has size two and $\rho_r$ is injective. Rows $r$ and $s$ each contribute $d$, since their relative permutations are the identity and $\sigma$, both preserving $U$ and $V$. The other $2n-2$ rows each contribute at least one. Therefore

$$
2(a^2+b^2)\ge2d+2n-2,
$$

which proves the claimed bound. $\square$

The actual array hypotheses use the same source domain as Theorem 1.1. Generic involution parity and finite permutation cardinality are standard; the argument uses the original reflected incidences to justify saturation and contraction.
