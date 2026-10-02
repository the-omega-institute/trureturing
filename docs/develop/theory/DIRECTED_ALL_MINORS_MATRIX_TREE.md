# Directed all-minors matrix-tree identity over commutative rings

## 1. Source and conventions

The reference is Amitai Zernik, *Taylor expansion proof of the matrix tree theorem — part II*, arXiv:1308.2160v1, Definitions 1 and 4, Theorem 2 and Lemma 5, pages 1–5. The forest identity and signs are literature-attested. The source uses real matrices in its Taylor-expansion proof. The integral-coefficient argument below explains the commutative-ring extension; it does not transfer the vanishing of real derivatives to positive characteristic. This exposition is reference input, not a kernel-verified assertion.

Vertices are $V=\{0,\ldots,n-1\}$. All subsets and their complements are enumerated in increasing order. Changing the source's one-based vertex labels to these labels subtracts $2k$ from the root-sum exponent, so the sign is unchanged. An arrow $i\to j$ has weight $M_{ij}$. Rows indexed by $W$ and columns indexed by $U$ are deleted, not the other way around.

## 2. Forests and their signs

**Definition 2.1 (literal directed forests).** Let $U,W\subseteq V$ have cardinality $k\geq1$. A forest from $U$ to $W$ is a finite set $F\subseteq V\times V$ of directed edges, without loops or antiparallel pairs, whose underlying undirected graph is acyclic. Each connected component contains exactly one element of $U$ and exactly one element of $W$. Within each component all edges point away from its unique $U$ vertex. Isolated vertices are included as components. Thus a vertex in $U\cap W$ is the unique $W$ vertex of its own component, although that component may have other vertices.

**Definition 2.2 (component matching).** For each $u\in U$, let $\pi_F(u)$ be the unique element of $W$ in its connected component. The uniqueness of both roots in every component makes $\pi_F:U\to W$ a bijection. Write $U=\{u_0<\cdots<u_{k-1}\}$ and $W=\{w_0<\cdots<w_{k-1}\}$, and let $\sigma_F\in S_k$ be the unique permutation satisfying $\pi_F(u_a)=w_{\sigma_F(a)}$. Define

$$
\epsilon(U,W,F)=(-1)^{n+k+\sum_{u\in U}u+\sum_{w\in W}w}\operatorname{sgn}(\sigma_F).
$$

## 3. The identity and integral coefficients

**Theorem 3.1 (full directed all-minors identity).** For every commutative ring $R$, including the zero ring, every $n\in\mathbb N$, every $M\in R^{V\times V}$ satisfying $\sum_{i\in V}M_{ij}=0$ for every column $j$, and every $U,W\subseteq V$ of equal cardinality $k\geq1$,

$$
\det M[W^c,U^c]
=\sum_{F\in\mathcal F(U,W)}\epsilon(U,W,F)\prod_{(i,j)\in F}M_{ij}.
$$

Here both complements inherit the increasing order, and the integer signs are mapped into $R$. There are no restrictions on support, signs, characteristic, connectivity, nontriviality or size. In particular, $k=n$ gives the empty determinant and the empty forest, both with value $1$.

**Proof.** Put $I=W^c$, $J=U^c$ and $m=n-k$. The column-sum condition writes column $j\in J$ as $\sum_{i\ne j}M_{ij}(e_i-e_j)$. Determinant multilinearity expands the minor over choices of a parent $p(j)\ne j$ for every $j\in J$. The coefficient of $\prod_{j\in J}M_{p(j),j}$ is the integer determinant of the matrix $B_p$ with entries $\mathbf1_{i=p(j)}-\mathbf1_{i=j}$ for $i\in I$, $j\in J$.

Following parents either reaches $U$ or enters a directed cycle outside $U$. In the latter case the columns on the cycle sum to zero, giving a nonzero integer column relation and determinant zero. In the former case stopping depths partition the vertices into rooted trees, with literal edges $(p(j),j)$ pointing away from the terminal root. Each component contains exactly one $U$ vertex. Conversely, the unique incoming edge at each nonroot of a literal away-oriented tree recovers precisely this parent map, preserving every edge and its weight.

If $W$ does not meet every rooted component once, equal cardinalities imply that some component contains no $W$ vertex. Its indicator vector is supported on $I$, is nonzero over the integers, and annihilates $B_p$ on the left. Hence its determinant is zero. This dependence argument is performed over the integers before any ring homomorphism is applied.

For a surviving forest, form the full matrix $C$ whose root column at $u\in U$ is $e_u$ and whose nonroot column at $j$ is $e_j-e_{p(j)}$. Ordering vertices by increasing stopping depth makes this matrix triangular with all diagonal entries $1$, so $\det C=1$. For each root $u$, the unique path to $\pi_F(u)$ telescopes: $e_{\pi_F(u)}-e_u$ is the sum of the nonroot columns along that path. Adding those columns to the root column preserves the determinant and changes it to $e_{\pi_F(u)}$; all nonroot columns remain unchanged. This includes the empty path when $u\in W$.

Move the ascending $W$ rows and ascending $U$ columns to the front. The lower-left block vanishes; the upper-left block is the permutation matrix of $\sigma_F$ and the lower-right block is $-B_p$. The two shuffle signs have exponents $\sum U-k(k-1)/2$ and $\sum W-k(k-1)/2$. Since $k(k-1)$ is even, the determinant equation gives

$$
\det B_p=(-1)^{m+\sum U+\sum W}\operatorname{sgn}(\sigma_F).
$$

The exponents $m$ and $n+k$ differ by $2k$. Mapping these fixed integer coefficients into $R$, removing exactly the zero terms, and reindexing by the edge-preserving parent-map correspondence proves the identity. The arbitrary entries of $M$ need not lift to integers. No division, domain assumption or analytic continuation is used. If $k=n$, $U=W=V$, there are no parent columns, the only forest is empty, and its matching is the identity. If $n=0$, the root-cardinality hypotheses are impossible.

## 4. Zernik's gluing signs

**Theorem 4.1 (sign identities, Lemma 5).** The signs in Definition 2.2 satisfy the following properties. First, $\epsilon(V,V,\varnothing)=1$. Second, take $w_0\in W$, $i\notin W$, $j\notin U$ and a forest $F$ from $U\cup\{j\}$ to $W\cup\{i\}$. If there is a directed path from $j$ to $i$, set $F_{ij;w_0}=F\cup\{(w_0,j)\}$; otherwise set $F_{ij;w_0}=F\cup\{(i,j)\}$. This is a forest from $U$ to $W$, and

$$
(-1)^{i+|\{w\in W:w<i\}|+j+|\{u\in U:u<j\}|}
\epsilon(U\cup\{j\},W\cup\{i\},F)
=\epsilon''_{ij}(F)\epsilon(U,W,F_{ij;w_0}),
$$

where $\epsilon''_{ij}(F)=-1$ if $i$ is a descendant of $j$, including $i=j$, and $+1$ otherwise. Third, if $F$ and $F'=F\setminus\{(i,j)\}\cup\{(w_0,j)\}$ are both forests from $U$ to $W$, then $\epsilon(U,W,F)=\epsilon(U,W,F')$.

**Proof.** The first property follows from the identity matching and the even exponent $2n+2\sum V$. For the second, if $j$ and $i$ lie in different components, gluing replaces the two matching arrows $u\mapsto i$, $j\mapsto w$ by $u\mapsto w$. Removing their ascending coordinates changes the matching sign by $(-1)^{|\{u\in U:u<j\}|+|\{w\in W:w<i\}|-1}$. If $j$ and $i$ lie in the same component, gluing removes the single matching arrow $j\mapsto i$, with sign change $(-1)^{|\{u\in U:u<j\}|+|\{w\in W:w<i\}|}$. Combining either sign change with the root-sum exponent yields the displayed identity. For the third property, the detached subtree has no $W$ vertex, because the reattachment is also a forest with exactly one $W$ vertex per component. Consequently the component matching is unchanged. These are the combinatorial sign properties used by the real Taylor-expansion proof; the integral proof of Theorem 3.1 instead computes every coefficient directly.
