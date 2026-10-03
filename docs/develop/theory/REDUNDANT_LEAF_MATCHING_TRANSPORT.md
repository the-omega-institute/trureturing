# Redundant-leaf maximal-matching transport

## 1. Graphs, matchings, and maps

**Definition 1.1 (Setting and transport maps).** Let $V$ be a finite vertex type with decidable
equality, and let $G$ be an undirected simple graph on $V$. Write $xy$ for the unordered pair
with endpoints $x,y$, an element of $\operatorname{Sym2} V$. Graph edges have distinct endpoints;
each undirected edge is counted once. A matching is a finite set of graph edges whose distinct
members have disjoint endpoint sets. A vertex is saturated when it belongs to a matching edge.
Write $\operatorname{Max}_K(M)$ when $M$ is a matching of $K$ to which no new edge of $K$ can be
added while retaining the matching property; this means inclusion-maximal, not maximum size.

Fix $u,v,a\in V$ satisfying

$$
u\ne v,\qquad \deg_G(u)=\deg_G(v)=1,\qquad G(u,a),\qquad G(v,a),
$$

where $G(x,y)$ denotes adjacency. Thus $u,v$ are leaves in the original graph, each with unique
neighbour $a$; simplicity gives $a\ne u,v$. Define the actual subtype and induced graph

$$
W=\{x:V\mathbin{//}x\ne u\},\qquad H=G[W],\qquad
H(w,z)\ \Longleftrightarrow\ G(w.\mathrm{val},z.\mathrm{val}).
$$

Here $W$ consists of a vertex together with its proof of inequality to $u$. Every vertex other
than $u$ is retained, including isolated vertices. For $x\ne u$, write $\bar x\in W$ for this
subtype element. Define inclusion $i:W\to V$ and the fold $f:V\to W$ by

$$
i(\bar x)=x,\qquad
f(x)=\begin{cases}\bar v&x=u,\\\bar x&x\ne u.\end{cases}
$$

For any vertex map $g$, $\operatorname{Sym2.map}(g)$ sends $xy$ to the unordered pair $g(x)g(y)$.
For finite edge sets $M$ on $V$ and $N$ on $W$, define finite-set images

$$
R(M)=\{\operatorname{Sym2.map}(f)(e):e\in M\},\qquad
L(N)=\{\operatorname{Sym2.map}(i)(e):e\in N\}.
$$

Coincident images are counted only once, as in a finite-set image.

## 2. Transport theorem

**定理 2.1 (Redundant-leaf maximal-matching transport).** For every finite $V$, every simple
graph $G$ on $V$, and every $u,v,a$ satisfying exactly the hypotheses of Definition 1.1, the
specified maps satisfy the following single transport statement:

$$
\begin{aligned}
&\bigl(\forall M:\operatorname{Finset}(\operatorname{Sym2}V),\quad
\operatorname{Max}_G(M)\Rightarrow
[\operatorname{Max}_H(R(M))\land |R(M)|=|M|]\bigr)\\
&\quad\land\bigl(\forall N:\operatorname{Finset}(\operatorname{Sym2}W),\quad
\operatorname{Max}_H(N)\Rightarrow
[\operatorname{Max}_G(L(N))\land |L(N)|=|N|]\bigr).
\end{aligned}
$$

Proof. For a matching, inclusion-maximality is equivalent to every graph edge having a
saturated endpoint: an edge with two unsaturated endpoints can be added, whereas a new edge
touching a saturated endpoint conflicts with a matching edge.

Let $M$ be any inclusion-maximal matching of $G$. If $au\notin M$, then $u$ is unsaturated,
since its only incident edge is $au$, and folding just retags all edges into $W$. If $au\in M$,
then $v$ is unsaturated: its only incident edge $av$ would conflict with $au$ at $a$. Replace
$au$ by $av$ and retag into $W$. All other matching edges avoid $a,u,v$, so the replacement
is a matching. In either case this is exactly $R(M)$, and each of its pairs is an edge of $H$.

The only distinct vertices identified by $f$ are $u,v$, and these cannot both be saturated by
$M$: their incident matching edges would share $a$. Consequently $f$ is injective on the
endpoints of $M$. If two edges of $M$ have the same folded unordered pair, this endpoint
injectivity forces the original unordered pairs to agree. Thus $\operatorname{Sym2.map}(f)$
is injective on the matched edges, and finite-set image cardinality gives $|R(M)|=|M|$.

Every retained vertex saturated by $M$ remains saturated in $R(M)$. In the replacement case,
$a$ keeps a matched edge and $v$ gains saturation; only the deleted $u$ loses saturation.
Each edge of $H$ is an edge of $G$ with both endpoints retained. Maximality of $M$ supplies a
saturated endpoint of that edge, which remains saturated after transport. Hence $R(M)$ is
inclusion-maximal in $H$.

Now let $N$ be any inclusion-maximal matching of $H$. Inclusion sends its edges to edges of
$G$ and preserves their disjointness. Since $i$ is injective, its map on unordered edges is
injective, so $L(N)$ is a matching and $|L(N)|=|N|$. The vertex $\bar a$ must be saturated by
$N$: if it were not, $\bar v$ would also be unsaturated, because its only neighbour in $H$ is
$\bar a$, and the edge $\bar a\bar v$ could be added. Every edge of $G$ with retained endpoints
is blocked by maximality of $N$. The only edge involving the restored vertex $u$ is $ua$,
and it is blocked by saturation of $a$ in $L(N)$. Therefore $L(N)$ is inclusion-maximal in $G$.

Construction source: `repo-derived`, the matching argument under “zero cost leaf reduction”
in [issue 12282](https://github.com/the-omega-institute/trureturing/issues/12282), expressed
here with the actual subtype and explicit unordered-edge image maps. The matching conventions
follow the Formal Conjectures Authors' [Matching.lean at
df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1](https://github.com/google-deepmind/formal-conjectures/blob/df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Matching.lean),
$\texttt{IsEdgeMatching}$ and $\texttt{IsMaximalEdgeMatching}$, licensed under
[Apache 2.0](https://www.apache.org/licenses/LICENSE-2.0).

## 3. Scope boundary

The transport is not a bijection: in $K_{1,2}$ with centre $a$ and leaves $u,v$, the two
maximal matchings $\{au\}$ and $\{av\}$ both fold to $\{\bar a\bar v\}$ after deleting $u$.
No connectedness or upper bound on vertex degrees is required. The statement concerns
matching transport only and asserts no harmonic-index conclusion.

## 追加锚（本行以下为增补区）
