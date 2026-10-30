# CDSO minimizers without a universal vertex for every cyclomatic number

This volume is reference input; nothing in it is kernel-verified. Its text is append-only: corrections and additions belong after the final append anchor.

## 1. Scope

The complementary diminished Sombor index of a graph is $\sum_{uv\in E}\sqrt{d_u^2+d_v^2}/\max(d_u,d_v)$. Among connected graphs of order $n$ with cyclomatic number $\ell\ge1$, this volume shows that a graph with a universal vertex pays an excess over the edge count that is bounded below independently of $n$, while a two-hub graph without a universal vertex has excess of order $1/n$. Consequently, for every $\ell\ge1$ and every $n\ge3\ell+9$, no minimizer of the index has a universal vertex; for $\ell=1$ the same holds for every $n\ge7$. The minimum excess over the edge count lies between two explicit functions of order $1/n$.

## 2. Notation and cited facts

**Cited facts.** The following are taken from A. M. Albalahi, S. Das, A. Ali, J. Barman, A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*, Discrete Math. Lett. 16 (2025) 108–115, DOI 10.47443/dml.2025.176; preprint arXiv:2510.24809v1.

- (a) Definition, Sec. 1 (journal p. 109; arXiv v1 Sec. 1): for a graph $G$ with edge set $E$ and degrees $d(w)$, the complementary diminished Sombor (CDSO) index is ${}^c\mathrm{DSO}(G)=\sum_{uv\in E}\sqrt{d(u)^2+d(v)^2}/\max\{d(u),d(v)\}$.
- (b) Sec. 4, Concluding remarks (journal p. 115): the cyclomatic number of a graph is the minimum number of edges whose removal makes the graph acyclic, and Conjecture 4.1 reads: “A graph minimizing (maximizing, respectively) the CDSO index (HSO index, respectively) among fixed-order connected graphs with cyclomatic number $\ell(\ge1)$ has a vertex adjacent to all other vertices.” In arXiv v1 the same assertion appears as prose in Sec. 4, Concluding Remarks, without a conjecture number.

**Convention 2.1 (Graph classes and excess).** Graphs are finite and simple. For integers $n\ge1$ and $\ell\ge0$ let $\mathcal G(n,\ell)$ be the set of connected graphs on the vertex set $\{1,\dots,n\}$ with cyclomatic number $\ell$. Write $\Phi(G)={}^c\mathrm{DSO}(G)$ and $m=m(G)$ for the number of edges. For $G\in\mathcal G(n,\ell)$ we use the standard identity $m=n-1+\ell$ for connected graphs (cyclomatic number $m-n+1$), recalled with its usual argument: an acyclic spanning subgraph of a graph on $n$ vertices has at most $n-1$ edges, so at least $m-n+1$ edges must be removed, and removing the edges outside a spanning tree of the connected graph $G$ removes exactly $m-n+1$. The excess of $G$ is $E(G)=\Phi(G)-m$. A vertex is universal if it is adjacent to all other vertices. A minimizer in $\mathcal G(n,\ell)$ is a graph $G\in\mathcal G(n,\ell)$ with $\Phi(G)\le\Phi(G')$ for all $G'\in\mathcal G(n,\ell)$; when $\mathcal G(n,\ell)$ is nonempty a minimizer exists, since the set is finite. Stance: repo-derived for the notation fixed in this volume; the identity $m=n-1+\ell$ is a standard textbook fact of graph theory, not claimed as repo-derived.

**Convention 2.2 (Edge cost).** For positive integers $a,b$ put $\varphi(a,b)=\sqrt{a^2+b^2}/\max(a,b)=\sqrt{1+r^2}$ with $r=\min(a,b)/\max(a,b)\in(0,1]$, so $\Phi(G)=\sum_{uv\in E}\varphi(d_u,d_v)$ and $E(G)=\sum_{uv\in E}(\varphi(d_u,d_v)-1)$. For integers $D\ge k\ge1$ put $\psi(D,k)=\varphi(D,k)-1=\sqrt{1+k^2/D^2}-1$. Finally

$$
c_\ell=\ell\left(\frac{\sqrt{(\ell+1)^2+4}}{\ell+1}-1\right)\qquad(\ell\ge1).
$$

Stance: repo-derived (notation fixed in this volume).

## 3. The universal-vertex floor

**Lemma 3.2 (Floor for a universal vertex).** Let $\ell\ge1$, $n\ge3$ and $G\in\mathcal G(n,\ell)$ have a universal vertex. Then $E(G)\ge c_\ell$, and

$$
c_\ell\ge\frac{2\ell}{(\ell+1)^2+1}.
$$

Stance: suspected-novel (see §6).

**Proof.** Let $h$ be a universal vertex. The $n-1$ edges at $h$ each have $\varphi\ge1$. The remaining $m-(n-1)=\ell$ edges avoid $h$. For $u\ne h$ let $e_u$ be the number of these $\ell$ edges at $u$; then $d_u=1+e_u$ and $e_u\le\ell$. If $uv$ is one of the $\ell$ edges avoiding $h$, then $e_u,e_v\ge1$, so $2\le d_u,d_v\le\ell+1$ and $r=\min(d_u,d_v)/\max(d_u,d_v)\ge2/(\ell+1)$. Since $\sqrt{1+r^2}$ increases in $r$, each such edge has $\varphi(d_u,d_v)\ge\sqrt{(\ell+1)^2+4}/(\ell+1)$. Summing, $\Phi(G)\ge(n-1)+\ell\sqrt{(\ell+1)^2+4}/(\ell+1)=m+c_\ell$.

For the lower bound on $c_\ell$, put $x=4/(\ell+1)^2$. Rationalising gives $\sqrt{1+x}-1=x/(\sqrt{1+x}+1)$, and $\sqrt{1+x}\le1+x/2$ (square both sides), so $\sqrt{1+x}-1\ge x/(2+x/2)=2x/(4+x)$. Hence $c_\ell=\ell(\sqrt{1+x}-1)\ge\ell\cdot2x/(4+x)=2\ell/((\ell+1)^2+1)$. ∎

## 4. Two-hub graphs and the main theorems

**Definition 4.1 (Two-hub graph).** Let $\ell\ge1$ and $n\ge\ell+3$, and put $p=n-\ell-3\ge0$. The graph $H_{n,\ell}$ has vertices $a,b$, $w_0,\dots,w_\ell$ and $q_1,\dots,q_p$; its edges are $aw_i$ and $bw_i$ for $0\le i\le\ell$, $aq_j$ for $1\le j\le\lfloor p/2\rfloor$, and $bq_j$ for $\lfloor p/2\rfloor<j\le p$. Stance: repo-derived (construction fixed in this volume).

**Lemma 4.2 (Two-hub graphs are admissible and cheap).** Let $\ell\ge1$ and $n\ge\ell+3$. Then $H_{n,\ell}\in\mathcal G(n,\ell)$ up to relabelling, $H_{n,\ell}$ has no universal vertex, and

$$
E(H_{n,\ell})\le\frac{2(n+7\ell+5)}{(n+\ell-2)^2}.
$$

Stance: suspected-novel (see §6).

**Proof.** The graph has $2+(\ell+1)+p=n$ vertices and $2(\ell+1)+p=n+\ell-1$ edges, and it is connected because every vertex is joined to $a$ or $b$ and $a,b$ are both joined to $w_0$. Hence its cyclomatic number is $(n+\ell-1)-n+1=\ell$ by Convention 2.1. The vertices $a$ and $b$ are not adjacent, so neither is universal; every other vertex has degree at most $2<n-1$, since $n\ge4$.

The degrees are $D_a=\ell+1+\lfloor p/2\rfloor$, $D_b=\ell+1+\lceil p/2\rceil$, $d(w_i)=2$ and $d(q_j)=1$. Let $D=\min(D_a,D_b)=D_a$. Then $D\ge\ell+1+(p-1)/2=(n+\ell-2)/2$ and $D\ge\ell+1\ge2$. Every edge joins a hub of degree at least $D$ to a vertex of degree $k\in\{1,2\}$, and since $\sqrt{1+x}\le1+x/2$ for $x\ge0$ (square both sides) its cost is $\psi(D_\ast,k)\le k^2/(2D_\ast^2)\le k^2/(2D^2)$, where $D_\ast\in\{D_a,D_b\}$ is the hub degree. The $2(\ell+1)$ edges with $k=2$ contribute at most $4(\ell+1)/D^2$, and the $p$ edges with $k=1$ contribute at most $p/(2D^2)$. Therefore

$$
E(H_{n,\ell})\le\frac{8(\ell+1)+n-\ell-3}{2D^2}=\frac{n+7\ell+5}{2D^2}\le\frac{2(n+7\ell+5)}{(n+\ell-2)^2}.
$$

∎

**Theorem 4.3 (No universal vertex for large order).** Let $\ell\ge1$ and $n\ge3\ell+9$. Then no minimizer in $\mathcal G(n,\ell)$ has a universal vertex. More precisely, every graph in $\mathcal G(n,\ell)$ with a universal vertex has a strictly larger index than $H_{n,\ell}$. Stance: suspected-novel (see §6).

**Proof.** By Lemmas 3.2 and 4.2 it suffices to show

$$
\frac{2(n+7\ell+5)}{(n+\ell-2)^2}<\frac{2\ell}{(\ell+1)^2+1},
$$

for then every $G\in\mathcal G(n,\ell)$ with a universal vertex satisfies $\Phi(G)\ge m+c_\ell>\Phi(H_{n,\ell})$, while every minimizer $G^\ast$ satisfies $\Phi(G^\ast)\le\Phi(H_{n,\ell})$. Put $s=n+\ell-2$, so that $n+7\ell+5=s+6\ell+7$ and $s\ge4\ell+7$. Clearing the positive denominators, the inequality is equivalent to $f(s)>0$, where

$$
f(s)=\ell s^2-(\ell^2+2\ell+2)(s+6\ell+7).
$$

At $s=4\ell+7$, using $\ell(4\ell+7)^2=16\ell^3+56\ell^2+49\ell$ and $(\ell^2+2\ell+2)(10\ell+14)=10\ell^3+34\ell^2+48\ell+28$,

$$
f(4\ell+7)=6\ell^3+22\ell^2+\ell-28\ge6+22+1-28=1>0,
$$

since the cubic increases in $\ell\ge1$. For $s\ge4\ell+7$ the derivative satisfies $f'(s)=2\ell s-(\ell^2+2\ell+2)\ge2\ell(4\ell+7)-(\ell^2+2\ell+2)=7\ell^2+12\ell-2>0$, so $f(s)\ge f(4\ell+7)>0$ for all $s\ge4\ell+7$. ∎

**Definition 4.4 (The unicyclic graphs $U_n$ and $T_n$).** For $n\ge3$, $U_n$ is the graph with a vertex $h$ adjacent to all of $x,y,z_1,\dots,z_{n-3}$ and one further edge $xy$. For $n\ge5$, $T_n$ is the graph with edges $hx$, $hy$, $xy$, $xz$ and $hz_j$ for $1\le j\le n-4$. Stance: repo-derived (construction fixed in this volume).

**Theorem 4.5 (The unicyclic case for every order at least seven).** Let $n\ge7$. Then $T_n\in\mathcal G(n,1)$ up to relabelling, $T_n$ has no universal vertex, every graph in $\mathcal G(n,1)$ with a universal vertex has index $\Phi(U_n)$, and $\Phi(T_n)<\Phi(U_n)$. Consequently no minimizer in $\mathcal G(n,1)$ has a universal vertex. Stance: suspected-novel for $n\ge8$ (see §6); the instance $n=7$ was obtained earlier in this project (repo-derived), and the proof below covers it uniformly.

**Proof.** Membership: $T_n$ has the $n$ vertices $h,x,y,z,z_1,\dots,z_{n-4}$ and $n$ edges, and it is connected, so its cyclomatic number is $1$. Its degrees are $d_h=n-2$, $d_x=3$, $d_y=2$ and $1$ for $z$ and each $z_j$; as $n\ge7$ every degree is below $n-1$, so $T_n$ has no universal vertex.

Universal-vertex graphs: if $G\in\mathcal G(n,1)$ has a universal vertex $h$, then exactly one edge avoids $h$, say $xy$; so $d_h=n-1$, $d_x=d_y=2$ and all other vertices are leaves at $h$, and $G$ is a relabelling of $U_n$. With $\psi$ from Convention 2.2,

$$
E(U_n)=(\sqrt2-1)+2\psi(n-1,2)+(n-3)\psi(n-1,1),
$$

$$
E(T_n)=\Big(\tfrac{\sqrt{13}}3-1\Big)+\Big(\tfrac{\sqrt{10}}3-1\Big)+\psi(n-2,3)+\psi(n-2,2)+(n-4)\psi(n-2,1),
$$

where the two bracketed terms are the edges $xy$ (degrees $3,2$) and $xz$ (degrees $3,1$), and $n-2\ge3$ is the larger endpoint degree on every edge at $h$. Both graphs have $n$ edges, so $\Phi(U_n)-\Phi(T_n)=E(U_n)-E(T_n)$.

For $x\ge0$ put $y=\sqrt{1+x}-1\ge0$, so $x=2y+y^2$; then $x/2-x^2/8=y-y^3/2-y^4/8\le y$, and $\sqrt{1+x}\le1+x/2$ (square both sides). Applying the lower bound $\sqrt{1+x}-1\ge x/2-x^2/8$ with $x=k^2/(n-1)^2$ to $E(U_n)$ and the upper bound $\sqrt{1+x}-1\le x/2$ with $x=k^2/(n-2)^2$ to $E(T_n)$ gives

$$
E(U_n)\ge(\sqrt2-1)+\frac{n+5}{2(n-1)^2}-\frac{n+29}{8(n-1)^4},\qquad E(T_n)\le\frac{\sqrt{13}+\sqrt{10}}3-2+\frac{n+9}{2(n-2)^2}.
$$

Hence $E(U_n)-E(T_n)\ge K-g(n)$ with

$$
K=\sqrt2+1-\frac{\sqrt{13}+\sqrt{10}}3,\qquad g(n)=\frac{n+9}{2(n-2)^2}-\frac{n+5}{2(n-1)^2}+\frac{n+29}{8(n-1)^4}.
$$

From $1.41421^2<2$, $3.60556^2>13$ and $3.16228^2>10$ we get $K>2.41421-6.76784/3=47479/300000>0.1582$. Exact evaluation gives $g(7)=1129/7200<0.1569$, $g(8)=9109/86436<0.106$ and $g(9)=60579/802816<0.076$. For $n\ge10$, the inequality $4(n+5)(n-1)^2\ge n+29$ shows that the last two terms of $g(n)$ have a nonpositive sum, so $g(n)\le(n+9)/(2(n-2)^2)$; this bound decreases in $n$ for $n>2$, because its derivative is $-(n+20)/(2(n-2)^3)$, and at $n=10$ it equals $19/128<0.1485$. Thus $g(n)<K$ for every $n\ge7$, and $\Phi(T_n)<\Phi(U_n)$. Every minimizer $G^\ast$ satisfies $\Phi(G^\ast)\le\Phi(T_n)<\Phi(U_n)$, so it has no universal vertex. ∎

**Corollary 4.6 (The CDSO half of the universal-vertex assertion fails for every cyclomatic number).** For every $\ell\ge1$ there is an order $n$, namely every $n\ge3\ell+9$ and, for $\ell=1$, every $n\ge7$, such that no minimizer of the CDSO index in $\mathcal G(n,\ell)$ has a vertex adjacent to all other vertices. In particular the CDSO half of the assertion quoted in cited fact (b) is false for each fixed $\ell\ge1$. Stance: suspected-novel for $\ell\ge2$ and for $\ell=1$ with $n\ge8$ (see §6); the failure at $(n,\ell)=(7,1)$ was obtained earlier in this project (repo-derived), and the proof below covers it uniformly.

**Proof.** Theorems 4.3 and 4.5. ∎

**Proposition 4.7 (Window for the minimum excess).** Let $\ell\ge1$, $n\ge\ell+3$, and let $E^\ast(n,\ell)=\min\{E(G):G\in\mathcal G(n,\ell)\}$. Then

$$
\frac{\sqrt2-1}{n}<E^\ast(n,\ell)\le\frac{2(n+7\ell+5)}{(n+\ell-2)^2}.
$$

In particular, for fixed $\ell$, $E^\ast(n,\ell)$ lies between $(\sqrt2-1)/n$ and $(2+o(1))/n$ as $n\to\infty$, while by Lemma 3.2 every graph with a universal vertex has excess at least $2\ell/((\ell+1)^2+1)$, independent of $n$. Stance: suspected-novel (see §6).

**Proof.** The upper bound is Lemma 4.2. For the lower bound let $G\in\mathcal G(n,\ell)$ and $uv\in E(G)$. Since $1\le\min(d_u,d_v)$ and $\max(d_u,d_v)\le n-1$, the ratio satisfies $r\ge1/(n-1)$. The function $x\mapsto\sqrt{1+x}-1$ is concave on $[0,1]$ with values $0$ and $\sqrt2-1$ at the endpoints, so it lies above its chord $(\sqrt2-1)x$ there; with $x=r^2\le1$ this gives $\varphi(d_u,d_v)-1\ge(\sqrt2-1)r^2\ge(\sqrt2-1)/(n-1)^2$. Summing over the $m=n-1+\ell\ge n$ edges, $E(G)\ge(\sqrt2-1)n/(n-1)^2>(\sqrt2-1)/n$. ∎

## 5. Boundaries and open questions

**Remark 5.1 (What is not claimed).** The thresholds $3\ell+9$ and $7$ are sufficient conditions; this volume does not determine the least order from which minimizers lack a universal vertex, and makes no statement about orders below these thresholds, in particular none asserting that minimizers of small order have a universal vertex. It identifies no minimizer and does not assert that $H_{n,\ell}$ or $T_n$ is one. It gives no asymptotic constant for $E^\ast(n,\ell)$ beyond the window of Proposition 4.7. It does not address the HSO half of the assertion in cited fact (b), nor Conjecture 4.2 of the cited paper. Stance: repo-derived.

**Open question 5.2 (Exact thresholds and minimizer structure).** For each $\ell\ge2$, determine the least $n_0(\ell)$ such that no minimizer in $\mathcal G(n,\ell)$ has a universal vertex for all $n\ge n_0(\ell)$, and decide whether the set of orders $n$ at which some minimizer has a universal vertex is an initial segment. Determine the structure of the minimizers in $\mathcal G(n,\ell)$ and the limit of $n\,E^\ast(n,\ell)$, if it exists. Theorem 4.3 gives $n_0(\ell)\le3\ell+9$; the missing ingredient for a sharp answer is a matching lower bound on $E(G)$ for graphs without a universal vertex. Stance: repo-derived (question posed in this volume).

## 6. Sources and literature status

| Source | Exact scope and use |
| --- | --- |
| A. M. Albalahi, S. Das, A. Ali, J. Barman, A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*, Discrete Math. Lett. 16 (2025) 108–115, DOI 10.47443/dml.2025.176, Sec. 1 (p. 109) and Sec. 4 (p. 115); preprint arXiv:2510.24809v1, Secs. 1 and 4 | `literature-attested`: the definition of the CDSO index (cited fact (a)), the definition of cyclomatic number and the wording of Conjecture 4.1 (cited fact (b)). The paper proves no result about minimizers with fixed positive cyclomatic number. |
| — | `repo-derived`: Conventions 2.1 (notation; the identity $m=n-1+\ell$ is standard), 2.2, Definitions 4.1, 4.4, Remark 5.1, Open question 5.2; the instance $n=7$ of Theorem 4.5 and the instance $(n,\ell)=(7,1)$ of Corollary 4.6, obtained earlier in this project and covered uniformly by the proofs here. |
| — | `suspected-novel`: Lemma 3.2, Lemma 4.2, Theorem 4.3, Theorem 4.5 for $n\ge8$, Corollary 4.6 apart from the instance $(7,1)$, Proposition 4.7. Searched: the full text of the journal version and of arXiv:2510.24809v1; I. Gutman, *Survey of Sombor-type degree-based topological indices*, MATCH Commun. Math. Comput. Chem. 96 (2026) 819–837, which lists the CDSO index by its definition only; S. Akbari, A. Ali, B. Furtula, F. Movahedi, M. Rahmani Moghadam, *Revisiting the diminished Sombor index*, MATCH Commun. Math. Comput. Chem. 96(2) (2026) 611–624, whose abstract concerns the diminished Sombor index on classes of fixed order and size; web searches combining complementary diminished Sombor index, CDSO, hyperbolic Sombor index, cyclomatic number, minimizer, universal vertex and the arXiv identifier 2510.24809. No statement of these results was found in the searched scope; this establishes no worldwide priority. |

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）

## 7. Rigidity below an inverse-order excess bound

**Theorem 7.1 (Exact structure at small excess).** Let $\ell\ge1$ be an integer, put

$$
N(\ell)=30(\ell+14)^2,
$$

and let $n\ge N(\ell)$. If $G\in\mathcal G(n,\ell)$ satisfies $E(G)\le3/n$, then $G$ is obtained from $K_{2,\ell+1}$ by attaching all remaining $n-\ell-3$ vertices as leaves to the two vertices in its part of size two. The numbers of leaves at these two hubs need not be equal. The hubs are nonadjacent, and each has degree at least $2n/15$. Stance: repo-derived.

**Proof.** Put $K=\ell+14$ and $m=n-1+\ell$. The threshold gives

$$
n\ge30K^2\ge6750>\frac{3375}{2},\qquad
n>5(\ell-1),\qquad n>\ell-1.
$$

For the latter two inequalities it suffices to note that

$$
30(\ell+14)^2-5(\ell-1)=30\ell^2+835\ell+5885>0.
$$

For $0\le r\le1$, rationalization gives

$$
g(r):=\sqrt{1+r^2}-1
=\frac{r^2}{\sqrt{1+r^2}+1},\qquad
\frac25r^2\le g(r)\le\frac12r^2.
$$

Indeed, the denominator is at least $2$ and at most $1+\sqrt2<5/2$. Each edge cost is nonnegative and is a summand of $E(G)$. Thus, for every edge $uv$,

$$
\left(\frac{\min(d_u,d_v)}{\max(d_u,d_v)}\right)^2
\le\frac{15}{2n}<1.
$$

Orient every edge from its endpoint of smaller degree to its endpoint of larger degree. The inequality excludes equal-degree endpoints. A sink means a vertex of outgoing degree zero, and a source means a vertex of incoming degree zero. Since $G$ is connected and $n>1$, every vertex has positive degree.

Let $S$ be the set of sinks, $s=|S|$, and let $k_v$ be the outgoing degree of $v$. A vertex of maximum degree is a sink, so $s\ge1$. If a sink has degree $D$, every incident edge contributes at least $2/(5D^2)$, because its other endpoint has positive degree at most $D$. Consequently

$$
\frac3n\ge E(G)\ge\frac{2}{5D},\qquad D\ge\frac{2n}{15}.
$$

The sinks are independent: an edge between two of them would give one an outgoing edge. Hence each edge is incident to at most one sink, and

$$
\frac{2ns}{15}\le\sum_{v\in S}d_v\le m<2n.
$$

It follows that $s\le14$. Counting outgoing edges once gives the exact identity

$$
\sum_v(k_v-1)=m-n=\ell-1,
\qquad
\sum_{v:k_v\ge2}(k_v-1)=\ell-1+s.
$$

For every vertex with $k_v\ge2$ this implies $k_v\le\ell+s\le K$; vertices with outgoing degree zero or one satisfy the same bound.

Suppose that some vertex $v$ has both an incoming and an outgoing edge. Write $d=d_v$, $k=k_v\le K$ and $j=d-k\ge1$ for its incoming degree. An outgoing edge joins it to a vertex of degree at most $n-1$, so the edge-ratio bound yields

$$
d\le(n-1)\sqrt{\frac{15}{2n}}<\sqrt{\frac{15n}{2}}.
$$

Each incoming edge contributes at least $2/(5d^2)$. If $d<2K$, even one incoming edge gives

$$
E(G)\ge\frac{2}{5d^2}>\frac1{10K^2}\ge\frac3n,
$$

a contradiction. If $d\ge2K$, then $j=d-k\ge d/2$, whence

$$
E(G)\ge\frac{2j}{5d^2}\ge\frac1{5d}
>\frac1{5\sqrt{15n/2}}>\frac3n.
$$

The last inequality is equivalent to $n>3375/2$. This is again a contradiction. Therefore every vertex is either a source or a sink, and every edge joins a source to a sink.

In particular, each edge meets exactly one sink, so $\sum_{v\in S}d_v=m$. Summing the lower estimate on the edges at each sink and applying Cauchy–Schwarz to these actual degrees gives

$$
E(G)\ge\frac25\sum_{v\in S}\frac1{d_v}
\ge\frac{2s^2}{5m}.
$$

If $s\ge3$, then

$$
E(G)\ge\frac{18}{5m}>\frac3n,
$$

where the strict inequality is equivalent to $n>5(\ell-1)$. If $s=1$, simplicity and connectedness force every other vertex to be a leaf at the single sink, making $G$ a star and $\ell=0$. Thus $s=2$.

Every source now has degree one or two. Let $q$ be the number of sources of degree two. Summing degrees on the source side of this bipartition gives

$$
m=(n-2-q)+2q=n-2+q,
\qquad q=\ell+1.
$$

Each such source is adjacent to both sinks; all other sources are leaves at one sink. This is exactly the asserted graph, and the lower bounds on the hub degrees were proved above. ∎

## 8. The unique eventual minimizer

**Definition 8.1 (Analytic hub contribution).** For $x>0$, $k\in\{1,2\}$ and an integer $b\ge2$, put

$$
f_k(x)=\sqrt{1+\frac{k^2}{x^2}}-1,\qquad
M_b(x)=(x-b)f_1(x)+bf_2(x).
$$

In a graph consisting of $K_{2,b}$ and leaves attached only to its two hubs, a hub of degree $D\ge b$ has $D-b$ incident leaf edges and $b$ incident edges to degree-two vertices. Its contribution to $E$ is therefore $M_b(D)$. Stance: repo-derived.

**Theorem 8.2 (Unique minimizer beyond a sufficient threshold).** For every integer $\ell\ge1$ and every $n\ge N(\ell)=30(\ell+14)^2$, the graph $H_{n,\ell}$ of Definition 4.1 is the unique minimizing isomorphism class in $\mathcal G(n,\ell)$. Equivalently, for every $G\in\mathcal G(n,\ell)$,

$$
\Phi(G)\ge\Phi(H_{n,\ell}),
$$

with equality if and only if $G\cong H_{n,\ell}$. This determines the eventual minimizer structure asked for in Open question 5.2; $N(\ell)$ is a sufficient threshold, without a claim of optimality. Stance: repo-derived.

**Cited facts attached to Theorem 8.2.** The unicyclic comparison in Theorem 4.5, and hence its implication for the unicyclic part of Corollary 4.6, is literature-attested by A. Ali, K. C. Das and A. A. Attiya, *Bond incident degree indices of fixed-order unicyclic graphs*, Discrete Math. Lett. 16 (2025), 135–142, DOI 10.47443/dml.2025.192, Remark 2.3: their comparison holds for every $n\ge7$, and their reported finite minima concern $4\le n\le10$. The two-hub construction is Definition 4.1; its specialization $n=5\ell+7$, with $2(\ell+1)$ leaves at each hub, is also the construction in A. M. Albalahi, *On Two Conjectures Concerning the Hyperbolic Sombor Index and Its Counterpart*, Discrete Math. Lett. 18 (2026), 122–128, DOI 10.47443/dml.2026.217, proof of Proposition 2.1. Those comparisons and that construction are prior results. Theorem 8.2 concerns the global CDSO minimum and its equality class; the CDSO theorem in Albalahi's Theorem 2.2 and the bicyclic classification in N. Smirnov, *Bicyclic Graphs with Maximum Complementary Diminished Sombor Index*, Discrete Math. Lett. 18 (2026), 100–106, DOI 10.47443/dml.2026.164, Theorem 2.1, concern maxima.

**Proof.** We use the existing construction and estimate from Definition 4.1 and Lemma 4.2. Since

$$
N(\ell)-(8\ell+22)=30\ell^2+832\ell+5858>0,
$$

our range has $n\ge8\ell+22$, and

$$
3(n+\ell-2)^2-2n(n+7\ell+5)
=n(n-8\ell-22)+3(\ell-2)^2\ge0.
$$

Consequently Lemma 4.2 gives

$$
E(H_{n,\ell})\le\frac{2(n+7\ell+5)}{(n+\ell-2)^2}\le\frac3n.
$$

If $E(G)>3/n$, then $E(G)>E(H_{n,\ell})$. Otherwise Theorem 7.1 places $G$ in the two-hub family. Put $b=\ell+1$ and denote its hub degrees by $D_1,D_2$. They satisfy

$$
D_1,D_2\ge b,\qquad D_1+D_2=m=n-1+\ell,\qquad
E(G)=M_b(D_1)+M_b(D_2).
$$

We prove that $M_b$ is strictly convex on $(0,\infty)$. Since $xf_1(x)=\sqrt{x^2+1}-x$, differentiation gives

$$
f_k''(x)=\frac{k^2(3x^2+2k^2)}{x^3(x^2+k^2)^{3/2}},
\qquad
M_b''(x)=\frac1{(x^2+1)^{3/2}}+b\bigl(f_2''(x)-f_1''(x)\bigr).
$$

For each fixed $x>0$, define

$$
Q_x(t)=\frac{t(3x^2+2t)}{(x^2+t)^{3/2}}\qquad(t>0).
$$

Its derivative is

$$
Q_x'(t)=\frac{6x^4+5x^2t+2t^2}{2(x^2+t)^{5/2}}>0.
$$

As $f_k''(x)=Q_x(k^2)/x^3$, this proves $f_2''(x)>f_1''(x)$ and hence $M_b''(x)>0$ for every $x>0$.

If the integer hub degrees satisfy $D_2\ge D_1+2$, strict increase of $M_b'$ gives

$$
M_b(D_2)-M_b(D_2-1)
>M_b(D_1+1)-M_b(D_1).
$$

For example, integrate the pointwise strict inequality $M_b'(D_2-1+t)>M_b'(D_1+t)$ over $0\le t\le1$. Since $D_2>b$, at least one leaf is attached to the second hub. Moving one such leaf to the first hub is an admissible graph operation and strictly decreases $E$. The same reasoning applies with the hubs exchanged. Thus the minimizing unordered degree pair is uniquely

$$
\{D_1,D_2\}=\left\{\left\lfloor\frac m2\right\rfloor,
\left\lceil\frac m2\right\rceil\right\}.
$$

This pair is admissible because $m=2b+(n-\ell-3)\ge2b$. Subtracting $b$ from each degree yields exactly the balanced leaf counts of Definition 4.1. For specified leaf counts every graph in the family is isomorphic to the same graph, and exchanging the two hubs exchanges the counts. This proves both the minimum and uniqueness up to isomorphism within the family. Theorem 7.1 and the strict comparison for $E(G)>3/n$ make the conclusion global. Finally, $\Phi=m+E$ with the same $m$ throughout $\mathcal G(n,\ell)$, so the comparisons and equality statement hold for $\Phi$ as well. ∎

## 9. The sharp limiting constant and structural stability

**Lemma 9.1 (Uniform error for a hub contribution).** For the functions of Definition 8.1, every $x>0$ and integer $b\ge2$ satisfy

$$
-\frac1{8x^3}\le M_b(x)-\frac1{2x}\le\frac{3b}{2x^2}.
$$

Consequently, if a graph in the two-hub family of Theorem 7.1 has hub degrees $D_1,D_2\ge2n/15$ and $b=\ell+1$, then

$$
E(G)=\frac12\left(\frac1{D_1}+\frac1{D_2}\right)+R,
\qquad
-\frac{3375}{32n^3}\le R\le\frac{675b}{4n^2}.
$$

Stance: repo-derived.

**Proof.** Rationalization gives the exact identities

$$
xf_1(x)=\frac1{\sqrt{x^2+1}+x},\qquad
\frac1{2x}-xf_1(x)
=\frac1{2x(\sqrt{x^2+1}+x)^2},
$$

and

$$
f_2(x)-f_1(x)
=\frac{3}{x^2\left(\sqrt{1+4/x^2}+\sqrt{1+1/x^2}\right)}.
$$

The first difference lies in $[0,1/(8x^3)]$, since $\sqrt{x^2+1}+x\ge2x$; the second lies in $[0,3/(2x^2)]$. Now use $M_b(x)=xf_1(x)+b(f_2(x)-f_1(x))$. Summing the resulting bounds at $D_1,D_2$ proves the second assertion, because

$$
\frac18\left(\frac1{D_1^3}+\frac1{D_2^3}\right)
\le\frac{3375}{32n^3},\qquad
\frac{3b}{2}\left(\frac1{D_1^2}+\frac1{D_2^2}\right)
\le\frac{675b}{4n^2}.
$$

∎

**Theorem 9.2 (Limit and exact eventual membership of asymptotically optimal sequences).** Fix an integer $\ell\ge1$, and use the notation $E^\ast(n,\ell)$ of Proposition 4.7. Then

$$
\lim_{n\to\infty}nE^\ast(n,\ell)=2.
$$

Furthermore, let $G_n\in\mathcal G(n,\ell)$ for every sufficiently large integer $n$, and suppose

$$
nE(G_n)\longrightarrow2.
$$

Then, for all sufficiently large $n$, $G_n$ is exactly $K_{2,\ell+1}$ with all remaining vertices attached as leaves only to its two nonadjacent hubs. If $D_{1,n},D_{2,n}$ are the hub degrees, in either order, then

$$
\frac{D_{1,n}}n\longrightarrow\frac12,\qquad
\frac{D_{2,n}}n\longrightarrow\frac12.
$$

In particular these conclusions apply whenever $E(G_n)-E^\ast(n,\ell)=o(1/n)$. Exact equality or a bounded difference between the two leaf counts is not required of these sequences. All limits in this theorem keep $\ell$ fixed. Stance: repo-derived.

**Proof.** By Theorem 8.2, for all $n\ge N(\ell)$ the minimum is attained at $H_{n,\ell}$. Its hub degrees are $\lfloor m/2\rfloor$ and $\lceil m/2\rceil$, where $m=n-1+\ell$, and each divided by $n$ tends to $1/2$. We have already shown $E(H_{n,\ell})\le3/n$, so Theorem 7.1 supplies the degree bounds needed in Lemma 9.1. That lemma yields

$$
nE^\ast(n,\ell)
=\frac12\left(\frac n{\lfloor m/2\rfloor}
+\frac n{\lceil m/2\rceil}\right)+O_\ell(1/n)
\longrightarrow2.
$$

For the general sequence, $nE(G_n)\to2$ implies $E(G_n)\le3/n$ eventually. Since $\ell$ is fixed, also $n\ge N(\ell)$ eventually, and Theorem 7.1 proves the exact eventual membership assertion. Drop the subscript $n$ from the hub degrees and put

$$
\delta_n=\frac{D_1-D_2}{m},\qquad
D_1+D_2=m,\qquad |\delta_n|<1.
$$

Lemma 9.1 supplies a remainder $R_n$ with $nR_n\to0$ and gives

$$
nE(G_n)-nR_n
=\frac n2\left(\frac1{D_1}+\frac1{D_2}\right)
=\frac{2n/m}{1-\delta_n^2}.
$$

The left side tends to $2$, and $2n/m\to2$. Thus

$$
1-\delta_n^2
=\frac{2n/m}{nE(G_n)-nR_n}\longrightarrow1,
\qquad \delta_n\longrightarrow0.
$$

It follows that $D_i/n=(m/(2n))(1\pm\delta_n)\to1/2$. Finally, if $E(G_n)-E^\ast(n,\ell)=o(1/n)$, the first assertion implies $nE(G_n)\to2$, proving the stated consequence. ∎

**Open question 9.3 (Least thresholds and small orders).** Theorem 8.2 supplies an eventual minimizer, and Theorem 9.2 supplies the exact limit in Open question 5.2, extending the scope described in Remark 5.1 and sharpening the window of Proposition 4.7. For each fixed $\ell$, determine the least threshold from which $H_{n,\ell}$ is always the unique minimizing isomorphism class and determine the minimizers at the smaller admissible orders. The least threshold $n_0(\ell)$ for exclusion of a universal vertex and the initial-segment question in Open question 5.2 remain separate questions. The sufficient bound $N(\ell)$ does not settle these exact thresholds or the small orders; no stability assertion for varying $\ell=\ell(n)$ is made here.

## 追加锚（本行以下为增补区）

## 10. A linear range for rigidity and the exact minimum

**Theorem 10.1 (Rigidity with a linear cyclomatic restriction).** Let $\ell\ge1$ and $n\ge453$ be integers with $n>5(\ell-1)$. If $G\in\mathcal G(n,\ell)$ satisfies $E(G)\le3/n$, then $G$ is obtained from $K_{2,\ell+1}$ by attaching all remaining $n-\ell-3$ vertices as leaves to its two nonadjacent hubs. Each hub has degree at least $2n/15$.

**Proof.** Write $m=n-1+\ell$ and use the edge-cost estimate from the proof of Theorem 7.1:

$$
\frac25r^2\le g(r)=\sqrt{1+r^2}-1\le\frac12r^2
\qquad(0\le r\le1).
$$

Since the cost of any edge is a nonnegative summand of $E(G)$, its smaller-to-larger endpoint degree ratio is at most

$$
\delta=\sqrt{\frac{15}{2n}}<1.
$$

Thus every edge has endpoints of different degrees and can be oriented from smaller degree to larger degree. Degrees strictly increase along directed paths, so their vertices are distinct. Connectedness gives positive degree at every vertex.

There is no directed path $v_0\to v_1\to v_2\to v_3$ of three edges. Such a path would give

$$
1\le d(v_0)\le\delta^3d(v_3)\le\delta^3(n-1)<\delta^3n,
\qquad
(\delta^3n)^2=\frac{3375}{8n}<1.
$$

The last strict inequality already holds for $n\ge422$, since $8\cdot422-3375=1$.

Let $S$ be the sink set and put $s=|S|$. A maximum-degree vertex is a sink, so $s\ge1$. The sinks form an independent set, and their incident edge sets are pairwise disjoint. At a sink of degree $D$, each incident edge contributes at least $2/(5D^2)$, since the other endpoint has degree at least one. Consequently

$$
E(G)\ge\frac{2}{5D},\qquad D\ge\frac{2n}{15}.
$$

Summing these contributions over sinks and applying Cauchy–Schwarz to their actual degrees gives, before any restriction on the remaining vertices,

$$
E(G)\ge\frac25\sum_{v\in S}\frac1{d(v)}
\ge\frac{2s^2}{5\sum_{v\in S}d(v)}
\ge\frac{2s^2}{5m}.
$$

Here $\sum_{v\in S}d(v)\le m$ follows from disjointness of the incident edge sets. The hypothesis $n>5(\ell-1)$ gives $m<6n/5$. If $s\ge3$, the preceding bound yields $E(G)\ge18/(5m)>3/n$, a contradiction. Hence $1\le s\le2$.

Suppose that a vertex $v$ has both an incoming and an outgoing edge, and write $d=d(v)$ and $k$ for its outgoing degree. Every outgoing neighbor of $v$ must be a sink: otherwise an incoming edge at $v$, that outgoing edge, and an outgoing edge at its endpoint form a forbidden directed path of three edges. Simplicity therefore gives $k\le s\le2$.

One incoming edge and the ratio bound imply $1\le\delta d$, while one outgoing edge gives $d\le\delta(n-1)$. Thus

$$
\sqrt{\frac{2n}{15}}\le d<R:=\sqrt{\frac{15n}{2}},
\qquad d>4.
$$

The incoming degree is $d-k\ge d-2$. Each incoming edge contributes at least $2/(5d^2)$, so

$$
E(G)\ge\frac{2(d-2)}{5d^2}
>\frac{2(R-2)}{5R^2}
=\frac{4(R-2)}{75n}
>\frac3n.
$$

The first strict inequality uses the strict decrease of $(x-2)/x^2$ on $x>4$, whose derivative is $(4-x)/x^3$. The final strict inequality is equivalent to $R>233/4$, or $120n>233^2$; at the least permitted order its integer margin is $120\cdot453-233^2=71>0$. This contradiction excludes every vertex with both kinds of incident edge.

Every vertex is therefore a source or a sink, and each edge joins the two classes. The adjacency reconstruction at the end of the proof of Theorem 7.1 now applies: it uses only this bipartition, simplicity, connectedness, $\ell\ge1$, and the edge count. Explicitly, one sink would make the graph a star and force $\ell=0$. There are therefore two sinks. Every source has degree one or two; if $q$ sources have degree two, then

$$
m=(n-2-q)+2q=n-2+q,
\qquad q=\ell+1.
$$

Each degree-two source is adjacent to both sinks, and every other source is a leaf at one sink. This recovers the asserted complete adjacency structure. The hub degree lower bounds were established before the exclusion of mixed vertices. ∎

**Theorem 10.2 (Unique minimum in a linear range).** Let $\ell\ge1$ and

$$
n\ge\max\{453,\,8\ell+22\}.
$$

Then $H_{n,\ell}$ of Definition 4.1 is the unique minimizing isomorphism class for $\Phi$ in $\mathcal G(n,\ell)$. With $b=\ell+1$, $m=n-1+\ell$, and $M_b$ as in Definition 8.1, the exact minimum excess is

$$
E^\ast(n,\ell)
=M_b\!\left(\left\lfloor\frac m2\right\rfloor\right)
+M_b\!\left(\left\lceil\frac m2\right\rceil\right).
$$

In particular $\Phi(G)\ge m+E^\ast(n,\ell)$, with equality if and only if $G\cong H_{n,\ell}$. The constants $453$ and $8\ell+22$ are sufficient thresholds; their optimality is not asserted.

**Proof.** The range implies $n\ge\ell+3$ and $n>5(\ell-1)$. Thus Definition 4.1 gives an actual connected simple graph $H_{n,\ell}$ in the required class. Lemma 4.2 and the identity

$$
3(n+\ell-2)^2-2n(n+7\ell+5)
=n(n-8\ell-22)+3(\ell-2)^2\ge0
$$

give $E(H_{n,\ell})\le3/n$. Every $G$ with $E(G)>3/n$ is strictly worse than this graph. Every remaining $G$ satisfies Theorem 10.1 and hence has two nonadjacent hubs with degrees

$$
D_1,D_2\ge b,\qquad D_1+D_2=m,\qquad
E(G)=M_b(D_1)+M_b(D_2).
$$

Use the analytic calculation in the proof of Theorem 8.2, which holds for every $x>0$ and is independent of that theorem's threshold:

$$
M_b''(x)=\frac1{(x^2+1)^{3/2}}
+b\bigl(f_2''(x)-f_1''(x)\bigr)>0.
$$

If $D_2\ge D_1+2$, the second hub has a leaf because $D_2>b$. Moving one such leaf to the first hub keeps the graph connected and simple with the same order and size. Strict convexity, by the leaf-exchange argument of Theorem 8.2, strictly decreases the excess. The reversed inequality is treated by exchanging the hubs. The unique minimizing unordered degree pair is therefore $\{\lfloor m/2\rfloor,\lceil m/2\rceil\}$. It is realizable, since $m-2b=n-\ell-3\ge0$, and its leaf counts are precisely those of $H_{n,\ell}$. Every other pair admits finitely many strictly decreasing leaf exchanges to this pair. Specifying the two leaf counts specifies the graph up to isomorphism and hub exchange. This proves the exact value and the global equality class. ∎

**Mathematical citations for Theorem 10.2.** The index and the universal-vertex minimizer assertion are those of Albalahi–Das–Ali–Barman–Hamza, DOI 10.47443/dml.2025.176, §1 and Conjecture 4.1. The unicyclic comparison for all $n\ge7$ is Ali–Das–Attiya, DOI 10.47443/dml.2025.192, Remark 2.3. At $n=5\ell+7$ the construction of Definition 4.1 is the graph with $2(\ell+1)$ leaves at each hub used by Albalahi, DOI 10.47443/dml.2026.217, proof of Proposition 2.1. That proposition excludes universal vertices at those orders; it does not identify the global minimum. Theorem 2.2 of that paper and Theorem 2.1 of Smirnov, DOI 10.47443/dml.2026.164, determine CDSO maxima in their respective classes.

## 11. Uniform hub expansion and quantitative stability

**Lemma 11.1 (A two-term expansion uniform in the cyclomatic number).** For the functions of Definition 8.1 and every real $x\ge b\ge2$ with $b$ integral,

$$
-\frac{x+15b}{8x^4}
\le M_b(x)-\left(\frac1{2x}+\frac{3b}{2x^2}\right)
\le0.
$$

In particular the absolute value of this error is at most $2/x^3$. If $G$ is a graph consisting of $K_{2,b}$ and leaves attached only to its two hubs, with order $n$ and hub degrees $D_i\ge2n/15$, then

$$
E(G)=\sum_{i=1}^2\left(\frac1{2D_i}+\frac{3b}{2D_i^2}\right)+R_G,
\qquad
-\frac{3375}{2n^3}\le R_G\le0.
$$

**Proof.** Use the elementary square-root estimate from the proof of Theorem 4.5. For completeness, if $z\ge0$ and $y=\sqrt{1+z}-1$, then $z=2y+y^2$ and

$$
0\le\frac z2-y=\frac{y^2}{2}\le\frac{z^2}{8},
$$

where the last inequality follows from $0\le y\le z/2$. Apply this estimate to $f_1(x)$ and $f_2(x)$ with $z=1/x^2$ and $z=4/x^2$. The weights $x-b$ and $b$ in $M_b(x)$ are nonnegative. Their quadratic terms sum to

$$
\frac{x-b}{2x^2}+\frac{4b}{2x^2}
=\frac1{2x}+\frac{3b}{2x^2},
$$

and the total error has absolute value at most

$$
\frac{x-b+16b}{8x^4}
=\frac{x+15b}{8x^4}\le\frac2{x^3}.
$$

For the graph assertion, the actual edge multiplicities at a hub are $D_i-b$ and $b$, as in Definition 8.1, and $D_i\ge b$. Thus $E(G)=M_b(D_1)+M_b(D_2)$. Sum the error estimates and use

$$
2\left(D_1^{-3}+D_2^{-3}\right)
\le4\left(\frac{15}{2n}\right)^3
=\frac{3375}{2n^3}.
$$

∎

**Theorem 11.2 (A finite bound for hub imbalance).** Let $\ell\ge1$, $n\ge\max\{453,8\ell+22\}$, and let $G\in\mathcal G(n,\ell)$ be any graph obtained from $K_{2,\ell+1}$ by attaching its remaining vertices as leaves only to its two hubs. If their degrees are $D_1,D_2$, then

$$
\left(\frac{D_1-D_2}{n}\right)^2
\le4n\bigl(E(G)-E^\ast(n,\ell)\bigr)+\frac1{n^2}.
$$

Consequently the same estimate holds for every $G\in\mathcal G(n,\ell)$ with $E(G)\le3/n$, whose hub structure is supplied by Theorem 10.1.

**Proof.** Put $b=\ell+1$, $c=m/2$, and $t=|D_1-D_2|/2$. Let $\varepsilon=0$ if $m$ is even and $\varepsilon=1/2$ if $m$ is odd. The degrees are integers with sum $m$, so $t\ge\varepsilon$. Simplicity of this actual family gives

$$
b\le D_i\le n-2.
$$

The interval $[c-t,c+t]$ therefore lies in $[b,n-2]$. On that interval, the curvature calculation used in Theorem 8.2 gives

$$
M_b''(x)\ge(x^2+1)^{-3/2}\ge\frac1{n^3},
$$

since $x^2+1\le(n-2)^2+1<n^2$. Define $L(u)=M_b(c+u)+M_b(c-u)$ for $0\le u\le t$. Then

$$
L'(u)=M_b'(c+u)-M_b'(c-u)
=\int_{c-u}^{c+u}M_b''(x)\,dx
\ge\frac{2u}{n^3}.
$$

Theorem 10.2 identifies $E^\ast(n,\ell)=L(\varepsilon)$, whereas $E(G)=L(t)$. Integrating from $\varepsilon$ to $t$ yields

$$
E(G)-E^\ast(n,\ell)\ge\frac{t^2-\varepsilon^2}{n^3}.
$$

Multiply by $4n$ and use $4t^2=(D_1-D_2)^2$ and $4\varepsilon^2\le1$. The final assertion follows from Theorem 10.1. ∎

## 12. Limits with varying cyclomatic number

**Theorem 12.1 (Positive-density limit and exact eventual family membership).** Let $\ell_n\ge1$ be integers such that $\ell_n/n\to\alpha$ as $n\to\infty$, where $0\le\alpha<1/8$. Then

$$
\lim_{n\to\infty}nE^\ast(n,\ell_n)
=F(\alpha):=\frac2{1+\alpha}+\frac{12\alpha}{(1+\alpha)^2}.
$$

The same conclusion holds at $\alpha=1/8$ under the additional assumption that $n\ge8\ell_n+22$ for all sufficiently large $n$.

Under either set of assumptions, if $G_n\in\mathcal G(n,\ell_n)$ and

$$
n\bigl(E(G_n)-E^\ast(n,\ell_n)\bigr)\longrightarrow0,
$$

then for all sufficiently large $n$, $G_n$ is exactly $K_{2,\ell_n+1}$ with all remaining vertices attached as leaves only to its two nonadjacent hubs. Their degrees, in either order, satisfy

$$
\frac{D_{1,n}}n\longrightarrow\frac{1+\alpha}{2},
\qquad
\frac{D_{2,n}}n\longrightarrow\frac{1+\alpha}{2}.
$$

These conclusions also hold if the scaled-gap assumption is replaced by $nE(G_n)\to F(\alpha)$. The assertion is proportional balance; it does not assert eventual equality or a bounded difference of the two leaf counts. The density interval and its additional endpoint assumption are sufficient conditions.

**Proof.** If $\alpha<1/8$, then

$$
\frac{n-8\ell_n-22}{n}\longrightarrow1-8\alpha>0,
$$

so $n\ge\max\{453,8\ell_n+22\}$ eventually. At the endpoint this follows from its explicit additional assumption. Theorem 10.2 therefore makes $H_{n,\ell_n}$ the unique minimizer eventually. Its actual hub degrees are $\lfloor m_n/2\rfloor$ and $\lceil m_n/2\rceil$, where $m_n=n-1+\ell_n$, and its excess is at most $3/n$. Theorem 10.1 gives the lower bounds on the two degrees needed for Lemma 11.1.

Put $b_n=\ell_n+1$, $\beta_n=b_n/n$, and $a_{i,n}=D_{i,n}/n$ for the degrees of this balanced graph. Lemma 11.1 gives

$$
nE^\ast(n,\ell_n)
=\sum_{i=1}^2\left(\frac1{2a_{i,n}}+\frac{3\beta_n}{2a_{i,n}^2}\right)+\rho_n,
\qquad
-\frac{3375}{2n^2}\le\rho_n\le0.
$$

Since $a_{i,n}\to(1+\alpha)/2$ and $\beta_n\to\alpha$, this proves the stated limit. Retaining the term involving $\beta_n$ is essential when $\alpha>0$.

On $[0,1/8]$,

$$
F'(\alpha)=\frac{10-14\alpha}{(1+\alpha)^3}>0,
\qquad
F(1/8)=\frac{80}{27}<3.
$$

Thus the scaled-gap assumption gives $nE(G_n)\to F(\alpha)<3$, so $E(G_n)<3/n$ eventually. Theorem 10.1 applies to these actual graphs and gives the exact eventual family membership. Theorem 11.2 then implies

$$
\left(\frac{D_{1,n}-D_{2,n}}n\right)^2
\le4n\bigl(E(G_n)-E^\ast(n,\ell_n)\bigr)+\frac1{n^2}
\longrightarrow0.
$$

Together with $(D_{1,n}+D_{2,n})/n=m_n/n\to1+\alpha$, this proves both degree limits. If instead $nE(G_n)\to F(\alpha)$ is assumed, subtracting the proved minimum limit gives the scaled-gap condition and the same argument applies. ∎

## 追加锚（本行以下为增补区）
