# CDSO minimizers without a universal vertex for every cyclomatic number

This volume is reference input; nothing in it is kernel-verified. Its text is append-only: corrections and additions belong after the final append anchor.

## 1. Scope

The complementary diminished Sombor index of a graph is $\sum_{uv\in E}\sqrt{d_u^2+d_v^2}/\max(d_u,d_v)$. Among connected graphs of order $n$ with cyclomatic number $\ell\ge1$, this volume shows that a graph with a universal vertex pays an excess over the edge count that is bounded below independently of $n$, while a two-hub graph without a universal vertex has excess of order $1/n$. Consequently, for every $\ell\ge1$ and every $n\ge3\ell+9$, no minimizer of the index has a universal vertex; for $\ell=1$ the same holds for every $n\ge7$. The minimum excess over the edge count lies between two explicit functions of order $1/n$.

## 2. Notation and cited facts

**Cited facts.** The following are taken from A. M. Albalahi, S. Das, A. Ali, J. Barman, A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*, Discrete Math. Lett. 16 (2025) 108–115, DOI 10.47443/dml.2025.176; preprint arXiv:2510.24809v1.

- (a) Definition, Sec. 1 (journal p. 109; arXiv v1 Sec. 1): for a graph $G$ with edge set $E$ and degrees $d(w)$, the complementary diminished Sombor (CDSO) index is ${}^c\mathrm{DSO}(G)=\sum_{uv\in E}\sqrt{d(u)^2+d(v)^2}/\max\{d(u),d(v)\}$.
- (b) Sec. 4, Concluding remarks (journal p. 115): the cyclomatic number of a graph is the minimum number of edges whose removal makes the graph acyclic, and Conjecture 4.1 reads: “A graph minimizing (maximizing, respectively) the CDSO index (HSO index, respectively) among fixed-order connected graphs with cyclomatic number $\ell(\ge1)$ has a vertex adjacent to all other vertices.” In arXiv v1 the same assertion appears as prose in Sec. 4, Concluding Remarks, without a conjecture number.

**Convention 2.1 (Graph classes and excess).** Graphs are finite and simple. For integers $n\ge1$ and $\ell\ge0$ let $\mathcal G(n,\ell)$ be the set of connected graphs on the vertex set $\{1,\dots,n\}$ with cyclomatic number $\ell$. Write $\Phi(G)={}^c\mathrm{DSO}(G)$ and $m=m(G)$ for the number of edges. For $G\in\mathcal G(n,\ell)$ we have $m=n-1+\ell$: an acyclic spanning subgraph of a graph on $n$ vertices has at most $n-1$ edges, so at least $m-n+1$ edges must be removed, and removing the edges outside a spanning tree of the connected graph $G$ removes exactly $m-n+1$. The excess of $G$ is $E(G)=\Phi(G)-m$. A vertex is universal if it is adjacent to all other vertices. A minimizer in $\mathcal G(n,\ell)$ is a graph $G\in\mathcal G(n,\ell)$ with $\Phi(G)\le\Phi(G')$ for all $G'\in\mathcal G(n,\ell)$; when $\mathcal G(n,\ell)$ is nonempty a minimizer exists, since the set is finite. Stance: repo-derived (notation fixed in this volume; the identity $m=n-1+\ell$ is proved in place).

**Convention 2.2 (Edge cost).** For positive integers $a,b$ put $\varphi(a,b)=\sqrt{a^2+b^2}/\max(a,b)=\sqrt{1+r^2}$ with $r=\min(a,b)/\max(a,b)\in(0,1]$, so $\Phi(G)=\sum_{uv\in E}\varphi(d_u,d_v)$ and $E(G)=\sum_{uv\in E}(\varphi(d_u,d_v)-1)$. For integers $D\ge k\ge1$ put $\psi(D,k)=\varphi(D,k)-1=\sqrt{1+k^2/D^2}-1$. Finally

$$
c_\ell=\ell\left(\frac{\sqrt{(\ell+1)^2+4}}{\ell+1}-1\right)\qquad(\ell\ge1).
$$

Stance: repo-derived (notation fixed in this volume).

## 3. The universal-vertex floor

**Lemma 3.1 (Square-root bounds).** For every real $x\ge0$,

$$
\frac x2-\frac{x^2}8\le\sqrt{1+x}-1\le\frac x2,\qquad \sqrt{1+x}-1=\frac{x}{\sqrt{1+x}+1}\ge\frac{2x}{4+x},
$$

and for $0\le x\le1$ also $\sqrt{1+x}-1\ge(\sqrt2-1)x$. Stance: repo-derived.

**Proof.** Put $y=\sqrt{1+x}-1\ge0$, so $x=2y+y^2$. Then $x/2=y+y^2/2\ge y$, and $x/2-x^2/8=y+y^2/2-(4y^2+4y^3+y^4)/8=y-y^3/2-y^4/8\le y$. The identity $y=x/(\sqrt{1+x}+1)$ follows from $(\sqrt{1+x}-1)(\sqrt{1+x}+1)=x$, and $\sqrt{1+x}+1\le2+x/2$ by the upper bound, giving $y\ge x/(2+x/2)=2x/(4+x)$. The function $x\mapsto\sqrt{1+x}-1$ is concave on $[0,1]$ and takes the values $0$ and $\sqrt2-1$ at the endpoints, so it lies above the chord $(\sqrt2-1)x$ there. ∎

**Lemma 3.2 (Floor for a universal vertex).** Let $\ell\ge1$, $n\ge3$ and $G\in\mathcal G(n,\ell)$ have a universal vertex. Then $E(G)\ge c_\ell$, and

$$
c_\ell\ge\frac{2\ell}{(\ell+1)^2+1}.
$$

Stance: suspected-novel (see §6).

**Proof.** Let $h$ be a universal vertex. The $n-1$ edges at $h$ each have $\varphi\ge1$. The remaining $m-(n-1)=\ell$ edges avoid $h$. For $u\ne h$ let $e_u$ be the number of these $\ell$ edges at $u$; then $d_u=1+e_u$ and $e_u\le\ell$. If $uv$ is one of the $\ell$ edges avoiding $h$, then $e_u,e_v\ge1$, so $2\le d_u,d_v\le\ell+1$ and $r=\min(d_u,d_v)/\max(d_u,d_v)\ge2/(\ell+1)$. Since $\sqrt{1+r^2}$ increases in $r$, each such edge has $\varphi(d_u,d_v)\ge\sqrt{(\ell+1)^2+4}/(\ell+1)$. Summing, $\Phi(G)\ge(n-1)+\ell\sqrt{(\ell+1)^2+4}/(\ell+1)=m+c_\ell$.

For the lower bound on $c_\ell$, apply Lemma 3.1 with $x=4/(\ell+1)^2$: $c_\ell=\ell(\sqrt{1+x}-1)\ge\ell\cdot2x/(4+x)=2\ell/((\ell+1)^2+1)$. ∎

## 4. Two-hub graphs and the main theorems

**Definition 4.1 (Two-hub graph).** Let $\ell\ge1$ and $n\ge\ell+3$, and put $p=n-\ell-3\ge0$. The graph $H_{n,\ell}$ has vertices $a,b$, $w_0,\dots,w_\ell$ and $q_1,\dots,q_p$; its edges are $aw_i$ and $bw_i$ for $0\le i\le\ell$, $aq_j$ for $1\le j\le\lfloor p/2\rfloor$, and $bq_j$ for $\lfloor p/2\rfloor<j\le p$. Stance: repo-derived (construction fixed in this volume).

**Lemma 4.2 (Two-hub graphs are admissible and cheap).** Let $\ell\ge1$ and $n\ge\ell+3$. Then $H_{n,\ell}\in\mathcal G(n,\ell)$ up to relabelling, $H_{n,\ell}$ has no universal vertex, and

$$
E(H_{n,\ell})\le\frac{2(n+7\ell+5)}{(n+\ell-2)^2}.
$$

Stance: suspected-novel (see §6).

**Proof.** The graph has $2+(\ell+1)+p=n$ vertices and $2(\ell+1)+p=n+\ell-1$ edges, and it is connected because every vertex is joined to $a$ or $b$ and $a,b$ are both joined to $w_0$. Hence its cyclomatic number is $(n+\ell-1)-n+1=\ell$ by Convention 2.1. The vertices $a$ and $b$ are not adjacent, so neither is universal; every other vertex has degree at most $2<n-1$, since $n\ge4$.

The degrees are $D_a=\ell+1+\lfloor p/2\rfloor$, $D_b=\ell+1+\lceil p/2\rceil$, $d(w_i)=2$ and $d(q_j)=1$. Let $D=\min(D_a,D_b)=D_a$. Then $D\ge\ell+1+(p-1)/2=(n+\ell-2)/2$ and $D\ge\ell+1\ge2$. Every edge joins a hub of degree at least $D$ to a vertex of degree $k\in\{1,2\}$, and by Lemma 3.1 its cost is $\psi(D_\ast,k)\le k^2/(2D_\ast^2)\le k^2/(2D^2)$, where $D_\ast\in\{D_a,D_b\}$ is the hub degree. The $2(\ell+1)$ edges with $k=2$ contribute at most $4(\ell+1)/D^2$, and the $p$ edges with $k=1$ contribute at most $p/(2D^2)$. Therefore

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

**Theorem 4.5 (The unicyclic case for every order at least seven).** Let $n\ge7$. Then $T_n\in\mathcal G(n,1)$ up to relabelling, $T_n$ has no universal vertex, every graph in $\mathcal G(n,1)$ with a universal vertex has index $\Phi(U_n)$, and $\Phi(T_n)<\Phi(U_n)$. Consequently no minimizer in $\mathcal G(n,1)$ has a universal vertex. Stance: suspected-novel for $n\ge8$ (see §6); the instance $n=7$ is repo-derived (used as a cited step; not a load-bearing item of this volume), and the proof below covers it uniformly.

**Proof.** Membership: $T_n$ has the $n$ vertices $h,x,y,z,z_1,\dots,z_{n-4}$ and $n$ edges, and it is connected, so its cyclomatic number is $1$. Its degrees are $d_h=n-2$, $d_x=3$, $d_y=2$ and $1$ for $z$ and each $z_j$; as $n\ge7$ every degree is below $n-1$, so $T_n$ has no universal vertex.

Universal-vertex graphs: if $G\in\mathcal G(n,1)$ has a universal vertex $h$, then exactly one edge avoids $h$, say $xy$; so $d_h=n-1$, $d_x=d_y=2$ and all other vertices are leaves at $h$, and $G$ is a relabelling of $U_n$. With $\psi$ from Convention 2.2,

$$
E(U_n)=(\sqrt2-1)+2\psi(n-1,2)+(n-3)\psi(n-1,1),
$$

$$
E(T_n)=\Big(\tfrac{\sqrt{13}}3-1\Big)+\Big(\tfrac{\sqrt{10}}3-1\Big)+\psi(n-2,3)+\psi(n-2,2)+(n-4)\psi(n-2,1),
$$

where the two bracketed terms are the edges $xy$ (degrees $3,2$) and $xz$ (degrees $3,1$), and $n-2\ge3$ is the larger endpoint degree on every edge at $h$. Both graphs have $n$ edges, so $\Phi(U_n)-\Phi(T_n)=E(U_n)-E(T_n)$.

Applying the lower bound of Lemma 3.1 with $x=k^2/(n-1)^2$ to $E(U_n)$ and the upper bound with $x=k^2/(n-2)^2$ to $E(T_n)$ gives

$$
E(U_n)\ge(\sqrt2-1)+\frac{n+5}{2(n-1)^2}-\frac{n+29}{8(n-1)^4},\qquad E(T_n)\le\frac{\sqrt{13}+\sqrt{10}}3-2+\frac{n+9}{2(n-2)^2}.
$$

Hence $E(U_n)-E(T_n)\ge K-g(n)$ with

$$
K=\sqrt2+1-\frac{\sqrt{13}+\sqrt{10}}3,\qquad g(n)=\frac{n+9}{2(n-2)^2}-\frac{n+5}{2(n-1)^2}+\frac{n+29}{8(n-1)^4}.
$$

From $1.41421^2<2$, $3.60556^2>13$ and $3.16228^2>10$ we get $K>2.41421-6.76784/3=47479/300000>0.1582$. Exact evaluation gives $g(7)=1129/7200<0.1569$, $g(8)=9109/86436<0.106$ and $g(9)=60579/802816<0.076$. For $n\ge10$, the inequality $4(n+5)(n-1)^2\ge n+29$ shows that the last two terms of $g(n)$ have a nonpositive sum, so $g(n)\le(n+9)/(2(n-2)^2)$; this bound decreases in $n$ for $n>2$, because its derivative is $-(n+20)/(2(n-2)^3)$, and at $n=10$ it equals $19/128<0.1485$. Thus $g(n)<K$ for every $n\ge7$, and $\Phi(T_n)<\Phi(U_n)$. Every minimizer $G^\ast$ satisfies $\Phi(G^\ast)\le\Phi(T_n)<\Phi(U_n)$, so it has no universal vertex. ∎

**Corollary 4.6 (The CDSO half of the universal-vertex assertion fails for every cyclomatic number).** For every $\ell\ge1$ there is an order $n$, namely every $n\ge3\ell+9$ and, for $\ell=1$, every $n\ge7$, such that no minimizer of the CDSO index in $\mathcal G(n,\ell)$ has a vertex adjacent to all other vertices. In particular the CDSO half of the assertion quoted in cited fact (b) is false for each fixed $\ell\ge1$. Stance: suspected-novel for $\ell\ge2$ and for $\ell=1$ with $n\ge8$ (see §6); the failure at $(n,\ell)=(7,1)$ is repo-derived (used as a cited step; not a load-bearing item of this volume).

**Proof.** Theorems 4.3 and 4.5. ∎

**Proposition 4.7 (Window for the minimum excess).** Let $\ell\ge1$, $n\ge\ell+3$, and let $E^\ast(n,\ell)=\min\{E(G):G\in\mathcal G(n,\ell)\}$. Then

$$
\frac{\sqrt2-1}{n}<E^\ast(n,\ell)\le\frac{2(n+7\ell+5)}{(n+\ell-2)^2}.
$$

In particular, for fixed $\ell$, $E^\ast(n,\ell)$ lies between $(\sqrt2-1)/n$ and $(2+o(1))/n$ as $n\to\infty$, while by Lemma 3.2 every graph with a universal vertex has excess at least $2\ell/((\ell+1)^2+1)$, independent of $n$. Stance: suspected-novel (see §6).

**Proof.** The upper bound is Lemma 4.2. For the lower bound let $G\in\mathcal G(n,\ell)$ and $uv\in E(G)$. Since $1\le\min(d_u,d_v)$ and $\max(d_u,d_v)\le n-1$, the ratio satisfies $r\ge1/(n-1)$, and Lemma 3.1 with $x=r^2\le1$ gives $\varphi(d_u,d_v)-1\ge(\sqrt2-1)r^2\ge(\sqrt2-1)/(n-1)^2$. Summing over the $m=n-1+\ell\ge n$ edges, $E(G)\ge(\sqrt2-1)n/(n-1)^2>(\sqrt2-1)/n$. ∎

## 5. Boundaries and open questions

**Remark 5.1 (What is not claimed).** The thresholds $3\ell+9$ and $7$ are sufficient conditions; this volume does not determine the least order from which minimizers lack a universal vertex, and makes no statement about orders below these thresholds, in particular none asserting that minimizers of small order have a universal vertex. It identifies no minimizer and does not assert that $H_{n,\ell}$ or $T_n$ is one. It gives no asymptotic constant for $E^\ast(n,\ell)$ beyond the window of Proposition 4.7. It does not address the HSO half of the assertion in cited fact (b), nor Conjecture 4.2 of the cited paper. Stance: repo-derived.

**Open question 5.2 (Exact thresholds and minimizer structure).** For each $\ell\ge2$, determine the least $n_0(\ell)$ such that no minimizer in $\mathcal G(n,\ell)$ has a universal vertex for all $n\ge n_0(\ell)$, and decide whether the set of orders $n$ at which some minimizer has a universal vertex is an initial segment. Determine the structure of the minimizers in $\mathcal G(n,\ell)$ and the limit of $n\,E^\ast(n,\ell)$, if it exists. Theorem 4.3 gives $n_0(\ell)\le3\ell+9$; the missing ingredient for a sharp answer is a matching lower bound on $E(G)$ for graphs without a universal vertex. Stance: repo-derived (question posed in this volume).

## 6. Sources and literature status

| Source | Exact scope and use |
| --- | --- |
| A. M. Albalahi, S. Das, A. Ali, J. Barman, A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*, Discrete Math. Lett. 16 (2025) 108–115, DOI 10.47443/dml.2025.176, Sec. 1 (p. 109) and Sec. 4 (p. 115); preprint arXiv:2510.24809v1, Secs. 1 and 4 | `literature-attested`: the definition of the CDSO index (cited fact (a)), the definition of cyclomatic number and the wording of Conjecture 4.1 (cited fact (b)). The paper proves no result about minimizers with fixed positive cyclomatic number. |
| — | `repo-derived`: Conventions 2.1, 2.2, Lemma 3.1, Definitions 4.1, 4.4, Remark 5.1, Open question 5.2; the instance $n=7$ of Theorem 4.5 and the instance $(n,\ell)=(7,1)$ of Corollary 4.6, used as cited steps and not load-bearing items of this volume. |
| — | `suspected-novel`: Lemma 3.2, Lemma 4.2, Theorem 4.3, Theorem 4.5 for $n\ge8$, Corollary 4.6 apart from the instance $(7,1)$, Proposition 4.7. Searched: the full text of the journal version and of arXiv:2510.24809v1; I. Gutman, *Survey of Sombor-type degree-based topological indices*, MATCH Commun. Math. Comput. Chem. 96 (2026) 819–837, which lists the CDSO index by its definition only; S. Akbari, A. Ali, B. Furtula, F. Movahedi, M. Rahmani Moghadam, *Revisiting the diminished Sombor index*, MATCH Commun. Math. Comput. Chem. 96 (2026), whose abstract concerns the diminished Sombor index on classes of fixed order and size; web searches combining complementary diminished Sombor index, CDSO, hyperbolic Sombor index, cyclomatic number, minimizer, universal vertex and the arXiv identifier 2510.24809. No statement of these results was found in the searched scope; this establishes no worldwide priority. |

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）
