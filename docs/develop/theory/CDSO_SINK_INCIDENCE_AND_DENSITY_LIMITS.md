# CDSO sink incidences and density limits

## 1. Graphs, orientations and hub families

**Definition 1.1 (Fixed graph class and edge cost).** All graphs are finite, simple and connected. For integers $n\ge2$ and $\ell\ge0$, write $\mathcal G(n,\ell)$ for the graphs of order $n$ with exactly $m=n-1+\ell$ edges, so their cyclomatic number is $\ell$. Degrees and neighborhoods always belong to the graph being evaluated. Write

$$
\Phi(G)=\sum_{uv\in E(G)}\frac{\sqrt{d_u^2+d_v^2}}{\max(d_u,d_v)},\qquad
E(G)=\Phi(G)-m=\sum_{uv\in E(G)}g(r_{uv}),
$$

$$
g(r)=\sqrt{1+r^2}-1,\qquad r_{uv}=\frac{\min(d_u,d_v)}{\max(d_u,d_v)},\qquad
E^\ast(n,\ell)=\min_{G\in\mathcal G(n,\ell)}E(G)
$$

when the class is nonempty. Each unordered edge occurs once. These are the conventions of [*CDSO minimizers without a universal vertex for every cyclomatic number*, §§1–9](CDSO_UNIVERSAL_VERTEX_ALL_CYCLOMATIC.md), hereafter the preceding volume. The CDSO definition is from A. M. Albalahi, S. Das, A. Ali, J. Barman and A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*, Discrete Math. Lett. 16 (2025), 108–115, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176), §1, p.109. All extremal comparisons below fix the same $n$, $\ell$ and $m$.

**Definition 1.2 (Degree orientation and sink incidences).** If every edge has unequal endpoint degrees, orient it from the smaller degree to the larger degree. A source has no incoming edge, a sink has no outgoing edge, and a mixed vertex has both. Let $R$ be the sink set, $s=|R|$, and $D_i=d_i$ for $i\in R$. Put

$$
\mathcal I_R=\{(i,v):i\in R,\ v\in N(i)\},\qquad
h(v)=|N(v)\cap R|\quad(v\notin R),
$$

$$
T_R=\sum_{v\notin R}\frac{h(v)}{d_v^2},\qquad
Q_R=\sum_{(i,v)\in\mathcal I_R}\frac{d_v^2}{D_i^2},\qquad
Q(G)=\sum_{uv\in E(G)}r_{uv}^2.
$$

The orientation strictly increases degree along every directed edge. A two-layer graph means that every edge joins a source to a sink in this orientation.

**Definition 1.3 (The full two-hub family).** For $\ell\ge1$ and $n\ge\ell+3$, put $b=\ell+1$ and $p=n-\ell-3$. Let $\mathcal B(n,\ell)$ consist of $K_{2,b}$ with all $p$ remaining vertices attached as leaves to its two vertices in the part of size two, called hubs. The two hubs are nonadjacent. Their degrees $D_1,D_2$ satisfy

$$
D_1,D_2\ge b,\qquad D_1+D_2=m=n-1+\ell.
$$

Let $H_{n,\ell}$ be the graph with leaf counts $\lfloor p/2\rfloor$ and $\lceil p/2\rceil$, exactly as in Definition 4.1 of the preceding volume. Use its Definition 8.1:

$$
f_k(x)=g(k/x),\qquad M_b(x)=(x-b)f_1(x)+bf_2(x)\quad(x>0).
$$

For every member of $\mathcal B(n,\ell)$, its actual excess is $M_b(D_1)+M_b(D_2)$.

## 2. An incidence bound before the two-layer reduction

**Theorem 2.1 (Sink-incidence lower bound).** Suppose $n\ge2$ and

$$
E(G)\le\eta<\sqrt2-1.
$$

Then the degree orientation exists, $1\le s<n$, $T_R>0$, and

$$
Q(G)\ge Q_R\ge\frac{s^2}{T_R}\ge\frac{s^2}{n-s},
$$

$$
E(G)\ge\frac{Q_R}{2+\eta}\ge\frac{s^2}{(2+\eta)T_R}
\ge\frac{s^2}{(2+\eta)(n-s)}.
$$

Every individual sink satisfies

$$
D_i\ge\frac1{(2+\eta)E(G)}.
$$

These bounds require no assumption on the cyclomatic number or on the number of edges beyond those of Definition 1.1.

**Proof.** For the cost $e=g(r)$ of any edge, $0<e\le\eta$ and

$$
r^2=e(2+e),\qquad r^2\le\eta(2+\eta)<1,\qquad
e\ge\frac{r^2}{2+\eta}.
$$

Thus adjacent degrees differ. A maximum-degree vertex is a sink. Two sinks cannot be adjacent, since their connecting edge would give one an outgoing edge. Connectedness and $n\ge2$ give a positive degree at every vertex, at least one nonsink, and at least one sink incidence. Hence $1\le s<n$ and $T_R>0$. Since sinks are independent, their incidences represent distinct actual edges and $Q(G)\ge Q_R$.

On this same incidence set, counting all $D_i$ neighbors of each sink gives

$$
\sum_{(i,v)\in\mathcal I_R}\frac1{D_i}=s.
$$

Cauchy–Schwarz, with factors $d_v/D_i$ and $1/d_v$, yields

$$
s^2\le
\left(\sum_{(i,v)\in\mathcal I_R}\frac{d_v^2}{D_i^2}\right)
\left(\sum_{(i,v)\in\mathcal I_R}\frac1{d_v^2}\right)
=Q_RT_R.
$$

Moreover, $h(v)\le d_v$ and $d_v\ge1$, whence

$$
T_R\le\sum_{v\notin R}\frac1{d_v}\le n-s.
$$

Summing the edge-cost lower bound on $\mathcal I_R$ proves the assertions about $Q$ and $E$. At one sink $i$, its $D_i$ incident edges each have $r^2=d_v^2/D_i^2\ge1/D_i^2$. Therefore $E(G)\ge1/((2+\eta)D_i)$, proving the last assertion. All factors, incidence counts and degrees used in these inequalities come from $G$. ∎

## 3. Every fixed inverse-order budget has finitely many hubs

**Theorem 3.1 (Uniform two-layer reduction at fixed cost).** Fix $C>0$. There exists an integer $N(C)$ such that every graph of order $n\ge N(C)$ with $E(G)\le C/n$ is a two-layer graph. Its number $s$ of sinks is bounded solely in terms of $C$, and every sink has degree at least $n/(3C)$. If its cyclomatic number is positive, then $s\ge2$.

One sufficient choice is obtained by setting

$$
A=2C+1,\qquad K=\lceil\sqrt A\rceil,
$$

and taking any integer

$$
N(C)>\max\{1,C^2,3C,A^3,4AK^2,36C^2A\}.
$$

For this choice $s\le K$.

**Proof.** For $n\ge N(C)$, put $\eta=C/n<1/3<\sqrt2-1$. The exact edge identity in Theorem 2.1 gives

$$
r^2\le\frac{2C+C^2/n}{n}\le\frac An,\qquad
g(r)\ge\frac{r^2}{2+C/n}\ge\frac13r^2.
$$

The incidence bound implies

$$
s^2\le E(G)(2+C/n)(n-s)\le C(2+C/n)\le A,
$$

so $s\le K$. A directed path $v_0\to v_1\to v_2\to v_3$ would give

$$
1\le d_{v_0}\le(A/n)^{3/2}d_{v_3}
\le\frac{A^{3/2}(n-1)}{n^{3/2}}<\frac{A^{3/2}}{\sqrt n}<1,
$$

which is impossible.

Suppose $v$ is mixed. Every outgoing neighbor of $v$ is a sink: otherwise an incoming edge at $v$, this outgoing edge and an outgoing edge at its other endpoint form a forbidden directed path of length three. Therefore its outgoing degree $k$ is at most $K$. An incoming edge, whose smaller endpoint has degree at least one, and an outgoing edge, whose larger endpoint has degree at most $n-1$, imply

$$
\sqrt{n/A}\le d_v<\sqrt{An}.
$$

Since $n>4AK^2$, we have $d_v>2K$, so the incoming degree $j=d_v-k>d_v/2$. Its incoming edges alone cost

$$
E(G)\ge\frac{j}{3d_v^2}>\frac1{6d_v}
>\frac1{6\sqrt{An}}>\frac Cn,
$$

where the final inequality follows from $n>36C^2A$. This contradiction excludes mixed vertices. Each vertex is now either a source or a sink and every edge joins the two classes. The individual-sink bound gives

$$
D_i\ge\frac{n}{C(2+C/n)}\ge\frac n{3C}.
$$

If $s=1$, every other vertex is a source with the single sink as its only possible neighbor. Simplicity and connectedness make the graph a star, whose cyclomatic number is zero. This proves the positive-cyclomatic assertion. ∎

## 4. A uniform finite minimum for the entire two-hub range

**Theorem 4.1 (Two-hub rigidity from order 729).** Let $n\ge729$, $\ell\ge1$ and $G\in\mathcal G(n,\ell)$. If

$$
E(G)\le\frac{17}{4n},
$$

then $\ell\le n-3$, $G\in\mathcal B(n,\ell)$ up to relabelling, and both hub degrees satisfy $D_i\ge49n/425$.

**Proof.** Put $C=17/4$ and $\eta=C/n$. At $n=729$ the exact inequalities

$$
2C+\frac{C^2}{n}=\frac{99433}{11664}<9,\qquad
\frac1{2+C/n}=\frac{2916}{5849}>\frac{49}{100}
$$

hold; their left sides respectively decrease and increase with $n$. Thus, for every edge of this actual graph,

$$
r<\frac3{\sqrt n}<1,\qquad g(r)\ge\frac{49}{100}r^2.
$$

As in Theorem 2.1, the degree orientation exists and

$$
E(G)\ge\frac{49}{100}\frac{s^2}{n-s}.
$$

If $s\ge3$, this is greater than $441/(100n)>17/(4n)$. Hence $s\le2$, without having assumed that the graph is two-layer.

A directed path of three edges would give

$$
1\le d_{v_0}<\frac{27}{n^{3/2}}d_{v_3}
\le\frac{27(n-1)}{n^{3/2}}<\frac{27}{\sqrt n}\le1.
$$

There is no such path. If $v$ is mixed, every outgoing neighbor is a sink by the same path argument. Its outgoing degree $k$ is at most two. Writing $d=d_v$ and $j=d-k$ for its incoming degree, one incoming and one outgoing edge give

$$
\frac{\sqrt n}{3}<d<3\sqrt n,\qquad j\ge d-2,\qquad d\ge9.
$$

The incoming edges alone yield

$$
E(G)\ge\frac{49}{100}\frac{d-2}{d^2}.
$$

The function $(t-2)/t^2$ decreases for $t\ge4$. Using $d<3\sqrt n$ therefore gives

$$
nE(G)>\frac{49}{100}\left(\frac{\sqrt n}{3}-\frac29\right)
\ge\frac{3871}{900}>\frac{17}{4},
$$

a contradiction. Thus the graph is two-layer. One sink would force a star, contradicting $\ell\ge1$, so there are exactly two sinks. Every source has degree one or two. If $b$ sources have degree two, each meets both sinks, and

$$
m=(n-2-b)+2b=n-2+b=n-1+\ell,
\qquad b=\ell+1.
$$

The other $n-\ell-3$ vertices are leaves at these two hubs. In particular $\ell\le n-3$ and the asserted family is recovered from the actual graph. Finally, its $D_i$ sink edges give $E(G)\ge49/(100D_i)$, so $D_i\ge49n/425$. ∎

**Theorem 4.2 (Unique balanced minimizer with an absolute sufficient threshold).** For all integers $n\ge729$ and $1\le\ell\le n-3$, the unique minimizing isomorphism class of $\Phi$ in $\mathcal G(n,\ell)$ is $H_{n,\ell}$. Its minimum excess is exactly

$$
E^\ast(n,\ell)=M_{\ell+1}\left(\left\lfloor\frac{n-1+\ell}{2}\right\rfloor\right)
+M_{\ell+1}\left(\left\lceil\frac{n-1+\ell}{2}\right\rceil\right).
$$

The number 729 is a sufficient threshold, with no assertion that it is least.

**Proof.** Definition 4.1 and Lemma 4.2 of the preceding volume supply an actual member $H_{n,\ell}\in\mathcal G(n,\ell)$ and the bound

$$
E(H_{n,\ell})\le\frac{2(n+7\ell+5)}{(n+\ell-2)^2}.
$$

The polynomial identity

$$
49(n+\ell-2)^2-4(6n-19)(n+7\ell+5)
=(7\ell-5n+24)^2
$$

implies

$$
nE(H_{n,\ell})\le\frac{49n}{12n-38}<\frac{17}{4}
$$

for $n\ge729$; the last strict inequality already holds for $n\ge81$. Thus every minimizer, and every graph tying $H_{n,\ell}$, satisfies the budget in Theorem 4.1 and belongs to $\mathcal B(n,\ell)$.

For this family use the threshold-independent strict convexity established inside the proof of Theorem 8.2 of the preceding volume. Namely, for every $b\ge2$ and $x>0$,

$$
M_b''(x)=\frac1{(x^2+1)^{3/2}}+b\bigl(f_2''(x)-f_1''(x)\bigr)>0.
$$

The inequality there follows by differentiating $t(3x^2+2t)/(x^2+t)^{3/2}$, whose derivative is $(6x^4+5x^2t+2t^2)/(2(x^2+t)^{5/2})>0$. It uses no bound involving $n$ or $\ell$.

If $D_2\ge D_1+2$, then $D_2>b$, so hub 2 has a leaf. Moving that leaf to hub 1 preserves simplicity, connectedness, $n$, $m$ and $\ell$, and changes the excess by

$$
M_b(D_1+1)-M_b(D_1)-M_b(D_2)+M_b(D_2-1)<0
$$

by strict convexity. Exchanging the hubs gives the other imbalance case. The only minimizing unordered integer degree pair is therefore $\{\lfloor m/2\rfloor,\lceil m/2\rceil\}$, which is feasible since $m\ge2b$. Subtracting $b$ gives the balanced leaf counts, determining $H_{n,\ell}$ up to isomorphism. Graphs above the budget have strictly larger excess than $H_{n,\ell}$. Since $\Phi=m+E$ at the same $m$, this proves the global claim and its equality statement.

The prior unicyclic comparison with universal-vertex graphs holds for every $n\ge7$ in A. Ali, K. C. Das and A. A. Attiya, *Bond incident degree indices of fixed-order unicyclic graphs*, Discrete Math. Lett. 16 (2025), 135–142, DOI [10.47443/dml.2025.192](https://doi.org/10.47443/dml.2025.192), Remark 2.3; its reported all-graph computations cover $4\le n\le10$. The specialization of the two-hub construction to $n=5\ell+7$, with $2(\ell+1)$ leaves at each hub, is also in A. M. Albalahi, *On Two Conjectures Concerning the Hyperbolic Sombor Index and Its Counterpart*, Discrete Math. Lett. 18 (2026), 122–128, DOI [10.47443/dml.2026.217](https://doi.org/10.47443/dml.2026.217), Proposition 2.1 and its proof. That proposition compares with universal-vertex graphs; its Theorem 2.2 concerns maxima. The construction and those comparisons are the cited intermediate results, whereas the conclusion here compares with every graph in $\mathcal G(n,\ell)$.

The coordinate-increasing property $P$ used by H. Liu, Z. Du, Y. Huang, H. Chen and S. Elumalai, *Note on the Minimum Bond Incident Degree Indices of k-Cyclic Graphs*, MATCH Commun. Math. Comput. Chem. 91 (2024), 255–266, DOI [10.46793/match.91-1.255L](https://doi.org/10.46793/match.91-1.255L), §1 and Theorem 2.1, fails for this weight: at fixed $y>0$, $\sqrt{1+(y/x)^2}$ strictly decreases for $x>y$. Likewise condition P2 in M. Bašić, *A general algebraic characterization of extremal $\Delta$-trees and $k$-cyclic graphs for degree-homogeneous VDB indices*, [arXiv:2610.34361v1](https://arxiv.org/abs/2610.34361v1), §2.1, requires $f(x,\Delta)>f(\Delta,\Delta)$ for $x<\Delta$, whereas CDSO has $f(x,\Delta)<\sqrt2=f(\Delta,\Delta)$. Neither hypothesis supplies the minimum asserted here. ∎

## 5. Finite-hub profiles with exact integer cycle budgets

**Definition 5.1 (Profile space and energy).** Fix $\alpha\in[0,1)$ and any finite integer $s\ge2$. Let $\mathcal P_s(\alpha)$ be the arrays $(x_S)_{\varnothing\ne S\subseteq[s]}$ satisfying

$$
x_S\ge0,\qquad \sum_Sx_S=1,\qquad
\sum_S(|S|-1)x_S=\alpha,\qquad
y_i:=\sum_{S\ni i}x_S>0\quad(1\le i\le s).
$$

Set

$$
J_s(x)=\frac12\sum_Sx_S|S|^2\sum_{i\in S}\frac1{y_i^2},\qquad
F(\alpha)=\frac{2+14\alpha}{(1+\alpha)^2}.
$$

Zero-mass types $x_S=0$ are allowed. The strict inequalities on the $y_i$ specify the finite-energy hub domain.

**Theorem 5.2 (Necessary profiles and exact-budget realization).** Let $(\ell_n)$ be any prescribed sequence of integers with $\ell_n\ge1$ and $\ell_n/n\to\alpha\in[0,1)$.

For every sequence $G_n\in\mathcal G(n,\ell_n)$ with $\sup_n nE(G_n)<\infty$, every subsequence has a further subsequence on which the graphs are two-layer, the number $s\ge2$ of sinks is fixed, their normalized neighborhood-type counts converge to some $x\in\mathcal P_s(\alpha)$, and

$$
nE(G_n)\longrightarrow J_s(x).
$$

Conversely, for every fixed finite $s\ge2$ and every $x\in\mathcal P_s(\alpha)$ there exist, for all sufficiently large $n$, actual simple connected graphs $G_n\in\mathcal G(n,\ell_n)$ with those type limits and $nE(G_n)\to J_s(x)$. This assertion keeps every specified integer $\ell_n$ exactly.

**Proof.** Choose a fixed $C>0$ bounding $nE(G_n)$. Theorem 3.1 gives eventual two-layer structure, bounded sink number and $D_i\ge n/(3C)$. Pass to a subsequence with constant $s\ge2$, label its sinks by $[s]$, and let $a_{S,n}$ count sources with neighborhood exactly $S\subseteq[s]$. All these neighborhoods are nonempty, and source degree is $|S|\le s$. Exact counting in this same graph gives

$$
\sum_Sa_{S,n}=n-s,\qquad
\sum_S(|S|-1)a_{S,n}=\ell_n+s-1,\qquad
D_{i,n}=\sum_{S\ni i}a_{S,n}.
$$

There are only $2^s-1$ types. Finite-dimensional compactness gives a further subsequence with $a_{S,n}/n\to x_S$. Dividing the identities by $n$ yields the constraints in Definition 5.1 and

$$
y_i=\lim_n D_{i,n}/n\ge1/(3C)>0.
$$

For $r\ge0$, rationalization gives the exact remainder

$$
0\le\frac{r^2}{2}-g(r)
=\frac{r^4}{2(\sqrt{1+r^2}+1)^2}\le\frac{r^4}{8}.
$$

This elementary expansion is used here on the actual edges. The bounded source degrees and linear hub degrees imply

$$
E(G_n)=\frac12\sum_Sa_{S,n}|S|^2\sum_{i\in S}D_{i,n}^{-2}+O(n^{-3}),
$$

since there are $O(n)$ edges and each edge remainder is $O(n^{-4})$. Multiplication by $n$ proves $nE(G_n)\to J_s(x)$.

For the converse, fix $s$ and $x$ and reserve $s$ hub vertices and $s-1$ distinct sources of degree two. Join the latter respectively to the pairs $\{1,2\},\{2,3\},\ldots,\{s-1,s\}$. This subdivided path connects all hubs. There remain

$$
M=n-2s+1
$$

source vertices. Round $Mx_S$ to nonnegative integer counts summing to $M$, with bounded error in each of the finitely many types; for example take all floors and distribute the remaining fewer than $2^s-1$ vertices. Give the remaining sources these nonempty hub neighborhoods. Their total additional membership count

$$
B=\sum_S(|S|-1)a_S
$$

satisfies $B=M\alpha+O_s(1)$ and hence $B-\ell_n=o(n)$. The exact target for these $M$ sources is $\ell_n$, because the reserved path already has $s-1$ additional memberships over one per source.

For sufficiently large $n$, $0\le\ell_n\le(s-1)M$: indeed $\ell_n/n\to\alpha<1\le s-1$ and $M/n\to1$. If $B<\ell_n$, a remaining source has fewer than $s$ neighbors whenever $B<(s-1)M$; add one missing hub membership. If $B>\ell_n$, a remaining source has at least two neighbors whenever $B>0$; delete one membership while keeping its neighborhood nonempty. Repeat in the required direction until $B=\ell_n$. There are exactly $|B_{\mathrm{initial}}-\ell_n|=o(n)$ edits. They change the count of any type by at most $o(n)$, preserving its limiting mass, including every zero-mass type.

The reserved path is never changed, so the graph stays connected; every other vertex still has a nonempty hub neighborhood. It is simple because memberships are subsets and all source vertices are distinct. It has precisely $n$ vertices and

$$
2(s-1)+M+\ell_n=n-1+\ell_n
$$

edges. Thus it has exactly the required cyclomatic number. Its hub degrees satisfy $D_{i,n}/n\to y_i>0$, whereas every source degree is at most $s$. Consequently these are its actual degree-oriented sinks for all sufficiently large $n$. The same remainder estimate proves the desired energy limit.

This construction applies also at $\alpha=0$, even when the positive-mass support contains only disjoint singleton groups: the reserved $s-1$ sources still connect the hubs, and the $o(n)$ membership adjustment realizes each prescribed $\ell_n\ge1$. There is no requirement that a positive-mass type be shared by two hubs. ∎

**Theorem 5.3 (The hub boundary and the unique global optimizing profile).** In the domain of Definition 5.1,

$$
J_s(x)\ge\frac1{2y_i}\quad(1\le i\le s),\qquad
J_s(x)\ge\frac{s^2}{2\sum_Sx_S/|S|}\ge\frac{s^2}{2}.
$$

Thus any fixed-$s$ profile sequence with a hub mass tending to zero has diverging energy. Over every finite $s\ge2$,

$$
\min_{\substack{s\ge2\\x\in\mathcal P_s(\alpha)}}J_s(x)=F(\alpha).
$$

The only minimizing profile, up to exchange of hub labels, has

$$
s=2,\qquad x_{\{1,2\}}=\alpha,\qquad
x_{\{1\}}=x_{\{2\}}=\frac{1-\alpha}{2}.
$$

Every $s\ge3$ profile has $J_s(x)-F(\alpha)\ge5/12$.

**Proof.** The $i$th summand in $2J_s$ is

$$
\frac{\sum_{S\ni i}|S|^2x_S}{y_i^2}\ge\frac{\sum_{S\ni i}x_S}{y_i^2}=\frac1{y_i},
$$

which proves the first bound and the divergence assertion. For the joint bound use all pairs $(S,i)$ with $i\in S$. Their exact marginal identity is

$$
\sum_S\sum_{i\in S}\frac{x_S}{y_i}=s.
$$

Cauchy–Schwarz, applied with factors $\sqrt{x_S}|S|/y_i$ and $\sqrt{x_S}/|S|$, gives

$$
s^2\le
\left(\sum_Sx_S|S|^2\sum_{i\in S}y_i^{-2}\right)
\left(\sum_Sx_S/|S|\right)=2J_s(x)\sum_Sx_S/|S|.
$$

Zero-mass types contribute zero to both factors, so no positive-type assumption is used. The second factor is positive and at most one. Hence $J_s\ge s^2/2$.

The exact identity

$$
\frac{49}{12}-F(\alpha)=\frac{(7\alpha-5)^2}{12(1+\alpha)^2}\ge0
$$

shows that every $s\ge3$ has $J_s\ge9/2>49/12\ge F(\alpha)$, with gap at least $5/12$. Thus it remains to optimize $s=2$. Its constraints imply

$$
x_{\{1,2\}}=\alpha,\qquad y_1+y_2=1+\alpha,\qquad
J_2(x)=h_\alpha(y_1)+h_\alpha(y_2),
\quad h_\alpha(y)=\frac1{2y}+\frac{3\alpha}{2y^2}.
$$

For every $y>0$,

$$
h_\alpha''(y)=\frac1{y^3}+\frac{9\alpha}{y^4}>0.
$$

Strict convexity therefore gives the unique minimum at $y_1=y_2=(1+\alpha)/2$, with value $F(\alpha)$. The corresponding singleton masses are $(1-\alpha)/2>0$ and the shared mass is $\alpha\ge0$, so this profile is feasible, including at $\alpha=0$. It is realized at every prescribed budget sequence by Theorem 5.2, or by $H_{n,\ell_n}$ directly. No compactness assumption over unbounded $s$ is needed, because the bound $J_s\ge s^2/2$ excludes all $s\ge3$.

The formally possible one-hub probability array at $\alpha=0$ is not part of this variational problem: an actual two-layer simple connected graph with one sink is a star and has $\ell=0$. Theorem 3.1 excludes such a limit from any bounded-energy sequence with $\ell_n\ge1$. Likewise an additional hub of vanishing normalized degree cannot be suppressed inside a bounded-energy sequence, since Theorem 2.1 gives $nE(G_n)\ge n/((2+C/n)D_{i,n})$. ∎

## 6. All subunit densities, exact eventual structure and a gap

**Theorem 6.1 (Density limit and complete near-minimum structure).** Let $\ell_n\ge1$ be any prescribed integer sequence with $\ell_n/n\to\alpha\in[0,1)$. Then eventually $\ell_n\le n-3$ and

$$
\lim_{n\to\infty}nE^\ast(n,\ell_n)=F(\alpha)=\frac{2+14\alpha}{(1+\alpha)^2}.
$$

For any $G_n\in\mathcal G(n,\ell_n)$ the following conditions are equivalent:

1. $E(G_n)-E^\ast(n,\ell_n)=o(1/n)$.
2. $nE(G_n)\to F(\alpha)$.
3. Eventually $G_n\in\mathcal B(n,\ell_n)$ up to relabelling, and its hub degrees satisfy $|D_{1,n}-D_{2,n}|/n\to0$.

For these sequences both hub degrees divided by $n$ tend to $(1+\alpha)/2$, the proportion of common degree-two neighbors tends to $\alpha$, and the proportion of leaves at each hub tends to $(1-\alpha)/2$. They can be transformed to $H_{n,\ell_n}$ with $o(n)$ leaf moves, each preserving $n$ and $\ell_n$.

**Proof.** Since $1-\alpha>0$, eventually $n-\ell_n\ge3$. Theorem 4.2 gives the exact minimum there. To evaluate it, the remainder identity in Theorem 5.2, applied to the actual nonnegative edge counts at a hub, gives for $x\ge b\ge2$

$$
0\le\left(\frac1{2x}+\frac{3b}{2x^2}\right)-M_b(x)
\le\frac{(x-b)+16b}{8x^4}
=\frac{x+15b}{8x^4}\le\frac2{x^3}.
$$

This keeps the $b/x^2$ term when $b$ is of order $n$. For $H_{n,\ell_n}$ set $b=\ell_n+1$ and $D_i\in\{\lfloor m/2\rfloor,\lceil m/2\rceil\}$. Then $b/n\to\alpha$ and $D_i/n\to(1+\alpha)/2$. Multiplying the estimate by $n$ yields

$$
nE^\ast(n,\ell_n)\longrightarrow
\frac2{1+\alpha}+\frac{12\alpha}{(1+\alpha)^2}=F(\alpha).
$$

This proves the equivalence of conditions 1 and 2. If condition 2 holds, $F(\alpha)\le49/12<17/4$ implies $nE(G_n)<17/4$ eventually. Theorem 4.1 then gives exact membership in $\mathcal B(n,\ell_n)$ and $D_{i,n}/n\ge49/425$. Put $z_{i,n}=D_{i,n}/n$ and $\beta_n=(\ell_n+1)/n$. The same hub estimate, uniformly on these actual degrees, gives

$$
nE(G_n)=h_{\beta_n}(z_{1,n})+h_{\beta_n}(z_{2,n})+O(n^{-2}),
\qquad z_{1,n}+z_{2,n}=m/n\to1+\alpha.
$$

Every subsequential limit of $(z_{1,n},z_{2,n})$ lies in $[49/425,1]^2$ and has sum $1+\alpha$. Strict convexity of $h_\alpha$ from Theorem 5.3 shows that its energy equals $F(\alpha)$ only at the balanced pair. Condition 2 forces every such limit to be that pair. Thus $z_{i,n}\to(1+\alpha)/2$, proving condition 3.

Conversely, condition 3 and $D_{1,n}+D_{2,n}=m$ force the same two degree limits. They are positive, so the expansion applies and gives condition 2. There are exactly $\ell_n+1$ common neighbors. Subtracting their number from each hub degree gives the two leaf counts and their stated limits. Moving leaves from the larger hub to the smaller until their degrees differ by at most one takes at most $|D_{1,n}-D_{2,n}|/2+1=o(n)$ moves. Each move changes only the hub incident to one leaf and preserves the common-neighbor core, connectedness, simplicity and both integer budgets. ∎

**Theorem 6.2 (Uniform normalized gap outside the two-hub family).** Under the assumptions of Theorem 6.1, let $I$ be any infinite set of orders for which $G_n\notin\mathcal B(n,\ell_n)$ up to relabelling. Then

$$
\liminf_{\substack{n\to\infty\\n\in I}}nE(G_n)\ge\frac92,
$$

and consequently

$$
\liminf_{\substack{n\to\infty\\n\in I}}
 n\bigl(E(G_n)-E^\ast(n,\ell_n)\bigr)
\ge\frac92-F(\alpha)\ge\frac5{12}.
$$

**Proof.** If the first liminf is infinite there is nothing to prove. Otherwise take a subsequence along $I$ attaining its finite liminf, and bound $nE(G_n)$ on it by a fixed $C$. Theorem 3.1 gives eventual two-layer structure with at least two sinks. Exactly two would force $\mathcal B(n,\ell_n)$ by the actual vertex and edge counts in Theorem 4.1. Thus these graphs have at least three sinks. Applying Theorem 2.1 to these same graphs with $\eta=C/n$ gives

$$
nE(G_n)\ge\frac{ns^2}{(2+C/n)(n-s)}
\ge\frac9{2+C/n}.
$$

Taking the limit proves the first inequality. Theorem 6.1 permits subtraction of the convergent minimum, and $F(\alpha)\le49/12$ gives $9/2-F(\alpha)\ge5/12$. ∎

## 追加锚（本行以下为增补区）

## 7. The first supercritical density window

**Definition 7.1 (The three-hub family).** Let

$$
n-2\le \ell\le 2n-8,\qquad N=n-3,\qquad c=\ell-n+5,\qquad b=2n-\ell-8.
$$

Then $c\ge3$, $b\ge0$ and $b+c=N$. Define $\mathcal C(n,\ell)$ to be the family of simple graphs with three pairwise nonadjacent hubs and $N$ source vertices: $c$ sources are adjacent to all three hubs, and the remaining $b$ sources are adjacent to exactly two hubs. If $b_i$ is the number of pair sources missing hub $i$, then

$$
\sum_{i=1}^3b_i=b,\qquad D_i=N-b_i,\qquad |b_i-b_j|\le1.
$$

The last condition defines the balanced subfamily. For $c\ge0$ and $D>0$ with $D\ge c$, put

$$
H_c(D)=(D-c)g(2/D)+cg(3/D)\qquad(D\ge c).
$$

Every graph in $\mathcal C(n,\ell)$ has excess $\sum_{i=1}^3H_c(D_i)$. The edge count is

$$
3c+2b=n-1+\ell,
$$

so the family lies in $\mathcal G(n,\ell)$; its triple sources make it connected.

**Theorem 7.2 (Uniform three-hub minimum).** There is an absolute sufficient threshold $N_0=10^6$ such that, for every integer $n\ge N_0$ and every

$$
n-2\le\ell\le2n-8,
$$

the unique minimizing isomorphism class in $\mathcal G(n,\ell)$ is the balanced member of $\mathcal C(n,\ell)$. Write $b=3q+r$ with $0\le r\le2$. Its exact minimum excess is

$$
E^\ast(n,\ell)=(3-r)H_c(N-q)+rH_c(N-q-1),
$$

and $\Phi^\ast(n,\ell)=n-1+\ell+E^\ast(n,\ell)$. The threshold is sufficient and is not asserted to be least.

**Proof.** We first record the uniform finite estimate used to compare actual graphs with profiles. Let a two-layer graph have $s$ sinks, $M=n-s$ sources, and let $N_T$ count sources whose neighborhood is the nonempty set $T\subseteq[s]$. Put

$$
x_T=N_T/M,\qquad y_i=\sum_{T\ni i}x_T,\qquad
\beta=\sum_T(|T|-1)x_T=\frac{\ell+s-1}{n-s}.
$$

The displayed expression $J_s$ of Definition 5.1 is used with this $\beta$; its formula is valid for every $0\le\beta\le s-1$. Exact counting gives $\sum_TN_T=M$ and $D_i=M y_i$ for every $i\in[s]$. If $E(G)\le14/n$, Theorem 3.1 gives $s\le6$ and $D_i\ge n/42$. Its proof also gives the sharper $s^2\le14(2+14/n)<36$, hence $s\le5$ for $n\ge10^6$. Since every source degree is at most $s$, rationalization yields

$$
0\le\frac{r^2}{2}-g(r)\le\frac{r^4}{8}.
$$

Summing this inequality over the actual source--sink edges gives the uniform bound

$$
0\le \frac{J_s(x)}{M}-E(G)\le\frac{B}{n^3},\qquad
B=\frac{5^5\,42^4}{8}=1215506250.
\tag{7.1}
$$

Indeed, a source of degree $k\le5$ contributes at most $k^5 42^4/(8n^4)$ to the remainder, and there are at most $n$ sources. This estimate uses actual degrees and does not replace the graph by a relaxed profile.

For every profile, Cauchy--Schwarz on the incidences $(T,i)$ gives

$$
s^2\le 2J_s(x)L_s(x),\qquad
L_s(x)=\sum_T\frac{x_T}{|T|}.
$$

Since

$$
\frac1{|T|}\le1-\frac{|T|-1}{s},
$$

we have $L_s(x)\le1-\beta/s$ and therefore

$$
J_s(x)\ge L_s^{\rm low}(\beta):=\frac{s^3}{2(s-\beta)}.
\tag{7.2}
$$

For real $s\ge4$ and $1\le\beta\le2$, this lower bound is increasing in $s$, and

$$
\frac{32}{4-\beta}-F_3(\beta)
=\frac{5(47\beta^2-131\beta+92)}
 {2(4-\beta)(1+\beta)^2}\ge\delta,\qquad
\delta=\frac{75}{752},
\tag{7.3}
$$

where $F_3(\beta)=9(19\beta-11)/(2(1+\beta)^2)$. The last displayed constant is a conservative bound on the interval $[1,2]$: complete the square in the numerator and use $2(4-\beta)(1+\beta)^2\le36$.

We next optimize the three-hub profile without imposing symmetry. Let $u_i=x_{\{i\}}$, $b_i=x_{[3]\setminus\{i\}}$, $c'=x_{[3]}$, and $t=\sum_i u_i$. The constraints imply

$$
c'=\beta-1+t,\qquad \sum_i b_i=2-\beta-2t,\qquad
\sum_i y_i=1+\beta.
$$

For hub $i$, its weighted incidence numerator in $2J_3$ is

$$
w_i=u_i+4\!\sum_{j\ne i}b_j+9c'
=4y_i+5(\beta-1)+5t-3u_i
\ge4y_i+5(\beta-1)+2t.
$$

Put $f_\beta(y)=4/y+5(\beta-1)/y^2$ and $\mu=(1+\beta)/3$. Every feasible $y_i\le1$, and $f_\beta''(y)=8/y^3+30(\beta-1)/y^4\ge8$. Strong convexity, $\sum_i(y_i-\mu)=0$, and Cauchy--Schwarz give

$$
J_3(x)\ge F_3(\beta)+\frac{27t}{(1+\beta)^2}
 +2\sum_{i=1}^3(y_i-\mu)^2.
\tag{7.4}
$$

Thus the unique minimizing profile (up to hub labels) has

$$
t=0,\qquad y_1=y_2=y_3=\frac{1+\beta}{3},\qquad
c'=\beta-1,\qquad b_1=b_2=b_3=\frac{2-\beta}{3}.
\tag{7.5}
$$

This includes both endpoints: at $\beta=1$ the triple mass is zero, and at $\beta=2$ the pair masses are zero. In particular every profile with $s\ge4$ has, by (7.2)--(7.3), a gap at least $\delta$ above $F_3(\beta)$ whenever $1\le\beta\le2$; no symmetry or positive-mass assumption was used.

Now fix $n\ge10^6$ and the stated $\ell$. The balanced graph in Definition 7.1 has $t=0$ and $|y_i-(1+\beta_3)/3|\le1/N$, where $\beta_3=(\ell+2)/N$. On the interval $y\ge1/3$, $1\le\beta_3\le2$, one has $f_{\beta_3}''(y)\le2646$. Taylor's theorem and cancellation of the three first-order deviations give

$$
J_3(x_{\rm bal})\le F_3(\beta_3)+\frac{2000}{N^2},\qquad
E_{\rm bal}\le\frac{F_3(\beta_3)}N+\frac{2000}{N^3}.
\tag{7.6}
$$

Since $F_3(\beta_3)\le27/2$, this implies

$$
nE_{\rm bal}<\frac{27}{2}+\frac{81}{n}+\frac{16000}{n^2}<14.
\tag{7.7}
$$

Every minimizer consequently satisfies $E(G)\le14/n$, so the preceding two-layer and error estimates apply. A two-layer graph with at most two sinks has at most $2(n-2)=2n-4$ edges, whereas here $m\ge2n-3$; hence its sink number is at least three.

Suppose first that $s\in\{4,5\}$. Put $\beta_s=(\ell+s-1)/(n-s)$. Direct subtraction gives

$$
\beta_s-\beta_3=\frac{(s-3)(n+\ell-1)}{(n-s)(n-3)}\ge0.
$$

The function $L_s^{\rm low}(\beta)$ is increasing in $\beta$, so (7.2) and (7.3), even when $\beta_s>2$, give

$$
J_s(x)\ge L_s^{\rm low}(\beta_s)\ge L_s^{\rm low}(\beta_3)\ge F_3(\beta_3)+\delta.
$$

Using (7.1), $M=n-s<N$, and (7.6),

$$
E(G)-E_{\rm bal}\ge\frac{\delta}{n}-\frac{B+16000}{n^3}>0.
$$

The last inequality follows from the stronger checked inequality $\delta n^2>8(B+2000)$ at $n=10^6$ and hence for all larger $n$. Thus every minimizer has exactly three sinks.

It remains to pass from the three-hub profile to the actual graph. Let $a$ be the number of singleton sources. If $a>0$, choose one singleton adjacent to hub $i$ and one triple source adjacent to all three hubs. Replace the triple source's edge to hub $j\ne i$ by the singleton's edge to $j$. The two source neighborhoods become $\{i,j\}$ and $\{i,k\}$, where $k$ is the third hub. The graph remains simple and connected, all vertex and edge counts are unchanged, and all three hub degrees are unchanged; at least two triple sources remain because $c\ge3$. The excess change is

$$
[2g(2/D_i)-g(1/D_i)-g(3/D_i)]
 +[g(2/D_j)-g(3/D_j)]
 +[g(2/D_k)-g(3/D_k)]<0.
$$

Here $g$ is strictly increasing and strictly convex on $(0,\infty)$, so each bracket is strictly negative. This contradiction proves $a=0$. Exact counting then forces precisely $c$ triple sources and $b$ pair sources.

For the remaining pair sources, let $b_i$ be the number missing hub $i$, so $D_i=N-b_i$. The contribution at hub $i$ is $H_c(D_i)$. The identity

$$
H_c(D)=\sqrt{D^2+4}-D+\frac c2\int_4^9\frac{dz}{D\sqrt{D^2+z}}
$$

shows strict convexity: the first term has second derivative $4/(D^2+4)^{3/2}$, and the second derivative of the integrand is

$$
\frac{6D^4+5zD^2+2z^2}{D^3(D^2+z)^{5/2}}>0.
$$

If $b_i\ge b_j+2$, choose a pair source missing $i$ and change its neighbor $j$ to $i$. This changes $(D_i,D_j)$ to $(D_i+1,D_j-1)$, preserves simplicity, connectedness and both integer budgets, and strictly decreases the sum of the two strictly convex hub contributions. Hence every minimizer has $|b_i-b_j|\le1$. Conversely every unbalanced triple admits this strict improvement until balanced. Writing $b=3q+r$ gives the displayed exact formula, and all balanced assignments are related by a hub permutation. The minimizing isomorphism class is therefore unique. ∎

**Theorem 7.3 (Density limit and complete near-minimum structure).** Let $\ell_n\ge n-2$, $\ell_n/n\to\alpha\in[1,2)$. Then eventually $\ell_n\le2n-8$, and

$$
\lim_{n\to\infty}nE^\ast(n,\ell_n)=F_3(\alpha)
=\frac{9(19\alpha-11)}{2(1+\alpha)^2}.
$$

For any $G_n\in\mathcal G(n,\ell_n)$,

$$
n\bigl(E(G_n)-E^\ast(n,\ell_n)\bigr)\longrightarrow0
$$

if and only if, eventually, $G_n$ is a three-hub two-layer graph for which, writing $a_n$ for the singleton count, $b_{i,n}$ for the count of pair sources missing hub $i$, and $c_n$ for the triple count,

$$
a_n=o(n),\qquad
b_{i,n}=\frac{2n-\ell_n-8}{3}+o(n)\quad(i=1,2,3),\qquad
\frac{c_n}{n}\longrightarrow\alpha-1.
\tag{7.8}
$$

The condition permits an unbounded $o(n)$ singleton count. It is equivalent to the three hub degrees divided by $n$ tending to $(1+\alpha)/3$, together with singleton proportion tending to zero. The exact minimizers of Theorem 7.2 have $a_n=0$ and pair counts differing by at most one.

**Proof.** For the balanced graph, $\beta_3=(\ell_n+2)/(n-3)\to\alpha$, and (7.6) together with (7.1) gives the stated limit. For a near-minimizing sequence, this same upper bound makes $E(G_n)=O(1/n)$. Theorem 3.1 and the capacity count give three sinks eventually; the $s\ge4$ comparison in the proof of Theorem 7.2 excludes infinitely many such terms. With three sinks, (7.1) and (7.4) imply

$$
J_3(x_n)-F_3(\beta_{3,n})\longrightarrow0,\qquad
\beta_{3,n}=\frac{\ell_n+2}{n-3}\longrightarrow\alpha.
$$

The quantitative terms in (7.4) give $a_n/(n-3)\to0$ and $D_{i,n}/(n-3)\to(1+\alpha)/3$. The exact identities

$$
c_n=\ell_n-n+5+a_n,\qquad
\sum_i b_{i,n}=2n-\ell_n-8-2a_n,\qquad
b_{i,n}/(n-3)=1-a_n/(n-3)+u_{i,n}-D_{i,n}/(n-3)
$$

then give (7.8). Conversely, (7.8) makes the seven-type profile converge to the unique equality profile in (7.5); (7.1) gives $nE(G_n)\to F_3(\alpha)$, while the balanced graphs have the same limit. Thus the scaled excess difference tends to zero.

To see why $a_n=o(n)$ cannot be strengthened to eventual vanishing, start with a balanced graph and choose $r_n=\lfloor\sqrt n\rfloor$ pair sources of types $\{1,2\}$ and $\{1,3\}$. Replace each pair of sources by a singleton of type $\{1\}$ and a triple source. For fixed $\alpha<2$ there are linearly many sources of both selected pair types, so this is possible eventually. It preserves all three hub degrees, $n$, $m$ and connectedness. Each replacement changes the excess by $O(n^{-2})$, hence $n(E-E^\ast)=O(r_n/n)\to0$, while $r_n\to\infty$. ∎

**Theorem 7.4 (The capacity jump at the two-hub boundary).** At the two adjacent budgets,

$$
\lim_{n\to\infty}nE^\ast(n,n-3)=4,\qquad
\lim_{n\to\infty}nE^\ast(n,n-2)=9.
$$

For all sufficiently large $n$, the unique minimizer at $\ell=n-3$ is $K_{2,n-2}$, while the unique minimizer at $\ell=n-2$ is the balanced member of $\mathcal C(n,n-2)$, with three triple sources and $n-6$ pair sources. Thus the one-edge increase crosses a genuine finite-capacity jump; the common ratio limit $\ell/n\to1$ does not identify the two values.

**Proof.** For $\ell=n-3$, $K_{2,n-2}$ is admissible and

$$
E(K_{2,n-2})=2(n-2)g(2/(n-2)),\qquad nE(K_{2,n-2})\to4.
$$

Every minimizer has excess $O(1/n)$, so Theorem 3.1 applies with a fixed constant. If a subsequence had at least three sinks, pass to a fixed bounded sink number and use (7.2) with $\beta\to1$; its normalized excess has liminf at least $L_3^{\rm low}(1)=27/4>4$. Hence eventually there are two sinks. Their two-layer simple graph has at most $2(n-2)=2n-4$ edges, exactly the required number, so every source is adjacent to both hubs and the graph is $K_{2,n-2}$. For $\ell=n-2$, Theorem 7.2 applies and gives the second limit as $F_3(1)=9$, with $c=3$ and $b=n-6$. ∎

The new statements in this section are repo-derived. The CDSO definition and the earlier conjectural universal-vertex scope are supplied by Albalahi--Das--Ali--Barman--Hamza, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176). The single-cycle comparison and the two-hub construction cited in the preceding volume remain intermediate references from Ali--Das--Attiya, DOI [10.47443/dml.2025.192](https://doi.org/10.47443/dml.2025.192), and Albalahi, DOI [10.47443/dml.2026.217](https://doi.org/10.47443/dml.2026.217); neither is used as a theorem about this three-hub interval. The coordinate-increasing hypotheses in Liu--Du--Huang--Chen--Elumalai, MATCH 91 (2024), 255--266, DOI [10.46793/match.91-1.255L](https://doi.org/10.46793/match.91-1.255L), and the separable-form and density hypotheses in Ali--Gutman--Saber--Alanazi, MATCH 87 (2022), 89--96, DOI [10.46793/match.87-1.089A](https://doi.org/10.46793/match.87-1.089A), do not apply to the CDSO kernel, so their extremal theorems are not invoked here. The threshold, gap, actual exchanges, exact integer formula, near-minimum characterization and capacity jump are proved above for the stated finite simple connected graph class. The preceding citations are the sources checked for the statements above. The full text of the Zhao--Zhao source was not obtained, so its overlap with these results remains unassessed and no priority claim is made for that source.

## 追加锚（本行以下为增补区）
