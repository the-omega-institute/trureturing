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
