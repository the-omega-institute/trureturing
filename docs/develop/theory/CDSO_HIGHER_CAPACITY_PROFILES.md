# CDSO higher-capacity profiles and the four-hub phase

## 1. Graphs and joint profiles

All graphs below are finite, simple and connected. For integers $n\ge2$ and $\ell\ge0$, let $\mathcal G(n,\ell)$ be the graphs with $n$ vertices and

$$
m=n-1+\ell
$$

edges. For an edge $uv$ write

$$
r_{uv}=\frac{\min(d_u,d_v)}{\max(d_u,d_v)},\qquad
g(r)=\sqrt{1+r^2}-1,
$$

and set

$$
E(G)=\sum_{uv\in E(G)}g(r_{uv}),\qquad
\Phi(G)=m+E(G),
$$

so minimizing the CDSO index $\Phi$ at fixed $(n,\ell)$ is the same as minimizing $E$. These are the conventions of *CDSO sink incidences and density limits*, §§1--3.

A two-layer graph has independent hubs $[s]=\{1,\ldots,s\}$ and sources outside $[s]$, with every edge joining a source to a hub. For a source $v$, write $T(v)\subseteq[s]$ for its nonempty hub neighborhood. If $N_T$ is the number of sources with $T(v)=T$, put

$$
N_s=n-s,\qquad x_T=\frac{N_T}{N_s},\qquad
y_i=\sum_{T\ni i}x_T.
$$

The same source distribution determines every quantity below. Its mean source degree and excess are

$$
q=\sum_{\varnothing\ne T\subseteq[s]}|T|x_T=\sum_{i=1}^s y_i,
\qquad a=q-1=\sum_T(|T|-1)x_T.
$$

The normalized joint profile domain is

$$
\mathcal P_s(a)=\left\{(x_T):
\begin{array}{l}
x_T\ge0,\quad \sum_Tx_T=1,\quad \sum_T(|T|-1)x_T=a,\\
 y_i=\sum_{T\ni i}x_T>0\quad(1\le i\le s)
\end{array}\right\}.
$$

For $x\in\mathcal P_s(a)$ define the profile energy

$$
J_s(x)=\frac12\sum_Tx_T|T|^2\sum_{i\in T}\frac1{y_i^2}.
$$

The positivity condition on every $y_i$ is the finite-energy hub condition. Types of zero mass remain in the domain.

For an actual two-layer graph, the same edge count gives

$$
\sum_TN_T=N_s,\qquad
\sum_T(|T|-1)N_T=\ell+s-1,
\qquad D_i=\sum_{T\ni i}N_T,
$$

and therefore

$$
a=\frac{\ell+s-1}{N_s},\qquad q=\frac{m}{N_s}.
$$

The elementary remainder identity

$$
0\le \frac{r^2}{2}-g(r)
=\frac{r^4}{2(\sqrt{1+r^2}+1)^2}
\le \frac{r^4}{8}
$$

will always be applied to the actual source--hub edges.

## 2. The complete joint optimization in the four-hub capacity window

**Lemma 2.1 (A residual identity).** Let $s\ge2$, let $q\in[s-1,s]$, and let $x\in\mathcal P_s(q-1)$. Set

$$
d_T=s-|T|,\qquad \delta=\sum_Tx_Td_T=s-q.
$$

For each $i$ define

$$
w_i=\sum_{T\ni i}|T|^2x_T.
$$

Then

$$
w_i=(s-1)^2y_i+(2s-1)(q-s+1)+R_i,
$$

where

$$
R_i=(2s-1)\sum_{T\not\ni i}x_T(d_T-1)
+\sum_{T\ni i}x_Td_T(d_T-1)\ge0.
$$

Consequently,

$$
J_s(x)\ge
\frac{s^2\bigl((3s^2-3s+1)q-s(s-1)(2s-1)\bigr)}{2q^2}.
$$

Equality holds exactly when

$$
x_{[s]}=q-s+1,
\qquad
x_{[s]\setminus\{i\}}=\frac{s-q}{s}\quad(1\le i\le s),
$$

and every other type has zero mass.

**Proof.** For an incidence $i\in T$, the identity

$$
|T|^2=(s-1)^2+(2s-1)(1-d_T)+d_T(d_T-1)
$$

holds. Summing over $T\ni i$ and adding and subtracting the global sum $(2s-1)\sum_Tx_T(1-d_T)=(2s-1)(q-s+1)$ gives the displayed $R_i$. If $i\notin T$, then $d_T\ge1$; if $i\in T$, then $d_T\ge0$, so every summand in $R_i$ is nonnegative.

Since $2J_s=\sum_iw_i/y_i^2$, we obtain

$$
2J_s\ge (s-1)^2\sum_i\frac1{y_i}
 +(2s-1)(q-s+1)\sum_i\frac1{y_i^2}.
$$

The coefficient of the second sum is nonnegative. Strict convexity of $t\mapsto t^{-1}$ and $t\mapsto t^{-2}$, together with $\sum_i y_i=q$, gives

$$
\sum_i y_i^{-1}\ge\frac{s^2}{q},
\qquad
\sum_i y_i^{-2}\ge\frac{s^3}{q^2}.
$$

Substitution gives the bound. Equality forces all $y_i=q/s$ and every $R_i=0$. A positive type of size at most $s-2$ would contribute a positive term to $R_i$ for some $i\in T$, so only sizes $s-1$ and $s$ can occur. The common mass and the equal marginals then force the displayed values. Direct substitution gives equality. ∎

For $s=4$ write

$$
F_4(a)=\frac{8(37a-47)}{(a+1)^2}.
$$

**Theorem 2.2 (Four-hub profile minimum and all equality cases).** For every $a\in[2,3]$,

$$
\min_{x\in\mathcal P_4(a)}J_4(x)=F_4(a).
$$

The unique profile attaining equality is

$$
x_{[4]}=a-2,
\qquad
x_{[4]\setminus\{i\}}=\frac{3-a}{4}\quad(1\le i\le4),
$$

with all one-, two- and other types of mass zero. The endpoint profiles are included: at $a=2$ the full type has zero mass, and at $a=3$ all mass is on the full type.

**Proof.** Apply Lemma 2.1 with $s=4$ and $q=a+1$. Its lower bound is

$$
J_4(x)\ge
\frac{16(37q-84)}{2q^2}=F_4(a),
$$

and its equality statement gives exactly the stated profile. ∎

**Lemma 2.3 (A scalar certificate for every integer source size).** For every integer $k\ge1$ and every $0<y\le1$,

$$
\frac{k^2}{y^2}
\ge \frac{16}{y}+\frac{64}{3}\left(1-\frac4k\right).
$$

**Proof.** Put $z=1/y\ge1$ and

$$
P_k(z)=k^2z^2-16z-\frac{64}{3}\left(1-\frac4k\right).
$$

For $k=1,2,3$,

$$
P_1(z)=(z-8)^2,
$$

$$
P_2(z)=4(z-2)^2+\frac{16}{3},
$$

$$
P_3(z)=9(z-1)^2+2(z-1)+\frac19.
$$

For $k\ge4$,

$$
P_k(z)=k^2(z-1)^2+(2k^2-16)(z-1)
 +\frac{(k-4)(3k^2+12k-64)}{3k},
$$

whose terms are nonnegative. ∎

**Theorem 2.4 (All finite hub numbers are strictly worse in the four-hub window).** Let $a\in[2,3]$. For every finite $s\ge5$ and every $x\in\mathcal P_s(a)$,

$$
J_s(x)\ge 8s+\frac{32}{3}(a-3)>F_4(a)+4.
$$

Hence

$$
\min_{s\ge4}\ \min_{x\in\mathcal P_s(a)}J_s(x)=F_4(a),
$$

and the equality profile is exactly the one in Theorem 2.2.

**Proof.** Apply Lemma 2.3 to every incidence $(T,i)$ with $i\in T$, writing $k=|T|$ and $y=y_i$. Since $y_i\le1$,

$$
\begin{aligned}
2J_s(x)
&=\sum_Tx_T|T|^2\sum_{i\in T}y_i^{-2}\\
&\ge16\sum_T\sum_{i\in T}\frac{x_T}{y_i}
 +\frac{64}{3}\sum_Tx_T|T|\left(1-\frac4{|T|}\right)\\
&=16s+\frac{64}{3}(q-4)
 =16s+\frac{64}{3}(a-3).
\end{aligned}
$$

The first incidence identity is exact because
$\sum_T\sum_{i\in T}x_T/y_i=\sum_i y_i/y_i=s$. Dividing by two proves the first bound. For $s\ge5$ it is enough to compare with $s=5$. Put $u=a-2\in[0,1]$. A direct expansion gives

$$
3(a+1)^2\left(40+\frac{32}{3}(a-3)-F_4(a)-4\right)
=36(1-2u)^2+124u^2+32u^3>0.
$$

Thus every $s\ge5$ has a strict gap. Theorem 2.2 supplies the four-hub value and its complete equality conditions. ∎

The first inequality in this proof, before the comparison with $F_4$, remains valid whenever the profile domain is nonempty, with no restriction $a\in[2,3]$.

## 3. Exact integer budgets and connected realizations

**Theorem 3.1 (Exact-budget realization of every finite profile).** Fix a finite $s\ge4$, a number $a\in[2,3)$, and a profile $x\in\mathcal P_s(a)$. Let $(\ell_n)$ be any integer sequence with $\ell_n\ge1$ and $\ell_n/n\to a$. For all sufficiently large $n$ there is a simple connected two-layer graph $G_n\in\mathcal G(n,\ell_n)$ with exactly $s$ hubs such that

$$
\frac{N_{T,n}}{n-s}\longrightarrow x_T,
\qquad
\frac{D_{i,n}}{n-s}\longrightarrow y_i,
\qquad
nE(G_n)\longrightarrow J_s(x).
$$

Every prescribed integer budget $\ell_n$ is used exactly.

**Proof.** Reserve $s$ hubs and $s-1$ source vertices. Join the reserved sources respectively to

$$
\{1,2\},\ \{2,3\},\ \ldots,\ \{s-1,s\}.
$$

These sources form a subdivided path through all hubs. Let

$$
M=n-2s+1
$$

be the number of remaining sources. Round the finitely many numbers $Mx_T$ to nonnegative integer counts summing to $M$, with an error bounded independently of $n$ in every type. Initially assign those neighborhoods to the remaining sources. If $B$ denotes their total excess membership,

$$
B=\sum_T(|T|-1)N_T=M a+O_s(1)=\ell_n+o(n).
$$

The reserved path contributes exactly $s-1$ to the total excess, so the ordinary sources must have total excess exactly $\ell_n$. Since $a<s-1$, for all sufficiently large $n$,

$$
0\le\ell_n\le(s-1)M.
$$

If $B<\ell_n$, add one missing hub membership to a source whose neighborhood is not all of $[s]$. If $B>\ell_n$, delete one membership from a source having at least two neighbors. The required operation is always available until $B=\ell_n$, and it changes the type counts by at most $|B-\ell_n|=o(n)$. All neighborhoods remain nonempty subsets of $[s]$.

The reserved path is unchanged, so the graph stays connected. Its edge count is

$$
2(s-1)+M+\ell_n=n-1+\ell_n.
$$

The hub degrees are linear because each $y_i>0$, whereas all source degrees are at most $s$; hence the hubs are the actual higher-degree endpoints for all sufficiently large $n$. On every edge the source degree is bounded and the hub degree is linear. Using the remainder identity in §1 gives

$$
E(G_n)=\frac{J_s(x_n)}{n-s}+O(n^{-3}),
$$

where $x_n$ is the adjusted profile and $x_n\to x$. Multiplication by $n$ proves the limit. ∎

## 4. The finite four-hub capacity phase

For integers $n,\ell$ in the range

$$
 n\ge3{,}000{,}000,
\qquad 2n-7\le\ell\le3n-15,
$$

put

$$
N=n-4,
\qquad c=\ell-2n+11,
\qquad b=3n-\ell-15.
$$

Then

$$
4\le c\le N,\qquad b\ge0,\qquad b+c=N,\qquad 3b+4c=n-1+\ell.
$$

Let $b=4q+r$ with $0\le r\le3$. For a nonnegative integer parameter $c$, define, for real $D>0$,

$$
M_c(D)=(D-c)g(3/D)+c\,g(4/D),
$$

and let $H^{(4)}_{n,\ell}$ be the two-layer graph with four hubs, $c$ sources adjacent to all four hubs, and $b$ sources adjacent to all but one hub, with the four missing-hub counts equal to $q+1$ for $r$ hubs and $q$ for the other $4-r$ hubs. Its hub degrees are $N-q-1$ on the first group and $N-q$ on the second group.

**Lemma 4.1 (The balanced candidate has a uniform upper bound).** With $a_4=(\ell+3)/N\in[2,3]$,

$$
E(H^{(4)}_{n,\ell})
\le \frac{F_4(a_4)}{N}+\frac{204}{N^3}<\frac{34}{n}.
$$

**Proof.** Put $y_i=D_i/N$. The four missing-hub counts differ by at most one, so

$$
\sum_{i=1}^4\left(y_i-\frac{a_4+1}{4}\right)^2\le\frac1{N^2}.
$$

For the pure three- and four-neighborhood profile,

$$
J_4=\sum_{i=1}^4h_{a_4}(y_i),
\qquad
h_a(y)=\frac9{2y}+\frac{7(a-2)}{2y^2}.
$$

On $1/2\le y\le1$ and $2\le a\le3$,

$$
0<h_a''(y)=\frac9{y^3}+\frac{21(a-2)}{y^4}\le408.
$$

Taylor's theorem around $(a_4+1)/4$, whose first-order terms sum to zero, gives

$$
J_4\le F_4(a_4)+204N^{-2}.
$$

Since $g(t)\le t^2/2$, the same upper bound divided by $N$ holds for $E(H^{(4)}_{n,\ell})$. Finally $F_4(a_4)\le32$ and
$(1+4/N)(32+204/N^2)<34$ for $N\ge2{,}999{,}996$. ∎

**Theorem 4.2 (Exact four-hub minimum at the specified finite orders).** For every integer pair $(n,\ell)$ in the range above, $H^{(4)}_{n,\ell}$ is the unique minimizing isomorphism class in $\mathcal G(n,\ell)$. Its exact minimum excess is

$$
E^\ast(n,\ell)
=(4-r)M_c(N-q)+rM_c(N-q-1),
$$

and the exact minimum CDSO index is

$$
\Phi^\ast(n,\ell)=n-1+\ell+E^\ast(n,\ell).
$$

**Proof.** Let $G$ minimize $E$ and compare it with $H^{(4)}_{n,\ell}$. Lemma 4.1 gives $E(G)<34/n$. The sink-incidence reduction in *CDSO sink incidences and density limits*, Theorem 3.1, with $C=34$, applies because its explicit sufficient threshold is

$$
36\cdot34^2\cdot69=2{,}871{,}504<3{,}000{,}000.
$$

Thus $G$ is two-layer, has at most nine hubs, and every hub degree is at least $n/102$. A two-layer graph with $s\le3$ hubs has at most $s(n-s)\le3n-9$ edges, while the present graphs have
$m\ge3n-8$; hence $s\ge4$.

Suppose $s\ge5$. Put $N_s=n-s$ and $a_s=(\ell+s-1)/N_s$. The scalar incidence bound in the proof of Theorem 2.4 is valid for this $a_s$ as well, and the edge remainder gives

$$
E(G)\ge \frac{J_s}{N_s}-\frac{B}{n^3},
\qquad
B=\frac{9^4 102^4}{2}=355091870088.
$$

Because $s\ge5$, $a_s\ge a_4$, and the certificate is increasing in $s$ and $a$, so

$$
E(G)\ge\frac{40+\frac{32}{3}(a_4-3)}{N}-\frac{B}{n^3}
>\frac{F_4(a_4)+4}{N}-\frac{B}{n^3}.
$$

The last expression is larger than the upper bound in Lemma 4.1: indeed

$$
\frac{B}{n^2}+\frac{204}{N^2}<4
$$

at $n\ge3{,}000{,}000$. This contradiction leaves $s=4$.

For four hubs, Lemma 2.1 gives, for every hub $i$,

$$
\sum_{T\ni i}|T|^2N_T\ge9D_i.
$$

Every edge cost is at most $34/n$, so the edge inequality
$g(r)\ge r^2/(2+34/n)$ and the preceding display imply

$$
E(G)\ge\frac9{(2+34/n)D_i}.
$$

Since $E(G)<34/n$ and $n\ge3{,}000{,}000$, this gives $D_i\ge n/8$ for every hub. The remainder bound now improves to

$$
E(G)\ge\frac{J_4}{N}-\frac{B_0}{n^3},
\qquad
B_0=\frac{4^4 8^4}{2}=524288.
$$

Let $p_k=\sum_{|T|=k}x_T$. Summing the residuals in Lemma 2.1 for $s=4$ gives

$$
\sum_iR_i=48p_1+18p_2.
$$

Because $y_i\le1$, the exact decomposition in that lemma yields

$$
J_4\ge F_4(a_4)+24p_1+9p_2.
$$

If $p_1+p_2>0$, integrality gives $24p_1+9p_2\ge9/N$, and therefore

$$
E(G)\ge\frac{F_4(a_4)}N+\frac9{N^2}-\frac{B_0}{n^3}
>\frac{F_4(a_4)}N+\frac{204}{N^3}\ge E(H^{(4)}_{n,\ell}),
$$

where the strict inequality follows from
$B_0/n+204/N<9$. Hence $p_1=p_2=0$.

It follows that exactly $c$ sources have degree four and exactly $b$ have degree three. If $b_i$ is the number of degree-three sources missing hub $i$, then

$$
\sum_i b_i=b,\qquad D_i=N-b_i,\qquad
E(G)=\sum_{i=1}^4M_c(D_i).
$$

For $f_k(D)=g(k/D)$,

$$
 f_k''(D)=\frac{k^2(3D^2+2k^2)}{D^3(D^2+k^2)^{3/2}}.
$$

Writing

$$
Q_D(t)=\frac{t(3D^2+2t)}{(D^2+t)^{3/2}},
$$

we have

$$
Q_D'(t)=\frac{6D^4+5D^2t+2t^2}{2(D^2+t)^{5/2}}>0.
$$

Also

$$
M_c''(D)=\frac9{(D^2+9)^{3/2}}+c\bigl(f_4''(D)-f_3''(D)\bigr)>0.
$$

If $D_j\ge D_i+2$, then $b_i\ge b_j+2$, so choose a degree-three source $v$ missing $i$. It is adjacent to $j$. Delete $vj$ and add $vi$, making $v$ a source missing $j$. Since $vi$ was absent, no repeated edge or loop is introduced. The $c\ge4$ full-neighborhood sources are unchanged and connect all four hubs; every other source still has three or four hub neighbors. Thus the graph remains simple and connected, with the same $n,m,\ell$, the same numbers of hubs and sources, and the same source-degree counts $b,c$. Only $(D_i,D_j)$ changes, to $(D_i+1,D_j-1)$, and strict convexity of $M_c$ strictly lowers the energy. Repeating the exchange proves that every minimizer has the four $b_i$ differing by at most one. The resulting multiset is uniquely $q+1$ repeated $r$ times and $q$ repeated $4-r$ times. The full and missing-one neighborhoods then determine the graph up to hub and source relabelling, giving the stated unique isomorphism class and exact value. ∎

## 5. Density limits and complete near-minimum structure

**Theorem 5.1 (The four-hub density phase).** Let $(\ell_n)$ be an integer sequence with

$$
\frac{\ell_n}{n}\longrightarrow\alpha\in[2,3),
\qquad
\ell_n\ge2n-7
$$

for all sufficiently large $n$. Then eventually $\ell_n\le3n-15$, and

$$
\lim_{n\to\infty}nE^\ast(n,\ell_n)
=F_4(\alpha)=\frac{8(37\alpha-47)}{(1+\alpha)^2}.
$$

For any choice $G_n\in\mathcal G(n,\ell_n)$, the following are equivalent:

1. $E(G_n)-E^\ast(n,\ell_n)=o(n^{-1})$;
2. $nE(G_n)\to F_4(\alpha)$;
3. After labelling the hubs whenever they exist, $G_n$ is eventually a two-layer graph with exactly four hubs, and its profile satisfies
   $$
   x_{[4],n}\to\alpha-2,
   \qquad
   x_{[4]\setminus\{i\},n}\to\frac{3-\alpha}{4}\quad(1\le i\le4),
   $$
   while the total mass of all one- and two-neighborhood types tends to zero. Equivalently, $G_n$ is eventually a two-layer graph with exactly four hubs, the total mass of all one- and two-neighborhood types tends to zero, and
   $$
   \frac{D_{i,n}}n\to\frac{1+\alpha}{4}\quad(1\le i\le4).
   $$

The exact finite minimizers supplied by Theorem 4.2 have no one- or two-neighborhood sources. Near-minimizing sequences only force their total number to be $o(n)$; zero-limit types may occur at finitely many or sublinear many vertices to provide a connected bridge.

**Proof.** Since $\alpha<3$, the upper finite capacity inequality holds eventually, so Theorem 4.2 applies and gives the exact minimum for all sufficiently large $n$. Its balanced profile has $a_4\to\alpha$, and the same remainder estimate used in §4 gives

$$
 nE^\ast(n,\ell_n)\longrightarrow F_4(\alpha).
$$

Thus (1) and (2) are equivalent.

Assume (2). The sequence has bounded $nE(G_n)$, so the sink-incidence reduction gives an eventual two-layer graph with a bounded number of hubs and hub degrees bounded below linearly. Passing to a subsequence with fixed hub number and a convergent profile is legitimate because there are finitely many types for each fixed number. The exact edge identities give a limit profile in $\mathcal P_s(\alpha)$. Write $x_n$ for the profiles on this fixed-$s$ subsequence and $x$ for their limit. Choose a fixed $C>0$ bounding $nE(G_n)$. The same actual-edge calculation as in §3 applies uniformly: the fixed-$C$ reduction bounds $s$ solely in terms of $C$ and gives $D_{i,n}\ge n/(3C)$, so source degrees are bounded, every edge ratio is $O_C(n^{-1})$, and there are $O_C(n)$ edges. Summing the remainder in §1 therefore gives an $O_C(n^{-3})$ error in $E(G_n)$, and hence

$$
nE(G_n)-\frac{n}{n-s}J_s(x_n)=O_C(n^{-2})\longrightarrow0.
$$

The same degree bound gives $y_{i,n}=D_{i,n}/(n-s)\ge1/(3C)>0$. Thus $J_s$ is continuous at the limit profile, including boundary faces where some type masses vanish while all hub masses remain positive, and $J_s(x_n)\to J_s(x)$. Since $n/(n-s)\to1$, it follows that $nE(G_n)\to J_s(x)$. If $s\ge5$ occurs infinitely often, Theorem 2.4 gives a limiting value strictly larger than $F_4(\alpha)$, a contradiction. The capacity inequality excludes $s\le3$ because $\ell_n\ge2n-7$. Hence exactly four hubs occur eventually. Every profile limit must attain equality in Theorem 2.2, so all profile limits are the unique profile displayed in (3). Therefore the whole sequence of profiles converges, including the vanishing total mass of the one- and two-neighborhood types and the hub-degree limits.

To verify the alternative formulation of (3), use the same profile array throughout and put

$$
p_{k,n}=\sum_{|T|=k}x_{T,n},\qquad
L_{i,n}=\sum_{\substack{|T|\le2\\i\in T}}x_{T,n},\qquad
y_{i,n}=\frac{D_{i,n}}{n-4}.
$$

Its exact mean constraint is $a_n=(\ell_n+3)/(n-4)=p_{2,n}+2p_{3,n}+3p_{4,n}\to\alpha$. Together with $\sum_{k=1}^4p_{k,n}=1$, it gives the exact identities

$$
p_{4,n}=a_n-2+2p_{1,n}+p_{2,n},
\qquad
x_{[4]\setminus\{i\},n}
=1-p_{1,n}-p_{2,n}+L_{i,n}-y_{i,n}.
$$

Since $0\le L_{i,n}\le p_{1,n}+p_{2,n}$ and $(n-4)/n\to1$, vanishing one- and two-type mass together with $D_{i,n}/n\to(1+\alpha)/4$ forces $p_{4,n}\to\alpha-2$ and each missing-one mass to tend to $(3-\alpha)/4$. Conversely, the complete candidate profile in (3) gives

$$
y_{i,n}=p_{4,n}+\sum_{j\ne i}x_{[4]\setminus\{j\},n}+L_{i,n}
\longrightarrow\alpha-2+\frac{3(3-\alpha)}4=\frac{1+\alpha}4,
$$

and hence the stated hub-degree limits. Both formulations retain the eventual four-hub two-layer condition and the vanishing one- and two-type mass.

Conversely, (3) gives a profile converging to the equality profile of Theorem 2.2. The actual-edge remainder identity then gives $nE(G_n)\to F_4(\alpha)$, proving (3)$\Rightarrow$(2). ∎

The lower capacity condition has a genuine endpoint obstruction. At $\ell=2n-8$, the graph $K_{3,n-3}$ belongs to $\mathcal G(n,\ell)$ and

$$
 nE(K_{3,n-3})\longrightarrow\frac{27}{2},
$$

whereas $F_4(2)=24$. Thus density $\alpha=2$ alone does not replace the exact lower budget $\ell\ge2n-7$. At the other boundary, $\ell=3n-14$ exceeds the four-hub simple two-layer capacity $3n-15$; the four-hub theorem therefore stops at $\alpha<3$ and makes no claim for the next capacity phase.

## 6. Literature and scope

The fixed-order conventions and the earlier two-hub convexity, expansion and density arguments are in [*CDSO minimizers without a universal vertex for every cyclomatic number*](CDSO_UNIVERSAL_VERTEX_ALL_CYCLOMATIC.md), §8 (*The unique eventual minimizer*) and §§10--12 (*A linear range for rigidity and the exact minimum*, *Uniform hub expansion and quantitative stability*, and *Limits with varying cyclomatic number*); the density theorem in §12 covers $0\le\alpha<1/8$ and a conditional endpoint at $\alpha=1/8$. The fixed-$C$ two-layer reduction used in §§4--5 is [*CDSO sink incidences and density limits*](CDSO_SINK_INCIDENCE_AND_DENSITY_LIMITS.md), Theorem 3.1 (*Uniform two-layer reduction at fixed cost*). Its Theorems 5.2--5.3 (*Necessary profiles and exact-budget realization* and *The hub boundary and the unique global optimizing profile*) give the preceding actual joint-profile/realization interface and hub-boundary analysis in their stated range $0\le\alpha<1$. Those subunit-density conclusions do not supply the four-hub phase by extrapolation. The actual-edge bridge needed here is derived in §§1 and 3 and applied uniformly in §§4--5 of this volume, and the exact-budget realization is proved in Theorem 3.1 here; the new load-bearing profile relations are the residual identity in Lemma 2.1 and the scalar certificate in Lemma 2.3.

The original CDSO definition and the universal-vertex conjecture are in A. M. Albalahi, S. Das, A. Ali, J. Barman and A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*, Discrete Mathematics Letters 16 (2025), 108--115, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176), §1 and §4. The unicyclic comparison recorded in A. Ali, K. C. Das and A. A. Attiya, *Bond incident degree indices of fixed-order unicyclic graphs*, Discrete Mathematics Letters 16 (2025), 135--142, DOI [10.47443/dml.2025.192](https://doi.org/10.47443/dml.2025.192), Remark 2.3, is prior one-cycle evidence and is not used as a high-density profile theorem. The two-hub construction in A. M. Albalahi, *On Two Conjectures Concerning the Hyperbolic Sombor Index and Its Counterpart*, Discrete Mathematics Letters 18 (2026), 122--128, DOI [10.47443/dml.2026.217](https://doi.org/10.47443/dml.2026.217), Proposition 2.1, is likewise a cited intermediate construction; its maximum theorem is a different extremal problem.

The coordinate-increasing hypothesis in H. Liu, Z. Du, Y. Huang, H. Chen and S. Elumalai, *Note on the Minimum Bond Incident Degree Indices of $k$-Cyclic Graphs*, MATCH Communications in Mathematical and Computer Chemistry 91 (2024), 255--266, DOI [10.46793/match.91-1.255L](https://doi.org/10.46793/match.91-1.255L), does not hold for $g(y/x)$ at fixed $y$ when $x>y$. Likewise, condition P2 in M. Bašić, *A general algebraic characterization of extremal $\Delta$-trees and $k$-cyclic graphs for degree-homogeneous VDB indices*, [arXiv:2610.34361](https://arxiv.org/abs/2610.34361), is not satisfied by CDSO for $x<\Delta$. Those results therefore do not supply the four-hub theorem above.

The full text of Zhao--Zhao, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), has not been obtained; its overlap with these results and the associated priority questions remain unassessed. Its abstract is not used to exclude overlap, and the finite literature comparison here does not certify global originality.

The fixed-density statements here concern $\alpha\in[2,3)$ and the exact lower budget stated in Theorem 5.1. They do not determine the exact minimum for a fixed $s\ge5$, the least finite order threshold below $3{,}000{,}000$, or any capacity phase beginning at $\alpha=3$.

## 追加锚（本行以下为增补区）
