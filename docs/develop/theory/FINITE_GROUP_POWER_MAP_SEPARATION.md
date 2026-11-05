# Finite groups with separately isomorphic power maps and no simultaneous power bijection

## 1. Definitions and the two groups

**定义 1.1（The two power relations）。** For a finite group $S$ and an integer $m$, let $\Gamma_m(S)$ have vertex set $S$ and precisely the directed edges $x\longrightarrow x^m$, including loops. Thus an isomorphism $\Gamma_m(S)\cong\Gamma_m(S')$ is a bijection $f_m:S\to S'$ satisfying $f_m(x^m)=f_m(x)^m$ for every $x$. Write

$$
\begin{aligned}
S\sim_5 S'&\iff (\forall m\in\mathbb Z)(\exists f_m:S\overset\sim\longrightarrow S')
                 (\forall x\in S)\ f_m(x^m)=f_m(x)^m,\\
S\sim_2 S'&\iff (\exists f:S\overset\sim\longrightarrow S')
                 (\forall x\in S)(\forall m\in\mathbb Z)\ f(x^m)=f(x)^m.
\end{aligned}
$$

These are Definition 1.4, Definition 1.5(2,5), and Remark 1.6 of Fernandes–Qureshi–Reis–Ribas [F]. Their Problem 6.1 asks whether $S\sim_5 S'$ and $S\not\sim_2 S'$ can hold for fixed finite groups.

**定义 1.2（Bilinear data and multiplication）。** Put $F=\mathbb F_3$, $V=F^2$, $W=F^3$, and $Z=F^2$. Coordinates and the values of the following maps are in $F$:

$$
\begin{aligned}
B_0(v,w)&=(v_1w_1+v_2w_2,\ v_1w_2+v_2w_3),\\
B_1(v,w)&=(v_1w_1-v_2w_2,\ v_2w_1+v_1w_2).
\end{aligned}                                                    \tag{1.1}
$$

For $i\in\{0,1\}$, give $P_i=V\times W\times Z$ the operation

$$
(v,w,z)(v',w',z')=(v+v',w+w',z+z'+B_i(v,w')).                    \tag{1.2}
$$

Set $\tau_i(v,w,z)=(v,-w,-z)$. On $S_i=P_i\times\mathbb Z/2\mathbb Z$ use the operation

$$
(p;\epsilon)(p';\epsilon')=
(p\,\tau_i^\epsilon(p');\epsilon+\epsilon').                     \tag{1.3}
$$

The identity is denoted by $1$; in coordinates it is $(0,0,0;0)$. We identify $P_i$ with the subset of $S_i$ having last coordinate $0$. The group laws for (1.2)–(1.3) are proved below.

The bilinear group construction is classical. More precisely, Wilson [W, §3, (3.1)][W] uses matrices $L_j$ with bilinear coordinates $v^{\mathsf T}L_jw$. For $P_0$ the parameters are $p=3$, $r=2$, $s=3$, $t=2$, and

$$
L_{01}=\begin{pmatrix}1&0&0\\0&1&0\end{pmatrix},\qquad
L_{02}=\begin{pmatrix}0&1&0\\0&0&1\end{pmatrix}.                  \tag{1.4}
$$

These rectangular matrices also occur in [W, proof of Lemma 3.5][W] with $e=3$. Their common kernel is zero, so the matrix realization retains all three coordinates of $w$. For $P_1$, write $E=F[\iota]/(\iota^2+1)$. Since $-1$ is not a square in $F$, $E$ is a field of order $9$. Identifying $(v_1,v_2)$, $(w_1,w_2)$, and $z$ with elements of $E$ makes $B_1$ multiplication in $E$. Consequently

$$
P_1\cong H(E)\times(F,+),\qquad
H(E)=\{(a,b,c):a,b,c\in E\},\quad
(a,b,c)(a',b',c')=(a+a',b+b',c+c'+ab').                          \tag{1.5}
$$

The last factor in (1.5) is the coordinate $w_3$. The two matrices for $H(E)$ are $\left(\begin{smallmatrix}1&0\\0&-1\end{smallmatrix}\right)$ and $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$, as in [W, Example 3.4][W]. In particular that extra $F$ factor is retained; omitting it would change the group in (1.3).

**定理 1.3（Separate power graphs do not determine simultaneous powers）。** The operations (1.2)–(1.3) define finite groups. The fixed pair

$$
G=S_0=P_0\rtimes_{\tau_0}C_2,\qquad
H=S_1=P_1\rtimes_{\tau_1}C_2
$$

has $|G|=|H|=2\cdot3^7$ and satisfies

$$
(\forall m\in\mathbb Z)\ \Gamma_m(G)\cong\Gamma_m(H),
\qquad G\not\sim_2 H.                                          \tag{1.6}
$$

In fact no bijection $G\to H$ preserves both squares and cubes. The proof of (1.6) is given in §§2–5. The classical inputs are the definitions in [F], the bilinear groups just identified in [W], and elementary finite-field and group identities. The additional inference is the combination of the two semidirect products, their complete power-graph component descriptions, and an obstruction defined jointly by squares and cubes.

## 2. Group laws, orders, and the bilinear fibers

Proof of Theorem 1.3. Fix $i$ and abbreviate $B_i$ by $B$. Bilinearity gives the cocycle identity

$$
B(v,w')+B(v+v',w'')=B(v',w'')+B(v,w'+w'').                     \tag{2.1}
$$

The first two coordinates of either association in (1.2) are coordinate sums, and (2.1) equates their last coordinates. Thus (1.2) is associative. Its identity and inverse are

$$
1_{P_i}=(0,0,0),\qquad
(v,w,z)^{-1}=(-v,-w,-z+B(v,w)).                                 \tag{2.2}
$$

Substitution in both orders verifies (2.2). Also

$$
\begin{aligned}
(v,w,z)^2&=(2v,2w,2z+B(v,w)),\\
(v,w,z)^3&=(0,0,3z+B(v,w)+B(2v,w))=(0,0,0).
\end{aligned}                                                    \tag{2.3}
$$

Therefore $P_i$ has $3^7$ elements and every nonidentity element has order $3$.

The map $\tau_i$ squares to the identity. Applying it to a product changes the last coordinate to $-z-z'-B(v,w')$; multiplying the two images gives the same coordinate because $B(v,-w')=-B(v,w')$. Hence $\tau_i$ is an automorphism. Associativity of (1.3) follows explicitly from

$$
\bigl(p\tau_i^\epsilon(p')\bigr)\tau_i^{\epsilon+\epsilon'}(p'')
=p\tau_i^\epsilon\bigl(p'\tau_i^{\epsilon'}(p'')\bigr).
$$

Its identity is $(1_{P_i};0)$ and the inverse of $(p;\epsilon)$ is $(\tau_i^\epsilon(p^{-1});\epsilon)$. This proves that $S_i$ is a group of order $2\cdot3^7$ with normal subgroup $P_i$ and quotient $C_2$.

For every $v\ne0$, the map $B_i(v,-):W\to Z$ is onto with kernel of size $3$. For $i=0$ its matrix is

$$
\begin{pmatrix}v_1&v_2&0\\0&v_1&v_2\end{pmatrix}.
$$

If $v_1\ne0$, the first two columns have determinant $v_1^2\ne0$. If $v_1=0$, then $v_2\ne0$ and the last two columns have determinant $v_2^2\ne0$. For $i=1$ the first two columns form

$$
\begin{pmatrix}v_1&-v_2\\v_2&v_1\end{pmatrix}.
$$

Its determinant $v_1^2+v_2^2$ is nonzero: every nonzero square in $F$ is $1$, so this sum is $1$ or $2$ when $v\ne0$. In both cases the linear map has rank $2$ and a one-dimensional kernel. Every fiber therefore has exactly $3$ elements.

The common right kernels, by contrast, are different. Define

$$
K_i=\{w\in W:B_i(v,w)=0\text{ for every }v\in V\}.
$$

Testing $v=(1,0)$ and $v=(0,1)$ in (1.1) gives

$$
K_0=\{0\},\qquad K_1=\{(0,0,c):c\in F\},\qquad
|K_0|=1,\quad |K_1|=3.                                         \tag{2.4}
$$

For $B_0$ the two tests impose $w_1=w_2=w_3=0$. For $B_1$ the first imposes $w_1=w_2=0$, and these conditions suffice for every $v$, leaving $w_3$ free.

## 3. Involutions and commuting pairs

An element outside $P_i$ has square

$$
(v,w,z;1)^2=(2v,0,-B_i(v,w);0).                                 \tag{3.1}
$$

This is the identity exactly when $v=0$. Thus the complete set of involutions is

$$
T_i=\{t_i(w,z)=(0,w,z;1):w\in W,\ z\in Z\},\qquad |T_i|=3^5.    \tag{3.2}
$$

Every other outside element has square a nonidentity element of $P_i$, hence has order $6$. In particular every element of $S_i$ has sixth power $1$, and the orders and their multiplicities are

$$
\begin{array}{c|cccc}
\text{order}&1&2&3&6\\ \hline
\text{multiplicity}&1&3^5&3^7-1&(3^2-1)3^5.
\end{array}                                                     \tag{3.3}
$$

These assertions also show directly that all integer power maps depend only on their exponent modulo $6$.

For $x=(v,u,s;0)\in P_i$ and $t=t_i(w,z)$, the two products are

$$
\begin{aligned}
xt&=(v,u+w,s+z+B_i(v,w);1),\\
tx&=(v,w-u,z-s;1).
\end{aligned}
$$

Equality requires $2u=0$ and $2s=-B_i(v,w)$. In characteristic $3$ these are $u=0$ and $s=B_i(v,w)$. Consequently the centralizer inside $P_i$ is exactly

$$
C_i(t_i(w,z)):=C_{P_i}(t_i(w,z))
=\{(v,0,B_i(v,w);0):v\in V\}.                                  \tag{3.4}
$$

This is an abelian subgroup of order $3^2$: multiplication on the displayed graph is addition in $V$. It is independent of $z$.

Define the following set of nonidentity elements of $P_i$:

$$
A_i=\{(v,0,s;0):v\in V\setminus\{0\},\ s\in Z\},\qquad
a:=|A_i|=(3^2-1)3^2.                                            \tag{3.5}
$$

Each element $(v,0,s;0)\in A_i$ commutes with exactly $3^3$ involutions. Indeed (3.4) asks for $B_i(v,w)=s$, with $3$ choices for $w$ by §2, and then permits all $3^2$ choices for $z$. No other nonidentity element of $P_i$ commutes with an involution: a nonzero $u$ is forbidden by (3.4), and $v=0$ in (3.4) forces $s=0$. Thus $A_i$ is exactly the union of the nonidentity elements of the subgroups (3.4).

Every outside element $x$ has the unique decomposition

$$
x=bt,\qquad b=x^4\in P_i,\qquad t=x^3\in T_i,\qquad bt=tb.       \tag{3.6}
$$

To prove this, $x^6=1$ gives $x^4x^3=x$, and the two powers commute. The quotient $S_i/P_i=C_2$ puts $x^4$ inside and $x^3$ outside; the latter has square $1$, so is an involution. Conversely, if $t\in T_i$ and $b\in C_i(t)$, then $bt$ is outside and

$$
(bt)^3=t,\qquad (bt)^4=b,\qquad (bt)^2=b^2.                     \tag{3.7}
$$

These equalities prove both existence and uniqueness in (3.6). The case $b=1$ is the involution itself, and $b\ne1$ gives order $6$. In particular, for each fixed $t$ there are $3^2-1$ elements of order $6$ with cube $t$.

## 4. All integer-exponent functional graphs

For positive $c$ and nonnegative $d$, let $\mathcal C(c,d)$ be the directed graph consisting of a directed $c$-cycle and exactly $d$ additional vertices at each cycle vertex, each additional vertex pointing directly to that vertex. There are no further edges. For $c=1$ the cycle is a loop. Write $n\mathcal C(c,d)$ for the disjoint union of $n$ copies, and $\sqcup$ for disjoint union.

We claim the following complete component descriptions for either $S_i$, with $a$ as in (3.5):

$$
\begin{array}{c|l}
m\pmod6&\Gamma_m(S_i)\\ \hline
0&\mathcal C(1,2\cdot3^7-1)\\
1&(2\cdot3^7)\mathcal C(1,0)\\
2&\mathcal C(1,3^5)\ \sqcup\ \dfrac a2\mathcal C(2,3^3)
  \ \sqcup\ \dfrac{3^7-1-a}{2}\mathcal C(2,0)\\
3&\mathcal C(1,3^7-1)\ \sqcup\ 3^5\mathcal C(1,3^2-1)\\
4&\mathcal C(1,3^5)\ \sqcup\ a\mathcal C(1,3^3)
  \ \sqcup\ (3^7-1-a)\mathcal C(1,0)\\
5&(1+3^5)\mathcal C(1,0)\ \sqcup
  \dfrac{2\cdot3^7-1-3^5}{2}\mathcal C(2,0).
\end{array}                                                     \tag{4.1}
$$

For residue $0$, every vertex maps to the identity and the identity has its loop. For residue $1$, every vertex has a loop and there are no other edges. For residue $5$, the map is inversion. Its fixed points are the identity and precisely the involutions. All remaining vertices occur in inverse pairs, which give the directed $2$-cycles in (4.1).

For residue $3$, every element of $P_i$ maps to $1$. Each involution is fixed. By (3.6)–(3.7), the other elements outside $P_i$ map to their involution $t$, with exactly $3^2-1$ such vertices for each $t$. No element maps to a nonidentity element of $P_i$ or to an element of order $6$. These are exactly the two families of loop-stars in (4.1), with no longer branches.

It remains to prove both even-residue rows, including the attachment of every outside vertex. For $m=2$ or $4$, the restriction of $x\mapsto x^m$ to $P_i$ is a permutation: it is inversion for $m=2$ and the identity for $m=4$, since $x^3=1$ in $P_i$. Thus all of $P_i$ is periodic. Every outside vertex maps into $P_i$, so it is not periodic and lies exactly one edge from a periodic vertex. There can be no edge into an outside vertex, since every $m$th power lies in $P_i$.

For a prescribed $y\in P_i$, there is exactly one $b\in P_i$ satisfying $b^m=y$, namely $b=y^2$ for $m=2$ and $b=y$ for $m=4$. By (3.6), the outside preimages of $y$ are in bijection with

$$
\{t\in T_i:b\in C_i(t)\},                                      \tag{4.2}
$$

via $t\mapsto bt$. If $y=1$, then $b=1$ and (4.2) is all of $T_i$, giving $3^5$ leaves at the identity loop. If $y\in A_i$, then $b\in A_i$ and (4.2) has size $3^3$. If $y\notin A_i\cup\{1\}$, it has size zero. Here $A_i$ is invariant under inversion: on its elements (2.2) gives $(v,0,s;0)^{-1}=(-v,0,-s;0)$. Its complement in $P_i\setminus\{1\}$ is invariant as well. Inversion has no fixed point there, since an element of order dividing both $2$ and $3$ is $1$.

For $m=2$, the $a$ active vertices therefore form $a/2$ inverse pairs, each with $3^3$ leaves at both vertices. The remaining $3^7-1-a$ nonidentity vertices form $(3^7-1-a)/2$ inverse pairs without leaves. For $m=4$, those same vertices are individually fixed and have respectively $3^3$ and zero leaves. This proves the two remaining rows. It also justifies the integral multiplicities in (4.1); the halved numbers count free inversion orbits.

All component data in (4.1) are independent of $i$. For any one residue, pair the components of each displayed type between $S_0$ and $S_1$. In each pair, biject the cycle vertices in cyclic order and biject the leaves attached to corresponding vertices. This gives a bijection preserving every directed edge, including every loop. The graph has exactly one outgoing edge at each vertex, so the resulting bijection $f_m$ satisfies

$$
f_m(x^m)=f_m(x)^m\qquad(x\in S_0).
$$

For an arbitrary integer $m$, use the corresponding residue in (4.1). Every element has sixth power $1$, hence $x^m=x^r$ whenever $m\equiv r\pmod6$, for negative integers and zero as well as positive integers. The groups are fixed throughout; only the bijection may depend on the residue. This proves $S_0\sim_5 S_1$ with the full quantifiers of Definition 1.1.

## 5. A joint square-and-cube obstruction

For $t\in T_i$, define a subset of the underlying set of $S_i$ solely by two power operations:

$$
N_i(t)=\{x^2:x\in S_i,\ x^3=t\}.                               \tag{5.1}
$$

Every $x$ with cube $t$ is outside $P_i$, because elements of $P_i$ have cube $1$. Equations (3.6)–(3.7) identify all such $x$ as $bt$ with $b\in C_i(t)$. Squaring permutes $C_i(t)$, whose exponent divides $3$. Consequently

$$
N_i(t)=C_i(t).                                                  \tag{5.2}
$$

By (3.4), these sets are graphs of the maps $v\mapsto B_i(v,w)$ over the same first coordinate. Therefore

$$
\begin{aligned}
N_i(t_i(w,z))=N_i(t_i(w',z'))
&\iff B_i(v,w)=B_i(v,w')\quad(\forall v\in V)\\
&\iff w-w'\in K_i.                                             \tag{5.3}
\end{aligned}
$$

In the first equivalence, equality of sets forces equality at each $v$, because each graph contains exactly one point with that first coordinate. Thus each equivalence class of involutions under equality of the sets (5.1) has size $|K_i||Z|$. Equation (2.4) gives

$$
\begin{array}{c|cc}
 &S_0&S_1\\ \hline
\text{size of every equal-}N\text{ class in }T_i&3^2=9&3^3=27.
\end{array}                                                     \tag{5.4}
$$

Suppose, for contradiction, that $f:S_0\to S_1$ is a bijection preserving squares and cubes. The identity is the unique element satisfying both $x^2=x$ and $x^3=x$: already $x^2=x$ in a group forces $x=1$. Preservation of squares gives $f(1)^2=f(1)$, hence $f(1)=1$. Injectivity and preservation of squares imply

$$
t\ne1,\ t^2=1\quad\iff\quad f(t)\ne1,\ f(t)^2=1.
$$

By surjectivity this makes $f$ a bijection $T_0\to T_1$. Preservation of squares and cubes also gives

$$
f[N_0(t)]=N_1(f(t)).                                           \tag{5.5}
$$

Indeed $x^3=t$ implies $f(x)^3=f(t)$ and $f(x^2)=f(x)^2$, giving one inclusion. Conversely, for $y^3=f(t)$ choose $x$ with $f(x)=y$. Then $f(x^3)=f(t)$, so injectivity gives $x^3=t$, and $y^2=f(x^2)$ gives the other inclusion.

Since images under a bijection preserve and reflect equality of subsets, (5.5) makes $f:T_0\to T_1$ an isomorphism of the equality-of-$N$ equivalence relations. It must biject each equivalence class onto the class of its image. This contradicts (5.4). Thus no bijection preserves both squares and cubes, and in particular none preserves all integer powers simultaneously. This proves (1.6) and Theorem 1.3. ∎

## 6. Mathematical source correspondences

The prime-exponent phenomenon in [F, Lemma 3.1(i), §6][F] and [L, §5, p.14][L] identifies same-order prime-exponent examples under a single compatible power bijection. The repository's [PowerInvariantRefinement construction](../../../D5/S3/FiniteGroups/PowerInvariantRefinement.lean), its [mathematical exposition](../../../Blueprint/D5/S3/FiniteGroups/PowerInvariantRefinement.md), [Scribe source](../../../Blueprint/D5/S3/FiniteGroups/PowerInvariantRefinement.scribe.cs), [literature note](../../../Library/FiniteGroups/fernandes2026invariants.md), and [problem statement](../../../Problems/fernandes-2026-intermediate-group-invariant.md) use this phenomenon on $F^5$ to answer the first alternative of Problem 6.2. Their three alternating-form groups have the same scalar integer-power operations. They therefore supply simultaneous-power-equivalent pairs, whereas (1.6) requires simultaneous-power inequivalence. None of those pairs is used as a witness in Theorem 1.3.

The groups in (1.2) are classical bilinear groups, with the exact correspondences (1.4)–(1.5). Wilson's main subgroup-profile theorem [W, Theorem 1.1][W] has different hypotheses and a different conclusion; it is not an input to (1.6). Likewise the nilpotent-group conclusion $\sim_5=\sim_2$ in [F, Theorem 1.8][F] concerns the nilpotent class. The proof above establishes its witnesses and their power maps directly from (1.1)–(1.3).

The cycle-with-attached-trees description is standard for functional graphs; see Qureshi–Reis [QR, §2.1][QR]. Their further formulas for flower groups require the common-pistil condition in [QR, Definition 3.1][QR], and those formulas are not premises of (4.1). Larson [L] uses undirected multigraphs for the maps considered there; the directed, loop-retaining convention here is exactly [F, Definition 1.4][F].

Power quandles in Szymik–Vik [SV, Definition 1.1, Theorems 3.1–3.2][SV] retain conjugation together with all powers. Their center and central-quotient conclusions use preservation of conjugation. By contrast (5.1)–(5.5) use only squares and cubes. The graph reconstruction statements in Mirzargar–Sorgun–Nadjafi-Arani [MSN, §3][MSN] concern cyclic-subgroup and unlabelled power-type graph data, rather than the separately conjugated functional maps in Definition 1.1. No reconstruction statement from that paper is needed here. Panja–Singh [PS] concerns power-map images, roots, and related group families; no estimate from that survey is a premise of (1.6).

For the orthogonal radicals in Hao–Yang [HY, Theorem 6.1][HY], $q$ is odd, $a,M\ge1$, and $J,J'$ are invertible symmetric $M\times M$ matrices. The logarithmic coordinates in their proof satisfy $u_J(X,Z)^j=u_J(jX,jZ)$ for every integer $j$. Thus the coordinate bijection $u_J(X,Z)\mapsto u_{J'}(X,Z)$ preserves all element powers simultaneously. Their further nonisomorphism conclusion for differing Witt types, with $a\ge3$ and positive even $M$, does not change this power equivalence. That result is therefore different from (1.6); group nonisomorphism is not the obstruction proved in §5.

[F]: https://arxiv.org/abs/2609.20516v1 "Arthur Fernandes, Claudio Qureshi, Lucas Reis and Sávio Ribas, On a class of combinatorial group invariants, arXiv:2609.20516v1"
[W]: https://arxiv.org/abs/1612.01444v1 "James B. Wilson, The threshold for subgroup profiles to agree is Ω(log n), arXiv:1612.01444v1"
[L]: https://math.colgate.edu/~integers/t58/t58.pdf "Matt Larson, Power maps in finite groups, Integers 19, A58"
[QR]: https://arxiv.org/abs/2107.00584v2 "Claudio Qureshi and Lucas Reis, On the functional graph of the power map over finite groups, arXiv:2107.00584v2"
[SV]: https://arxiv.org/abs/2111.08998v1 "Markus Szymik and Torstein Vik, Groups, conjugation and powers, arXiv:2111.08998v1"
[MSN]: https://arxiv.org/abs/2511.12374v1 "M. Mirzargar, S. Sorgun and M. J. Nadjafi-Arani, Cyclic Subgroup Lattices as Universal Sources of Power-Type Graphs, arXiv:2511.12374v1"
[PS]: https://arxiv.org/abs/2411.07017v1 "Saikat Panja and Anupam Singh, A survey on power maps in groups, arXiv:2411.07017v1"
[HY]: https://arxiv.org/abs/2610.29976v1 "Qingchun Hao and Yang Yang, Characters and Polynomiality for Maximal Parabolic Unipotent Radicals in Finite Classical Groups, arXiv:2610.29976v1"

## 追加锚（本行以下为增补区）
