# Repeated-block caterpillar principal-specialization classification

## 1. Graphs, color conventions and polynomial notation

**Definition 1.1 (Caterpillars and admissibility).** For a positive integer vector
$a=(a_0,\ldots,a_{\ell-1})$, let $C_a$ consist of the path
$v_0\cdots v_{\ell-1}$ and $a_i-1$ distinct pendant vertices adjacent only to
$v_i$, for each $i$. Thus $|V(C_a)|=\sum_i a_i$; a part equal to one has no
pendant vertices. The admissible vectors are the singleton $(1)$ and the
nonempty positive vectors whose first and last parts are at least two. This
is the domain of [P1, Definition 2.1], with spine indices decreased by one.

For integers $m\geq0$ and $j\geq1$, write $j^m$ for a word of $m$ copies of
$j$, including the empty word $j^0$, and put

$$
G_{m,j}=C_{(5,j^m,4,3)},\qquad H_{m,j}=C_{(4,j^m,5,3)}.
$$

Both vectors are admissible, have $m+3$ spine vertices and have
$5+mj+4+3=12+mj$ actual vertices. In particular, neither $m=0$ nor $j=1$
is excluded.

**Definition 1.2 (Ordinary principal specialization).** For a finite graph $T$
and an integer $k\geq1$, define, with $q$ an indeterminate,

$$
P_k(T)=\sum_{\substack{c:V(T)\to\{0,\ldots,k-1\}\\
                     c(u)\ne c(v)\text{ for every }uv\in E(T)}}
                     q^{\sum_{v\in V(T)}c(v)}\in\mathbb Z[q].
$$

The sum includes every proper map, with no surjectivity condition and no
specified root. Its exponent includes every actual vertex. It is the
ordinary specialization of [P1, Definition 2.9 and equation (2.1)].
The same sum in $\mathbb C[q]$ is its coefficientwise image under the
injective inclusion $\iota:\mathbb Z[q]\hookrightarrow\mathbb C[q]$.
For the one-based color convention of [P2, equation (1)],

$$
\chi_T^{\mathbf1}(q,k)=q^{|V(T)|}P_k(T).
$$

Indeed, replacing $c(v)$ by $c(v)+1$ adds $|V(T)|$ to every exponent.
Consequently, comparisons of the present equal-order pairs are unchanged
by that shift. The polynomial in [P2, Theorem 1] instead has an additional
variable $x$, coefficients in $\mathbb Q(q)$ and specializes at $x=[k]_q$;
its existence does not identify two evaluations at a fixed $k$.

The rooted invariant in [P3, Theorem 17] is
$X_0(T_*;q,q,1,1)$, where the root is required to receive color $0$.
It uses four color variables with two repeated values. It is different
from the unrooted sum $P_3(T)$ at $(1,q,q^2)$, and also from $P_4(T)$ at
$(1,q,q^2,q^3)$. For [P1, Definition 3.1], the finite $t$-refined specialization gives
each coloring the additional factor $t^{|\operatorname{im}c|}$; the
ordinary polynomial $P_k$ is its value at $t=1$. No rooted, four-color,
$t$-refined or stable
specialization is implicit in the notation $P_k$.

**Definition 1.3 (Block weights and coefficient polynomials).** For $s\geq1$
and $0\leq c<k$, put

$$
B_s^{(k)}(c)=q^c\left(\sum_{\substack{0\leq d<k\\d\ne c}}q^d\right)^{s-1}.
$$

For three colors abbreviate $B_s=B_s^{(3)}$. For fixed $j\geq1$ set

$$
\begin{aligned}
w_0&=q^{j-1}(1+q)^{j-1},&
w_1&=q(1+q^2)^{j-1},&
w_2&=q^2(1+q)^{j-1},\\
e_2&=w_0w_1+w_0w_2+w_1w_2,&
e_3&=w_0w_1w_2,\\
Q&=q^5(1+q)^3(1+q^2)^3(q-1)^2(q^3-1).
\end{aligned}
$$

Thus $w_c=B_j(c)$. For every integer $n<0$ set $H_n=0$; for $n\geq0$ set

$$
H_n=\sum_{\substack{u,v\geq0\\2u+3v=n}}
       \binom{u+v}{u}e_2^u(2e_3)^v\in\mathbb Z[q].
$$

All subscripts on $H_n$ refer to these polynomials for the fixed $j$.
The sum is finite; in particular $H_0=1$ and $H_1=0$.

## 2. Exact difference for every repetition length

**Theorem 2.1 (Exact repeated-block difference).** For every pair of integers
$m\geq0$ and $j\geq1$,

$$
\boxed{\quad
P_3(G_{m,j})-P_3(H_{m,j})
 =Q(1+q)^{j-1}(q^{j-1}-q^2)H_{m-1}.
\quad}
$$

The identity is in $\mathbb Z[q]$ and hence also in $\mathbb C[q]$ under
$\iota$.

Proof. Use the full actual-coloring factorization [R1,
`coloringEquiv`, `assemble_weight`, `coloring_factorization`,
`ps_spine_sum`]. In the present notation it gives, for every positive vector,

$$
P_k(C_a)=\sum_{\substack{c_0,\ldots,c_{\ell-1}\in\{0,\ldots,k-1\}\\
                         c_i\ne c_{i+1}\ (0\leq i<\ell-1)}}
                         \prod_{i=0}^{\ell-1}B_{a_i}^{(k)}(c_i).
\tag{2.1}
$$

The factorization includes the empty leaf sets when $a_i=1$: the spine
color and the independent colors on its $a_i-1$ leaves contribute precisely
the displayed block weight. We use this cited identity, including its
private coloring-bijection and weight identities, as an intermediate input.

For three colors, let all vectors below be columns, and put

$$
K=\begin{pmatrix}0&1&1\\1&0&1\\1&1&0\end{pmatrix},\qquad
D=\operatorname{diag}(w_0,w_1,w_2),\qquad M=DK,
$$

$$
a=B_5,\qquad b=B_4,\qquad c=B_3,\qquad t=Kc.
$$

Let $\operatorname{diag}(b)$ mean the diagonal matrix with diagonal $b$.
Equation (2.1) gives, for every $m\geq0$,

$$
\begin{aligned}
P_3(G_{m,j})&=a^{\mathsf T}KM^m\operatorname{diag}(b)Kc,\\
P_3(H_{m,j})&=b^{\mathsf T}KM^m\operatorname{diag}(a)Kc.
\end{aligned}
\tag{2.2}
$$

Each $K$ enforces inequality on a spine edge, each $D$ contributes the
weight of one repeated block, and the remaining diagonal matrix contributes
the penultimate block. Thus the $m=0$ expression has exactly two spine
edges. This is the standard weighted-path transfer-matrix method
[P4, §V.6], applied inside the difference proof.

Write $\Delta_m$ for the difference in the theorem. We calculate its
three initial values. Put

$$
z=1+q,\qquad y=1+q^2,\qquad
h=q^2z^2,\qquad d=qy^2.
$$

The explicit block weights are

$$
\begin{aligned}
a&=(q^4z^4,\ qy^4,\ q^2z^4)^{\mathsf T},\\
b&=(q^3z^3,\ qy^3,\ q^2z^3)^{\mathsf T},\\
c&=(h,d,h)^{\mathsf T},\qquad
 t=(h+d,2h,h+d)^{\mathsf T}.
\end{aligned}
\tag{2.3}
$$

For $i<s$ define $p_{is}=a_i b_s-b_i a_s$. Two of these minors agree:

$$
\begin{aligned}
p_{01}&=q^4z^3y^3(qz-y)
       =q^4z^3y^3(q-1),\\
p_{12}&=q^3z^3y^3(y-z)
       =q^4z^3y^3(q-1).
\end{aligned}
$$

Call their common value $A$. Pairing the terms with spine colors $(i,s)$
and $(s,i)$ in (2.2) for $m=0$ gives

$$
\Delta_0=\sum_{i<s}p_{is}(t_s-t_i)
 =A(h-d)+p_{02}\,0+A(d-h)=0.
\tag{2.4}
$$

For $m=1$, first fix the middle color $s$. Its coefficient $C_s$ in
$\Delta_1=\sum_s w_sC_s$ is

$$
C_s=\left(\sum_{i\ne s}a_i\right)
     \left(\sum_{u\ne s}b_ut_u\right)
    -\left(\sum_{i\ne s}b_i\right)
     \left(\sum_{u\ne s}a_ut_u\right).
$$

For the two allowed indices $i<u$, the right side is
$p_{iu}(t_u-t_i)$. Inserting (2.3) therefore gives

$$
C_0=A(d-h),\qquad C_1=0,\qquad C_2=-A(d-h).
$$

Furthermore,

$$
\begin{aligned}
d-h&=q\bigl((1+q^2)^2-q(1+q)^2\bigr)
     =q(q-1)(q^3-1),\\
A(d-h)&=q^5z^3y^3(q-1)^2(q^3-1)=Q.
\end{aligned}
$$

Consequently,

$$
\Delta_1=Q(w_0-w_2).
\tag{2.5}
$$

The remaining initial value is the cited arbitrary-middle-weight
identity [R1, `diagonal_identity`]. If $F(U_0,\ldots,U_4)$ denotes the
sum of $\prod_{i=0}^4 U_i(c_i)$ over all five consecutive unequal colors
in $\{0,1,2\}$, that identity states

$$
F(B_5,w,w,B_4,B_3)=F(B_4,w,w,B_5,B_3)
\quad\text{for every }w\in\mathbb Z[q]^3.
$$

Apply it to the present $w$ in (2.1). It gives

$$
\Delta_2=0.
\tag{2.6}
$$

In particular this input is stronger than its specialization to a fixed
$j$; no new two-middle-block identity is needed.

The matrix $M$ has entries $M_{is}=w_i$ for $i\ne s$ and zero diagonal.
Direct multiplication gives

$$
M^3=e_2M+2e_3I.
\tag{2.7}
$$

For completeness, if $i,s,u$ are the three distinct indices, the
$(i,s)$ entry of $M^3$ is
$w_i^2(w_s+w_u)+w_iw_sw_u=e_2w_i$, while its $(i,i)$ entry is
$2w_0w_1w_2=2e_3$. These are all the entries, proving (2.7) over
$\mathbb Z[q]$ without any invertibility assumption on the weights.
Multiplying (2.7) by $M^m$ and using both linear expressions (2.2) yields

$$
\Delta_{m+3}=e_2\Delta_{m+1}+2e_3\Delta_m
\qquad(m\geq0).
\tag{2.8}
$$

Introduce a second indeterminate $x$ and work in $\mathbb Z[q][[x]]$.
Equations (2.4)--(2.8) imply

$$
\left(1-e_2x^2-2e_3x^3\right)\sum_{m\geq0}\Delta_mx^m
       =Q(w_0-w_2)x.
\tag{2.9}
$$

Indeed, the coefficients of $x^0,x^1,x^2$ on the left are respectively
$0,Q(w_0-w_2),0$, and every higher coefficient is zero by (2.8).
The factor in parentheses has constant coefficient one, so the formal
geometric-series identity and the binomial theorem give

$$
\begin{aligned}
\frac1{1-e_2x^2-2e_3x^3}
 &=\sum_{s\geq0}(e_2x^2+2e_3x^3)^s\\
 &=\sum_{u,v\geq0}\binom{u+v}{u}
                     e_2^u(2e_3)^v x^{2u+3v}
  =\sum_{n\geq0}H_nx^n.
\end{aligned}
\tag{2.10}
$$

These standard formal-series operations [P4, §I.2] require no analytic
convergence: only finitely many summands contribute to each coefficient.
Taking coefficients in (2.9)--(2.10) gives
$\Delta_m=Q(w_0-w_2)H_{m-1}$, including $m=0$ by $H_{-1}=0$.
Finally
$w_0-w_2=(1+q)^{j-1}(q^{j-1}-q^2)$, which proves the formula. Applying
$\iota$ proves its complex-coefficient version. ∎

## 3. The converse and all zero cases

**Theorem 3.1 (Complete three-color classification in the repeated-block family).**
For every $m\geq0$ and $j\geq1$,

$$
P_3(G_{m,j})=P_3(H_{m,j})
\quad\Longleftrightarrow\quad
m\in\{0,2\}\ \text{or}\ j=3.
$$

This equivalence holds both in $\mathbb Z[q]$ and for the corresponding
polynomials in $\mathbb C[q]$.

Proof. Each $w_i$ is a nonzero polynomial with nonnegative integer
coefficients, even when $j=1$, where $w=(1,q,q^2)$. Hence $e_2$ and $e_3$
are also nonzero and have nonnegative coefficients. Every summand defining
$H_n$ has nonnegative coefficients. If $2u+3v=n$ has a nonnegative integer
solution, its corresponding summand is nonzero: the binomial coefficient
is positive and $\mathbb Z[q]$ is an integral domain. It cannot cancel
against the other summands. Thus

$$
H_n\ne0\quad\Longleftrightarrow\quad
n=2u+3v\text{ for some integers }u,v\geq0\qquad(n\geq0).
$$

Here $0=2\cdot0+3\cdot0$ is included. Every nonnegative even $n$ is
$2(n/2)$; every odd $n\geq3$ is $2((n-3)/2)+3$. The only missing
nonnegative integer is $1$. Together with the negative-index definition,
this proves

$$
H_{m-1}=0\quad\Longleftrightarrow\quad m=0\text{ or }m=2
\qquad(m\geq0).
\tag{3.1}
$$

Each displayed factor of $Q$ is a nonzero polynomial, and
$(1+q)^{j-1}$ is nonzero. Also
$q^{j-1}-q^2=0$ exactly when $j-1=2$, since distinct nonnegative powers
of the indeterminate $q$ have distinct coefficients. Thus $j=3$ is the
only zero of this last factor in the integer parameter domain; for $j=1$
it is $1-q^2\ne0$. There are no zero divisors in $\mathbb Z[q]$.
Theorem 2.1 and (3.1) now give both implications, with no further
cancellation possibility.

For the coefficient extension, use the bridge [R2, `ordinary_eq_map`,
`ordinary_eq_iff`]: its map is exactly $\iota$ of Definition 1.2.
Coefficientwise injectivity means
$\iota(f)=\iota(g)$ if and only if $f=g$, so it transfers the equivalence
and its inequality complement. ∎

## 4. Two colors and the simultaneous classification

**Theorem 4.1 (Exact two-color formulas and simultaneous condition).**
For every $r\geq0$ and $j\geq1$,

$$
\begin{aligned}
P_2(G_{2r,j})&=q^{rj+5}+q^{rj+7},&
P_2(H_{2r,j})&=2q^{rj+6},\\
P_2(G_{2r+1,j})&=q^{(r+1)j+3}+q^{rj+9},&
P_2(H_{2r+1,j})&=q^{(r+1)j+3}+q^{rj+9}.
\end{aligned}
$$

All sums retain multiplicity when exponents coincide. Consequently, for
every $m\geq0$ and $j\geq1$,

$$
P_2(G_{m,j})\ne P_2(H_{m,j})
\quad\Longleftrightarrow\quad m\text{ is even},
$$

and

$$
\begin{aligned}
&P_3(G_{m,j})=P_3(H_{m,j})\ \text{and}\
 P_2(G_{m,j})\ne P_2(H_{m,j})\\
&\hspace{15mm}\Longleftrightarrow\quad
m\text{ is even and }\bigl(m\in\{0,2\}\text{ or }j=3\bigr).
\end{aligned}
$$

The formulas and both equivalences also hold after coefficient inclusion
in $\mathbb C[q]$.

Proof. Use the connected-bipartite coloring fact underlying
[P1, Proposition 3.16(3) and Corollary 3.17]: a connected bipartite graph with parts of sizes
$s,t$ has precisely two proper maps into $\{0,1\}$ and therefore has
$P_2=q^s+q^t$. To see why it applies here, every $C_a$ is a tree; after
choosing the color of $v_0$, adjacency forces alternation along each
unique path. Both choices extend to a coloring, and the two parts are
the vertices at even and odd distance from $v_0$.

Let $U$ be the part containing $v_0$ and let $V$ be the other part.
For a vector of length $\ell$, the even-index spine vertices belong to
$U$, and all leaves at odd-index spine vertices also belong to $U$.
Thus the actual vertex counts, with zero-based indices, are

$$
|U|=\left\lceil\frac\ell2\right\rceil+
                  \sum_{i\text{ odd}}(a_i-1),\qquad
|V|=\left\lfloor\frac\ell2\right\rfloor+
                  \sum_{i\text{ even}}(a_i-1).
\tag{4.1}
$$

For $m=2r$, the repeated positions $1,\ldots,2r$ contain $r$ of each
parity. The next two positions are odd and even. For $G_{2r,j}$,
formula (4.1) consequently gives

$$
|U|=(r+2)+r(j-1)+3=rj+5,\qquad
|V|=(r+1)+4+r(j-1)+2=rj+7.
$$

For $H_{2r,j}$, the leaf contributions $3$ and $4$ at the swapped
blocks exchange roles, giving

$$
|U|=(r+2)+r(j-1)+4=rj+6,\qquad
|V|=(r+1)+3+r(j-1)+2=rj+6.
$$

For $m=2r+1$, there are $r+1$ odd repeated positions and $r$ even
repeated positions. The two final positions are even and odd, and the
spine has $r+2$ vertices of each parity. In either graph,

$$
\begin{aligned}
|U|&=(r+2)+(r+1)(j-1)+2=(r+1)j+3,\\
|V|&=(r+2)+4+r(j-1)+3=rj+9.
\end{aligned}
$$

The second line uses $4+3$ pendant vertices at the first and penultimate
blocks in $G$, or $3+4$ in $H$. These calculations prove all four
formulas, including $r=0$ and leafless repeated parts $j=1$.
If $j=6$ in the odd case, the two exponents coincide and both
polynomials are $2q^{6r+9}$, as the formulas prescribe.

In the even case the coefficient at degree $rj+5$ is one for $G$ and
zero for $H$; in the odd case the displayed polynomials agree.
This proves the parity equivalence. Intersecting it with Theorem 3.1
proves the simultaneous condition. Injectivity of $\iota$, as used in
the proof of Theorem 3.1, preserves all these statements. ∎

## 5. An unbounded family outside the listed isomorphism closure

**Definition 5.1 (The listed unordered pair classes).** Let $\mathcal L$ be
the set of unordered pairs of graph-isomorphism classes represented by

$$
\{C_{(5,4,3)},C_{(4,5,3)}\}
\quad\text{and}\quad
\{C_{(5,h,h,4,3)},C_{(4,h,h,5,3)}\}\qquad(h\geq1).
$$

Graph isomorphisms allow arbitrary relabeling; unordered pairs allow
exchange of their members. Reversal of a composition is already included
because it induces a graph isomorphism. This is exactly the listed
closure of [P1, Remark 3.11] and [R2, `pairIso`, `listed`]. The positive
parameter $h$ has no upper bound. The all-$h$ specialization assertion
for its five-part members is given by [R1, `result`], and the failure
of exhaustiveness is given by [R2, `result`], using the pair
$(2,2,2,2,2,1,4,3)$ and $(2,2,3,2,3,4,2)$. Neither assertion is a new
conclusion of the following theorem.

**Theorem 5.2 (Infinitely many unlisted pair classes with canonical spines).**
For every integer $r\geq2$, put $A_r=G_{2r,3}$ and $B_r=H_{2r,3}$.
These are admissible caterpillars with $12+6r$ vertices satisfying

$$
P_3(A_r)=P_3(B_r),\qquad
P_2(A_r)=q^{3r+5}+q^{3r+7}\ne2q^{3r+6}=P_2(B_r).
$$

Each unordered pair $\{[A_r],[B_r]\}$ lies outside $\mathcal L$.
Its two graph classes are distinct, and different integers $r\geq2$
give different unordered pair classes. In particular there are
infinitely many such pairs. The number of repeated blocks is the even
integer $m=2r$; the total spine length is the odd integer $2r+3$.

Proof. The specialization statements follow from Theorems 3.1 and 4.1
at $j=3$. Admissibility and the vertex count follow from Definition 1.1.
Unequal two-color polynomials imply $A_r\not\cong B_r$, since composing
colorings with a graph isomorphism preserves the sum of all vertex colors.

For exclusion from $\mathcal L$, use the nonleaf mechanism of [R2,
`leaf_neighbor`, `nonleaf_root`, `iso_two_neighbors`]. In any caterpillar
a pendant vertex has just one neighbor, so every vertex with at least
two neighbors lies on the spine. Conversely, for every vector at issue
here, all spine vertices have at least two neighbors: an internal one
has its two path neighbors, and an endpoint has its path neighbor and
at least one pendant neighbor. This remains true for every listed
$h=1$. Thus the vertices of degree at least two are exactly the spine
vertices. The graph they induce is the spine path and is intrinsic to
the graph, independently of names or the chosen description.

An isomorphism preserves degrees and the induced nonleaf path. Each of
$A_r,B_r$ has exactly $2r+3\geq7$ nonleaf vertices. A member of the base
listed pair has three, and a member with parameter $h$ has five for
every $h\geq1$. Hence neither $A_r$ nor $B_r$ can be isomorphic to any
listed member. Either matching of an unordered pair with a pair in
$\mathcal L$ would require such an isomorphism, so all pair exchanges,
reversals and arbitrary relabelings are excluded at once. This argument
uses the canonical nonleaf spine, not a bound on graph order: the
listed orders $12+2h$ are unbounded and even coincide with $12+6r$
when $h=3r$.

Finally, if $\{[A_r],[B_r]\}=\{[A_s],[B_s]\}$, then some member at
$r$ is isomorphic to a member at $s$. Their intrinsic nonleaf paths
have the same number of vertices, so $2r+3=2s+3$ and $r=s$.
Equivalently their actual vertex counts $12+6r$ and $12+6s$ already
force this equality. Since there are infinitely many integers
$r\geq2$, the pair classes are actually infinite. ∎

## 6. A precise middle-word comparison problem

**Definition 6.1 (Nonconstant palindromic middle words).** For a finite word
$b=(b_1,\ldots,b_s)$ of positive integers, define

$$
T_b=C_{(5,b_1,\ldots,b_s,4,3)},\qquad
U_b=C_{(4,b_1,\ldots,b_s,5,3)}.
$$

Call $b$ palindromic when $b_i=b_{s+1-i}$ for every $i$, and nonconstant
when at least two of its entries differ. The comparison problem is to
determine exactly which nonconstant palindromic words satisfy

$$
P_3(T_b)=P_3(U_b)\quad\text{and}\quad P_2(T_b)\ne P_2(U_b).
$$

For such a word the matrix product in (2.2) becomes
$(D_{b_1}K)\cdots(D_{b_s}K)$, where
$D_t=\operatorname{diag}(B_t(0),B_t(1),B_t(2))$.
The recurrence proof in Theorem 2.1 treats the equality
$D_{b_1}=\cdots=D_{b_s}=D_j$, that is, the constant-word case.
Theorems 2.1--5.2 classify the constant words with the fixed
outside blocks $5,4,3$; no criterion for these nonconstant palindromic
products is asserted here.

## 7. Mathematical references

[P1] Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana,
Jianping Pan and Mary Claire Simone, *Principal specializations of the
t-chromatic symmetric function*,
[arXiv:2610.31785v1](https://arxiv.org/html/2610.31785v1),
Definitions 2.1, 2.4, 2.7, 2.9, equation (2.1), Remark 3.11 and
Definition 3.1, Proposition 3.16(3) and Corollary 3.17. The graph and ordinary coloring conventions, the listed
pairs and the bipartition interpretation are cited inputs; the
all-$m,j$ difference, its converse and the family of Theorem 5.2 are the
additional deductions proved above. Statements about the $t$-refined
invariant in that source retain their own stronger hypotheses and data.

[P2] Esme Bajo, Matthias Beck and Andrés R. Vindas-Meléndez,
*q-chromatic polynomials*,
[arXiv:2403.19573v3](https://arxiv.org/html/2403.19573v3),
equation (1) and Theorems 1 and 6. Equation (1) uses one-based colors;
Theorem 1 is the $\mathbb Q(q)[x]$ interpolation at $[k]_q$, and
Theorem 6 concerns the positive-color infinite specialization. These
are different contracts from equality at the fixed color bound three.

[P3] Nicholas A. Loehr and Gregory S. Warrington, *A rooted variant of
Stanley's chromatic symmetric function*,
[arXiv:2206.05392v3](https://arxiv.org/html/2206.05392v3),
§2.1, Theorem 17 and Conjecture 21. Theorem 17 concerns rooted trees
and $X_0(T_*;q,q,1,1)$; Conjecture 21 concerns unrooted trees with at
most $N+1$ vertices and $N+1$ distinct principal-specialization
variables. The pairs in Theorem 5.2 have at least twenty-four vertices
and are compared at three colors, so they do not refute that
size-dependent conjecture.

[P4] Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*,
§I.2 (admissible constructions and specifications) and §V.6
(transfer matrix models), [author text](https://ac.cs.princeton.edu/home/)
and [§V.6 contents](https://ac.cs.princeton.edu/50applications/).
The formal geometric-series and weighted-path methods are classical
intermediates in the proof of Theorem 2.1.

[R1] *BinghamCaterpillarPs3Family*,
[coloring identities and family result](https://github.com/the-omega-institute/trureturing/blob/9d2eb78abd964ce047726ba72b6b8adf076fe10d/D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family.lean).
The factorization (2.1) and arbitrary-vector identity used in (2.6) are
reused, including the private identities cited in that proof.

[R2] *BinghamCaterpillarUniquenessRefutation*,
[coefficient bridge and nonleaf argument](https://github.com/the-omega-institute/trureturing/blob/9d2eb78abd964ce047726ba72b6b8adf076fe10d/D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation.lean).
The coefficientwise inclusion, nonleaf mechanism and finite
counterexample cited above are inputs. The unbounded repeated-block
classification and the injective sequence of unlisted pair classes are
the deductions of Theorems 2.1--5.2.

## 追加锚（本行以下为增补区）
