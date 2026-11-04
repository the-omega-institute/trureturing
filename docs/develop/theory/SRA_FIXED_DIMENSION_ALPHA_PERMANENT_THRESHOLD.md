# A dimension-only threshold for principal alpha-permanents

## 1. Definitions

**Definition 1.1 (Matrix class and principal alpha-permanents).** Let
$[n]=\{1,\ldots,n\}$, where $n\geq1$ is an integer. A real matrix $A$
is an inverse $M$-matrix if it is entrywise nonnegative and invertible,
and $(A^{-1})_{uv}\leq0$ whenever $u\ne v$. For $U\subseteq[n]$, let
$A_U=A[U,U]$. For a real number $\alpha>0$, put

$$
 p_{\alpha,A}(U)=\operatorname{per}_{\alpha}(A_U)
 =\sum_{\sigma\in\mathfrak S(U)}
   \alpha^{c(\sigma)}\prod_{u\in U}A_{u,\sigma(u)},
 \qquad p_{\alpha,A}(\varnothing)=1.
$$

Here $\mathfrak S(U)$ is the set of permutations of $U$, and $c(\sigma)$
counts all cycles, including fixed points. The empty permutation has zero
cycles, and its weight is one. For any matrix $B$ indexed by a finite set,
$p_{\alpha,B}$ has the same meaning. These are Sra's Definition 1.3 and
equation (3.1) in *A Koteljanskii inequality for permanents*,
[arXiv:2609.39979v1](https://arxiv.org/html/2609.39979v1).

**Definition 1.2 (Log-supermodularity).** A nonnegative function $f$ on
$2^{[n]}$ is log-supermodular if

$$
 f(S\cup T)f(S\cap T)\geq f(S)f(T)
 \qquad(S,T\subseteq[n]).
$$

This is Sra's Definition 1.4. In all four factors of an inequality for
$p_{\alpha,A}$, the matrix $A$ and the real parameter $\alpha$ are fixed.
We write $Ri=R\cup\{i\}$ and $Rij=R\cup\{i,j\}$ when $i,j\notin R$.

## 2. A comparison of overlapping permutation pairs

**Theorem 2.1 (Uniform local bound).** Let $B=(b_{uv})_{u,v\in V}$ be a
matrix on a finite set $V$, with

$$
 b_{uv}\geq0,\qquad b_{uu}=1,\qquad
 b_{uv}b_{vw}\leq b_{uw}\quad(u,v,w\in V).
 \tag{2.1}
$$

For $R\subseteq V$ and distinct $i,j\in V\setminus R$, set $r=|R|$.
For every real $\alpha\geq1$,

$$
\begin{aligned}
 &p_{\alpha,B}(Rij)p_{\alpha,B}(R)
       -p_{\alpha,B}(Ri)p_{\alpha,B}(Rj)\\
 &\hspace{12mm}\geq
 b_{ij}b_{ji}\,\alpha^{2r}
       \bigl(\alpha-((r+1)!)^2\bigr).
\end{aligned}
\tag{2.2}
$$

*Proof.* Use the permutation cycle expansion in Definition 1.1. The
factorization of a permutation's weight over its disjoint cycles is the
one used by Harry Crane in *Some algebraic identities for the
$\alpha$-permanent*, §2.1,
[arXiv:1304.1772v1](https://arxiv.org/html/1304.1772v1).
For a directed cycle $C=(v_1,\ldots,v_\ell)$ put

$$
 w(C)=b_{v_1v_2}\cdots b_{v_{\ell-1}v_\ell}b_{v_\ell v_1}.
$$

A one-cycle at $v$ has weight $b_{vv}=1$. A pair of permutations,
with a total of $k$ cycles and a product $w$ of their matrix entries,
contributes $\alpha^k w$.

Expand the first product on the left of (2.2) as pairs

$$
 \mathcal P_+=\mathfrak S(Rij)\times\mathfrak S(R),
$$

and the second as pairs

$$
 \mathcal P_-=\mathfrak S(Ri)\times\mathfrak S(Rj).
$$

Color the cycles of the first permutation red and those of the second
blue. Distinguish equal cycles of different colors as separate cycle
occurrences. In either family each $v\in R$ appears in one red and one
blue cycle; $i$ appears only in red. The index $j$ appears in red for
$\mathcal P_+$ and in blue for $\mathcal P_-$.

Associate an undirected bipartite multigraph to each pair. Its vertices
are the colored cycle occurrences. For every $v\in R$, an edge labeled
$v$ joins the red and blue cycles containing $v$. Mark the cycle
containing $i$ and the cycle containing $j$; both marks may lie on the
same vertex in $\mathcal P_+$. Call the pair connected between the marks
when the marked vertices lie in the same graph component. All other
pairs are separated between the marks.

For a separated pair, interchange red and blue on the entire component
containing the $j$-mark. Both occurrences of any $v\in R$ belong to the
same graph component, since the edge labeled $v$ joins them. Thus the
interchange leaves exactly one occurrence of $v$ in each color. The
$i$-mark is outside this component and stays red, whereas $j$ changes
color. The recolored cycles consequently give a member of the other
family, with its required index sets. No directed cycle or entry factor
changes, and the total number of cycles is unchanged. The graph and its
components are unchanged apart from their colors, so repeating the
operation recovers the original pair.

This is a weight-preserving bijection between the separated members of
$\mathcal P_+$ and $\mathcal P_-$. If $\mathcal C_+$ and $\mathcal C_-$
denote their respective members connected between the marks, the
following is an exact identity:

$$
\begin{aligned}
 D&:=p_{\alpha,B}(Rij)p_{\alpha,B}(R)
           -p_{\alpha,B}(Ri)p_{\alpha,B}(Rj)\\
  &=\sum_{P\in\mathcal C_+}\alpha^{k(P)}w(P)
       -\sum_{P\in\mathcal C_-}\alpha^{k(P)}w(P).
\end{aligned}
\tag{2.3}
$$

We next bound each summand in the second sum. Iterating (2.1) along
any finite directed walk gives

$$
 \prod_{a=0}^{\ell-1}b_{v_a v_{a+1}}\leq b_{v_0v_\ell}.
 \tag{2.4}
$$

For $\ell=0$ this is $1=b_{v_0v_0}$; for $\ell=1$ it is equality.
For longer walks, multiply the bound for the first $\ell-1$ edges by
the nonnegative last factor and apply (2.1). Repeated vertices and
zero factors are permitted. In particular $0\leq w(C)\leq1$ for every
cycle occurrence.

Fix $P\in\mathcal C_-$. The cycles in its marked component can be
spliced into a single closed directed walk starting at $i$, with each
edge occurrence of each of those cycles used exactly once. To see this,
start with the red cycle containing $i$. If a cycle in the component
has not been inserted, connectedness supplies an uninserted cycle
adjacent to an inserted one. They share the index labeling that graph
edge. At that index insert a complete directed traversal of the new
cycle into the current walk. This keeps a closed directed walk and
adds exactly the new cycle's edge occurrences. Finitely many such
insertions include every cycle of the component. Edge occurrences
retain their multiplicities, even when two cycles have the same edges.

The resulting walk visits $j$. Split it at an occurrence of $j$ into
an $i$-to-$j$ walk and a $j$-to-$i$ walk. Equation (2.4) bounds their
respective weights by $b_{ij}$ and $b_{ji}$. Their product is exactly
the product of all cycle weights in the marked component. Every cycle
outside that component has weight at most one. Therefore

$$
 0\leq w(P)\leq b_{ij}b_{ji}.
 \tag{2.5}
$$

There is also a uniform bound on $k(P)$. The red cycle containing $i$
cannot be a fixed point: a one-cycle at $i$ has no incident graph edge,
because $i\notin R$, and would be isolated from the blue $j$-mark.
The same argument applies to the blue cycle containing $j$. Hence both
permutations in $P$ have a nontrivial cycle. A permutation on $r+1$
indices with a nontrivial cycle has at most $r$ cycles, since a cycle of
length $\ell\geq2$ replaces $\ell$ one-cycles by one. Consequently

$$
 k(P)\leq2r\qquad(P\in\mathcal C_-).
 \tag{2.6}
$$

When $r=0$, the same isolation argument says that $\mathcal C_-$ is
empty. Thus (2.6) applies without an exceptional nonempty family.
There are $((r+1)!)^2$ pairs in $\mathcal P_-$, so
$|\mathcal C_-|\leq((r+1)!)^2$. From $\alpha\geq1$, (2.5), and (2.6),

$$
 \sum_{P\in\mathcal C_-}\alpha^{k(P)}w(P)
 \leq ((r+1)!)^2\alpha^{2r}b_{ij}b_{ji}.
 \tag{2.7}
$$

In $\mathcal P_+$ take the first permutation to be the transposition
$(i\ j)$ together with fixed points on $R$, and the second to be the
identity on $R$. Both marks lie on the transposition cycle, so this
pair belongs to $\mathcal C_+$. Its weight is
$\alpha^{2r+1}b_{ij}b_{ji}$. All other summands in $\mathcal C_+$ are
nonnegative. Keeping this term in (2.3) and using (2.7) proves (2.2).
No division by an entry of $B$ has been used. $\square$

## 3. The fixed-dimension inequality

**Theorem 3.1 (Explicit sufficient threshold).** For every integer
$n\geq1$, let

$$
 \alpha_n=((n-1)!)^2>0.
 \tag{3.1}
$$

For every real entrywise nonnegative invertible $n\times n$ matrix $A$
whose inverse has nonpositive off-diagonal entries, every real
$\alpha\geq\alpha_n$, and all $S,T\subseteq[n]$,

$$
 \operatorname{per}_{\alpha}(A_{S\cup T})
 \operatorname{per}_{\alpha}(A_{S\cap T})
 \geq
 \operatorname{per}_{\alpha}(A_S)
 \operatorname{per}_{\alpha}(A_T).
 \tag{3.2}
$$

*Proof.* First obtain the entry inequalities needed for Theorem 2.1.
Write $M=A^{-1}$. For every $v$, the identity $MA=I$ gives

$$
 1=M_{vv}A_{vv}+\sum_{u\ne v}M_{vu}A_{uv}
       \leq M_{vv}A_{vv}.
$$

Since $A_{vv}\geq0$, this implies $A_{vv}>0$ (and $M_{vv}>0$).

We use the domination principle, credited to Claude Dellacherie,
Servet Martínez, and Jaime San Martín, *Inverse $M$-matrix, a new
characterization*, Definition 3.1 and Theorem 3.2,
[arXiv:2002.09432v1](https://arxiv.org/html/2002.09432v1).
Their theorem says that a nonnegative nonsingular matrix $U$ has
$U^{-1}$ an $M$-matrix if and only if, for nonnegative vectors $x,y$,

$$
 (Ux)_v\leq(Uy)_v\text{ whenever }x_v>0
 \quad\Longrightarrow\quad Ux\leq Uy.
 \tag{3.3}
$$

Here $U=A$ meets exactly those hypotheses: $A\geq0$, $A$ is
nonsingular, $M$ has nonpositive off-diagonal entries, and $M^{-1}=A\geq0$.
The positivity of $M$'s diagonal was also established above.
For indices $v,w$ with $A_{vw}>0$, take
$x=A_{vw}e_v$ and $y=A_{vv}e_w$, where $e_v$ is a coordinate vector.
The only positive coordinate of $x$ is $v$, and
$(Ax)_v=A_{vv}A_{vw}=(Ay)_v$. Applying (3.3), at every index $u$,

$$
 A_{uv}A_{vw}\leq A_{uw}A_{vv}.
 \tag{3.4}
$$

If $A_{vw}=0$, the left side of (3.4) is zero and the same inequality
follows from nonnegativity. Thus (3.4) holds for all $u,v,w$.

Put $d_v=A_{vv}$ and $B=A\operatorname{diag}(d_v^{-1})$, so
$b_{uv}=A_{uv}/d_v$. This is a column normalization, with

$$
 b_{vv}=1,\qquad b_{uv}\geq0,\qquad
 b_{uv}b_{vw}
   =\frac{A_{uv}A_{vw}}{d_vd_w}
   \leq\frac{A_{uw}}{d_w}=b_{uw}.
 \tag{3.5}
$$

For $d_U=\prod_{v\in U}d_v$, the cycle expansion, or equivalently the
fact that a permutation uses each column once, gives

$$
 p_{\alpha,A}(U)=d_U p_{\alpha,B}(U).
 \tag{3.6}
$$

This is the positive column scaling used in Sra's Remark A.2, applied
to the alpha-permanent with its unchanged cycle count. In particular,

$$
 d_{S\cup T}d_{S\cap T}=d_Sd_T>0,
 \tag{3.7}
$$

so log-supermodularity is equivalent for the two set functions.

Assume first $n\geq2$. Fix any $R\subseteq[n]$ and distinct
$i,j\in[n]\setminus R$. Then $r=|R|\leq n-2$, and

$$
 \alpha\geq((n-1)!)^2\geq((r+1)!)^2\geq1.
$$

Equations (3.5) and (2.2) yield

$$
 p_{\alpha,B}(Rij)p_{\alpha,B}(R)
      \geq p_{\alpha,B}(Ri)p_{\alpha,B}(Rj).
 \tag{3.8}
$$

We give the passage from these elementary inequalities to all subset
pairs explicitly. Write $f(U)=p_{\alpha,B}(U)$. The identity permutation
has weight $\alpha^{|U|}$, so $f(U)\geq\alpha^{|U|}>0$ for every $U$,
including $f(\varnothing)=1$. For $i\notin U$, define

$$
 q_i(U)=\frac{f(Ui)}{f(U)}.
$$

Dividing (3.8) by the positive number $f(R)f(Rj)$ shows
$q_i(Rj)\geq q_i(R)$. Adding elements one at a time proves
$q_i(X)\leq q_i(Y)$ whenever $X\subseteq Y$ and $i\notin Y$.

For arbitrary $S,T$, put $I=S\cap T$ and list
$S\setminus T=\{i_1,\ldots,i_k\}$. Let
$X_a=I\cup\{i_1,\ldots,i_{a-1}\}$ and
$Y_a=T\cup\{i_1,\ldots,i_{a-1}\}$. Then $X_a\subseteq Y_a$ and
$i_a\notin Y_a$. Multiplying their ratio inequalities gives

$$
 \frac{f(S)}{f(I)}
   =\prod_{a=1}^k q_{i_a}(X_a)
   \leq\prod_{a=1}^k q_{i_a}(Y_a)
   =\frac{f(S\cup T)}{f(T)}.
 \tag{3.9}
$$

The products are one when $k=0$. Multiplying by $f(I)f(T)>0$
proves log-supermodularity of $f$, and (3.6)--(3.7) give (3.2) for $A$.

If $n=1$, any two subsets are nested. Their union and intersection
are the two original subsets, so (3.2) is equality. The value
$\alpha_1=(0!)^2=1$ is therefore sufficient as well.

All inequalities above are non-strict at the stated threshold.
Only diagonal entries were divided by, and they are strictly positive
for every matrix in the stated class. In particular, off-diagonal
zeros and reducibility require no limiting argument. $\square$

The quantifiers in Theorem 3.1 are those of Sra's §4(c). Sra's
Appendix A.1 instead asserts that for each fixed $\alpha>0$ some
possibly larger dimension admits a failure. These assertions are
compatible, since the sufficient values in (3.1) are unbounded as
$n$ grows. Theorem 3.1 does not assert that (3.1) is the least possible
threshold. Its matrix class is the full inverse-$M$ class, whereas
Sra's §4(b) singles out symmetrizable matrices and asks about other
positive orders; §4(d) concerns the reciprocal-permanent polynomial
rather than (3.2).

## 追加锚（本行以下为增补区）
