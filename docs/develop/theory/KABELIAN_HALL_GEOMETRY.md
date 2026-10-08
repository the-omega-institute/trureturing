# Uniform geometry of four-digit continued-fraction cuts

## 1. Prefixes and lengths

Let $m=(\sqrt{2}-1)/2$, $M=4m$, $w=M-m$, and $d=1+m-M$.
A finite simple continued-fraction prefix has positive digits, current denominator
$q$, previous denominator $q'$, and its usual continuant tail action $T$.
The empty prefix has $q=1$ and $q'=0$. Put $s=q'/q$ and define the image lengths

$$
c_a=|T(1/(a+m))-T(1/(a+M))|,\qquad
g_a=|T(1/(a+M))-T(1/(a+1+m))|.
$$

## 2. Uniform cut estimates

**Theorem 2.1 (prefix cut geometry).** For every such prefix, $0\le q'\le q$,
and for every real $a\ge1$,

$$
c_a=\frac{w}{q^2(a+m+s)(a+M+s)},\qquad
g_a=\frac{d}{q^2(a+M+s)(a+1+m+s)}.
$$

For $1\le a\le3$, the gap is positive and shorter than each adjacent child:
$0<g_a<c_a$ and $g_a<c_{a+1}$. Moreover $c_a\le3g_a$,
$c_4\le3g_3$, and $g_b<g_a$ whenever $1\le a<b$.
For $1\le a\le3$, $3g_a<|T(m)-T(M)|$.

The denominator recurrence gives $0\le q'\le q$ by induction, so $s\in[0,1]$.
The continuant determinant difference formula gives the displayed lengths.
For the right adjacent child, the quotient of the gap length and child length
is $(d/w)(a+m+s)/(a+1+m+s)$, which is less than $d/w<1$.
For the other child, the quotient is
$(d/w)(1+1/(a+M+s))$, whose maximum occurs at $a=1,s=0$ and equals
$2\sqrt{2}/3<1$. The first quotient increases with $a+s$;
its minimum is $(d/w)(1+m)/(2+m)=1/3$.
The fourth child has $g_3/c_4>d/w>1/3$.
Finally both denominator factors in $g_a$ strictly increase with $a$, proving
strictly decreasing gaps. All denominators in these estimates are positive.
The two adjacent child lengths and their gap add to the image length of their
combined interval, which is contained in the full prefix hull. Both children
are longer than the gap, so the combined length exceeds three times the gap.
The determinant difference formula establishes additivity of image lengths on
ordered subintervals, independently of the prefix orientation.

## 3. Source and scope

These estimates supply the all-prefix geometry in the elementary four-digit Hall
construction in Section 7.2 of the supplied k-abelian Lagrange proof. The classical
source is M. Hall, Jr., *On the sum and products of continued fractions*,
Ann. of Math. 48 (1947), 966–993, DOI 10.2307/1969389.
They do not alone construct the binary tree or assert a Cantor sum interval.

## 追加锚（本行以下为增补区）

## 4. Binary branch addresses

Encode a committed positive digit by an element of $\operatorname{Fin}(4)$ plus one.
An address consists of a committed finite digit list $P$ and a cursor
$j\in\{0,1,2\}$, representing the pending digits $j+1,\ldots,4$.
Initially $P$ is empty and $j=0$. At a binary cut, choosing the physical right child
commits digit $j+1$ when the committed prefix length is even; the physical left child
commits it when that length is odd. A commitment resets the cursor to zero.
The opposite child increments the cursor, except at $j=2$, where it commits digit four
and resets the cursor. Thus the number of pending cuts between two commitments is bounded.

**Theorem 4.1 (infinite binary branch expansion).** For every infinite binary path,
there exists $x\in C_4$ such that, at every stage $n$, its computed expansion begins
with exactly the committed digit list $P_n$, and its next computed digit belongs to
$\{j_n+1,\ldots,4\}$. Furthermore $n\le3|P_n|+j_n$.

The stage inequality and the fact that committed lists only extend imply that every
position is eventually committed. Select digit $i$ from the list at stage $3(i+1)$.
Any two lists have a common later extension, so this diagonal selection agrees with
all previously committed digits. A joint induction tracks the cursor until the next
commitment and bounds that committed digit from below by the earlier cursor.
The resulting infinite stream has positive digits at most four. Its irrational value
has that exact computed expansion, and satisfies every stage's pending-digit restriction.
The construction establishes branch realizability; interval-tree endpoints and their
sum set require the separate all-prefix geometry and nesting arguments.

## 追加锚（本行以下为增补区）

## 5. Descendant cuts

**Theorem 5.1 (binary gap descent).** Let an infinite positive simple continued fraction
agree with every committed prefix of a binary Hall address. At stage $n$, write $q_n$
and $p_n$ for its current and previous denominators, and $j_n$ for the pending cursor.
The sequence of pending gap lengths

$$
\gamma_n=\frac{d}{((j_n+1+M)q_n+p_n)((j_n+2+m)q_n+p_n)}
$$

is nonincreasing and tends to zero. The denominators here are evaluated at the
committed digit length, rather than at the binary stage number.

If a step only increments the cursor, both denominator factors increase. If a step
commits a digit $b$, then $b\ge a=j_n+1$, the cursor resets to zero, and the new
denominators are $Q=bq_n+p_n$ and $q_n$. The new factors are
$(1+M)Q+q_n$ and $(2+m)Q+q_n$. They dominate the old factors because
$b\ge a\ge1$, $q_n>0$, $p_n\ge0$, $M>0$, and $m>0$.
Indeed their respective differences are
$((b-a)+M(b-1)+1)q_n+Mp_n$ and
$((b-a)+(1+m)(b-1)+1)q_n+(1+m)p_n$.
Both are positive. Taking products and reciprocals proves the commitment estimate.
The address recurrence exhausts the two cases, so adjacent-stage comparison gives
descent for all later stages. The stage inequality $n\le3|P_n|+j_n$, with $j_n<3$,
forces the committed length to grow. Fibonacci growth gives
$q_n\ge f_{|P_n|+1}\ge|P_n|+1$ once the committed length is at least four.
The normalized gap is less than $1/q_n^2$, since $d<1$ and both normalized
denominator factors exceed one. This gives the asserted convergence with a threshold
uniform over compatible continued fractions. This result supplies gap monotonicity
and shrinking gaps; interval nesting and the Hall sum theorem remain separate obligations.

## 追加锚（本行以下为增补区）

## 6. Pending cylinders and their intersection

**Theorem 6.1 (nested binary cylinders).** Let a simple continued fraction with head
zero agree with all the committed digit prefixes of an infinite binary Hall path.
At stage $n$, let $P_n$ be the committed prefix and $j_n$ its cursor. Write

$$
I_n=T_{P_n}([m,1/(j_n+1+m)]).
$$

Then $I_{n+1}\subseteq I_n$. Their diameters tend to zero, uniformly over paths and
compatible continued fractions. Their common intersection consists of one point of $C_4$.

A cursor increment decreases the upper tail endpoint. A digit commitment selects a
digit $a\in\{j_n+1,\ldots,4\}$. The reciprocal image of $[m,M]$ under this digit
lies in $[m,1/(j_n+1+m)]$, using $m=1/(4+M)$ and $M=1/(1+m)$.
The continuant recurrence composes this reciprocal with the old prefix action.
Induction on the number of appended digits also projects every later full cylinder
into every earlier full cylinder. Since $n\le3|P_n|+j_n$ and $j_n<3$, prefix lengths
grow uniformly. The Fibonacci prefix estimate bounds the diameter by
$1/f_{|P_n|+1}^2$. Each pending cylinder is a nonempty compact image of a closed
interval, so nested compact intersection supplies a survivor. For every digit depth,
a sufficiently late pending cylinder projects into a four-digit cylinder of that depth.
The finite-cylinder survivor classification identifies the common point as a member of
$C_4$. The diameter bound gives uniqueness. Physical endpoint orientation and the
two-child Hall sum construction remain separate obligations.

## 追加锚（本行以下为增补区）

## 7. Coding every four-digit expansion

**Theorem 7.1 (binary address completeness).** For every $x\in C_4$, there is an
infinite binary path whose committed list $P_n$ agrees with the computed expansion
of $x$ at every stage $n$, and whose next computed digit is in
$\{j_n+1,\ldots,4\}$.

At each cut, inspect the next computed digit $a$. If $a=j+1$, choose the child
that commits this digit, accounting for the parity of the committed length.
Otherwise choose the opposite child. If $j=2$, the inequalities $3<a\le4$ force
$a=4$, so this child commits digit four. In the remaining case the cursor increases
and stays below the next digit. A joint induction proves that committed digits agree
with the given expansion and that the cursor restriction persists. Each finite path
changes only its newly chosen binary coordinate. Hence the coordinate at every fixed
position stabilizes; the diagonal infinite path agrees with every finite stage.
Induction on address depth proves that these agreements preserve the address itself.
This establishes address completeness without a second continued-fraction representation.

## 追加锚（本行以下为增补区）

## 8. The physical endpoint tree

**Theorem 8.1 (concrete four-digit Hall tree).** There is a binary interval tree
with root $[m,M]$ whose interval at every finite binary path is the continuant image
of $[m,1/(j+1+m)]$ for that path's committed prefix $P$ and pending cursor $j$.
The image is independent of the infinite continuation used to represent the prefix.
Each cut retains the two outer endpoints, has strictly positive gap, and leaves two
children of width at least that gap. Gaps do not increase along an edge, and interval
widths shrink uniformly with binary path depth.

Reconstruct the finite address by reading the reversed path, padding after its end
with arbitrary binary choices. Induction shows that address computation depends only
on the choices already read. A continuant recurrence induction shows that two streams
with the same first $|P|$ digits have identical continuants at that depth. Consequently
all infinite extensions give the same interval.

The signed determinant gives increasing orientation at even prefix depth and decreasing
orientation at odd depth. Write $a=j+1$, $u=1/(a+m)$, $v=1/(a+1+m)$, and
$w=1/(a+M)$. The committed child has tail hull $[w,u]$; the pending child has tail hull
$[m,v]$. At the last cursor, that pending hull is precisely the digit-four child,
because $m=1/(4+M)$. Orientation identifies their physical left and right endpoints.
The determinant difference formula identifies the cut width as $g_a$ and the committed
width as $c_a$. The pending child contains the adjacent digit-$(a+1)$ hull, so its width
is at least $c_{a+1}$. The uniform adjacent-cell estimates imply both child-size bounds.
The cross-depth normalized gap comparison gives the descendant-gap bound. Finally
binary progress forces $n\le3|P|+j$, and Fibonacci denominator growth makes the widths
shrink uniformly in all paths.

**Theorem 8.2 (four-digit Hall sum).**

$$
C_4+C_4=[\sqrt2-1,4(\sqrt2-1)].
$$

Every real $t$ has a representation $t=N+x+y$ with $N\in\mathbb Z$ and $x,y\in C_4$.

Positive separation makes the level interval containing a point unique. Induction on
level shows that two containing intervals have the same parent and then the same child.
Thus independently chosen surviving level intervals have compatible parents. Reading
their final child choices constructs an infinite path. The concrete tree bridge and the
nested-cylinder theorem identify its survivor with a point of $C_4$.

The root gap fits within the root interval, so the abstract Hall splitting theorem applies
to two copies of this tree. Its two level survivors belong to $C_4$ by the preceding
compatibility construction, proving containment of the whole hull sum in $C_4+C_4$.
The reverse containment follows from the sharp hull bound. Since
$3(\sqrt2-1)>1$, choosing $N=\lfloor t-(\sqrt2-1)\rfloor$ places $t-N$ in that hull sum.
