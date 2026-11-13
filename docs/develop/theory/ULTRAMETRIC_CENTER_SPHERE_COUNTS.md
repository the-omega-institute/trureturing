# Prescribed sphere counts at the center of a finite ultrametric space

## 1. The center and the size recurrence

**Definition 1.1.** In a nonempty finite ultrametric space $(X,d)$, write
$S(x,c)=\{y\in X:d(x,y)=c\}$. The center of distances is
$C(X)=\{c\ge 0:S(x,c)\ne\varnothing\text{ for every }x\in X\}$.

Dovgoshey, Jaiswal, Kainth, Kaur, and Rovenska ask in
[Problem 5.4 of their preprint on maximal distance centers](https://arxiv.org/pdf/2609.11384v1#page=27) when a finite ultrametric
can have prescribed pointwise sphere counts at every central radius. The
following criterion gives all possible orders for any fixed list of radii.

**Theorem 1.2.** Fix real radii $0=c_0<c_1<\cdots<c_h$ and positive integers
$b_0,\ldots,b_h$. For a set $A$ of positive integers, let $\Sigma^+(A)$
be the set of sums of nonempty finite lists from $A$, with repetition
allowed. Define

$$
A_0=\{1\},\qquad
A_i=\{b_i+t:t\in\Sigma^+(A_{i-1}),\ t\mid b_i\}
\quad (1\le i\le h).
$$

If $b_0\ne 1$, there is no nonempty finite ultrametric space with center
$\{c_0,\ldots,c_h\}$ and $|S(x,c_i)|=b_i$ for every $x$ and $i$.
If $b_0=1$, the possible orders of such spaces are exactly the elements of
$A_h$. Moreover, for any choice of pairs $c_{i-1}<u_i<v_i<c_i$, each of
these orders can be realized using only the central radii and the chosen
$u_i,v_i$ as distance values. In computing $A_i$, it suffices to check
positive sums up to $b_i$.

*Proof.* The zero sphere is a singleton. For $i\ge 1$, the relation
$d\le c_i$ partitions $X$ into closed balls, by the ultrametric
inequality. Fix one such ball $B$. The relation $d<c_i$ partitions $B$
into classes. At each point $x\in B$, the $c_i$-sphere is the complement
of its class in $B$. Thus every class has size $t=|B|-b_i>0$; if there
are $r$ classes, then $b_i=(r-1)t$. Each class is a union of closed
$c_{i-1}$-balls. Since closed $c_0$-balls are singletons, induction
shows that $t\in\Sigma^+(A_{i-1})$ and $|B|=b_i+t\in A_i$.

The diameter $D$ of a nonempty finite ultrametric space belongs to the
center: for any diameter pair $p,q$ and any $x$,
$\max(d(x,p),d(x,q))=D$. The diameter is therefore $c_h$, since $c_h$
is itself a realized distance and is the largest central radius. Hence
$X$ is a single closed $c_h$-ball. This also gives the singleton case
when $h=0$. The sum bound follows because each candidate $t$ is a
positive divisor of $b_i$.

For the converse, use the following join: take a disjoint union of
ultrametric spaces with all distances strictly below $a>0$, and set the
distance between distinct components to $a$. In a triple meeting more
than one component, at least two distances equal $a$, so the resulting
space is ultrametric. At any radius below $a$, each point sees precisely
its former sphere in its component. At radius $a$, it sees exactly the
points outside its component. These statements include the join of just
one component.

At stage zero use a singleton. Inductively, realize each element of
$A_{i-1}$ with exactly the central radii and counts through $c_{i-1}$,
using only those radii and the chosen pairs from the preceding gaps. For
$b_i+t\in A_i$, choose a list of elements of $A_{i-1}$ summing to $t$
and a list of corresponding ultrametric spaces. Form $r=1+b_i/t\ge 2$
groups, each containing disjoint copies of that list. Join the pieces of
the first group at $u_i$ and the pieces of each other group at $v_i$.
Finally join the groups at $c_i$. This space has $rt=b_i+t$ points. Each
point has $(r-1)t=b_i$ neighbors at $c_i$, and all earlier sphere
counts and witnesses for absent radii persist. A point in the first group
has no neighbor at $v_i$, and a point in any other group has no neighbor
at $u_i$. Thus neither new gap radius is central. Every distance is on
the stated list, so the center at stage $i$ is exactly
$\{c_0,\ldots,c_i\}$. This gives a space for each order in $A_h$.

## 2. Sharpness of the two distances per gap

**Proposition 2.1.** Suppose the center is $\{0,1,2\}$ and the pointwise
sphere counts are $(1,2,4)$. The space has eight points, and at least two
distinct distances in $(0,1)$ are necessary. Any two fixed distances in
that gap suffice, with no extra distances in $(1,2)$.

*Proof.* The recurrence gives $A_1=\{3,4\}$. Among the positive divisors
of $4$, only $4$ is a sum from $A_1$, so $A_2=\{8\}$. As in the
necessity proof, every strict $2$-class has four points and must be a
single closed $1$-ball. Within such a ball every strict $1$-class has
two points. Every point therefore has a neighbor at a distance in
$(0,1)$. If only one distance in that interval occurred, it would be
central, contrary to the prescribed center.

Conversely, form two four-point blocks, each split into two pairs. Use the
first chosen distance within pairs of the first block and the second within
pairs of the second block. Put distance $1$ between pairs in a block and
distance $2$ between blocks. This is an ultrametric by the join argument.
Each point has exactly two neighbors at $1$ and four at $2$, and each
chosen distance is absent from every sphere centered in the other block.
