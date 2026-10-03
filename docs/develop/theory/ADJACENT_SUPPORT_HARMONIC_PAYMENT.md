# Adjacent-support harmonic payment

## 1. Graphs and potentials

**定义 1.1（Harmonic and defect potentials）。** For a finite simple graph $F$, let

$$
H(F)=\sum_{xy\in E(F)}\frac{2}{d_F(x)+d_F(y)},\qquad
\phi(d,e)=\frac{(d-e)^2}{2de(d+e)},\qquad
D(F)=\sum_{xy\in E(F)}\phi(d_F(x),d_F(y)).
$$

Every edge is unordered and counted once. The arithmetic is rational. Isolated
vertices contribute zero to both sums. Endpoint degrees on an edge are positive.
For a set $X$ of vertices, $F[V(F)\setminus X]$ retains all vertices outside $X$,
including isolates, and uses their degrees in the induced graph.

## 2. Simultaneous deletion of adjacent supports

**定理 2.1（Adjacent-support payment）。** Let $G$ be any finite connected simple
graph of maximum degree at most four. Suppose that every vertex has at most one
neighbor of original degree one. Let $a,b,u,v\in V(G)$ satisfy $ab,au,bv\in E(G)$,
$d_G(a),d_G(b)\geq2$, and $d_G(u)=d_G(v)=1$. For the actual induced graph
$Q=G[V(G)\setminus\{a,b\}]$, one has

$$
\frac{21}{20}\leq H(G)-H(Q).
$$

Proof. Put $X=\{a,b\}$. For each retained vertex $x$, let
$q(x)=|N_G(x)\setminus X|$, $r(x)=|N_G(x)\cap X|$, and let $t(x)$ count its
original degree-one neighbors. Thus $q(x)=d_Q(x)$, $q(x)+r(x)=d_G(x)$,
$0\leq r(x)\leq2$, and $0\leq t(x)\leq\min(1,q(x))$. An original leaf cannot
belong to $X$. If an original leaf edge survives, the leaf's residual degree is
one. In particular the loss at a shared neighbor is the joint value $r=2$.

Define $c(1,t)=0$, and for nonleaf degrees use

$$
\begin{aligned}
(c(2,0),c(2,1))&=(0,1/12),\\
(c(3,0),c(3,1))&=(1/30,1/10),\\
(c(4,0),c(4,1))&=(3/40,13/120).
\end{aligned}
$$

Let $m(d,0)=0$, $m(2,r)=0$, $m(3,r)=1/60$ for $r=1,2$,
$m(4,1)=1/40$, and $m(4,2)=1/24$. For retained adjacent vertices define the
directed charge

$$
A(x,y)=\begin{cases}
0,&d_G(x)=1,\\
\phi(d_G(x),1)-\phi(q(x),1),&d_G(x)>1,\ d_G(y)=1,\\
m(d_G(x),r(x)),&d_G(y)>1,\ d_G(y)<d_G(x),\\
0,&\text{otherwise}.
\end{cases}
$$

On a retained edge both residual endpoint degrees are positive. Its defect
decrease is at most $A(x,y)+A(y,x)$. For an original leaf edge this uses its
exact defect difference. For equal original nonleaf degrees the original
defect is zero and the residual defect is nonnegative. For unequal original
nonleaf degrees, the pairs are $(3,2)$, $(4,2)$, and $(4,3)$, together with
reverse orientations; substitution of the allowed losses $0,1,2$ gives the
stated $m$ bounds.

At a retained nonleaf vertex of original degree $d$, exactly $t$ surviving
neighbors are original leaves and $q-t$ are original nonleaves. Consequently

$$
\sum_{y\in N_G(x)\setminus X}A(x,y)
\leq t\bigl(\phi(d,1)-\phi(q,1)\bigr)+(q-t)m(d,r)
\leq r c(d,t).
$$

The last inequality follows by substituting $d\in\{2,3,4\}$,
$r\in\{0,1,2\}$, $q=d-r$, and $t\in\{0,1\}$ with $t\leq q$.
If $q=0$, necessarily $t=0$ and the row is empty.

Define charges on all directed original edges as follows. Between retained
vertices use $A(x,y)$. From a retained vertex $x$ to a deleted vertex use
$-c(d_G(x),t(x))$. From a deleted vertex $x$ to a retained vertex $y$ use
$\phi(d_G(x),d_G(y))+c(d_G(y),t(y))$. Between two deleted vertices use half
their original defect. Summing the two orientations dominates each unordered
edge's actual defect decrease; the capacities cancel across boundary edges.
Every retained vertex row is nonpositive by the preceding estimate.

Set $K(2)=3/20$, $K(3)=4/35$, and $K(4)=1/8$. For a deleted support of degree
$d$ and a retained nonleaf neighbor of degree $e$, direct substitution of
$d,e\in\{2,3,4\}$ and $t\in\{0,1\}$ gives
$\phi(d,e)+c(e,t)\leq K(d)$. Reserve the edge to the other support and the
unique original pendant edge. The remaining $d-2$ neighbors are nonleaves.
The row at $a$, writing $d=d_G(a)$ and $e=d_G(b)$, is therefore at most
$\phi(d,1)+\phi(d,e)/2+(d-2)K(d)$. The analogous row at $b$ gives

$$
D(G)-D(Q)\leq\phi(d,1)+\phi(e,1)+\phi(d,e)
 +(d-2)K(d)+(e-2)K(e)\leq\frac{19}{20}.
$$

The final inequality is the nine substitutions $d,e\in\{2,3,4\}$.
The edge $ab$ has been counted once, and both original pendant edges have
been retained in the estimate.

For any finite graph $F$, summing
$2/(d+e)=1/(2d)+1/(2e)-\phi(d,e)$ over its unordered edges gives
$H(F)=n_+(F)/2-D(F)$, where $n_+(F)$ counts nonisolated vertices.
The edge $ab$ forces $a\ne b$. The original degree-one vertices $u,v$ are
outside $X$, and they are distinct: equality would give a leaf adjacent to
both $a$ and $b$. Both become isolates in $Q$. If $i$ is the total number of
isolates in $Q$, then $i\geq2$ and

$$
H(G)-H(Q)=\frac{2+i}{2}-(D(G)-D(Q))
\geq2-\frac{19}{20}=\frac{21}{20}.
$$

The argument allows triangles, common neighbors, and additional residual
leaves or isolates. It imposes no minimum degree on $Q$.

## 3. Retained-leaf and pendant boundaries

For the triangle $abc$ with pendant edges $au,bv,cw$, the original degrees
are $3,3,3,1,1,1$. Deleting $a,b$ leaves $cw$ and the isolates $u,v$.
Thus $H(G)=5/2$, $H(Q)=1$, and the decrease is $3/2$.
The retained original leaf edge $cw$ has defect decrease
$\phi(3,1)-\phi(1,1)=1/6>1/15$. A bound that omits its leaf charge is false.
For $K_4$, deletion of two adjacent vertices has harmonic decrease exactly
one; $K_4$ has no original pendant neighbors, so removing the pendant
hypotheses invalidates the conclusion.

## 追加锚（本行以下为增补区）
