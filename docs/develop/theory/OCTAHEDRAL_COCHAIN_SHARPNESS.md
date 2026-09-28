# Octahedral degree-two cochain sharpness

## 1. Simplicial model

Let $X$ be the boundary of the four-dimensional cross-polytope. Its vertex set is
$\{(i,\epsilon):i\in\{0,1,2,3\},\ \epsilon\in\mathbf F_2\}$, and a face contains
at most one vertex from each pair with fixed $i$. Thus its 16 tetrahedra are
indexed by $b\in\mathbf F_2^4$, and its 32 unordered triangular faces are
indexed by a coordinate $i$ and an assignment of the other three bits. A
triangle is incident to the two tetrahedra obtained by choosing either value
of its missing coordinate. All faces have distinct vertices.

For a triangular cochain $F$ with coefficients in $\mathbf F_2$, let $d_2F$
sum its four incident triangle values at each tetrahedron, and let
$\operatorname{wt}(F)$ count triangles on which $F$ is nonzero. An edge cochain
$e$ has coboundary $d_1e$ equal to the sum of its three edge values on each
triangle. Write $T(F)=\operatorname{wt}(d_2F)$ and
$R(F)=\min_e\operatorname{wt}(F+d_1e)$.

Dotterrer--Kahle, *Coboundary expanders* (2012), Proposition 5.5, DOI
10.1142/S1793525312500197, and Lubotzky--Meshulam--Mozes, *Expansion of
building-like complexes* (2016), Theorem 3.3, DOI 10.4171/GGD/346, imply
$R(F)\leq 2T(F)$ for this complex.

## 2. Antipodal sharpness

**定理 2.1（四面支集与二处缺陷）。** There is a triangular cochain $P$ supported on
exactly four faces such that $T(P)=2$ and, for every edge cochain $e$,
$\operatorname{wt}(P+d_1e)\geq4$. In fact $R(P)=4$, so the coefficient $2$ in
the preceding inequality is attained.

Take the four cube edges of the path
$0000\to1000\to1100\to1110\to1111$ as the support of $P$. Every interior
tetrahedron meets the path in two edges and the endpoints meet it in one;
therefore $d_2P$ is supported precisely at $0000$ and $1111$. Each simplicial
edge lies in two triangles of a tetrahedron, so $d_2d_1e=0$. For any cochain
$H$ with $d_2H=d_2P$, sum $d_2H$ over tetrahedra with coordinate $i$ equal to
zero. Every triangle whose missing coordinate differs from $i$ occurs twice
and cancels. A triangle whose missing coordinate is $i$ occurs once. Exactly
one endpoint is on that side, hence the direction-$i$ triangle values sum to
one. Each of the four disjoint direction classes therefore contains a
supported triangle, giving $\operatorname{wt}(H)\geq4$. Apply this to
$H=P+d_1e$; choosing $e=0$ gives equality.

## 追加锚（本行以下为增补区）
