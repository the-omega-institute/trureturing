# Ordered simplex cochain energy

## 1. Alternating triangle cochains

**Definition 1.1 (ordered cochains and energies).** Let $V$ be a nonempty
finite set of size $n$. A real triangle cochain $F:V^3\to\mathbb R$ is
alternating when swapping either adjacent pair of arguments changes its
sign. Put
$$
 S(i,j)=\sum_{r\in V}F(r,i,j),\qquad
 a(i,j)=\frac{S(i,j)}n,\qquad
 (da)(i,j,k)=a(j,k)-a(i,k)+a(i,j),
$$
and
$$
 (dF)(r,i,j,k)=F(i,j,k)-F(r,j,k)+F(r,i,k)-F(r,i,j).
$$
All sums below range over ordered tuples, including tuples with repeated
vertices. Alternation determines the values on those tuples.

**Theorem 1.2 (exact degree-two energy projection).** Every alternating
real triangle cochain on $V$ satisfies
$$
 \sum_{r,i,j,k\in V}(dF)(r,i,j,k)^2
 =4n\sum_{i,j,k\in V}\bigl(F(i,j,k)-(da)(i,j,k)\bigr)^2.
$$

*Proof.* Antisymmetry gives $S(i,j)=-S(j,i)$ and
$\sum_i S(i,j)=0$: the latter sum cancels after interchanging the two
summation indices. Write $\|F\|_2^2=\sum_{i,j,k}F(i,j,k)^2$ and
$\|S\|_2^2=\sum_{i,j}S(i,j)^2$. Expanding $da$ and using the
zero-divergence relation removes all its mixed products, giving
$\|da\|_2^2=3\|S\|_2^2/n$. Alternation also gives
$\langle F,da\rangle=3\|S\|_2^2/n$. Hence
$$
 \|F-da\|_2^2=\|F\|_2^2-3\|S\|_2^2/n.
$$
In the expansion of $\|dF\|_2^2$, each of the four diagonal terms is
$n\|F\|_2^2$. Each of the six mixed products, with its sign from the
coboundary, is $-\|S\|_2^2$ before the factor two from squaring.
Consequently $\|dF\|_2^2=4n\|F\|_2^2-12\|S\|_2^2$, which is four
times $n$ times the preceding residual identity. $\square$

The complete-simplex Laplacian is classical; see Danijela Horak and
Jurgen Jost, *Spectra of combinatorial Laplace operators on simplicial
complexes*, Advances in Mathematics (2013), DOI
[10.1016/j.aim.2013.05.007](https://doi.org/10.1016/j.aim.2013.05.007).
The theorem records the explicit ordered normalization and averaged edge
reconstruction used here.

## 2. The optimal coefficient

**Theorem 2.1 (sharp degree-two energy coefficient).** Suppose $n\ge4$.
The coefficient $4n$ in Theorem 1.2 is the least real number $C$ for
which every alternating triangle cochain satisfies
$$
 \sum_{r,i,j,k\in V}(dF)(r,i,j,k)^2
 \le C\sum_{i,j,k\in V}\bigl(F(i,j,k)-(da)(i,j,k)\bigr)^2.
$$
In particular, for every $C<4n$ an alternating cochain violates this
inequality.

*Proof.* Theorem 1.2 shows that $4n$ is an admissible coefficient.
To prove minimality, choose four distinct vertices $p_0,p_1,p_2,p_3$.
For $t\in V$ write $e_t(x)=1$ if $x=t$ and $0$ otherwise. Let $F$ be
the alternating determinant of the three coordinate functions
$e_{p_1},e_{p_2},e_{p_3}$, evaluated at $(i,j,k)$. Expanding the
determinant shows that $F(p_1,p_2,p_3)=1$, while $F$ vanishes on every
triple containing $p_0$. Consequently
$(dF)(p_0,p_1,p_2,p_3)=1$, so the defect energy is positive. Theorem
1.2 and $n>0$ imply that its averaged-reconstruction residual energy
is also positive. Substituting this $F$ into a universal bound with
coefficient $C$ and cancelling the positive residual energy gives
$4n\le C$. $\square$
