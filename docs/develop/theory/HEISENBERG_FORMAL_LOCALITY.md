# Formal distributions and Heisenberg locality

## 1. Conventions

**Convention 1.1 (modes).** Let $V$ be a rational vector space, let
$A:\operatorname{VertexOperator}(\mathbb Q,V)$, and write its normalized modes as
$A_m=A[[m]]\in\operatorname{End}_{\mathbb Q}(V)$, so formally
$A(z)=\sum_{m\in\mathbb Z}A_mz^{-m-1}$. This indexing agrees with the Heisenberg-field
expansion in Chu--Lin [1, Section 3.1]; Kac [2] is background on vertex algebras.
Let $K\in\operatorname{End}_{\mathbb Q}(V)$, with no assumption that $K$ is nonzero.

**Convention 1.2 (coefficient shift).** For an endomorphism-valued function
$F:\mathbb Z^2\to\operatorname{End}_{\mathbb Q}(V)$ define
$(\Delta F)(m,n)=F(m+1,n)-F(m,n+1)$. With the normalized exponents in Convention 1.1,
this is the coefficient of $z^{-m-1}w^{-n-1}$ in $(z-w)\sum_{i,j}F(i,j)z^{-i-1}w^{-j-1}$.
Write $C_A(m,n)=A_m\circ A_n-A_n\circ A_m$.

## 2. Heisenberg locality

**Theorem 2.1 (mode-to-locality with sharp first-order obstruction).** For every rational vector
space $V$, every $A:\operatorname{VertexOperator}(\mathbb Q,V)$ and
$K\in\operatorname{End}_{\mathbb Q}(V)$, suppose that for every $m,n\in\mathbb Z$,
$C_A(m,n)=mK$ when $m+n=0$, and $C_A(m,n)=0$ otherwise. This is the Heisenberg
mode-relation form of the bracket in Chu--Lin [1, Section 3.1]. Then
$(\Delta^2C_A)(m,n)=0$ for every $m,n$,
$(\Delta C_A)(0,-1)=K$, and
$[\forall m,n,\ (\Delta C_A)(m,n)=0]\iff K=0$.

**Proof.** The two arguments of $C_A$ in $(\Delta C_A)(m,n)$ have the same index sum
$m+n+1$. Off its zero locus both terms vanish. On that locus their scalar coefficients are
$m+1$ and $m$, whose difference is one. Thus $(\Delta C_A)(m,n)$ is $K$ precisely when
$m+n+1=0$, and zero otherwise. Applying $\Delta$ again subtracts two equal values because
$(m+1)+n+1=m+(n+1)+1$. The pair $(0,-1)$ lies on the nonzero locus and recovers $K$;
the resulting coefficient identity gives both directions of the stated equivalence.

**Remark 2.2.** The theorem is conditional on the stated mode relation. It does not assert
the existence of $A$ with $K\ne0$. When $K=0$, the first coefficient shift vanishes;
when $K\ne0$, the coefficient at $(0,-1)$ shows that the first shift does not vanish.

## References

[1] Y. Chu and Z. Lin, *Moduli spaces of conformal structures on Heisenberg vertex
algebras*, arXiv:1812.11378v1 (2018), Section 3.1,
https://arxiv.org/abs/1812.11378v1. The cited section displays the Heisenberg
bracket and $Y(h,z)=\sum_n h(n)z^{-n-1}$; the coefficient-shift consequence is proved above.

[2] V. Kac, *Vertex Algebras for Beginners*, AMS University Lecture Series 10
(1998), DOI: 10.1090/ulect/010.

## 追加锚（本行以下为增补区）

## 3. A rational polynomial Heisenberg field

**Theorem 3.1 (shifted polynomial Fock modes).** Let
$V=\mathbb Q[X_0,X_1,\ldots]$, with vacuum $1\in V$. For each integer $m$ define a
$\mathbb Q$-linear endomorphism $a_m$ of $V$: if $m=k+1>0$, set
$a_m=(k+1)\partial/\partial X_k$; if $m=-(k+1)<0$, set $a_m$ to multiplication
by $X_k$; and set $a_0=0$. There is a Mathlib vertex operator $A$ on $V$ whose
normalized coefficient $A[[m]]$ is $a_m$ for every $m\in\mathbb Z$. Its Laurent
coefficients are pointwise bounded below: for each polynomial $p$, all sufficiently
large positive modes $a_m$ annihilate $p$. For every $m,n\in\mathbb Z$,
$$
  a_m\circ a_n-a_n\circ a_m
  =\begin{cases}m\,\mathrm{id}_V,&m+n=0,\\0,&m+n\ne0.\end{cases}
$$
In particular, $(a_1\circ a_{-1}-a_{-1}\circ a_1)(1)=1\ne0$.
Every variable $X_k=a_{-(k+1)}(1)$ is reached from the vacuum; products of
negative modes applied to $1$ span $V$ over $\mathbb Q$.

**Proof.** A polynomial has finite variable support. A positive mode indexed beyond
that support is a partial derivative in a missing variable, hence zero on the
polynomial. This supplies the pointwise support bound for `VertexOperator.of_coeff`.
Two multiplication modes commute, as do two partial derivatives. The Leibniz rule
and $\partial X_j/\partial X_i=\delta_{ij}$ give
$[a_{k+1},a_{-(j+1)}]=(k+1)\delta_{kj}\,\mathrm{id}_V$; reversing the order changes
the sign. The zero mode contributes zero. These cases yield the displayed relation
for every integer pair. Since $a_{-1}(1)=X_0$, $a_1(X_0)=1$, and $a_1(1)=0$,
the vacuum commutator equals $1$. The monomials in the $X_k$ form the polynomial
basis and are products of the stated multiplication modes applied to $1$.

Chu--Lin [1, Section 3.1] describe the standard Heisenberg Fock construction over
$\mathbb C$ and its mode bracket. The rational polynomial carrier, shifted indexing,
pointwise support argument, and the exact Mathlib `VertexOperator` realization above
are the claims proved here, not a claim that the cited complex setup supplies their
formal proof.
