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

## 3. Attained sharpness

**Theorem 3.1 (cyclic realization of the sharp coefficient shift).** There is a
pointwise lower-truncated formal field $A(z)=\sum_{m\in\mathbb Z}a_mz^{-m-1}$
on $V=\mathbb Q[X_0,X_1,\ldots]$ with vacuum $1$ such that
$$
[a_m,a_n]=\begin{cases}m\,\mathrm{id}_V,&m+n=0,\\0,&m+n\ne0,\end{cases}
\qquad
(\Delta^2 C_A)(m,n)=0,
\qquad
(\Delta C_A)(0,-1)=\mathrm{id}_V\ne0.
$$
Its negative modes generate every variable from the vacuum, and finite words
of negative modes applied to $1$ span $V$. Thus the order-two coefficientwise
locality of Theorem 2.1 is attained by a cyclic field and cannot be lowered to
order one.

**Proof.** For $k\ge0$ take $a_{k+1}=(k+1)\partial/\partial X_k$,
$a_{-(k+1)}$ to be multiplication by $X_k$, and $a_0=0$. These are the
rank-one charge-zero Heisenberg Fock formulas, specialized algebraically from
the complex construction of Chu--Lin [1, Section 3.1]. Each polynomial has
finite variable support, so sufficiently high positive modes annihilate it.
Multiplication operators commute with each other, as do partial derivatives;
the Leibniz rule gives the displayed mixed commutator. Also
$a_{-(k+1)}(1)=X_k$, and monomials are finite products of these negative modes
applied to $1$. Finally Theorem 2.1 with $K=\mathrm{id}_V$ yields the two
coefficient-shift identities. The endomorphism $\mathrm{id}_V$ is nonzero
because it sends the vacuum $1$ to $1\ne0$.
