# Simplex coverage spanning-polynomial Hessian

> Reference input, not a mathematical truth source. The atomizer is `generic-v1`; existing text is append-only. Lean declarations and their kernel-checked proof terms are the formal truth source.

## 1. Scope

The full coverage-depth optimizer concerns all finite fields, all dimensions at least two, and every full-rank generator of simplex length. Physical zero, repeated, and scalar-parallel columns are retained, and sampling is iid uniform with replacement. The matrix implication below is a necessary dependency of the contracted spanning-polynomial concavity route, not a separate open problem or a settlement of the optimizer.

## 2. Finite matrix implication

**Theorem 2.1 (connected nonnegative Hessian normalization).** Let $I$ be a finite nonempty set, $S$ a symmetric real $I$-by-$I$ matrix with nonnegative entries, and $v\in\mathbb R^I$ have strictly positive coordinates and satisfy $Sv=v$. Suppose the graph with edges $i\ne j$ and $S_{ij}>0$ is connected, allowing a singleton carrier. If $z^T S z\le z^T S^2 z$ for every real vector $z$, then $z^T S z\le0$ for every $z$ with $z^T v=0$.

**Proof.** For a nonzero eigenvector $w$ of eigenvalue $\lambda$, maximize $|w_i|/v_i$. Nonnegativity and $Sv=v$ give $|\lambda|\le1$. The quadratic hypothesis gives $\lambda\le\lambda^2$, so a positive eigenvalue is one. For a fixed vector $Sw=w$, maximize $w_i/v_i$. Every term $S_{ij}(c v_j-w_j)$ is nonnegative, and their sum is zero at a maximizing index. Hence every positive neighbor also maximizes. Connectedness forces the maximizing set to be the whole carrier, so $w=cv$. Expand a vector perpendicular to $v$ in an orthonormal eigenbasis. Its coefficients on eigenvalue-one vectors vanish; all remaining contributions to its quadratic form are nonpositive.

**Convention 2.2 (connectedness interface).** For the symmetric nonnegative matrix, connectedness is expressed by: every nonempty proper subset $A\subset I$ has $i\in A$, $j\notin A$ with $S_{ij}>0$. This is equivalent to connectedness of the positive off-diagonal graph. It includes zero entries and complete multipartite graphs, and is vacuous on a singleton.

## 3. Intended consumer and boundaries

The intended consumer is the induction for reciprocal-factorial represented spanning polynomials. Its normalized Hessian has the form $S=D^{1/2}HD^{1/2}$ on active coordinates. The induction must independently provide entrywise nonnegativity, connected positive support, the strictly positive fixed vector, and the quadratic inequality. No polynomial concavity, orbit averaging, sampling identity, stopping-time comparison, expectation inequality, or full optimizer settlement follows from this matrix implication alone.

## 4. Sources

Brändén and Huh, *Lorentzian polynomials*, arXiv:1902.03719v8, Sections 2 and 3, supplies the published concavity context. The displayed matrix argument is an ordinary finite-dimensional spectral/max-principle dependency. The pinned Mathlib matrix spectral theorem supplies the orthonormal eigenbasis; no general Lorentzian formal framework is asserted here.

## 追加锚（本行以下为增补区）

## 5. Represented coefficients and contraction

**Definition 5.1 (represented spanning polynomial).** For a finite represented index set $I$, columns $a_i$ in a vector space over a field, a subspace $U$, and $m\in\mathbb N$, put $R_U(\alpha)=U+\operatorname{span}\{a_i:\alpha_i>0\}$ and $c(\alpha)=\prod_{i\in I}(\alpha_i!)^{-1}\in\mathbb Q$. Define $F_{U,m}=\sum_{\sum_i\alpha_i=m,\ R_U(\alpha)=V}c(\alpha)X^\alpha$. Zero, repeated, and parallel represented columns remain distinct indices. The finite encoding by coordinates in $\operatorname{Fin}(m+1)$ is bijective with all natural exponent vectors of total $m$, because each coordinate is bounded by the total.

**Theorem 5.2 (exact coefficients and contraction).** At every natural exponent vector $\alpha$, the coefficient of $F_{U,m}$ is $c(\alpha)$ if $\sum_i\alpha_i=m$ and $R_U(\alpha)=V$, and zero otherwise. For each represented index $i$,

$$
\partial_i F_{U,m+1}=F_{U+\operatorname{span}\{a_i\},m}.
$$

**Proof.** Injectivity of the finite encoding gives the coefficient formula with exactly one summand at each admitted exponent. The support of $\alpha+e_i$ is the union of the support of $\alpha$ with $\{i\}$, including when $\alpha_i$ is already positive. Consequently $R_U(\alpha+e_i)=R_{U+\operatorname{span}\{a_i\}}(\alpha)$. Its total is $\sum_j\alpha_j+1$. Factorial successor and cancellation in $\mathbb Q$ give $(\alpha_i+1)c(\alpha+e_i)=c(\alpha)$. Coefficientwise polynomial differentiation now gives the asserted identity, including zero columns and every zero-polynomial case.

**Theorem 5.3 (homogeneity and Euler).** The actual polynomial $F_{U,m}$ is homogeneous of degree $m$, including when it is zero, and satisfies $\sum_{i\in I}X_i\partial_iF_{U,m}=mF_{U,m}$.

**Proof.** Every supported exponent has total $m$ by the exact coefficient formula. The weighted homogeneous Euler identity with all weights one applies to this polynomial.

**Boundary 5.4.** These algebraic identities do not establish the degree-two reverse quadratic inequality, active-coordinate connectedness, normalized-Hessian induction, root concavity, or the physical probability and expectation comparison. The full finite-field optimizer remains a separate obligation.

## 追加锚（本行以下为增补区）

## 6. Degree-two represented quadratic form

**Theorem 6.1 (actual degree-two rank classification).** Assume the column space $V$ is finite dimensional over its field $K$, with no finiteness assumption on $K$. Write $r=\dim_K(V/U)$ and $U_i=U+\operatorname{span}_K\{a_i\}$. The actual degree-two Hessian is constant in its evaluation point, with entry $H_{ij}=1$ precisely when $U_i+\operatorname{span}_K\{a_j\}=V$. For $r=0$ every entry is one. For $r=1$ only the loop-loop entries vanish, where a loop means $a_i\in U$. For $r=2$ an entry is one precisely when both indices are nonloops and $U_i\ne U_j$. For $r>2$ every entry is zero. These statements retain every represented index, including repeated columns and parallel columns. Finite-field coordinate spaces $K^{\operatorname{Fin}(k)}$ satisfy the finite-dimensional hypothesis.

**Proof.** Two contractions reduce each Hessian entry to the constant polynomial $F_{U_i+\operatorname{span}\{a_j\},0}$, hence give the indicator with coefficient one. Adjoining a column outside a subspace increases its dimension by exactly one. The quotient dimension identity then gives all four cases. In quotient dimension two, distinct one-column extensions have dimension $\dim U+1$; containment would force equality, whereas a column outside such an extension raises its dimension to $\dim V$. No pair spans a quotient of dimension greater than two.

**Theorem 6.2 (degree-two reverse quadratic bound).** For the actual represented polynomial $F=F_{U,2}$ in a finite-dimensional column space, every nonnegative real coordinate vector $x$ and every real vector $y$ satisfy

$$
2F(x)\,y^THy\ \le\ (g^Ty)^2,
\qquad g_i=(\partial_i F)(x),\qquad H_{ij}=(\partial_i\partial_j F)(x).
$$

**Proof.** For quotient dimension zero the quadratic form is $(\sum_i y_i)^2$. For dimension one it is $(\sum_i y_i)^2-(\sum_{a_i\in U}y_i)^2$. For dimension two it is $(\sum_{a_i\notin U}y_i)^2-\sum_C(\sum_{i\in C}y_i)^2$, where the finite classes are the fibers of $i\mapsto U_i$ on the represented nonloops. For larger quotient dimension the form vanishes. In each case choose the indicated first sum as $L(y)$; the quadratic form is nonpositive when $L(y)=0$.

The homogeneous Euler identities give $Hx=g$ and $x^THx=2F(x)\ge0$. If this value is zero, the asserted division-free bound is immediate. Otherwise, suppose $x^THy=0$ and $y^THy>0$. The vector $L(y)x-L(x)y$ belongs to the kernel of $L$, but its quadratic value is $L(y)^2x^THx+L(x)^2y^THy>0$, since positivity of $x^THx$ forces $L(x)\ne0$. This contradiction proves nonpositivity on the $H$-orthogonal complement of $x$. Applying it to $y-(x^THy)/(x^THx)x$ proves the bound. The argument uses no division by a degree-dependent $d-2$ and includes zero-polynomial families and empty carriers.

## 追加锚（本行以下为增补区）

## 7. Actual positive support

**Theorem 7.1 (positive evaluation and quotient rank).** Let the represented index set be finite and nonempty, let $V$ be finite dimensional, and suppose $U+\operatorname{span}\{a_i:i\in I\}=V$. At every strictly positive real coordinate vector $x$ and every degree $m$, the actual represented polynomial satisfies $F_{U,m}(x)\ge0$, and

$$
F_{U,m}(x)>0\quad\Longleftrightarrow\quad \dim_K(V/U)\le m.
$$

**Proof.** Every admitted coefficient is a product of strictly positive reciprocal factorials, so every monomial evaluates nonnegatively. For positivity, induct on degree using the actual contractions and the evaluated homogeneous Euler identity. At degree zero the constant polynomial is one exactly when $U=V$, equivalently when the quotient dimension is zero. At successor degree, positivity of the finite Euler sum is equivalent to positivity of at least one actual contracted derivative, because each $x_i$ is strictly positive. A loop leaves the quotient dimension unchanged and a nonloop lowers it by exactly one. If $U\ne V$, full represented spanning supplies a nonloop. If $U=V$, the nonempty index set supplies an index for padding. This proves both directions without replacing the polynomial or enumerating a positive finite surrogate.

**Theorem 7.2 (connected derivative-positive Hessian support).** Under the hypotheses of Theorem 7.1, let $d\ge2$ and define the actual active set by $A=\{i:(\partial_iF_{U,d})(x)>0\}$. For every nonempty proper subset $B\subset A$, there are $i\in B$ and $j\in A\setminus B$ with $(\partial_i\partial_jF_{U,d})(x)>0$. Empty active sets are included vacuously; no represented index or physical sampling mass is removed from the family.

**Proof.** Apply the positive-evaluation criterion to one and two actual contractions. If $r=\dim(V/U)\le d-2$, every Hessian entry is positive. If $r=d-1$, every coordinate is active and only loop-loop entries vanish. A nonloop exists by full spanning and joins any two loops. If $r=d$, the active coordinates are precisely the nonloops, and positive edges join distinct one-column extension subspaces. Two nonadjacent active coordinates have the same extension; full spanning supplies a column outside it, since its quotient codimension is $d-1\ge1$. This column joins both. If $r>d$, there are no active coordinates. Thus two active coordinates either have a positive edge or a common active positive neighbor; any cut is crossed by one of these edges. Activity is established from actual positive derivatives, not imposed by a nonloop definition.

## 追加锚（本行以下为增补区）

## 8. Exact zero-polynomial regimes

**Theorem 8.1 (rank obstruction and unspanned families).** For any finite represented index set in a finite-dimensional column space, the actual polynomial $F_{U,m}$ is identically zero if either $\dim_K(V/U)>m$ or $U+\operatorname{span}\{a_i:i\in I\}\ne V$. No nonempty-carrier or full-spanning assumption is imposed in this statement.

**Proof.** For the rank obstruction, induct on degree. At degree zero a positive quotient dimension excludes $U=V$. At successor degree, every one-column contraction has quotient dimension at least $\dim(V/U)-1$, so each contracted polynomial vanishes by induction. Euler then gives $(m+1)F_{U,m+1}=0$, and the nonzero rational scalar cancels. For an unspanned family, every represented support span is contained in the span of the entire represented family together with $U$, hence cannot be the whole space. The exact coefficient formula makes every coefficient zero. This includes empty carriers, repeated columns, loops, and all zero derivative-polynomial contractions satisfying these obstructions.

## 追加锚（本行以下为增补区）

## 9. Actual higher-degree reverse Hessian inequality

**Theorem 9.1 (represented reverse Hessian bound).** Let $K$ be any field, $V$ a finite-dimensional $K$-vector space, $I$ any finite physical index set, $a:I\to V$, and $U\le V$. For every integer $d\ge2$, every strictly positive real coordinate vector $x$, and every signed real vector $y$, put $f=F_{U,d}$, $g_i=(\partial_i f)(x)$, and $H_{ij}=(\partial_i\partial_j f)(x)$. Then

$$
d f(x)\sum_{i,j\in I}y_iH_{ij}y_j
\le (d-1)\left(\sum_{i\in I}g_i y_i\right)^2.
$$

Empty index sets, unspanned families, loops, repeated columns, and scalar-parallel columns are included. At degrees zero and one the Hessian vanishes; the same displayed inequality holds, with the degree-zero gradient also zero. There is no finite-field restriction on $K$, and no full-spanning premise in the conclusion.

**Proof.** Induct on degree with $U$ generalized. Homogeneity and Euler give $x\cdot g=df(x)$, $Hx=(d-1)g$, and $\sum_i x_iH_i=(d-2)H$, where $H_i$ is the Hessian of the actual contraction $F_{U+\operatorname{span}\{a_i\},d-1}$. The degree-two inequality is the quotient-rank classification bound. An unspanned family has zero polynomial. At zero evaluation the left side is zero and the right side nonnegative.

For $d\ge3$ and $f(x)>0$, let $A=\{i:g_i>0\}$. Euler makes $A$ nonempty. The exact positive-evaluation criterion and rank obstruction imply that every inactive contracted polynomial is identically zero, hence its Hessian row vanishes. For each active $i$, the induction hypothesis for its actual contraction gives $(d-1)g_i y^TH_i y\le(d-2)(Hy)_i^2$. Multiply by $x_i/((d-1)g_i)$ and sum. Third-derivative Euler and $d-2>0$ give $y^THy\le y^THDH y$, where $D_i=x_i/((d-1)g_i)>0$ on $A$.

Set $a_i=\sqrt{D_i}$, $S_{ij}=a_iH_{ij}a_j$, and $v_i=x_i/a_i$ on $A$. The actual contraction identities supply symmetry and nonnegative Hessian entries. Euler gives $Sv=v$; positive diagonal factors preserve the actual active-support cut connectivity. Substituting $y_i=a_i z_i$ into the preceding quadratic estimate proves $z^TSz\le z^TS^2z$. The connected normalization theorem therefore gives $y^THy\le0$ whenever $g\cdot y=0$, since $(y/a)\cdot v=(d-1)g\cdot y$.

Finally replace arbitrary $y$ by $y-(g\cdot y)/(df(x))\,x$. Euler makes this vector gradient-orthogonal, while $x^THx=d(d-1)f(x)$ and $x^THy=(d-1)g\cdot y$. Expanding its nonpositive quadratic form and multiplying by the positive denominator yields the displayed division-free inequality. This polynomial statement alone asserts neither analytic root concavity nor a sampling or expected-time optimizer.

## 追加锚（本行以下为增补区）
