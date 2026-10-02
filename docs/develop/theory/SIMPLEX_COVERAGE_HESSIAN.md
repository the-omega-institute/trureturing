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

## 10. Analytic identification and closed-orthant root concavity

**Theorem 10.1 (analytic line derivatives).** For every finite index set $I$, rational multivariate polynomial $f$, and real coordinate vectors $x,y$, define $z(t)_i=x_i+t y_i$ and $A(t)=f(z(t))$ using the coefficient homomorphism $\mathbb Q\to\mathbb R$. Then $A'(t)=\sum_i y_i(\partial_i f)(z(t))$. The derivative of this displayed first derivative is $\sum_j\sum_i y_j y_i(\partial_i\partial_j f)(z(t))$. In particular, for the actual represented spanning polynomial it equals $y^TH(z(t))y$, with the formal Hessian orientation of Theorem 9.1 and no mixed-partial interchange assumption.

**Proof.** Structural polynomial induction treats constants, addition, and multiplication by one variable. The last case is the ordinary product rule; the formal product rule and the Kronecker delta for the derivative of a variable identify the same finite sum. Apply this result to each $\partial_j f$ and use the finite-sum derivative rule. Interchange finite sums and commute real scalar factors to identify the quadratic form. No nonempty-index assumption is used.

**Theorem 10.2 (actual root concavity on the entire nonnegative orthant).** Let $K$ be any field, $V$ any finite-dimensional $K$-vector space, $I$ any finite physical index set, $a:I\to V$, $U\le V$, and $d\ge1$. Then $x\mapsto F_{U,d}(x)^{1/d}$, with the nonnegative real root, is concave on $\{x\in\mathbb R^I:\forall i,\ x_i\ge0\}$. All universes are independent. The statement has no full-spanning, nonempty-index, positive-evaluation, Hessian, derivative, or concavity premise. Zero, repeated, and scalar-parallel columns are retained.

**Proof.** The zero-polynomial branch is constant. Empty $I$ forces every natural exponent vector to be zero, so the exact coefficient formula makes every positive-degree polynomial zero. For nonempty $I$, the rank obstruction and unspanned-family theorem give the zero branch unless the family spans and $\dim(V/U)\le d$. The exact positivity theorem then gives strictly positive evaluation throughout the positive orthant. Put $p=1/d$. Along any segment there, Theorem 10.1 and the real-power derivative rule give the second derivative
$$p A^{p-2}\bigl(A A''+(p-1)(A')^2\bigr).$$
Theorem 9.1 implies that the parenthesis is nonpositive, since multiplying it by $d>0$ gives $d A A''-(d-1)(A')^2$. The prefactor is positive. The line function is continuous at both endpoints and twice differentiable in the open segment, hence concave on the closed unit interval. This includes degree one. For arbitrary nonnegative endpoints, add the same strictly positive constant to every coordinate, apply the positive-orthant inequality, and let this constant decrease to zero. Polynomial evaluation is globally continuous, as is the real $p$-power for $p>0$, so the Jensen inequality survives the limit. No fractional root is differentiated at zero.

**Boundary 10.3.** Analytic root concavity is a dependency of the full named simplex optimizer, not its settlement. The actual all-horizon iid physical sampling identities, probability comparison, and expected-time comparison remain separate obligations.

**Theorem 10.4 (finite-quotient scope).** Theorem 10.2 holds for an arbitrary $K$-vector space $V$ whenever $V/U$ is finite dimensional; finite dimensionality of $V$ itself is unnecessary. The same physical index set, original columns, subspace $U$, all degrees $d\ge1$, and entire nonnegative orthant are retained.

**Proof.** Keep every index and replace only its represented vector by its image in $V/U$. For each exponent vector, its original support spans together with $U$ if and only if its quotient support spans $V/U$, by the quotient map's span and top-image identities. The exact coefficient formula therefore identifies the original spanning polynomial with the actual quotient spanning polynomial over the same variables and rational coefficients. Their analytic evaluations and formal derivatives are identical. Apply the actual reverse-Hessian induction and positivity suppliers in the finite-dimensional quotient, and carry out the analytic line and boundary argument of Theorem 10.2 for this common polynomial.

## 11. Spanning-filtered physical words and actual sampling

**Definition 11.1 (physical word polynomial).** Let $K$ be any field, $V$ any $K$-vector space, $I$ any finite physical index set, $a:I\to V$, and $U\le V$. For every $t\in\mathbb N$, define the rational polynomial

$$
W_{U,t}=\sum_{w:\operatorname{Fin}(t)\to I}
\mathbf1_{\{U+\operatorname{span}\{a_{w(j)}:j<t\}=V\}}
\prod_{j<t}X_{w(j)}.
$$

The indicator is implemented by selecting the monomial or zero, not by replacing the represented spanning polynomial. All physical indices remain distinct, including zero, repeated, and scalar-parallel columns. Neither finite dimensionality nor a spanning assumption is imposed; the index set may be empty.

**Theorem 11.2 (exact first-coordinate recurrence and normalization).** For all such data and every $t\ge0$,

$$
W_{U,0}=\begin{cases}1&U=V,\\0&U\ne V,\end{cases}
\qquad
W_{U,t+1}=\sum_{i\in I}X_i W_{U+\operatorname{span}\{a_i\},t},
\qquad
W_{U,t}=t!F_{U,t}.
$$

The last equation is an identity in $\mathbb Q[X_i:i\in I]$ for the existing exact reciprocal-factorial polynomial of Definition 5.1. It therefore holds under every rational-algebra evaluation, without a nonnegativity or probability assumption.

**Proof.** There is a unique length-zero word; its sampled span is zero and its product is one. The equivalence between a length-$(t+1)$ word and its first index together with its length-$t$ tail preserves both the product and the span: the range of the represented word is the union of the first singleton and the represented tail range. The span of this union is the join of their spans. Reindexing the finite sum through this equivalence and distributing multiplication proves the recurrence, also for an empty alphabet. The degree-zero coefficient formula for $F$ gives the same indicator. In degree $t+1$, homogeneity and Euler give $\sum_i X_i\partial_i F_{U,t+1}=(t+1)F_{U,t+1}$, and exact contraction gives $\partial_iF_{U,t+1}=F_{U+\operatorname{span}\{a_i\},t}$. Induction in the recurrence, with $(t+1)t!=(t+1)!$, proves normalization. No histogram counting or unfiltered multinomial identity is substituted for the spanning condition.

**Theorem 11.3 (actual uniform physical recovery probability).** Assume additionally that $I$ is nonempty, has a measurable space with measurable singletons, and sampling has exactly the measure `MinimumRetrievalTime.uniformSamples I`. Write $N=|I|$ and $x_i=1/N\in\mathbb R$. For every $t\ge0$, the actual event `MinimumRetrievalTime.recovered a top t` satisfies

$$
\Pr(\operatorname{recovered}(a,V,t))
=\operatorname{ofReal}\bigl(W_{0,t}(x)\bigr)
=\operatorname{ofReal}\bigl(t!F_{0,t}(x)\bigr).
$$

This uses the original physical alphabet, not a projective pushforward, and imposes no full-spanning or finite-dimensional hypothesis. It includes zero ambient space, degree zero, and unspanned families. Nonemptiness is necessary for the specified uniform distribution and is not required by Theorem 11.2.

**Proof.** Partition the event by its finite prefix words. Each word cylinder specifies precisely the first $t$ coordinates; distinct words give disjoint measurable cylinders. The finite-cylinder formula for the existing infinite product measure gives each cylinder measure $(N^{-1})^t$, including the empty prefix. A prefix is admitted exactly when its represented span is top, since recovery of top is the inclusion of top in the actual prefix span. Finite additivity over the admitted words gives the spanning-filtered word sum. Evaluating each monomial at the common nonnegative coordinate $1/N$ gives the same cylinder weight. The map `ENNReal.ofReal` preserves these finite sums and products because every evaluated summand is nonnegative. Theorem 11.2 gives the second identity.

**Boundary 11.4.** These all-horizon identities are dependencies, not a settlement of the named optimizer. Projective transport, orbit averaging, zero-column replacement, the all-horizon probability comparison, and its transfer to the original actual expected retrieval time remain separate obligations. The existing `retrieval_time_probability_bridge` supplies the tail and expectation transfer once the appropriate full-spanning hypothesis and probability comparison have been proved.

## 追加锚（本行以下为增补区）

## 12. Projective averaging and physical fiber weights

**Theorem 12.1 (all-horizon represented projective maximum).** Let $K$ be any finite field, $k\ge2$, $V=K^k$, and $P=\mathbb P(K,V)$ with every ray retained. Choose a nonzero representative $a_p$ of each ray $p$. For every natural horizon $t$ and every real vector $x:P\to\mathbb R$ with $x_p\ge0$ and $\sum_p x_p=1$, the actual reciprocal-factorial polynomial of Definition 5.1 satisfies

$$
F_{0,t}(x)\le F_{0,t}\bigl((1/|P|)_{p\in P}\bigr).
$$

**Proof.** Replacing a representative by a nonzero scalar multiple does not change the span of any selected word, including words whose probability is zero. A linear automorphism maps a selected span to the span of the transformed representatives and preserves the condition that it is the whole space. Reindexing words therefore preserves the evaluated spanning-filtered word polynomial and, by Theorem 11.2 and cancellation of $t!$, the exact polynomial $F_{0,t}$. For the finite linear general linear group $G$, form $A(x)_p=|G|^{-1}\sum_g x_{g^{-1}p}$. Finite reindexing preserves mass and makes this average invariant; pretransitivity makes it constant, and its mass identifies it as $1/|P|$. For $t>0$, apply the closed nonnegative orthant root concavity of Theorem 10.2 and finite Jensen to these actual permuted vectors. Nonnegative coefficients give nonnegative evaluations, so the positive exponent $1/t$ converts the root inequality to the stated polynomial inequality even when either value is zero. At $t=0$ the word polynomial is independent of the weights. No lower bound on $t$ in terms of $k$ is used.

**Theorem 12.2 (physical iid comparison without zero columns).** In the same field and dimension, let $I$ be any nonempty finite physical alphabet and let $b:I\to V$ have no zero column. Distinct physical indices may have equal or scalar-parallel columns. For every $t\ge0$, the actual uniform iid recovery probability of $b$ is at most that of one representative of every projective ray, sampled uniformly. The physical fiber weights are

$$
x_p=\frac{|\{i\in I:[b_i]=p\}|}{|I|}.
$$

**Proof.** For arbitrary nonnegative physical weights $y_i$, group the spanning-filtered length-$t$ word sum by its coordinatewise ray image. The image word spans exactly when the physical word spans. Distributing the product of the fiber sums gives its weight as the sum of the weights of all physical words in that fiber. Thus the actual physical word polynomial evaluates to the projective word polynomial at $x_p=\sum_{[b_i]=p}y_i$, without conditioning, renormalization or removal of a physical index. Use $y_i=1/|I|$, finite reindexing for total mass, Theorem 12.1 and the exact factorial identity. Theorem 11.3 transfers both sides to the original infinite iid sample measures and recovery events.

**Boundary 12.3 (local deductions).** Sections 12.1–12.2 are routine deductions used locally inside the full optimizer proof, not independently retained formal declarations. They concern the exact represented polynomial and the original uniform physical-coordinate law at every horizon. The nonzero-column comparison alone is not the named full settlement: original zero columns require a same-index replacement coupling, followed by all-horizon tail comparison and the existing actual integrability and expectation bridge. No new expectation definition, generic orbit surrogate, GL-invariance premise or concavity premise replaces those obligations. The finite group, projectivization action, pretransitivity and finite Jensen are supplied by pinned Mathlib; the projective invariant polynomial and physical fiber transport are composite deductions, not separately assumed suppliers.

## 13. Original physical simplex optimizer

**Theorem 13.1 (Bertuzzo–Ravagnani–Yaakobi simplex optimality).** Let $K$ be any finite field of cardinality $q$, let $k\ge2$, and put $n=(q^k-1)/(q-1)$. For every rank-$k$ matrix $G\in K^{k\times n}$, and every matrix $S\in K^{k\times n}$ whose columns are exactly one nonzero representative of each projective line in $K^k$, let $X_0,X_1,\ldots$ be iid uniform physical positions in $\operatorname{Fin}(n)$. Write $T_C=\min\{t:\operatorname{span}_K(C_{X_0},\ldots,C_{X_{t-1}})=K^k\}$. Then

$$
\mathbb E[T_S]\le\mathbb E[T_G].
$$

**Source and scope.** The assertion is arXiv:2603.06489v1, Section 3, Conjecture 3.2 (Problem B), with its predecessor in arXiv:2507.20639v1, Section III, the unnumbered simplex-optimizer paragraph. All zero, repeated and scalar-parallel competitor columns retain their original physical positions. No uniqueness, restricted-field, conditioned-sampling, rank-deficient or projective-only conclusion is asserted. The known simplex closed-form expectation is literature context, not another conclusion here.

**Proof.** Put $V=K^k$ and $P=\mathbb P(K,V)$. The projective cardinality formula gives $|P|=(q^k-1)/(q-1)=n>0$. Fix $v_0\ne0$ and define $G'_i=v_0$ when $G_i=0$, and $G'_i=G_i$ otherwise. All $G'_i$ are nonzero. For every physical sample sequence and natural horizon $t$,

$$
\operatorname{span}_K\{G_{X_j}:j<t\}
\subseteq\operatorname{span}_K\{G'_{X_j}:j<t\}.
$$

Indeed each old generator is either zero, which lies in every subspace, or an unchanged new generator. This is subspace containment, not a claim that the old set of vector values is contained in the new set. The same argument over all positions shows that $G'$ spans $V$, since matrix rank $k$ identifies the old column span with $V$.

Let $e:\operatorname{Fin}(n)\to P$ be the bijection $i\mapsto[S_i]$, and choose $a_p=S_{e^{-1}(p)}$. These representatives span $V$: a nonzero vector $v$ belongs to the singleton span of $a_{[v]}$, because that singleton span is the line of $v$; zero belongs automatically. Thus $S$ also spans $V$. For every $p\in P$, the physical fiber of $S$ contains exactly one position, so its uniform ray weight is $1/n=1/|P|$. The physical word identity of Section 12.2, applied to this actual bijection, therefore identifies uniform projective recovery with uniform physical simplex recovery. It does not require scalar representative choices to be equivariant.

On the original physical sample space, prefix containment and Sections 12.1–12.2 give, for every $t\in\mathbb N$,

$$
\Pr(T_G\le t)\le\Pr(T_{G'}\le t)\le\Pr(T_S\le t).
$$

Each recovery event is measurable: it is the inverse image of the set of spanning length-$t$ words under the measurable prefix map, and that finite word space has measurable singletons. Complementing under probability-one measures gives

$$
\Pr(T_S>t)\le\Pr(T_G>t).
$$

These statements include the empty prefix and every horizon below $k$; no positive recovery probability at a particular horizon is assumed. For either full-span generator $C=G,S$, uniform iid sampling has finite expectation: failure by time $t$ implies that at least one of the $n$ positions has not appeared, so its probability is at most $n(1-1/n)^t$. Summation gives finiteness. The nonnegative stopping time satisfies the exact tail identity

$$
\mathbb E[T_C]=\sum_{t=0}^{\infty}\Pr(T_C>t).
$$

Comparing the nonnegative extended-real sums first gives the claimed order. Their finiteness makes conversion to the ordinary real expectations order-preserving and gives integrability of both stopping times. This proves the assertion for the original physical sampling law without deleting, conditioning away or renormalizing any position. All projective averaging and physical transport deductions are local steps of this argument.
