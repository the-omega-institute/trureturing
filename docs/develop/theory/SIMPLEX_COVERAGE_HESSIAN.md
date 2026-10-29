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
## 14. Strict full-recovery comparison at each finite deadline

**Definition 14.1 (physical model and projective word evaluation).** Let $K$ be a finite field of cardinality $q$, let $k\ge3$, and put

$$
V=K^k,\qquad P=\mathbb P(K,V),\qquad N=|P|=\frac{q^k-1}{q-1},\qquad I=\operatorname{Fin}(N).
$$

Let $G\in K^{k\times N}$ have rank $k$, and let $S\in K^{k\times N}$ have exactly one nonzero representative of each ray in $P$. Each draw $X_j$ is uniform on the physical positions $I$, independently and with replacement. For $C=G,S$, set

$$
T_C=\min\bigl\{t\in\mathbb N:\operatorname{span}_K\{C_{X_j}:0\le j<t\}=V\bigr\},
\qquad R_C(t)=\Pr(T_C\le t),
$$

with minimum $+\infty$ if the set is empty. The empty prefix has span zero. Zero columns, repeated columns and scalar-parallel columns remain separate physical positions.

Choose representatives $a_p\in p\setminus\{0\}$ for all $p\in P$, write $u_p=1/N$, and let

$$
\Delta=\bigl\{x\in\mathbb R^P:x_p\ge0\text{ for all }p,\ \sum_{p\in P}x_p=1\bigr\},
\qquad Q_t(x)=W_{0,t}(x)=t!F_{0,t}(x),
$$

where $W$ and $F$ are the actual represented polynomials of Definitions 11.1 and 5.1 for the columns $a_p$. Thus $Q_t$ denotes their real evaluation, and is a polynomial on all of $\mathbb R^P$. If $C$ has no zero column, its physical ray weights are

$$
x_p(C)=\frac{|\{i\in I:[C_i]=p\}|}{N}.
$$

The exact word normalization and physical fiber transport in Sections 11–13 identify $R_C(t)=Q_t(x(C))$ and $R_S(t)=Q_t(u)$. These identities concern the specified physical sampling law.

**Theorem 14.2 (equality at every attainable finite deadline).** For every field, dimension and pair of physical matrices in Definition 14.1, and for every integer $t\ge k$,

$$
R_G(t)=R_S(t)
\quad\Longleftrightarrow\quad
\bigl(G_i\ne0\text{ for every }i\in I\bigr)
\ \text{and}\ \bigl(i\mapsto[G_i]\text{ is a bijection }I\to P\bigr).
$$

Every other such rank-$k$ matrix satisfies $R_G(t)<R_S(t)$ for every integer $t\ge k$. Both probabilities are zero for $0\le t<k$, and every $t\ge k$ has positive recovery probability for both matrices. Column permutation, multiplication of individual columns by nonzero scalars, and invertible row-basis transformations preserve the equality criterion and each recovery-time distribution. This classifies equality in the all-horizon recovery comparison used in the proof of Theorem 13.1.

**Proof.** Fix an arbitrary $t\ge k$. Sections 12–13 already give the weak comparison at every horizon, including original zero columns. We use that comparison without repeating its averaging proof. By Theorem 10.2 and the positive constant factor $(t!)^{1/t}$, $x\mapsto Q_t(x)^{1/t}$ is concave on the entire nonnegative orthant. The nonnegative root is used throughout. A basis of $V$, followed by repetitions of one of its rays if $t>k$, supplies a positive summand at $u$, so $Q_t(u)>0$.

We first determine a strict curvature property at $u$. An invertible linear map preserves the spanning condition on words; replacing any representative by a nonzero multiple preserves it as well. Therefore the word polynomial is invariant under the coordinate permutations induced by $\operatorname{GL}(V)$, as in the proof of Theorem 12.1. This group is transitive on ordered pairs of distinct rays: choose independent representatives of the first pair, extend to a basis, do the same for the second pair, and map the first basis to the second. Since $u$ is fixed by all these permutations, differentiating the polynomial invariance shows that all entries of $\nabla Q_t(u)$ are equal, and that there are real numbers $A_t,B_t$ such that

$$
\partial_p^2Q_t(u)=A_t\quad(p\in P),
\qquad \partial_p\partial_rQ_t(u)=B_t\quad(p\ne r).
$$

For a word $w\in P^{t-2}$ write $L(w)=\operatorname{span}_K\{a_{w(j)}:0\le j<t-2\}$. Direct differentiation of the word sum, marking an ordered pair of distinct positions in a length-$t$ word, gives, for distinct $p,r$,

$$
\begin{aligned}
\partial_p^2Q_t(u)
&=t(t-1)N^{-(t-2)}
  \sum_{w\in P^{t-2}}\mathbf1_{\{L(w)+p=V\}},\\
\partial_p\partial_rQ_t(u)
&=t(t-1)N^{-(t-2)}
  \sum_{w\in P^{t-2}}\mathbf1_{\{L(w)+p+r=V\}}.
\end{aligned}
$$

Here $p,r$ themselves denote their one-dimensional subspaces. To justify the common factor, after marking the ordered positions their letters are fixed to $p,p$ or $p,r$; the remaining letters form $w$, and their evaluated product is $N^{-(t-2)}$. There are $t(t-1)$ choices of marked positions. This counts repeated occurrences with their derivative multiplicities, including the diagonal second derivative. Since $L(w)+p\subseteq L(w)+p+r$, subtracting gives

$$
B_t-A_t=t(t-1)N^{-(t-2)}
\bigl|\{w\in P^{t-2}:L(w)+p\ne V,\ L(w)+p+r=V\}\bigr|>0.
$$

For the strict inequality, extend $a_p,a_r$ to a basis $a_p,a_r,b_1,\ldots,b_{k-2}$ of $V$. The complement $D=\operatorname{span}_K\{b_1,\ldots,b_{k-2}\}$ has dimension $k-2\ge1$. Take a word containing once each ray $[b_1],\ldots,[b_{k-2}]$, and fill its remaining $t-k$ positions with $[b_1]$. It has exactly length $t-2$ and span $D$. Thus $L(w)+p$ has dimension $k-1$, whereas $L(w)+p+r=V$. This one word proves positivity for every $t\ge k$, including $t=k$, over every finite field.

Consequently, for every nonzero $h\in\mathbb R^P$ with $\sum_p h_p=0$,

$$
\begin{aligned}
\nabla Q_t(u)\cdot h&=0,\\
h^T\nabla^2Q_t(u)h
&=A_t\sum_p h_p^2+B_t\sum_{p\ne r}h_ph_r
=(A_t-B_t)\sum_p h_p^2<0.
\end{aligned}
$$

Let $x\in\Delta$ with $x\ne u$, allowing zero coordinates, and put $h=x-u$. Since $u$ is strictly positive, $u+sh$ lies in the positive orthant for all real $s$ in some neighborhood of zero. By continuity $Q_t(u+sh)>0$ on a possibly smaller neighborhood. Hence

$$
\psi(s)=Q_t(u+sh)^{1/t}
$$

is twice continuously differentiable there, with

$$
\psi'(0)=0,\qquad
\psi''(0)=\frac1t Q_t(u)^{1/t-1}(A_t-B_t)\sum_p h_p^2<0.
$$

Taylor's formula gives $\psi(s)=\psi(0)+\tfrac12\psi''(0)s^2+o(s^2)<\psi(0)$ for all sufficiently small positive $s$. If $Q_t(x)=Q_t(u)$, concavity on the closed segment from $u$ to $x$ would instead give

$$
\psi(s)\ge(1-s)Q_t(u)^{1/t}+sQ_t(x)^{1/t}=\psi(0)
\qquad(0\le s\le1),
$$

a contradiction. The already supplied weak maximum $Q_t(x)\le Q_t(u)$ from Theorem 12.1 is therefore strict for every $x\in\Delta\setminus\{u\}$. The argument includes boundary weights without differentiating a root at a zero evaluation.

Suppose first that every column of $G$ is nonzero. Physical fiber transport gives $R_G(t)=Q_t(x(G))$. The preceding strictness says that equality with $R_S(t)=Q_t(u)$ holds exactly when $x_p(G)=1/N$ for every $p$. Each fiber size is a nonnegative integer and there are exactly $N$ positions and $N$ rays, so this means each fiber has exactly one member, precisely the asserted bijection. Conversely, this bijection gives $x(G)=u$ and equality at every horizon, independently of the representative scalings.

Now suppose that $G$ has at least one zero column. Rank $k$ supplies an original nonzero column $G_j$. On the same physical alphabet define

$$
G'_i=\begin{cases}G_j,&G_i=0,\\G_i,&G_i\ne0.\end{cases}
$$

Every column of $G'$ is nonzero, its column span contains that of $G$, and its fiber at $[G_j]$ has at least two positions. Hence $G'$ still has rank $k$ and $x(G')\ne u$. For every original sample sequence, at every horizon, each old sampled generator is zero or is an unchanged new generator. Therefore

$$
\operatorname{span}_K\{G_{X_\ell}:\ell<t\}
\subseteq\operatorname{span}_K\{G'_{X_\ell}:\ell<t\},
\qquad
R_G(t)\le R_{G'}(t)=Q_t(x(G'))<Q_t(u)=R_S(t).
$$

All draws still take place at their original uniform physical positions. The inequality compares two generators on that same probability space; it does not condition away any draw or identify physical positions.

For $t<k$, the span of $t$ columns has dimension at most $t$, so both recovery events are empty. For any $t\ge k$, rank $k$ supplies $k$ physical basis columns of $G$; the analogous basis exists among the simplex columns. Sampling those $k$ positions in a fixed order and then repeating the first position gives a spanning word of length $t$ and probability $N^{-t}>0$ for either generator. Thus all and only the deadlines $t\ge k$ are attainable.

Finally, a nonzero scaling of each column preserves every sampled span. An invertible row transformation maps each sampled span isomorphically onto the transformed span, preserving full recovery, zeros and the bijectivity of the ray map. A column permutation is a bijection of physical positions and induces a measure-preserving relabeling of the iid uniform sample sequences. It preserves the distribution of $T_C$, and permutes the fibers of the ray map without changing their sizes. These operations therefore preserve both the criterion and all the asserted comparisons. $\square$

The original physical model is that of Bertuzzo–Ravagnani–Yaakobi, [*The DNA Coverage Depth Problem: Duality, Weight Distributions, and Applications*, arXiv:2603.06489v1](https://arxiv.org/html/2603.06489v1), Section 2, Problems A and B; Section 3, Conjecture 3.2 concerns the expected-time optimizer of Theorem 13.1. Their predecessor [arXiv:2507.20639v1](https://arxiv.org/html/2507.20639v1), Section III, Example 1 already reports expected uniqueness for binary $[7,3]$ codes, with simplex expectation $47/12$ and nonsimplex expectation at least $17/4$. That expected-time computation is overlap, rather than a consequence first asserted here.

For the expected-time comparison, Kong–Elishco–Wang–Duman, [*The Coverage Depth Problem in Distributed DNA Data Storage*, arXiv:2610.02931v1](https://arxiv.org/pdf/2610.02931v1), Corollary II.4 (pp. 6–7), Lemma IV.2 (pp. 18–19), and Theorem IV.3 with its equality proof (pp. 19–20) already supply minimization and uniqueness for every nonnegative projective probability law, including laws with zero ray weights, for $k\ge2$; Corollary IV.4 also supplies a quantitative expected gap. In their notation $\pi_p=x_p(C)$ and $\pi(U)=\sum_{p\subseteq U}x_p(C)$ for a nonzero physical generator $C$, by the exact physical fiber identity above. Their standing physical model on p. 4 excludes zero columns but retains repetitions and nonzero scalar multiples with multiplicity. For an original $G$ with zeros, the same-index $G'$ just constructed is an actual nonzero generator with those exact fiber weights; the samplewise containment also gives $T_G\ge T_{G'}$. Thus invoking their expected-time result on $G'$ is a faithful comparison with the original law, and does not assert that $G$ itself has a probability law on $P$. Expected uniqueness and its quantitative form are supplied results, not additional numbered conclusions of this section.

The finite-deadline equality criterion uses the strict difference $B_t-A_t$ and its propagation from $u$ to every boundary point along a concave root segment. The root concavity itself is Theorem 10.2; the non-strict concavity context in Brändén–Huh, [*Lorentzian polynomials*, arXiv:1902.03719v8](https://arxiv.org/abs/1902.03719v8), Sections 2–3, supplies no strictness premise here. A strict expected-time inequality alone does not imply strictness at each prescribed deadline. Theorem 14.2 concerns only exact full-span recovery, length $N$, rank $k$ and iid uniform physical-position sampling with replacement. Its proof asserts no stability estimate or rate of separation, and no priority claim concerning other finite-deadline comparisons.

## 追加锚（本行以下为增补区）

## 15. Projective word counts and the single-defect value

**Definition 15.1 (word counts and physical multiplicities).** Fix a finite field $K$ of cardinality $q$ and an integer $k\ge3$. Retain $V=K^k$, $P=\mathbb P(K,V)$, $N=[k]_q=(q^k-1)/(q-1)$, the $N$ original labelled positions $I$, and the iid uniform sampling with replacement of Definition 14.1. For a rank-$k$ matrix $G\in K^{k\times N}$, let $z(G)$ count its zero columns and put

$$
n_p(G)=|\{i\in I:G_i\ne0,\ [G_i]=p\}|,
\qquad z(G)+\sum_{p\in P}n_p(G)=N.
$$

Every occurrence at a physical position is counted, including equal vectors and nonzero scalar multiples. Write $S_t=R_S(t)$ for the simplex recovery probability.

For integers $d,v\ge0$, let $C(d,v)$ be the number of ordered length-$v$ words over the rays of $K^d$ whose representatives span $K^d$. For $d\ge1$, let $E(d,v)$ be the number of these spanning words avoiding one specified ray. Linear isomorphisms show independence of the specified ray and of the nonzero representatives. The empty word has span zero, and the ray alphabet of $K^0$ is empty. In particular,

$$
\begin{gathered}
C(0,0)=1,\qquad C(0,v)=0\ (v>0),\\
C(d,0)=E(d,0)=0\ (d\ge1),\qquad C(d,v)=E(d,v)=0\ (v<d),\\
C(1,v)=1\ (v\ge1),\qquad E(1,v)=0\ (v\ge0).
\end{gathered}
$$

As a formal dimension-zero convention set $E(0,v)=C(0,v)$; no specified ray is asserted to exist in dimension zero. Put $[0]_q=0$ and $0^0=1$.

The classical subspace Möbius identity gives an explicit evaluation of these counts. With Gaussian coefficients outside $0\le j\le d$ set to zero, put

$$
\mu_{d,j}=(-1)^{d-j}q^{\binom{d-j}{2}},\qquad
b_{d,j}=\begin{cases}{d-1\brack j-1}_q,&j\ge1,\\0,&j=0.\end{cases}
$$

For $d\ge1$ the evaluations are

$$
\begin{aligned}
C(d,v)&=\sum_{j=0}^{d}{d\brack j}_q\mu_{d,j}[j]_q^v,\\
E(d,v)&=\sum_{j=0}^{d}\left({d\brack j}_q-b_{d,j}\right)\mu_{d,j}[j]_q^v
       +\sum_{j=1}^{d}b_{d,j}\mu_{d,j}([j]_q-1)^v.
\end{aligned}
$$

Indeed, the indicator that a word spans is the sum of $\mu_{d,\dim U}$ over subspaces $U$ containing its span. A $j$-space contains $[j]_q$ rays; exactly $b_{d,j}$ such subspaces contain the forbidden ray, and their allowed alphabet has $[j]_q-1$ letters. This is the subspace-Möbius supplier in Kong–Elishco–Wang–Duman, [arXiv:2610.02931v1](https://arxiv.org/pdf/2610.02931v1), Lemma II.2 and Theorem II.3, specialized to one container. Its physical parameters are $M=1$, $n_1=N$, $\rho_U=N^{-1}\sum_{p\subseteq U}n_p(G)$ when $z(G)=0$, and round count equal to draw count. The displayed counting identity itself applies to the stated finite alphabets, including the empty word. The exact word and fiber identities of Sections 11–12 give

$$
S_t=\frac{C(k,t)}{N^t},\qquad
R_G(t)=\frac{Q_t(n(G))}{N^t}\quad\text{if }z(G)=0,
$$

where $Q_t=W_{0,t}=t!F_{0,t}$ uses one representative of every ray and is evaluated at the unnormalized multiplicities in the second formula.

**Theorem 15.2 (exact single-defect deficit).** Let $a,b\in P$ be distinct and let $H$ have no zero column and multiplicities

$$
y^{a,b}=\mathbf1-e_a+e_b.
$$

For every integer $t\ge k$,

$$
R_H(t)=S_t-D_t,
$$

where

$$
D_t=\frac1{N^t}\sum_{m=2}^{t}\binom tm
\left[q^{k-2}E(k-1,t-m)+q^{2(k-2)}C(k-2,t-m)\right](2^m-2)>0.
$$

The matrix $H$ has rank $k$, and this value is independent of $a,b$, of the label assignment, and of all nonzero representatives.

**Proof.** The rays other than $a$ span $V$: a proper subspace has at most $[k-1]_q$ rays, whereas $N-1>[k-1]_q$. Thus $H$ has rank $k$. Count physical spanning words by first specifying the $m$ positions whose ray is in $\{a,b\}$, and then a word $w$ of length $v=t-m$ over $P\setminus\{a,b\}$. Every other ray occurs at one physical position in both matrices. In the simplex, these $m$ positions have the $2^m$ assignments of $a,b$. In $H$, they have $2^m$ physical assignments, all on ray $b$. Let $L$ be the span of $w$.

For $m=0$ the two word counts agree directly. Assume $m\ge1$ for the following cases. If $L=V$, or if each of $L+a$ and $L+b$ is $V$, the spanning-word counts agree. If $L+a=V$ but $L+b\ne V$, the simplex contributes $2^m-1$ and $H$ contributes zero. Interchanging $a,b$ is an invertible linear transformation preserving the remaining alphabet, so the number of such residual words equals the number with $L+b=V$ but $L+a\ne V$; in the latter case the contributions are $2^m-1$ and $2^m$. Together these two equally numerous classes contribute $(2^m-2)$ times the size of the first class. If neither single ray completes $L$ but both together do, the contributions are $2^m-2$ and zero. If even both together do not complete $L$, both contributions vanish. For $m=1$ the total difference is zero by the same pairing, and only $m\ge2$ remains.

For the first residual class, $L$ is a hyperplane containing $b$ and not $a$. There are exactly $q^{k-2}$ such hyperplanes: in $V/b$, subtract the hyperplanes containing the nonzero image of $a$ from all hyperplanes, giving $[k-1]_q-[k-2]_q=q^{k-2}$. For each such $L$, the residual word must span $L$ and avoid $b$, giving $E(k-1,v)$ words. Hence this class has size $q^{k-2}E(k-1,v)$.

In the class where both rays are necessary, $\dim L=k-2$ and $L\cap(a+b)=0$. Conversely every such complement has precisely the required completion properties. Fixing one complement to $a+b$, all other complements are graphs of linear maps from a $(k-2)$-space to a $2$-space, so there are $q^{2(k-2)}$. Each has $C(k-2,v)$ spanning words and contains neither $a$ nor $b$. This class therefore has size $q^{2(k-2)}C(k-2,v)$. Multiplying by $\binom tm$, summing, and dividing by the unchanged physical word count $N^t$ proves the formula.

For $m=2$, $v=t-2\ge k-2\ge1$. A basis word of $K^{k-2}$ padded by repetitions of a basis ray proves $C(k-2,v)>0$; also $2^2-2>0$. All summands are nonnegative, so $D_t>0$. The count uses only spans and physical fiber sizes, proving all asserted invariances. $\square$

## 16. The unrestricted finite-deadline runner-up

**Theorem 16.1 (sharp comparison on the original alphabet).** For every finite field $K$ of cardinality $q$, every integer $k\ge3$, every integer $t\ge k$, and every rank-$k$ original labelled $k$-by-$N$ matrix $G$ with $N=[k]_q$ that is not simplex-equivalent,

$$
R_G(t)\le S_t-D_t.
$$

Equality holds if and only if $G$ has no zero column, exactly one missing ray $a$, exactly one distinct doubled ray $b$, and every other ray once. In particular the maximum over the entire nonsimplex domain is attained and equals $S_t-D_t$; its equality class is the same for every $t\ge k$. Zero columns and arbitrary repeated or scalar-parallel physical columns are included in the domain. For $0\le t<k$ all recovery probabilities are zero.

**Proof.** Fix $K,k,t$. We first prove the strict supporting inequality on a face with one missing ray that will make the integer comparison decisive. All polynomial identities below are identities of the actual represented polynomials; multiplying $F_{U,d}$ by a positive constant has no effect on their kernel or strictness statements. We use the exact contraction of Theorem 5.2, Euler homogeneity, the reverse Hessian inequality of Theorem 9.1, and the closed-orthant concavity of Theorem 10.2, with their original hypotheses. In particular these suppliers apply to the represented alphabet $A=P\setminus\{a\}$ at every positive weight vector on $A$, and to all its actual subspace contractions.

For clarity, one consequence of the reverse inequality is needed with equality analyzed. Let $f=F_{U,d}$, $d\ge2$, evaluated at a positive vector $x$, suppose $f(x)>0$, and write $g=\nabla f(x)$, $H=\nabla^2f(x)$. On $g^\perp$, the quadratic form of $H$ is nonpositive. If $g\cdot h=0$ and $h^THh=0$, polarization on $g^\perp$ shows $Hh$ is a multiple of $g$. Euler gives $Hx=(d-1)g$ and $g\cdot x=df(x)>0$, so

$$
x^THh=(d-1)g\cdot h=0
$$

forces that multiple to vanish. Thus $Hh=0$.

The Hessian kernel propagates through actual derivatives. Suppose $d\ge3$ and $Hh=0$. For $f_i=\partial_i f$ with $f_i(x)>0$, its reverse inequality gives

$$
h^T\nabla^2 f_i(x)h\le0,
\qquad \nabla f_i(x)\cdot h=(Hh)_i=0.
$$

If $f_i(x)=0$, its nonnegative coefficients and positive $x$ make $f_i$ identically zero. The differentiated Euler identity yields

$$
\sum_i x_i h^T\nabla^2f_i(x)h=(d-2)h^THh=0.
$$

Every nonzero derivative therefore has zero quadratic value on $h$, and the preceding polarization argument, now applied to $f_i$ of degree $d-1$, gives $\nabla^2 f_i(x)h=0$. The zero derivatives have this property as well. Iteration propagates $h$ into the Hessian kernel of every iterated partial derivative of remaining degree at least two.

Apply this to $f=F_{0,t}$ on $A=P\setminus\{a\}$. We claim its Hessian has trivial kernel at every positive $x$ on $A$. Extend a kernel vector $h$ by $h_a=0$, and for a subspace $B\le V$ write $h(B)=\sum_{p\subseteq B}h_p$. Take any $(k-2)$-space $U$ spanned by rays in $A$. Contract a basis of $U$, then repeat one of its basis rays $t-k$ times; this is possible because $k-2\ge1$. The remaining degree is two and the contracted subspace is $U$. Kernel propagation and the degree-two classification of Theorem 6.1 apply to $F_{U,2}$ on the same alphabet $A$.

Its nonloop parallel classes are indexed by the hyperplanes $B\supset U$, and each class consists of the rays in $B\setminus U$, with $a$ omitted if necessary. All $q+1$ classes are nonempty, since each has $q^{k-2}$ rays before that possible omission. If $s_B=h(B)-h(U)$ and $s=\sum_{B\supset U}s_B$, the kernel equation in any row of class $B$ is $s-s_B=0$. Thus every $s_B=s$ and $s=(q+1)s$, so all $s_B=0$. We have proved

$$
h(B)=h(U)\quad
\text{for every represented }U\text{ of dimension }k-2
\text{ and every hyperplane }B\supset U. \tag{16.1}
$$

If $k=3$, choose any projective line $B$ avoiding $a$. Each ray $p$ of $B$ is an allowed $U$ in (16.1), so $h(B)=h_p$ for its $q+1$ rays. Summing gives $h(B)=(q+1)h(B)$, hence all those $h_p$ vanish. Every ray other than $a$ lies on a line avoiding $a$: extend representatives of it and $a$ to a basis of the three-dimensional space and use the line through the first and the third basis ray. Consequently $h=0$.

If $k\ge4$, every $(k-2)$-space is represented by $A$, since its dimension is at least two and deleting one ray cannot leave it in a proper subspace. Fix a hyperplane $B$. It has $[k-1]_q$ subspaces $U$ of dimension $k-2$, and each ray of $B$ is in $[k-2]_q$ of them. Summing (16.1) gives

$$
[k-1]_q h(B)=[k-2]_q h(B),
$$

so $h(B)=0$ for every hyperplane. Summing over all hyperplanes first gives $\sum_p h_p=0$. Summing instead over the hyperplanes containing a fixed ray $r$ gives

$$
0=[k-2]_q\sum_p h_p+\bigl([k-1]_q-[k-2]_q\bigr)h_r
  =q^{k-2}h_r.
$$

Here the hyperplane counts through one ray and through two distinct rays are $[k-1]_q$ and $[k-2]_q$, respectively. This again gives $h=0$ and proves the Hessian claim for all $k\ge3$.

It follows that the root has strictly negative curvature in every nonzero direction preserving total mass on this face. Indeed, for any direction $h$, put

$$
v=h-\frac{g\cdot h}{t f(x)}x.
$$

Then $g\cdot v=0$, and direct differentiation and Euler give

$$
h^T\nabla^2(f^{1/t})(x)h
=\frac1t f(x)^{1/t-1}v^THv.
$$

If this quantity were zero, polarization followed by the trivial-kernel claim would imply $v=0$. Thus $h$ would be a multiple of $x$. For $\sum h_p=0$ and $\sum x_p>0$ that is possible only for $h=0$. The reverse inequality supplies nonpositivity, so the curvature is strictly negative for every nonzero mass-preserving direction.

In particular, with $y=\mathbf1-e_a+e_b$ and $\Phi=Q_t^{1/t}$, every nonnegative $n$ satisfying $n_a=0$, $\sum n_p=N$, and $n\ne y$ satisfies the strict supporting inequality

$$
\Phi(n)<\Phi(y)+\nabla\Phi(y)\cdot(n-y). \tag{16.2}
$$

To include boundary $n$, the segment $y+s(n-y)$ is positive on $A$ near $s=0$. Its root has strictly negative second derivative there, whereas it is concave and continuous on the entire segment by Theorem 10.2. A sufficiently short secant has slope strictly below the derivative at zero; concavity bounds the full secant by that short secant. This proves (16.2) even if some coordinates of $n$, or $Q_t(n)$ itself, vanish.

We next determine the gradient at $y$ to the extent needed for the integer comparison. Let $L=a+b$ denote the two-dimensional vector subspace, or its projective line when discussing rays. The stabilizer of the ordered pair $(a,b)$ acts transitively on the rays of $L\setminus\{a,b\}$ and on the rays outside $L$. To see this, choose the first two basis vectors on $a,b$; diagonal changes move any nonendpoint ray of $L$ to any other, and an arbitrary outside vector can be completed with these two vectors to a basis. The word polynomial is invariant under these linear transformations. Hence its gradient at $y$ has one value on each of these two classes, and a separate value at $b$.

There are real numbers $\gamma,\alpha,\beta$ with

$$
\partial_bQ_t(y)=\gamma-\alpha,\qquad
\partial_cQ_t(y)=\gamma\quad(c\in L\setminus\{a,b\}),\qquad
\partial_dQ_t(y)=\gamma-\beta\quad(d\notin L),
\qquad \alpha>\beta>0. \tag{16.3}
$$

Here is a direct verification of the comparison between the last two classes. For an $r$-space $U$, let $A_{r,v}$ count words over all of $P$ of length $v$ whose span together with $U$ is $V$. This depends only on $r,v$. Choosing nested subspaces shows $A_{r+1,v}\ge A_{r,v}$. Let $D=\partial_b-\partial_a$ and let $(t)_j=t(t-1)\cdots(t-j+1)$. Marking $j$ distinct word positions gives

$$
(\partial_{p_1}\cdots\partial_{p_j}Q_t)(\mathbf1)
=(t)_j A_{\dim(p_1+\cdots+p_j),\,t-j},
$$

including repeated $p_i$. Taylor expansion from $\mathbf1$ to $y=\mathbf1+e_b-e_a$ is exact. For $c\in L\setminus\{a,b\}$, every term in $D^\ell\partial_cQ_t(\mathbf1)$ with $\ell\ge1$ has contracted rank two, so the binomial signs sum to zero. Thus $\partial_cQ_t(y)=\partial_cQ_t(\mathbf1)=\gamma$, independent of $c$. For $d\notin L$, the endpoint terms of the binomial expansion have rank two and the other terms rank three. Odd $\ell$ cancel, the term $\ell=1$ is zero, and even $\ell\ge2$ give

$$
\beta=
\sum_{\substack{2\le\ell\le t-1\\\ell\ \mathrm{even}}}
\frac{2(t)_{\ell+1}}{\ell!}
\left(A_{3,t-\ell-1}-A_{2,t-\ell-1}\right)>0.
$$

Nonnegativity follows from nested subspaces. The $\ell=2$ term is strictly positive: fix nested subspaces $U_2<U_3$ of dimensions two and three, choose a basis of a complement $D$ to $U_3$, and pad its $k-3$ rays to $t-3$ letters with a ray in $U_2$. The resulting word completes $U_3$, whereas its span with $U_2$ is contained in the proper hyperplane $D+U_2$. For $k=3,t=3$ this is the empty word; for $k=3,t>3$ all padding is still inside $U_2$. This verifies $\beta>0$.

Finally choose any $d\notin L$. The vectors $y$ and $y'=\mathbf1-e_a+e_d$ have equal $Q_t$ values by an invertible linear map fixing $a$ and carrying $b$ to $d$. They are distinct positive vectors on $A$ with the same total mass. Applying (16.2) to $y'$ gives $\nabla Q_t(y)\cdot(y'-y)>0$, since the root-to-polynomial gradient factor is positive. Thus $\partial_dQ_t(y)>\partial_bQ_t(y)$, namely $\alpha>\beta$. This completes (16.3).

We now give the integer incidence argument. Let $n\in\mathbb Z_{\ge0}^P$, $\sum_p n_p=N$, $n\ne\mathbf1$, and put $h=n-\mathbf1$. Its negative entries are exactly $-1$. Let $Z=\{p:h_p=-1\}$, $B=\{p:h_p>0\}$, and $z=|Z|=\sum_{b\in B}h_b>0$. For a projective line $L$ put

$$
Z_L=|Z\cap L|,\qquad B_L=\sum_{b\in B\cap L}h_b,
\qquad h(L)=B_L-Z_L.
$$

There exist a line $L$ meeting both $Z$ and $B$, and $b\in B\cap L$, such that

$$
h(L)\le h_b-1. \tag{16.4}
$$

Otherwise, integrality would imply $B_L-Z_L\ge M_L:=\max_{b\in B\cap L}h_b$ on every mixed line. On each such line,

$$
B_LZ_L\le B_L^2-B_LM_L
\le B_L^2-\sum_{b\in B\cap L}h_b^2.
$$

The same inequality holds on nonmixed lines because its left side is zero and its right side is the sum of the nonnegative products of distinct positive entries on that line. Each distinct pair of projective points determines exactly one line. Summing over all lines would therefore give

$$
z^2=\sum_L B_LZ_L
\le\sum_L\left(B_L^2-\sum_{b\in B\cap L}h_b^2\right)
=z^2-\sum_{b\in B}h_b^2<z^2,
$$

a contradiction. Choose $b$ realizing the maximum on a line for which the assumed inequality fails; this proves (16.4). Choose any $a\in Z\cap L$. Then $L=a+b$, $n_a=0$, and $h_b\ge1$.

Use this pair to set $y=\mathbf1-e_a+e_b$. Since $\sum h_p=0$, the gradient values (16.3) give

$$
\begin{aligned}
\nabla Q_t(y)\cdot(n-y)
&=-\alpha(h_b-1)-\beta\sum_{p\notin L}h_p\\
&=-\alpha(h_b-1)+\beta h(L)\\
&\le-(\alpha-\beta)(h_b-1)\le0.
\end{aligned}
$$

The gradient of $\Phi$ has the same positive scalar factor at $y$. If $n\ne y$, (16.2) implies $Q_t(n)<Q_t(y)$. If $n=y$, equality holds. This proves the sharp bound for every nonuniform nonnegative integer multiplicity vector of total $N$, without a restriction on the number or arrangement of its missing and repeated rays. For a zero-free matrix, the exact physical fiber identity gives $R_G(t)=N^{-t}Q_t(n(G))$, and Theorem 15.2 supplies the asserted value and equality characterization.

It remains to treat original zero columns strictly. Suppose $z(G)>0$, choose an original nonzero column on ray $b$, and replace every zero column by that same nonzero vector on its original label. Call the resulting matrix $G'$. Its span contains that of $G$, so it has rank $k$, and every original sampled prefix span is contained in the corresponding new one. Its ray $b$ has multiplicity at least two, so $n(G')\ne\mathbf1$ and the integer comparison applies.

Moreover the probability comparison is strict at every $t\ge k$. Extend the chosen original nonzero column to a basis using original nonzero columns, and retain the other $k-1$ basis labels. A physical word consisting of one original zero label and these $k-1$ labels, padded to length $t$ by one of the retained labels, has probability $N^{-t}>0$. It spans in $G'$ and has rank $k-1$ in $G$. Hence

$$
R_G(t)<R_{G'}(t)\le S_t-D_t.
$$

This coupling retains the iid uniform law on all original labels; no zero is removed or conditioned away. Finally fewer than $k$ columns cannot span $V$, which proves the statement for $t<k$. Theorem 15.2 exhibits rank-$k$ equality matrices for every allowed $K,k$, completing attainment and the entire equivalence. $\square$

The physical model is Bertuzzo–Ravagnani–Yaakobi, [arXiv:2603.06489v1](https://arxiv.org/html/2603.06489v1), Section 2, Problems A and B. Their Section 3, Conjecture 3.2 is an expected-time optimizer question. Their predecessor [arXiv:2507.20639v1](https://arxiv.org/html/2507.20639v1), Section III, Example 1 already gives the binary length-seven nonsimplex expected lower value $17/4$ and simplex value $47/12$. These expectation values are cited inputs, not additional conclusions of Theorem 16.1.

The analytic and physical suppliers used here are Sections 5–12 and the strict simplex comparison of Section 14. The additional inference is the exact single-defect word count, the strict face supporting inequality, and the integer line-incidence argument connecting that value to the unrestricted discrete domain. For the literature parameter map, Kong–Elishco–Wang–Duman, [arXiv:2610.02931v1](https://arxiv.org/pdf/2610.02931v1), Theorem II.3 gives exact subspace-Möbius tails. In its single-container specialization, $\pi_p=n_p(G)/N$, $\pi(U)=\sum_{p\subseteq U}\pi_p$, and $\rho_U=\pi(U)$ for a zero-free matrix. Its standing physical generator has rank $k\ge2$, excludes zero columns, and retains repeated and scalar-parallel columns. Theorem IV.3 and Corollary IV.4 give the expected-time optimizer, uniqueness, and quantitative expected gap for probability laws on $P$; they do not replace (16.2)–(16.4) or the fixed-$t$ deficit calculation. Their tail formula is an exact evaluation, distinct from maximizing that evaluation over original matrices.

Gross–Grunbaum–Bertuzzo–Yaakobi–Ravagnani, [arXiv:2610.07370v1](https://arxiv.org/html/2610.07370v1), Theorem IV.1 allows a probability law on all vectors of $K^k$, including vector zero, and gives the expected-time lower bound with equality exactly when $p(0)=0$ and the induced ray law is uniform. Corollary 3 specializes it to original rank-$k$ generators of length $N$. Here its vector law is $p(v)=N^{-1}|\{i:G_i=v\}|$, so $p(0)=z(G)/N$ and $p(L)=n_L(G)/N$ for nonzero vectors on ray $L$. Its Lemma VI.3 gives

$$
I(G,s)=\sum_{\substack{B\subseteq P,\ |B|=s\\B\ \mathrm{independent}}}
\prod_{p\in B}n_p(G)\qquad(1\le s\le k),
$$

counting independent physical subsets. This supplies exactly the independent-subset multiplicity polynomial; for $t=k$, the word count is $Q_k(n)=k!I(G,k)$. For $t>k$, recovery words can contain repetitions and dependent distinct rays, so the full word and fiber suppliers are required. Expected-time and independent-subset statements alone do not give the finite-deadline runner-up.

Anceaume–Busnel–Schulte-Geers–Sericola, [arXiv:1504.03878v1](https://arxiv.org/pdf/1504.03878v1), Theorems 1–2 concern collecting a specified number $c$ of distinct non-null coupon types, with strictly positive type probabilities summing to one. Theorem 1 applies a two-coordinate averaging with parameter in $[0,1]$; Theorem 2 compares to the uniform law. Theorem 3 retains strictly positive non-null probabilities with sum less than one, fixes the null mass $p_0=1-\sum_i p_i$, and compares to $v_i=(1-p_0)/n$ and to $u_i=1/n$. Our physical zero mass would be $p_0=z(G)/N$, but missing rays have probability zero and projective spanning is not the collection of a fixed number of distinct types. Thus neither their positivity assumptions nor their collection event can be substituted for the hypotheses or event of Theorem 16.1. The use of concavity here is precisely Theorem 10.2 for the actual spanning polynomial, with Brändén–Huh, [arXiv:1902.03719v8](https://arxiv.org/abs/1902.03719v8), Sections 2–3 providing the general Lorentzian context.

## 17. Complete labelled equality assignments

**Theorem 17.1 (representatives, fixed labels, and optional permutations).** Under the field and dimension hypotheses of Theorem 16.1, every original labelled equality matrix, and only such a matrix, is obtained by the following data: an ordered pair of distinct rays $(a,b)$, an unordered two-element subset $J\subset I$, a bijection

$$
\sigma:I\setminus J\longrightarrow P\setminus\{a,b\},
$$

and an arbitrary nonzero representative of $b$ at each label in $J$ and of $\sigma(i)$ at each $i\notin J$. Equivalently, after fixing representatives $v_p\in p\setminus\{0\}$, all such matrices have

$$
G_i=\begin{cases}\lambda_i v_b,&i\in J,\\
\lambda_i v_{\sigma(i)},&i\notin J,
\end{cases}
\qquad \lambda_i\in K^\times.
$$

With labels fixed, quotienting by invertible row transformations and independent nonzero column scalings is exactly the $\operatorname{PGL}(k,q)$ action on these labelled ray maps $\rho:I\to P$. There is no field-automorphism quotient. If column permutations are additionally allowed, there is exactly one equality type. The raw number of labelled matrices attaining equality, before any of these quotients, is

$$
N(N-1)\frac{N!}{2}(q-1)^N.
$$

**Proof.** Theorem 16.1 forces a unique missing ray $a$ and a unique doubled ray $b$. The labels on $b$ form the unique unordered pair $J$, and every remaining label is assigned once to every other ray. This gives precisely $\sigma$ and all its stated data. Conversely every such assignment has exactly the required multiplicities and is zero-free, has rank $k$ by Theorem 15.2, and attains equality at every $t\ge k$. Once the reference $v_p$ are fixed, each nonzero column has one and only one scalar $\lambda_i\in K^\times$, so this parameterization has no further identifications.

Suppose $G'_i=c_i A G_i$ for every fixed label $i$, with $A\in\operatorname{GL}(k,q)$ and $c_i\in K^\times$. Then $\rho'(i)=A\rho(i)$ at each label. Conversely, if this equality of ray maps holds for one $A$, the two nonzero vectors $G'_i$ and $AG_i$ differ by a nonzero scalar $c_i$ separately at each label. Scalar row matrices act trivially on every ray, and quotienting $\operatorname{GL}(k,q)$ by those matrices is precisely $\operatorname{PGL}(k,q)$. To check the action's projective kernel, a linear map fixing every ray fixes basis rays, hence is diagonal, and fixing the rays of sums of two basis vectors forces all diagonal entries equal. This is a linear action over the fixed field $K$; no semilinear transformations are included. Thus the fixed-label classes are exactly the stated projective-group orbits of labelled maps. In particular the double-label pair is preserved by this equivalence, so the optional permutation quotient is a separate operation.

For that optional quotient, $\operatorname{GL}(k,q)$ is transitive on ordered distinct ray pairs: choose independent representatives of each pair, extend each to a basis, and map bases. After this row transformation aligns $(a,b)$ with any other desired pair, a label permutation aligns the double pair and all the singleton fibers; independent column scalings then align all nonzero representatives. Hence there is one equality type under this larger equivalence.

There are $N(N-1)$ choices of $(a,b)$, $\binom N2$ choices of $J$, $(N-2)!$ bijections $\sigma$, and $(q-1)^N$ choices of the actual nonzero vectors. The unique recovery of these data from a labelled matrix prevents overcounting. Since $\binom N2(N-2)!=N!/2$, their product is the asserted raw count. $\square$

## 追加锚（本行以下为增补区）
