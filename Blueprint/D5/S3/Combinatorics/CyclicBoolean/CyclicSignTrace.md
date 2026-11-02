# Odd cyclic Boolean inversion and the sign-matrix trace

## Abstract

The ordered integer sign-matrix trace equals its cyclic Boolean phase sum at every positive length. The cyclic Boolean map has an explicit inverse at every positive odd length, where integer Walsh inversion supplies nonempty trace support.

**Definition 1.1 (Binary words on a cyclic index set).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.Word`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word of length n is a function from ZMod n to the binary field ZMod 2. All additions in an index are modulo n; all additions in a word value are modulo two.

**Definition 1.2 (The forward cyclic map).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.chi`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.chi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At index i, chi(x) is x_i + x_(i+2) + x_(i+1) x_(i+2). Repeated indices denote the same variable, including at length one.

**Definition 1.3 (Integer signs).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sign`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sign of a binary field element z is the integer (-1) raised to its representative z.val, which is zero or one.

**Definition 1.4 (The literal source matrix).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sourceMatrix`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sourceMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary binary words b and a and cyclic index k, the entry at binary row s and column t is sign((a_k + a_(k-2) + b_k)s + a_(k-1)st). The first row is (1,1); the second is ((-1)^h_k,(-1)^(h_k+g_k)), with g_k=a_(k-1) and h_k=a_k+a_(k-2)+b_k.

**Definition 1.5 (The ordered integer trace).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sourceTrace`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sourceTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Form the list of source matrices at representatives zero through n-1 in that order, multiply the list, and take its integer matrix trace. No commutation of matrix factors is used.

**Definition 1.6 (Nonzero trace support).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.traceSupport`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.traceSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace support consists of every a for which the literal ordered integer trace is nonzero. No word a is excluded.

**Definition 1.7 (The full affine-support question).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.claim`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m and every nonzero b of length 2m+1, the direction of the affine span over ZMod 2 of the trace support has dimension at least 2m. The parameter m runs from zero, so this is exactly all positive odd lengths, including length one. The inequality is a lower bound, not an equality. This definition states the question; the trace, inverse and Walsh results below do not prove its dimension bound.

**Definition 1.8 (Alternating products).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.alternatingPrefix`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.alternatingPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alternating prefix at i of length t is the product, for r from zero through t-1, of 1+y_(i+2r+1). The empty product is one.

**Definition 1.9 (The inverse polynomial).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At length 2m+1, the inverse coordinate at i is the sum, for r from zero through m, of y_(i+2r) times the alternating prefix at i of length r. Thus its first term is y_i.

**Theorem 1.10 (Both inverse identities at every positive odd length).**

$$\forall m \in \mathrm{Nat},\; {\forall x \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \mathrm{inverse}\left(m, \mathrm{chi}\left(x\right)\right) = x} \land {\forall y \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \mathrm{chi}\left(\mathrm{inverse}\left(m, y\right)\right) = y}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m, applying the inverse polynomial after chi gives the original word, and applying chi after the inverse polynomial does the same. The proof does not assume either identity or invertibility.

Write y=chi(x). The local Boolean identity is x_i=y_i+(1+y_(i+1))x_(i+2). Iterating t times gives the first t terms of the inverse polynomial plus the alternating prefix of length t times x_(i+2t). For t=m+1 the latter x-coordinate is x_(i+1). If this tail were nonzero, x_(i+1) would be one and the m+1 alternating y-coordinates would all vanish. At each of these positions the recurrence forces the next intervening y-coordinate to vanish and the next x-coordinate in steps of two to be one. The even and odd representatives together cover the cycle, hence y=0.

When chi(x)=0 the recurrence makes x invariant under addition of two. Multiplication by m+1 is an inverse to multiplication by two modulo 2m+1, so every index is reached and x is constant. The image under chi of a constant binary word is that same constant word. Thus the zero fiber contains only the zero word, contradicting the tail's x-coordinate being one. This proves the left inverse identity. The finite domain and codomain have the same cardinality, so injectivity gives surjectivity and hence the right inverse identity.

**Definition 1.11 (Binary dot products).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.dot`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.dot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dot product of a and x is the sum over all cyclic indices of a_i x_i in ZMod 2.

**Definition 1.12 (Unnormalized integer Walsh coefficients).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walsh`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walsh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any Boolean function f on the entire binary word space, its coefficient at a is the integer sum over every x of sign(f(x)+dot(a,x)).

**Theorem 1.13 (Exact integer Walsh inversion).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall f \in \mathrm{Word}\left(n\right) \to \mathrm{ZMod}\left(2\right),\; \forall y \in \mathrm{Word}\left(n\right),\; \sum_{a \in \mathrm{Word}\left(n\right)} {\mathrm{walsh}\left(f, a\right)} \cdot {\mathrm{sign}\left(\mathrm{dot}\left(a, y\right)\right)} = {\mathrm{card}\left(\mathrm{Word}\left(n\right)\right)} \cdot {\mathrm{sign}\left(\mathrm{f}\left(y\right)\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walsh_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive length n, every Boolean f and every word y, summing walsh(f,a) sign(dot(a,y)) over all a gives the number of binary words times sign(f(y)). Character orthogonality is applied to an actual AddChar into the integers; this is an integer identity without a choice of normalization.

**Theorem 1.14 (The spectral support is nonempty).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall f \in \mathrm{Word}\left(n\right) \to \mathrm{ZMod}\left(2\right),\; \exists a \in \mathrm{Word}\left(n\right),\; \mathrm{walsh}\left(f, a\right) \ne 0}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walsh_support_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive length, every Boolean f has a nonzero integer Walsh coefficient. Otherwise inversion at the zero word would equate zero to the nonzero product of the number of words and an integer sign.

**Definition 1.15 (An arbitrary component of the inverse).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverseComponent`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverseComponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary mask b at length 2m+1, the inverse component at y is dot(b,inverse(m,y)). The mask is unrestricted in this definition.

**Theorem 1.16 (The exact inverse-component orientation).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall a \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \sum_{x \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right)} \mathrm{sign}\left({\mathrm{dot}\left(b, x\right)} + {\mathrm{dot}\left(a, \mathrm{chi}\left(x\right)\right)}\right) = \mathrm{walsh}\left(\mathrm{inverseComponent}\left(m, b\right), a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_phase_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m and all masks b,a, the sum over x of sign(dot(b,x)+dot(a,chi(x))) is the Walsh coefficient at a of the inverse component associated with b. Reindex by the proved bijection chi and use its left inverse identity. Zero and all-one masks are included.

**Theorem 1.17 (The cyclic Boolean phase support is nonempty).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \exists a \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \sum_{x \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right)} \mathrm{sign}\left({\mathrm{dot}\left(b, x\right)} + {\mathrm{dot}\left(a, \mathrm{chi}\left(x\right)\right)}\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_phase_support_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m and every mask b, some a has a nonzero phase sum over x of sign(dot(b,x)+dot(a,chi(x))). This uses Walsh nonemptiness and the proved inverse reindexing. The trace identity below therefore also makes the literal source trace support nonempty, without any assumption on b.

**Theorem 1.18 (Constant Boolean derivatives and Walsh support).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall f \in \mathrm{Word}\left(n\right) \to \mathrm{ZMod}\left(2\right),\; \forall u \in \mathrm{Word}\left(n\right),\; \forall c \in \mathrm{ZMod}\left(2\right),\; {\forall y \in \mathrm{Word}\left(n\right),\; {\mathrm{f}\left({y} + {u}\right)} + {\mathrm{f}\left(y\right)} = c} \Leftrightarrow {\forall a \in \mathrm{Word}\left(n\right),\; {\mathrm{walsh}\left(f, a\right) \ne 0} \Rightarrow {\mathrm{dot}\left(a, u\right) = c}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walsh_constant_derivative_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive length, a Boolean derivative in direction u is the constant c exactly when every nonzero Walsh coefficient is supported on the character level dot(a,u)=c. This is the exact two-way character statement; identifying the affine-span dimension still requires a separate argument.

**Definition 1.19 (The dot-product dual map).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.dotDual`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.dotDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Send a direction u to the linear functional a ↦ dot(a,u) on the binary word space.

**Definition 1.20 (Nondegenerate binary dot pairing).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.dotDualEquiv`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.dotDualEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dot-product map is a linear equivalence between the word space and its algebraic dual. Injectivity is checked on every coordinate vector and finite-dimensionality supplies surjectivity; this is the nondegenerate pairing used by the affine bridge.

**Definition 1.21 (Affine direction of Walsh support).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walshSupportDirection`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walshSupportDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the direction of the affine span over ZMod 2 of the nonzero Walsh support.

**Definition 1.22 (Constant-derivative submodule).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.constantDerivativeSubmodule`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.constantDerivativeSubmodule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define the derivative directions as the comap of the dual annihilator of the Walsh-support affine direction along the dot-product dual map.

**Theorem 1.23 (Affine-span and dual-annihilator bridge).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall f \in \mathrm{Word}\left(n\right) \to \mathrm{ZMod}\left(2\right),\; {\forall u \in \mathrm{Word}\left(n\right),\; {\mathrm{mem}\left(u, \mathrm{constantDerivativeSubmodule}\left(f\right)\right)} \Leftrightarrow {\exists c \in \mathrm{ZMod}\left(2\right),\; \forall y \in \mathrm{Word}\left(n\right),\; {\mathrm{f}\left({y} + {u}\right)} + {\mathrm{f}\left(y\right)} = c}} \land {{\mathrm{finrank}\left(\mathrm{ZMod}\left(2\right), \mathrm{constantDerivativeSubmodule}\left(f\right)\right)} + {\mathrm{finrank}\left(\mathrm{ZMod}\left(2\right), \mathrm{walshSupportDirection}\left(f\right)\right)} = \mathrm{finrank}\left(\mathrm{ZMod}\left(2\right), \mathrm{Word}\left(n\right)\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.constantDerivative_affineSpan_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive length and Boolean function, membership in the canonical constant-derivative submodule is equivalent to having a constant Boolean derivative. Its finrank plus the finrank of the Walsh-support affine direction equals the finrank of the full word space. The proof uses a nonzero Walsh coefficient as an affine base point, identifies the direction with the span of support differences, applies walsh_constant_derivative_iff, and transports the dual-annihilator finrank identity through the nondegenerate dot pairing. Length one is included by the same statement.

**Theorem 1.24 (The ordered trace is the exact Boolean phase sum).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall b \in \mathrm{Word}\left(n\right),\; \forall a \in \mathrm{Word}\left(n\right),\; \mathrm{sourceTrace}\left(b, a\right) = \sum_{x \in \mathrm{Word}\left(n\right)} \mathrm{sign}\left({\mathrm{dot}\left(b, x\right)} + {\mathrm{dot}\left(a, \mathrm{chi}\left(x\right)\right)}\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sourceTrace_eq_phase_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive length n and for all words b,a, the literal ordered matrix trace is the sum over every x of sign(dot(b,x)+dot(a,chi(x))). Length one and all coincident cyclic indices are included. This identity also applies to even lengths; oddness is needed only for the inverse construction.

For a list of r+1 matrices, expand its (i,j) entry over all r intermediate states. The row tuple is i followed by the intermediate states; the column tuple is those states followed by j. Induction uses the first matrix factor and the ordinary Matrix.mul entry formula, preserving the complete list order. Taking the trace identifies j with i. Joining the initial state to the intermediate tuple gives every cyclic path exactly once; the final column is the initial state, including for a one-factor product.

The path product is the sign of the sum of its entry exponents. Reindex the a_(k-2)x_k term by k=i+2 and the a_(k-1)x_k x_(k+1) term by k=i+1. The coefficient of a_i becomes x_i+x_(i+2)+x_(i+1)x_(i+2), exactly chi(x)_i. These are bijections of the actual cyclic index set, so repeated indices need no separate independence assumption. Combining this identity with the inverse phase formula identifies traceSupport(b) with the nonzero Walsh support of inverseComponent(m,b) at every odd length. The established phase nonemptiness thus supplies trace nonemptiness.

**Definition 1.25 (Squarefree Boolean monomials).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.booleanMonomial`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.booleanMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set s of actual cyclic coordinates, booleanMonomial(s,z) is the product of z_i over i in s. Repeated cyclic coordinates are represented only once; the empty monomial is one.

**Definition 1.26 (Indicator words).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.indicatorWord`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.indicatorWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word indicatorWord(s) is one at coordinates in s and zero elsewhere.

**Definition 1.27 (Coefficients from actual function values).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.booleanCoeff`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.booleanCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of a Boolean function f at s is the sum in ZMod 2 of f(indicatorWord(t)) over every subset t of s. Thus equal actual functions have equal coefficients. Subset cancellation proves that extraction applied to the monomial at t is one exactly when s=t and zero otherwise; this establishes uniqueness for finite sums of squarefree monomials without assuming injectivity of polynomial evaluation.

**Definition 1.28 (Cyclic prefix variable sets).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.prefixVariables`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.prefixVariables` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set prefixVariables(i,r) is the image of t=0,...,r-1 under t ↦ i+2t+1 in the actual cyclic index type.

**Theorem 1.29 (Exact coefficients of the shifted inverse component).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall s \in \mathrm{Finset}\left(\mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)\right),\; \mathrm{booleanCoeff}\left({z:\mathrm{Word}\left({{2} \cdot {m}} + {1}\right)}\mapsto\mathrm{inverseComponent}\left(m, b, {1} + {z}\right), s\right) = \sum_{i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)} \sum_{r \in \mathrm{range}\left({m} + {1}\right)} {\mathrm{b}\left(i\right)} \cdot {{\mathrm{ite}\left(s = \mathrm{prefixVariables}\left(i, r\right), 1, 0\right)} + {\mathrm{ite}\left(s = \mathrm{insert}\left({i} + {{2} \cdot {r}}, \mathrm{prefixVariables}\left(i, r\right)\right), 1, 0\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_component_boolean_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m, mask b and finite cyclic-coordinate set s, extract the coefficient of z ↦ inverseComponent(m,b)(1+z). Each inverse term contributes the prefix monomial and the prefix with its endpoint i+2r inserted, weighted by b_i. Equality of finite sets decides whether each contributes at s. This statement includes all masks and length one, with no distinct-index premise.

Binary idempotence identifies a product over repeated coordinates with its squarefree monomial. After y=1+z the alternating prefix becomes the monomial on prefixVariables(i,r), and its endpoint factor is 1+z_(i+2r). The coefficient formula follows by linearity of extraction and the subset-cancellation identity. No Boolean normal-form uniqueness or coefficient vanishing is assumed.

**Definition 1.30 (Exact monomial derivative coefficients).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.monomialDerivativeCoeff`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.monomialDerivativeCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At variable sets t,s and direction u, this is the product of u on t minus s when s is a subset of t, plus one when s=t; absent contributions are zero. Product expansion and coefficient extraction prove that this is the coefficient at s of z ↦ booleanMonomial(t,z+u)+booleanMonomial(t,z).

**Theorem 1.31 (Necessary coefficient equations for a constant inverse derivative).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall u \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {\exists c \in \mathrm{ZMod}\left(2\right),\; \forall y \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {\mathrm{inverseComponent}\left(m, b, {y} + {u}\right)} + {\mathrm{inverseComponent}\left(m, b, y\right)} = c} \Rightarrow {\forall s \in \mathrm{Finset}\left(\mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)\right),\; {\mathrm{Nonempty}\left(s\right)} \Rightarrow {\sum_{i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)} \sum_{r \in \mathrm{range}\left({m} + {1}\right)} {\mathrm{b}\left(i\right)} \cdot {{\mathrm{monomialDerivativeCoeff}\left(\mathrm{prefixVariables}\left(i, r\right), s, u\right)} + {\mathrm{monomialDerivativeCoeff}\left(\mathrm{insert}\left({i} + {{2} \cdot {r}}, \mathrm{prefixVariables}\left(i, r\right)\right), s, u\right)}} = 0}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_component_derivative_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m, b,u and nonempty finite set s, if the derivative of the actual inverse component in direction u is constant on all words, the displayed sum of its monomial derivative coefficients is zero. The proof translates by the all-one word and extracts the coefficient from actual functions. It assumes neither a degree argument nor the intended mask classification.

**Definition 1.32 (Highest-degree cyclic variable sets).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.topVariables`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.topVariables` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set topVariables(m,i) is prefixVariables(i,m) with coordinate i+2m inserted. It has m+1 elements. Its coordinate sum has slope m+1 as a function of i; multiplication by two in the odd cycle inverts that slope, so the sets for distinct i are distinct.

**Theorem 1.33 (Highest-degree coefficients recover every mask bit).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right),\; \mathrm{booleanCoeff}\left({z:\mathrm{Word}\left({{2} \cdot {m}} + {1}\right)}\mapsto\mathrm{inverseComponent}\left(m, b, {1} + {z}\right), \mathrm{topVariables}\left(m, i\right)\right) = \mathrm{b}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_component_top_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m, b and cyclic coordinate i, the coefficient of the shifted inverse component at topVariables(m,i) is exactly b_i. Cardinality excludes every shorter prefix and endpoint term; injectivity of the highest-degree variable sets leaves exactly the term indexed by i. Length one and zero masks are included.

**Theorem 1.34 (The degree-m derivative equation).**

$$\forall m \in \mathrm{Nat},\; {0 < m} \Rightarrow {\forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall u \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {\mathrm{mem}\left(u, \mathrm{constantDerivativeSubmodule}\left(\mathrm{inverseComponent}\left(m, b\right)\right)\right)} \Rightarrow {\forall s \in \mathrm{Finset}\left(\mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)\right),\; {\mathrm{card}\left(s\right) = m} \Rightarrow {\sum_{i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)} {\mathrm{b}\left(i\right)} \cdot {\mathrm{ite}\left(\mathrm{subset}\left(s, \mathrm{topVariables}\left(m, i\right)\right), \mathrm{booleanMonomial}\left(\mathrm{sdiff}\left(\mathrm{topVariables}\left(m, i\right), s\right), u\right), 0\right)} = 0}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_component_top_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive m and constant derivative direction u of the inverse component, and every finite coordinate set s of cardinality m, the sum over i of b_i times the product of u on topVariables(m,i) minus s, with zero contribution unless s is a subset, vanishes. A derivative of a monomial of degree at most m has zero degree-m coefficient; hence only the degree-(m+1) endpoint terms survive. The statement includes m=1 but does not claim the subsequent overlap classification.

For positive m, each topVariables(m,i) has exactly one adjacent cyclic pair, at i+2m-1 and i+2m. The prefix itself contains no adjacent pair, including across the cyclic boundary. Deleting any other coordinate a leaves this pair intact, so any top variable set containing the deletion must have the same index i. Applying the degree-m derivative equation at that deletion therefore proves b_i u_a=0. This establishes the interior-deletion constraints for every odd length at least five, and the same implication at length three where there is no interior coordinate. The endpoint deletions, their shared coefficient equation and the lower-degree equations remain unproved here.

The literal trace model follows ricardorr, MathOverflow question 512655, original revision E06A6743-2C15-41CD-9390-04D1862ABA02, https://mathoverflow.net/questions/512655, attributed under CC-BY-SA 4.0. The inverse argument above is a direct derivation for this cyclic map.

The affine-span duality is proved above. The affine-support assertion still requires the complete classification of constant derivative directions for every nonzero inverse-component mask, including the cyclic top-overlap and lower-coefficient arguments for lengths at least five, the length-three polar case and assembly with length one. The coefficient formula alone does not establish that classification or settle the dimension bound.

## References

- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.Word`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.alternatingPrefix`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.booleanCoeff`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.booleanMonomial`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.chi`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.claim`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.constantDerivativeSubmodule`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.constantDerivative_affineSpan_duality`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.dot`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.dotDual`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.dotDualEquiv`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.indicatorWord`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverseComponent`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_component_boolean_coefficient`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_component_derivative_coefficients`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_component_top_coefficient`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_component_top_derivative`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_phase_sum`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_phase_support_nonempty`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.inverse_spec`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.monomialDerivativeCoeff`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.prefixVariables`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sign`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sourceMatrix`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sourceTrace`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.sourceTrace_eq_phase_sum`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.topVariables`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.traceSupport`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walsh`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walshSupportDirection`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walsh_constant_derivative_iff`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walsh_inversion`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.walsh_support_nonempty`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates](../../QuantumBounds/MerminMeasurementDependence/Coordinates.md)
