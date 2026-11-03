# Cyclic Boolean foundations

## Abstract

The foundational odd-cycle inverse, Walsh bridge, and affine duality for the cyclic Boolean sign-trace model.

**Definition 1.1 (Binary words on a cyclic index set).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.Word`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.Word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

A word of length n is a function from ZMod n to the binary field ZMod 2. All additions in an index are modulo n; all additions in a word value are modulo two.

**Definition 1.2 (The forward cyclic map).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.chi`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.chi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

At index i, chi(x) is x_i + x_(i+2) + x_(i+1) x_(i+2). Repeated indices denote the same variable, including at length one.

**Definition 1.3 (Integer signs).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sign`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sign` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The sign of a binary field element z is the integer (-1) raised to its representative z.val, which is zero or one.

**Definition 1.4 (The literal source matrix).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sourceMatrix`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sourceMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For arbitrary binary words b and a and cyclic index k, the entry at binary row s and column t is sign((a_k + a_(k-2) + b_k)s + a_(k-1)st). The first row is (1,1); the second is ((-1)^h_k,(-1)^(h_k+g_k)), with g_k=a_(k-1) and h_k=a_k+a_(k-2)+b_k.

**Definition 1.5 (The ordered integer trace).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sourceTrace`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sourceTrace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Form the list of source matrices at representatives zero through n-1 in that order, multiply the list, and take its integer matrix trace. No commutation of matrix factors is used.

**Definition 1.6 (Nonzero trace support).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.traceSupport`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.traceSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The trace support consists of every a for which the literal ordered integer trace is nonzero. No word a is excluded.

**Definition 1.7 (The full affine-support question).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.claim`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every natural m and every nonzero b of length 2m+1, the direction of the affine span over ZMod 2 of the trace support has dimension at least 2m. The parameter m runs from zero, so this is exactly all positive odd lengths, including length one. The inequality is a lower bound, not an equality. The final theorem proves this assertion through the exact trace and Walsh identities and a bound on constant-derivative directions.

**Definition 1.8 (Alternating products).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.alternatingPrefix`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.alternatingPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The alternating prefix at i of length t is the product, for r from zero through t-1, of 1+y_(i+2r+1). The empty product is one.

**Definition 1.9 (The inverse polynomial).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverse`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

At length 2m+1, the inverse coordinate at i is the sum, for r from zero through m, of y_(i+2r) times the alternating prefix at i of length r. Thus its first term is y_i.

**Theorem 1.10 (Both inverse identities at every positive odd length).**

$$\forall m \in \mathrm{Nat},\; {\forall x \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \mathrm{inverse}\left(m, \mathrm{chi}\left(x\right)\right) = x} \land {\forall y \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \mathrm{chi}\left(\mathrm{inverse}\left(m, y\right)\right) = y}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverse_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every m, applying the inverse polynomial after chi gives the original word, and applying chi after the inverse polynomial does the same. The proof does not assume either identity or invertibility.

**Lemma 1.11 (Two has an inverse on the odd cycle).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.twice_half`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.twice_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Multiplication by two and the displayed half-index construction are inverse on ZMod (2*m+1). This helper supplies the actual odd-cycle reindexing used by the inverse proof.

**Lemma 1.12 (Step-two traversal reaches every odd-cycle index).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.step_two_reaches`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.step_two_reaches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every odd cycle, repeated addition of two reaches any target index from any start. The result is used to propagate the inverse recurrence around the complete cycle.

Write y=chi(x). The local Boolean identity is x_i=y_i+(1+y_(i+1))x_(i+2). Iterating t times gives the first t terms of the inverse polynomial plus the alternating prefix of length t times x_(i+2t). For t=m+1 the latter x-coordinate is x_(i+1). If this tail were nonzero, x_(i+1) would be one and the m+1 alternating y-coordinates would all vanish. At each of these positions the recurrence forces the next intervening y-coordinate to vanish and the next x-coordinate in steps of two to be one. The even and odd representatives together cover the cycle, hence y=0.

When chi(x)=0 the recurrence makes x invariant under addition of two. Multiplication by m+1 is an inverse to multiplication by two modulo 2m+1, so every index is reached and x is constant. The image under chi of a constant binary word is that same constant word. Thus the zero fiber contains only the zero word, contradicting the tail's x-coordinate being one. This proves the left inverse identity. The finite domain and codomain have the same cardinality, so injectivity gives surjectivity and hence the right inverse identity.

**Definition 1.13 (Binary dot products).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.dot`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.dot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The dot product of a and x is the sum over all cyclic indices of a_i x_i in ZMod 2.

**Definition 1.14 (Unnormalized integer Walsh coefficients).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walsh`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walsh` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For any Boolean function f on the entire binary word space, its coefficient at a is the integer sum over every x of sign(f(x)+dot(a,x)).

**Lemma 1.15 (Signs multiply across binary addition).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sign_add`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sign_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For binary exponents a and b, sign(a+b) equals sign(a) times sign(b) as an integer identity. The trace and Walsh expansions use this exact multiplicative character law.

**Theorem 1.16 (Exact integer Walsh inversion).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall f \in \mathrm{Word}\left(n\right) \to \mathrm{ZMod}\left(2\right),\; \forall y \in \mathrm{Word}\left(n\right),\; \sum_{a \in \mathrm{Word}\left(n\right)} {\mathrm{walsh}\left(f, a\right)} \cdot {\mathrm{sign}\left(\mathrm{dot}\left(a, y\right)\right)} = {\mathrm{card}\left(\mathrm{Word}\left(n\right)\right)} \cdot {\mathrm{sign}\left(\mathrm{f}\left(y\right)\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walsh_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every positive length n, every Boolean f and every word y, summing walsh(f,a) sign(dot(a,y)) over all a gives the number of binary words times sign(f(y)). Character orthogonality is applied to an actual AddChar into the integers; this is an integer identity without a choice of normalization.

**Theorem 1.17 (The spectral support is nonempty).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall f \in \mathrm{Word}\left(n\right) \to \mathrm{ZMod}\left(2\right),\; \exists a \in \mathrm{Word}\left(n\right),\; \mathrm{walsh}\left(f, a\right) \ne 0}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walsh_support_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

At every positive length, every Boolean f has a nonzero integer Walsh coefficient. Otherwise inversion at the zero word would equate zero to the nonzero product of the number of words and an integer sign.

**Definition 1.18 (An arbitrary component of the inverse).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverseComponent`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverseComponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For arbitrary mask b at length 2m+1, the inverse component at y is dot(b,inverse(m,y)). The mask is unrestricted in this definition.

**Theorem 1.19 (The exact inverse-component orientation).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall a \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \sum_{x \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right)} \mathrm{sign}\left({\mathrm{dot}\left(b, x\right)} + {\mathrm{dot}\left(a, \mathrm{chi}\left(x\right)\right)}\right) = \mathrm{walsh}\left(\mathrm{inverseComponent}\left(m, b\right), a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverse_phase_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every m and all masks b,a, the sum over x of sign(dot(b,x)+dot(a,chi(x))) is the Walsh coefficient at a of the inverse component associated with b. Reindex by the proved bijection chi and use its left inverse identity. Zero and all-one masks are included.

**Theorem 1.20 (Constant Boolean derivatives and Walsh support).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall f \in \mathrm{Word}\left(n\right) \to \mathrm{ZMod}\left(2\right),\; \forall u \in \mathrm{Word}\left(n\right),\; \forall c \in \mathrm{ZMod}\left(2\right),\; {\forall y \in \mathrm{Word}\left(n\right),\; {\mathrm{f}\left({y} + {u}\right)} + {\mathrm{f}\left(y\right)} = c} \Leftrightarrow {\forall a \in \mathrm{Word}\left(n\right),\; {\mathrm{walsh}\left(f, a\right) \ne 0} \Rightarrow {\mathrm{dot}\left(a, u\right) = c}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walsh_constant_derivative_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every positive length, a Boolean derivative in direction u is the constant c exactly when every nonzero Walsh coefficient is supported on the character level dot(a,u)=c. This is the exact two-way character statement; identifying the affine-span dimension still requires a separate argument.

**Definition 1.21 (The dot-product dual map).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.dotDual`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.dotDual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Send a direction u to the linear functional a ↦ dot(a,u) on the binary word space.

**Definition 1.22 (Nondegenerate binary dot pairing).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.dotDualEquiv`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.dotDualEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The dot-product map is a linear equivalence between the word space and its algebraic dual. Injectivity is checked on every coordinate vector and finite-dimensionality supplies surjectivity; this is the nondegenerate pairing used by the affine bridge.

**Definition 1.23 (Affine direction of Walsh support).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walshSupportDirection`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walshSupportDirection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Take the direction of the affine span over ZMod 2 of the nonzero Walsh support.

**Definition 1.24 (Constant-derivative submodule).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.constantDerivativeSubmodule`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.constantDerivativeSubmodule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Define the derivative directions as the comap of the dual annihilator of the Walsh-support affine direction along the dot-product dual map.

**Theorem 1.25 (Affine-span and dual-annihilator bridge).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall f \in \mathrm{Word}\left(n\right) \to \mathrm{ZMod}\left(2\right),\; {\forall u \in \mathrm{Word}\left(n\right),\; {\mathrm{mem}\left(u, \mathrm{constantDerivativeSubmodule}\left(f\right)\right)} \Leftrightarrow {\exists c \in \mathrm{ZMod}\left(2\right),\; \forall y \in \mathrm{Word}\left(n\right),\; {\mathrm{f}\left({y} + {u}\right)} + {\mathrm{f}\left(y\right)} = c}} \land {{\mathrm{finrank}\left(\mathrm{ZMod}\left(2\right), \mathrm{constantDerivativeSubmodule}\left(f\right)\right)} + {\mathrm{finrank}\left(\mathrm{ZMod}\left(2\right), \mathrm{walshSupportDirection}\left(f\right)\right)} = \mathrm{finrank}\left(\mathrm{ZMod}\left(2\right), \mathrm{Word}\left(n\right)\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.constantDerivative_affineSpan_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every positive length and Boolean function, membership in the canonical constant-derivative submodule is equivalent to having a constant Boolean derivative. Its finrank plus the finrank of the Walsh-support affine direction equals the finrank of the full word space. The proof uses a nonzero Walsh coefficient as an affine base point, identifies the direction with the span of support differences, applies walsh_constant_derivative_iff, and transports the dual-annihilator finrank identity through the nondegenerate dot pairing. Length one is included by the same statement.

## References

- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.Word`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.alternatingPrefix`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.chi`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.claim`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.constantDerivativeSubmodule`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.constantDerivative_affineSpan_duality`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.dot`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.dotDual`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.dotDualEquiv`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverse`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverseComponent`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverse_phase_sum`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.inverse_spec`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sign`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sign_add`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sourceMatrix`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.sourceTrace`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.step_two_reaches`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.traceSupport`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.twice_half`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walsh`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walshSupportDirection`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walsh_constant_derivative_iff`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walsh_inversion`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude.walsh_support_nonempty`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates](../../../QuantumBounds/MerminMeasurementDependence/Coordinates.md)
