# Boolean coefficients and top-degree constraints

## Abstract

Actual Boolean coefficient extraction supplies the exact top-degree equations used by the rank assembly.

**Definition 1.1 (Squarefree Boolean monomials).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.booleanMonomial`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.booleanMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For a finite set s of actual cyclic coordinates, booleanMonomial(s,z) is the product of z_i over i in s. Repeated cyclic coordinates are represented only once; the empty monomial is one.

**Definition 1.2 (Indicator words).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.indicatorWord`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.indicatorWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The word indicatorWord(s) is one at coordinates in s and zero elsewhere.

**Definition 1.3 (Coefficients from actual function values).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.booleanCoeff`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.booleanCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The coefficient of a Boolean function f at s is the sum in ZMod 2 of f(indicatorWord(t)) over every subset t of s. Thus equal actual functions have equal coefficients. Subset cancellation proves that extraction applied to the monomial at t is one exactly when s=t and zero otherwise; this establishes uniqueness for finite sums of squarefree monomials without assuming injectivity of polynomial evaluation.

**Lemma 1.4 (Coefficient extraction on a monomial).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_monomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Extraction of a squarefree Boolean monomial at a finite coordinate set is the equality indicator for the two sets. This is the subset-cancellation fact used by every coefficient expansion below.

**Lemma 1.5 (Coefficient extraction is additive).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_add`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Boolean coefficient extraction of a pointwise sum is the sum of the extracted coefficients.

**Lemma 1.6 (Coefficient extraction commutes with finite sums).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Boolean coefficient extraction commutes with a finite indexed sum of Boolean functions.

**Lemma 1.7 (Scalar multiplication under coefficient extraction).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Multiplying a Boolean function by a binary scalar multiplies its extracted coefficient by the same scalar.

**Lemma 1.8 (Constant coefficient extraction).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every binary scalar a and every nonempty finite coordinate set s, the coefficient at s of the constant function with value a is zero.

**Definition 1.9 (Cyclic prefix variable sets).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefixVariables`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefixVariables` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The finite set prefixVariables(i,r) is the image of t=0,...,r-1 under t ↦ i+2t+1 in the actual cyclic index type.

**Lemma 1.10 (Inserting an endpoint into a monomial).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.monomial_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.monomial_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The Boolean monomial on a finite set with one endpoint inserted factors as the endpoint value times the monomial on the original set, with duplicate coordinates handled by binary idempotence.

**Lemma 1.11 (Expansion of the shifted inverse component).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.shifted_inverse_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.shifted_inverse_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

After translating the inverse input by the all-one word, the inverse component expands into the prefix monomials and their endpoint insertions with the original mask coefficients.

**Theorem 1.12 (Exact coefficients of the shifted inverse component).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall s \in \mathrm{Finset}\left(\mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)\right),\; \mathrm{booleanCoeff}\left({z:\mathrm{Word}\left({{2} \cdot {m}} + {1}\right)}\mapsto\mathrm{inverseComponent}\left(m, b, {1} + {z}\right), s\right) = \sum_{i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)} \sum_{r \in \mathrm{range}\left({m} + {1}\right)} {\mathrm{b}\left(i\right)} \cdot {{\mathrm{ite}\left(s = \mathrm{prefixVariables}\left(i, r\right), 1, 0\right)} + {\mathrm{ite}\left(s = \mathrm{insert}\left({i} + {{2} \cdot {r}}, \mathrm{prefixVariables}\left(i, r\right)\right), 1, 0\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_boolean_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every m, mask b and finite cyclic-coordinate set s, extract the coefficient of z ↦ inverseComponent(m,b)(1+z). Each inverse term contributes the prefix monomial and the prefix with its endpoint i+2r inserted, weighted by b_i. Equality of finite sets decides whether each contributes at s. This statement includes all masks and length one, with no distinct-index premise.

Binary idempotence identifies a product over repeated coordinates with its squarefree monomial. After y=1+z the alternating prefix becomes the monomial on prefixVariables(i,r), and its endpoint factor is 1+z_(i+2r). The coefficient formula follows by linearity of extraction and the subset-cancellation identity. No Boolean normal-form uniqueness or coefficient vanishing is assumed.

**Definition 1.13 (Exact monomial derivative coefficients).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.monomialDerivativeCoeff`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.monomialDerivativeCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

At variable sets t,s and direction u, this is the product of u on t minus s when s is a subset of t, plus one when s=t; absent contributions are zero. Product expansion and coefficient extraction prove that this is the coefficient at s of z ↦ booleanMonomial(t,z+u)+booleanMonomial(t,z).

**Theorem 1.14 (Necessary coefficient equations for a constant inverse derivative).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall u \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {\exists c \in \mathrm{ZMod}\left(2\right),\; \forall y \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {\mathrm{inverseComponent}\left(m, b, {y} + {u}\right)} + {\mathrm{inverseComponent}\left(m, b, y\right)} = c} \Rightarrow {\forall s \in \mathrm{Finset}\left(\mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)\right),\; {\mathrm{Nonempty}\left(s\right)} \Rightarrow {\sum_{i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)} \sum_{r \in \mathrm{range}\left({m} + {1}\right)} {\mathrm{b}\left(i\right)} \cdot {{\mathrm{monomialDerivativeCoeff}\left(\mathrm{prefixVariables}\left(i, r\right), s, u\right)} + {\mathrm{monomialDerivativeCoeff}\left(\mathrm{insert}\left({i} + {{2} \cdot {r}}, \mathrm{prefixVariables}\left(i, r\right)\right), s, u\right)}} = 0}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_derivative_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every m, b,u and nonempty finite set s, if the derivative of the actual inverse component in direction u is constant on all words, the displayed sum of its monomial derivative coefficients is zero. The proof translates by the all-one word and extracts the coefficient from actual functions. It assumes neither a degree argument nor the intended mask classification.

**Definition 1.15 (Highest-degree cyclic variable sets).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.topVariables`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.topVariables` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The set topVariables(m,i) is prefixVariables(i,m) with coordinate i+2m inserted. It has m+1 elements. Its coordinate sum has slope m+1 as a function of i; multiplication by two in the odd cycle inverts that slope, so the sets for distinct i are distinct.

**Lemma 1.16 (The indices within a prefix are distinct).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefix_index_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefix_index_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For r at most m and a fixed starting coordinate i on the cycle of length 2m+1, the map t ↦ i+2t+1 is injective on t=0,...,r-1.

**Lemma 1.17 (Prefix cardinality).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefix_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefix_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

A prefix of length r at an odd cycle has exactly r coordinates whenever r is at most m.

**Lemma 1.18 (The endpoint is outside its prefix).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.endpoint_not_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.endpoint_not_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For r at most m, the endpoint coordinate i+2r is not already in prefixVariables(i,r).

**Lemma 1.19 (Top-variable set cardinality).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.top_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.top_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

Each topVariables(m,i) set has exactly m+1 coordinates.

**Theorem 1.20 (Highest-degree coefficients recover every mask bit).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right),\; \mathrm{booleanCoeff}\left({z:\mathrm{Word}\left({{2} \cdot {m}} + {1}\right)}\mapsto\mathrm{inverseComponent}\left(m, b, {1} + {z}\right), \mathrm{topVariables}\left(m, i\right)\right) = \mathrm{b}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_top_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every m, b and cyclic coordinate i, the coefficient of the shifted inverse component at topVariables(m,i) is exactly b_i. Cardinality excludes every shorter prefix and endpoint term; injectivity of the highest-degree variable sets leaves exactly the term indexed by i. Length one and zero masks are included.

**Theorem 1.21 (The degree-m derivative equation).**

$$\forall m \in \mathrm{Nat},\; {0 < m} \Rightarrow {\forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall u \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {\mathrm{mem}\left(u, \mathrm{constantDerivativeSubmodule}\left(\mathrm{inverseComponent}\left(m, b\right)\right)\right)} \Rightarrow {\forall s \in \mathrm{Finset}\left(\mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)\right),\; {\mathrm{card}\left(s\right) = m} \Rightarrow {\sum_{i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)} {\mathrm{b}\left(i\right)} \cdot {\mathrm{ite}\left(\mathrm{subset}\left(s, \mathrm{topVariables}\left(m, i\right)\right), \mathrm{booleanMonomial}\left(\mathrm{sdiff}\left(\mathrm{topVariables}\left(m, i\right), s\right), u\right), 0\right)} = 0}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_top_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every positive m and constant derivative direction u of the inverse component, and every finite coordinate set s of cardinality m, the sum over i of b_i times the product of u on topVariables(m,i) minus s, with zero contribution unless s is a subset, vanishes. A derivative of a monomial of degree at most m has zero degree-m coefficient; hence only the degree-(m+1) endpoint terms survive. The statement includes m=1 but does not claim the subsequent overlap classification.

## References

- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.booleanCoeff`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.booleanMonomial`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_add`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_constant`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_monomial`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_mul`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.coeff_sum`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.endpoint_not_prefix`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.indicatorWord`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_boolean_coefficient`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_derivative_coefficients`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_top_coefficient`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_top_derivative`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.monomialDerivativeCoeff`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.monomial_insert`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefixVariables`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefix_card`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefix_index_injective`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.shifted_inverse_expansion`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.topVariables`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.top_card`
- Dependency: [D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude](Prelude.md)
