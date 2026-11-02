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

**Definition 1.4 (Cyclic prefix variable sets).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefixVariables`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefixVariables` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The finite set prefixVariables(i,r) is the image of t=0,...,r-1 under t ↦ i+2t+1 in the actual cyclic index type.

**Theorem 1.5 (Exact coefficients of the shifted inverse component).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall s \in \mathrm{Finset}\left(\mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)\right),\; \mathrm{booleanCoeff}\left({z:\mathrm{Word}\left({{2} \cdot {m}} + {1}\right)}\mapsto\mathrm{inverseComponent}\left(m, b, {1} + {z}\right), s\right) = \sum_{i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)} \sum_{r \in \mathrm{range}\left({m} + {1}\right)} {\mathrm{b}\left(i\right)} \cdot {{\mathrm{ite}\left(s = \mathrm{prefixVariables}\left(i, r\right), 1, 0\right)} + {\mathrm{ite}\left(s = \mathrm{insert}\left({i} + {{2} \cdot {r}}, \mathrm{prefixVariables}\left(i, r\right)\right), 1, 0\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_boolean_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every m, mask b and finite cyclic-coordinate set s, extract the coefficient of z ↦ inverseComponent(m,b)(1+z). Each inverse term contributes the prefix monomial and the prefix with its endpoint i+2r inserted, weighted by b_i. Equality of finite sets decides whether each contributes at s. This statement includes all masks and length one, with no distinct-index premise.

Binary idempotence identifies a product over repeated coordinates with its squarefree monomial. After y=1+z the alternating prefix becomes the monomial on prefixVariables(i,r), and its endpoint factor is 1+z_(i+2r). The coefficient formula follows by linearity of extraction and the subset-cancellation identity. No Boolean normal-form uniqueness or coefficient vanishing is assumed.

**Definition 1.6 (Exact monomial derivative coefficients).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.monomialDerivativeCoeff`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.monomialDerivativeCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

At variable sets t,s and direction u, this is the product of u on t minus s when s is a subset of t, plus one when s=t; absent contributions are zero. Product expansion and coefficient extraction prove that this is the coefficient at s of z ↦ booleanMonomial(t,z+u)+booleanMonomial(t,z).

**Theorem 1.7 (Necessary coefficient equations for a constant inverse derivative).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall u \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {\exists c \in \mathrm{ZMod}\left(2\right),\; \forall y \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {\mathrm{inverseComponent}\left(m, b, {y} + {u}\right)} + {\mathrm{inverseComponent}\left(m, b, y\right)} = c} \Rightarrow {\forall s \in \mathrm{Finset}\left(\mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)\right),\; {\mathrm{Nonempty}\left(s\right)} \Rightarrow {\sum_{i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)} \sum_{r \in \mathrm{range}\left({m} + {1}\right)} {\mathrm{b}\left(i\right)} \cdot {{\mathrm{monomialDerivativeCoeff}\left(\mathrm{prefixVariables}\left(i, r\right), s, u\right)} + {\mathrm{monomialDerivativeCoeff}\left(\mathrm{insert}\left({i} + {{2} \cdot {r}}, \mathrm{prefixVariables}\left(i, r\right)\right), s, u\right)}} = 0}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_derivative_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every m, b,u and nonempty finite set s, if the derivative of the actual inverse component in direction u is constant on all words, the displayed sum of its monomial derivative coefficients is zero. The proof translates by the all-one word and extracts the coefficient from actual functions. It assumes neither a degree argument nor the intended mask classification.

**Definition 1.8 (Highest-degree cyclic variable sets).**

Lean statement: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.topVariables`

*Formalization.* `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.topVariables` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

The set topVariables(m,i) is prefixVariables(i,m) with coordinate i+2m inserted. It has m+1 elements. Its coordinate sum has slope m+1 as a function of i; multiplication by two in the odd cycle inverts that slope, so the sets for distinct i are distinct.

**Theorem 1.9 (Highest-degree coefficients recover every mask bit).**

$$\forall m \in \mathrm{Nat},\; \forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right),\; \mathrm{booleanCoeff}\left({z:\mathrm{Word}\left({{2} \cdot {m}} + {1}\right)}\mapsto\mathrm{inverseComponent}\left(m, b, {1} + {z}\right), \mathrm{topVariables}\left(m, i\right)\right) = \mathrm{b}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_top_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every m, b and cyclic coordinate i, the coefficient of the shifted inverse component at topVariables(m,i) is exactly b_i. Cardinality excludes every shorter prefix and endpoint term; injectivity of the highest-degree variable sets leaves exactly the term indexed by i. Length one and zero masks are included.

**Theorem 1.10 (The degree-m derivative equation).**

$$\forall m \in \mathrm{Nat},\; {0 < m} \Rightarrow {\forall b \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; \forall u \in \mathrm{Word}\left({{2} \cdot {m}} + {1}\right),\; {\mathrm{mem}\left(u, \mathrm{constantDerivativeSubmodule}\left(\mathrm{inverseComponent}\left(m, b\right)\right)\right)} \Rightarrow {\forall s \in \mathrm{Finset}\left(\mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)\right),\; {\mathrm{card}\left(s\right) = m} \Rightarrow {\sum_{i \in \mathrm{ZMod}\left({{2} \cdot {m}} + {1}\right)} {\mathrm{b}\left(i\right)} \cdot {\mathrm{ite}\left(\mathrm{subset}\left(s, \mathrm{topVariables}\left(m, i\right)\right), \mathrm{booleanMonomial}\left(\mathrm{sdiff}\left(\mathrm{topVariables}\left(m, i\right), s\right), u\right), 0\right)} = 0}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_top_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

For every positive m and constant derivative direction u of the inverse component, and every finite coordinate set s of cardinality m, the sum over i of b_i times the product of u on topVariables(m,i) minus s, with zero contribution unless s is a subset, vanishes. A derivative of a monomial of degree at most m has zero degree-m coefficient; hence only the degree-(m+1) endpoint terms survive. The statement includes m=1 but does not claim the subsequent overlap classification.

## References

- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.booleanCoeff`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.booleanMonomial`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.indicatorWord`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_boolean_coefficient`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_derivative_coefficients`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_top_coefficient`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.inverse_component_top_derivative`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.monomialDerivativeCoeff`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.prefixVariables`
- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients.topVariables`
- Dependency: [D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude](Prelude.md)
