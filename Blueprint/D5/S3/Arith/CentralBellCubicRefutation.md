# Central Bell Cubic Refutations

## Abstract

Rational double-root certificates refute the two distinct-root claims for the printed n = 3, lambda = 3 central Bell cosine cubics. The proposed D5/S1/Polynomial bucket does not exist; D5/S3/Arith is the nearest existing integer/polynomial-arithmetic owner, and capacity was checked.

**Definition 1.1 (Expanded Euler-type cubic).**

$$\forall x \in \mathbb{C}, y \in \mathbb{C}, z \in \mathbb{C},\; eulerCubic\left(x, y, z\right) = -\frac{9 \cdot x}{4} + x^{3} - 3 \cdot x \cdot y^{2} - 2 \cdot z + 3 \cdot x^{2} \cdot z - 3 \cdot y^{2} \cdot z + 3 \cdot x \cdot z^{2} + z^{3}$$

*Formalization.* `D5/S3/Arith/CentralBellCubicRefutation.eulerCubic` (`✓ std3`).

*Citation.* Waseem Ahmad Khan and Francesco Aldo Costabile and Khidir Shaib Mohamed and Ugur Duran and Abdulghani Muhyi and Azhar Iqbal and Wei Sin Koh (2026). *Algebraic properties of central Bell-based type 2 Bernoulli and Euler polynomials of complex variable*. DOI: [10.3934/nhm.2026030](https://doi.org/10.3934/nhm.2026030).

*Commentary.*

This repository definition transcribes the printed n = 3, lambda = 3 Euler-type cosine cubic, with all three arguments and its value in the complex numbers. Khan et al., Networks and Heterogeneous Media 21(2) (2026), 693-724, DOI 10.3934/nhm.2026030, Conjecture 3, is the claim in scope; the paper is not cited as proving the refutation below.

**Definition 1.2 (Expanded Bernoulli-type cubic).**

$$\forall x \in \mathbb{C}, y \in \mathbb{C}, z \in \mathbb{C},\; bernoulliCubic\left(x, y, z\right) = -\frac{3 \cdot x}{4} + x^{3} - 3 \cdot x \cdot y^{2} - \frac{z}{2} + 3 \cdot x^{2} \cdot z - 3 \cdot y^{2} \cdot z + 3 \cdot x \cdot z^{2} + z^{3}$$

*Formalization.* `D5/S3/Arith/CentralBellCubicRefutation.bernoulliCubic` (`✓ std3`).

*Citation.* Waseem Ahmad Khan and Francesco Aldo Costabile and Khidir Shaib Mohamed and Ugur Duran and Abdulghani Muhyi and Azhar Iqbal and Wei Sin Koh (2026). *Algebraic properties of central Bell-based type 2 Bernoulli and Euler polynomials of complex variable*. DOI: [10.3934/nhm.2026030](https://doi.org/10.3934/nhm.2026030).

*Commentary.*

This repository definition transcribes the printed n = 3, lambda = 3 Bernoulli-type cosine cubic, with all arguments and its value complex. Conjecture 1 of the same paper is the claim in scope. The definition uses the printed expansion; its factorization is derived in the proof.

**Definition 1.3 (Three pairwise distinct complex zeros).**

$$\forall f \in \mathbb{C} \to \mathbb{C},\; HasThreeDistinctRoots\left(f\right) \Leftrightarrow (\exists a \in \mathbb{C}, b \in \mathbb{C}, c \in \mathbb{C},\; f\left(a\right) = 0 \land \left(f\left(b\right) = 0 \land \left(f\left(c\right) = 0 \land \left(a \ne b \land \left(a \ne c \land b \ne c\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Arith/CentralBellCubicRefutation.HasThreeDistinctRoots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate asks for three zeros and all three pairwise inequalities. It counts distinct complex solutions, not algebraic multiplicities. Both refutation theorems use this predicate.

**Definition 1.4 (Finite generating-function jet).**

$$\forall q \in \mathbb{C}, x \in \mathbb{C}, y \in \mathbb{C}, z \in \mathbb{C},\; egfJet\left(q, x, y, z\right) = (1 - C\left(q\right) \cdot X^{2}) \cdot (1 + C\left(x\right) \cdot X + C\left(\frac{x^{2}}{2}\right) \cdot X^{2} + C\left(\frac{x^{3}}{6}\right) \cdot X^{3}) \cdot (1 - C\left(\frac{y^{2}}{2}\right) \cdot X^{2}) \cdot (1 + C\left(z\right) \cdot X + C\left(\frac{z^{2}}{2}\right) \cdot X^{2} + C\left(\frac{z^{3}}{6} + \frac{z}{24}\right) \cdot X^{3})$$

*Formalization.* `D5/S3/Arith/CentralBellCubicRefutation.egfJet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product is a polynomial over the complex numbers. C denotes Polynomial.C and X denotes Polynomial.X. It records the four finite jets, including the central Bell z/24 contribution, without asserting an infinite-series identity.

**Theorem 1.5 (Euler coefficient identity).**

$$\forall x \in \mathbb{C}, y \in \mathbb{C}, z \in \mathbb{C},\; 6 \cdot coeff\left(egfJet\left(\frac{3}{8}, x, y, z\right), 3\right) = eulerCubic\left(x, y, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CentralBellCubicRefutation.euler_egf_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Six times the degree-three coefficient with prefactor parameter 3/8 is the printed Euler cubic. coeff denotes Polynomial.coeff.

**Theorem 1.6 (Bernoulli coefficient identity).**

$$\forall x \in \mathbb{C}, y \in \mathbb{C}, z \in \mathbb{C},\; 6 \cdot coeff\left(egfJet\left(\frac{1}{8}, x, y, z\right), 3\right) = bernoulliCubic\left(x, y, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CentralBellCubicRefutation.bernoulli_egf_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Six times the degree-three coefficient with prefactor parameter 1/8 is the printed Bernoulli cubic.

**Theorem 1.7 (Shifted Euler identity).**

$$\forall x \in \mathbb{C}, y \in \mathbb{C}, z \in \mathbb{C},\; eulerCubic\left(x, y, z\right) = (x + z)^{3} - 3 \cdot (x + z) \cdot (y^{2} + \frac{3}{4}) + \frac{z}{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CentralBellCubicRefutation.euler_coefficient_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shift x+z isolates the Euler quadratic parameter y squared plus 3/4.

**Theorem 1.8 (Shifted Bernoulli identity).**

$$\forall x \in \mathbb{C}, y \in \mathbb{C}, z \in \mathbb{C},\; bernoulliCubic\left(x, y, z\right) = (x + z)^{3} - 3 \cdot (x + z) \cdot (y^{2} + \frac{1}{4}) + \frac{z}{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CentralBellCubicRefutation.bernoulli_coefficient_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shift x+z isolates the Bernoulli quadratic parameter y squared plus 1/4.

**Theorem 1.9 (Euler rational factorization).**

$$\forall x \in \mathbb{C},\; eulerCubic\left(x, \frac{1}{2}, 8\right) = (x + 7)^{2} \cdot (x + 10)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CentralBellCubicRefutation.euler_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the rational parameters 1/2 and 8, the repeated factor is x+7.

**Theorem 1.10 (Bernoulli rational factorization).**

$$\forall x \in \mathbb{C},\; bernoulliCubic\left(x, \frac{2}{3}, \frac{125}{27}\right) = (x + \frac{205}{54})^{2} \cdot (x + \frac{170}{27})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CentralBellCubicRefutation.bernoulli_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the rational parameters 2/3 and 125/27, the repeated factor is x+205/54.

**Theorem 1.11 (Bernoulli rational parameter identities).**

$$(\frac{2}{3})^{2} + \frac{1}{4} = (\frac{5}{6})^{2} \land \frac{\frac{125}{27}}{4} = 2 \cdot (\frac{5}{6})^{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CentralBellCubicRefutation.bernoulli_parameter_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both equalities hold in the rationals and exhibit the parameter 5/6 in the Bernoulli double-root certificate.

**Theorem 1.12 (Euler rational double-root refutation).**

$$(\exists y \in \mathbb{Q}, z \in \mathbb{Q},\; y = \frac{1}{2} \land \left(z = 8 \land \left((\forall x \in \mathbb{C},\; eulerCubic\left(x, ofReal\left(val\left(y\right)\right), ofReal\left(val\left(z\right)\right)\right) = 0 \Leftrightarrow (x = -7 \lor x = -10)) \land \left(\neg HasThreeDistinctRoots\left(x \mapsto eulerCubic\left(x, ofReal\left(val\left(y\right)\right), ofReal\left(val\left(z\right)\right)\right)\right)\right)\right)\right)) \land \left(-7 \ne -10 \land \left(\neg (\forall y \in \mathbb{R}, z \in \mathbb{R},\; HasThreeDistinctRoots\left(x \mapsto eulerCubic\left(x, ofReal\left(y\right), ofReal\left(z\right)\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CentralBellCubicRefutation.conjecture3_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the printed n = 3, lambda = 3 cubics, the Euler parameters y = 1/2 and z = 8 are rational and the entire complex zero set is {-7,-10}. These roots are unequal, so there are exactly two distinct solutions and there cannot be three. The last conjunct refutes the universal real-parameter reading of Conjecture 3 at this degree and lambda. It also refutes any universal-lambda reading that includes 3.

In both refutation formulas, val denotes Rat.cast : Rat -> Real and ofReal denotes Complex.ofReal : Real -> Complex. Thus the nested coercions in the rational witness and the single coercions in the universal clause are explicit. Every displayed division is field division.

Provenance correction: the atom bracket's lambda=1 is an orchestrator typo corrected by 评注 27.847 (PR #5860). This module refutes the paper's printed n = 3, lambda = 3 cubics; the existing 4.105 and 4.106 atoms remain the coverage targets.

The live proof extracts six times the degree-three coefficient of the finite generating-function jet with Euler prefactor 1-3t^2/8. It identifies the result with the expanded cubic, rewrites it as (x+z)^3-3(x+z)(y^2+3/4)+z/4, and proves the factorization (x+7)^2(x+10). Product-zero reasoning gives the complete root set. The finite-jet coefficient identity is kernel checked; an identity with the full infinite generating function is not asserted.

**Theorem 1.13 (Bernoulli rational double-root refutation).**

$$(\exists y \in \mathbb{Q}, z \in \mathbb{Q},\; y = \frac{2}{3} \land \left(z = \frac{125}{27} \land \left((\forall x \in \mathbb{C},\; bernoulliCubic\left(x, ofReal\left(val\left(y\right)\right), ofReal\left(val\left(z\right)\right)\right) = 0 \Leftrightarrow (x = -\frac{205}{54} \lor x = -\frac{170}{27})) \land \left(\neg HasThreeDistinctRoots\left(x \mapsto bernoulliCubic\left(x, ofReal\left(val\left(y\right)\right), ofReal\left(val\left(z\right)\right)\right)\right)\right)\right)\right)) \land \left(-\frac{205}{54} \ne -\frac{170}{27} \land \left(\neg (\forall y \in \mathbb{R}, z \in \mathbb{R},\; HasThreeDistinctRoots\left(x \mapsto bernoulliCubic\left(x, ofReal\left(y\right), ofReal\left(z\right)\right)\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CentralBellCubicRefutation.conjecture1_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the printed n = 3, lambda = 3 cubics, the Bernoulli parameters y = 2/3 and z = 125/27 are rational and the entire complex zero set is {-205/54,-170/27}. The inequality of these two roots and the absence of three distinct roots are both explicit. The last conjunct refutes the universal real-parameter reading of Conjecture 1 at this degree and lambda, hence any universal-lambda reading including 3.

The finite-jet prefactor is 1-t^2/8. The coefficient bridge gives (x+z)^3-3(x+z)(y^2+1/4)+z/4. Exact rational arithmetic then yields (x+205/54)^2(x+170/27), and the proof determines all complex zeros before excluding three pairwise distinct ones. As for the Euler case, the kernel statement concerns the printed cubic and the finite coefficient computation, not an infinite-series theorem.

## References

- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.HasThreeDistinctRoots`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.bernoulliCubic`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.bernoulli_coefficient_bridge`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.bernoulli_egf_coefficient`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.bernoulli_factorization`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.bernoulli_parameter_identities`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.conjecture1_refuted`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.conjecture3_refuted`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.egfJet`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.eulerCubic`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.euler_coefficient_bridge`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.euler_egf_coefficient`
- Truth anchor: `D5/S3/Arith/CentralBellCubicRefutation.euler_factorization`
