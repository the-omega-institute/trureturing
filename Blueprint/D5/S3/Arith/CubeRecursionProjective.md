# The projective cubic family

## Abstract

The cubic family has true degree three and is not conjugate to the cubic power map over the full complex projective group.

The information-escape audit remains unfinished. The eight same-author registration attempts remain declared_unresolved with null certificates; the missing compiler source bindings are disclosed in https://github.com/the-omega-institute/trureturing/issues/18969. The linked issue does not validate the registrations. Mathematical proof, canonical admission, independent acceptance and solve credit are distinct; no native acceptance or solve credit is claimed here.

N includes zero, C is the complex field, C[X] is its polynomial ring, RatFunc(C) is its rational-function field, and P is OnePoint(C). finite(z) is the canonical embedding C into P, and infinity is its remaining point. num and denom on a rational function mean its coprime polynomial numerator and monic denominator; natDegree is polynomial degree as a natural number. The function e is Mathlib's canonical equivalence from P to the projectivization of C squared; pair(x,y) denotes the class of the displayed nonzero vector. act is the actual projective PGL action, GL means invertible two by two complex matrices, mk is the quotient to PGL, and entry(m,i,j) is a matrix entry. The operator ite denotes if-then-else. Proof arguments witnessing a nonzero vector are implicit and irrelevant to its projective class.

The construction answers Section 7 question 2 under the explicit minimal uniform autonomous fixed-degree-family reading documented with the main result. These proofs are repository-derived; the source paper asks the question and does not contain this family. Global priority is UNDETERMINED.

**Definition 1.1 (numerator).**

$$\forall t: \mathbb{N}, \operatorname{numerator}\left(t\right) = X + \operatorname{C}\left(t\right)$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.numerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

X is the polynomial indeterminate, not a free complex variable. C(t) is the constant polynomial.

**Definition 1.2 (denominator).**

$$\forall t: \mathbb{N}, \operatorname{denominator}\left(t\right) = (X + \operatorname{C}\left(t\right) + 1)^{3} - \left(X + \operatorname{C}\left(t\right)\right)$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.denominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The affine denominator is monic cubic.

**Definition 1.3 (rationalMap).**

$$\forall t: \mathbb{N}, \operatorname{rationalMap}\left(t\right) = \frac{\operatorname{algebraMap}\left(\operatorname{numerator}\left(t\right)\right)}{\operatorname{algebraMap}\left(\operatorname{denominator}\left(t\right)\right)}$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.rationalMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

algebraMap is the canonical inclusion of C[X] into RatFunc(C).

**Definition 1.4 (mapDegree).**

$$\forall f: \operatorname{RatFunc}\left(\mathbb{C}\right), \operatorname{mapDegree}\left(f\right) = \operatorname{max}\left(\operatorname{natDegree}\left(\operatorname{num}\left(f\right)\right), \operatorname{natDegree}\left(\operatorname{denom}\left(f\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.mapDegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

This is the maximum of the reduced polynomial degrees, not RatFunc.intDegree, which is their difference.

**Definition 1.5 (q).**

$$\forall t: \mathbb{N}, \forall z: \mathbb{C}, \operatorname{q}\left(t, z\right) = (z + t + 1)^{3} - \left(z + t\right)$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

q is evaluation of the denominator in the finite chart.

**Definition 1.6 (projectiveMap).**

$$\forall t: \mathbb{N}, (\operatorname{projectiveMap}\left(t, \infty\right) = \operatorname{finite}\left(0\right)) \land (\forall z: \mathbb{C}, \operatorname{projectiveMap}\left(t, \operatorname{finite}\left(z\right)\right) = \operatorname{ite}\left(\operatorname{q}\left(t, z\right) = 0, \infty, \operatorname{finite}\left(\frac{z + t}{\operatorname{q}\left(t, z\right)}\right)\right))$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.projectiveMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

Every pole maps to infinity; infinity maps to zero.

**Definition 1.7 (homogeneousA).**

$$\forall t: \mathbb{N}, \forall x: \mathbb{C}, \forall y: \mathbb{C}, \operatorname{homogeneousA}\left(t, x, y\right) = \left(x + t \cdot y\right) \cdot (y)^{2}$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.homogeneousA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The first homogeneous form has degree three.

**Definition 1.8 (homogeneousB).**

$$\forall t: \mathbb{N}, \forall x: \mathbb{C}, \forall y: \mathbb{C}, \operatorname{homogeneousB}\left(t, x, y\right) = (x + \left(t + 1\right) \cdot y)^{3} - \left(x + t \cdot y\right) \cdot (y)^{2}$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.homogeneousB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The second homogeneous form has no common nonzero-coordinate zero with the first.

**Definition 1.9 (projectivePoint).**

$$\forall x: \mathbb{C}, \forall y: \mathbb{C}, ((x \neq 0) \lor (y \neq 0)) \implies (\operatorname{projectivePoint}\left(x, y\right) = \operatorname{inverse}\left(\operatorname{e}, \operatorname{pair}\left(x, y\right)\right))$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.projectivePoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The vector (x,y) is nonzero. inverse(e,pair(x,y)) means e inverse applied to that projective class.

**Definition 1.10 (homogeneousImage).**

$$\forall t: \mathbb{N}, \forall x: \mathbb{C}, \forall y: \mathbb{C}, ((x \neq 0) \lor (y \neq 0)) \implies (\operatorname{homogeneousImage}\left(t, x, y\right) = \operatorname{inverse}\left(\operatorname{e}, \operatorname{pair}\left(\operatorname{homogeneousA}\left(t, x, y\right), \operatorname{homogeneousB}\left(t, x, y\right)\right)\right))$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.homogeneousImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The internal nonvanishing proof covers y=0 and x+t*y=0 as well as ordinary finite points.

**Definition 1.11 (powerMap).**

$$(\operatorname{powerMap}\left(\infty\right) = \infty) \land (\forall z: \mathbb{C}, \operatorname{powerMap}\left(\operatorname{finite}\left(z\right)\right) = \operatorname{finite}\left((z)^{3}\right))$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.powerMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

This is z cubed extended to the entire complex projective line.

**Definition 1.12 (mobius).**

$$\forall g: \operatorname{PGL}\left(2, \mathbb{C}\right), \forall p: \operatorname{OnePoint}\left(\mathbb{C}\right), \operatorname{mobius}\left(g, p\right) = \operatorname{inverse}\left(\operatorname{e}, \operatorname{act}\left(g, \operatorname{e}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/CubeRecursionProjective.mobius` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

mobius is a genuine permutation transported from the PGL action, with group inverse acting as inverse permutation.

**Theorem 1.13 (map degree three).**

$$\forall t: \mathbb{N}, (\operatorname{natDegree}\left(\operatorname{num}\left(\operatorname{rationalMap}\left(t\right)\right)\right) = 1) \land ((\operatorname{natDegree}\left(\operatorname{denom}\left(\operatorname{rationalMap}\left(t\right)\right)\right) = 3) \land (\operatorname{mapDegree}\left(\operatorname{rationalMap}\left(t\right)\right) = 3))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CubeRecursionProjective.map_degree_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

A polynomial Bezout identity proves coprimality. The monic denominator fixes the reduced pair, of degrees one and three.

**Theorem 1.14 (homogeneous coordinates).**

$$\forall t: \mathbb{N}, \forall x: \mathbb{C}, \forall y: \mathbb{C}, ((x \neq 0) \lor (y \neq 0)) \implies (\operatorname{projectiveMap}\left(t, \operatorname{projectivePoint}\left(x, y\right)\right) = \operatorname{homogeneousImage}\left(t, x, y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CubeRecursionProjective.homogeneous_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The e-equivalence gives x/y in the finite chart and infinity when y=0. Direct algebra proves the equality, including denominator zeros.

**Theorem 1.15 (rational map semantics).**

$$\forall t: \mathbb{N}, (\operatorname{projectiveMap}\left(t, \infty\right) = \operatorname{finite}\left(0\right)) \land (\forall z: \mathbb{C}, \operatorname{projectiveMap}\left(t, \operatorname{finite}\left(z\right)\right) = \operatorname{ite}\left(\operatorname{eval}\left(\operatorname{denom}\left(\operatorname{rationalMap}\left(t\right)\right), z\right) = 0, \infty, \operatorname{finite}\left(\operatorname{eval}\left(\operatorname{rationalMap}\left(t\right), z\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CubeRecursionProjective.rational_map_semantics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The reduced rational-function numerator and denominator identify its evaluation with the same finite-point map. Poles and infinity are explicit.

**Theorem 1.16 (not conjugate).**

$$\forall t: \mathbb{N}, \forall g: \operatorname{PGL}\left(2, \mathbb{C}\right), \neg (\forall p: \operatorname{OnePoint}\left(\mathbb{C}\right), \operatorname{mobius}\left(g, \operatorname{projectiveMap}\left(t, \operatorname{mobius}\left(\operatorname{inv}\left(g\right), p\right)\right)\right) = \operatorname{powerMap}\left(p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CubeRecursionProjective.not_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The zero fibre is exactly {-t,infinity}. If two distinct points have the same image under z cubed, there is a third: for finite u,v take -u-v. The factorization of u cubed minus v cubed proves the third image and distinctness. A bijection preserves fibre cardinality, so conjugacy by any PGL element is impossible. No local critical-degree axiom or conditional normal form is used.

**Theorem 1.17 (mobius coordinates).**

$$\forall m: \operatorname{GL}\left(2, \mathbb{C}\right), (\operatorname{mobius}\left(\operatorname{mk}\left(m\right), \infty\right) = \operatorname{ite}\left(\operatorname{entry}\left(m, 1, 0\right) = 0, \infty, \operatorname{finite}\left(\frac{\operatorname{entry}\left(m, 0, 0\right)}{\operatorname{entry}\left(m, 1, 0\right)}\right)\right)) \land (\forall z: \mathbb{C}, \operatorname{mobius}\left(\operatorname{mk}\left(m\right), \operatorname{finite}\left(z\right)\right) = \operatorname{ite}\left(\operatorname{entry}\left(m, 1, 0\right) \cdot z + \operatorname{entry}\left(m, 1, 1\right) = 0, \infty, \operatorname{finite}\left(\frac{\operatorname{entry}\left(m, 0, 0\right) \cdot z + \operatorname{entry}\left(m, 0, 1\right)}{\operatorname{entry}\left(m, 1, 0\right) \cdot z + \operatorname{entry}\left(m, 1, 1\right)}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CubeRecursionProjective.mobius_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

Every complex PGL class has a GL representative by Mathlib's mk_surjective. These are the actual fractional-linear formulas for every invertible matrix, including its finite poles and infinity. The main result consumes both this theorem and the quotient surjectivity.

## References

- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.denominator`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.homogeneousA`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.homogeneousB`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.homogeneousImage`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.homogeneous_coordinates`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.mapDegree`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.map_degree_three`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.mobius`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.mobius_coordinates`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.not_conjugate`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.numerator`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.powerMap`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.projectiveMap`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.projectivePoint`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.q`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.rationalMap`
- Truth anchor: `D5/S3/Arith/CubeRecursionProjective.rational_map_semantics`
