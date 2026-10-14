# Geronimus

## Abstract

Finite Riesz moments, orthogonal Laurent polynomials and scale-four projection identities.

**Definition 1.1 (caratheodory).**

$$\operatorname{caratheodory} = \operatorname{PowerSeries.mk} \operatorname{fun} (n : \mathbb{N}) \mapsto \operatorname{if} n = 0 \operatorname{then} 1 \operatorname{else} 2 \cdot \operatorname{Rat.cast}\left((\operatorname{rieszMoment} \operatorname{Nat.cast}\left(n\right))\right)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Geronimus.caratheodory` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “Given a measure μ on ∂D, the Carathéodory and Schur functions are defined as follows.” The real moments give the Carathéodory series F(z)=1+2∑ₙ≥₁μₙzⁿ, Section 2, arXiv PDF p. 2. PowerSeries.mk specifies every coefficient.

**Definition 1.2 (schur0).**

$$\operatorname{schur0} = \operatorname{D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail} (\operatorname{fun} (k : \mathbb{N}) \mapsto (\operatorname{PowerSeries.coeff} k) ((\operatorname{caratheodory} - 1) \cdot (\operatorname{caratheodory} + 1)^{-1})) 1$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Geronimus.schur0` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “Given a measure μ on ∂D, the Carathéodory and Schur functions are defined as follows.” Section 2 defines f(z)=z⁻¹(F(z)−1)/(F(z)+1). Removal of the vanishing constant coefficient is a coefficient shift after inversion of the unit denominator; PowerSeries.X has no multiplicative inverse in this ring.

**Definition 1.3 (schurStep).**

$$\forall (f : PowerSeries \mathbb{R}) , \operatorname{schurStep} f = \operatorname{D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail} (\operatorname{fun} (k : \mathbb{N}) \mapsto (\operatorname{PowerSeries.coeff} k) ((f - \operatorname{PowerSeries.C} (\operatorname{PowerSeries.constantCoeff} f)) \cdot (1 - \operatorname{PowerSeries.C} (\operatorname{PowerSeries.constantCoeff} f) \cdot f)^{-1})) 1$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Geronimus.schurStep` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “Then, the Verblunsky parameters αₖ are given by the following algorithm.” The Schur algorithm removes f(0) and divides by 1−f(0)f before shifting coefficients. The strict Verblunsky bound makes the denominator a unit.

**Definition 1.4 (schurSeq).**

$$\begin{aligned}\operatorname{schurSeq} 0 = \operatorname{schur0}\\\forall (k : \mathbb{N}) , \operatorname{schurSeq} (k + 1) = \operatorname{schurStep} (\operatorname{schurSeq} k)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Geronimus.schurSeq` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “where f₀(z) = f(z).” The initial function is schur0 and each successor is the Schur transform of the preceding function.

**Definition 1.5 (alpha).**

$$\forall (k : \mathbb{N}) , \operatorname{alpha} k = \operatorname{PowerSeries.constantCoeff} (\operatorname{schurSeq} k)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Geronimus.alpha` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “Then, the Verblunsky parameters αₖ are given by the following algorithm.” The Schur parameter is the constant coefficient of the kth Schur function.

**Theorem 1.6 (polynomial expansion).**

$$\forall (n : \mathbb{N}) \{p : LaurentPolynomial \mathbb{R}\} , p \in \operatorname{polyWindow} n \to p = \sum k \in \operatorname{Finset.range} (n + 1) , (\operatorname{coeffLM} \operatorname{Nat.cast}\left(k\right)) p \cdot \operatorname{LaurentPolynomial.T} \operatorname{Nat.cast}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/Geronimus.polynomial_expansion` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, a real Laurent polynomial in polyWindow n equals the sum of the monomials at exponents zero through n weighted by its corresponding coefficients.

**Theorem 1.7 (schur equals gram).**

$$\forall (n : \mathbb{N}) , \operatorname{alpha} n = \operatorname{verblunsky} n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/Geronimus.schur_equals_gram` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, the nth Schur parameter alpha n equals the Verblunsky coefficient verblunsky n obtained from Gram-Schmidt orthogonalization.

## References

- Truth anchor: `D5/S3/Quantum/Walks/CMV/Geronimus.alpha`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Geronimus.caratheodory`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Geronimus.polynomial_expansion`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Geronimus.schur0`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Geronimus.schurSeq`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Geronimus.schurStep`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Geronimus.schur_equals_gram`
- Dependency: [D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries](../../../../S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.md)
- Dependency: [D5/S3/Quantum/Walks/CMV/SzegoRecurrence](SzegoRecurrence.md)
