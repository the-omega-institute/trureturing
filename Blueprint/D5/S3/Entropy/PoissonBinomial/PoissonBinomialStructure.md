# Poisson-binomial Structure

## Abstract

Finite Bernoulli-sum laws, removal of two coordinates, and majorization chains in the open unit cube.

**Definition 1.1 (The Bernoulli-sum law).**

$$\operatorname{pb}\left(c, k\right) = \sum_{A: \operatorname{card}\left(A\right)=k} \operatorname{w}\left(c, A\right)$$

*Formalization.* `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb` (`✓ std3`).

*Citation.* D. Monkman; J. Sirker (2023). *Symmetry-resolved entanglement: general considerations, calculation from correlation functions, and bounds for symmetry-protected topological phases*. DOI: [10.48550/arXiv.2307.05820](https://doi.org/10.48550/arXiv.2307.05820). URL: <https://arxiv.org/abs/2307.05820>.

*Commentary.*

For c : Fin M → ℝ, pb c k sums over all subsets A of Fin M of cardinality k. The weight w(c,A) is the product of c i over i in A times the product of 1−c i over i outside A. On the closed unit cube this is the law of the sum of independent Bernoulli variables. All cardinalities and indices are natural numbers; empty products are one.

**Definition 1.2 (Configurational entropy).**

$$\operatorname{F}\left(c\right) = \sum_{i} \operatorname{h}\left(\operatorname{c}\left(i\right)\right)- \sum_{k=0}^{M} \operatorname{negMulLog}\left(\operatorname{pb}\left(c, k\right)\right)$$

*Formalization.* `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.F` (`✓ std3`).

*Citation.* D. Monkman; J. Sirker (2023). *Symmetry-resolved entanglement: general considerations, calculation from correlation functions, and bounds for symmetry-protected topological phases*. DOI: [10.48550/arXiv.2307.05820](https://doi.org/10.48550/arXiv.2307.05820). URL: <https://arxiv.org/abs/2307.05820>.

*Commentary.*

Here h is Real.binEntropy, and Real.negMulLog x is −x log x with value zero at zero. The first sum ranges over Fin M and the second over 0 through M. Natural logarithms give nats. This is S−SN in Monkman and Sirker, Section 3.3. For independent coordinates it is also the Shannon conditional entropy of the coordinate vector given its sum: independence gives H(X)=Σ h(c i), and the sum N is a deterministic function of X, so H(X|N)=H(X)−H(N).

**Theorem 1.3 (Nonnegative masses).**

$$\operatorname{ClosedCube}\left(c\right) \Rightarrow 0\le\operatorname{pb}\left(c, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every dimension, closed-cube parameter vector and natural k, each summand is nonnegative.

**Theorem 1.4 (Total mass).**

$$\sum_{k=0}^{M} \operatorname{pb}\left(c, k\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb_sum_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite expansion of the product of c i+(1−c i) gives total mass one. The polynomial identity holds for arbitrary real parameters, including the empty vector.

**Theorem 1.5 (Permutation invariance).**

$$\operatorname{pb}\left(c\circ sigma, k\right) = \operatorname{pb}\left(c, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every permutation σ of Fin M, permuting the parameters preserves each mass. The coefficient of degree k in the product of (c i)X+(1−c i) represents pb c k.

**Definition 1.6 (The remaining coordinates).**

$$\operatorname{pbRest}\left(c, i, j, k\right) = \operatorname{pb}\left(\operatorname{zeroPair}\left(c, i, j\right), k\right)$$

*Formalization.* `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pbRest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

zeroPair denotes the two function updates setting coordinates i and j to zero. The resulting mass describes the sum of the remaining coordinates.

**Theorem 1.7 (Removal gives three-point convolution).**

$$\operatorname{pb}\left(c, k\right) = v0 \operatorname{r}\left(k\right)+v1 \operatorname{r1}\left(k\right)+v2 \operatorname{r2}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb_remove_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct i,j, put p=c i, q=c j and r=pbRest c i j. The three weights are v₀=(1−p)(1−q), v₁=p(1−q)+q(1−p), v₂=pq. The shifted r₋₁(k) is r(k−1) when 1≤k and zero otherwise; r₋₂ uses the corresponding guard 2≤k. These guards prevent truncated natural subtraction from assigning spurious boundary mass. The identity holds for arbitrary real parameters.

**Definition 1.8 (An interior T-transform).**

$$\operatorname{InteriorT}\left(x, y\right) = \operatorname{IsTTransform}\left(x, y\right)\land \operatorname{OpenCube}\left(x\right)\land \operatorname{OpenCube}\left(y\right)$$

*Formalization.* `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.InteriorT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OpenCube means every coordinate lies in (0,1). IsTTransform uses a convex combination of the vector and a transposition of two coordinates.

**Theorem 1.9 (A stepwise criterion).**

$$\operatorname{StepMonotone}\left(G\right)\land \operatorname{OpenCube}\left(c\right)\land \operatorname{OpenCube}\left(d\right)\land \operatorname{moreMixed}\left(d, c\right) \Rightarrow \operatorname{G}\left(c\right)\le\operatorname{G}\left(d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.le_of_interior_ttransform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

StepMonotone G means G x≤G y for every InteriorT x y. Applying this premise along the finite chain proves monotonicity under majorization for any real-valued G on Fin M → ℝ.

## References

- Truth anchor: `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.F`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.InteriorT`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.le_of_interior_ttransform`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pbRest`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb_nonneg`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb_perm`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb_remove_two`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.pb_sum_one`
- Dependency: [D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone](../../Geometry/AlphaGeometry/LogScalarCurvatureMonotone.md)
