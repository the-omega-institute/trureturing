# PairCurvatureInequality

## Abstract

Positivity and strict ratio growth for the two-coordinate curvature pair.

**Definition 1.1 (E).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), \forall (k : \mathbb{N}), E\left(r, z, k\right) = (\operatorname{MvPolynomial}. \operatorname{aeval}\left(z, (\operatorname{MvPolynomial}. \operatorname{esymm}\left((\operatorname{Fin}\left(r\right)), \mathbb{R}, k\right))\right))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

Evaluation of the elementary symmetric polynomial gives the elementary symmetric sum of the real coordinates.

**Definition 1.2 (P).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), \forall (k : \mathbb{N}), P\left(r, z, k\right) = (\operatorname{MvPolynomial}. \operatorname{aeval}\left(z, (\operatorname{MvPolynomial}. \operatorname{psum}\left((\operatorname{Fin}\left(r\right)), \mathbb{R}, k\right))\right))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

Evaluation of the power-sum polynomial gives the sum of the kth powers of the real coordinates.

**Lemma 1.3 (E_evalSum).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), \forall (k : \mathbb{N}), E\left(r, z, k\right) = \sum_{s \in \operatorname{Finset}. \operatorname{powersetCard}\left(k, ((\operatorname{Finset}. \operatorname{univ}) : (\operatorname{Finset}\left((\operatorname{Fin}\left(r\right))\right)))\right)} (\prod_{i \in s} (z\left(i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.E_evalSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The evaluated elementary symmetric polynomial is the sum of coordinate products over k-element subsets.

**Lemma 1.4 (P_evalSum).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), \forall (k : \mathbb{N}), P\left(r, z, k\right) = \sum_{i} ((z\left(i\right))^{k})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.P_evalSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The evaluated power-sum polynomial is the finite sum of kth powers.

**Lemma 1.5 (E_one_eq_sum).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), E\left(r, z, 1\right) = \sum_{i} (z\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.E_one_eq_sum` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The first elementary symmetric sum is the coordinate sum.

**Lemma 1.6 (newton2).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), P\left(r, z, 2\right) = ((E\left(r, z, 1\right)))^{2} - 2 \cdot E\left(r, z, 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.newton2` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The second Newton identity relates the square sum to the first two elementary symmetric sums.

**Lemma 1.7 (newton3).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), P\left(r, z, 3\right) = ((\sum_{i} (z\left(i\right))))^{3} - 3 \cdot (\sum_{i} (z\left(i\right))) \cdot E\left(r, z, 2\right) + 3 \cdot E\left(r, z, 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.newton3` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The third Newton identity expresses the cube sum through the coordinate sum and the second and third elementary symmetric sums.

**Lemma 1.8 (newton4).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), P\left(r, z, 4\right) = ((\sum_{i} (z\left(i\right))))^{4} - 4 \cdot ((\sum_{i} (z\left(i\right))))^{2} \cdot E\left(r, z, 2\right) + 2 \cdot ((E\left(r, z, 2\right)))^{2} + 4 \cdot (\sum_{i} (z\left(i\right))) \cdot E\left(r, z, 3\right) - 4 \cdot E\left(r, z, 4\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.newton4` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The fourth Newton identity expresses the fourth-power sum through the first four elementary symmetric sums.

**Definition 1.9 (pairT).**

$$\forall (u : \mathbb{R}), \forall (v : \mathbb{R}), \forall (B : \mathbb{R}), \operatorname{pairT}\left(u, v, B\right) = ((u)^{2} - 2 \cdot v + B)$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairT` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The quadratic power sum after separating two coordinates is u squared minus twice their product v, plus the rest square sum B.

**Definition 1.10 (pairN).**

$$\forall (u : \mathbb{R}), \forall (v : \mathbb{R}), \forall (A : \mathbb{R}), \forall (B : \mathbb{R}), \forall (E_{2} : \mathbb{R}), \forall (E_{3} : \mathbb{R}), \forall (E_{4} : \mathbb{R}), \operatorname{pairN}\left(u, v, A, B, E_{2}, E_{3}, E_{4}\right) = (v \cdot A + u \cdot E_{2} + E_{3} - 4 \cdot (v \cdot E_{2} + u \cdot E_{3} + E_{4}))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairN` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The elementary-symmetric curvature numerator is expressed through the pair sum u, pair product v and remaining elementary symmetric sums.

**Definition 1.11 (pairK).**

$$\forall (u : \mathbb{R}), \forall (v : \mathbb{R}), \forall (A : \mathbb{R}), \forall (B : \mathbb{R}), \forall (E_{2} : \mathbb{R}), \forall (E_{3} : \mathbb{R}), \forall (E_{4} : \mathbb{R}), \operatorname{pairK}\left(u, v, A, B, E_{2}, E_{3}, E_{4}\right) = ((A - 4 \cdot E_{2}) \cdot \operatorname{pairT}\left(u, v, B\right) + 4 \cdot \operatorname{pairN}\left(u, v, A, B, E_{2}, E_{3}, E_{4}\right))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

This polynomial controls the sign of curvature growth as the pair product increases at fixed pair sum.

**Definition 1.12 (pairR).**

$$\forall (u : \mathbb{R}), \forall (A : \mathbb{R}), \forall (B : \mathbb{R}), \forall (E_{2} : \mathbb{R}), \forall (E_{3} : \mathbb{R}), \forall (E_{4} : \mathbb{R}), \forall (v : \mathbb{R}), \operatorname{pairR}\left(u, A, B, E_{2}, E_{3}, E_{4}, v\right) = ((2 \cdot \operatorname{pairN}\left(u, v, A, B, E_{2}, E_{3}, E_{4}\right)) / ((\operatorname{pairT}\left(u, v, B\right))^{2}))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairR` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The pair curvature is twice pairN divided by the square of pairT.

**Definition 1.13 (mixProduct).**

$$\forall (a : \mathbb{R}), \forall (b : \mathbb{R}), \forall (t : \mathbb{R}), \operatorname{mixProduct}\left(a, b, t\right) = (((1 - t) \cdot a + t \cdot b) \cdot (t \cdot a + (1 - t) \cdot b))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.mixProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

This is the product of the two coordinates after convex mixing with their swap.

**Theorem 1.14 (coordinateB_le_sum_sq).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), (\forall i , (0 \le z\left(i\right))) \Rightarrow (P\left(r, z, 2\right) \le ((\sum_{i} (z\left(i\right))))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.coordinateB_le_sum_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

For nonnegative coordinates, the square sum is bounded above by the square of the coordinate sum.

**Theorem 1.15 (coordinateB_pos).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), (\exists i , (0 < z\left(i\right))) \Rightarrow (0 < P\left(r, z, 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.coordinateB_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

A positive coordinate makes the square sum strictly positive.

**Theorem 1.16 (key_pos).**

$$\forall (u : \mathbb{R}), \forall (v : \mathbb{R}), \forall (B : \mathbb{R}), \forall (q : \mathbb{R}), (0 \le q) \Rightarrow ((0 < u) \Rightarrow ((u < 1) \Rightarrow ((0 < v) \Rightarrow ((v \le ((u)^{2}) / (4)) \Rightarrow ((0 < B) \Rightarrow ((B \le ((1 - u))^{2}) \Rightarrow (q + u \cdot (3 - 4 \cdot u) \cdot B + (u)^{2} \cdot (1 - u) + v \cdot (4 \cdot B - 4 \cdot (u)^{2} + 6 \cdot u - 2) > 0)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.key_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

Separating u at one half and bounding the coefficient of v proves the displayed strict estimate.

**Theorem 1.17 (pairT_pos).**

$$\forall (u : \mathbb{R}), \forall (v : \mathbb{R}), \forall (B : \mathbb{R}), (0 < u) \Rightarrow ((v \le ((u)^{2}) / (4)) \Rightarrow ((0 < B) \Rightarrow (0 < \operatorname{pairT}\left(u, v, B\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairT_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The product bound v≤u²/4 and positivity of B keep the quadratic denominator positive.

**Theorem 1.18 (ratio_strict_increase).**

$$\forall (u : \mathbb{R}), \forall (A : \mathbb{R}), \forall (B : \mathbb{R}), \forall (E_{2} : \mathbb{R}), \forall (E_{3} : \mathbb{R}), \forall (E_{4} : \mathbb{R}), \forall (v_{1} : \mathbb{R}), \forall (v_{2} : \mathbb{R}), (v_{1} < v_{2}) \Rightarrow ((0 < \operatorname{pairT}\left(u, v_{1}, B\right)) \Rightarrow ((0 < \operatorname{pairT}\left(u, v_{2}, B\right)) \Rightarrow ((0 < \operatorname{pairK}\left(u, v_{1}, A, B, E_{2}, E_{3}, E_{4}\right)) \Rightarrow ((0 < \operatorname{pairK}\left(u, v_{2}, A, B, E_{2}, E_{3}, E_{4}\right)) \Rightarrow ((2 \cdot \operatorname{pairN}\left(u, v_{1}, A, B, E_{2}, E_{3}, E_{4}\right)) / ((\operatorname{pairT}\left(u, v_{1}, B\right))^{2}) < (2 \cdot \operatorname{pairN}\left(u, v_{2}, A, B, E_{2}, E_{3}, E_{4}\right)) / ((\operatorname{pairT}\left(u, v_{2}, B\right))^{2}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.ratio_strict_increase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

Positivity of pairK at both endpoints and of both denominators gives strict growth of the rational curvature ratio.

**Theorem 1.19 (coordinate_key_pos).**

$$\forall (r : \mathbb{N}), \forall (z : (\operatorname{Fin}\left(r\right)) \to (\mathbb{R})), \forall (u : \mathbb{R}), \forall (v : \mathbb{R}), \forall (A : \mathbb{R}), \forall (B : \mathbb{R}), \forall (E_{2} : \mathbb{R}), \forall (E_{3} : \mathbb{R}), \forall (E_{4} : \mathbb{R}), (A = 1 - u) \Rightarrow ((A = \sum_{i} (z\left(i\right))) \Rightarrow ((B = P\left(r, z, 2\right)) \Rightarrow ((E_{2} = E\left(r, z, 2\right)) \Rightarrow ((E_{3} = E\left(r, z, 3\right)) \Rightarrow ((E_{4} = E\left(r, z, 4\right)) \Rightarrow ((\exists i , (0 < z\left(i\right))) \Rightarrow ((0 < u) \Rightarrow ((u < 1) \Rightarrow ((0 < v) \Rightarrow ((v \le ((u)^{2}) / (4)) \Rightarrow ((B \le ((1 - u))^{2}) \Rightarrow (0 < \operatorname{pairK}\left(u, v, A, B, E_{2}, E_{3}, E_{4}\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.coordinate_key_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

The Newton identities and the nonnegative square decomposition put the remaining coordinates into the strict pair estimate.

**Theorem 1.20 (ttransform_product_increase).**

$$\forall (a : \mathbb{R}), \forall (b : \mathbb{R}), \forall (lam : \mathbb{R}), (0 < lam) \Rightarrow ((lam < 1) \Rightarrow ((a \ne b) \Rightarrow (a \cdot b < (lam \cdot a + (1 - lam) \cdot b) \cdot ((1 - lam) \cdot a + lam \cdot b))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.ttransform_product_increase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Acknowledgement.* Mathlib contributors (2026). *Mathlib symmetric polynomial definitions and Newton identities*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean>.

*Commentary.*

Interior mixing of two unequal coordinates strictly increases their product.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.E`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.E_evalSum`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.E_one_eq_sum`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.P`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.P_evalSum`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.coordinateB_le_sum_sq`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.coordinateB_pos`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.coordinate_key_pos`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.key_pos`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.mixProduct`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.newton2`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.newton3`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.newton4`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairK`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairN`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairR`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairT`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.pairT_pos`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.ratio_strict_increase`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.ttransform_product_increase`
