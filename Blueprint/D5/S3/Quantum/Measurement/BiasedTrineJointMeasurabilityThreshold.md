# The exact compatibility threshold for biased trine qubit measurements

## Abstract

The biased trine qubit family has triplewise joint-measurability threshold min(2/3, 1 - |b|).

**Definition 1.1 (The three trine directions).**

$$\forall (i: \operatorname{Fin}\left(3\right)), ((\operatorname{D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.trineDir}\left(i\right): \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)) = \operatorname{WithLp.toLp}\left(2, ![![\frac{-1}{2}, 0, \frac{\operatorname{Real.sqrt}\left(3\right)}{2}], ![\frac{-1}{2}, 0, \frac{-\operatorname{Real.sqrt}\left(3\right)}{2}], ![1, 0, 0]]\left(i\right)\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.trineDir` (`✓ std3`).

*Citation.* Shiv Akshar Yadavalli; Nikola Andrejic; Ravi Kunjwal (2024). *Qualitative equivalence between incompatibility and Bell nonlocality*. DOI: [10.1103/PhysRevA.110.L060201](https://doi.org/10.1103/PhysRevA.110.L060201). URL: <https://arxiv.org/abs/2008.10100v3>.

*Commentary.*

The three unit vectors lie in the xz plane at angles 2π/3, 4π/3 and 2π. The index i in Fin 3 corresponds to the source's index i + 1. Their coordinates are ordered x, y, z, and WithLp.toLp equips the coordinate functions with the Euclidean norm. These are the directions in Supplemental Material TeX lines 117–118; their explicit coordinates also fix the index order.

**Definition 1.2 (The common-bias binary effects).**

$$\forall (b: \mathbb{R}), (\forall (\mathit{eta}: \mathbb{R}), (\forall (k: \operatorname{Fin}\left(3\right)), (\forall (x: \operatorname{Bool}), ((\operatorname{D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.trineEffect}\left(b, \mathit{eta}, k, x\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)) = ((\frac{1}{2}: \mathbb{C})) \cdot (\operatorname{D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB}\left(1 + \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(x\right) \cdot b, (\mathit{eta} \cdot \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(x\right)) \cdot (\operatorname{D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.trineDir}\left(k\right))\right))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.trineEffect` (`✓ std3`).

*Citation.* Shiv Akshar Yadavalli; Nikola Andrejic; Ravi Kunjwal (2024). *Qualitative equivalence between incompatibility and Bell nonlocality*. DOI: [10.1103/PhysRevA.110.L060201](https://doi.org/10.1103/PhysRevA.110.L060201). URL: <https://arxiv.org/abs/2008.10100v3>.

*Commentary.*

For bias b and purity η, each direction k gives two complex two-by-two matrices. The parameter eta in the formulas denotes η. The real sign sgn x is +1 for true and −1 for false. The function scalarB(t,a) is t times the identity plus the Pauli matrix expansion of a, so the displayed expression is precisely the first family in Supplemental Material TeX line 115. The outer scalar one half belongs to the complex numbers; the bias and Bloch-vector coefficients are real. On the domain −1 ≤ b ≤ 1, 0 ≤ η ≤ 1 and |b| ≤ 1 − η, these are binary POVMs.

**Definition 1.3 (A common eight-outcome measurement).**

$$\forall (b: \mathbb{R}), (\forall (\mathit{eta}: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.TriplewiseJointlyMeasurable}\left(b, \mathit{eta}\right)) \Leftrightarrow (\operatorname{D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence.FamilyJointlyMeasurable}\left(\operatorname{D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.trineEffect}\left(b, \mathit{eta}\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.TriplewiseJointlyMeasurable` (`✓ std3`).

*Citation.* Shiv Akshar Yadavalli; Nikola Andrejic; Ravi Kunjwal (2024). *Qualitative equivalence between incompatibility and Bell nonlocality*. DOI: [10.1103/PhysRevA.110.L060201](https://doi.org/10.1103/PhysRevA.110.L060201). URL: <https://arxiv.org/abs/2008.10100v3>.

*Commentary.*

Triplewise joint measurability means that one POVM indexed by the eight functions Fin 3 → Bool has each of the three binary measurements as a marginal. Thus its matrices G(s) are positive semidefinite, sum to the identity, and satisfy ∑ over s with s(k) = x of G(s) = trineEffect(b,η,k,x) for every k and x. This is the existence condition for the triplewise joint POVM in Supplemental Material TeX lines 131 and 147–150.

**Definition 1.4 (The piecewise threshold).**

$$\forall (b: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.trineThreshold}\left(b\right): \mathbb{R}) = \operatorname{ite}\left(b < \frac{-1}{3}, 1 + b, \operatorname{ite}\left(b \le \frac{1}{3}, \frac{2}{3}, 1 - b\right)\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.trineThreshold` (`✓ std3`).

*Citation.* Shiv Akshar Yadavalli; Nikola Andrejic; Ravi Kunjwal (2024). *Qualitative equivalence between incompatibility and Bell nonlocality*. DOI: [10.1103/PhysRevA.110.L060201](https://doi.org/10.1103/PhysRevA.110.L060201). URL: <https://arxiv.org/abs/2008.10100v3>.

*Commentary.*

The function is 1 + b below −1/3, is 2/3 throughout the closed interval [−1/3,1/3], and is 1 − b above 1/3. These are the three expressions in Supplemental Material TeX lines 151–158. The definition gives a real value for every real b; the compatibility theorem concerns the stated physical domain.

**Lemma 1.5 (A sum over the eight Boolean strings).**

$$\forall (A: \operatorname{Type}*), (\forall (inst: \operatorname{AddCommMonoid}\left(A\right)), (\forall (f: ((\operatorname{Fin}\left(3\right)) \to (\operatorname{Bool})) \to (A)), (\sum_{s: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Bool})} f\left(s\right) = f\left(![\operatorname{false}, \operatorname{false}, \operatorname{false}]\right) + f\left(![\operatorname{false}, \operatorname{false}, \operatorname{true}]\right) + f\left(![\operatorname{false}, \operatorname{true}, \operatorname{false}]\right) + f\left(![\operatorname{false}, \operatorname{true}, \operatorname{true}]\right) + f\left(![\operatorname{true}, \operatorname{false}, \operatorname{false}]\right) + f\left(![\operatorname{true}, \operatorname{false}, \operatorname{true}]\right) + f\left(![\operatorname{true}, \operatorname{true}, \operatorname{false}]\right) + f\left(![\operatorname{true}, \operatorname{true}, \operatorname{true}]\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.sum_strings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any type A in any universe with an additive commutative monoid structure, the sum of f over all functions Fin 3 → Bool is the displayed eight-term sum. The coordinates are ordered 0, 1, 2, with false before true in each coordinate.

**Theorem 1.6 (The exact triplewise joint-measurability criterion).**

$$\forall (b: \mathbb{R}), (\forall (\mathit{eta}: \mathbb{R}), ((-1 \le b) \to ((b \le 1) \to ((0 \le \mathit{eta}) \to ((\mathit{eta} \le 1) \to ((\left|b\right| \le 1 - \mathit{eta}) \to ((\operatorname{D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.TriplewiseJointlyMeasurable}\left(b, \mathit{eta}\right)) \Leftrightarrow (\mathit{eta} \le \operatorname{D5.S3.Quantum.Measurement.BiasedTrineJointMeasurabilityThreshold.trineThreshold}\left(b\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.result` (`✓ std3`). ∎

*Resolves.* `Problems/yadavalli-andrejic-kunjwal-2024-biased-trine-joint-measurability` (proved) by `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yadavalli-andrejic-kunjwal-2024-biased-trine-joint-measurability","declaration_gid":"D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shiv Akshar Yadavalli; Nikola Andrejic; Ravi Kunjwal (2024). *Qualitative equivalence between incompatibility and Bell nonlocality*. DOI: [10.1103/PhysRevA.110.L060201](https://doi.org/10.1103/PhysRevA.110.L060201). URL: <https://arxiv.org/abs/2008.10100v3>.

*Commentary.*

Write nₖ = trineDir(k) and S(t,a) = scalarB(t,a) = tI + a·σ. The explicit coordinates agree with the cosine and sine expressions at angles 2(k + 1)π/3. They give ‖nₖ‖ = 1 and ∑ₖ nₖ = 0. For every sign string s, the vector aₛ = ∑ₖ sgn(s(k))nₖ is zero when all signs agree and is either 2nⱼ or −2nⱼ otherwise. Consequently ‖aₛ‖ ≤ 2.

The map (t,a) ↦ S(t,a) is injective: the real diagonal entries determine t and the z coordinate, while the real and imaginary parts of the upper-right entry determine the x and y coordinates. Also S(1,0) = I, and an effect has scalar coordinate (1 + sgn(x)b)/2 and vector coordinate (η sgn(x)/2)nₖ.

Suppose a common parent G exists. Decompose each Hermitian matrix as G(s) = S(qₛ,rₛ), with qₛ = Re(trace(G(s)))/2 and rₛ equal to one half of its Bloch vector. The positivity criterion for S gives ‖rₛ‖ ≤ qₛ. Additivity of S and injectivity of its coordinates turn ∑ₛ G(s) = I into ∑ₛ qₛ = 1. Applying the same coordinate comparison to each marginal gives ∑ over s with s(k) = x of rₛ = (η sgn(x)/2)nₖ. Subtracting the false marginal from the true marginal yields ∑ₛ sgn(s(k))rₛ = ηnₖ.

Interchange the finite sums and take real inner products with the unit vectors nₖ. The marginal identities imply ∑ₛ ⟨aₛ,rₛ⟩ = 3η. Cauchy–Schwarz and the bound on aₛ give 3η ≤ ∑ₛ 2‖rₛ‖ ≤ ∑ₛ 2qₛ = 2. Together with the assumed |b| ≤ 1 − η, this proves η ≤ trineThreshold(b) in all three branches.

For the converse, enumerate the eight sign strings. For each k let mₖ be the string with its only false entry at k, and let pₖ be its pointwise complement. Given real c,d,u,v,e,f, assign S(c,−unₖ) to mₖ, S(d,vnₖ) to pₖ, S(e,0) to the all-true string and S(f,0) to the all-false string. The sum of these matrices is S(3c + 3d + e + f,0). The true marginal at k is S(2c + d + e,(u + v)nₖ), and the false marginal is S(c + 2d + f,−(u + v)nₖ). These identities follow by expanding the eight matrices and their entries.

The positivity criterion makes all eight matrices positive semidefinite whenever |u| ≤ c, |v| ≤ d, 0 ≤ e and 0 ≤ f. The equations 2c + d + e = (1 + b)/2, c + 2d + f = (1 − b)/2 and u + v = η/2 then give the required marginals. Adding the first two equations gives 3c + 3d + e + f = 1, so their total is I. Thus these inequalities and equations suffice to construct a common parent.

When −1/3 ≤ b ≤ 1/3 and 0 ≤ η ≤ 2/3, take c = (1 + 3b)/6, d = (1 − 3b)/6, u = c(3η/2), v = d(3η/2), e = f = 0. Here c,d ≥ 0 and 0 ≤ 3η/2 ≤ 1, so |u| ≤ c and |v| ≤ d; the three marginal equations follow by substitution.

When b ≥ 1/3 and 0 ≤ η ≤ 1 − b, take c = (1 − b)/2, d = 0, u = η/2, v = 0, e = (3b − 1)/2, f = 0. When b ≤ −1/3 and 0 ≤ η ≤ 1 + b, take c = 0, d = (1 + b)/2, u = 0, v = η/2, e = 0, f = (−1 − 3b)/2. Each choice satisfies the positivity inequalities and the three marginal equations.

Finally, expand the definition of trineThreshold in the inequality η ≤ trineThreshold(b). Its first branch uses the negative-bias construction, its second uses the central construction, and its last uses the positive-bias construction. Both endpoints −1/3 and 1/3 belong to the central branch. This proves sufficiency and completes the equivalence on the full stated domain.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.TriplewiseJointlyMeasurable`
- Truth anchor: `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.result`
- Truth anchor: `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.sum_strings`
- Truth anchor: `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.trineDir`
- Truth anchor: `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.trineEffect`
- Truth anchor: `D5/S3/Quantum/Measurement/BiasedTrineJointMeasurabilityThreshold.trineThreshold`
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](FourQubitParentConstruction.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence](../QuantumChannels/HeisenbergChannelCompressionEquivalence.md)
