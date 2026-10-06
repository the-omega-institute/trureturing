# The within-DOF minimum clause of equipartition duality fails

## Abstract

At two degrees of freedom, a nonuniform phase density has the same joint action marginal as its uniform-phase product comparator and strictly smaller uncertainty in both degrees of freedom.

Real.Angle is the quotient AddCircle(2*pi), with angular volume of mass 2*pi. The action reference measure action is Lebesgue measure restricted to strictly positive reals. TorusOne is Real.Angle times the reals, TorusTwo is its square, and CartesianTwo is the square of a real coordinate pair. torusBase is angular volume times action; torusFullBase is its square. Cartesian volume is the standard product Lebesgue measure. The first Bool index selects the degree of freedom; the second selects q for false and p for true. Pair, fst and snd below denote ordered pairing and projections. integral, integralNN, ae, and withDensity use their indicated measures; ofReal is the nonnegative extended-real embedding. Function spaces and products are ordinary function and Cartesian product types.

**Definition 1.1 (The action-angle source map).**

$$\forall z \in TorusOne,\; \operatorname{PsiA}\left(z\right) = \operatorname{pair}\left(\operatorname{sqrt}\left(2 \cdot \operatorname{snd}\left(z\right)\right) \cdot \operatorname{sin}\left(\operatorname{fst}\left(z\right)\right), \operatorname{sqrt}\left(2 \cdot \operatorname{snd}\left(z\right)\right) \cdot \operatorname{cos}\left(\operatorname{fst}\left(z\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.PsiA` (`✓ std3`).

*Citation.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

The sine and cosine are those of the quotient angle. PsiA2 applies PsiA independently to the two coordinate pairs. R2(q,p)=q^2+p^2; radialAction takes R2/2 in each degree of freedom, and actionProjection takes the two action coordinates.

**Definition 1.2 (Covariance of the actual Cartesian coordinates).**

$$\forall mu \in \operatorname{Measure}\left(CartesianTwo\right),\; \forall i \in \operatorname{Product}\left(Bool, Bool\right),\; \forall k \in \operatorname{Product}\left(Bool, Bool\right),\; \operatorname{actualCovariance}\left(mu\right)\left(i, k\right) = \operatorname{covariance}\left(\operatorname{actualCoordinate}\left(i\right), \operatorname{actualCoordinate}\left(k\right), mu\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actualCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Covariance is the integral of the centered product under the actual law. No covariance matrix is prescribed as a hypothesis.

**Definition 1.3 (Within-DOF uncertainty).**

$$\forall mu \in \operatorname{Measure}\left(CartesianTwo\right),\; \forall j \in Bool,\; \operatorname{actualUncertainty}\left(mu, j\right) = \operatorname{sqrt}\left(\operatorname{det}\left(\operatorname{covarianceBlock}\left(mu, j\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actualUncertainty` (`✓ std3`).

*Citation.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

covarianceBlock(mu,j) is the two by two q,p principal block of actualCovariance(mu), in that order. The uncertainty is its determinant's nonnegative square root, as in Theorem 3.16.

**Definition 1.4 (The normalized Cartesian density law).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \operatorname{cartesianLaw}\left(F\right) = \operatorname{withDensity}\left(volume, \operatorname{fun} x \mapsto {\operatorname{ofReal}\left(F\left(x\right)\right)}\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.cartesianLaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Normalization and nonnegativity are requirements of sourceState; the density law itself is defined for every real-valued function.

**Definition 1.5 (Density pulled back through the source map).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \forall z \in TorusTwo,\; \operatorname{sourcePullback}\left(F, z\right) = F\left(\operatorname{PsiA2}\left(z\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourcePullback` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

sourceTorusLaw(F) is torusFullBase.withDensity(ofReal(sourcePullback(F))). It uses the actual quotient-angle source map.

**Definition 1.6 (Cartesian differential entropy).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \operatorname{sourceEntropy}\left(F\right) = -\operatorname{integral}\left(volume, \operatorname{fun} x \mapsto {F\left(x\right) \cdot \operatorname{log}\left(F\left(x\right)\right)}\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourceEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Entropy uses the natural logarithm. sourceUncertainty(F,j) is actualUncertainty(cartesianLaw(F),j). The finite integrals and the torus-to-Cartesian entropy identity are certified in sourceState.

**Definition 1.7 (A joint action density).**

$$\forall r \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right) \to \mathbb{R},\; \operatorname{actionDensity}\left(r\right) \Leftrightarrow {{\operatorname{Measurable}\left(r\right)} \land {{\forall J \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right),\; 0 \le r\left(J\right)} \land {\operatorname{integralNN}\left(\operatorname{prod}\left(action, action\right), \operatorname{fun} J \mapsto {\operatorname{ofReal}\left(r\left(J\right)\right)}\right) = 1}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actionDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

actionLaw(r) is the action product measure weighted by ofReal(r). oneActionDensity is the same measurable, nonnegative, unit-mass condition for one action coordinate.

**Definition 1.8 (Finite-entropy states with their source realization).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \operatorname{sourceState}\left(F\right) \Leftrightarrow {{\operatorname{Measurable}\left(F\right)} \land {{\forall x \in CartesianTwo,\; 0 \le F\left(x\right)} \land {{\operatorname{IsProbabilityMeasure}\left(\operatorname{cartesianLaw}\left(F\right)\right)} \land {{\operatorname{Integrable}\left(\operatorname{fun} x \mapsto {F\left(x\right) \cdot \operatorname{log}\left(F\left(x\right)\right)}, volume\right)} \land {{\forall i \in \operatorname{Product}\left(Bool, Bool\right),\; \operatorname{MemLp}\left(\operatorname{actualCoordinate}\left(i\right), 2, \operatorname{cartesianLaw}\left(F\right)\right)} \land {{\operatorname{PosDef}\left(\operatorname{actualCovariance}\left(\operatorname{cartesianLaw}\left(F\right)\right)\right)} \land {{\operatorname{Integrable}\left(\operatorname{fun} x \mapsto {\operatorname{sourcePullback}\left(F, x\right) \cdot \operatorname{log}\left(\operatorname{sourcePullback}\left(F, x\right)\right)}, torusFullBase\right)} \land {{\operatorname{integral}\left(torusFullBase, \operatorname{fun} x \mapsto {\operatorname{sourcePullback}\left(F, x\right) \cdot \operatorname{log}\left(\operatorname{sourcePullback}\left(F, x\right)\right)}\right) = \operatorname{integral}\left(volume, \operatorname{fun} x \mapsto {F\left(x\right) \cdot \operatorname{log}\left(F\left(x\right)\right)}\right)} \land {\operatorname{map}\left(PsiA2, \operatorname{sourceTorusLaw}\left(F\right)\right) = \operatorname{cartesianLaw}\left(F\right)}}}}}}}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourceState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

The density is Borel measurable, pointwise nonnegative and normalized on Cartesian volume. Every one of its four Cartesian coordinates belongs to L2, and its full four by four actual covariance is positive definite. Both entropy integrands are integrable; their integrals agree, and PsiA2 pushes the actual source law to the Cartesian density law. These extra certificates restrict the universal comparison and are all established for the counterexample.

**Definition 1.9 (The same joint marginal in both representations).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \forall G \in CartesianTwo \to \mathbb{R},\; \forall r \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right) \to \mathbb{R},\; \operatorname{commonActionMarginal}\left(F, G, r\right) \Leftrightarrow {{\operatorname{ae}\left(\operatorname{prod}\left(action, action\right), \operatorname{fun} J \mapsto {{\operatorname{Integrable}\left(\operatorname{fun} ts \mapsto {\operatorname{sourcePullback}\left(F, \operatorname{pair}\left(\operatorname{pair}\left(\operatorname{fst}\left(ts\right), \operatorname{fst}\left(J\right)\right), \operatorname{pair}\left(\operatorname{snd}\left(ts\right), \operatorname{snd}\left(J\right)\right)\right)\right)}, volume\right)} \land {\operatorname{integral}\left(volume, \operatorname{fun} ts \mapsto {\operatorname{sourcePullback}\left(F, \operatorname{pair}\left(\operatorname{pair}\left(\operatorname{fst}\left(ts\right), \operatorname{fst}\left(J\right)\right), \operatorname{pair}\left(\operatorname{snd}\left(ts\right), \operatorname{snd}\left(J\right)\right)\right)\right)}\right) = r\left(J\right)}}\right)} \land {{\operatorname{ae}\left(\operatorname{prod}\left(action, action\right), \operatorname{fun} J \mapsto {{\operatorname{Integrable}\left(\operatorname{fun} ts \mapsto {\operatorname{sourcePullback}\left(G, \operatorname{pair}\left(\operatorname{pair}\left(\operatorname{fst}\left(ts\right), \operatorname{fst}\left(J\right)\right), \operatorname{pair}\left(\operatorname{snd}\left(ts\right), \operatorname{snd}\left(J\right)\right)\right)\right)}, volume\right)} \land {\operatorname{integral}\left(volume, \operatorname{fun} ts \mapsto {\operatorname{sourcePullback}\left(G, \operatorname{pair}\left(\operatorname{pair}\left(\operatorname{fst}\left(ts\right), \operatorname{fst}\left(J\right)\right), \operatorname{pair}\left(\operatorname{snd}\left(ts\right), \operatorname{snd}\left(J\right)\right)\right)\right)}\right) = r\left(J\right)}}\right)} \land {{\operatorname{map}\left(actionProjection, \operatorname{sourceTorusLaw}\left(F\right)\right) = \operatorname{actionLaw}\left(r\right)} \land {{\operatorname{map}\left(actionProjection, \operatorname{sourceTorusLaw}\left(G\right)\right) = \operatorname{actionLaw}\left(r\right)} \land {{\operatorname{map}\left(radialAction, \operatorname{cartesianLaw}\left(F\right)\right) = \operatorname{actionLaw}\left(r\right)} \land {\operatorname{map}\left(radialAction, \operatorname{cartesianLaw}\left(G\right)\right) = \operatorname{actionLaw}\left(r\right)}}}}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.commonActionMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

For almost every positive action pair J, both angular fibers are integrable and their integrals equal r(J). Both source-law action projections and both Cartesian radial-action projections equal actionLaw(r). Marginal equality is joint equality for the same two actions.

**Definition 1.10 (The phase-uniform product comparator).**

$$\forall G \in CartesianTwo \to \mathbb{R},\; \forall r \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right) \to \mathbb{R},\; \operatorname{phaseUniformProduct}\left(G, r\right) \Leftrightarrow {{\operatorname{aeEq}\left(torusFullBase, \operatorname{sourcePullback}\left(G\right), \operatorname{fun} z \mapsto {\frac{r\left(\operatorname{actionProjection}\left(z\right)\right)}{{2 \cdot \pi}^{2}}}\right)} \land {\exists rone \in \mathbb{R} \to \mathbb{R},\; \exists rtwo \in \mathbb{R} \to \mathbb{R},\; {\operatorname{oneActionDensity}\left(rone\right)} \land {{\operatorname{oneActionDensity}\left(rtwo\right)} \land {\operatorname{aeEq}\left(\operatorname{prod}\left(action, action\right), r, \operatorname{fun} J \mapsto {rone\left(\operatorname{fst}\left(J\right)\right) \cdot rtwo\left(\operatorname{snd}\left(J\right)\right)}\right)}}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.phaseUniformProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

The source density equals r(actionProjection(z))/(2*pi)^2 almost everywhere. The joint action density factors almost everywhere into two actually normalized nonnegative one-action densities. This condition certifies existence of the product comparator.

**Definition 1.11 (The necessary two-DOF minimum assertion).**

$$dinovTwoDofMinimumClause \Leftrightarrow {\forall s \in \mathbb{R},\; \forall r \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right) \to \mathbb{R},\; \forall F \in CartesianTwo \to \mathbb{R},\; \forall G \in CartesianTwo \to \mathbb{R},\; {\operatorname{actionDensity}\left(r\right)} \Rightarrow {{\operatorname{sourceState}\left(F\right)} \Rightarrow {{\operatorname{sourceState}\left(G\right)} \Rightarrow {{\operatorname{commonActionMarginal}\left(F, G, r\right)} \Rightarrow {{\operatorname{phaseUniformProduct}\left(G, r\right)} \Rightarrow {{s \le \operatorname{sourceEntropy}\left(F\right)} \Rightarrow {{s \le \operatorname{sourceEntropy}\left(G\right)} \Rightarrow {\forall j \in Bool,\; \operatorname{sourceUncertainty}\left(G, j\right) \le \operatorname{sourceUncertainty}\left(F, j\right)}}}}}}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.dinovTwoDofMinimumClause` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Conjecture 3.22 (Equipartition duality): "Fix n ≥ 2, an entropy value s, and an action marginal ρ_J on (0,∞)^n. Among all states on T^n × (0,∞)^n with entropy ≥ s and action marginal ρ_J, the phase-equipartitioned product state (unique when it exists) simultaneously (i) maximizes the entropy, (ii) minimizes every within-DOF uncertainty u_j, and (iii) is the unique state at which the per-DOF conjectured bound of Problem 3.17(b) is saturated for all j; moreover it is the unique fixed point, with the given marginal, of the multi-DOF kime-deformed semigroup ∂t ρ = Σj (−ωj ∂θj + ε ∂θj²) ρ." The formal predicate expresses only a necessary specialization of clause (ii), at n=2, on the certified finite-entropy, L2, positive-definite subclass. The original all-n assertion implies clause (ii), which implies this specialization. The predicate has no n quantifier and makes no separate assertion about clauses (i), (iii), or the semigroup.

**Theorem 1.12 (Both uncertainties are smaller than the comparator's).**

$$\neg dinovTwoDofMinimumClause$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/dinov-2026-equipartition-duality-minimum-refutation` (refuted) by `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dinov-2026-equipartition-duality-minimum-refutation","declaration_gid":"D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Use r(J1,J2)=exp(-(J1+J2)) and independent phases phi(theta)=(1+cos(2*theta)/2)/(2*pi). Each action has density exp(-J), and the comparator has uniform phases. The two Cartesian densities are the products of the actual one-DOF densities exp(-R2/2)*(1+(p^2-q^2)/(2*R2))/(2*pi) and exp(-R2/2)/(2*pi); the first is set to zero at R2=0. The zero-action planes have zero measure. Change of variables proves normalization, the source pushforwards, common joint marginal and entropy equality. Both entropies are finite and nonnegative, so s=0 is admissible. The actual covariance matrices, ordered q1,p1,q2,p2, are diag(3/4,5/4,3/4,5/4) and the identity. Both are positive definite and all coordinates belong to L2. For each of the two degrees of freedom the uncertainties are sqrt(15/16) and 1, respectively, with sqrt(15/16)<1. Adding both strict comparisons contradicts the sum of both inequalities required by the minimum assertion. Thus clause (ii), and hence the simultaneous conjecture as written, fails. Entropy maximization, saturation uniqueness and semigroup claims receive no separate settlement here.

## References

- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.PsiA`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actionDensity`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actualCovariance`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actualUncertainty`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.cartesianLaw`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.commonActionMarginal`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.dinovTwoDofMinimumClause`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.phaseUniformProduct`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourceEntropy`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourcePullback`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourceState`
