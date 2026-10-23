# Optimal visibility for calibrated joint measurements

## Abstract

The fluctuation condition forces the optimal calibrated visibility bound.

**Definition 1.1 (Initial white-noise effects).**

$$\forall d \in \mathbb{N},\; \forall lam \in \mathbb{R},\; \forall a \in \operatorname{Fin}\left(d\right),\; \operatorname{effA}\left(d, lam, a\right) = \operatorname{HSMul}.\operatorname{hSMul}\left((lam : \mathbb{C}), \operatorname{Matrix}.\operatorname{single}\left(a, a, 1\right)\right) + \operatorname{HSMul}.\operatorname{hSMul}\left((\frac{1 - lam}{(d : \mathbb{R})} : \mathbb{C}), 1\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.effA` (`✓ std3`).

*Citation.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Equation (5), p. 3: A_a = λΠ_a + ((1−λ)/d)𝟙. The initial energy projectors are standard matrix units.

**Definition 1.2 (Final white-noise effects).**

$$\forall d \in \mathbb{N},\; \forall gam \in \mathbb{R},\; \forall b \in \operatorname{Fin}\left(d\right),\; \operatorname{effB}\left(d, gam, b\right) = \operatorname{HSMul}.\operatorname{hSMul}\left((gam : \mathbb{C}), \operatorname{Matrix}.\operatorname{single}\left(b, b, 1\right)\right) + \operatorname{HSMul}.\operatorname{hSMul}\left((\frac{1 - gam}{(d : \mathbb{R})} : \mathbb{C}), 1\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.effB` (`✓ std3`).

*Citation.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Equation (5), p. 3: B_b = γΠ′_b + ((1−γ)/d)𝟙. The final energy projectors are standard matrix units before the unitary rotation.

**Definition 1.3 (Rotated final effects).**

$$\forall d \in \mathbb{N},\; \forall gam \in \mathbb{R},\; \forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall b \in \operatorname{Fin}\left(d\right),\; \operatorname{effBU}(gam := gam)(U)\left(b\right) = ((\operatorname{star}\left(U\right)) \cdot (\operatorname{effB}\left(d, gam, b\right))) \cdot (U)$$

*Formalization.* `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.effBU` (`✓ std3`).

*Citation.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Page 3: B^U_b = U†B_bU. Both energy bases are represented by standard matrix units; varying U over Matrix.unitaryGroup covers arbitrary relative bases. The final white-noise effect is effB from Eq. (5).

**Definition 1.4 (The Lüders instrument).**

$$\forall d \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{luders}\left(A, rho\right) = ((\operatorname{CFC}.\operatorname{sqrt}\left(A\right)) \cdot (rho)) \cdot (\operatorname{CFC}.\operatorname{sqrt}\left(A\right))$$

*Formalization.* `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.luders` (`✓ std3`).

*Citation.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Page 3 uses the Lüders instrument I^A_a(ρ) = A_a^{1/2}ρA_a^{1/2}. The positive square root is CFC.sqrt on complex matrices.

**Definition 1.5 (The average condition).**

$$\forall d \in \mathbb{N},\; \forall W \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall A \in \operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall B \in \operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{AverageCondition}\left(W, A, B\right)) \Leftrightarrow (\forall f \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \forall g \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \sum_{a:\operatorname{Fin}\left(d\right)} (\sum_{b:\operatorname{Fin}\left(d\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left((g\left(b\right) - f\left(a\right) : \mathbb{C}), W\left((a, b)\right)\right))) = \sum_{b:\operatorname{Fin}\left(d\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left((g\left(b\right) : \mathbb{C}), B\left(b\right)\right)) - \sum_{a:\operatorname{Fin}\left(d\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left((f\left(a\right) : \mathbb{C}), A\left(a\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.AverageCondition` (`✓ std3`).

*Citation.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Page 3: “(i) Average condition: The average operator of W^U agrees with the difference of the average operators of B^U and A for all choices of f and g”. The real energy assignments f and g are arbitrary, and their difference multiplies each joint effect.

**Definition 1.6 (The fluctuation condition).**

$$\forall d \in \mathbb{N},\; \forall W \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall A \in \operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall B \in \operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{FluctuationCondition}\left(W, A, B\right)) \Leftrightarrow (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(rho\right) = 1) \Rightarrow ((\forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; (i \ne j) \Rightarrow (rho\left(i, j\right) = 0)) \Rightarrow (\forall a \in \operatorname{Fin}\left(d\right),\; \forall b \in \operatorname{Fin}\left(d\right),\; \operatorname{Matrix}.\operatorname{trace}\left((W\left((a, b)\right)) \cdot (rho)\right) = \operatorname{Matrix}.\operatorname{trace}\left((B\left(b\right)) \cdot (\operatorname{luders}\left(A\left(a\right), rho\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.FluctuationCondition` (`✓ std3`).

*Citation.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Page 3: “(ii) Fluctuation condition: For states ρ_Δ diagonal in the initial energy eigenbasis the statistics given by W^U agrees with the sequentially measured GTPM statistics”. The states are all positive semidefinite complex matrices of trace one whose off-diagonal entries vanish. Equality holds for each pair of outcomes.

**Definition 1.7 (The coherence coefficient).**

$$\forall d \in \mathbb{N},\; \forall lam \in \mathbb{R},\; \operatorname{kappa}\left(d, lam\right) = ((2) \cdot (\operatorname{Real}.\operatorname{sqrt}\left(lam + \frac{1 - lam}{(d : \mathbb{R})}\right))) \cdot (\operatorname{Real}.\operatorname{sqrt}\left(\frac{1 - lam}{(d : \mathbb{R})}\right)) + ((d : \mathbb{R}) - 2) \cdot (\frac{1 - lam}{(d : \mathbb{R})})$$

*Formalization.* `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.kappa` (`✓ std3`).

*Citation.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Equation (9), p. 4 defines κ = 2√(λ + (1−λ)/d)√((1−λ)/d) + (d−2)(1−λ)/d. The two distinguished levels contribute the square-root products; the other d−2 levels contribute the common diagonal coefficient.

**Definition 1.8 (The visibility bound).**

$$\forall d \in \mathbb{N},\; \forall lam \in \mathbb{R},\; \operatorname{visibilityBound}\left(d, lam\right) = \frac{(2) \cdot (\operatorname{kappa}\left(d, lam\right))}{(d : \mathbb{R}) + (2) \cdot (\operatorname{kappa}\left(d, lam\right)) - ((d : \mathbb{R})) \cdot (\operatorname{kappa}\left(d, lam\right))}$$

*Formalization.* `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.visibilityBound` (`✓ std3`).

*Citation.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Equation (8), p. 4 gives γ ≤ 2κ/(d + 2κ − dκ). The divisions are real divisions; d is coerced from a natural number to a real number.

**Definition 1.9 (Optimality of the calibrated visibility).**

$$(claim) \Leftrightarrow (\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow (\forall lam \in \mathbb{R},\; \forall gam \in \mathbb{R},\; (0 < lam) \Rightarrow ((lam < 1) \Rightarrow ((0 < gam) \Rightarrow ((gam < 1) \Rightarrow ((\forall U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \Rightarrow (\exists W \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{ConcealmentKernelNecessityRefutation}.\operatorname{IsPOVM}\left(W\right)) \land ((\operatorname{AverageCondition}\left(W, \operatorname{effA}\left(d, lam\right), \operatorname{effBU}(gam := gam)(U)\right)) \land (\operatorname{FluctuationCondition}\left(W, \operatorname{effA}\left(d, lam\right), \operatorname{effBU}(gam := gam)(U)\right))))) \Rightarrow (gam \le \operatorname{visibilityBound}\left(d, lam\right))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.claim` (`✓ std3`).

*Citation.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Page 4: “The ansatz for the effects W^U_ab in Eq. (6) is a priori not the most general one [54]. However, numerical simulations suggest that our visibility bounds are tight and we conjecture that our construction is optimal to satisfy condition (ii) for the given model Eq. (5)”. The encoding states necessity of Eq. (8) for every d ≥ 2 and 0 < lam, gam < 1 when every intermediate unitary has a parent POVM satisfying (i) and (ii). IsPOVM is the positive-effect and normalization predicate from ConcealmentKernelNecessityRefutation. The source proves sufficiency by its inverse Lüders construction.

**Theorem 1.10 (No parent POVM exceeds the bound).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.result` (`✓ std3`). ∎

*Resolves.* `Problems/beyer-uola-luoma-strunz-2022-calibrated-visibility-optimality` (proved) by `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"beyer-uola-luoma-strunz-2022-calibrated-visibility-optimality","declaration_gid":"D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Beyer; R. Uola; K. Luoma; W. T. Strunz (2022). *Joint measurability in nonequilibrium quantum thermodynamics*. DOI: [10.1103/PhysRevE.106.L022101](https://doi.org/10.1103/PhysRevE.106.L022101). URL: <https://arxiv.org/abs/2111.02854>.

*Commentary.*

Evaluating the fluctuation condition on each diagonal matrix unit fixes every parent effect's diagonal to the product of the two marginal diagonals. CartesianVariance.psd_entry_bound and the triangle inequality bound the sum of coherences between two levels. A Hadamard rotation of those levels gives gam/2 ≤ kappa d lam · (gam/2 + (1−gam)/d). The identity kappa d lam = 1 − (√(lam+(1−lam)/d) − √((1−lam)/d))² ensures a positive denominator, yielding the visibility bound. This proves necessity for arbitrary parent effects. Sufficiency is the source's theorem and is not asserted by the Lean result.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.AverageCondition`
- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.FluctuationCondition`
- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.effA`
- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.effB`
- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.effBU`
- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.kappa`
- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.luders`
- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.result`
- Truth anchor: `D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.visibilityBound`
- Dependency: [D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation](../Entanglement/NandiMutualPredictabilityLOCCRefutation.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](../QuantumChannels/TomiyamaDiagonalKPositivity.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../RandomCircuits/HaarTwoCopyTwirl.md)
