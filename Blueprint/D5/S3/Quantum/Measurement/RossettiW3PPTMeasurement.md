# The complementary W-state effect is not fully separable

## Abstract

The optimal three-qubit W-state PPT measurement is not fully separable.

A basis index x : Fin 3 → Fin 2 lists the bits of the three qubits in order. Pi.single x 1 is the computational basis vector |x⟩. Matrix.vecMulVec u (star u) is the rank-one operator |u⟩⟨u|. Complex.ofReal is the coercion from real to complex numbers. The identity in the formulas is the identity matrix on this eight-dimensional space.

**Definition 1.1 (The three-qubit W state).**

$$(\operatorname{W3}: (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}) = \operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\frac{1}{3}\right)\right), (\operatorname{Pi.single}\left(![1, 0, 0], (1: \mathbb{C})\right) + \operatorname{Pi.single}\left(![0, 1, 0], (1: \mathbb{C})\right) + \operatorname{Pi.single}\left(![0, 0, 1], (1: \mathbb{C})\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.W3` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

Section X.0.4, printed page 22, uses |W₃⟩ = √(1/3)(|100⟩ + |010⟩ + |001⟩). The square root is real and is then embedded in the complex scalars.

**Definition 1.2 (The anti-W state).**

$$(\operatorname{W3bar}: (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}) = \operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\frac{1}{3}\right)\right), (\operatorname{Pi.single}\left(![0, 1, 1], (1: \mathbb{C})\right) + \operatorname{Pi.single}\left(![1, 0, 1], (1: \mathbb{C})\right) + \operatorname{Pi.single}\left(![1, 1, 0], (1: \mathbb{C})\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.W3bar` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

Section X.0.4, printed page 22, defines |W̄₃⟩ = √(1/3)(|011⟩ + |101⟩ + |110⟩). The three terms have Hamming weight two.

**Definition 1.3 (The weight-one projector).**

$$(\operatorname{P1}: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{Matrix.vecMulVec}\left(\operatorname{Pi.single}\left(![1, 0, 0], (1: \mathbb{C})\right), \operatorname{star}\left(\operatorname{Pi.single}\left(![1, 0, 0], (1: \mathbb{C})\right)\right)\right) + \operatorname{Matrix.vecMulVec}\left(\operatorname{Pi.single}\left(![0, 1, 0], (1: \mathbb{C})\right), \operatorname{star}\left(\operatorname{Pi.single}\left(![0, 1, 0], (1: \mathbb{C})\right)\right)\right) + \operatorname{Matrix.vecMulVec}\left(\operatorname{Pi.single}\left(![0, 0, 1], (1: \mathbb{C})\right), \operatorname{star}\left(\operatorname{Pi.single}\left(![0, 0, 1], (1: \mathbb{C})\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.P1` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

The source states on printed page 22: “the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|”. On printed page 22, P₁ is the sum of the three computational-basis projectors of weight one.

**Definition 1.4 (The weight-two projector).**

$$(\operatorname{P2}: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{Matrix.vecMulVec}\left(\operatorname{Pi.single}\left(![0, 1, 1], (1: \mathbb{C})\right), \operatorname{star}\left(\operatorname{Pi.single}\left(![0, 1, 1], (1: \mathbb{C})\right)\right)\right) + \operatorname{Matrix.vecMulVec}\left(\operatorname{Pi.single}\left(![1, 0, 1], (1: \mathbb{C})\right), \operatorname{star}\left(\operatorname{Pi.single}\left(![1, 0, 1], (1: \mathbb{C})\right)\right)\right) + \operatorname{Matrix.vecMulVec}\left(\operatorname{Pi.single}\left(![1, 1, 0], (1: \mathbb{C})\right), \operatorname{star}\left(\operatorname{Pi.single}\left(![1, 1, 0], (1: \mathbb{C})\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.P2` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

The source states on printed page 22: “the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|”. On printed page 22, P₂ is the sum of the three computational-basis projectors of weight two.

**Definition 1.5 (The W-state projector).**

$$(\operatorname{Q1}: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{Matrix.vecMulVec}\left(\operatorname{W3}, \operatorname{star}\left(\operatorname{W3}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q1` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

The source states on printed page 22: “the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|”. The first of the six invariant projectors on printed page 22 is Q₁ = |W₃⟩⟨W₃|.

**Definition 1.6 (The anti-W projector).**

$$(\operatorname{Q2}: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{Matrix.vecMulVec}\left(\operatorname{W3bar}, \operatorname{star}\left(\operatorname{W3bar}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q2` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

The source states on printed page 22: “the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|”. The second invariant projector is Q₂ = |W̄₃⟩⟨W̄₃|.

**Definition 1.7 (The remaining weight-one subspace).**

$$(\operatorname{Q3}: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{P1} - \operatorname{Matrix.vecMulVec}\left(\operatorname{W3}, \operatorname{star}\left(\operatorname{W3}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q3` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

The source states on printed page 22: “the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|”. Q₃ subtracts the W-state projector from P₁. The source uses W₃ for the projector in this subtraction.

**Definition 1.8 (The remaining weight-two subspace).**

$$(\operatorname{Q4}: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{P2} - \operatorname{Matrix.vecMulVec}\left(\operatorname{W3bar}, \operatorname{star}\left(\operatorname{W3bar}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q4` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

The source states on printed page 22: “the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|”. Q₄ subtracts the anti-W projector from P₂. The source uses W̄₃ for the projector in this subtraction.

**Definition 1.9 (The zero-weight projector).**

$$(\operatorname{Q5}: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{Matrix.vecMulVec}\left(\operatorname{Pi.single}\left(![0, 0, 0], (1: \mathbb{C})\right), \operatorname{star}\left(\operatorname{Pi.single}\left(![0, 0, 0], (1: \mathbb{C})\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q5` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

The source states on printed page 22: “the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|”. The fifth invariant projector is Q₅ = |000⟩⟨000|.

**Definition 1.10 (The weight-three projector).**

$$(\operatorname{Q6}: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{Matrix.vecMulVec}\left(\operatorname{Pi.single}\left(![1, 1, 1], (1: \mathbb{C})\right), \operatorname{star}\left(\operatorname{Pi.single}\left(![1, 1, 1], (1: \mathbb{C})\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q6` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

The source states on printed page 22: “the invariant operators can be shown to be linear combinations of six projectors: Q₁ = |W₃⟩⟨W₃|, Q₂ = |W̄₃⟩⟨W̄₃|, Q₃ = P₁ − W₃, Q₄ = P₂ − W̄₃, Q₅ = |000⟩⟨000|, and Q₆ = |111⟩⟨111|”. The sixth invariant projector is Q₆ = |111⟩⟨111|.

**Definition 1.11 (The optimal PPT effect from equation (83)).**

$$(\operatorname{Mprime}: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \operatorname{Q1} + \operatorname{HSMul.hSMul}\left((\frac{1}{2}: \mathbb{C}), \operatorname{Q2}\right) + \operatorname{HSMul.hSMul}\left((0: \mathbb{C}), \operatorname{Q3}\right) + \operatorname{HSMul.hSMul}\left((0: \mathbb{C}), \operatorname{Q4}\right) + \operatorname{HSMul.hSMul}\left((\frac{2}{3}: \mathbb{C}), \operatorname{Q5}\right) + \operatorname{HSMul.hSMul}\left((\frac{1}{12}: \mathbb{C}), \operatorname{Q6}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Mprime` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

Equation (83), printed page 23: “t₂ = 1/2, t₃ = t₄ = 0, t₅ = 2/3, t₆ = 1/12”. All six terms are displayed, including the zero coefficients of Q₃ and Q₄.

**Definition 1.12 (Effects proportional to fully separable states).**

$$\forall E \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{IsSEPEffect}\left(E\right) \Leftrightarrow (\exists c \in \mathbb{R},\; (\exists rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; ((0 \le c) \land ((\operatorname{FullySeparableExchangeObstruction.IsFullySeparableLocal}\left(rho\right)) \land (E = \operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(c\right), rho\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.IsSEPEffect` (`✓ std3`).

*Citation.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

After equation (62), printed page 17: “In other words, the POVM elements are proportional to separable states.” The real proportionality constant is nonnegative. IsFullySeparableLocal is the finite convex-mixture definition from FullySeparableExchangeObstruction, with three sites and two local basis states.

**Definition 1.13 (SEP membership of the specified two-outcome measurement).**

$$\operatorname{claim} \Leftrightarrow ((\operatorname{IsSEPEffect}\left(\operatorname{Mprime}\right)) \land (\operatorname{IsSEPEffect}\left(((1: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) - \operatorname{Mprime})\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

Printed page 23: “Nevertheless, none of the tests conducted so far have succeeded in detecting entanglement, leaving open the question of whether (M′, 𝟙 − M′) belongs to the SEP class.” The proposition says that each of the two displayed effects is proportional to a fully separable state.

**Theorem 1.14 (This two-outcome measurement is outside SEP).**

$$\neg ((\operatorname{IsSEPEffect}\left(\operatorname{Mprime}\right)) \land (\operatorname{IsSEPEffect}\left(((1: \operatorname{Matrix}\left((\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) - \operatorname{Mprime})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.result` (`✓ std3`). ∎

*Resolves.* `Problems/rossetti-mancini-winter-schindler-2025-w3-ppt-measurement-not-separable` (refuted) by `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rossetti-mancini-winter-schindler-2025-w3-ppt-measurement-not-separable","declaration_gid":"D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* L. Rossetti; S. Mancini; A. Winter; J. Schindler (2025). *Observational entropy of quantum correlations and entanglement*. DOI: [10.1109/TIT.2026.3700031](https://doi.org/10.1109/TIT.2026.3700031). URL: <https://arxiv.org/abs/2510.10058v1>.

*Commentary.*

Put R = 𝟙 − M′. The quadratic form of R vanishes at |100⟩ + |010⟩ + |001⟩. The partial-transpose quadratic forms vanish at 2|000⟩ + |110⟩ + |101⟩, 2|000⟩ + |110⟩ + |011⟩, and 2|000⟩ + |101⟩ + |011⟩ for the respective sites. In a sum of positive product operators these zeros force every summand to have weight-two diagonal mass twice its weight-one mass, including when a local diagonal vanishes. The same relation holds for their sum. For R the masses are 5/2 and 2, so the relation fails. Thus the complementary effect is not fully separable. This conclusion concerns the specified measurement; the optimal SEP entropy and the possible attainment of trace 9/4 by another SEP measurement remain separate questions.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.IsSEPEffect`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Mprime`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.P1`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.P2`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q1`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q2`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q3`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q4`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q5`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.Q6`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.W3`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.W3bar`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/RossettiW3PPTMeasurement.result`
- Dependency: [D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation](../Dynamics/PronkoFredkinNonCyclicAnnihilation.md)
- Dependency: [D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction](../Entanglement/FullySeparableExchangeObstruction.md)
