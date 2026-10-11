# Fourier Clifford Vacuum

## Abstract

The product of Fourier number projections is a Hermitian idempotent.

Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.

**Definition 1.1 (averaging).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\\forall (u : R),\\(\operatorname{averaging} (R : = R) (u : = u) : R \to_{l} [\mathbb{C}] R) = ((1 / 2 : \mathbb{C}) \cdot (\operatorname{LinearMap} . \operatorname{id} + (\operatorname{LinearMap} . \operatorname{mulLeftRight} \mathbb{C} (u , u))))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.averaging` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines averaging.

**Definition 1.2 (finiteTwirl).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\\forall (g : \mathbb{N} \to R),\\\forall (k : \mathbb{N}),\\(\operatorname{finiteTwirl} (R : = R) (g : = g) (k : = k) : R \to_{l} [\mathbb{C}] R) = (((\operatorname{List} . \operatorname{range} k) . \operatorname{map} (\operatorname{fun} j \mapsto \operatorname{averaging} (g j))) . \operatorname{prod})\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.finiteTwirl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines finiteTwirl.

**Lemma 1.3 (finiteTwirl step).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\\forall (g : \mathbb{N} \to R),\\\forall (k : \mathbb{N}),\\\forall (X : R),\\\operatorname{finiteTwirl} g (k + 1) X = (1 / 2 : \mathbb{C}) \cdot (\operatorname{finiteTwirl} g k X + \operatorname{finiteTwirl} g k (g k \cdot X \cdot g k))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.finiteTwirl_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This finiteTwirl step identity is used in the FourierCliffordVacuum construction.

**Definition 1.4 (vacuumWord).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\\forall (p : \mathbb{N} \to R),\\\forall (k : \mathbb{N}),\\(\operatorname{vacuumWord} (R : = R) (p : = p) (k : = k) : R) = ((((\operatorname{List} . \operatorname{range} k) . \operatorname{reverse}) . \operatorname{map} p) . \operatorname{prod})\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.vacuumWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines vacuumWord.

**Definition 1.5 (cycleFrequency).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\\forall (r : \operatorname{Fin} L),\\(\operatorname{cycleFrequency} (L : = L) (r : = r) : \mathbb{R}) = ((2 \cdot (r : \mathbb{R}) + 1) \cdot \operatorname{theta} L)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.cycleFrequency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines cycleFrequency.

**Definition 1.6 (modeScale).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\(\operatorname{modeScale} (L : = L) : \mathbb{C}) = (((((\operatorname{Real} . \operatorname{sqrt} ((4 \cdot L : \mathbb{N}) : \mathbb{R})))^{-1} : \mathbb{R}) : \mathbb{C}))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.modeScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines modeScale.

**Definition 1.7 (modeCoeff).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\\forall (r : \operatorname{Fin} L),\\\forall (j : \operatorname{Fin} (2 \cdot L)),\\(\operatorname{modeCoeff} (L : = L) (r : = r) (j : = j) : \mathbb{C}) = (\operatorname{modeScale} L \cdot (\operatorname{fun} x : \mathbb{R} \mapsto (\operatorname{Real} . \operatorname{probChar} x : \mathbb{C})) (- (j : \mathbb{R}) \cdot \operatorname{cycleFrequency} L r))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.modeCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines modeCoeff.

**Lemma 1.8 (modeScale star).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\\operatorname{star} (\operatorname{modeScale} L) = \operatorname{modeScale} L\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.modeScale_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This modeScale star identity is used in the FourierCliffordVacuum construction.

**Lemma 1.9 (modeScale square).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\(0 < L) \to\\\operatorname{modeScale} L \cdot \operatorname{modeScale} L = (((4 \cdot L : \mathbb{N}) : \mathbb{C}))^{-1}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.modeScale_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This modeScale square identity is used in the FourierCliffordVacuum construction.

**Definition 1.10 (fourierMode).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\\forall (L : \mathbb{N}),\\\forall (g : \operatorname{Fin} (2 \cdot L) \to R),\\\forall (r : \operatorname{Fin} L),\\(\operatorname{fourierMode} (R : = R) (L : = L) (g : = g) (r : = r) : R) = (\operatorname{Fintype} . \operatorname{linearCombination} \mathbb{C} g (\operatorname{modeCoeff} L r))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines fourierMode.

**Definition 1.11 (totalGamma).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\\forall (L : \mathbb{N}),\\\forall (g : \operatorname{Fin} (2 \cdot L) \to R),\\\forall (k : \mathbb{N}),\\(\operatorname{totalGamma} (R : = R) (L : = L) (g : = g) (k : = k) : R) = (\operatorname{if} \operatorname{hk} : k < 2 \cdot L \operatorname{then} g \langle k , \operatorname{hk} \rangle \operatorname{else} 0)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.totalGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines totalGamma.

**Definition 1.12 (cliffordAverage).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\\forall (L : \mathbb{N}),\\\forall (g : \operatorname{Fin} (2 \cdot L) \to R),\\(\operatorname{cliffordAverage} (R : = R) (L : = L) (g : = g) : R \to_{l} [\mathbb{C}] R) = (\operatorname{finiteTwirl} (\operatorname{totalGamma} g) (2 \cdot L))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.cliffordAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines cliffordAverage.

**Definition 1.13 (totalMode).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\\forall (L : \mathbb{N}),\\\forall (g : \operatorname{Fin} (2 \cdot L) \to R),\\\forall (k : \mathbb{N}),\\(\operatorname{totalMode} (R : = R) (L : = L) (g : = g) (k : = k) : R) = (\operatorname{if} \operatorname{hk} : k < L \operatorname{then} \operatorname{fourierMode} g \langle k , \operatorname{hk} \rangle \operatorname{else} 0)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.totalMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines totalMode.

**Definition 1.14 (numberProjection).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\{}[\operatorname{StarRing} R] ,\\\forall (L : \mathbb{N}),\\\forall (g : \operatorname{Fin} (2 \cdot L) \to R),\\\forall (k : \mathbb{N}),\\(\operatorname{numberProjection} (R : = R) (L : = L) (g : = g) (k : = k) : R) = (\operatorname{totalMode} g k \cdot \operatorname{star} (\operatorname{totalMode} g k))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.numberProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines numberProjection.

**Definition 1.15 (fourierVacuum).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\{}[\operatorname{StarRing} R] ,\\\forall (L : \mathbb{N}),\\\forall (g : \operatorname{Fin} (2 \cdot L) \to R),\\(\operatorname{fourierVacuum} (R : = R) (L : = L) (g : = g) : R) = (\operatorname{vacuumWord} (\operatorname{numberProjection} g) L)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierVacuum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines fourierVacuum.

**Lemma 1.16 (fourierVacuum properties).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\{}[\operatorname{StarRing} R] ,\\{}[\operatorname{StarModule} \mathbb{C} R] ,\\\forall (L : \mathbb{N}),\\(0 < L) \to\\\forall (g : \operatorname{Fin} (2 \cdot L) \to R),\\(\forall j , g j \cdot g j = 1) \to\\(\forall j , \operatorname{star} (g j) = g j) \to\\(\forall j k , j \neq k \to g j \cdot g k = - (g k \cdot g j)) \to\\\operatorname{star} (\operatorname{fourierVacuum} g) = \operatorname{fourierVacuum} g \land \operatorname{fourierVacuum} g \cdot \operatorname{fourierVacuum} g = \operatorname{fourierVacuum} g \land (\forall k , k < L \to \operatorname{totalMode} g k \cdot \operatorname{fourierVacuum} g = 0 \land \operatorname{fourierVacuum} g \cdot \operatorname{star} (\operatorname{totalMode} g k) = 0) \land \operatorname{cliffordAverage} g (\operatorname{fourierVacuum} g) = (((1 / 2 : \mathbb{C}))^{L}) \cdot (1 : R)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierVacuum_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of Fourier number projections is a Hermitian idempotent. Every Fourier annihilator kills it on the left and its adjoint kills it on the right. Averaging conjugations by all Majoranas gives exactly 2^(−L) times the identity.

**Lemma 1.17 (fourierVacuum psd).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\{}[\operatorname{DecidableEq} \iota] ,\\\forall (L : \mathbb{N}),\\(0 < L) \to\\\forall (g : \operatorname{Fin} (2 \cdot L) \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\(\forall j , g j \cdot g j = 1) \to\\(\forall j , \operatorname{star} (g j) = g j) \to\\(\forall j k , j \neq k \to g j \cdot g k = - (g k \cdot g j)) \to\\(\operatorname{fourierVacuum} g) . \operatorname{PosSemidef}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierVacuum_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This fourierVacuum psd identity is used in the FourierCliffordVacuum construction.

**Lemma 1.18 (fourierVacuum covariance).**

$$\begin{aligned}\forall (R : \operatorname{Type}),\\{}[\operatorname{Ring} R] ,\\{}[\operatorname{Algebra} \mathbb{C} R] ,\\{}[\operatorname{StarRing} R] ,\\{}[\operatorname{StarModule} \mathbb{C} R] ,\\\forall (L : \mathbb{N}),\\(0 < L) \to\\\forall (g : \operatorname{Fin} (2 \cdot L) \to R),\\(\forall j , g j \cdot g j = 1) \to\\(\forall j , \operatorname{star} (g j) = g j) \to\\(\forall j k , j \neq k \to g j \cdot g k = - (g k \cdot g j)) \to\\\forall (j : \operatorname{Fin} (2 \cdot L)),\\\forall (k : \operatorname{Fin} (2 \cdot L)),\\\operatorname{cliffordAverage} g (g j \cdot g k \cdot \operatorname{fourierVacuum} g) = (4 \cdot \sum r : \operatorname{Fin} L , \operatorname{star} (\operatorname{modeCoeff} L r j) \cdot \operatorname{modeCoeff} L r k) \cdot \operatorname{cliffordAverage} g (\operatorname{fourierVacuum} g)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierVacuum_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This fourierVacuum covariance identity is used in the FourierCliffordVacuum construction.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.averaging`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.cliffordAverage`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.cycleFrequency`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.finiteTwirl`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.finiteTwirl_step`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierMode`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierVacuum`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierVacuum_covariance`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierVacuum_properties`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.fourierVacuum_psd`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.modeCoeff`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.modeScale`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.modeScale_square`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.modeScale_star`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.numberProjection`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.totalGamma`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.totalMode`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.vacuumWord`
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate](ShiftedFourierOperatorCertificate.md)
