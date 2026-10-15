/- GID: D5/S3/Quantum/PureState/FourCopyConcentrationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/PureState/FourCopyConcentrationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.claim; result=D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.result; claim=D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.claim
   digest: A singlet-sector protocol refutes the direct four-copy concentration bound. -/

import D5.S3.Quantum.QubitWitnesses
import D5.S3.Quantum.Entanglement.QutritThresholdSharing

set_option linter.style.longLine false

open scoped BigOperators Matrix ComplexOrder ComplexConjugate
open D5.S3.Quantum.FiniteDimensional (QubitMatrix)
open D5.S3.Quantum.QubitWitnesses (bellCoefficients)

namespace D5.S3.Quantum.PureState.FourCopyConcentrationRefutation

noncomputable section

/-- Four local qubits, ordered as the two pairs `(1, 2)` and `(3, 4)`. -/
abbrev Q := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- The normalization of the two-qubit pure-state coefficient matrix. -/
def normalized (C : QubitMatrix) : Prop :=
  (∑ i : Fin 2, ∑ j : Fin 2, ‖C i j‖ ^ 2) = 1

/-- Four-copy coefficients with Alice's four bits against Bob's four bits. -/
def amp4 (C : QubitMatrix) (a b : Q) : ℂ :=
  C a.1.1 b.1.1 * C a.1.2 b.1.2 * C a.2.1 b.2.1 * C a.2.2 b.2.2

/-- Local success operators act on coefficients with Bob's factor transposed. -/
def output (KA KB : Matrix (Fin 2) Q ℂ) (C : QubitMatrix) : QubitMatrix :=
  fun i j => ∑ a : Q, ∑ b : Q, KA i a * KB j b * amp4 C a b

/-- Every normalized input produces a scalar multiple of the Bell vector, including zero. -/
def universal (KA KB : Matrix (Fin 2) Q ℂ) : Prop :=
  ∀ C : QubitMatrix, normalized C →
    output KA KB C 0 1 = 0 ∧ output KA KB C 1 0 = 0 ∧
      output KA KB C 0 0 = output KA KB C 1 1

/-- The squared norm of the unnormalized success output. -/
def success (KA KB : Matrix (Fin 2) Q ℂ) (C : QubitMatrix) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ‖output KA KB C i j‖ ^ 2

/-- The literal four-copy bound of Eq. (8). -/
def B (C : QubitMatrix) : ℝ :=
  2 * ‖C 0 1 ^ 4 * C 1 0 ^ 4‖ + 2 * ‖C 0 0 ^ 4 * C 1 1 ^ 4‖ -
    4 * (C 0 0 ^ 2 * C 1 1 ^ 2 * (conj (C 0 1)) ^ 2 * (conj (C 1 0)) ^ 2).re

/-- The direct four-copy bound restricted to locally contractive product success operators. -/
def claim : Prop :=
  ∀ KA KB : Matrix (Fin 2) Q ℂ, (1 - KAᴴ * KA).PosSemidef →
    (1 - KBᴴ * KB).PosSemidef → universal KA KB →
      ∀ C, normalized C → success KA KB C ≤ B C

/-- The product of singlets on positions `(1, 2)` and `(3, 4)`. -/
def u (q : Q) : ℂ :=
  if q = ((0, 1), (0, 1)) ∨ q = ((1, 0), (1, 0)) then 1 / 2
  else if q = ((0, 1), (1, 0)) ∨ q = ((1, 0), (0, 1)) then -1 / 2
  else 0

/-- The product of singlets on positions `(1, 3)` and `(2, 4)`. -/
def w (q : Q) : ℂ :=
  if q = ((0, 0), (1, 1)) ∨ q = ((1, 1), (0, 0)) then 1 / 2
  else if q = ((0, 1), (1, 0)) ∨ q = ((1, 0), (0, 1)) then -1 / 2
  else 0

/-- The orthogonal second singlet-sector vector. -/
def v (q : Q) : ℂ := (Real.sqrt 3 : ℂ)⁻¹ * (2 * w q - u q)

/-- The two real singlet-sector bras form the local success operator. -/
def K : Matrix (Fin 2) Q ℂ := fun i q => if i = 0 then u q else v q

/-- A normalized maximally entangled input whose Eq. (8) bound is zero. -/
def C0 : QubitMatrix := !![(1 / 2 : ℂ), 1 / 2; -1 / 2, 1 / 2]

end

end D5.S3.Quantum.PureState.FourCopyConcentrationRefutation
