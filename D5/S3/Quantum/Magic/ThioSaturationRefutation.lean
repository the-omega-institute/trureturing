/- GID: D5/S3/Quantum/Magic/ThioSaturationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ThioSaturationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/ThioSaturationRefutation.claim; result=D5/S3/Quantum/Magic/ThioSaturationRefutation.result; claim=D5/S3/Quantum/Magic/ThioSaturationRefutation.claim
   digest: A noisy Strange qutrit saturates the purity bound with eight Wigner coordinates. -/

import D5.S3.Quantum.Algebra.WeylDisplacementTrace
import D5.S3.Entropy.EntropyEquality
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
open scoped BigOperators Matrix
open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Entropy.MaxEntropy

namespace D5.S3.Quantum.Magic.ThioSaturationRefutation

/-- The phase-adjusted displacement in the source convention, Eq. (19). -/
def grossDisplacement (q : ℕ) [NeZero q] (a b : ZMod q) : Matrix (ZMod q) (ZMod q) ℂ :=
  windowRoot q ^ (a * b * (((q + 1) / 2 : ℕ) : ZMod q)).val • displacement q a b

/-- The source's sum, including its factor `1/q²`. -/
def grossOrigin (q : ℕ) [NeZero q] : Matrix (ZMod q) (ZMod q) ℂ :=
  ((q : ℂ) ^ 2)⁻¹ • ∑ a, ∑ b, grossDisplacement q a b

/-- Local source phase-space operators; dagger means complex conjugate transpose. -/
def grossLocal (q : ℕ) [NeZero q] (a b : ZMod q) : Matrix (ZMod q) (ZMod q) ℂ :=
  grossDisplacement q a b * grossOrigin q * (grossDisplacement q a b)ᴴ

/-- Tensor product over the local odd dimensions, written on the dependent product basis. -/
def grossTensor (n : ℕ) (q : Fin n → ℕ) (hq : ∀ k, NeZero (q k))
    (a b i j : (k : Fin n) → ZMod (q k)) : ℂ :=
  ∏ k, @grossLocal (q k) (hq k) (a k) (b k) (i k) (j k)

/-- Rank-one projector of a column of a complex orthonormal basis matrix. -/
def columnProjector {I : Type} (U : Matrix I I ℂ) (a : I) : Matrix I I ℂ :=
  Matrix.vecMulVec (fun i => U i a) (fun j => star (U j a))

/-- Source MUB-KD frames, Eq. (17), with both complete bases and all overlaps. -/
def IsMUBKD {I L : Type} [Fintype I] [DecidableEq I]
    (S : L → Matrix I I ℂ) : Prop :=
  ∃ A B : Matrix I I ℂ, Aᴴ * A = 1 ∧ Bᴴ * B = 1 ∧
    (∀ a b, Complex.normSq (∑ i, star (A i a) * B i b) = (Fintype.card I : ℝ)⁻¹) ∧
    ∃ labels : L ≃ I × I, ∀ l,
      S l = columnProjector A (labels l).1 * columnProjector B (labels l).2

/-- Exact odd-local Gross tensor frames, allowing relabeling and an arbitrary orthonormal
computational basis. The dual operators are `card I • S l` as in Eq. (20). -/
def IsGross {I L : Type} [Fintype I] [DecidableEq I]
    (S : L → Matrix I I ℂ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ q : Fin n → ℕ,
    (∀ k, 3 ≤ q k ∧ Odd (q k)) ∧ ∃ hq : ∀ k, NeZero (q k),
    ∃ basis : I ≃ ((k : Fin n) → ZMod (q k)),
    ∃ labels : L ≃ (((k : Fin n) → ZMod (q k)) × ((k : Fin n) → ZMod (q k))),
    ∃ U : Matrix I I ℂ, Uᴴ * U = 1 ∧ ∀ l,
      S l = U * (fun i j => grossTensor n q hq (labels l).1 (labels l).2 (basis i) (basis j)) * Uᴴ

/-- The union of the two source classes, without an arbitrary-frame replacement. -/
def IsSourceFrame {I L : Type} [Fintype I] [DecidableEq I]
    (S : L → Matrix I I ℂ) : Prop := IsMUBKD S ∨ IsGross S

/-- Eq. (9), before taking a real part. -/
def coordinate {I : Type} [Fintype I] (rho S : Matrix I I ℂ) : ℂ :=
  Matrix.trace (rho * Sᴴ)

/-- Coordinate support counts nonzero coordinates, rather than matrix rank. -/
def coordinateSupport {L : Type} [Fintype L] (Q : L → ℂ) : ℕ :=
  (Finset.univ.filter fun l => Q l ≠ 0).card

/-- Natural-log Shannon entropy, with `negMulLog 0 = 0`; no coordinate is discarded. -/
def coordinateEntropy {L : Type} [Fintype L] (Q : L → ℂ) : ℝ :=
  shannonEntropy fun l => (Q l).re

/-- The unchanged universal only-multiples saturation assertion. Purity includes both
endpoints. Q positivity includes zero and also asserts that the complex law is real. -/
def claim : Prop :=
  ∀ (I L : Type) [Fintype I] [DecidableEq I] [Fintype L],
    2 ≤ Fintype.card I → ∀ (S : L → Matrix I I ℂ), IsSourceFrame S →
    ∀ rho : Matrix I I ℂ, rho.PosSemidef → Matrix.trace rho = 1 →
    let Q := fun l => coordinate rho (S l)
    let tau := (Matrix.trace (rho * rho)).re
    (∀ l, (Q l).im = 0 ∧ 0 ≤ (Q l).re) →
    (∑ l, Q l) = 1 →
    (Fintype.card I : ℝ)⁻¹ ≤ tau → tau ≤ 1 →
    coordinateEntropy Q = -Real.log tau + Real.log (Fintype.card I) →
    ∃ delta : ℕ, 1 ≤ delta ∧ delta ≤ Fintype.card I ∧
      coordinateSupport Q = delta * Fintype.card I

/-- The known noisy Strange state, on the source residue basis. -/
def rho : Matrix (ZMod 3) (ZMod 3) ℂ :=
  !![1/4, 0, 0; 0, 3/8, -1/8; 0, -1/8, 3/8]

private theorem root_cube : windowRoot 3 ^ 3 = 1 :=
  (windowRoot_isPrimitiveRoot 3).pow_eq_one

private theorem root_sum : 1 + windowRoot 3 + windowRoot 3 ^ 2 = 0 := by
  have h := (windowRoot_isPrimitiveRoot 3).geom_sum_eq_zero (by norm_num : 1 < 3)
  simpa [Finset.sum_range_succ, pow_zero, pow_one, add_assoc] using h

end D5.S3.Quantum.Magic.ThioSaturationRefutation
