/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229691Strip.result)
Valid: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
decidableValid: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
cl: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
zeroBudgetSector: proof_shape=bind-only; consumers=T
T: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
initial: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
terminal: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
W: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
-/

import Mathlib.Data.Matrix.Block
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData

/-! Finite class data consumed by the registered settlement. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripData
open HardinA229583StripData (Row Boundary horizontal antidiagonal boundary cross)
def Valid (p : Boundary) (d : ℕ) : Prop :=
  d ≤ 2 ∧ (Finset.univ.filter fun j : Fin 3 => p j.castSucc = p j.succ).card ≤ 2 - d
private instance decidableValid (p : Boundary) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Boundary) (d : ℕ) : Fin 27 :=
  let c := D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.cls
    (p 0, p 1, p 2, p 3)
  match d, c.val with
  | 0, 1 => 14
  | 0, 2 => 15
  | 0, 3 => 16
  | 0, 4 => 17
  | 0, 5 => 18
  | 0, 6 => 19
  | 0, 7 => 20
  | 0, 8 => 21
  | 0, 9 => 22
  | 0, 10 => 23
  | 0, 11 => 24
  | 0, 12 => 25
  | 1, 2 => 4
  | 1, 4 => 5
  | 1, 5 => 6
  | 1, 6 => 7
  | 1, 7 => 8
  | 1, 8 => 9
  | 1, 10 => 10
  | 1, 11 => 11
  | 1, 12 => 12
  | 1, 13 => 13
  | 2, 6 => 0
  | 2, 7 => 1
  | 2, 11 => 2
  | 2, 12 => 3
  | _, _ => 26
private def zeroBudgetSector : Fin 13 → Fin 10 ⊕ Fin 3 :=
  ![Sum.inr 0, Sum.inl 0, Sum.inr 1, Sum.inl 1, Sum.inl 2, Sum.inl 3,
    Sum.inl 4, Sum.inl 5, Sum.inr 2, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9]
def T : Matrix (Fin 27) (Fin 27) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 14 ⊕ Fin 13 ≃ Fin 27)
    (finSumFinEquiv : Fin 14 ⊕ Fin 13 ≃ Fin 27)
    (Matrix.fromBlocks (HardinA229583StripData.T)
      (![![2, 7, 1, 7, 3, 5, 5, 5, 2, 5, 5, 5, 5],
      ![0, 7, 2, 7, 2, 8, 8, 5, 3, 5, 5, 5, 6],
      ![0, 2, 4, 2, 7, 5, 5, 5, 3, 5, 5, 5, 6],
      ![4, 5, 2, 5, 6, 2, 2, 8, 1, 8, 8, 8, 4],
      ![0, 1, 0, 1, 3, 7, 7, 1, 0, 1, 7, 7, 2],
      ![0, 2, 0, 2, 2, 7, 7, 2, 0, 2, 8, 8, 2],
      ![0, 1, 0, 1, 1, 8, 8, 5, 0, 5, 2, 2, 4],
      ![0, 1, 0, 1, 5, 3, 3, 2, 0, 2, 5, 5, 3],
      ![0, 2, 0, 2, 4, 2, 2, 3, 0, 3, 6, 6, 3],
      ![0, 5, 0, 5, 1, 7, 7, 2, 0, 2, 5, 5, 3],
      ![0, 4, 0, 4, 2, 5, 5, 1, 0, 1, 4, 4, 3],
      ![0, 4, 0, 4, 2, 7, 7, 3, 0, 3, 6, 6, 3],
      ![0, 2, 0, 2, 4, 6, 6, 1, 0, 1, 4, 4, 3],
      ![0, 2, 0, 2, 2, 5, 5, 4, 0, 4, 8, 8, 2]])
      (0)
      ((Matrix.fromBlocks
        (HardinA229583StripData.T.submatrix (fun i : Fin 10 => i.natAdd 4)
          (fun j : Fin 10 => j.natAdd 4))
        (0 : Matrix (Fin 10) (Fin 3) ℤ)
        (![![0, 0, 0, 1, 1, 0, 0, 2, 2, 0],
          ![0, 0, 0, 1, 1, 0, 0, 2, 2, 0],
          ![0, 0, 0, 3, 3, 0, 0, 0, 0, 0]])
        (0 : Matrix (Fin 3) (Fin 3) ℤ)).submatrix zeroBudgetSector zeroBudgetSector))
def initial : Fin 27 → ℤ :=
  Fin.append HardinA229583StripData.initial (![12, 6, 12, 6, 6, 0, 0, 6, 12, 6, 0, 0, 6])
def terminal : Fin 27 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 8 → Fin 27 → ℤ :=
  Fin.append (fun i =>
    let w := HardinA229583StripData.W i
    let v := (![![12, 6, 6, 0, 0, 6, 6, 0, 0],
      ![72, 486, 486, 942, 942, 510, 510, 954, 954],
      ![936, 9702, 9702, 37350, 37350, 10050, 10050, 37278, 37278],
      ![12744, 173070, 173070, 993438, 993438, 179586, 179586, 958446, 958446],
      ![174312, 2913894, 2913894, 22210038, 22210038, 3033018, 3033018, 20838870, 20838870],
      ![2385288, 47327166, 47327166, 449438382, 449438382, 49380354, 49380354, 412458318, 412458318]]) i
    Fin.append w ![v 0, v 1, w 4, v 2, w 7, v 3, v 4, v 5, w 9, v 6, v 7, v 8, w 11])
    (![![87191316, 87191316, 68076936, 68076936, 48962556, 48962556, 87191316, 1116505782, 1116505782, 51756084, 51756084, 961725960, 961725960, 68076936, 32641704, 749602998, 48962556, 749602998, 1116505782, 8519487174, 8519487174, 783513162, 51756084, 783513162, 7681405446, 7681405446, 961725960],
      ![1193183460, 1193183460, 931609512, 931609512, 670035564, 670035564, 1193183460, 17763290766, 17763290766, 708264324, 708264324, 15100570152, 15100570152, 931609512, 446690376, 11653127694, 670035564, 11653127694, 17763290766, 154178657982, 154178657982, 12196766322, 708264324, 12196766322, 137032507998, 137032507998, 15100570152]])
end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripData
