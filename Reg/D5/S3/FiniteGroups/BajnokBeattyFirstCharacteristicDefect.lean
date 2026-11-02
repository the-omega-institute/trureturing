import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyFirstCharacteristicDefect
import Reg.Support.DependentFamily

/-! Complete original-telescope DependentFamily proof evidence for
`D5.S3.FiniteGroups.BajnokBeattyFirstCharacteristicDefect.first_characteristic_defect`.
A faithful four-slot outer registration is attempted in this delivery.
Outer discovery status is reported by the scoped inspector; no validation is inferred
from compilation alone.
Only genuine kernel-checked family proof terms are retained here; no
`declared_validated` status is claimed. The complete coefficient-prefix, exact-gap and polynomial-inequality conclusion
is preserved in the closed law, observing the actual group-order family. -/

/-! UNFINISHED outer four-slot audit: the selected batch failed at the concrete
consumer with `contract.discovery:rigid_universes`; the generic outer assessment
was not completed by that failed batch. Both outer terms genuinely compiled.
See https://github.com/the-omega-institute/trureturing/issues/24448.
The full-telescope family evidence below is kernel checked; it is not a
`declared_validated` outer registration. -/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyFirstCharacteristicDefect
open _root_.D5.S3.FiniteGroups.BajnokBeattyFirstCharacteristicDefect
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments (graph q19 q33)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

private theorem audit_vertices_finite (p t : ℤ) (hp3 : 3 ≤ p) (ht : 2 ≤ t) :
    Finite (ZMod p.natAbs × ZMod (p * (((6*t-1)^2-9)/2)).natAbs) := by
  have hp : 0 < p := by omega
  have hf : ((6*t-1)^2-9)/2 = (3*t+1)*(6*t-4) := by
    have h : (6*t-1)^2-9 = 2*((3*t+1)*(6*t-4)) := by ring
    rw [h]
    omega
  have hD : 0 < ((6*t-1)^2-9)/2 := by
    rw [hf]
    exact mul_pos (by omega) (by omega)
  letI : NeZero p.natAbs := ⟨Int.natAbs_ne_zero.mpr hp.ne'⟩
  letI : NeZero (p * (((6*t-1)^2-9)/2)).natAbs :=
    ⟨Int.natAbs_ne_zero.mpr (mul_pos hp hD).ne'⟩
  infer_instance

abbrev coefficientSignature : Signature where
  Params := Unit
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def groupOrder (pt : ℤ × ℤ) : ℤ :=
  (Nat.card (ZMod pt.1.natAbs × ZMod (pt.1 * (((6*pt.2-1)^2-9)/2)).natAbs) : ℤ)

noncomputable def actualCoefficient : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ pt => groupOrder pt) (fun e => nomatch e)

noncomputable def rejectedCoefficient : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ pt => groupOrder pt + 1) (fun e => nomatch e)

abbrev coefficientArena : Arena where
  signature := coefficientSignature
  Law R := ∀ (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t),
    let m : ℤ := 6 * t - 1
    let D : ℤ := (m ^ 2 - 9) / 2
    let H := ZMod p.natAbs × ZMod (p * D).natAbs
    let N : ℤ := p ^ 2 * D
    let n : ℕ := (p * (m - 3)).toNat
    letI : Finite H := audit_vertices_finite p t hp3 ht
    letI : Fintype H := Fintype.ofFinite H
    let C19 : SimpleGraph H := graph (q19 p D t)
    let C33 : SimpleGraph H := graph (q33 p D t)
    let A19 : Matrix H H ℂ := C19.adjMatrix ℂ
    let A33 : Matrix H H ℂ := C33.adjMatrix ℂ
    R.readout () () (p,t) = N ∧
    0 < n ∧ n ≤ Fintype.card H ∧
    (∀ j : ℕ, j < n →
      A19.charpoly.coeff (Fintype.card H - j) =
        A33.charpoly.coeff (Fintype.card H - j)) ∧
    (A33.charpoly.coeff (Fintype.card H - n) -
      A19.charpoly.coeff (Fintype.card H - n) =
        ((-2 * p * (3 * t + 1) : ℤ) : ℂ)) ∧
    A19.charpoly ≠ A33.charpoly

private theorem actual_law : coefficientArena.Law actualCoefficient := by
  exact first_characteristic_defect

private theorem rejected_law : ¬ coefficientArena.Law rejectedCoefficient := by
  intro h
  have bad := (h 3 2 (by norm_num) (by decide) (by norm_num)).1
  have good := (first_characteristic_defect 3 2 (by norm_num) (by decide) (by norm_num)).1
  change groupOrder (3,2) + 1 = 504 at bad
  change groupOrder (3,2) = 504 at good
  omega

noncomputable def coefficientSource : Registration coefficientArena
    (type_of% first_characteristic_defect) where
  actual := actualCoefficient
  bridge := Iff.rfl
  variation := ⟨actual_law, rejectedCoefficient, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedCoefficient, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (3,2), (5,2), ?_⟩
    have h3 := (first_characteristic_defect 3 2 (by norm_num) (by decide) (by norm_num)).1
    have h5 := (first_characteristic_defect 5 2 (by norm_num) (by decide) (by norm_num)).1
    change groupOrder (3,2) = 504 at h3
    change groupOrder (5,2) = 1400 at h5
    change groupOrder (3,2) ≠ groupOrder (5,2)
    omega


end Reg.D5.S3.FiniteGroups.BajnokBeattyFirstCharacteristicDefect
