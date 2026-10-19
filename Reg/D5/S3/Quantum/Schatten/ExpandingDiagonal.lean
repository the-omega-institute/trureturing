import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.ExpandingDiagonal
import Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm

namespace Reg.D5.S3.Quantum.Schatten.ExpandingDiagonal
open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.Quantum.Schatten.UINorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
open Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev relationSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

namespace SubsetProducts

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (x y : Fin n → ℝ)
    (_hx : ∀ i, 0 ≤ x i) (_hy : ∀ i, 0 ≤ y i) (_hyanti : Antitone y)
    (_hprod : ∀ I : Finset (Fin n),
      (∏ i ∈ I, x i) ≤ ∏ j : Fin I.card, y ⟨j.val, by
        have h := Finset.card_le_card (Finset.subset_univ I)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        omega⟩),
    R.readout () () (ν.N (diagonal (fun i => (x i : ℂ))))
      (ν.N (diagonal (fun i => (y i : ℂ))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 0 zeroDimNorm (fun _ => 0) (fun _ => 0)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro I; simp)

def source_registration : Registration arena (type_of% @N_diagonal_subsetProducts_le) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@N_diagonal_subsetProducts_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law orderActual rejected
    rejected_law
  dependence := order_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@N_diagonal_subsetProducts_le) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.N_diagonal_subsetProducts_le.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.ExpandingDiagonal.SubsetProducts.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.ExpandingDiagonal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end SubsetProducts


namespace ExpandingLower

abbrev arena : Arena where
  signature := relationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (a b : Fin n → ℝ)
    (_ha : ∀ i, 0 ≤ a i) (_hb : ∀ i, 0 ≤ b i),
    ∃ σ : Equiv.Perm (Fin n), ∀ T : Matrix (Fin n) (Fin n) ℂ,
      (Tᴴ * T - 1).PosSemidef →
      R.readout () () (ν.N (diagonal (fun i => (a i : ℂ)) * σ.permMatrix ℂ *
        diagonal (fun i => (b i : ℂ))))
        (ν.N (diagonal (fun i => (a i : ℂ)) * T * diagonal (fun i => (b i : ℂ))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨σ, hσ⟩ := @h 0 zeroDimNorm (fun _ => 0) (fun _ => 0)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
  exact hσ 1 (by simpa using (Matrix.PosSemidef.zero :
    (0 : Matrix (Fin 0) (Fin 0) ℂ).PosSemidef))

def source_registration : Registration arena (type_of% @exists_permutation_expanding_lower_bound) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@exists_permutation_expanding_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law orderActual rejected
    rejected_law
  dependence := order_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_permutation_expanding_lower_bound) (Realization relationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.exists_permutation_expanding_lower_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Schatten.ExpandingDiagonal.ExpandingLower.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize relationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.ExpandingDiagonal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ExpandingLower

end
end Reg.D5.S3.Quantum.Schatten.ExpandingDiagonal
