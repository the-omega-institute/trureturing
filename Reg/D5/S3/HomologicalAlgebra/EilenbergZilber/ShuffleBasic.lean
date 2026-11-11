import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleBasic

/-! Source-bound all-degree shuffle-sign observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleBasic
open _root_.D5.S3.HomologicalAlgebra.EilenbergZilber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, ℕ) (fun p => Shuffle p.1 p.2) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ u => u.sign) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℕ} (u : Shuffle p q),
    R.readout () ⟨p,q⟩ u = (-1 : ℤ) ^ (p*q) * u.swap.sign
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (Shuffle.trivialShuffle 0 0)
  change (0 : ℤ) = (-1 : ℤ) ^ (0*0) * (Shuffle.trivialShuffle 0 0).swap.sign at hh
  rw [← Shuffle.sign_eq_negOnePow_mul_swap_sign] at hh
  norm_num [Shuffle.sign_trivialShuffle] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1⟩, Shuffle.trivialShuffle 1 1, (Shuffle.trivialShuffle 1 1).swap, ?_⟩
  change (Shuffle.trivialShuffle 1 1).sign ≠ (Shuffle.trivialShuffle 1 1).swap.sign
  have h := Shuffle.sign_eq_negOnePow_mul_swap_sign (Shuffle.trivialShuffle 1 1)
  rw [Shuffle.sign_trivialShuffle] at h ⊢
  norm_num at h
  omega

def family : Registration arena
    (type_of% (@Shuffle.sign_eq_negOnePow_mul_swap_sign)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Shuffle.sign_eq_negOnePow_mul_swap_sign, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Shuffle.sign_eq_negOnePow_mul_swap_sign) (type_of% actual) Unit Unit := {
  unitName := `D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.sign_eq_negOnePow_mul_swap_sign.__information_unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleBasic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleBasic
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms audit
end
end Reg.D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleBasic
