import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.HeadleyCoordinateKernel
import Reg.Support.DependentFamily

/-! The full exponent-family readout for the two-coordinate decrease identity. -/

namespace Reg.D5.S3.FiniteGroups.HeadleyCoordinateKernel
open _root_.D5.S3.FiniteGroups.HeadleyCoordinateKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ r : ℕ, Fin r × Fin r
  State p := Fin p.1 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature := realize signature
  (fun _ p e => ∑ k, lower e p.2.1 p.2.2 k) (fun x => nomatch x)

noncomputable def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun x => nomatch x)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℕ} (e : Fin r → ℕ) (i j : Fin r)
    (_ : i ≠ j) (_ : 0 < e i) (_ : 0 < e j),
    R.readout () ⟨r,(i,j)⟩ e + 2 = ∑ k, e k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ : Fin 2 => 2) 0 1 (by decide) (by decide) (by decide)
  norm_num [rejected, realize, Fin.sum_univ_succ] at hh

noncomputable def sourceRegistration : Registration arena (type_of% (@lower_sum_add_two)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lower_sum_add_two, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro role
    cases role
    refine ⟨⟨2,(0,1)⟩, (fun _ => 1), (fun _ => 2), ?_⟩
    decide

noncomputable def lowerSumRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@lower_sum_add_two) (Realization signature) (type_of% (@lower)) Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.HeadleyCoordinateKernel.lower_sum_unit
  realizationName := `Reg.D5.S3.FiniteGroups.HeadleyCoordinateKernel.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p e => ∑ k, lower e p.2.1 p.2.2 k) (fun x => nomatch x))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@lower)
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.HeadleyCoordinateKernel
    definition := none
    coordinates := #[0,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.HeadleyCoordinateKernel
