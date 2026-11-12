import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtIncidence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : Fin 15 → ℝ) (ha : ∀ i, 0 ≤ a i),
    ∃ (p : Fin 5 → ℝ) (π : Edge 6 ≃ Fin 15),
      (∀ i, 0 ≤ p i) ∧ (∑ i, (p i)^2 = 1) ∧
      R.readout () () (Real.sqrt (∑ i, (a i)^2)) (headValue a p π)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, π, hp, hn, hf⟩ := h (fun _ => 0) (fun _ => le_rfl)
  exact hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at hf

def family : Registration arena (type_of% (@head_exists)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@head_exists, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hji
        exact (hji (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@head_exists) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead.head_exists.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead
