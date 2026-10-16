import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching
open LeanInformationAudit
universe u

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => x^2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : ℝ) (x : E) (D : UnitDictionary E) (hlam : 0 ≤ lam),
    0 ≤ codeCost lam x D ∧ codeCost lam x D ≤ R.readout ⟨()⟩ () ‖x‖ / 2

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let e : EuclideanSpace ℝ (ULift.{u} Unit) := EuclideanSpace.single ⟨()⟩ 1
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.single]
  let D := canonicalDictionary e e he he
  have hc := h 0 0 D (by norm_num)
  have hlo := hc.1
  have hhi := hc.2
  norm_num [rejected, realize] at hhi
  linarith

def family : Registration arena.{u} (type_of% (@code_cost_bounds.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@code_cost_bounds.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    norm_num [actual, realize]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@code_cost_bounds.{u}) (type_of% (realize signature.{u}
      (fun _ _ x => x^2) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching.code_cost_bounds.__information_unit
  realizationName := `Reg.D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x => x^2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching
