import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension
import Reg.Support.DependentFamily

/-! Source-equivalence registration for the positive extension criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension

noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun anchor => nomatch anchor)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (pA pB pC : ℝ) (α β : ℂ),
    Extendible pA pB pC α β ↔
      minDouble pA pB pC ≤ pA ∧ 0 ≤ pB ∧ minDouble pA pB pC ≤ pC ∧
      Complex.normSq α ≤ pB * (pA - minDouble pA pB pC) ∧
      R.readout () () (Complex.normSq β) (pB * (pC - minDouble pA pB pC))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : Extendible 0 0 0 0 0 := (extendible_iff 0 0 0 0 0).mpr (by
    norm_num [minDouble])
  exact ((h 0 0 0 0 0).mp he).2.2.2.2

def family : Registration arena (type_of% @extendible_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@extendible_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have impossible : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) (le_refl 0)
    norm_num at impossible

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@extendible_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension.extendible_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension
