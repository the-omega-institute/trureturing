import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance
import Reg.Support.DependentFamily

/-! Complete source telescopes with typed variation, sensitivity and dependence proofs. -/
namespace Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
open _root_.D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Matrix ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
private def testSector : Sector := ⟨0,1,2⟩
private lemma test_regular : Regular testSector := by
  norm_num [Regular,testSector,delta,alpha,beta,Complex.normSq_apply]

namespace Numerator
abbrev signature : Signature where
  Params := Unit
  State _ := Bond
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bond
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (s : Sector), Regular s → ∀ (z : ℂ), z ≠ 0 → ∀ (p q : ℕ) (P H : Bond),
    A.readout () () (leftNumerator s z p P) = (Gamma s*Complex.normSq z : ℂ)^p • trialLeft s p P z ∧
    A.readout () () (rightNumerator s z q H) =
      ((Gamma s*Complex.normSq z : ℂ)^q * (d s^2*Complex.normSq z^2 : ℂ)) • trialRight s q H z
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrFun (congrFun ((h testSector test_regular 1 (by norm_num) 0 0 1 0).1) 0) 0
  norm_num [rejected,realize,trialLeft] at hh
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,(fun _ _ => 1),?_⟩
  intro h
  have h0 := congrFun (congrFun h 0) 0
  exact zero_ne_one (show (0 : ℂ) = 1 from h0)
def source_registration : Registration arena (type_of% @numerator_clear) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@numerator_clear,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@numerator_clear) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance.numerator_clear.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance.Numerator.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Numerator

namespace Determinant
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (s : Sector), Regular s → ∀ (z : ℂ), z ≠ 0 → ∀ (p q : ℕ) (P H : Bond),
    A.readout () () (leftNumerator s z p P).det.re = cL s p z * (residual s p q P H z).re ∧
    A.readout () () (rightNumerator s z q H).det.re = cR s q z * (residual s p q P H z).im
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h testSector test_regular 1 (by norm_num) 0 0 1 0).1
  norm_num [rejected,realize,cL,_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization.residual,trialLeft] at hh
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]
def source_registration : Registration arena (type_of% @determinant_clear) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@determinant_clear,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@determinant_clear) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance.determinant_clear.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance.Determinant.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Determinant

namespace Positive
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (s : Sector), Regular s → ∀ (z : ℂ), z ≠ 0 → ∀ (p q : ℕ),
    0 < A.readout () () (cL s p z) ∧ 0 < A.readout () () (cR s q z)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h testSector test_regular 1 (by norm_num) 0 0).1
  norm_num [rejected,realize] at hh
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual,realize]
def source_registration : Registration arena (type_of% @clearance_positive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@clearance_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@clearance_positive) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance.clearance_positive.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance.Positive.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Positive
end
end Reg.D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance
