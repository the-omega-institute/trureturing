import D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.ResetIntegralUnits

set_option maxHeartbeats 800000
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ × Fin 2 × Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (QF 2)ˣ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ p => normal p.1 p.2.1 p.2.2) (fun e => nomatch e)
abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ u : (QF 2)ˣ, ∃! p : ℤ × Fin 2 × Fin 2, u = r.readout () () p
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨p,_,hp⟩ := h 1
  have h0 := hp (0,0,0) rfl
  have h1 := hp (1,0,0) rfl
  have he := congrArg Prod.fst (h0.trans h1.symm)
  norm_num at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0,0,0), (1,0,0), ?_⟩
  intro h
  change normal 0 0 0 = normal 1 0 0 at h
  obtain ⟨p,_,hp⟩ := unit_normal_form (normal 0 0 0)
  have h0 := hp (0,0,0) rfl
  have h1 := hp (1,0,0) h
  have he := congrArg Prod.fst (h0.trans h1.symm)
  norm_num at he
def evidence : Registration arena
    (∀ u : (QF 2)ˣ, ∃! p : ℤ × Fin 2 × Fin 2, u = normal p.1 p.2.1 p.2.2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unit_normal_form, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def unit_normal_form_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits.unit_normal_form)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => normal p.1 p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits.quadratic_chartsAudit
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding
open _root_.D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open _root_.D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open _root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
open _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S0.Carrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped QuadraticAlgebra
noncomputable section
local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) := AddCommGroup.toIntModule _
abbrev signature : Signature where
  Params := Bool
  State p := match p with | true => Plus 2 | false => Minus 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := E₂
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ p => match p with | true => fun z => goldenReduce (golden z) | false => fun z => modTwo (eisenstein z)) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := IsField (Common 2) ∧ Nat.card (Common 2) = 4 ∧
    golden (AdjoinRoot.root (f 2)) = phi ∧
    eisenstein (AdjoinRoot.root (g 2)) = QuadraticAlgebra.omega ∧
    common (AdjoinRoot.root (reduce (g 2))) = QuadraticAlgebra.omega ∧
    (∀ z : Plus 2, common (rplus 2 z) = r.readout () true z) ∧
    (∀ z : Minus 2, common (rminus 2 z) = r.readout () false z)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := h.2.2.2.2.2.1 1
  have hn : (1 : E₂) = 0 := by simpa [bad, realize] using he
  have hr := congrArg QuadraticAlgebra.re hn
  norm_num at hr
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨true, (0 : Plus 2), (1 : Plus 2), ?_⟩
  intro h
  have hn : (0 : E₂) = 1 := by simpa [actual, realize] using h
  have hr := congrArg QuadraticAlgebra.re hn
  norm_num at hr
def evidence : Registration arena (IsField (Common 2) ∧ Nat.card (Common 2) = 4 ∧
    golden (AdjoinRoot.root (f 2)) = phi ∧
    eisenstein (AdjoinRoot.root (g 2)) = QuadraticAlgebra.omega ∧
    common (AdjoinRoot.root (reduce (g 2))) = QuadraticAlgebra.omega ∧
    (∀ z : Plus 2, common (rplus 2 z) = goldenReduce (golden z)) ∧
    (∀ z : Minus 2, common (rminus 2 z) = modTwo (eisenstein z))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits.quadratic_charts, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits.quadratic_charts) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits.quadratic_chartsAudit.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits.quadratic_chartsAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => match p with | true => fun z => goldenReduce (golden z) | false => fun z => modTwo (eisenstein z)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits.quadratic_chartsAudit
