import D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option maxHeartbeats 800000
namespace Reg.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.centralizingMap_scalarAudit
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
  Params := (Σ q : {q : ℕ // 0 < q}, {A : Native q.val →ₗ[ℤ] Native q.val // ∀ x, A (resetTheta q.val x) = resetTheta q.val (A x)})
  State p := QF p.1.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := QF p.1.val
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ p b => centralizingMap p.1.val p.1.property p.2.val p.2.property b) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (A : Native q →ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) (b : QF q),
    r.readout () ⟨⟨q,hq⟩,⟨A,ht⟩⟩ b = b * r.readout () ⟨⟨q,hq⟩,⟨A,ht⟩⟩ 1
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := h 2 (by decide) (LinearMap.id : Native 2 →ₗ[ℤ] Native 2) (by intro x; rfl) 0
  have hz : (1 : QF 2) = 0 := by simpa [bad, realize] using he
  have hg := congrArg goldenComponent hz
  have ha := congrArg GoldenInt.a hg
  norm_num at ha
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨⟨2, by decide⟩, ⟨LinearMap.id, by intro x; rfl⟩⟩, 0, 1, ?_⟩
  intro h
  change (nativeIntEquiv 2 (by decide)).symm (nativeIntEquiv 2 (by decide) 0) =
    (nativeIntEquiv 2 (by decide)).symm (nativeIntEquiv 2 (by decide) 1) at h
  have hg := congrArg goldenComponent (by simpa using h : (0 : QF 2) = 1)
  have ha := congrArg GoldenInt.a hg
  norm_num at ha
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q) (A : Native q →ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) (b : QF q),
    centralizingMap q hq A ht b = b * centralizingMap q hq A ht 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.centralizingMap_scalar, bad, bad_law⟩
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
      (_root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.centralizingMap_scalar) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.centralizingMap_scalarAudit.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.centralizingMap_scalarAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => centralizingMap p.1.val p.1.property p.2.val p.2.property b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.centralizingMap_scalarAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.rho_timeAudit
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
  Params := (Σ q : {q : ℕ // 0 < q}, ResetFullAut q.val)
  State p := Native p.1.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Native p.1.val
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ p x => rho p.1.val p.1.property p.2 x) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ p _ => nativeIntEquiv p.1.val p.1.property 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (x : Native q),
    r.readout () ⟨⟨q,hq⟩,h⟩ (resetTheta q x) = resetTheta q (r.readout () ⟨⟨q,hq⟩,h⟩ x)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := h 2 (by decide) 1 0
  change nativeIntEquiv 2 (by decide) 1 =
    resetTheta 2 (nativeIntEquiv 2 (by decide) 1) at he
  have ht := (native_presentation 2 (by decide)).2.1 (1 : QF 2)
  rw [mul_one] at ht
  rw [← ht] at he
  have hg := congrArg goldenComponent ((nativeIntEquiv 2 (by decide)).injective he)
  rw [map_one] at hg
  change (1 : GoldenInt) = golden (AdjoinRoot.root (f 2)) at hg
  rw [quadratic_charts.2.2.1] at hg
  have hb := congrArg GoldenInt.b hg
  norm_num [phi] at hb
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨⟨2, by decide⟩,1⟩, 0, nativeIntEquiv 2 (by decide) 1, ?_⟩
  intro h
  have hz : (0 : Native 2) = nativeIntEquiv 2 (by decide) 1 := by
    simpa [actual, realize] using h
  have hi := congrArg (nativeIntEquiv 2 (by decide)).symm hz
  have hg := congrArg goldenComponent (by simpa using hi : (0 : QF 2) = 1)
  have ha := congrArg GoldenInt.a hg
  norm_num at ha
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (x : Native q),
    rho q hq h (resetTheta q x) = resetTheta q (rho q hq h x)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.rho_time, bad, bad_law⟩
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
      (_root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.rho_time) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.rho_timeAudit.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.rho_timeAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => rho p.1.val p.1.property p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel.rho_timeAudit
