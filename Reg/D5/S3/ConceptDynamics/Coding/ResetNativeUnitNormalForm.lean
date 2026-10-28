import D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option maxHeartbeats 800000
namespace Reg.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_gluingAudit
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
  Params := {q : ℕ // 0 < q}
  State p := Native p.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Compatible p.val
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ p v => nativeGluing p.val p.property v) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q),
    (∀ z : QF q, r.readout () ⟨q,hq⟩ (nativeIntEquiv q hq z) = gluing q z) ∧
    (∀ v : Native q, r.readout () ⟨q,hq⟩ (resetTheta q v) =
      gluing q (fp q X) * r.readout () ⟨q,hq⟩ v) ∧
    (∀ v : Native q, r.readout () ⟨q,hq⟩
      (InertGroupBlockConjugacy.groupAction (resetMatrix q) (Multiplicative.ofAdd true) v) =
      gluing q (fp q (W q)) * r.readout () ⟨q,hq⟩ v) ∧
    (∀ z : ℤ, ∀ v : Native q, r.readout () ⟨q,hq⟩ (z • v) = z • r.readout () ⟨q,hq⟩ v) ∧
    (∀ n : ℕ, ∀ v : InertGroupBlockConjugacy.VertexModule Sign q,
      r.readout () ⟨q,hq⟩ (ResetNativeIntegerChart.nativeStage q n v) =
        gluing q (ringEquiv q (pp q
          (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial resetLabel q
            ((resetInverse q hq ^ n) v)))))
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := (h 2 (by decide)).1 1
  have hz : (0 : Compatible 2) = 1 := by simpa [bad, realize] using he
  have hg := congrArg (fun z : Compatible 2 => golden z.val.1) hz
  have ha := congrArg GoldenInt.a hg
  norm_num at ha
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, by decide⟩, nativeIntEquiv 2 (by decide) 0,
    nativeIntEquiv 2 (by decide) 1, ?_⟩
  intro h
  change nativeGluing 2 (by decide) (nativeIntEquiv 2 (by decide) 0) =
    nativeGluing 2 (by decide) (nativeIntEquiv 2 (by decide) 1) at h
  rw [(native_gluing 2 (by decide)).1, (native_gluing 2 (by decide)).1] at h
  have hg := congrArg (fun z : Compatible 2 => golden z.val.1) h
  have ha := congrArg GoldenInt.a hg
  norm_num at ha
def evidence : Registration arena (∀ (q : ℕ) (hq : 0 < q),
    (∀ z : QF q, nativeGluing q hq (nativeIntEquiv q hq z) = gluing q z) ∧
    (∀ v : Native q, nativeGluing q hq (resetTheta q v) =
      gluing q (fp q X) * nativeGluing q hq v) ∧
    (∀ v : Native q, nativeGluing q hq
      (InertGroupBlockConjugacy.groupAction (resetMatrix q) (Multiplicative.ofAdd true) v) =
      gluing q (fp q (W q)) * nativeGluing q hq v) ∧
    (∀ z : ℤ, ∀ v : Native q, nativeGluing q hq (z • v) = z • nativeGluing q hq v) ∧
    (∀ n : ℕ, ∀ v : InertGroupBlockConjugacy.VertexModule Sign q,
      nativeGluing q hq (ResetNativeIntegerChart.nativeStage q n v) =
        gluing q (ringEquiv q (pp q
          (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial resetLabel q
            ((resetInverse q hq ^ n) v)))))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_gluing, bad, bad_law⟩
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
      (_root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_gluing) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_gluingAudit.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_gluingAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => nativeGluing p.val p.property v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_gluingAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_normal_formsAudit
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
  Params := Unit
  State p := ℤ × Fin 2 × Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := N → N
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ p v => ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v))) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ v => v) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := (∀ A : N ≃ₗ[ℤ] N, (∀ v, A (resetTheta 2 v) = resetTheta 2 (A v)) →
      ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
        A v = r.readout () () p v) ∧
    (∀ h : ResetFullAut 2, ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
      rho 2 (by omega) h v =
        r.readout () () p v)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨p,_,hp⟩ := h.1 (LinearEquiv.refl ℤ N) (by intro v; rfl)
  have h0 := hp (0,0,0) (by intro v; rfl)
  have h1 := hp (1,0,0) (by intro v; rfl)
  have he := congrArg Prod.fst (h0.trans h1.symm)
  norm_num at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0,0,0), (1,0,0), ?_⟩
  intro h
  obtain ⟨p,_,hp⟩ := native_normal_forms.1 (LinearEquiv.refl ℤ N) (by intro v; rfl)
  have h0 : ∀ v : N, v = ((-1 : ℤ) ^ (0 : Fin 2).val) •
      ((U ^ (0 : Fin 2).val) ((T ^ (0 : ℤ)) v)) := by intro v; simp
  have h1 : ∀ v : N, v = ((-1 : ℤ) ^ (0 : Fin 2).val) •
      ((U ^ (0 : Fin 2).val) ((T ^ (1 : ℤ)) v)) := by
    intro v
    have hv := congrFun h v
    change ((-1 : ℤ) ^ (0 : Fin 2).val) •
      ((U ^ (0 : Fin 2).val) ((T ^ (0 : ℤ)) v)) = _ at hv
    exact (h0 v).trans hv
  have he := congrArg Prod.fst ((hp (0,0,0) h0).trans (hp (1,0,0) h1).symm)
  norm_num at he
def evidence : Registration arena ((∀ A : N ≃ₗ[ℤ] N, (∀ v, A (resetTheta 2 v) = resetTheta 2 (A v)) →
      ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
        A v = ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v))) ∧
    (∀ h : ResetFullAut 2, ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
      rho 2 (by omega) h v =
        ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v)))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_normal_forms, bad, bad_law⟩
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
      (_root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_normal_forms) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_normal_formsAudit.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_normal_formsAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p v => ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm.native_normal_formsAudit
