import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral

/-! Source-bound audits of the reference logarithm in the forward identities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u w

open Matrix MeasureTheory RHLinalg Set
open scoped ComplexOrder ENNReal MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix
open _root_.D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Real.log) (fun e => nomatch e)

private def negativeOne : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev forwardArena : Arena where
  signature := signature
  Law L := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef),
    let E := forwardProfile hA.isHermitian hB.isHermitian
    IntegrableOn (fun s => (E s - rtrace (A - s • B)) / s) (Ioo 0 1) ∧
    IntegrableOn (fun s => E s / s) (Ioi 1) ∧
    (A * (CFC.log A - cfc (L.readout () ()) B)).trace.re =
      (∫ s in Ioo (0 : ℝ) 1, (E s - rtrace (A - s • B)) / s) +
      (∫ s in Ioi (1 : ℝ), E s / s) + rtrace (A - B)

private theorem forwardRejected : ¬ forwardArena.{u}.Law negativeOne := by
  intro h
  let n := ULift.{u} Unit
  have hp : (1 : Matrix n n ℂ).PosDef := Matrix.PosDef.one
  have hactual := integral_forwardProfile_eq_umegaki hp.posSemidef hp
  have hbad := @h n _ _ 1 1 hp.posSemidef hp
  have he := hactual.2.2.trans hbad.2.2.symm
  change ((1 : Matrix n n ℂ) * (CFC.log 1 - cfc Real.log 1)).trace.re =
    ((1 : Matrix n n ℂ) * (CFC.log 1 - cfc (fun _ : ℝ => (-1 : ℝ)) 1)).trace.re at he
  simp [CFC.log, cfc_apply_one, Matrix.trace_one, n] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

def forwardFamily : Registration forwardArena.{u}
    (type_of% @integral_forwardProfile_eq_umegaki.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_forwardProfile_eq_umegaki, negativeOne, forwardRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    forwardArena.Law actual negativeOne forwardRejected
  dependence := dependence

set_option linter.style.longLine false in
def forwardAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_forwardProfile_eq_umegaki.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral.integral_forwardProfile_eq_umegaki.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral.forwardFamily
  realizationSource := none
  generated := false
  arena := .source ⟨forwardArena⟩
  objectArena := .source ⟨forwardArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source forwardArena ⟨forwardFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev differenceArena : Arena where
  signature := signature
  Law L := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {k : Type w} [Fintype k] [DecidableEq k]
    {A B : Matrix n n ℂ} {C D : Matrix k k ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) (hC : C.PosSemidef) (hD : D.PosDef)
    (hmA : rtrace A = rtrace C) (hmB : rtrace B = rtrace D)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hloAB : u • B ≤ A) (hhiAB : A ≤ v • B) (hloCD : u • D ≤ C) (hhiCD : C ≤ v • D),
    let E := forwardProfile hA.isHermitian hB.isHermitian
    let F := forwardProfile hC.isHermitian hD.isHermitian
    EqOn E F (Iic u) ∧ EqOn E F (Ici v) ∧
    IntegrableOn (fun s => (E s - F s) / s) (Icc u v) ∧
    (A * (CFC.log A - cfc (L.readout () ()) B)).trace.re -
      (C * (CFC.log C - cfc Real.log D)).trace.re =
      ∫ s in u..v, (E s - F s) / s

private theorem differenceRejected : ¬ differenceArena.{u,w}.Law negativeOne := by
  intro h
  let n := ULift.{u} Unit
  let k := ULift.{w} Unit
  have hp : (1 : Matrix n n ℂ).PosDef := Matrix.PosDef.one
  have hq : (1 : Matrix k k ℂ).PosDef := Matrix.PosDef.one
  have hm : rtrace (1 : Matrix n n ℂ) = rtrace (1 : Matrix k k ℂ) := by
    simp [rtrace, Matrix.trace_one, n, k]
  have hn : (1 : ℝ) • (1 : Matrix n n ℂ) ≤ 1 := by simp
  have hnr : (1 : Matrix n n ℂ) ≤ (1 : ℝ) • (1 : Matrix n n ℂ) := by simp
  have hk : (1 : ℝ) • (1 : Matrix k k ℂ) ≤ 1 := by simp
  have hkr : (1 : Matrix k k ℂ) ≤ (1 : ℝ) • (1 : Matrix k k ℂ) := by simp
  have he := (@h n _ _ k _ _ 1 1 1 1 hp.posSemidef hp hq.posSemidef hq hm hm
    1 1 zero_lt_one le_rfl hn hnr hk hkr).2.2.2
  change ((1 : Matrix n n ℂ) * (CFC.log 1 - cfc (fun _ : ℝ => (-1 : ℝ)) 1)).trace.re -
    ((1 : Matrix k k ℂ) * (CFC.log 1 - cfc Real.log 1)).trace.re = (∫ s in (1 : ℝ)..1,
      (forwardProfile hp.isHermitian hp.isHermitian s -
        forwardProfile hq.isHermitian hq.isHermitian s) / s) at he
  simp [CFC.log, cfc_apply_one, Matrix.trace_one, n, k] at he

def differenceFamily : Registration differenceArena.{u,w}
    (type_of% @integral_forwardProfile_sub_eq_umegaki_sub.{u,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_forwardProfile_sub_eq_umegaki_sub, negativeOne, differenceRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    differenceArena.Law actual negativeOne differenceRejected
  dependence := dependence

set_option linter.style.longLine false in
def differenceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_forwardProfile_sub_eq_umegaki_sub.{u,w}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral.integral_forwardProfile_sub_eq_umegaki_sub.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral.differenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨differenceArena⟩
  objectArena := .source ⟨differenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source differenceArena ⟨differenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "arg", "fn", "arg", "fn",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral
