import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiBKMPath

noncomputable section
open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator
open _root_.D5.S3.Quantum.Divergence.UmegakiBKMPath
open _root_.D5.S3.Divergence.LogDerivTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiBKMPath

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef),
    R.readout () () ((A * (CFC.log A - CFC.log B)).trace.re - (A - B).trace.re)
      (∫ t in (0 : ℝ)..1, (1 - t) *
        ((A - B) * logDeriv (B + t • (A - B)) (A - B)).trace.re)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := 0) 1 1 Matrix.PosDef.one Matrix.PosDef.one

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% @relativeEntropy_eq_integral_bkm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@relativeEntropy_eq_integral_bkm, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@relativeEntropy_eq_integral_bkm) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiBKMPath.relativeEntropy_eq_integral_bkm.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiBKMPath.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiBKMPath
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

universe u
abbrev conditionalArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {ι : Type u} [Fintype ι] [Nonempty ι]
    (A B : ι → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef),
    R.readout () ()
      ((∑ i, (A i * (CFC.log (A i) - CFC.log (B i))).trace.re) -
        ((∑ i, A i) * (CFC.log (∑ i, A i) - CFC.log (∑ i, B i))).trace.re)
      (∫ t in (0 : ℝ)..1, (1 - t) *
        ((∑ i, ((A i - B i) *
            logDeriv (B i + t • (A i - B i)) (A i - B i)).trace.re) -
          (((∑ i, A i) - ∑ i, B i) *
            logDeriv ((∑ i, B i) + t • ((∑ i, A i) - ∑ i, B i))
              ((∑ i, A i) - ∑ i, B i)).trace.re))

private theorem conditional_rejected_law : ¬ conditionalArena.{u}.Law rejected := by
  intro h
  exact h (n := 0) (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 1)
    (fun _ => Matrix.PosDef.one) (fun _ => Matrix.PosDef.one)

def conditionalFamily : Registration conditionalArena.{u}
    (type_of% @conditional_relativeEntropy_eq_integral_bkm.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conditional_relativeEntropy_eq_integral_bkm.{u}, rejected,
    conditional_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    conditionalArena.Law actual rejected conditional_rejected_law
  dependence := dependence

def conditionalAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@conditional_relativeEntropy_eq_integral_bkm.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiBKMPath.conditional_relativeEntropy_eq_integral_bkm.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiBKMPath.conditionalFamily
  realizationSource := none
  generated := false
  arena := .source ⟨conditionalArena⟩
  objectArena := .source ⟨conditionalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source conditionalArena ⟨conditionalFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiBKMPath
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms relativeEntropy_eq_integral_bkm
#print axioms conditional_relativeEntropy_eq_integral_bkm
#print axioms audit

namespace CommonFloor

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef),
    ∃ c : ℝ, R.readout () () 0 c ∧ c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ A ∧
      c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, bad, _, _⟩ := h (n := 0) 1 1 Matrix.PosDef.one Matrix.PosDef.one
  exact bad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 1
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% @common_floor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@common_floor, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_floor) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiBKMPath.common_floor.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiBKMPath.CommonFloor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiBKMPath
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CommonFloor

namespace FloorContinuity

abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature
  ℕ (fun n => ℝ → Matrix (Fin n) (Fin n) ℂ) (fun _ => Set ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f s => ContinuousOn f s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℂ) (s : Set ℝ) (c : ℝ)
    (hc : 0 < c)
    (hfloor : ∀ t ∈ s, c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B + t • H),
    R.readout () n (fun t : ℝ => logDeriv (B + t • H) H) s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := 0) 0 0 ∅ 1 zero_lt_one (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun t => t⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ)), ?_⟩
  intro he
  have hh := congrFun he Set.univ
  change ContinuousOn (fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) Set.univ =
    ContinuousOn (fun t : ℝ => t⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ)) Set.univ at hh
  have hc : Continuous (fun t : ℝ => t⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ)) :=
    continuousOn_univ.mp (hh ▸ continuous_const.continuousOn)
  have hi : Continuous (fun t : ℝ => t⁻¹) := by
    convert Complex.continuous_re.comp
      ((Matrix.traceLinearMap (Fin 1) ℝ ℂ).toContinuousLinearMap.continuous.comp hc) using 1
    funext t
    simp [Matrix.trace_smul, Matrix.trace_one]
  have hne : (0 : ℝ) ≠ 0 := NormedField.continuousAt_inv.mp hi.continuousAt
  exact hne rfl

def family : Registration arena (type_of% @continuousOn_logDeriv_of_floor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuousOn_logDeriv_of_floor, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuousOn_logDeriv_of_floor) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiBKMPath.continuousOn_logDeriv_of_floor.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiBKMPath.FloorContinuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f s => ContinuousOn f s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiBKMPath
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FloorContinuity

end Reg.D5.S3.Quantum.Divergence.UmegakiBKMPath
