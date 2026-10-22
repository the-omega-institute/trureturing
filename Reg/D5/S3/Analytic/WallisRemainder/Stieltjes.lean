import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.WallisRemainder.Stieltjes
import Reg.Support.SingleDependentReadout

/-! Typed observations for positive resolvent transforms and their strict comparisons. -/

open _root_.D5.S3.Analytic.WallisRemainder.Stieltjes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Filter Set
open scoped ENNReal NNReal

noncomputable section
namespace Reg.D5.S3.Analytic.WallisRemainder.Stieltjes

private def twoPoint : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac 1 + (1/2 : ℝ≥0∞) • Measure.dirac 2

private instance : IsProbabilityMeasure twoPoint := ⟨by
  simp only [twoPoint, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one, one_div]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num⟩

private lemma twoPoint_integrable (f : ℝ → ℝ) : Integrable f twoPoint := by
  rw [twoPoint, integrable_add_measure]
  constructor <;> exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

private lemma twoPoint_integral (f : ℝ → ℝ) :
    (∫ v, f v ∂twoPoint) = (f 1+f 2)/2 := by
  rw [twoPoint, integral_add_measure ((integrable_dirac (by finiteness)).smul_measure (by finiteness))
    ((integrable_dirac (by finiteness)).smul_measure (by finiteness))]
  simp
  ring

private lemma twoPoint_pos : ∀ᵐ v ∂twoPoint, 0 < v := by
  simp [twoPoint, ae_add_measure_iff]

private lemma twoPoint_not_const (a : ℝ) : ¬ ∀ᵐ v ∂twoPoint, v=a := by
  simp only [twoPoint, ae_add_measure_iff]
  norm_num
  intro h1 h2
  linarith

abbrev jensenSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : Measure ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def jensenActual : Realization jensenSignature :=
  realize jensenSignature
    (fun _ p z => jensenRemainder p.1 p.2 (∫ v, (v-p.2)^2 ∂p.1) z)
    (fun e => nomatch e)

def jensenRejected : Realization jensenSignature :=
  realize jensenSignature (fun _ _ _ => 0) (fun e => nomatch e)

def jensenArena : Arena where
  signature := jensenSignature
  Law R := ∀ {M : Measure ℝ} [IsProbabilityMeasure M],
    (∀ᵐ v ∂M, 0 < v) → ∀ {a : ℝ},
    Integrable (fun v : ℝ => v) M →
    Integrable (fun v => (v-a)^2) M →
    (∫ v, v ∂M) = a → (0 < ∫ v, (v-a)^2 ∂M) →
    StrictMonoOn (R.readout () ⟨M,a⟩) (Ioi 0)

private lemma jensen_rejected : ¬ jensenArena.Law jensenRejected := by
  intro h
  have hm : (∫ v, v ∂twoPoint) = (3/2 : ℝ) := by rw [twoPoint_integral]; norm_num
  have hv : 0 < ∫ v, (v-(3/2 : ℝ))^2 ∂twoPoint := by rw [twoPoint_integral]; norm_num
  have hh := h twoPoint_pos (twoPoint_integrable _) (twoPoint_integrable _) hm hv
  have := hh (show (1:ℝ) ∈ Ioi 0 by norm_num)
    (show (2:ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1:ℝ)<2)
  norm_num [jensenRejected, realize] at this

private lemma jensen_dependence : ObservationalDependence jensenSignature jensenActual := by
  intro i
  refine ⟨⟨Measure.dirac 1,0⟩, 1,2, ?_⟩
  norm_num [jensenActual, realize, jensenRemainder, stieltjes]

def jensenFamily : Registration jensenArena (type_of% @strictMonoOn_jensenRemainder) where
  actual := jensenActual
  bridge := Iff.rfl
  variation := ⟨@strictMonoOn_jensenRemainder, jensenRejected, jensen_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    jensenArena.Law jensenActual jensenRejected jensen_rejected
  dependence := jensen_dependence

abbrev inverseSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Measure ℝ) (fun _ => ℝ) (fun _ => ℝ)

def inverseActual : Realization inverseSignature :=
  realize inverseSignature (fun _ M z => 1/stieltjes M z-z) (fun e => nomatch e)

def inverseRejected : Realization inverseSignature :=
  realize inverseSignature (fun _ _ _ => 0) (fun e => nomatch e)

def inverseArena : Arena where
  signature := inverseSignature
  Law R := ∀ {M : Measure ℝ} [IsProbabilityMeasure M],
    (∀ᵐ v ∂M, 0 < v) → (∀ a : ℝ, ¬ ∀ᵐ v ∂M, v=a) →
    StrictMonoOn (R.readout () M) (Ioi 0)

private lemma inverse_rejected : ¬ inverseArena.Law inverseRejected := by
  intro h
  have hh := h twoPoint_pos twoPoint_not_const
  have := hh (show (1:ℝ) ∈ Ioi 0 by norm_num)
    (show (2:ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1:ℝ)<2)
  norm_num [inverseRejected, realize] at this

private lemma inverse_dependence : ObservationalDependence inverseSignature inverseActual := by
  intro i
  refine ⟨0,0,1, ?_⟩
  norm_num [inverseActual, realize, stieltjes]

def inverseFamily : Registration inverseArena (type_of% @strictMonoOn_inv_stieltjes_sub) where
  actual := inverseActual
  bridge := Iff.rfl
  variation := ⟨@strictMonoOn_inv_stieltjes_sub, inverseRejected, inverse_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    inverseArena.Law inverseActual inverseRejected inverse_rejected
  dependence := inverse_dependence

abbrev boundsSignature : Signature := inverseSignature

def boundsActual : Realization boundsSignature :=
  realize boundsSignature (fun _ M z => stieltjes M z) (fun e => nomatch e)

def boundsRejected : Realization boundsSignature :=
  realize boundsSignature (fun _ _ _ => 0) (fun e => nomatch e)

def boundsArena : Arena where
  signature := boundsSignature
  Law R := ∀ {M : Measure ℝ} [IsProbabilityMeasure M],
    (∀ᵐ v ∂M, 0 < v) → ∀ {z : ℝ}, 0 < z →
    0 < R.readout () M z ∧ z * R.readout () M z < 1

private lemma bounds_rejected : ¬ boundsArena.Law boundsRejected := by
  intro h
  have hh := h (M := Measure.dirac 1) (by simp) (z := 1) (by norm_num)
  norm_num [boundsRejected, realize] at hh

private lemma bounds_dependence : ObservationalDependence boundsSignature boundsActual := by
  intro i
  refine ⟨Measure.dirac 1,1,2, ?_⟩
  norm_num [boundsActual, realize, stieltjes]

def boundsFamily : Registration boundsArena (type_of% @stieltjes_bounds) where
  actual := boundsActual
  bridge := Iff.rfl
  variation := ⟨@stieltjes_bounds, boundsRejected, bounds_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    boundsArena.Law boundsActual boundsRejected bounds_rejected
  dependence := bounds_dependence

def jensenAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strictMonoOn_jensenRemainder) (Realization jensenSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Stieltjes.jensen_unit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Stieltjes.jensenFamily
  realizationSource := none
  generated := false
  arena := .source ⟨jensenArena⟩
  objectArena := .source ⟨jensenArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source jensenArena ⟨jensenFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize jensenSignature (fun _ p z => jensenRemainder p.1 p.2 (∫ v, (v-p.2)^2 ∂p.1) z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Stieltjes
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def inverseAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strictMonoOn_inv_stieltjes_sub) (Realization inverseSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Stieltjes.inverse_unit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Stieltjes.inverseFamily
  realizationSource := none
  generated := false
  arena := .source ⟨inverseArena⟩
  objectArena := .source ⟨inverseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inverseArena ⟨inverseFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize inverseSignature (fun _ M z => 1/stieltjes M z-z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Stieltjes
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def boundsAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stieltjes_bounds) (Realization boundsSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Stieltjes.bounds_unit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Stieltjes.boundsFamily
  realizationSource := none
  generated := false
  arena := .source ⟨boundsArena⟩
  objectArena := .source ⟨boundsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundsArena ⟨boundsFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundsSignature (fun _ M z => stieltjes M z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Stieltjes
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Reg.D5.S3.Analytic.WallisRemainder.Stieltjes
