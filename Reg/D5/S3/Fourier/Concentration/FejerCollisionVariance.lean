import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.FejerCollisionVariance

/-! Source dependence of the positive-kernel collision comparison and its variance limits. -/

namespace Reg.D5.S3.Fourier.Concentration.FejerCollisionVariance

open Finset Filter MeasureTheory
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Fourier.AngularFejerKernel
open _root_.D5.S3.Fourier.Concentration.FejerCollisionVariance
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.Reg.Support

noncomputable section
universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => K z.1 z.2) (fun e => nomatch e)

def zeroKernel : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def largeKernel : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem kernel_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1,0), (2,0), ?_⟩
  change K 1 0 ≠ K 2 0
  simp only [K,mul_zero,zero_div,Real.sinc_zero,one_pow,mul_one]
  intro h
  have hp := Real.pi_pos
  field_simp at h
  linarith

namespace Comparison

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (p : ℕ) {η : ℝ}, 0 < η →
    let kernel := R.readout () ()
    let s := piAntidiag univ p
    let x := monomialFrequency g
    let c := monomialWeight w
    let M := ∫ t : ℝ, kernel (η,t)*‖complexScore g w t‖^(2*p)
    M = (∑ m ∈ s, ∑ n ∈ s, c m*c n*phi η (x m-x n)) ∧
      ((∀ j, 0 ≤ w j) → M ≤ tailCollisionMass g w p η)

private theorem rejected_law : ¬ arena.{u}.Law zeroKernel := by
  intro h
  have hz := (h (J := ULift.{u} Unit) (fun _ => 0) (fun _ => 1) 0
    (η := 1) zero_lt_one).1
  norm_num [zeroKernel,realize,monomialWeight,monomialFrequency,phi] at hz

def evidence : Registration arena.{u} (type_of% @fejer_collision_comparison.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fejer_collision_comparison.{u}, zeroKernel, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual zeroKernel rejected_law
  dependence := kernel_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@fejer_collision_comparison.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionVariance.Comparison.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionVariance.Comparison.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FejerCollisionVariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Comparison

namespace Window

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (g w : J → ℝ), (∀ j, 0 ≤ w j) → ∀ (a V : ℝ) (p : ℕ)
    {η : ℝ}, 0 < η → ∀ {A : ℝ}, 0 ≤ A →
    (∑ j,w j*(g j-a)^2 ≤ V*∑ j,w j) →
    let kernel := R.readout () ()
    let W := ∑ j,w j
    W^(2*p)*(∫ t in -A..A, kernel (η,t)*(max 0 (1-V*t^2/2))^(2*p)) ≤
      tailCollisionMass g w p η

private theorem rejected_law : ¬ arena.{u}.Law largeKernel := by
  intro h
  have hz := h (J := ULift.{u} Unit) (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) 0 0 0 (η := 1) zero_lt_one (A := 1) zero_le_one (by simp)
  norm_num [largeKernel,realize,tailCollisionMass,nearCollisionMass,monomialFrequency,
    monomialWeight,intervalIntegral.integral_const,smul_eq_mul] at hz

def evidence : Registration arena.{u} (type_of% @fejer_collision_variance_lower.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fejer_collision_variance_lower.{u}, largeKernel, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual largeKernel rejected_law
  dependence := kernel_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@fejer_collision_variance_lower.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionVariance.Window.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionVariance.Window.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FejerCollisionVariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Window

namespace Asymptotic

abbrev scaleSignature := UniverseSingleReadout.signature Unit (fun _ => ℕ × ℝ) (fun _ => ℝ)

def scale : Realization scaleSignature :=
  realize scaleSignature (fun _ _ z => Real.sqrt ((z.1:ℝ)*z.2)) (fun e => nomatch e)

def rejected : Realization scaleSignature :=
  realize scaleSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem scale_dependence : ObservationalDependence scaleSignature scale := by
  intro i
  refine ⟨(), (0,1), (1,1), ?_⟩
  norm_num [scale,realize]

abbrev arena : Arena where
  signature := scaleSignature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (g w : J → ℝ), (∀ j, 0 ≤ w j) → ∀ (a V : ℝ), 0 < V →
    ∀ {η : ℝ}, 0 < η → (∑ j,w j*(g j-a)^2 ≤ V*∑ j,w j) →
    ∀ ε : ℝ, 0 < ε →
    let scaleReadout := R.readout () ()
    ∀ᶠ p : ℕ in atTop,
      (η/(2*Real.sqrt Real.pi)-ε)*(∑ j,w j)^(2*p) ≤
        scaleReadout (p,V)*tailCollisionMass g w p η

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hp := Real.sqrt_pos.mpr Real.pi_pos
  have hz := h (J := ULift.{u} Unit) (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) 0 1 zero_lt_one (η := 1) zero_lt_one (by simp)
    (1/(4*Real.sqrt Real.pi)) (by positivity)
  obtain ⟨p,hp'⟩ := hz.exists
  have he : (1:ℝ)/(2*Real.sqrt Real.pi)-1/(4*Real.sqrt Real.pi) ≤ 0 := by
    simpa [rejected,realize] using hp'
  have hpos : 0 < (1:ℝ)/(4*Real.sqrt Real.pi) := by positivity
  have heq : (1:ℝ)/(2*Real.sqrt Real.pi)-1/(4*Real.sqrt Real.pi) =
      1/(4*Real.sqrt Real.pi) := by ring
  rw [heq] at he
  linarith

def evidence : Registration arena.{u} (type_of% @fejer_collision_asymptotic_lower.{u}) where
  actual := scale
  bridge := Iff.rfl
  variation := ⟨@fejer_collision_asymptotic_lower.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law scale rejected rejected_law
  dependence := scale_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@fejer_collision_asymptotic_lower.{u}) (Realization scaleSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionVariance.Asymptotic.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FejerCollisionVariance.Asymptotic.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scaleSignature scale.readout scale.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FejerCollisionVariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Asymptotic

end

end Reg.D5.S3.Fourier.Concentration.FejerCollisionVariance
