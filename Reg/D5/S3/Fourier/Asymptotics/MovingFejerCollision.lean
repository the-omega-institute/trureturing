import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.MovingFejerCollision

/-! Scale dependence of the compatible window and uniform collision lower bound. -/

namespace Reg.D5.S3.Fourier.Asymptotics.MovingFejerCollision

open Filter Finset
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.MovingFejerCollision
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.Reg.Support

noncomputable section
universe u

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℕ × ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => Real.sqrt ((z.1:ℝ)*z.2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0,1), (1,1), ?_⟩
  norm_num [actual,realize]

namespace Window

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (V η : ℕ → ℝ), (∀ᶠ n in atTop, 0 < V n) →
    (∀ᶠ n in atTop, 0 < η n) →
    let scaleReadout := R.readout () ()
    let scale := fun n => scaleReadout (n,V n)
    Tendsto (fun n => η n/scale n) atTop (𝓝 0) ↔
      ∃ A : ℕ → ℝ, (∀ᶠ n in atTop, 0 < A n) ∧
        Tendsto (fun n => A n*scale n) atTop atTop ∧
        Tendsto (fun n => η n*A n) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (1:ℝ) := Eventually.of_forall fun _ => zero_lt_one
  have h := law (fun _ => 1) (fun _ => 1) hpos hpos
  obtain ⟨A,hA,hR,hsmall⟩ := h.mp (by simp [rejected,realize])
  have hz : Tendsto (fun _ : ℕ => (0:ℝ)) atTop atTop := by
    simpa [rejected,realize] using hR
  obtain ⟨n,hn⟩ := (hz.eventually_ge_atTop (1:ℝ)).exists
  norm_num at hn

def evidence : Registration arena (type_of% @exists_fejer_window_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_fejer_window_iff, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@exists_fejer_window_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.MovingFejerCollision.Window.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.MovingFejerCollision.Window.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.MovingFejerCollision
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Window

namespace Uniform

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (V η : ℕ → ℝ), (∀ᶠ n in atTop, 0 < V n) →
    (∀ᶠ n in atTop, 0 < η n) →
    let scaleReadout := R.readout () ()
    let scale := fun n => scaleReadout (n,V n)
    Tendsto (fun n => η n/scale n) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ {J : Type u} [Fintype J] [DecidableEq J] (g w : J → ℝ),
        (∀ j, 0 ≤ w j) → ∀ a : ℝ,
        (∑ j,w j*(g j-a)^2 ≤ V n*∑ j,w j) →
        (1/(2*Real.sqrt Real.pi)-ε)*η n*(∑ j,w j)^(2*n) ≤
          scale n*tailCollisionMass g w n (η n)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (1:ℝ) := Eventually.of_forall fun _ => zero_lt_one
  have h := law (fun _ => 1) (fun _ => 1) hpos hpos
    (by simp [rejected,realize]) (1/(4*Real.sqrt Real.pi)) (by positivity)
  obtain ⟨n,hn⟩ := h.exists
  have hb := hn (J := ULift.{u} Unit) (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) 0 (by simp)
  have hbad : (1:ℝ)/(2*Real.sqrt Real.pi)-1/(4*Real.sqrt Real.pi) ≤ 0 := by
    simpa [rejected,realize] using hb
  have he : (1:ℝ)/(2*Real.sqrt Real.pi)-1/(4*Real.sqrt Real.pi) =
      1/(4*Real.sqrt Real.pi) := by ring
  rw [he] at hbad
  exact (not_le_of_gt (by positivity : 0 < (1:ℝ)/(4*Real.sqrt Real.pi))) hbad

def evidence : Registration arena.{u} (type_of% @moving_fejer_uniform_lower.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moving_fejer_uniform_lower.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@moving_fejer_uniform_lower.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.MovingFejerCollision.Uniform.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.MovingFejerCollision.Uniform.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.MovingFejerCollision
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Uniform

end

end Reg.D5.S3.Fourier.Asymptotics.MovingFejerCollision
