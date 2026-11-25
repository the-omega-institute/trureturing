import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.SeparatedParabolicCollision

/-! Dependence of the exact separated collision construction on mass and resolution. -/

namespace Reg.D5.S3.Fourier.Concentration.SeparatedParabolicCollision

open Finset Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.D5.S3.Fourier.Concentration.SeparatedParabolicCollision
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

namespace Finite

def actual : Realization signature :=
  realize signature (fun _ _ m => (m : ℝ) * (4 * (m : ℝ)^2 - 1) / 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → ∀ η : ℝ, 0 ≤ η → η < 1 →
    let mass := R.readout () ()
    let c := fun k : ℤ => (n : ℝ)^2 - (k : ℝ)^2
    let W := mass n
    (∀ k ∈ latticeInterval n, 0 ≤ c k) ∧
    0 < W ∧
    (∑ k ∈ latticeInterval n, c k) = W ∧
    (∑ k ∈ latticeInterval n, c k * (k : ℝ)^2) = W * ((n : ℝ)^2 - 1)/5 ∧
    nearCollisionMass (latticeInterval n) (fun k : ℤ => (k : ℝ)) c η =
      W * (4 * (n : ℝ)^2 + 1)/5

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h 1 (by decide) 0 (by norm_num) (by norm_num)).2.1
  change (0 : ℝ) < 0 at hz
  exact (lt_irrefl _ hz)

def evidence : Registration arena (type_of% @separated_parabolic_collision) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@separated_parabolic_collision, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@separated_parabolic_collision) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.SeparatedParabolicCollision.Finite.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.SeparatedParabolicCollision.Finite.evidence
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
    owner := `D5.S3.Fourier.Concentration.SeparatedParabolicCollision
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Finite

namespace Limit

def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)/((n : ℝ)+1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    let V := fun n : ℕ => ((n : ℝ)^2 - 1)/5
    let η := R.readout () ()
    let W := fun n : ℕ => (n : ℝ) * (4 * (n : ℝ)^2 - 1)/3
    let E := fun n : ℕ => nearCollisionMass (latticeInterval n)
      (fun k : ℤ => (k : ℝ)) (fun k => (n : ℝ)^2 - (k : ℝ)^2) (η n)
    Tendsto (fun n => η n / Real.sqrt (V n)) atTop (𝓝 0) ∧
    Tendsto (fun n => E n * Real.sqrt (V n) / (W n ^ 2 * η n)) atTop
      (𝓝 (3 / (5 * Real.sqrt 5)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (3 / (5 * Real.sqrt 5))) := by
    simpa [arena, rejected, realize] using h.2
  have he := tendsto_nhds_unique tendsto_const_nhds hz
  have hp : 0 < (3 : ℝ) / (5 * Real.sqrt 5) := by positivity
  linarith

def evidence : Registration arena (type_of% @parabolic_collision_ratio_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parabolic_collision_ratio_limit, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@parabolic_collision_ratio_limit) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.SeparatedParabolicCollision.Limit.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.SeparatedParabolicCollision.Limit.evidence
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
    owner := `D5.S3.Fourier.Concentration.SeparatedParabolicCollision
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit

end

end Reg.D5.S3.Fourier.Concentration.SeparatedParabolicCollision
