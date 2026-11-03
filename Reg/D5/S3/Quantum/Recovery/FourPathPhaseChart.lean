import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathPhaseChart
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Quantum.Recovery.FourPathPhaseChart
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Topology
open Real Set
open Complex (I)

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FourPathPhaseChart

abbrev signature : Signature where
  Params := Unit
  State _ := Coordinates
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Coordinates → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {δ τ : ℝ}, (0 < δ ∧ δ < 2) → (τ = 1 ∨ τ = -1) →
    ∃ S : Set Coordinates, ∃ V : Set PhaseVector,
      IsOpen S ∧ IsOpen V ∧ baseCoordinates δ ∈ S ∧
      phaseChart τ (baseCoordinates δ) ∈ V ∧
      (∀ p ∈ S, (∀ i, ‖phaseChart τ p i‖ = 1) ∧
        traceModulus (phaseChart τ p) = 4 - p 0 ∧
        R.readout () () (phaseCoordinates τ (phaseChart τ p)) p ∧
        AnalyticAt ℝ (phaseChart τ) p ∧ 0 < cos (p 2) ∧
        (∀ h c s : ℝ, p 3 = 0 →
          amplitudeP h c (phaseChart τ p) =
            2 * ((h : ℂ) * radialX (p 0) (p 1) (p 2) * Complex.exp ((p 1 : ℂ) * I) +
              (c : ℂ) * cos (p 2)) ∧
          amplitudeQ h s (phaseChart τ p) =
            2 * τ * (I * h * sqrt (1 - radialX (p 0) (p 1) (p 2) ^ 2) *
              Complex.exp ((p 1 : ℂ) * I) - s * sin (p 2)) ∧
          oppositeModulus (phaseChart τ p) =
            2 * ‖I * sqrt (1 - radialX (p 0) (p 1) (p 2) ^ 2) *
              Complex.exp ((p 1 : ℂ) * I) - sin (p 2)‖) ∧
        (0 < radialX (p 0) (p 1) (p 2) ∧ radialX (p 0) (p 1) (p 2) < 1) ∧
        0 < (2 - p 0 / 2) ^ 2 - cos (p 2) ^ 2 * sin (p 1) ^ 2 ∧ FeedbackLaws τ p) ∧
      (∀ w ∈ V, AnalyticAt ℝ (phaseCoordinates τ) w ∧
        ((∀ i, ‖w i‖ = 1) → phaseCoordinates τ w ∈ S ∧
          phaseChart τ (phaseCoordinates τ w) = w)) ∧
      (∀ p ∈ S, ∀ q ∈ S, p 3 = 0 → q 3 = 0 → ∀ scalar : ℂ,
        (∀ i, phaseChart τ p i = scalar * phaseChart τ q i) → p = q ∧ scalar = 1) ∧
      Set.BijOn (phaseChart τ) S (V ∩ {w | ∀ i, ‖w i‖ = 1})

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨S, V, hSo, hVo, hp, hw, hs, hrest⟩ :=
    h (δ := 1) (τ := 1) (by norm_num) (Or.inl rfl)
  exact (hs (baseCoordinates 1) hp).2.2.1

def registration : Registration arena (type_of% @local_phase_chart) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_phase_chart, rejected, rejected_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := by
    intro i
    refine ⟨(), (0 : Coordinates), (1 : Coordinates), ?_⟩
    intro h
    have hf : (1 : Coordinates) = 0 := Eq.mp (congrFun h 0) rfl
    have hi := congrFun hf 0
    norm_num at hi

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@local_phase_chart) (Realization signature) Type Unit where
  unitName := `D5.S3.Quantum.Recovery.FourPathPhaseChart.local_phase_chart.audit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathPhaseChart.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathPhaseChart
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "arg", "arg",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.FourPathPhaseChart
