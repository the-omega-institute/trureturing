import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.KummerRatio.BetaAsymptotics
import Reg.Support.DependentFamily

/-! Observation of the Gamma coefficient in the beta endpoint limit. -/

namespace Reg.D5.S3.Analytic.KummerRatio.BetaAsymptotics

open _root_.D5.S3.Analytic.KummerRatio.BetaAsymptotics
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter MeasureTheory Set
open scoped Topology
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => Real.Gamma d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ d => Real.Gamma d + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s d : ℝ}, 0 < s → 0 < d →
    Tendsto (fun x : ℝ => Real.exp (-x) * x ^ d *
      (∫ t in (0 : ℝ)..1, Real.exp (x * t) * t ^ (s - 1) * (1 - t) ^ (d - 1)))
      atTop (𝓝 (R.readout () () d))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₁ := tendsto_beta_laplace (s := 1) (d := 1) zero_lt_one zero_lt_one
  have h₂ := h (s := 1) (d := 1) zero_lt_one zero_lt_one
  have he := tendsto_nhds_unique h₁ h₂
  simp [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 3, ?_⟩
  norm_num [actual, realize, Real.Gamma_add_one, Real.Gamma_one]

def betaRegistration : Registration arena (type_of% @tendsto_beta_laplace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tendsto_beta_laplace, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def betaAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tendsto_beta_laplace) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.BetaAsymptotics.betaAuditUnit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.BetaAsymptotics.betaRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨betaRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => Real.Gamma d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.BetaAsymptotics
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms betaAudit
end
end Reg.D5.S3.Analytic.KummerRatio.BetaAsymptotics
