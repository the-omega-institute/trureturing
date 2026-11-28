import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Weil.ZetaExplicit.SixthPowerSampling

/-! The sample logarithm is essential to the common convex interpolation law. -/

namespace Reg.D5.S3.Weil.ZetaExplicit.SixthPowerSampling

open _root_.D5.S3.Weil.ZetaExplicit.SixthPowerSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit Set

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => Real.log) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law observation :=
    ∃ H : ℝ → ℝ, ConvexOn ℝ univ H ∧
      (∀ n : ℕ, 1 ≤ n → H ((n : ℝ)^6) =
        (n : ℝ)^6 * observation.readout () () ((n : ℝ)^6)) ∧
      (∀ n : ℕ, 1 ≤ n →
        (9/1024 : ℝ) * (n : ℝ) * Real.sqrt (((n : ℝ)^6+((n : ℝ)+1)^6)/2) ≤
        H (((n : ℝ)^6+((n : ℝ)+1)^6)/2) -
          (((n : ℝ)^6+((n : ℝ)+1)^6)/2) * Real.log (((n : ℝ)^6+((n : ℝ)+1)^6)/2))

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨H, hH, hs, hm⟩
  have h1 := hs 1 (by decide)
  have h2 := hs 2 (by decide)
  norm_num [rejected, realize] at h1 h2
  have hc := hH.2 (x := (1 : ℝ)) (y := (64 : ℝ))
    (mem_univ _) (mem_univ _)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  norm_num [smul_eq_mul, h1, h2] at hc
  have hmid := hm 1 (by decide)
  norm_num at hmid
  have hsqrt : 0 < Real.sqrt (65/2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hlog : 0 ≤ Real.log (65/2 : ℝ) := Real.log_nonneg (by norm_num)
  have hpositive : 0 < (9/1024 : ℝ) * Real.sqrt (65/2 : ℝ) :=
    mul_pos (by norm_num) hsqrt
  have hnonnegative : 0 ≤ (65/2 : ℝ) * Real.log (65/2 : ℝ) :=
    mul_nonneg (by norm_num) hlog
  linarith only [hc, hmid, hpositive, hnonnegative]

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (x := 2) (by norm_num)).ne'

def evidence : Registration arena (type_of% @sixth_power_convex_sampling_countermodel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sixth_power_convex_sampling_countermodel, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@sixth_power_convex_sampling_countermodel) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZetaExplicit.SixthPowerSampling.sixth_power_convex_sampling_countermodel.audit
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.SixthPowerSampling.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.SixthPowerSampling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "fn", "arg", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Weil.ZetaExplicit.SixthPowerSampling
