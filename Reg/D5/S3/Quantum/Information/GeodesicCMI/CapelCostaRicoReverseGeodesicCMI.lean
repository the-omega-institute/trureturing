import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceDistance traceNorm traceNorm_of_posSemidef)
open _root_.D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => DensityState Triple) (fun _ => DensityState Triple → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ρ => traceDistance ρ) (fun e => nomatch e)

/-- Replace the first state by the second, giving the same-state distance. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ σ => traceDistance σ σ) (fun e => nomatch e)

private theorem valid_square {x : ℝ} (hx : Valid x) : Valid (x ^ 2) := by
  refine ⟨pow_pos hx.1 _, ?_⟩
  have h := mul_pos hx.1 (show 0 < 1 - x by linarith [hx.2])
  nlinarith [hx.2]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ} (hx : Valid x),
    R.readout () () (family (x ^ 2) (valid_square hx)) (family x hx) = 4 * (x - x ^ 2)

private theorem same_state_distance (ρ : DensityState Triple) : traceDistance ρ ρ = 0 := by
  have hzero : traceNorm (0 : Matrix Triple Triple ℂ) = 0 := by
    have h := congrArg Complex.re
      (traceNorm_of_posSemidef (Matrix.PosSemidef.zero :
        (0 : Matrix Triple Triple ℂ).PosSemidef))
    simpa using h
  simp only [traceDistance, sub_self, hzero, zero_div]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx : Valid (1 / 32 : ℝ) := by norm_num [Valid]
  have he : traceDistance (family (1 / 32) hx) (family (1 / 32) hx) =
      4 * ((1 / 32 : ℝ) - (1 / 32 : ℝ) ^ 2) := h hx
  rw [same_state_distance] at he
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hx : Valid (1 / 32 : ℝ) := by norm_num [Valid]
  let ρ := family ((1 / 32 : ℝ) ^ 2) (valid_square hx)
  let σ := family (1 / 32) hx
  refine ⟨(), ρ, σ, ?_⟩
  change traceDistance ρ ≠ traceDistance σ
  intro he
  have hd : traceDistance ρ σ = 4 * ((1 / 32 : ℝ) - (1 / 32 : ℝ) ^ 2) :=
    family_traceDistance hx
  rw [congrFun he σ, same_state_distance] at hd
  norm_num at hd

def source_registration : Registration arena (type_of% @family_traceDistance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@family_traceDistance, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@family_traceDistance) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI.family_traceDistance.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => traceDistance ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
