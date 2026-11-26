import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.HingeMoments
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMV.Tracial.HingeMoments

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.RefinedBMV.Tracial (fourMarkPeriodicMean integral_fourMarkSignedDefect_lower)
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun anchor => nomatch anchor)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have h := congrFun heq (1 / 2 : ℝ)
  norm_num [actual, realize] at h

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ} (_hr : 0 ≤ r) (x y : ℝ), R.readout () ()
    ((x - y) ^ 2 * ((x ^ 2 + y ^ 2) / 40))
    (∫ s in (0 : ℝ)..1, Real.exp (r * s) *
      (((1 - s) * x + s * y) ^ 4 - fourMarkPeriodicMean s x y))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (r := 0) le_rfl 1 (-1)

def signedFamily : Registration arena (type_of% @integral_fourMarkSignedDefect_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_fourMarkSignedDefect_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual
    rejected rejected_law
  dependence := dependence

def signedRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_fourMarkSignedDefect_lower) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.Tracial.integral_fourMarkSignedDefect_lower.__information_unit
  realizationName := ``signedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨signedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Analysis.RefinedBMV.Tracial.HingeMoments
