import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Density.RationalBracketCollisionDensity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Density.RationalBracketCollisionDensity

open _root_.D5.S3.Arith.Density.RationalBracketCollisionDensity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Classical
open scoped Topology

noncomputable section

/-- Observe the rational limiting value by its real embedding. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ a => (a : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- The full source telescope, varying only the embedding of the rational limit. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℕ) (c : Fin t → ℤ) (α : Fin t → ℚ), (∀ i, 0 < α i) →
    ∀ k : ℕ, 0 < k → ∃ a : ℚ, Tendsto
      (fun N : ℕ => (((Finset.range (N + 1)).filter (collision c α k)).card : ℝ) /
        (N : ℝ)) atTop (𝓝 (R.readout () () a))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, ha⟩ := h 0 (fun _ => 0) (fun _ => 1) (by simp) 1 (by norm_num)
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa [rejected, realize, collision, bracket] using ha
  have he : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds hz
  norm_num at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Density.RationalBracketCollisionDensity.result)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Density.RationalBracketCollisionDensity.unit
  realizationName := `Reg.D5.S3.Arith.Density.RationalBracketCollisionDensity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => (a : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Density.RationalBracketCollisionDensity
    definition := some {
      owner := `D5.S3.Arith.Density.RationalBracketCollisionDensity
      name := `D5.S3.Arith.Density.RationalBracketCollisionDensity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Density.RationalBracketCollisionDensity
