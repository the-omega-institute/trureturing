import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

-- Transient faithful audit attempt for the newly public ORIGINAL supplier only.
-- No C08 receiver registration, new mathematical credit, or validated claim.
namespace Reg.D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry
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
  realize signature (fun _ _ ε => lowerGain ε) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
    R.readout () () ε = Real.sqrt (2 * ε / normalization ε)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (1 / 2) (by norm_num) (by norm_num)
  change (0 : ℝ) = Real.sqrt (2 * (1 / 2) / normalization (1 / 2)) at he
  have hp : 0 < Real.sqrt (2 * (1 / 2 : ℝ) / normalization (1 / 2)) :=
    Real.sqrt_pos.2 (by norm_num [normalization])
  exact (ne_of_gt hp) he.symm

def registration : Registration arena
    (∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      lowerGain ε = Real.sqrt (2 * ε / normalization ε)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lower_gain_eq_sqrt, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact False.elim (hj (@Subsingleton.elim Unit _ j i))
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (1 / 4 : ℝ), (1 / 2 : ℝ), ?_⟩
    change lowerGain (1 / 4) ≠ lowerGain (1 / 2)
    intro he
    have h1 := lower_gain_sq (1 / 4) (by norm_num) (by norm_num)
    have h2 := lower_gain_sq (1 / 2) (by norm_num) (by norm_num)
    norm_num at h1 h2
    rw [he] at h1
    linarith

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@lower_gain_eq_sqrt)
      (type_of% (realize signature (fun _ _ ε => lowerGain ε) (fun e => nomatch e)))
      (Type) (Unit) := {
  unitName := `C08OriginalSupplierVisibilityAudit,
  realizationName := `Reg.D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ ε => lowerGain ε) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry,
    definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
end
end Reg.D5.S3.ConceptDynamics.ObservationTopology.HarmonicSensors.SixDimensionalSharpGeometry
