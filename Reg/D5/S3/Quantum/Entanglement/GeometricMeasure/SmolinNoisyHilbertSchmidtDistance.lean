import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance
import Reg.Support.DependentFamily

/-! Source-bound audit of the noisy Smolin state's Hilbert–Schmidt distance. -/

namespace Reg.D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance

open _root_.D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance
open _root_.D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the distance value as the noise parameter varies. -/
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
  realize signature (fun _ _ p => f p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Vary the first distance coordinate while retaining all four partition clauses. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ p ∈ Set.Icc (0 : ℝ) 1,
    IsLeast {d | ∃ σ, IsSeparable σ ∧ d = hsDist (noisy p) σ} (r.readout () () p) ∧
    IsLeast {d | ∃ σ ∈ SepOneOneTwo, d = hsDist (noisy p) σ} (f p) ∧
    IsLeast {d | ∃ σ ∈ SepFull, d = hsDist (noisy p) σ} (f p) ∧
    IsLeast {d | ∃ σ ∈ SepTwoTwo, d = hsDist (noisy p) σ} 0

private theorem f_one_pos : 0 < f 1 := by
  norm_num [f]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := (h 1 (by norm_num)).1.unique (result 1 (by norm_num)).1
  change (0 : ℝ) = f 1 at hzero
  exact (ne_of_gt f_one_pos) hzero.symm

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change f 0 ≠ f 1
  have hzero : f 0 = 0 := by norm_num [f]
  rw [hzero]
  exact (ne_of_gt f_one_pos).symm

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ p => f p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance
      name := `D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance
