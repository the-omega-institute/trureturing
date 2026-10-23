import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the generation bound in the simplicial degree shift. -/

namespace Reg.D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift

open _root_.D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe whether the generation reaches the dimension's admissible range. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ d n => @decide (d + 1 ≤ n) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

/-- Keep the full labeling, freshness, dimension, and degree-set conclusion. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (V : Type) [DecidableEq V] (v₀ : V) (v : ℕ → Finset V → V),
    Function.Injective (Function.uncurry v) → (∀ s σ, v s σ ≠ v₀) →
    ∀ d n : ℕ, 1 ≤ d → R.readout () d n = true →
      degreeSet (dsc v₀ v n) d = insert 0 (degreeSet (dsc v₀ v (n - d)) 0)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨f, hf⟩ := exists_injective_nat (ℕ × Finset ℕ)
  let v (s : ℕ) (σ : Finset ℕ) := f (s, σ) + 1
  have hi : Function.Injective (Function.uncurry v) := by
    intro a b he
    exact hf (Nat.add_right_cancel he)
  have h₀ (s : ℕ) (σ : Finset ℕ) : v s σ ≠ 0 := by simp [v]
  have hbad := h ℕ 0 v hi h₀ 1 0 (by decide) rfl
  have hz := Set.ext_iff.mp hbad 0
  simp [degreeSet, dsc, upperDegree] at hz

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 2, ?_⟩
  simp [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp [claim, actual, realize]
  variation := ⟨by simpa [claim, arena, actual, realize] using result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ d n => @decide (d + 1 ≤ n) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift
    definition := some {
      owner := `D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift
      name := `D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift.claim
      path := #[] }
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift
