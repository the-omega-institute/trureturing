import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 * (k - 1)) (fun e => nomatch e)

def zeroAllowance : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (z : Fin 3 → ℕ),
    RealizableSeedCounts 1 k z ↔
      ∃ u : Fin 3 → ℕ, (∀ i, z i = 4 * u i) ∧ (∀ i, u i ≤ 2 * k) ∧
        (∑ i, u i) ≤ 4 * k ∧
          (k % 2 = 1 → ∀ i, 2 * u i ≤ (∑ j, u j) + R.readout () () k)

private theorem zero_allowance_fails : ¬ arena.Law zeroAllowance := by
  intro law
  let u : Fin 3 → ℕ := ![6, 1, 1]
  let z i := 4 * u i
  have realized : RealizableSeedCounts 1 3 z := (exact_three_coordinate_counts 3 z).mpr
    ⟨u, fun _ => rfl, (by decide : ∀ i, u i ≤ 6),
      (by decide : (∑ i, u i) ≤ 12),
      fun _ => (by decide : ∀ i, 2 * u i ≤ (∑ j, u j) + 4)⟩
  obtain ⟨v, scale, _, _, cuts⟩ := (law 3 z).mp realized
  have same : v = u := by
    funext i
    have eq := scale i
    change 4 * u i = 4 * v i at eq
    omega
  subst v
  exact (by decide : ¬ (12 ≤ 8)) (cuts (by decide) 0)

def family : Registration arena (type_of% exact_three_coordinate_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_three_coordinate_counts, zeroAllowance, zero_allowance_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroAllowance, ?_, rfl, zero_allowance_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨(), 1, 3, by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_three_coordinate_counts (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts.oddAllowance
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => 2 * (k - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "arg", "arg", "arg",
        "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts
