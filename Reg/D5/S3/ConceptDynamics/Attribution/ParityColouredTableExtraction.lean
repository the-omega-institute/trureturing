import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction
import Reg.Support.DependentFamily

/-! The coordinatewise table bound depends on the seed-count vector. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
open _root_.D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open _root_.D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Fin (n + 2) → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin (n + 2) → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def zeroBound : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), (n + 2) % 2 = 0 → ∀ z : Fin (n + 2) → ℕ,
    RealizableSeedCounts n k z →
    ∃ b : EvenSubset (n + 2) → OddSubset (n + 2) → Fin 2 → ℕ,
      (∀ p c, ∑ q, b p q c = k) ∧
      (∀ q, ∑ p, (b p q 0 + b p q 1) = 2 * k) ∧
      (∀ p q, p.val ≠ univ → b p q 0 = b p q 1) ∧
      (∀ i, 2 * (∑ p, ∑ q, ∑ c : Fin 2,
        if i ∈ p.val ∩ q.val then b p q c % 2 else 0) ≤ R.readout () n z i)

private theorem zero_bound_fails : ¬ arena.Law zeroBound := by
  classical
  intro law
  have first : RealizableSeedCounts 0 1 ![4,0] :=
    (exact_two_coordinate_counts 1 _).mpr ⟨1, 0, rfl, by decide, Or.inr (by decide)⟩
  obtain ⟨b, rows, _, _, counts⟩ := law 0 1 (by decide) _ first
  let full : EvenSubset 2 := ⟨univ, by decide⟩
  obtain ⟨q, weight⟩ : ∃ q, b full q 0 = 1 := by
    by_contra! h
    have zero (q : OddSubset 2) : b full q 0 = 0 := by
      have le := single_le_sum (f := fun q => b full q 0) (fun _ _ => Nat.zero_le _) (mem_univ q)
      rw [rows] at le
      have ne := h q
      omega
    simpa [zero] using rows full 0
  have someBit : q.val.Nonempty := by
    by_contra! empty
    have h := q.property
    rw [empty] at h
    simp at h
  obtain ⟨i, hi⟩ := someBit
  let score (p : EvenSubset 2) (q : OddSubset 2) (c : Fin 2) :=
    if i ∈ p.val ∩ q.val then b p q c % 2 else 0
  have one : score full q 0 = 1 := by simp [score, full, hi, weight]
  have a : score full q 0 ≤ ∑ c, score full q c :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ 0)
  have bnd : (∑ c, score full q c) ≤ ∑ q, ∑ c, score full q c :=
    single_le_sum (f := fun q => ∑ c, score full q c) (fun _ _ => Nat.zero_le _) (mem_univ q)
  have upper : (∑ q, ∑ c, score full q c) ≤ ∑ p, ∑ q, ∑ c, score p q c :=
    single_le_sum (f := fun p => ∑ q, ∑ c, score p q c) (fun _ _ => Nat.zero_le _) (mem_univ full)
  have impossible := counts i
  change 2 * (∑ p, ∑ q, ∑ c, score p q c) ≤ 0 at impossible
  omega

def family : Registration arena (type_of% (@extract_coloured_subsets)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@extract_coloured_subsets, zeroBound, zero_bound_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroBound, ?_, rfl, zero_bound_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨0, fun _ => 1, fun _ => 0, by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@extract_coloured_subsets) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction.coordinateBound
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParityColouredTableExtraction
