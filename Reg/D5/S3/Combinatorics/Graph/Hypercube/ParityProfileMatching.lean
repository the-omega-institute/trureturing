import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
import Reg.Support.DependentFamily

/-! The optimal common-one count responds to the marginal multiplicity. -/

namespace Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching

open Finset LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
open _root_.D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def best (n k : ℕ) : ℕ :=
  let M := k * 2 ^ n
  M - (M + (n + 2 - 1)) / (n + 2)

def actual : Realization signature :=
  realize signature (fun _ => best) (fun e => nomatch e)

def alwaysOne : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ, 0 < k →
    let count := R.readout () n k
    (∃ w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, w p q = k) ∧ (∀ q, ∑ p, w p q = k) ∧
      ∀ i, count ≤ commonOneCount w i) ∧
    ∀ w : ParityClass (n + 2) 0 → ParityClass (n + 2) 1 → ℕ,
      (∀ p, ∑ q, w p q = k) → (∀ q, ∑ p, w p q = k) →
      ∃ i, commonOneCount w i ≤ count

private theorem always_one_fails : ¬ arena.Law alwaysOne := by
  intro law
  obtain ⟨w, rows, cols, lower⟩ := (law 0 1 Nat.one_pos).1
  obtain ⟨i, upper⟩ := (best_profile_count 0 1 Nat.one_pos).2 w rows cols
  exact (Nat.not_succ_le_zero 0) ((lower i).trans upper)

def family : Registration arena (type_of% best_profile_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨best_profile_count, alwaysOne, always_one_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysOne, ?_, rfl, always_one_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    exact ⟨0, 1, 2, by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    best_profile_count (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching.bestCount
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
