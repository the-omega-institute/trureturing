import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
import Reg.Support.DependentFamily

/-! The attainable directions depend on the parity of the requested counts. -/

namespace Reg.D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching

open Finset LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
open scoped Classical

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
  realize signature (fun _ _ d => d) (fun e => nomatch e)

def alwaysOdd : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (d : Fin (n + 2) → ℕ), ∑ i, d i = 2 ^ (n + 1) →
    ((∃ (F : ParityClass (n + 2) 0 ≃ ParityClass (n + 2) 1)
        (dir : ParityClass (n + 2) 0 → Fin (n + 2)),
      (∀ p, F p = flipToOdd p (dir p)) ∧
        ∀ i, (∑ p, if dir p = i then 1 else (0 : ℕ)) = d i) ↔
      ∀ i, Even (R.readout () n d i))

private theorem always_odd_fails : ¬ arena.Law alwaysOdd := by
  intro law
  let d (i : Fin 2) : ℕ := if i = 0 then 2 else 0
  have total : (∑ i, d i) = 2 ^ (0 + 1) := by simp [d]
  have even : ∀ i, Even (d i) := by
    intro i
    by_cases h : i = 0 <;> simp [d, h]
  have existsMatching := (exact_matching_directions 0 d total).mpr even
  have contradiction' : Even (1 : ℕ) := ((law 0 d total).mp existsMatching) 0
  exact (by decide : ¬ Even (1 : ℕ)) contradiction'

def family : Registration arena (type_of% exact_matching_directions) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_matching_directions, alwaysOdd, always_odd_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysOdd, ?_, rfl, always_odd_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
    intro eq
    exact Nat.zero_ne_one (congrFun eq 0)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_matching_directions (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching.directionCounts
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Hypercube.DirectionMatching
