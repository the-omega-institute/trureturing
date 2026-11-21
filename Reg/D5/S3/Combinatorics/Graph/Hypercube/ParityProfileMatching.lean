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
    intro role
    cases role
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
  readout := some (realize signature (fun _ n k => best n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "value"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev boundarySignature : Signature where
  Params := Σ _ : ℕ, ℕ
  State p := Fin (p.1 + 2) → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def boundaryActual : Realization boundarySignature :=
  realize boundarySignature (fun _ p v => by classical exact decide (ProfileBoundary p.1 p.2 v))
    (fun e => nomatch e)

def boundaryFalse : Realization boundarySignature :=
  realize boundarySignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev boundaryArena : Arena where
  signature := boundarySignature
  Law R := ∀ n k (v : Fin (n + 2) → ℕ),
    (FeasibleProfileFloor n k v ∧
      ∀ u, FeasibleProfileFloor n k u → (∀ i, v i ≤ u i) → u = v) ↔
      R.readout () ⟨n, k⟩ v = true

private theorem zero_boundary : ProfileBoundary 0 0 (fun _ => 0) := by
  simp [ProfileBoundary]

private theorem one_not_boundary : ¬ ProfileBoundary 0 0 (fun _ => 1) := by
  intro h
  have limit := h.1 (0 : Fin 2)
  simp at limit

private theorem boundaryFalse_fails : ¬ boundaryArena.Law boundaryFalse := by
  intro h
  have no := (h 0 0 (fun _ => 0)).1 ((exact_profile_frontier 0 0 _).2 zero_boundary)
  simp [boundaryFalse, realize] at no

def boundaryFamily : Registration boundaryArena (type_of% exact_profile_frontier) where
  actual := boundaryActual
  bridge := by
    classical
    simp [boundaryActual, realize]
  variation := ⟨by
    classical
    simpa [boundaryArena, boundaryActual, realize] using exact_profile_frontier,
    boundaryFalse, boundaryFalse_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨boundaryFalse, fun j hj => (hj (Subsingleton.elim j role)).elim,
        rfl, boundaryFalse_fails⟩
    · intro e
      exact nomatch e
  dependence := by
    classical
    intro role
    cases role
    refine ⟨⟨0, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    simp [boundaryActual, realize, zero_boundary, one_not_boundary]

def boundaryRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_profile_frontier (Realization boundarySignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching.boundary
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching.boundaryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨boundaryArena⟩
  objectArena := .source ⟨boundaryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundaryArena ⟨boundaryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundarySignature
    (fun _ p v => by classical exact decide (ProfileBoundary p.1 p.2 v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
