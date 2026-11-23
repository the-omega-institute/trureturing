import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation

open _root_.D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation
open private Arc Positive normalizedSep adjacencySep directedSep HasSpanningOutArborescence
  from D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation

namespace Reg.D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

namespace Normalized

abbrev signature : Signature where
  Params := Σ n, Σ G : SimpleGraph (Fin n), MvPolynomial (G.edgeSet) ℤ
  State p := (p.2.1.edgeSet) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => MvPolynomial.eval₂ (Int.castRingHom ℝ) w p.2.2)
    (fun e => nomatch e)

/-- Replace the evaluation with the indicator of separation at the same weights. -/
def rejected : Realization signature := by
  classical
  exact realize signature (fun _ p w => if normalizedSep p.2.1 w then 1 else 0)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ ∀ (n : ℕ), 2 ≤ n → ∀ G : SimpleGraph (Fin n), G.Connected →
    ∃ (degree : ℕ) (P : MvPolynomial (G.edgeSet) ℤ), P ≠ 0 ∧ P.IsHomogeneous degree ∧
      ∀ w, Positive w → (normalizedSep G w ↔ R.readout () ⟨n, G, P⟩ w ≠ 0)

theorem rejected_fails : ¬ arena.Law rejected := by
  classical
  intro h
  apply h
  intro n _ G
  intro _
  refine ⟨0, 1, one_ne_zero, MvPolynomial.isHomogeneous_one _ _, ?_⟩
  intro w _
  change normalizedSep G w ↔ (if normalizedSep G w then (1 : ℝ) else 0) ≠ 0
  by_cases hSep : normalizedSep G w <;> simp [hSep]

def family : Registration arena (type_of% @normalized_refuted) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨normalized_refuted, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro _
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro _ h
      exact (h rfl).elim
    · intro a
      exact nomatch a
  dependence := by
    intro _
    let G := (SimpleGraph.pathGraph 5)
    let e : G.edgeSet := ⟨s(0, 1), SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)⟩
    refine ⟨⟨_, G, MvPolynomial.X e⟩, (fun _ => 1), (fun _ => 2), ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@normalized_refuted) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation.normalized_refuted.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation.Normalized.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ p w => MvPolynomial.eval₂ (Int.castRingHom ℝ) w p.2.2)
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation
    definition := some {
      owner := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation
      name := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation.NormalizedClaim
      path := #["arg"] }
    coordinates := #[0, 2, 5]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Normalized

namespace Adjacency

abbrev signature : Signature where
  Params := Σ n, Σ G : SimpleGraph (Fin n), MvPolynomial (G.edgeSet) ℤ
  State p := (p.2.1.edgeSet) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => MvPolynomial.eval₂ (Int.castRingHom ℝ) w p.2.2)
    (fun e => nomatch e)

/-- Replace the evaluation with the indicator of separation at the same weights. -/
def rejected : Realization signature := by
  classical
  exact realize signature (fun _ p w => if adjacencySep p.2.1 w then 1 else 0)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ ∀ (n : ℕ), 2 ≤ n → ∀ G : SimpleGraph (Fin n), G.Connected →
    ∃ (degree : ℕ) (P : MvPolynomial (G.edgeSet) ℤ), P ≠ 0 ∧ P.IsHomogeneous degree ∧
      ∀ w, Positive w → (adjacencySep G w ↔ R.readout () ⟨n, G, P⟩ w ≠ 0)

theorem rejected_fails : ¬ arena.Law rejected := by
  classical
  intro h
  apply h
  intro n _ G
  intro _
  refine ⟨0, 1, one_ne_zero, MvPolynomial.isHomogeneous_one _ _, ?_⟩
  intro w _
  change adjacencySep G w ↔ (if adjacencySep G w then (1 : ℝ) else 0) ≠ 0
  by_cases hSep : adjacencySep G w <;> simp [hSep]

def family : Registration arena (type_of% @adjacency_refuted) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨adjacency_refuted, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro _
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro _ h
      exact (h rfl).elim
    · intro a
      exact nomatch a
  dependence := by
    intro _
    let G := (SimpleGraph.pathGraph 5)
    let e : G.edgeSet := ⟨s(0, 1), SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)⟩
    refine ⟨⟨_, G, MvPolynomial.X e⟩, (fun _ => 1), (fun _ => 2), ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@adjacency_refuted) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation.adjacency_refuted.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation.Adjacency.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ p w => MvPolynomial.eval₂ (Int.castRingHom ℝ) w p.2.2)
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation
    definition := some {
      owner := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation
      name := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation.AdjacencyClaim
      path := #["arg"] }
    coordinates := #[0, 2, 5]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Adjacency

namespace Directed

abbrev signature : Signature where
  Params := Σ n, Σ G : Digraph (Fin n), MvPolynomial (Arc G) ℤ
  State p := (Arc p.2.1) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => MvPolynomial.eval₂ (Int.castRingHom ℝ) w p.2.2)
    (fun e => nomatch e)

/-- Replace the evaluation with the indicator of separation at the same weights. -/
def rejected : Realization signature := by
  classical
  exact realize signature (fun _ p w => if directedSep p.2.1 w then 1 else 0)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ ∀ (n : ℕ), 2 ≤ n → ∀ G : Digraph (Fin n), (∀ i, ¬ G.Adj i i) →
    HasSpanningOutArborescence G →
    ∃ (degree : ℕ) (P : MvPolynomial (Arc G) ℤ), P ≠ 0 ∧ P.IsHomogeneous degree ∧
      ∀ w, Positive w → (directedSep G w ↔ R.readout () ⟨n, G, P⟩ w ≠ 0)

theorem rejected_fails : ¬ arena.Law rejected := by
  classical
  intro h
  apply h
  intro n _ G
  intro _ _
  refine ⟨0, 1, one_ne_zero, MvPolynomial.isHomogeneous_one _ _, ?_⟩
  intro w _
  change directedSep G w ↔ (if directedSep G w then (1 : ℝ) else 0) ≠ 0
  by_cases hSep : directedSep G w <;> simp [hSep]

def family : Registration arena (type_of% @directed_refuted) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨directed_refuted, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro _
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro _ h
      exact (h rfl).elim
    · intro a
      exact nomatch a
  dependence := by
    intro _
    let G := (⟨fun i j => i.val + 1 = j.val⟩ : Digraph (Fin 3))
    let e : Arc G := ⟨(0, 1), rfl⟩
    refine ⟨⟨_, G, MvPolynomial.X e⟩, (fun _ => 1), (fun _ => 2), ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@directed_refuted) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation.directed_refuted.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation.Directed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ p w => MvPolynomial.eval₂ (Int.castRingHom ℝ) w p.2.2)
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation
    definition := some {
      owner := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation
      name := `D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation.DirectedClaim
      path := #["arg"] }
    coordinates := #[0, 2, 6]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Directed

end

end Reg.D5.S3.Combinatorics.SpectralGraph.PinedaSeparatingWeightsRefutation
