import D5.S3.Combinatorics.Graph.Queries.BranchingPathPosterior
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Read out the graph edges carried by a path disclosure. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.ForwardPathPosterior
open _root_.D5.S3.Combinatorics.Graph.Queries.BranchingPathPosterior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.BranchingPathPosterior

noncomputable section
universe u v w

private abbrev PathSignature : Signature where
  Params := Σ P : Type u, Σ V : Type v, Σ (_ : V × V), P → ℕ → ℕ
  State p := List (Entry p.1 (List (p.2.1 × p.2.1)) p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (p.2.1 × p.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

private def disclosedEdges : Realization PathSignature.{u,v} :=
  realize PathSignature (fun _ p t => t.map fun row => ((incoming p.2.2.1 p.2.2.2 row.1.1 row.2.1).2, row.2.2))
    (fun e => nomatch e)

private abbrev Vertex := ULift.{v} (Fin 4)
private abbrev Position := ULift.{u} Unit

private def initial : Vertex.{v} × Vertex.{v} := (⟨0⟩, ⟨1⟩)
private def choices : Position.{u} → (Vertex.{v} × Vertex.{v}) → Bool → Vertex.{v} :=
  fun _ _ b => if b then ⟨3⟩ else ⟨2⟩

private theorem choices_injective (p : Position.{u}) (s : Vertex.{v} × Vertex.{v}) :
    Function.Injective (choices p s) := by
  intro a b h
  cases a <;> cases b <;> simp_all [choices]

private def extraEdge : Realization PathSignature.{u,v} :=
  realize PathSignature
    (fun _ p t => t.map fun row =>
      let endpoint := (incoming p.2.2.1 p.2.2.2 row.1.1 row.2.1).2
      (endpoint, endpoint))
    (fun e => nomatch e)

private abbrev PathArena : Arena where
  signature := PathSignature.{u,v}
  Law R := ∀ {P : Type u} {V : Type v} {W : Type w} [Fintype P] [DecidableEq P]
    (π : PMF W) (graph : W → SimpleGraph V)
    (choices : W → P → (V × V) → Bool → V)
    (hPair : ∀ w p state, Function.Injective (choices w p state))
    (initial : V × V) (hInitial : ∀ w, (graph w).Adj initial.1 initial.2)
    (parent : P → ℕ → ℕ) (slots : Schedule P) (ref : W × (P → Equiv.Perm Bool))
    (states : P → V × V) (observed : P → Bool → Option V)
    (seen : Finset P) (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, observed p b = some v),
    let next := fun p h y => ((incoming initial parent p h).2, y) :: h
    let candidate := fun w p h => choices w p (incoming initial parent p h)
    let t := run (candidate ref.1) next ref.2 slots []
    let source := fun row : Entry P (List (V × V)) V =>
      incoming initial parent row.1.1 row.2.1
    (∀ w row, row ∈ t → (graph w).Adj (source row).1 (source row).2 →
      (row.2.2 ∈ Set.range (choices w row.1.1 (source row)) ↔
        (graph w).Adj (source row).2 row.2.2 ∧ row.2.2 ≠ (source row).1)) →
    (∀ row ∈ t, row.2.2 ≠ (source row).1) →
    (∀ row ∈ t, source row = states row.1.1) →
    (∀ p b v, observed p b = some v ↔ ∃ h, ((p, b), h, v) ∈ t) →
    let Ω := P → Equiv.Perm Bool
    let μ : PMF (W × Ω) := π.bind fun w => (uniformPmf Ω).map (Prod.mk w)
    let H : Set (W × Ω) := {x | run (candidate x.1) next x.2 slots [] = t}
    let edges := R.readout () ⟨P, V, initial, parent⟩ t
    let allowed : Set W := {w | ∀ e ∈ edges, (graph w).Adj e.1 e.2}
    μ.toOuterMeasure H ≠ 0 →
      ∀ B : Set W, μ.toOuterMeasure (H ∩ Prod.fst ⁻¹' B) / μ.toOuterMeasure H =
        π.toOuterMeasure (allowed ∩ B) / π.toOuterMeasure allowed

private theorem extraEdge_invalid : ¬ PathArena.{u,v,w}.Law extraEdge := by
  intro h
  let W := ULift.{w} Unit
  let p : Position.{u} := ⟨()⟩
  let world : W := ⟨()⟩
  let π := PMF.pure world
  let graph : W → SimpleGraph Vertex.{v} := fun _ => ⊤
  let Ω := Position.{u} → Equiv.Perm Bool
  let ref : W × Ω := (world, fun _ => 1)
  let parent : Position.{u} → ℕ → ℕ := fun _ _ => 0
  let candidate p history := choices p (incoming initial parent p history)
  let next p history y := ((incoming initial parent p history).2, y) :: history
  let slots : Schedule Position.{u} := [(p, false)]
  let observed : Position.{u} → Bool → Option Vertex.{v} :=
    fun _ b => if b then none else some ⟨2⟩
  let μ : PMF (W × Ω) := π.bind fun w => (uniformPmf Ω).map (Prod.mk w)
  let H : Set (W × Ω) := {x | run candidate next x.2 slots [] =
    run candidate next ref.2 slots []}
  have hPositive : μ.toOuterMeasure H ≠ 0 := by
    rw [ne_eq, PMF.toOuterMeasure_apply_eq_zero_iff, Set.not_disjoint_iff]
    refine ⟨ref, ?_, rfl⟩
    simp [μ, π, ref, uniformPmf]
  have hBad := h π graph (fun _ => choices) (fun _ => choices_injective)
    initial (by simp [graph, initial]) parent slots ref (fun _ => initial) observed {p}
    (by intro q; have : q = p := Subsingleton.elim _ _; subst q; simp [observed])
    (by simp [candidate, next, incoming, parent, run, slots, ref, graph, initial, choices])
    (by simp [candidate, next, incoming, parent, run, slots, ref, initial, choices])
    (by simp [candidate, next, incoming, parent, run, slots, ref])
    (by
      intro q b y
      have : q = p := Subsingleton.elim _ _
      subst q
      cases b <;> simp [observed, candidate, next, incoming, parent, slots, ref, run, choices, eq_comm])
    hPositive Set.univ
  have hEmpty : {w : W | ∀ e ∈ extraEdge.{u,v}.readout () ⟨Position.{u}, Vertex.{v}, initial, parent⟩
      (run candidate next ref.2 slots []), (graph w).Adj e.1 e.2} =
      ∅ := by
    simp [extraEdge, slots, candidate, next, incoming, parent, run, realize]
  change μ.toOuterMeasure (H ∩ Prod.fst ⁻¹' Set.univ) / μ.toOuterMeasure H =
    π.toOuterMeasure (_ ∩ Set.univ) / π.toOuterMeasure _ at hBad
  rw [hEmpty] at hBad
  have hFinite : μ.toOuterMeasure H ≠ ∞ := by
    rw [PMF.toOuterMeasure_apply]
    exact μ.tsum_coe_indicator_ne_top H
  rw [Set.preimage_univ, Set.inter_univ, ENNReal.div_self hPositive hFinite] at hBad
  simpa using hBad

private theorem disclosedEdges_varies :
    disclosedEdges.{u,v}.readout () ⟨Position.{u}, Vertex.{v}, initial, fun _ _ => 0⟩ [] ≠
      disclosedEdges.{u,v}.readout () ⟨Position.{u}, Vertex.{v}, initial, fun _ _ => 0⟩
        [((⟨()⟩, false), [], ⟨2⟩)] := by
  simp [disclosedEdges, realize]


def evidence : Registration PathArena.{u,v,w} (type_of% (@graph_branching_posterior.{u,v,w})) where
  actual := disclosedEdges
  bridge := Iff.rfl
  variation := ⟨@graph_branching_posterior.{u,v,w}, extraEdge, extraEdge_invalid⟩
  sensitivity := ⟨fun i => ⟨extraEdge,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, extraEdge_invalid⟩,
    fun e => nomatch e⟩
  dependence := fun _ => ⟨⟨Position.{u}, Vertex.{v}, initial, fun _ _ => 0⟩, [], _, disclosedEdges_varies⟩

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@graph_branching_posterior.{u,v,w}) (Realization PathSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.BranchingPathPosterior.graph_branching_posterior
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.BranchingPathPosterior.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨PathArena.{u,v,w}⟩
  objectArena := .source ⟨PathArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source PathArena.{u,v,w} ⟨evidence.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PathSignature
    (fun _ p t => t.map fun row => ((incoming p.2.2.1 p.2.2.2 row.1.1 row.2.1).2, row.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.BranchingPathPosterior
    definition := none
    coordinates := #[0, 1, 9, 11]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body",
        "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Queries.BranchingPathPosterior
