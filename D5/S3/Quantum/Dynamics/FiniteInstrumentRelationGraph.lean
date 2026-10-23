/- GID: D5/S3/Quantum/Dynamics/FiniteInstrumentRelationGraph
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/FiniteInstrumentRelationGraph
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Finite adaptive quantum instrument trees have unique static typed relation solutions. -/

import D5.S3.Quantum.Recovery.FiniteLocalProtocol

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph
open D5.S3.Quantum.Recovery.FiniteLocalProtocol
variable {A R Feedback : Type} [Fintype A] [DecidableEq A] [Fintype R]

/-- An independent matrix variable is assigned to each actual prefix vertex.
The inductive index preserves finite, outcome-dependent quantum interfaces. -/
inductive Assignment : {d : A → ℕ} → Tree Feedback d → Type
  | leaf {d : A → ℕ} {f : Feedback} (X : State R d) : Assignment (d := d) (.leaf (d := d) f)
  | node {d : A → ℕ} {J : Instrument d}
      {child : (y : Fin J.outcomes) → Tree Feedback (J.output y)}
      (X : State R d) (below : (y : Fin J.outcomes) → Assignment (child y)) :
      Assignment (d := d) (.node J child)

def rootValue {d : A → ℕ} {T : Tree Feedback d} : Assignment (R := R) T → State R d
  | .leaf X => X
  | .node X _ => X

/-- Neighbor equations use the actual local CP maps. Global equality is not an input. -/
def GraphLaw : {d : A → ℕ} → {T : Tree Feedback d} → Assignment (R := R) T → Prop
  | _, .leaf _, .leaf _ => True
  | _, .node J _, .node X below => ∀ y,
      rootValue (below y) = step J y X ∧ GraphLaw (below y)

def evaluate : {d : A → ℕ} → (T : Tree Feedback d) → State R d → Assignment (R := R) T
  | _, .leaf _, X => .leaf X
  | _, .node J child, X => .node X (fun y => evaluate (child y) (step J y X))

private theorem evaluate_root {d : A → ℕ} (T : Tree Feedback d) (X : State R d) :
    rootValue (evaluate T X) = X := by cases T <;> rfl

private theorem evaluate_law {d : A → ℕ} (T : Tree Feedback d) (X : State R d) :
    GraphLaw (evaluate T X) := by
  induction T with
  | leaf => trivial
  | @node d J child ih =>
    intro y
    exact ⟨evaluate_root (child y) _, ih y _⟩

private theorem law_unique {d : A → ℕ} (T : Tree Feedback d)
    (φ ψ : Assignment (R := R) T) (hφ : GraphLaw φ) (hψ : GraphLaw ψ)
    (hr : rootValue φ = rootValue ψ) : φ = ψ := by
  induction T with
  | leaf =>
    cases φ with | leaf X =>
      cases ψ with | leaf Y => exact congrArg Assignment.leaf hr
  | @node d J child ih =>
    cases φ with | node X below =>
      cases ψ with | node Y below' =>
        have hxy : X = Y := hr
        subst Y
        have hb : below = below' := by
          funext y
          exact ih y (below y) (below' y) (hφ y).2 (hψ y).2
            ((hφ y).1.trans (hψ y).1.symm)
        cases hb
        rfl

/-- Reading the terminal vertices is independent of operational evaluation. -/
def graphLeaves : {d : A → ℕ} → {T : Tree Feedback d} →
    Assignment (R := R) T → List (Terminal Feedback R A)
  | d, .leaf f, .leaf X => [⟨[],f,d,X⟩]
  | _, .node _ _, .node _ below => (List.ofFn (fun y =>
      (graphLeaves (below y)).map
        (fun z => {z with history := y.val :: z.history}))).flatten

/-- Reading all prefix vertices retains actual records and early terminals. -/
def graphPrefixes : {d : A → ℕ} → {T : Tree Feedback d} →
    Assignment (R := R) T → List (Terminal (Option Feedback) R A)
  | d, .leaf f, .leaf X => [⟨[],some f,d,X⟩]
  | d, .node _ _, .node X below => ⟨[],none,d,X⟩ ::
      (List.ofFn (fun y => (graphPrefixes (below y)).map
        (fun z => {z with history := y.val :: z.history}))).flatten

private theorem evaluate_observations {d : A → ℕ} (T : Tree Feedback d) (X : State R d) :
    graphLeaves (evaluate T X) = terminalOutputs T X ∧
      graphPrefixes (evaluate T X) = coarsePrefixes T X := by
  induction T with
  | leaf => exact ⟨rfl,rfl⟩
  | @node d J child ih =>
    constructor
    · simp only [evaluate, graphLeaves, terminalOutputs]
      congr 1
      apply congrArg List.ofFn
      funext y
      exact congrArg (List.map _) (ih y (step J y X)).1
    · simp only [evaluate, graphPrefixes, coarsePrefixes]
      congr 2
      apply congrArg List.ofFn
      funext y
      exact congrArg (List.map _) (ih y (step J y X)).2

/-- The graph has exactly one solution at each reference boundary. It preserves every actual
record and the complete retained terminal matrix, including correlated reference coordinates.
Local CP normalization gives total terminal trace; no Born law is derived from staticity. -/
theorem relation_graph_protocol_correspondence {d : A → ℕ} (T : Tree Feedback d)
    (X : State R d) :
    ∃! φ : Assignment (R := R) T, GraphLaw φ ∧ rootValue φ = X ∧
      graphLeaves φ = terminalOutputs T X ∧
      graphPrefixes φ = coarsePrefixes T X ∧
      ((graphLeaves φ).map (fun z => Matrix.trace z.state)).sum = Matrix.trace X := by
  refine ⟨evaluate T X, ⟨evaluate_law T X, evaluate_root T X,
    (evaluate_observations T X).1, (evaluate_observations T X).2, ?_⟩, ?_⟩
  · rw [(evaluate_observations T X).1]
    exact complete_subtree_trace T X
  · intro ψ hψ
    exact law_unique T ψ (evaluate T X) hψ.1 (evaluate_law T X)
      (hψ.2.1.trans (evaluate_root T X).symm)

#print axioms relation_graph_protocol_correspondence
end D5.S3.Quantum.Dynamics.FiniteInstrumentRelationGraph
