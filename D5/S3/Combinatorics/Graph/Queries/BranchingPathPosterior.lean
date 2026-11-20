/- GID: D5/S3/Combinatorics/Graph/Queries/BranchingPathPosterior
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/BranchingPathPosterior
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: A branching disclosure restricts the graph posterior to the recorded edges. -/

import D5.S3.Combinatorics.Graph.Queries.ForwardPathPosterior

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
open D5.S3.Combinatorics.Graph.Queries.ForwardPathPosterior
open scoped ENNReal

namespace D5.S3.Combinatorics.Graph.Queries.BranchingPathPosterior

variable {P V W : Type*}

/-- The incoming edge selected from the previously recorded edges at a slot request. -/
def incoming (initial : V × V) (parent : P → ℕ → ℕ) (p : P)
    (history : List (V × V)) : V × V :=
  history[parent p history.length]?.getD initial

private theorem incoming_adj {G : SimpleGraph V} {initial : V × V} {parent : P → ℕ → ℕ}
    {history : List (V × V)} (p : P) (hInitial : G.Adj initial.1 initial.2)
    (hHistory : ∀ e ∈ history, G.Adj e.1 e.2) :
    G.Adj (incoming initial parent p history).1 (incoming initial parent p history).2 := by
  unfold incoming
  cases h : history[parent p history.length]? with
  | none => exact hInitial
  | some e => exact hHistory e (List.mem_of_getElem? h)

private theorem constraints_iff {G : SimpleGraph V}
    (initial : V × V) (parent : P → ℕ → ℕ)
    (choices reference : P → (V × V) → Bool → V)
    (ref : P → Equiv.Perm Bool) (schedule : Schedule P)
    (hInitial : G.Adj initial.1 initial.2)
    (history : List (V × V)) (hHistory : ∀ e ∈ history, G.Adj e.1 e.2) :
    let next := fun p h y => ((incoming initial parent p h).2, y) :: h
    let t := run (fun p h => reference p (incoming initial parent p h))
      next ref schedule history
    let source := fun row : Entry P (List (V × V)) V =>
      incoming initial parent row.1.1 row.2.1
    (∀ row ∈ t, G.Adj (source row).1 (source row).2 →
      (row.2.2 ∈ Set.range (choices row.1.1 (source row)) ↔
        G.Adj (source row).2 row.2.2 ∧ row.2.2 ≠ (source row).1)) →
    (∀ row ∈ t, row.2.2 ≠ (source row).1) →
    ((∀ row ∈ t, G.Adj (source row).2 row.2.2) ↔
      (∀ row ∈ t, row.2.2 ∈ Set.range (choices row.1.1 (source row)))) := by
  induction schedule generalizing history with
  | nil => simp [run]
  | cons slot schedule ih =>
    obtain ⟨p, b⟩ := slot
    intro next t source hAvailable hNB
    let e := incoming initial parent p history
    let y := reference p e (ref p b)
    let first : Entry P (List (V × V)) V := ((p, b), history, y)
    let rest := run (fun p h => reference p (incoming initial parent p h))
      next ref schedule ((e.2, y) :: history)
    have hSource : source first = e := rfl
    have hFirst : first ∈ t := List.mem_cons_self
    have hRest {row : Entry P (List (V × V)) V} (hr : row ∈ rest) : row ∈ t :=
      List.mem_cons_of_mem _ hr
    have hPair : G.Adj e.1 e.2 := incoming_adj p hInitial hHistory
    have hLocal : y ∈ Set.range (choices p e) ↔ G.Adj e.2 y ∧ y ≠ e.1 :=
      hAvailable first hFirst hPair
    have hn : y ≠ e.1 := hNB first hFirst
    have hRec (he : G.Adj e.2 y) :=
      ih ((e.2, y) :: history) (by simpa only [List.forall_mem_cons] using ⟨he, hHistory⟩)
        (fun r hr => hAvailable r (hRest hr)) (fun r hr => hNB r (hRest hr))
    change (∀ row ∈ first :: rest, G.Adj (source row).2 row.2.2) ↔
      (∀ row ∈ first :: rest, row.2.2 ∈ Set.range (choices row.1.1 (source row)))
    simp only [List.forall_mem_cons, hSource]
    change (G.Adj e.2 y ∧ _) ↔ (y ∈ Set.range (choices p e) ∧ _)
    constructor
    · rintro ⟨he, ht⟩
      exact ⟨hLocal.mpr ⟨he, hn⟩, (hRec he).mp ht⟩
    · rintro ⟨ha, ht⟩
      have he := (hLocal.mp ha).1
      exact ⟨he, (hRec he).mpr ht⟩

/-- The posterior restricts the graph prior to worlds containing every recorded edge. -/
theorem graph_branching_posterior [Fintype P] [DecidableEq P]
    (π : PMF W) (graph : W → SimpleGraph V)
    (choices : W → P → (V × V) → Bool → V)
    (hPair : ∀ w p state, Function.Injective (choices w p state))
    (initial : V × V) (hInitial : ∀ w, (graph w).Adj initial.1 initial.2)
    (parent : P → ℕ → ℕ) (slots : Schedule P) (ref : W × (P → Equiv.Perm Bool))
    (states : P → V × V) (observed : P → Bool → Option V)
    (seen : Finset P) (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, observed p b = some v) :
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
    let edges := t.map fun row => ((source row).2, row.2.2)
    let allowed : Set W := {w | ∀ e ∈ edges, (graph w).Adj e.1 e.2}
    μ.toOuterMeasure H ≠ 0 →
      ∀ B : Set W, μ.toOuterMeasure (H ∩ Prod.fst ⁻¹' B) / μ.toOuterMeasure H =
        π.toOuterMeasure (allowed ∩ B) / π.toOuterMeasure allowed := by
  intro next candidate t source hAvailable hNB hStates hObs Ω μ H edges allowed
  have hReplay : H = {x | Matches (fun p => choices x.1 p (states p)) observed x.2} := by
    ext world
    change (run (candidate world.1) next world.2 slots [] = t) ↔ _
    rw [show t = run (candidate ref.1) next ref.2 slots [] from rfl, replay_iff]
    constructor
    · intro h p b v hv
      obtain ⟨history, hr⟩ := (hObs p b v).mp hv
      have hs := hStates ((p,b), history, v) hr
      have hMatch := h ((p,b), history, v) hr
      change incoming initial parent p history = states p at hs
      change choices world.1 p (incoming initial parent p history) (world.2 p b) = v at hMatch
      rw [hs] at hMatch
      exact hMatch
    · intro h row hr
      obtain ⟨⟨p, b⟩, history, v⟩ := row
      have hs := hStates ((p,b), history,v) hr
      change incoming initial parent p history = states p at hs
      change choices world.1 p (incoming initial parent p history) (world.2 p b) = v
      rw [hs]
      exact h p b v ((hObs p b v).mpr ⟨history, hr⟩)
  have hReferenceValues := (replay_iff (candidate ref.1) (candidate ref.1)
    next ref.2 ref.2 slots []).mp rfl
  have hAllowed : allowed = {w | Compatible (fun p => choices w p (states p)) observed} := by
    ext w
    change (∀ e ∈ edges, (graph w).Adj e.1 e.2) ↔
      Compatible (fun p => choices w p (states p)) observed
    simp only [edges, List.forall_mem_map]
    rw [constraints_iff initial parent (choices w) (choices ref.1) ref.2 slots
      (hInitial w) [] (by simp) (hAvailable w) hNB]
    constructor
    · intro h
      constructor
      · intro p b v hv
        obtain ⟨history, hr⟩ := (hObs p b v).mp hv
        have hu := h ((p,b), history, v) hr
        change v ∈ Set.range (choices w p (source ((p, b), history, v))) at hu
        rw [hStates _ hr] at hu
        exact hu
      · intro p v hFalse hTrue
        obtain ⟨h1, hr1⟩ := (hObs p false v).mp hFalse
        obtain ⟨h2, hr2⟩ := (hObs p true v).mp hTrue
        have hv1 := hReferenceValues ((p, false), h1, v) hr1
        have hv2 := hReferenceValues ((p, true), h2, v) hr2
        change choices ref.1 p (source ((p,false),h1,v)) (ref.2 p false) = v at hv1
        change choices ref.1 p (source ((p,true),h2,v)) (ref.2 p true) = v at hv2
        rw [hStates _ hr1] at hv1
        rw [hStates _ hr2] at hv2
        exact Bool.false_ne_true ((ref.2 p).injective (hPair _ _ _ (hv1.trans hv2.symm)))
    · intro h row hr
      obtain ⟨⟨p,b⟩, history, v⟩ := row
      change v ∈ Set.range (choices w p (source ((p, b), history, v)))
      rw [hStates _ hr]
      exact h.1 p b v ((hObs p b v).mpr ⟨history, hr⟩)
  rw [hReplay, hAllowed]
  exact partial_forward_order_posterior π (fun w p => choices w p (states p))
    (fun w p => hPair w p (states p)) observed seen hSeen

end D5.S3.Combinatorics.Graph.Queries.BranchingPathPosterior
