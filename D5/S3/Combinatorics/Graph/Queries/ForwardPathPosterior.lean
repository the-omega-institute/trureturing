/- GID: D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/ForwardPathPosterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A disclosed nonbacktracking path conditions the graph prior on its edges. -/

import D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! The forward candidate pair may depend on the preceding vertices of the path. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
open scoped ENNReal

namespace D5.S3.Combinatorics.Graph.Queries.ForwardPathPosterior

variable {P V W S : Type*}

abbrev Schedule (P : Type*) := List (P × Bool)
abbrev Entry (P S V : Type*) := (P × Bool) × S × V

def run (choices : P → S → Bool → V) (next : P → S → V → S)
    (f : P → Equiv.Perm Bool) : Schedule P → S → List (Entry P S V)
  | [], _ => []
  | (p, b) :: slots, state =>
    let value := choices p state (f p b)
    ((p, b), state, value) :: run choices next f slots (next p state value)

private theorem replay_iff (candidate reference : P → S → Bool → V)
    (next : P → S → V → S) (table ref : P → Equiv.Perm Bool)
    (slots : Schedule P) (initial : S) :
    run candidate next table slots initial = run reference next ref slots initial ↔
      ∀ e ∈ run reference next ref slots initial,
        candidate e.1.1 e.2.1 (table e.1.1 e.1.2) = e.2.2 := by
  induction slots generalizing initial with
  | nil => simp [run]
  | cons slot slots ih =>
    obtain ⟨p, b⟩ := slot
    let x := candidate p initial (table p b)
    let y := reference p initial (ref p b)
    change ((p, b), initial, x) :: run candidate next table slots (next p initial x) =
      ((p, b), initial, y) :: run reference next ref slots (next p initial y) ↔ _
    constructor
    · intro h e he
      obtain ⟨hHead, hTail⟩ := List.cons.inj h
      have hxy : x = y := congrArg (fun row : Entry P S V => row.2.2) hHead
      change e ∈ ((p, b), initial, y) :: run reference next ref slots (next p initial y) at he
      rcases List.mem_cons.mp he with rfl | he
      · exact hxy
      · rw [hxy] at hTail
        exact (ih _).mp hTail e he
    · intro h
      have hxy : x = y := h ((p, b), initial, y) List.mem_cons_self
      rw [hxy, (ih _).mpr fun e he => h e (List.mem_cons_of_mem _ he)]

/-- The reference rows specify the initial states and the observed values for each visited slot. -/
private theorem same_transcript_iff
    (candidate reference : P → S → Bool → V)
    (next : P → S → V → S) (f ref : P → Equiv.Perm Bool)
    (slots : Schedule P) (initial : S)
    (states : P → S) (observed : P → Bool → Option V)
    (hState : ∀ e ∈ run reference next ref slots initial, e.2.1 = states e.1.1)
    (hObs : ∀ p b v, observed p b = some v ↔
      ((p, b), states p, v) ∈ run reference next ref slots initial) :
    run candidate next f slots initial = run reference next ref slots initial ↔
      Matches (fun p => candidate p (states p)) observed f := by
  rw [replay_iff]
  constructor
  · intro h p b v hv
    exact h ((p, b), states p, v) ((hObs p b v).mp hv)
  · intro h e he
    obtain ⟨⟨p, b⟩, state, v⟩ := e
    have hre : state = states p := hState _ he
    subst state
    exact h p b v ((hObs p b v).mpr he)

private theorem state_dependent_posterior [Fintype P] [DecidableEq P]
    (π : PMF W) (choices : W → P → S → Bool → V)
    (next : P → S → V → S) (initial : S) (slots : Schedule P)
    (ref : W × (P → Equiv.Perm Bool))
    (states : P → S) (observed : P → Bool → Option V)
    (seen : Finset P) (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, observed p b = some v)
    (hState : ∀ e ∈ run (choices ref.1) next ref.2 slots initial, e.2.1 = states e.1.1)
    (hObs : ∀ p b v, observed p b = some v ↔
      ((p, b), states p, v) ∈ run (choices ref.1) next ref.2 slots initial)
    (hChoice : ∀ w p, Function.Injective (choices w p (states p))) :
    let Ω := P → Equiv.Perm Bool
    let μ : PMF (W × Ω) := π.bind fun w => (uniformPmf Ω).map (Prod.mk w)
    let H : Set (W × Ω) := {x | run (choices x.1) next x.2 slots initial =
      run (choices ref.1) next ref.2 slots initial}
    let feasible : Set W := {w | Compatible (fun p => choices w p (states p)) observed}
    μ.toOuterMeasure H ≠ 0 →
      ∀ B : Set W, μ.toOuterMeasure (H ∩ Prod.fst ⁻¹' B) / μ.toOuterMeasure H =
        π.toOuterMeasure (feasible ∩ B) / π.toOuterMeasure feasible := by
  intro Ω μ H feasible
  have he : H = {x | Matches (fun p => choices x.1 p (states p)) observed x.2} := by
    ext x
    exact same_transcript_iff (choices x.1) (choices ref.1) next x.2 ref.2
      slots initial states observed hState hObs
  rw [he]
  exact partial_forward_order_posterior π (fun w p => choices w p (states p))
    hChoice observed seen hSeen


/-- An incoming edge from the preceding step suffices to test availability at the next step. -/
private theorem path_edge_constraints_iff {G : SimpleGraph V}
    (choices reference : P → (V × V) → Bool → V)
    (ref : P → Equiv.Perm Bool) (slots : Schedule P) (initial : V × V)
    (hIncoming : G.Adj initial.1 initial.2) :
    let t := run reference (fun _ s y => (s.2, y)) ref slots initial
    (∀ row ∈ t, G.Adj row.2.1.1 row.2.1.2 →
      (row.2.2 ∈ Set.range (choices row.1.1 row.2.1) ↔
        G.Adj row.2.1.2 row.2.2 ∧ row.2.2 ≠ row.2.1.1)) →
    (∀ row ∈ t, row.2.2 ≠ row.2.1.1) →
    ((∀ r ∈ t, G.Adj r.2.1.2 r.2.2) ↔
      (∀ r ∈ t, r.2.2 ∈ Set.range (choices r.1.1 r.2.1))) := by
  induction slots generalizing initial with
  | nil => simp [run]
  | cons slot slots ih =>
    intro t availability hNB
    obtain ⟨p, b⟩ := slot
    let y := reference p initial (ref p b)
    let head : Entry P (V × V) V := ((p, b), initial, y)
    let tail := run reference (fun _ s z => (s.2, z)) ref slots (initial.2, y)
    have hNBHead : y ≠ initial.1 := hNB head List.mem_cons_self
    have hNBTail : ∀ r ∈ tail, r.2.2 ≠ r.2.1.1 := fun r hr =>
      hNB r (List.mem_cons_of_mem _ hr)
    change (∀ r ∈ head :: tail, G.Adj r.2.1.2 r.2.2) ↔
      (∀ r ∈ head :: tail, r.2.2 ∈ Set.range (choices r.1.1 r.2.1))
    have hAvailableHead := availability head List.mem_cons_self hIncoming
    have hAvailableTail : ∀ row ∈ tail, G.Adj row.2.1.1 row.2.1.2 →
        (row.2.2 ∈ Set.range (choices row.1.1 row.2.1) ↔
          G.Adj row.2.1.2 row.2.2 ∧ row.2.2 ≠ row.2.1.1) :=
      fun row hr => availability row (List.mem_cons_of_mem _ hr)
    constructor
    · intro h r hr
      have hEdge : G.Adj initial.2 y := h head List.mem_cons_self
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hAvailableHead.mpr ⟨hEdge, hNBHead⟩
      · exact (ih (initial.2, y) hEdge hAvailableTail hNBTail).mp
          (fun r hr => h r (List.mem_cons_of_mem _ hr)) r hr
    · intro h r hr
      have hAvail : y ∈ Set.range (choices p initial) := h head List.mem_cons_self
      have hEdge : G.Adj initial.2 y :=
        (hAvailableHead.mp hAvail).1
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hEdge
      · exact (ih (initial.2, y) hEdge hAvailableTail hNBTail).mpr
          (fun r hr => h r (List.mem_cons_of_mem _ hr)) r hr


private theorem value_of_row (choices : P → S → Bool → V) (next : P → S → V → S)
    (f : P → Equiv.Perm Bool) (slots : Schedule P) (initial : S)
    (row : Entry P S V) (hrow : row ∈ run choices next f slots initial) :
    row.2.2 = choices row.1.1 row.2.1 (f row.1.1 row.1.2) := by
  induction slots generalizing initial with
  | nil => simp [run] at hrow
  | cons slot slots ih =>
    obtain ⟨p, b⟩ := slot
    simp only [run, List.mem_cons] at hrow
    rcases hrow with rfl | htail
    · rfl
    · exact ih _ htail

private theorem path_compatibility_iff_edges {G : SimpleGraph V}
    (choices reference : P → (V × V) → Bool → V)
    (href : ∀ p state, Function.Injective (reference p state))
    (ref : P → Equiv.Perm Bool) (slots : Schedule P) (initial : V × V)
    (hIncoming : G.Adj initial.1 initial.2)
    (states : P → V × V) (observed : P → Bool → Option V) :
    let next : P → (V × V) → V → (V × V) := fun _ s y => (s.2, y)
    let t := run reference next ref slots initial
    (∀ row ∈ t, G.Adj row.2.1.1 row.2.1.2 →
      (row.2.2 ∈ Set.range (choices row.1.1 row.2.1) ↔
        G.Adj row.2.1.2 row.2.2 ∧ row.2.2 ≠ row.2.1.1)) →
    (∀ row ∈ t, row.2.2 ≠ row.2.1.1) →
    (∀ row ∈ t, row.2.1 = states row.1.1) →
    (∀ p b v, observed p b = some v ↔ ((p, b), states p, v) ∈ t) →
    (Compatible (fun p => choices p (states p)) observed ↔
      ∀ row ∈ t, G.Adj row.2.1.2 row.2.2) := by
  intro next t availability hNB hState hObserved
  have hEdges := path_edge_constraints_iff choices reference ref slots initial
    hIncoming availability hNB
  change (∀ row ∈ t, G.Adj row.2.1.2 row.2.2) ↔
    (∀ row ∈ t, row.2.2 ∈ Set.range (choices row.1.1 row.2.1)) at hEdges
  rw [hEdges]
  constructor
  · intro h row hrow
    obtain ⟨⟨p, b⟩,state,y⟩ := row
    have hs : state = states p := hState _ hrow
    subst state
    exact h.1 p b y ((hObserved p b y).mpr hrow)
  · intro h
    constructor
    · intro p b v hv
      exact h ((p, b), states p, v) ((hObserved p b v).mp hv)
    · intro p v hfalse htrue
      have hf := value_of_row reference next ref slots initial ((p, false), states p, v)
        ((hObserved p false v).mp hfalse)
      have ht := value_of_row reference next ref slots initial ((p, true), states p, v)
        ((hObserved p true v).mp htrue)
      have he : ref p false = ref p true :=
        href p (states p) (hf.symm.trans ht)
      exact (by decide : false ≠ true) ((ref p).injective he)


/-- The posterior over graph worlds after an actual nonbacktracking disclosure. -/
theorem graph_path_posterior [Fintype P] [DecidableEq P]
    (π : PMF W) (graph : W → SimpleGraph V)
    (choices : W → P → (V × V) → Bool → V)
    (hPair : ∀ w p state, Function.Injective (choices w p state))
    (initial : V × V) (hIncoming : ∀ w, (graph w).Adj initial.1 initial.2)
    (slots : Schedule P) (ref : W × (P → Equiv.Perm Bool))
    (states : P → V × V) (observed : P → Bool → Option V)
    (seen : Finset P) (hSeen : ∀ p, p ∈ seen ↔ ∃ b v, observed p b = some v) :
    let next : P → (V × V) → V → (V × V) := fun _ s y => (s.2, y)
    let t := run (choices ref.1) next ref.2 slots initial
    (∀ w row, row ∈ t → (graph w).Adj row.2.1.1 row.2.1.2 →
      (row.2.2 ∈ Set.range (choices w row.1.1 row.2.1) ↔
        (graph w).Adj row.2.1.2 row.2.2 ∧ row.2.2 ≠ row.2.1.1)) →
    (∀ row ∈ t, row.2.2 ≠ row.2.1.1) →
    (∀ row ∈ t, row.2.1 = states row.1.1) →
    (∀ p b v, observed p b = some v ↔ ((p, b), states p, v) ∈ t) →
    let Ω := P → Equiv.Perm Bool
    let μ : PMF (W × Ω) := π.bind fun w => (uniformPmf Ω).map (Prod.mk w)
    let H : Set (W × Ω) := {x | run (choices x.1) next x.2 slots initial = t}
    let edges := t.map fun row => (row.2.1.2, row.2.2)
    let allowed : Set W := {w | ∀ e ∈ edges, (graph w).Adj e.1 e.2}
    μ.toOuterMeasure H ≠ 0 →
      ∀ B : Set W, μ.toOuterMeasure (H ∩ Prod.fst ⁻¹' B) / μ.toOuterMeasure H =
        π.toOuterMeasure (allowed ∩ B) / π.toOuterMeasure allowed := by
  intro next t hAvailable hNB hState hObserved Ω μ H edges allowed
  have hAllowed : allowed = {w | Compatible (fun p => choices w p (states p)) observed} := by
    ext w
    change (∀ e ∈ edges, (graph w).Adj e.1 e.2) ↔
      Compatible (fun p => choices w p (states p)) observed
    simp only [edges, List.forall_mem_map]
    exact (path_compatibility_iff_edges (choices w) (choices ref.1)
      (hPair ref.1) ref.2 slots initial (hIncoming w) states observed (hAvailable w)
      hNB hState hObserved).symm
  rw [hAllowed]
  exact state_dependent_posterior π choices next initial slots ref states observed seen hSeen
    hState hObserved (fun w p => hPair w p (states p))

end D5.S3.Combinatorics.Graph.Queries.ForwardPathPosterior
