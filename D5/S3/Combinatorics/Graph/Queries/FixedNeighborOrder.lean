/- GID: D5/S3/Combinatorics/Graph/Queries/FixedNeighborOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/FixedNeighborOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transcript likelihood under independently chosen persistent neighbor orders. -/

import D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory
import D5.S0.Diagonal.Probability.EquivariantEscape
import Mathlib.Data.Fintype.Perm

/-! Every vertex receives a uniform local neighbor order once. A transcript
fixes the local table values at its distinct queried vertices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder

open D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf uniformPmf_toOuterMeasure_apply)
open scoped ENNReal BigOperators

section UniformTable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (F : V → Type*) [∀ v, Fintype (F v)] [∀ v, Nonempty (F v)]

theorem uniform_coordinate_cylinder (s : Finset V) (a : ∀ v : s, F v) :
    (uniformPmf (∀ v, F v)).toOuterMeasure
        {f : ∀ v, F v | ∀ v : s, f v = a v} =
      ((∏ v ∈ s, Fintype.card (F v) : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  let A := ∀ v : s, F v
  let B := ∀ v : {v // v ∉ s}, F v
  let e : (∀ v, F v) ≃ A × B := Equiv.piEquivPiSubtypeProd (· ∈ s) F
  let E : Set (∀ v, F v) := {f | ∀ v : s, f v = a v}
  let eSub : E ≃ B :=
    { toFun := fun f => (e f.1).2
      invFun := fun g => ⟨e.symm (a, g), fun v => by
        have h := congrArg Prod.fst (e.apply_symm_apply (a,g))
        exact congrFun h v⟩
      left_inv := fun f => by
        apply Subtype.ext
        apply e.injective
        rw [e.apply_symm_apply]
        exact Prod.ext (funext f.2).symm rfl
      right_inv := fun g => congrArg Prod.snd (e.apply_symm_apply (a,g)) }
  have hEvent : Fintype.card E = Fintype.card B := Fintype.card_congr eSub
  have hWhole : Fintype.card (∀ v, F v) = Fintype.card A * Fintype.card B := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hA : Fintype.card A = ∏ v ∈ s, Fintype.card (F v) := by
    rw [Fintype.card_pi]
    exact Finset.prod_attach s (fun v => Fintype.card (F v))
  have hBzero : (Fintype.card B : ℝ≥0∞) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  change (uniformPmf (∀ v, F v)).toOuterMeasure E = _
  rw [uniformPmf_toOuterMeasure_apply, hEvent, hWhole, Nat.cast_mul, ← hA, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_left_comm, ENNReal.mul_inv_cancel hBzero (ENNReal.natCast_ne_top _), mul_one]



variable {Y : V → Type*}

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (F v)] [∀ v, Nonempty (F v)] in
private theorem same_history_iff (read : ∀ v, F v → Y v)
    (p : PassiveProtocol V Y) (f g : ∀ v, F v) :
    runPassiveProtocol (fun v h => read v (h v)) p f =
      runPassiveProtocol (fun v h => read v (h v)) p g ↔
      ∀ entry ∈ runPassiveProtocol (fun v h => read v (h v)) p g,
        read entry.1 (f entry.1) = entry.2 := by
  induction p with
  | stop => simp [runPassiveProtocol]
  | query v next ih =>
      by_cases he : read v (f v) = read v (g v)
      · simp only [runPassiveProtocol, he, List.cons.injEq, true_and, List.mem_cons]
        rw [ih (read v (g v))]
        constructor
        · rintro h entry (rfl | htail)
          · exact he
          · exact h entry htail
        · intro h entry ht
          exact h entry (Or.inr ht)
      · constructor
        · intro h
          exfalso
          apply he
          have hfirst := (List.cons.inj (show
            (⟨v, read v (f v)⟩ : Sigma Y) :: _ = ⟨v, read v (g v)⟩ :: _ from h)).1
          exact eq_of_heq (Sigma.mk.inj_iff.mp hfirst).2
        · intro h
          apply (he (h ⟨v, read v (g v)⟩ (by simp [runPassiveProtocol]))).elim

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (F v)] [∀ v, Nonempty (F v)] in
private theorem recorded_answer (read : ∀ v, F v → Y v)
    (p : PassiveProtocol V Y) (g : ∀ v, F v) (entry : Sigma Y)
    (he : entry ∈ runPassiveProtocol (fun v h => read v (h v)) p g) :
    entry.2 = read entry.1 (g entry.1) := by
  induction p with
  | stop => simp [runPassiveProtocol] at he
  | query v next ih =>
      rw [runPassiveProtocol, List.mem_cons] at he
      rcases he with rfl | htail
      · rfl
      · exact ih _ htail

/-- In a fixed table of independent uniform answers, each queried label is charged once. -/
private theorem uniform_adaptive_history_mass (read : ∀ v, F v → Y v)
    (hr : ∀ v, Function.Injective (read v)) (p : PassiveProtocol V Y) (g : ∀ v, F v) :
    let t := runPassiveProtocol (fun v h => read v (h v)) p g
    let s := (t.map Sigma.fst).toFinset
    (uniformPmf (∀ v, F v)).toOuterMeasure
        {f : ∀ v, F v | runPassiveProtocol (fun v h => read v (h v)) p f = t} =
      ((∏ v ∈ s, Fintype.card (F v) : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  dsimp only
  let t := runPassiveProtocol (fun v h => read v (h v)) p g
  let s := (t.map Sigma.fst).toFinset
  have hEvent :
      {f : ∀ v, F v | runPassiveProtocol (fun v h => read v (h v)) p f = t} =
      {f | ∀ v : s, f v = g v} := by
    ext f
    change runPassiveProtocol (fun v h => read v (h v)) p f = t ↔ ∀ v : s, f v = g v
    rw [same_history_iff F read p f g]
    constructor
    · intro h v
      have hv : v.1 ∈ t.map Sigma.fst := List.mem_toFinset.mp v.2
      obtain ⟨entry, he, hv⟩ := List.mem_map.mp hv
      change entry.1 = v.1 at hv
      have hEntry := hr entry.1 ((h entry he).trans (recorded_answer F read p g entry he))
      change f entry.1 = g entry.1 at hEntry
      rw [hv] at hEntry
      exact hEntry
    · intro h entry he
      have hm : entry.1 ∈ s := List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, he, rfl⟩)
      exact (congrArg (read entry.1) (h ⟨entry.1, hm⟩)).trans
        (recorded_answer F read p g entry he).symm
  rw [hEvent]
  exact uniform_coordinate_cylinder F s (fun v => g v)


end UniformTable

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NeighborOrder (G : SimpleGraph V) (d : V → ℕ) (v : V) :=
  Fin (d v) ≃ G.neighborSet v

abbrev NeighborOrderTable (G : SimpleGraph V) (d : V → ℕ) := ∀ v, NeighborOrder G d v
abbrev OrderedResponse (d : V → ℕ) := fun v => Fin (d v) → V
abbrev OrderedProtocol (d : V → ℕ) := PassiveProtocol V (OrderedResponse d)

private def orderRead (G : SimpleGraph V) (d : V → ℕ) (v : V)
    (e : NeighborOrder G d v) : OrderedResponse d v :=
  fun i => (e i).1

def runWithOrders (G : SimpleGraph V) (d : V → ℕ) (p : OrderedProtocol d) (f : NeighborOrderTable G d) :=
  runPassiveProtocol (fun v h => orderRead G d v (h v)) p f

def reportedNeighborSets {d : V → ℕ} (t : List (Sigma (OrderedResponse d))) : History V :=
  t.map (fun entry => ⟨entry.1, Set.range entry.2⟩)

private theorem orderRead_range (G : SimpleGraph V) (d : V → ℕ) (v : V)
    (e : NeighborOrder G d v) : Set.range (orderRead G d v e) = G.neighborSet v := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).2
  · intro hw
    obtain ⟨i, hi⟩ := e.surjective ⟨w, hw⟩
    exact ⟨i, congrArg Subtype.val hi⟩

private theorem orderRead_injective (G : SimpleGraph V) (d : V → ℕ) (v : V) :
    Function.Injective (orderRead G d v) := by
  intro e f h
  ext i
  exact congrFun h i

private theorem run_encode {d : V → ℕ} (G : SimpleGraph V) (p : OrderedProtocol d) (f : NeighborOrderTable G d) :
    runWithOrders G d p f =
      runPassiveProtocol (fun v (g : ∀ v, OrderedResponse d v) => g v) p
        (fun v => orderRead G d v (f v)) := by
  induction p with
  | stop => rfl
  | query v next ih =>
      simp only [runWithOrders, runPassiveProtocol]
      exact congrArg (List.cons ⟨v, orderRead G d v (f v)⟩) (ih (orderRead G d v (f v)))

private theorem entry_range {G : SimpleGraph V} {d : V → ℕ} {p : OrderedProtocol d} {f : NeighborOrderTable G d}
    (entry : Sigma (OrderedResponse d)) (he : entry ∈ runWithOrders G d p f) :
    Set.range entry.2 = G.neighborSet entry.1 := by
  change entry ∈ runPassiveProtocol (fun v h => orderRead G d v (h v)) p f at he
  rw [recorded_answer (NeighborOrder G d) (orderRead G d) p f entry he]
  exact orderRead_range G d entry.1 (f entry.1)

private theorem report_sound (G : SimpleGraph V) (d : V → ℕ) (p : OrderedProtocol d)
    (f : NeighborOrderTable G d) : revealedEdges (reportedNeighborSets (runWithOrders G d p f)) ≤ G := by
  intro x y hxy
  rw [revealedEdges, SimpleGraph.fromRel_adj] at hxy
  rcases hxy.2 with ⟨seen, hs, rfl, hy⟩ | ⟨seen, hs, rfl, hx⟩
  · unfold reportedNeighborSets at hs
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hs
    change y ∈ Set.range entry.2 at hy
    rwa [entry_range entry he] at hy
  · unfold reportedNeighborSets at hs
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hs
    change x ∈ Set.range entry.2 at hx
    rw [entry_range entry he] at hx
    exact G.adj_symm hx

private theorem report_extends_replay {d : V → ℕ} (G H : SimpleGraph V) (p : OrderedProtocol d)
    (f : NeighborOrderTable G d) (g : NeighborOrderTable H d) :
    (∃ t : NeighborOrderTable G d, runWithOrders G d p t = runWithOrders H d p g) ↔
      revealedEdges (reportedNeighborSets (runWithOrders H d p g)) ≤ G := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    rw [← ht]
    exact report_sound G d p t
  · intro hext
    let s := ((runWithOrders H d p g).map Sigma.fst).toFinset
    have subset (v : V) (hv : v ∈ s) : H.neighborSet v ⊆ G.neighborSet v := by
      obtain ⟨entry, he, hve⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      subst v
      intro w hw
      apply hext
      rw [revealedEdges, SimpleGraph.fromRel_adj]
      refine ⟨H.ne_of_adj hw, Or.inl
        ⟨⟨entry.1, Set.range entry.2⟩, ?_, rfl, ?_⟩⟩
      · unfold reportedNeighborSets
        exact List.mem_map.mpr ⟨entry, he, rfl⟩
      rwa [entry_range entry he]
    have card_eq (v : V) : (G.neighborSet v).ncard = (H.neighborSet v).ncard := by
      change Nat.card (G.neighborSet v) = Nat.card (H.neighborSet v)
      exact (Nat.card_congr (f v).symm).trans (Nat.card_congr (g v))
    have same (v : V) (hv : v ∈ s) : H.neighborSet v = G.neighborSet v :=
      Set.eq_of_subset_of_ncard_le (subset v hv) (card_eq v).le
    let t : NeighborOrderTable G d := fun v => if hv : v ∈ s then
      (g v).trans (Set.equivOfEq (same v hv)) else f v
    refine ⟨t, ?_⟩
    rw [run_encode, run_encode]
    rw [same_history_iff (OrderedResponse d) (fun _ y => y)]
    intro entry he
    have he' : entry ∈ runWithOrders H d p g := (run_encode H p g).symm ▸ he
    have hv : entry.1 ∈ s :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, he', rfl⟩)
    change orderRead G d entry.1 (t entry.1) = entry.2
    have hentry := recorded_answer (NeighborOrder H d) (orderRead H d) p g entry he'
    rw [hentry]
    funext i
    simp [orderRead, t, hv]


/-- Likelihood of a complete ordered transcript when each vertex order is sampled once. -/
theorem fixed_neighbor_order_likelihood (G H : SimpleGraph V) (d : V → ℕ)
    (p : OrderedProtocol d) (g : NeighborOrderTable H d) (μ : PMF (NeighborOrderTable G d))
    (hμ : ∀ f, μ f = (Nat.card (NeighborOrderTable G d) : ℝ≥0∞)⁻¹) :
    let trace := runWithOrders H d p g
    let seen := (trace.map Sigma.fst).toFinset
    let report := revealedEdges (reportedNeighborSets trace)
    μ.toOuterMeasure {t | runWithOrders G d p t = trace} =
      if report ≤ G then ((∏ v ∈ seen, (d v).factorial : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  classical
  dsimp only
  obtain ⟨f, _⟩ := μ.support_nonempty
  let (v : V) : Fintype (G.neighborSet v) := Fintype.ofFinite _
  let (v : V) : Fintype (NeighborOrder G d v) := Fintype.ofFinite _
  let (v : V) : Nonempty (NeighborOrder G d v) := ⟨f v⟩
  have uniform : μ = uniformPmf (NeighborOrderTable G d) := by
    ext t
    rw [hμ, Nat.card_eq_fintype_card]
    rfl
  by_cases compatible : revealedEdges (reportedNeighborSets (runWithOrders H d p g)) ≤ G
  · rw [ite_eq_left compatible, uniform]
    obtain ⟨t, ht⟩ := (report_extends_replay G H p f g).mpr compatible
    have hc (v : V) : Fintype.card (NeighborOrder G d v) = (d v).factorial := by
      let e : Equiv.Perm (Fin (d v)) ≃ NeighborOrder G d v := Equiv.equivCongr (Equiv.refl _) (f v)
      rw [← Nat.card_eq_fintype_card, Nat.card_congr e.symm, Nat.card_eq_fintype_card,
        Fintype.card_perm, Fintype.card_fin]
    have result := uniform_adaptive_history_mass (NeighborOrder G d) (orderRead G d)
      (orderRead_injective G d) p t
    dsimp only at result
    change (uniformPmf (NeighborOrderTable G d)).toOuterMeasure
      {z | runWithOrders G d p z = runWithOrders G d p t} =
      (((∏ v ∈ ((runWithOrders G d p t).map Sigma.fst).toFinset,
        Fintype.card (NeighborOrder G d v) : ℕ) : ℝ≥0∞))⁻¹ at result
    simpa only [ht, hc] using result
  · rw [ite_eq_right compatible]
    have hE : {t | runWithOrders G d p t = runWithOrders H d p g} = (∅ : Set (NeighborOrderTable G d)) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun ht => compatible ((report_extends_replay G H p f g).mp ⟨t, ht⟩)
    simp [hE, PMF.toOuterMeasure_apply]


end D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder
