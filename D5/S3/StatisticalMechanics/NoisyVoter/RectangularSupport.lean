/- GID: D5/S3/StatisticalMechanics/NoisyVoter/RectangularSupport
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/NoisyVoter/RectangularSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact graph-ball rectangles support the native joint opinion and source history. -/

import D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! # The deterministic support rectangle of the native voter history -/

open MeasureTheory ProbabilityTheory

namespace D5.S3.StatisticalMechanics.NoisyVoter.RectangularSupport

open RepetitionVarianceLinear AncestralSources FiniteCausalInputs

variable {V Ω : Type} {G : SimpleGraph V} [G.LocallyFinite]

/-- A finite enumeration of the closed radius-N graph ball, identified below using connectivity. -/
noncomputable def K (G : SimpleGraph V) [G.LocallyFinite] (u : V) : ℕ → Finset V
  | 0 => {u}
  | N+1 => by
      classical
      exact {u} ∪ (G.neighborFinset u).biUnion (fun v => K G v N)

/-- Exactly the initial labels on K_N and fresh labels at times 1 through N on K_N. -/
noncomputable def L (G : SimpleGraph V) [G.LocallyFinite] (u : V) (N : ℕ) :
    Finset (Label V) := by
  classical
  exact (K G u N).image Sum.inl ∪ (Finset.range N).biUnion
    (fun n => (K G u N).image (fun v => Sum.inr (⟨n+1, Nat.succ_pos n⟩, v)))

/-- The entire original rectangle, including all three auxiliary coordinate kinds. -/
noncomputable def rectangle (G : SimpleGraph V) [G.LocallyFinite] (u : V) (N : ℕ) :
    Finset (Coord V) := by
  classical
  exact (K G u N).image Coord.initial ∪ (Finset.Icc 1 N).biUnion
    (fun n => (K G u N).biUnion (fun v => {.fresh n v, .refresh n v, .choice n v}))

abbrev RectangleState (G : SimpleGraph V) [G.LocallyFinite] (u : V) (N : ℕ) :=
  (c : {c // c ∈ rectangle G u N}) → Value G c.val

def restrictRectangle (x : (c : Coord V) → Ω → Value G c) (u : V) (N : ℕ) (ω : Ω) :
    RectangleState G u N := fun c => x c.val ω

private theorem K_spec (hG : G.Connected) :
    ∀ N u v, v ∈ K G u N ↔ G.dist u v ≤ N := by
  classical
  intro N
  induction N with
  | zero =>
      intro u v
      simp only [K, Finset.mem_singleton, Nat.le_zero]
      exact eq_comm.trans hG.dist_eq_zero_iff.symm
  | succ N ih =>
      intro u v
      simp only [K, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
      constructor
      · rintro (rfl | ⟨w, hw, hv⟩)
        · simp
        · have hd := hG.dist_triangle (u := u) (v := w) (w := v)
          have he : G.dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr
            (by simpa only [SimpleGraph.mem_neighborFinset] using hw)
          rw [he] at hd
          have := (ih w v).mp hv
          omega
      · intro hv
        obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
        cases p with
        | nil => exact Or.inl rfl
        | cons huw p =>
            right
            refine ⟨_, by simpa only [SimpleGraph.mem_neighborFinset] using huw,
              (ih _ _).mpr ?_⟩
            have hd := G.dist_le p
            simp only [SimpleGraph.Walk.length_cons] at hp
            omega

theorem vertices_countable (hG : G.Connected) (u : V) : Countable V := by
  have hc := Set.countable_iUnion (fun N => (K G u N).countable_toSet)
  have he : (⋃ N, (↑(K G u N) : Set V)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    exact Set.mem_iUnion.mpr ⟨G.dist u v, (K_spec hG _ _ _).mpr le_rfl⟩
  rw [he] at hc
  exact Set.countable_univ_iff.mp hc

private theorem L_spec (u : V) (N : ℕ) (l : Label V) :
    l ∈ L G u N ↔
      match l with
      | .inl v => v ∈ K G u N
      | .inr p => p.1.val ≤ N ∧ p.2 ∈ K G u N := by
  classical
  cases l with
  | inl v => simp [L]
  | inr p =>
      rcases p with ⟨n, v⟩
      simp only [L, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
        Finset.mem_range]
      constructor
      · rintro (⟨w, hw, he⟩ | ⟨k, hk, w, hw, he⟩)
        · cases he
        · have he' := Sum.inr.inj he
          have ht := congrArg (fun p : ℕ+ × V => p.1.val) he'
          have hv := congrArg Prod.snd he'
          dsimp at hv
          exact ⟨by dsimp at ht; omega, hv ▸ hw⟩
      · rintro ⟨hn, hv⟩
        right
        refine ⟨n.val-1, by have := n.pos; omega, v, hv, ?_⟩
        congr 1
        apply Prod.ext
        · apply Subtype.ext
          have := n.pos
          change n.val - 1 + 1 = n.val
          omega
        · rfl

private theorem rectangle_positive (u : V) (N : ℕ) :
    ∀ c ∈ rectangle G u N, positive c := by
  classical
  intro c hc
  simp only [rectangle, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with ⟨v, _, rfl⟩ | ⟨n, hn, v, _, (rfl | rfl | rfl)⟩
  · trivial
  all_goals exact hn.1

private theorem inputs_subset_rectangle (hG : G.Connected) (u : V) (N : ℕ) :
    ∀ n v, G.dist u v + n ≤ N → inputs (G := G) n v ⊆ rectangle G u N := by
  classical
  intro n
  induction n with
  | zero =>
      intro v hv c hc
      have hc' : c = .initial v := by simpa [inputs] using hc
      subst c
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨v, (K_spec hG _ _ _).mpr (by omega), rfl⟩)
  | succ n ih =>
      intro v hv c hc
      have hvertex := (K_spec hG N u v).mpr (show G.dist u v ≤ N by omega)
      have htime : n+1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have local_mem : ∀ c ∈ ({.fresh (n+1) v, .refresh (n+1) v,
          .choice (n+1) v} : Finset (Coord V)), c ∈ rectangle G u N := by
        intro c hc
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨n+1, htime,
          Finset.mem_biUnion.mpr ⟨v, hvertex, hc⟩⟩)
      simp only [inputs, Finset.mem_union, Finset.mem_biUnion] at hc
      rcases hc with hc | ⟨w, hw, hc⟩
      · exact local_mem c hc
      · have hadj := (show G.Adj _ _ from by simpa only [SimpleGraph.mem_neighborFinset] using hw)
        have hd := hG.dist_triangle (u := u) (v := v) (w := w)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hd
        exact ih w (by omega) hc

private theorem source_in_L (hG : G.Connected)
    (x : (c : Coord V) → Ω → Value G c) (u : V) (N : ℕ) :
    ∀ n v, G.dist u v + n ≤ N → ∀ ω, source x n v ω ∈ L G u N := by
  intro n
  induction n with
  | zero =>
      intro v hv ω
      exact (L_spec u N _).mpr ((K_spec hG _ _ _).mpr (by simpa using hv))
  | succ n ih =>
      intro v hv ω
      simp only [source]
      split_ifs
      · apply (L_spec u N _).mpr
        change n+1 ≤ N ∧ v ∈ K G u N
        exact ⟨by omega, (K_spec hG _ _ _).mpr (by omega)⟩
      · have hadj := (x (.choice (n+1) v) ω).property
        have hd := hG.dist_triangle (u := u) (v := v)
          (w := (x (.choice (n+1) v) ω).val)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hd
        exact ih _ (by omega) ω

/-- The exact displayed graph ball and disjoint label rectangle support a finite
measurable reconstruction of all native opinion/source observations, including N=0.
No probability or independence premise is needed for this pathwise prerequisite. -/
theorem rectangular_history_support (hG : G.Connected)
    (hNbr : ∀ v, ∃ w, G.Adj v w) (u : V) (N : ℕ) :
    (∀ v, v ∈ K G u N ↔ G.dist u v ≤ N) ∧ Countable V ∧
    (∀ v, Sum.inl v ∈ L G u N ↔ v ∈ K G u N) ∧
    (∀ (n : ℕ+) v, Sum.inr (n, v) ∈ L G u N ↔ n.val ≤ N ∧ v ∈ K G u N) ∧
    (∀ c ∈ rectangle G u N, positive c) ∧
    ∃ f : RectangleState G u N → Fin (N+1) → Bool × Label V,
      Measurable f ∧
      ∀ (x : (c : Coord V) → Ω → Value G c) (ω : Ω),
        history x u N ω = f (restrictRectangle x u N ω) ∧
        ∀ s : Fin (N+1), source x s.val u ω ∈ L G u N := by
  classical
  let base : (c : Coord V) → Value G c := fun c =>
    match c with
    | .initial _ | .fresh _ _ | .refresh _ _ => false
    | .choice _ v => ⟨(hNbr v).choose, (hNbr v).choose_spec⟩
  have hsub : historyInputs (G := G) u N ⊆ rectangle G u N := by
    intro c hc
    obtain ⟨n, hn, hc⟩ := Finset.mem_biUnion.mp hc
    exact inputs_subset_rectangle hG u N n u (by
      have := Finset.mem_range.mp hn
      simp only [SimpleGraph.dist_self, zero_add]
      omega) hc
  let restriction (z : RectangleState G u N) : InputState (G := G) u N :=
    fun c => z ⟨c.val, hsub c.property⟩
  let f := decode base u N ∘ restriction
  refine ⟨K_spec hG N u, vertices_countable hG u,
    (fun v => L_spec u N (.inl v)), (fun n v => L_spec u N (.inr (n, v))),
    rectangle_positive u N, f, measurable_of_finite _, ?_⟩
  intro x ω
  constructor
  · exact (finite_history_factorization base u N).2 x ω
  · intro s
    exact source_in_L hG x u N s.val u (by
      simp only [SimpleGraph.dist_self, zero_add]
      omega) ω

end D5.S3.StatisticalMechanics.NoisyVoter.RectangularSupport
