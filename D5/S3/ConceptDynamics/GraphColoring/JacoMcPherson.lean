/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoMcPherson
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree, lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount]
   utility: none
   digest: The McPherson number of the finite Jaco graph J_n(1) is b_n - 1, so it is nonrepetitive exactly when b_n is. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
import D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount

/-! The McPherson number of the finite linear Jaco graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoMcPherson

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount (out_step)

/-
proof_shape:
  explode, run, mcpherson: definition
  run_adj: content (consumer: run_eq_top_iff)
  run_eq_top_iff: content (consumers: mcpherson_jaco, result)
  bo_mono: bind-only (consumer: clique_bound)
  clique_bound: content (consumer: mcpherson_jaco)
  mcpherson_jaco: content (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beatty_threshold, beatty_bounds,
    endpoint_eq_beatty (statement_id
    sha256:15f9f8627a73d9d28232ecd5a1deb1d41054ab6114f152475628df4fd9def028)
  D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.out_step (statement_id
    sha256:74ed8276649f9d55a661f745fd37f2ae64e7da5a7f055108f907540926bcb3b4)
  D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.jaco (statement_id
    sha256:4b9772e09b0b920432abf047ae184610f43166f07e49ae9c6e49b79e6cf2092a)
escape_witness: run_eq_top_iff (explosions complete the graph exactly when the non-exploding
  vertices form a clique) and clique_bound (every clique of J_n(1) has at most n + 1 - b_n
  vertices, from the endpoint threshold n <= R_i iff b_n <= i), which together give
  Upsilon(J_n(1)) = b_n - 1.
admission_basis: escape-witness
-/

variable {V : Type*}

/-- One vertex explosion: the exploding vertex `w` is joined to every other vertex (an arc to
each vertex not yet joined to it; only the underlying graph is recorded). -/
def explode (H : SimpleGraph V) (w : V) : SimpleGraph V :=
  H ⊔ SimpleGraph.fromRel (fun u _ => u = w)

/-- The McPherson recursion: the vertices of `L` explode in order. -/
def run (G : SimpleGraph V) (L : List V) : SimpleGraph V := L.foldl explode G

/-- The McPherson number `Υ(G)`: the least number of explosions after which the underlying
graph is complete. -/
noncomputable def mcpherson (G : SimpleGraph V) : ℕ :=
  sInf {ℓ | ∃ L : List V, L.length = ℓ ∧ run G L = ⊤}

/-- After exploding `L`, two distinct vertices are adjacent exactly when they were adjacent in
`G` or one of them exploded. -/
theorem run_adj (G : SimpleGraph V) (L : List V) (a b : V) :
    (run G L).Adj a b ↔ G.Adj a b ∨ (a ≠ b ∧ (a ∈ L ∨ b ∈ L)) := by
  induction L generalizing G with
  | nil => simp only [run, List.foldl_nil, List.not_mem_nil, or_self, and_false, or_false]
  | cons w L ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [explode, SimpleGraph.sup_adj, SimpleGraph.fromRel_adj, List.mem_cons]
    constructor
    · rintro ((h | ⟨hab, h | h⟩) | ⟨hab, h | h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hab, Or.inl (Or.inl h)⟩
      · exact Or.inr ⟨hab, Or.inr (Or.inl h)⟩
      · exact Or.inr ⟨hab, Or.inl (Or.inr h)⟩
      · exact Or.inr ⟨hab, Or.inr (Or.inr h)⟩
    · rintro (h | ⟨hab, (h | h) | (h | h)⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨hab, Or.inl h⟩)
      · exact Or.inr ⟨hab, Or.inl h⟩
      · exact Or.inl (Or.inr ⟨hab, Or.inr h⟩)
      · exact Or.inr ⟨hab, Or.inr h⟩

/-- The explosions of `L` complete `G` exactly when the vertices that do not explode form a
clique of `G`; in particular the order of the explosions does not matter. -/
theorem run_eq_top_iff (G : SimpleGraph V) (L : List V) :
    run G L = ⊤ ↔ G.IsClique {v | v ∉ L} := by
  constructor
  · intro h a ha b hb hab
    have := (run_adj G L a b).mp (by rw [h]; exact hab)
    rcases this with h' | ⟨_, h' | h'⟩
    · exact h'
    · exact absurd h' ha
    · exact absurd h' hb
  · intro h
    ext a b
    simp only [SimpleGraph.top_adj, run_adj]
    constructor
    · rintro (h' | ⟨hab, _⟩)
      · exact h'.ne
      · exact hab
    · intro hab
      by_cases ha : a ∈ L
      · exact Or.inr ⟨hab, Or.inl ha⟩
      by_cases hb : b ∈ L
      · exact Or.inr ⟨hab, Or.inr hb⟩
      exact Or.inl (h ha hb hab)

private theorem bo_mono {a b : ℕ} (h : a ≤ b) : beattyOut a ≤ beattyOut b := by
  have hm : Monotone beattyOut := monotone_nat_of_le_succ fun k => by
    rcases out_step k with h | h <;> omega
  exact hm h

/-- Every clique of `J_n(1)` has at most `n + 1 - b_n` vertices. -/
private theorem clique_bound (n : ℕ) (hn : 1 ≤ n) (K : Finset (Vertex n))
    (hK : (jaco n).IsClique (K : Set (Vertex n))) : K.card + beattyOut n ≤ n + 1 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, zero_add]
    have := (beatty_bounds n hn).2
    omega
  have hbn := beatty_bounds n hn
  set S := K.image Subtype.val with hS
  have hcard : S.card = K.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hSne : S.Nonempty := hne.image _
  set m := S.min' hSne with hm
  have hmS : m ∈ S := S.min'_mem hSne
  obtain ⟨vm, hvmK, hvm⟩ := Finset.mem_image.mp hmS
  have hm1 : 1 ≤ m := by rw [← hvm]; exact (Finset.mem_Icc.mp vm.2).1
  have hsub : S ⊆ Finset.Icc m (min n (m + beattyOut m)) := by
    intro x hx
    obtain ⟨v, hvK, rfl⟩ := Finset.mem_image.mp hx
    have hmin : m ≤ v.1 := S.min'_le _ hx
    have hvn : v.1 ≤ n := (Finset.mem_Icc.mp v.2).2
    rw [Finset.mem_Icc]
    refine ⟨hmin, le_min hvn ?_⟩
    by_cases hv : v = vm
    · subst hv; rw [hvm]; omega
    · have hadj := hK hvmK hvK (Ne.symm hv)
      change Adj vm.1 v.1 at hadj
      rw [hvm] at hadj
      rcases hadj with ⟨_, h⟩ | ⟨h, _⟩
      · rw [endpoint_eq_beatty] at h; exact h
      · omega
  have hle := Finset.card_le_card hsub
  rw [Nat.card_Icc, hcard] at hle
  by_cases hmb : beattyOut n ≤ m
  · have := min_le_left n (m + beattyOut m)
    omega
  · -- m < b_n, so b_m ≤ b_(b_n - 1) ≤ n - b_n
    have hthr := (beatty_threshold n (beattyOut n - 1)).not.mpr (by omega)
    have hmono : beattyOut m ≤ beattyOut (beattyOut n - 1) := bo_mono (by omega)
    have := min_le_right n (m + beattyOut m)
    omega

/-- `Υ(J_n(1)) = b_n - 1` for every `n`. -/
private theorem mcpherson_jaco (n : ℕ) : mcpherson (jaco n) = beattyOut n - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `J_0` has no vertices: the empty explosion list completes it
    have hb0 : beattyOut 0 = 0 := by
      have := (beatty_threshold 0 0).mp (by omega)
      omega
    rw [hb0]
    apply Nat.eq_zero_of_le_zero
    apply Nat.sInf_le
    refine ⟨[], rfl, ?_⟩
    rw [run_eq_top_iff]
    intro a
    exact absurd a.2 (by simp)
  have hbn := beatty_bounds n hn
  -- the explosions of the labels below `b_n`
  let L : List (Vertex n) := (Finset.univ.filter fun v : Vertex n => v.1 < beattyOut n).toList
  have hLmem : ∀ v : Vertex n, v ∈ L ↔ v.1 < beattyOut n := by
    intro v; simp [L]
  have hLlen : L.length = beattyOut n - 1 := by
    rw [Finset.length_toList]
    have : (Finset.univ.filter fun v : Vertex n => v.1 < beattyOut n).map
        (Function.Embedding.subtype _) = Finset.Ico 1 (beattyOut n) := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coe_subtype, Finset.mem_Ico]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨(Finset.mem_Icc.mp v.2).1, hv⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, Finset.mem_Icc.mpr ⟨h1, by omega⟩⟩, h2, rfl⟩
    rw [← Finset.card_map, this, Nat.card_Ico]
  have hLtop : run (jaco n) L = ⊤ := by
    rw [run_eq_top_iff]
    intro a ha b hb hab
    simp only [Set.mem_ofPred_eq, hLmem, not_lt] at ha hb
    have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    have ha' := (Finset.mem_Icc.mp a.2).2
    have hb' := (Finset.mem_Icc.mp b.2).2
    have hta := (beatty_threshold n a.1).mpr ha
    have htb := (beatty_threshold n b.1).mpr hb
    change Adj a.1 b.1
    rcases lt_or_gt_of_ne hab' with h | h
    · left; rw [endpoint_eq_beatty]; omega
    · right; rw [endpoint_eq_beatty]; omega
  apply le_antisymm
  · exact Nat.sInf_le ⟨L, hLlen, hLtop⟩
  · unfold mcpherson
    refine le_csInf ⟨beattyOut n - 1, L, hLlen, hLtop⟩ ?_
    rintro ℓ ⟨M, rfl, hM⟩
    rw [run_eq_top_iff] at hM
    let K : Finset (Vertex n) := Finset.univ.filter fun v => v ∉ M
    have hK : (jaco n).IsClique (K : Set (Vertex n)) := by
      intro a ha b hb hab
      simp only [K, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      exact hM ha hb hab
    have hcb := clique_bound n hn K hK
    have hcard : (Finset.univ : Finset (Vertex n)).card = n := by simp
    have hsplit : M.toFinset.card + K.card = (Finset.univ : Finset (Vertex n)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext v; simp only [K, Finset.mem_union, List.mem_toFinset, Finset.mem_filter,
          Finset.mem_univ, true_and, iff_true]; tauto
      · rw [Finset.disjoint_left]; intro v hv
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
        exact List.mem_toFinset.mp hv
    have := List.toFinset_card_le M
    omega

/-- The McPherson number of `J_n(1)` is `Υ_n = b_n - 1` with `b_n = ⌊(n + 1)/φ⌋`, for every `n`;
in particular `Υ_n` is nonrepetitive (`Υ_(n-1) < Υ_n < Υ_(n+1)`) exactly when `b_n` is, for every
`n ≥ 2`. The explosions of a list complete a graph exactly when the non-exploding vertices form a
clique. -/
theorem result :
    (∀ (V : Type) (G : SimpleGraph V) (L : List V), run G L = ⊤ ↔ G.IsClique {v | v ∉ L}) ∧
    (∀ n, mcpherson (jaco n) = beattyOut n - 1) ∧
    (∀ n, 2 ≤ n →
      ((mcpherson (jaco (n - 1)) < mcpherson (jaco n) ∧
          mcpherson (jaco n) < mcpherson (jaco (n + 1))) ↔
        (beattyOut (n - 1) < beattyOut n ∧ beattyOut n < beattyOut (n + 1)))) := by
  refine ⟨fun _ G L => run_eq_top_iff G L, mcpherson_jaco, ?_⟩
  intro n hn
  rw [mcpherson_jaco, mcpherson_jaco, mcpherson_jaco]
  have h1 := (beatty_bounds (n - 1) (by omega)).1
  have h2 := (beatty_bounds n (by omega)).1
  have h3 := (beatty_bounds (n + 1) (by omega)).1
  omega

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoMcPherson
