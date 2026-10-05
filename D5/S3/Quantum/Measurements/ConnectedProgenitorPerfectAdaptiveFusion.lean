/- GID: D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Graph codes with connected progenitor graphs have perfect adaptive fusion strategies. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith

/-!
Graph codes and adaptive logical fusion.

A Pauli string is taken up to phase, one letter per qubit, each letter being its `(x, z)` bits:
`I = (false, false)`, `X = (true, false)`, `Z = (false, true)`, `Y = (true, true)`.
For a progenitor graph `G` with encoding vertex `e`, the stabilizers of the graph state are,
up to phase, the products of canonical generators `X_u ∏_{w ∈ N(u)} Z_w` over subsets `U`.
The logical operators of the code are the restrictions of these stabilizers to the physical
vertices; such an operator is non-trivial when the stabilizer is not the identity at `e`.

A physical fusion at a vertex either succeeds or fails; a failure measures both qubits in the
chosen failure axis. Fusion failures on a set `W` lead to a logical failure exactly when the
substrings of the realized axes on `W` contain a non-trivial logical operator. An adaptive
strategy attempts the physical vertices in a fixed order and chooses each failure axis from the
outcomes of the earlier attempts only. It is perfect when every outcome with at least one
successful fusion avoids a logical failure.
-/

namespace D5.S3.Quantum.Measurements.ConnectedProgenitorPerfectAdaptiveFusion

open SimpleGraph Finset

/-- A single-qubit Pauli letter up to phase, given by its `(x, z)` bits. -/
abbrev Pauli := Bool × Bool

/-- The identity letter. -/
def pauliI : Pauli := (false, false)

/-- The letter `X`. -/
def pauliX : Pauli := (true, false)

/-- The letter `Z`. -/
def pauliZ : Pauli := (false, true)

variable {V : Type}

/-- The letter at `w` of the product of the canonical generators over `U`, up to phase. -/
def genProduct [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (w : V) :
    Pauli :=
  (decide (w ∈ U), decide (Odd (U.filter (G.Adj w)).card))

/-- `P` is a non-trivial logical operator of the graph code with progenitor graph `G` and
encoding vertex `e`: it is the restriction to the physical vertices of a graph-state stabilizer
that is not the identity at `e`. -/
def IsNontrivialLogical [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : V)
    (P : V → Pauli) :
    Prop :=
  ∃ U : Finset V, (∀ w, w ≠ e → P w = genProduct G U w) ∧ genProduct G U e ≠ pauliI

/-- An adaptive fusion strategy: the physical vertices are attempted in increasing `rank`, and the
failure axis of a vertex depends only on the outcomes (`true` for a successful fusion) of the
physical vertices attempted before it. -/
structure AdaptiveStrategy (e : V) where
  /-- The attempt order. -/
  rank : V → ℤ
  rank_inj : ∀ a b, a ≠ e → b ≠ e → rank a = rank b → a = b
  /-- The failure axis of a vertex as a function of the outcomes. -/
  axis : V → (V → Bool) → Pauli
  axis_ne : ∀ w o, axis w o ≠ pauliI
  causal : ∀ w (o o' : V → Bool), (∀ u, u ≠ e → rank u < rank w → o u = o' u) →
    axis w o = axis w o'

/-- The outcome `o` leads to a logical failure: some non-trivial logical operator is, on every
failed vertex, the identity or the realized failure axis, and is the identity on every vertex
whose fusion succeeded. -/
def LogicalFailure [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : V)
    (S : AdaptiveStrategy e)
    (o : V → Bool) : Prop :=
  ∃ P : V → Pauli, IsNontrivialLogical G e P ∧
    ∀ w, w ≠ e → (o w = false → P w = pauliI ∨ P w = S.axis w o) ∧
      (o w = true → P w = pauliI)

/-- The graph code has a perfect adaptive fusion strategy: one successful physical fusion
always suffices for a successful logical fusion. -/
def HasPerfectAdaptiveStrategy [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : V) :
    Prop :=
  ∃ S : AdaptiveStrategy e, ∀ o : V → Bool, (∃ w, w ≠ e ∧ o w = true) →
    ¬ LogicalFailure G e S o

/-- The conjecture: every graph code whose progenitor graph is connected, with the encoding
vertex incident to an edge, has a perfect adaptive fusion strategy. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : V),
    G.Connected → (∃ w, G.Adj e w) → HasPerfectAdaptiveStrategy G e

section Construction

variable (G : SimpleGraph V) (e : V)

/-- Graph distance from the encoding vertex. -/
noncomputable def depth (w : V) : ℕ := G.dist e w

theorem depth_adj_le (hc : G.Connected) {a b : V} (h : G.Adj a b) :
    depth G e a ≤ depth G e b + 1 := by
  unfold depth
  calc G.dist e a ≤ G.dist e b + G.dist b a := hc.dist_triangle
    _ = G.dist e b + 1 := by rw [(dist_eq_one_iff_adj).2 h.symm]

theorem exists_parent (hc : G.Connected) {w : V} (hw : w ≠ e) :
    ∃ y, G.Adj w y ∧ depth G e y + 1 = depth G e w := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist w e
  cases p with
  | nil => exact absurd rfl hw
  | @cons _ y _ h q =>
    refine ⟨y, h, le_antisymm ?_ ?_⟩
    · have h1 : depth G e y ≤ q.length := by
        unfold depth; rw [dist_comm]; exact dist_le q
      have h2 : depth G e w = q.length + 1 := by
        unfold depth; rw [dist_comm, ← hp]; rfl
      omega
    · exact depth_adj_le G e hc h

open Classical in
/-- A neighbour one step closer to the encoding vertex. -/
noncomputable def parent (hc : G.Connected) (w : V) : V :=
  if hw : w = e then e else Classical.choose (exists_parent G e hc hw)

theorem parent_spec (hc : G.Connected) {w : V} (hw : w ≠ e) :
    G.Adj w (parent G e hc w) ∧ depth G e (parent G e hc w) + 1 = depth G e w := by
  unfold parent
  rw [dif_neg hw]
  exact Classical.choose_spec (exists_parent G e hc hw)

/-- `w` is an internal vertex of the chosen geodesic from `v` to the encoding vertex. -/
def OnPath (hc : G.Connected) (v w : V) : Prop :=
  ∃ k, 1 ≤ k ∧ k < depth G e v ∧ (parent G e hc)^[k] v = w

theorem depth_iterate (hc : G.Connected) (v : V) :
    ∀ k, k ≤ depth G e v → depth G e ((parent G e hc)^[k] v) = depth G e v - k
  | 0, _ => by simp
  | k + 1, hk => by
    have ih := depth_iterate hc v k (by omega)
    have hne : (parent G e hc)^[k] v ≠ e := by
      intro h
      rw [h] at ih
      have : depth G e e = 0 := by unfold depth; simp
      omega
    rw [Function.iterate_succ_apply']
    have := (parent_spec G e hc hne).2
    omega

/-- Vertices farther from the encoding vertex are attempted first. -/
noncomputable def rankOf [Fintype V] [DecidableEq V] (w : V) : ℤ :=
  -((depth G e w : ℤ) * Fintype.card V) + ((Fintype.equivFin V w : ℕ) : ℤ)

theorem rankOf_lt_of_depth_lt [Fintype V] [DecidableEq V] {a b : V}
    (h : depth G e b < depth G e a) :
    rankOf G e a < rankOf G e b := by
  unfold rankOf
  have ha := (Fintype.equivFin V a).isLt
  have hcard : (0 : ℤ) ≤ Fintype.card V := Int.natCast_nonneg _
  have hd : (depth G e b : ℤ) + 1 ≤ depth G e a := by exact_mod_cast h
  nlinarith

theorem rankOf_inj [Fintype V] [DecidableEq V] {a b : V} (h : rankOf G e a = rankOf G e b) :
    a = b := by
  rcases lt_trichotomy (depth G e a) (depth G e b) with hab | hab | hab
  · exact absurd h (rankOf_lt_of_depth_lt G e hab).ne'
  · have hidx : ((Fintype.equivFin V a : ℕ) : ℤ) = ((Fintype.equivFin V b : ℕ) : ℤ) := by
      unfold rankOf at h; rw [hab] at h; linarith
    exact (Fintype.equivFin V).injective (Fin.ext (by exact_mod_cast hidx))
  · exact absurd h (rankOf_lt_of_depth_lt G e hab).ne

/-- `v` is the first successful fusion among the vertices attempted before `w`. -/
def FirstSuccessBefore [Fintype V] [DecidableEq V] (o : V → Bool) (w v : V) : Prop :=
  v ≠ e ∧ o v = true ∧ rankOf G e v < rankOf G e w ∧
    ∀ u, u ≠ e → rankOf G e u < rankOf G e v → o u = false

open Classical in
/-- The failure axis: `X` on the internal vertices of the geodesic to the first success, once
that success has been observed, and `Z` otherwise. -/
noncomputable def axisOf [Fintype V] [DecidableEq V] (hc : G.Connected) (w : V) (o : V → Bool) :
    Pauli :=
  if ∃ v, FirstSuccessBefore G e o w v ∧ OnPath G e hc v w then pauliX else pauliZ

theorem axisOf_causal [Fintype V] [DecidableEq V] (hc : G.Connected) (w : V) (o o' : V → Bool)
    (h : ∀ u, u ≠ e → rankOf G e u < rankOf G e w → o u = o' u) :
    axisOf G e hc w o = axisOf G e hc w o' := by
  have key : (∃ v, FirstSuccessBefore G e o w v ∧ OnPath G e hc v w) ↔
      (∃ v, FirstSuccessBefore G e o' w v ∧ OnPath G e hc v w) := by
    constructor
    · rintro ⟨v, ⟨hv, hov, hlt, hfirst⟩, hp⟩
      refine ⟨v, ⟨hv, (h v hv hlt) ▸ hov, hlt, fun u hu hlu => ?_⟩, hp⟩
      rw [← h u hu (hlu.trans hlt)]; exact hfirst u hu hlu
    · rintro ⟨v, ⟨hv, hov, hlt, hfirst⟩, hp⟩
      refine ⟨v, ⟨hv, (h v hv hlt).symm ▸ hov, hlt, fun u hu hlu => ?_⟩, hp⟩
      rw [h u hu (hlu.trans hlt)]; exact hfirst u hu hlu
  unfold axisOf
  by_cases hq : ∃ v, FirstSuccessBefore G e o w v ∧ OnPath G e hc v w
  · rw [if_pos hq, if_pos (key.1 hq)]
  · rw [if_neg hq, if_neg (fun h' => hq (key.2 h'))]

/-- The adaptive strategy of the construction. -/
noncomputable def strategy [Fintype V] [DecidableEq V] (hc : G.Connected) : AdaptiveStrategy e where
  rank := rankOf G e
  rank_inj := fun _ _ _ _ h => rankOf_inj G e h
  axis := axisOf G e hc
  axis_ne := by
    intro w o
    unfold axisOf
    split_ifs <;> decide
  causal := axisOf_causal G e hc

end Construction

open Classical in
theorem perfect [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e : V)
    (hc : G.Connected)
    (o : V → Bool) (hs : ∃ w, w ≠ e ∧ o w = true) :
    ¬ LogicalFailure G e (strategy G e hc) o := by
  rintro ⟨P, ⟨U, hPU, hUe⟩, hP⟩
  -- the first successful fusion
  obtain ⟨v, hvmem, hvmin⟩ :=
    (Finset.univ.filter fun w => w ≠ e ∧ o w = true).exists_min_image
    (rankOf G e) (by obtain ⟨w, hw⟩ := hs; exact ⟨w, by simpa using hw⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvmem
  obtain ⟨hve, hov⟩ := hvmem
  have hfirst : ∀ u, u ≠ e → rankOf G e u < rankOf G e v → o u = false := by
    intro u hu hlt
    by_contra hcon
    have := hvmin u (by simp [hu, hcon])
    exact absurd hlt (not_lt.2 this)
  set q : ℕ → V := fun k => (parent G e hc)^[k] v with hq
  set ℓ := depth G e v with hℓ
  have hdepth : ∀ k, k ≤ ℓ → depth G e (q k) = ℓ - k :=
    fun k hk => depth_iterate G e hc v k hk
  have hzero : depth G e e = 0 := by unfold depth; simp
  have hdepth_eq_zero : ∀ x, depth G e x = 0 → x = e := fun x hx => by
    unfold depth at hx; exact ((hc.dist_eq_zero_iff).1 hx).symm
  have hℓpos : 1 ≤ ℓ := by
    by_contra h0
    exact hve (hdepth_eq_zero v (by omega))
  have hqne : ∀ k, k < ℓ → q k ≠ e := by
    intro k hk h
    have := hdepth k hk.le
    rw [h, hzero] at this
    omega
  have hqe : q ℓ = e := hdepth_eq_zero _ (by rw [hdepth ℓ le_rfl]; simp)
  have hqadj : ∀ k, k < ℓ → G.Adj (q k) (q (k + 1)) := by
    intro k hk
    have := (parent_spec G e hc (hqne k hk)).1
    simpa [hq, Function.iterate_succ_apply'] using this
  -- the realized axes
  have hX : ∀ w, OnPath G e hc v w → (strategy G e hc).axis w o = pauliX := by
    intro w hw
    obtain ⟨k, hk1, hkℓ, rfl⟩ := hw
    change axisOf G e hc _ o = pauliX
    unfold axisOf
    rw [if_pos]
    refine ⟨v, ⟨hve, hov, rankOf_lt_of_depth_lt G e ?_, hfirst⟩, ⟨k, hk1, hkℓ, rfl⟩⟩
    rw [depth_iterate G e hc v k hkℓ.le]; omega
  have hZ : ∀ w, ¬ OnPath G e hc v w → (strategy G e hc).axis w o = pauliZ := by
    intro w hw
    change axisOf G e hc w o = pauliZ
    unfold axisOf
    rw [if_neg]
    rintro ⟨v', ⟨hv'e, hov', _, hfirst'⟩, hp⟩
    have hvv : v' = v := by
      rcases lt_trichotomy (rankOf G e v') (rankOf G e v) with h | h | h
      · exact absurd (hvmin v' (by simp [hv'e, hov'])) (not_le.2 h)
      · exact rankOf_inj G e h
      · exact absurd (hfirst' v hve h) (by simp [hov])
    exact hw (hvv ▸ hp)
  -- letters forced by the outcome constraints
  have hnotU : ∀ w, w ≠ e → ¬ OnPath G e hc v w → w ∉ U := by
    intro w hwe hw hwU
    have hPw := hPU w hwe
    have hbit : (P w).1 = true := by rw [hPw]; simp [genProduct, hwU]
    cases how : o w
    · rcases (hP w hwe).1 how with h | h
      · rw [h] at hbit; exact absurd hbit (by decide)
      · rw [h, hZ w hw] at hbit; exact absurd hbit (by decide)
    · rw [(hP w hwe).2 how] at hbit; exact absurd hbit (by decide)
  have heven : ∀ w, w ≠ e → (w = v ∨ OnPath G e hc v w) →
      ¬ Odd (U.filter (G.Adj w)).card := by
    intro w hwe hw hodd
    have hPw := hPU w hwe
    have hbit : (P w).2 = true := by rw [hPw]; simp [genProduct, hodd]
    cases how : o w
    · rcases (hP w hwe).1 how with h | h
      · rw [h] at hbit; exact absurd hbit (by decide)
      · rcases hw with rfl | hw
        · exact absurd hov (by simp [how])
        · rw [h, hX w hw] at hbit; exact absurd hbit (by decide)
    · rw [(hP w hwe).2 how] at hbit; exact absurd hbit (by decide)
  -- every element of `U` lies on the geodesic
  have hUpath : ∀ y ∈ U, ∃ j, 1 ≤ j ∧ j ≤ ℓ ∧ q j = y := by
    intro y hy
    by_cases hye : y = e
    · exact ⟨ℓ, hℓpos, le_rfl, hqe.trans hye.symm⟩
    · by_contra hno
      apply hnotU y hye _ hy
      rintro ⟨k, hk1, hkℓ, hk⟩
      exact hno ⟨k, hk1, hkℓ.le, hk⟩
  -- an element of `U` adjacent to `q k` sits at a neighbouring index
  have hidx : ∀ k j, k ≤ ℓ → j ≤ ℓ → G.Adj (q k) (q j) →
      j + 1 = k ∨ j = k + 1 := by
    intro k j hk hj hadj
    have h1 := depth_adj_le G e hc hadj
    have h2 := depth_adj_le G e hc hadj.symm
    rw [hdepth k hk, hdepth j hj] at h1 h2
    have hne : k ≠ j := by
      rintro rfl; exact hadj.ne rfl
    omega
  -- downward induction along the geodesic
  have hpair : ∀ k, k + 1 ≤ ℓ → q k ∉ U ∧ q (k + 1) ∉ U := by
    intro k
    induction k with
    | zero =>
      intro h1
      have hq0 : q 0 = v := rfl
      refine ⟨hq0 ▸ hnotU v hve (fun ⟨k, hk1, hkℓ, hk⟩ => ?_), fun h1U => ?_⟩
      · have := depth_iterate G e hc v k hkℓ.le
        rw [hk] at this; omega
      · apply heven v hve (Or.inl rfl)
        have hsub : U.filter (G.Adj v) = {q 1} := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hyU, hadj⟩
            obtain ⟨j, hj1, hjℓ, rfl⟩ := hUpath y hyU
            rcases hidx 0 j (by omega) hjℓ (hq0 ▸ hadj) with h | h
            · omega
            · rw [h]
          · rintro rfl
            exact ⟨h1U, hq0 ▸ hqadj 0 (by omega)⟩
        rw [hsub]; simp
    | succ k ih =>
      intro hk
      obtain ⟨hk0, hk1⟩ := ih (by omega)
      refine ⟨hk1, fun h2U => ?_⟩
      have hint : OnPath G e hc v (q (k + 1)) := ⟨k + 1, by omega, by omega, rfl⟩
      apply heven (q (k + 1)) (hqne (k + 1) (by omega)) (Or.inr hint)
      have hsub : U.filter (G.Adj (q (k + 1))) = {q (k + 2)} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hyU, hadj⟩
          obtain ⟨j, hj1, hjℓ, rfl⟩ := hUpath y hyU
          rcases hidx (k + 1) j (by omega) hjℓ hadj with h | h
          · have : j = k := by omega
            subst this; exact absurd hyU hk0
          · rw [h]
        · rintro rfl
          exact ⟨h2U, hqadj (k + 1) (by omega)⟩
      rw [hsub]; simp
  have hUempty : U = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨j, hj1, hjℓ, rfl⟩ := hUpath y hy
    have := (hpair (j - 1) (by omega)).2
    rw [show j - 1 + 1 = j by omega] at this
    exact this hy
  apply hUe
  rw [hUempty]
  simp [genProduct, pauliI]

/-- Every graph code with a connected progenitor graph has a perfect adaptive fusion strategy. -/
theorem result : claim := by
  intro V _ _ G _ e hc _
  exact ⟨strategy G e hc, perfect G e hc⟩

end D5.S3.Quantum.Measurements.ConnectedProgenitorPerfectAdaptiveFusion
