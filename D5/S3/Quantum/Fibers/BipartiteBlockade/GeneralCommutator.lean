/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/GeneralCommutator
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/GeneralCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal single-site flips on the independent configurations of a finite simple graph. -/

import Mathlib

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048
open scoped BigOperators Matrix symmDiff Classical

namespace D5.S3.Quantum.Fibers.BipartiteBlockade

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All independent configurations, including the vacuum. -/
@[reducible] def Configuration (G : SimpleGraph V) :=
  {S : Finset V // ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v}

/-- No occupied vertex is adjacent to the chosen site. -/
def clear (G : SimpleGraph V) (v : V) (S : Configuration G) : Prop :=
  ∀ u ∈ S.val, ¬G.Adj v u

private theorem clear_of_mem (G : SimpleGraph V) (v : V) (S : Configuration G)
    (h : v ∈ S.val) : clear G v S := by
  exact S.property v h

private theorem independent_toggle (G : SimpleGraph V) (v : V) (S : Configuration G)
    (hc : clear G v S) :
    ∀ u ∈ S.val ∆ {v}, ∀ w ∈ S.val ∆ {v}, ¬G.Adj u w := by
  intro u hu w hw
  simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hu hw
  rcases hu with ⟨hu, huv⟩ | ⟨rfl, _⟩
  · rcases hw with ⟨hw, _⟩ | ⟨rfl, _⟩
    · exact S.property u hu w hw
    · exact fun h => hc u hu h.symm
  · rcases hw with ⟨hw, _⟩ | ⟨rfl, _⟩
    · exact hc w hw
    · exact G.irrefl

/-- The legal flip; blocked configurations are fixed, with zero transition weight. -/
def toggle (G : SimpleGraph V) (v : V) (S : Configuration G) : Configuration G :=
  if h : clear G v S then ⟨S.val ∆ {v}, independent_toggle G v S h⟩ else S

private theorem toggle_val (G : SimpleGraph V) (v : V) (S : Configuration G)
    (h : clear G v S) : (toggle G v S).val = S.val ∆ {v} := by
  simp [toggle, h]

private theorem clear_toggle (G : SimpleGraph V) (v : V) (S : Configuration G) :
    clear G v (toggle G v S) ↔ clear G v S := by
  by_cases h : clear G v S
  · constructor
    · intro _; exact h
    · intro _ u hu
      rw [toggle_val G v S h] at hu
      simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hu
      rcases hu with ⟨hu, _⟩ | ⟨rfl, _⟩
      · exact h u hu
      · exact G.irrefl
  · simp [toggle, h]

private theorem toggle_involutive (G : SimpleGraph V) (v : V) (S : Configuration G) :
    toggle G v (toggle G v S) = S := by
  by_cases h : clear G v S
  · apply Subtype.ext
    rw [toggle_val G v (toggle G v S) ((clear_toggle G v S).2 h), toggle_val G v S h]
    simp only [symmDiff_assoc, symmDiff_self, symmDiff_bot]
  · simp [toggle, h]

/-- An unweighted legal flip, on the actual independent-set basis. -/
def flip (G : SimpleGraph V) (v : V) :
    Matrix (Configuration G) (Configuration G) ℂ :=
  fun S T => if clear G v S ∧ toggle G v S = T then 1 else 0

/-- Site occupation projector. -/
def number (G : SimpleGraph V) (v : V) :
    Matrix (Configuration G) (Configuration G) ℂ :=
  Matrix.diagonal fun S => if v ∈ S.val then 1 else 0

/-- The diagonal projector for an empty open neighborhood. -/
def blockade (G : SimpleGraph V) (v : V) :
    Matrix (Configuration G) (Configuration G) ℂ :=
  Matrix.diagonal fun S => if clear G v S then 1 else 0

/-- Weighted legal single-flip Hamiltonian. -/
def hamiltonian (G : SimpleGraph V) (Ω : V → ℂ) :
    Matrix (Configuration G) (Configuration G) ℂ :=
  ∑ v, Ω v • flip G v

private theorem flip_mul_apply (G : SimpleGraph V) (v : V)
    (M : Matrix (Configuration G) (Configuration G) ℂ) (S T : Configuration G) :
    (flip G v * M) S T = if clear G v S then M (toggle G v S) T else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases h : clear G v S
  · rw [if_pos h, Finset.sum_eq_single (toggle G v S)]
    · simp [flip, h]
    · intro U _ hU
      simp [flip, h, Ne.symm hU]
    · simp
  · simp [flip, h]

private theorem mul_flip_apply (G : SimpleGraph V) (v : V)
    (M : Matrix (Configuration G) (Configuration G) ℂ) (S T : Configuration G) :
    (M * flip G v) S T = if clear G v T then M S (toggle G v T) else 0 := by
  classical
  rw [Matrix.mul_apply]
  have hiff : ∀ U : Configuration G,
      (clear G v U ∧ toggle G v U = T) ↔
        (clear G v T ∧ U = toggle G v T) := by
    intro U
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨(clear_toggle G v U).2 h, (toggle_involutive G v U).symm⟩
    · rintro ⟨h, rfl⟩
      exact ⟨(clear_toggle G v T).2 h, toggle_involutive G v T⟩
  simp_rw [flip, hiff]
  by_cases h : clear G v T
  · simp [h]
  · simp [h]

private theorem mem_toggle_ne (G : SimpleGraph V) (u v : V) (S : Configuration G)
    (huv : u ≠ v) : u ∈ (toggle G v S).val ↔ u ∈ S.val := by
  by_cases h : clear G v S
  · rw [toggle_val G v S h]
    simp [Finset.mem_symmDiff, huv]
  · simp [toggle, h]

private theorem mem_toggle_self (G : SimpleGraph V) (v : V) (S : Configuration G)
    (h : clear G v S) : v ∈ (toggle G v S).val ↔ v ∉ S.val := by
  rw [toggle_val G v S h]
  simp [Finset.mem_symmDiff]

private theorem clear_toggle_nonadjacent (G : SimpleGraph V) (u v : V)
    (S : Configuration G) (huv : ¬G.Adj u v) :
    clear G u (toggle G v S) ↔ clear G u S := by
  by_cases h : clear G v S
  · rw [clear, toggle_val G v S h]
    simp only [Finset.mem_symmDiff, Finset.mem_singleton]
    constructor
    · intro hc w hw huw
      by_cases hwv : w = v
      · subst w; exact huv huw
      · exact hc w (Or.inl ⟨hw, hwv⟩) huw
    · intro hc w hw
      rcases hw with ⟨hw, _⟩ | ⟨rfl, _⟩
      · exact hc w hw
      · exact huv
  · simp [toggle, h]

private theorem toggle_commute (G : SimpleGraph V) (u v : V)
    (S : Configuration G) (huv : ¬G.Adj u v) :
    toggle G u (toggle G v S) = toggle G v (toggle G u S) := by
  have hvu : ¬G.Adj v u := fun h => huv h.symm
  by_cases hu : clear G u S <;> by_cases hv : clear G v S
  · apply Subtype.ext
    rw [toggle_val G u (toggle G v S) ((clear_toggle_nonadjacent G u v S huv).2 hu),
      toggle_val G v (toggle G u S) ((clear_toggle_nonadjacent G v u S hvu).2 hv),
      toggle_val G v S hv, toggle_val G u S hu]
    simp only [symmDiff_assoc, symmDiff_comm ({u} : Finset V) {v}]
  · have hvt : ¬clear G v (toggle G u S) :=
      (clear_toggle_nonadjacent G v u S hvu).not.2 hv
    have hvs : toggle G v S = S := by simp [toggle, hv]
    have hvts : toggle G v (toggle G u S) = toggle G u S := by
      rw [toggle, dif_neg hvt]
    rw [hvs, hvts]
  · have hut : ¬clear G u (toggle G v S) :=
      (clear_toggle_nonadjacent G u v S huv).not.2 hu
    have hus : toggle G u S = S := by simp [toggle, hu]
    have huts : toggle G u (toggle G v S) = toggle G v S := by
      rw [toggle, dif_neg hut]
    rw [hus, huts]
  · simp [toggle, hu, hv]

private theorem bracket_number_apply (G : SimpleGraph V) (v : V)
    (M : Matrix (Configuration G) (Configuration G) ℂ) (S T : Configuration G) :
    ⁅M, number G v⁆ S T = M S T *
      ((if v ∈ T.val then 1 else 0) - (if v ∈ S.val then 1 else 0)) := by
  simp only [Ring.lie_def, number, Matrix.sub_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  ring

private theorem flip_number_commute (G : SimpleGraph V) (u v : V) (huv : u ≠ v) :
    ⁅flip G u, number G v⁆ = 0 := by
  ext S T
  rw [bracket_number_apply]
  by_cases h : clear G u S ∧ toggle G u S = T
  · rcases h with ⟨hc, rfl⟩
    simp [flip, hc, mem_toggle_ne G v u S huv.symm]
  · simp [flip, h]

private theorem flip_commute_nonadjacent (G : SimpleGraph V) (u v : V)
    (huv : ¬G.Adj u v) :
    flip G u * flip G v = flip G v * flip G u := by
  ext S T
  rw [flip_mul_apply, flip_mul_apply]
  have hvu : ¬G.Adj v u := fun h => huv h.symm
  simp only [flip, clear_toggle_nonadjacent G v u S hvu,
    clear_toggle_nonadjacent G u v S huv, toggle_commute G u v S huv]
  split_ifs <;> simp_all

/-- A flip at a non-neighbor contributes no mixed double commutator. -/
private theorem mixed_nonadjacent (G : SimpleGraph V) (u v : V)
    (hne : u ≠ v) (hadj : ¬G.Adj u v) :
    ⁅flip G u, ⁅flip G v, number G v⁆⁆ = 0 := by
  have hcomm : ⁅flip G u, flip G v⁆ = 0 := by
    rw [Ring.lie_def, sub_eq_zero]
    exact flip_commute_nonadjacent G u v hadj
  rw [leibniz_lie, hcomm, flip_number_commute G u v hne, zero_lie, lie_zero, add_zero]

private theorem clear_of_difference (G : SimpleGraph V) (v : V)
    (S T : Configuration G) (he : S.val ∆ {v} = T.val) : clear G v S := by
  by_cases hv : v ∈ S.val
  · exact clear_of_mem G v S hv
  · intro u hu hadj
    have huv : u ≠ v := by
      intro h; subst u; exact G.irrefl hadj
    have huT : u ∈ T.val := by
      rw [← he]
      simp [Finset.mem_symmDiff, hu, huv]
    have hvT : v ∈ T.val := by
      rw [← he]
      simp [Finset.mem_symmDiff, hv]
    exact T.property v hvT u huT hadj

private theorem flip_indicator (G : SimpleGraph V) (v : V) (S T : Configuration G) :
    flip G v S T = if S.val ∆ {v} = T.val then 1 else 0 := by
  by_cases h : clear G v S
  · simp only [flip, h, true_and, Subtype.ext_iff, toggle_val G v S h]
  · have hn : S.val ∆ {v} ≠ T.val := fun he => h (clear_of_difference G v S T he)
    simp [flip, h, hn]

private theorem pair_difference (S : Finset V) (u v : V) (huv : u ≠ v) :
    (S ∆ {u}) ∆ {v} = S ∆ {u, v} := by
  ext w
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  by_cases hwU : w = u <;> by_cases hwV : w = v <;> simp_all

/-- Exchange of two occupied alternatives, specified independently by the two-site
symmetric difference on legal configurations. -/
def exchange (G : SimpleGraph V) (u v : V) :
    Matrix (Configuration G) (Configuration G) ℂ :=
  fun S T => if S.val ∆ {u, v} = T.val then 1 else 0

private theorem adjacent_product (G : SimpleGraph V) (u v : V) (ha : G.Adj u v)
    (S T : Configuration G) :
    (flip G u * flip G v) S T =
      if u ∈ S.val ∧ S.val ∆ {u, v} = T.val then 1 else 0 := by
  have huv : u ≠ v := G.ne_of_adj ha
  rw [flip_mul_apply]
  by_cases hc : clear G u S
  · rw [if_pos hc, flip_indicator, toggle_val G u S hc, pair_difference _ u v huv]
    by_cases he : S.val ∆ {u, v} = T.val
    · have hu : u ∈ S.val := by
        by_contra hn
        have hv : v ∉ S.val := fun hv => hc v hv ha
        have huT : u ∈ T.val := by
          rw [← he]; simp [Finset.mem_symmDiff, hn]
        have hvT : v ∈ T.val := by
          rw [← he]; simp [Finset.mem_symmDiff, hv, huv.symm]
        exact T.property u huT v hvT ha
      simp [he, hu]
    · simp [he]
  · rw [if_neg hc]
    have hn : u ∉ S.val := fun h => hc (clear_of_mem G u S h)
    simp [hn]

private theorem mixed_entry (G : SimpleGraph V) (u v : V) (hne : u ≠ v)
    (S T : Configuration G) :
    ⁅flip G u, ⁅flip G v, number G v⁆⁆ S T =
      ((flip G u * flip G v) S T - (flip G v * flip G u) S T) *
        ((if v ∈ T.val then 1 else 0) - (if v ∈ S.val then 1 else 0)) := by
  rw [leibniz_lie, flip_number_commute G u v hne, lie_zero, add_zero,
    bracket_number_apply]
  simp only [Ring.lie_def, Matrix.sub_apply]

/-- On an edge, the mixed double commutator is exactly the legal occupancy exchange. -/
private theorem mixed_adjacent (G : SimpleGraph V) (u v : V) (ha : G.Adj u v) :
    ⁅flip G u, ⁅flip G v, number G v⁆⁆ = exchange G u v := by
  have huv : u ≠ v := G.ne_of_adj ha
  ext S T
  rw [mixed_entry G u v huv, adjacent_product G u v ha,
    adjacent_product G v u ha.symm]
  have hpair : ({v, u} : Finset V) = {u, v} := by ext w; simp [or_comm]
  rw [hpair]
  simp only [exchange]
  by_cases he : S.val ∆ {u, v} = T.val
  · have hvT : v ∈ T.val ↔ v ∉ S.val := by
      rw [← he]
      simp [Finset.mem_symmDiff, huv.symm]
    have hnot : ¬(u ∈ S.val ∧ v ∈ S.val) := fun h => S.property u h.1 v h.2 ha
    have hor : u ∈ S.val ∨ v ∈ S.val := by
      by_contra h
      push_neg at h
      have huT : u ∈ T.val := by rw [← he]; simp [Finset.mem_symmDiff, h.1]
      have hvT' : v ∈ T.val := by rw [← he]; simp [Finset.mem_symmDiff, h.2, huv.symm]
      exact T.property u huT v hvT' ha
    rcases hor with hu | hv
    · have hv : v ∉ S.val := fun hv => hnot ⟨hu, hv⟩
      simp [he, hu, hv, hvT]
    · have hu : u ∉ S.val := fun hu => hnot ⟨hu, hv⟩
      simp [he, hu, hv, hvT]
  · simp [he]

private theorem toggle_injective (G : SimpleGraph V) (v : V) :
    Function.Injective (toggle G v) := by
  intro S T h
  have h' := congrArg (toggle G v) h
  simpa only [toggle_involutive] using h'

/-- The diagonal local contribution to the double commutator. -/
private theorem same_site_double_commutator (G : SimpleGraph V) (v : V) :
    ⁅flip G v, ⁅flip G v, number G v⁆⁆ =
      (2 : ℂ) • ((2 : ℂ) • number G v - blockade G v) := by
  ext S T
  rw [Ring.lie_def, Matrix.sub_apply, flip_mul_apply, mul_flip_apply]
  simp only [bracket_number_apply]
  by_cases he : S = T
  · subst T
    by_cases hc : clear G v S
    · have hm := mem_toggle_self G v S hc
      simp only [hc, if_true, flip, clear_toggle, toggle_involutive,
        and_self, Matrix.smul_apply, Matrix.sub_apply, number, blockade,
        Matrix.diagonal_apply_eq, smul_eq_mul]
      by_cases hv : v ∈ S.val <;> simp [hv, hm] <;> norm_num
    · have hn : v ∉ S.val := fun h => hc (clear_of_mem G v S h)
      simp [hc, hn, number, blockade, Matrix.smul_apply]
  · have ht : toggle G v S ≠ toggle G v T := fun h => he (toggle_injective G v h)
    have hs : T ≠ S := Ne.symm he
    simp [flip, clear_toggle, toggle_involutive, ht, he, hs,
      number, blockade, Matrix.diagonal_apply, Matrix.smul_apply]

/-- General finite-graph double commutator. No bipartiteness or connectivity is
needed for this operator identity. -/
theorem general_double_commutator (G : SimpleGraph V) (Ω : V → ℂ) (v : V) :
    ⁅hamiltonian G Ω, ⁅hamiltonian G Ω, number G v⁆⁆ =
      (2 * Ω v ^ 2) • ((2 : ℂ) • number G v - blockade G v) +
        ∑ u, if G.Adj u v then (Ω u * Ω v) • exchange G u v else 0 := by
  have hinner : ⁅hamiltonian G Ω, number G v⁆ =
      Ω v • ⁅flip G v, number G v⁆ := by
    rw [hamiltonian, sum_lie, Finset.sum_eq_single v]
    · exact smul_lie _ _ _
    · intro u _ huv
      rw [smul_lie, flip_number_commute G u v huv, smul_zero]
    · simp
  rw [hinner, lie_smul, hamiltonian, sum_lie]
  simp_rw [smul_lie, Finset.smul_sum, smul_smul]
  have heach : ∀ u : V,
      (Ω v * Ω u) • ⁅flip G u, ⁅flip G v, number G v⁆⁆ =
        (if u = v then (2 * Ω v ^ 2) •
          ((2 : ℂ) • number G v - blockade G v) else 0) +
        (if G.Adj u v then (Ω u * Ω v) • exchange G u v else 0) := by
    intro u
    by_cases he : u = v
    · subst u
      rw [same_site_double_commutator]
      simp [G.irrefl, smul_smul, pow_two, mul_assoc, mul_comm, mul_left_comm]
    · by_cases ha : G.Adj u v
      · simp [he, ha, mixed_adjacent G u v ha, mul_comm]
      · simp [he, ha, mixed_nonadjacent G u v he ha]
  simp_rw [heach, Finset.sum_add_distrib]
  simp

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.general_double_commutator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms general_double_commutator

end D5.S3.Quantum.Fibers.BipartiteBlockade
