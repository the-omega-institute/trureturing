/- GID: D5/S3/StatisticalMechanics/TeaCoordinationSequence
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/TeaCoordinationSequence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barker's coordination sequence formula for the tea uniform tiling. -/

import D5.S1.Recurrence.Bilateral.HannaThetaFourModFour
import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum
import Mathlib.Algebra.Order.Floor.BigOperators

/-! The exact graph metric and coordination sequence of the tea slab graph. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.TeaCoordinationSequence

private def teaAdj (u v : ℤ × ℤ × ℤ) : Prop :=
  (u.2.2 = v.2.2 ∧
    ((v.1 = u.1 + 1 ∧ v.2.1 = u.2.1) ∨
     (u.1 = v.1 + 1 ∧ u.2.1 = v.2.1) ∨
     (v.1 = u.1 ∧ v.2.1 = u.2.1 + 1) ∨
     (u.1 = v.1 ∧ u.2.1 = v.2.1 + 1) ∨
     (v.1 = u.1 + 1 ∧ u.2.1 = v.2.1 + 1) ∨
     (u.1 = v.1 + 1 ∧ v.2.1 = u.2.1 + 1))) ∨
  (v.2.2 = u.2.2 + 1 ∧
    ((v.1 = u.1 ∧ v.2.1 = u.2.1) ∨
     (u.2.2 % 4 = 0 ∧
       ((v.1 = u.1 + 1 ∧ v.2.1 = u.2.1) ∨
        (v.1 = u.1 ∧ v.2.1 = u.2.1 + 1))) ∨
     (u.2.2 % 4 = 2 ∧
       ((v.1 = u.1 - 1 ∧ v.2.1 = u.2.1) ∨
        (v.1 = u.1 ∧ v.2.1 = u.2.1 - 1))))) ∨
  (u.2.2 = v.2.2 + 1 ∧
    ((u.1 = v.1 ∧ u.2.1 = v.2.1) ∨
     (v.2.2 % 4 = 0 ∧
       ((u.1 = v.1 + 1 ∧ u.2.1 = v.2.1) ∨
        (u.1 = v.1 ∧ u.2.1 = v.2.1 + 1))) ∨
     (v.2.2 % 4 = 2 ∧
       ((u.1 = v.1 - 1 ∧ u.2.1 = v.2.1) ∨
        (u.1 = v.1 ∧ u.2.1 = v.2.1 - 1)))))

private lemma teaAdj_symm : Std.Symm teaAdj := ⟨by
    intro u v h
    rcases h with ⟨hk, h⟩ | h | h
    · left
      refine ⟨hk.symm, ?_⟩
      rcases h with h | h | h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩

private lemma teaAdj_irrefl : Std.Irrefl teaAdj := ⟨by
    intro u h
    rcases h with ⟨_, h⟩ | h | h
    · rcases h with h | h | h | h | h | h <;> omega
    · omega
    · omega⟩

/-- The triangular layers and tetrahedral or prismatic slabs of the tea tiling. -/
def teaGraph : SimpleGraph (ℤ × ℤ × ℤ) where
  Adj := teaAdj
  symm := teaAdj_symm
  loopless := teaAdj_irrefl

/-- Vertices at graph distance exactly n from the representative origin. -/
def shell (n : ℕ) : ℕ := Set.ncard {v | teaGraph.dist (0, 0, 0) v = n}

def claim : Prop := ∀ n : ℕ, 0 < n →
  (n % 4 = 0 → 8 * shell n = 63 * n ^ 2 + 16) ∧
  (n % 4 = 1 → 8 * shell n = 63 * n ^ 2 + 17) ∧
  (n % 4 = 2 → 8 * shell n = 63 * n ^ 2 + 12) ∧
  (n % 4 = 3 → 8 * shell n = 63 * n ^ 2 + 17)

private def plusSlabs (k : ℤ) : ℤ :=
  if 0 ≤ k then (k + 3) / 4 else (-k + 2) / 4

private def minusSlabs (k : ℤ) : ℤ :=
  if 0 ≤ k then (k + 1) / 4 else (-k) / 4

def residual (i j p q : ℤ) : ℤ :=
  max 0 (max (i - p) (max (j - p) (max (i + j - p)
    (max (-q - i) (max (-q - j) (-q - i - j))))))

private def potential (v : ℤ × ℤ × ℤ) : ℕ :=
  v.2.2.natAbs + (residual v.1 v.2.1 (plusSlabs v.2.2) (minusSlabs v.2.2)).toNat

private lemma residual_le_iff (i j p q d : ℤ) :
    residual i j p q ≤ d ↔
      0 ≤ d ∧ i ≤ p + d ∧ j ≤ p + d ∧ i + j ≤ p + d ∧
        -q - d ≤ i ∧ -q - d ≤ j ∧ -q - d ≤ i + j := by
  dsimp only [residual]
  simp only [max_le_iff]
  omega

private lemma slabs_nonneg (k : ℤ) : 0 ≤ plusSlabs k ∧ 0 ≤ minusSlabs k := by
  dsimp only [plusSlabs, minusSlabs]
  split <;> omega

private lemma potential_step (u v : ℤ × ℤ × ℤ) (h : teaGraph.Adj u v) :
    potential u ≤ potential v + 1 := by
  rcases u with ⟨i, j, k⟩
  rcases v with ⟨a, b, l⟩
  have hu := (residual_le_iff i j (plusSlabs k) (minusSlabs k)
    (residual i j (plusSlabs k) (minusSlabs k))).mp le_rfl
  have hv := (residual_le_iff a b (plusSlabs l) (minusSlabs l)
    (residual a b (plusSlabs l) (minusSlabs l))).mp le_rfl
  change _ ∨ _ ∨ _ at h
  dsimp only at h
  rcases h with ⟨hk, h⟩ | ⟨hk, h⟩ | ⟨hk, h⟩
  · subst l
    have hr : residual i j (plusSlabs k) (minusSlabs k) ≤
        residual a b (plusSlabs k) (minusSlabs k) + 1 := by
      rw [residual_le_iff]
      rcases h with h | h | h | h | h | h <;> omega
    dsimp only [potential]
    omega
  · subst l
    have hr : residual i j (plusSlabs k) (minusSlabs k) ≤
        residual a b (plusSlabs (k + 1)) (minusSlabs (k + 1)) +
          (if 0 ≤ k then 2 else 0) := by
      rw [residual_le_iff]
      dsimp only [plusSlabs, minusSlabs] at hv ⊢
      by_cases hk : 0 ≤ k
      · simp only [ite_eq_left hk, ite_eq_left (show 0 ≤ k + 1 by omega)] at hv ⊢
        rcases h with h | ⟨hm, h | h⟩ | ⟨hm, h | h⟩ <;> omega
      · simp only [ite_eq_right hk] at hv ⊢
        by_cases hk' : 0 ≤ k + 1
        · have he : k = -1 := by omega
          subst k
          norm_num at hv ⊢
          rcases h with h | ⟨hm, h⟩ | ⟨hm, h⟩ <;> omega
        · simp only [ite_eq_right hk'] at hv ⊢
          rcases h with h | ⟨hm, h | h⟩ | ⟨hm, h | h⟩ <;> omega
    dsimp only [potential]
    split at hr <;> omega
  · subst k
    have hr : residual i j (plusSlabs (l + 1)) (minusSlabs (l + 1)) ≤
        residual a b (plusSlabs l) (minusSlabs l) + (if 0 ≤ l then 0 else 2) := by
      rw [residual_le_iff]
      dsimp only [plusSlabs, minusSlabs] at hv ⊢
      by_cases hl : 0 ≤ l
      · simp only [ite_eq_left hl, ite_eq_left (show 0 ≤ l + 1 by omega)] at hv ⊢
        rcases h with h | ⟨hm, h | h⟩ | ⟨hm, h | h⟩ <;> omega
      · simp only [ite_eq_right hl] at hv ⊢
        by_cases hl' : 0 ≤ l + 1
        · have he : l = -1 := by omega
          subst l
          norm_num at hv ⊢
          rcases h with h | ⟨hm, h⟩ | ⟨hm, h⟩ <;> omega
        · simp only [ite_eq_right hl'] at hv ⊢
          rcases h with h | ⟨hm, h | h⟩ | ⟨hm, h | h⟩ <;> omega
    dsimp only [potential]
    split at hr <;> omega

private lemma residual_descent (i j k p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : 0 < residual i j p q) :
    ∃ a b, teaGraph.Adj (a, b, k) (i, j, k) ∧
      residual a b p q + 1 = residual i j p q := by
  by_cases hi : 0 ≤ i
  · by_cases hj : 0 ≤ j
    · by_cases hi' : 0 < i
      · refine ⟨i - 1, j, Or.inl ⟨rfl, Or.inl ⟨by omega, rfl⟩⟩, ?_⟩
        dsimp only [residual] at h ⊢; omega
      · refine ⟨i, j - 1, Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, by dsimp only; omega⟩))⟩, ?_⟩
        dsimp only [residual] at h ⊢; omega
    · by_cases hi' : 0 < i
      · refine ⟨i - 1, j + 1,
          Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))))⟩, ?_⟩
        dsimp only [residual] at h ⊢; omega
      · refine ⟨i, j + 1, Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩, ?_⟩
        dsimp only [residual] at h ⊢; omega
  · by_cases hj : 0 < j
    · refine ⟨i + 1, j - 1,
        Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by dsimp only; omega⟩))))⟩, ?_⟩
      dsimp only [residual] at h ⊢; omega
    · refine ⟨i + 1, j, Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, ?_⟩
      dsimp only [residual] at h ⊢; omega

private lemma remove_plus (i j p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : residual i j (p + 1) q = 0) :
    ∃ a b, ((i = a ∧ j = b) ∨ (i = a + 1 ∧ j = b) ∨
      (i = a ∧ j = b + 1)) ∧ residual a b p q = 0 := by
  have hb := (residual_le_iff i j (p + 1) q 0).mp h.le
  by_cases h0 : residual i j p q = 0
  · exact ⟨i, j, Or.inl ⟨rfl, rfl⟩, h0⟩
  · by_cases hi : 0 < i
    · refine ⟨i - 1, j, Or.inr (Or.inl ⟨by omega, rfl⟩), ?_⟩
      dsimp only [residual] at h0 ⊢; omega
    · refine ⟨i, j - 1, Or.inr (Or.inr ⟨rfl, by omega⟩), ?_⟩
      dsimp only [residual] at h0 ⊢; omega

private lemma remove_minus (i j p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : residual i j p (q + 1) = 0) :
    ∃ a b, ((i = a ∧ j = b) ∨ (i = a - 1 ∧ j = b) ∨
      (i = a ∧ j = b - 1)) ∧ residual a b p q = 0 := by
  have hb := (residual_le_iff i j p (q + 1) 0).mp h.le
  by_cases h0 : residual i j p q = 0
  · exact ⟨i, j, Or.inl ⟨rfl, rfl⟩, h0⟩
  · by_cases hi : i < 0
    · refine ⟨i + 1, j, Or.inr (Or.inl ⟨by omega, rfl⟩), ?_⟩
      dsimp only [residual] at h0 ⊢; omega
    · refine ⟨i, j + 1, Or.inr (Or.inr ⟨rfl, by omega⟩), ?_⟩
      dsimp only [residual] at h0 ⊢; omega

private lemma inside_descent (i j k : ℤ) (hk : k ≠ 0)
    (h : residual i j (plusSlabs k) (minusSlabs k) = 0) :
    ∃ u, teaGraph.Adj u (i, j, k) ∧ potential u + 1 = potential (i, j, k) := by
  by_cases hk' : 0 < k
  · have hpq := slabs_nonneg (k - 1)
    by_cases h0 : (k - 1) % 4 = 0
    · have hp : plusSlabs k = plusSlabs (k - 1) + 1 := by
        dsimp only [plusSlabs]
        split <;> split <;> omega
      have hq : minusSlabs k = minusSlabs (k - 1) := by
        dsimp only [minusSlabs]
        split <;> split <;> omega
      have hr := h
      rw [hp, hq] at hr
      obtain ⟨a, b, hab, hr⟩ := remove_plus i j _ _ hpq.1 hpq.2 hr
      refine ⟨(a, b, k - 1), ?_, ?_⟩
      · refine Or.inr (Or.inl ⟨by dsimp only; omega, ?_⟩)
        rcases hab with hab | hab | hab
        · exact Or.inl hab
        · exact Or.inr (Or.inl ⟨h0, Or.inl hab⟩)
        · exact Or.inr (Or.inl ⟨h0, Or.inr hab⟩)
      · dsimp only [potential]
        rw [hr, h]
        omega
    · by_cases h2 : (k - 1) % 4 = 2
      · have hp : plusSlabs k = plusSlabs (k - 1) := by
          dsimp only [plusSlabs]
          split <;> split <;> omega
        have hq : minusSlabs k = minusSlabs (k - 1) + 1 := by
          dsimp only [minusSlabs]
          split <;> split <;> omega
        have hr := h
        rw [hp, hq] at hr
        obtain ⟨a, b, hab, hr⟩ := remove_minus i j _ _ hpq.1 hpq.2 hr
        refine ⟨(a, b, k - 1), ?_, ?_⟩
        · refine Or.inr (Or.inl ⟨by dsimp only; omega, ?_⟩)
          rcases hab with hab | hab | hab
          · exact Or.inl hab
          · exact Or.inr (Or.inr ⟨h2, Or.inl hab⟩)
          · exact Or.inr (Or.inr ⟨h2, Or.inr hab⟩)
        · dsimp only [potential]
          rw [hr, h]
          omega
      · have hp : plusSlabs k = plusSlabs (k - 1) := by
          dsimp only [plusSlabs]
          split <;> split <;> omega
        have hq : minusSlabs k = minusSlabs (k - 1) := by
          dsimp only [minusSlabs]
          split <;> split <;> omega
        refine ⟨(i, j, k - 1), ?_, ?_⟩
        · exact Or.inr (Or.inl ⟨by dsimp only; omega, Or.inl ⟨rfl, rfl⟩⟩)
        · dsimp only [potential]
          rw [← hp, ← hq, h]
          omega
  · have hpq := slabs_nonneg (k + 1)
    by_cases h0 : k % 4 = 0
    · have hp : plusSlabs k = plusSlabs (k + 1) := by
        dsimp only [plusSlabs]
        split <;> split <;> omega
      have hq : minusSlabs k = minusSlabs (k + 1) + 1 := by
        dsimp only [minusSlabs]
        split <;> split <;> omega
      have hr := h
      rw [hp, hq] at hr
      obtain ⟨a, b, hab, hr⟩ := remove_minus i j _ _ hpq.1 hpq.2 hr
      refine ⟨(a, b, k + 1), ?_, ?_⟩
      · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨ha.symm, hb.symm⟩
        · exact Or.inr (Or.inl ⟨h0, Or.inl ⟨by dsimp only; omega, hb.symm⟩⟩)
        · exact Or.inr (Or.inl ⟨h0, Or.inr ⟨ha.symm, by dsimp only; omega⟩⟩)
      · dsimp only [potential]
        rw [hr, h]
        omega
    · by_cases h2 : k % 4 = 2
      · have hp : plusSlabs k = plusSlabs (k + 1) + 1 := by
          dsimp only [plusSlabs]
          split <;> split <;> omega
        have hq : minusSlabs k = minusSlabs (k + 1) := by
          dsimp only [minusSlabs]
          split <;> split <;> omega
        have hr := h
        rw [hp, hq] at hr
        obtain ⟨a, b, hab, hr⟩ := remove_plus i j _ _ hpq.1 hpq.2 hr
        refine ⟨(a, b, k + 1), ?_, ?_⟩
        · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
          rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl ⟨ha.symm, hb.symm⟩
          · exact Or.inr (Or.inr ⟨h2, Or.inl ⟨by dsimp only; omega, hb.symm⟩⟩)
          · exact Or.inr (Or.inr ⟨h2, Or.inr ⟨ha.symm, by dsimp only; omega⟩⟩)
        · dsimp only [potential]
          rw [hr, h]
          omega
      · have hp : plusSlabs k = plusSlabs (k + 1) := by
          dsimp only [plusSlabs]
          split <;> split <;> omega
        have hq : minusSlabs k = minusSlabs (k + 1) := by
          dsimp only [minusSlabs]
          split <;> split <;> omega
        refine ⟨(i, j, k + 1), ?_, ?_⟩
        · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
        · dsimp only [potential]
          rw [← hp, ← hq, h]
          omega

private lemma potential_descent (v : ℤ × ℤ × ℤ) (h : 0 < potential v) :
    ∃ u, teaGraph.Adj u v ∧ potential u + 1 = potential v := by
  rcases v with ⟨i, j, k⟩
  have hpq := slabs_nonneg k
  have hr : 0 ≤ residual i j (plusSlabs k) (minusSlabs k) := le_max_left _ _
  by_cases hz : residual i j (plusSlabs k) (minusSlabs k) = 0
  · apply inside_descent i j k (by
      intro hk
      subst k
      dsimp only [potential] at h
      rw [hz] at h
      norm_num at h) hz
  · obtain ⟨a, b, hab, he⟩ := residual_descent i j k _ _ hpq.1 hpq.2 (by omega)
    refine ⟨(a, b, k), hab, ?_⟩
    have hr' : 0 ≤ residual a b (plusSlabs k) (minusSlabs k) := le_max_left _ _
    dsimp only [potential]
    omega

private lemma geodesic (v : ℤ × ℤ × ℤ) :
    ∃ w : teaGraph.Walk (0, 0, 0) v, w.length = potential v := by
  suffices ∀ m, ∀ v, potential v = m →
      ∃ w : teaGraph.Walk (0, 0, 0) v, w.length = potential v from
    this (potential v) v rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro v hv
    by_cases hm : m = 0
    · have hz : v = (0, 0, 0) := by
        rcases v with ⟨i, j, k⟩
        dsimp only [potential] at hv
        have hk : k = 0 := by omega
        subst k
        have hr := (residual_le_iff i j 0 0 0)
        have hb : residual i j 0 0 ≤ 0 := by
          have hn : 0 ≤ residual i j 0 0 := le_max_left _ _
          change (0 : ℕ) + (residual i j 0 0).toNat = m at hv
          omega
        have hb' := hr.mp hb
        have hi : i = 0 := by omega
        have hj : j = 0 := by omega
        subst i; subst j; rfl
      subst v
      refine ⟨.nil, ?_⟩
      dsimp only [potential, plusSlabs, minusSlabs, residual]
      norm_num
    · obtain ⟨u, hu, he⟩ := potential_descent v (by omega)
      obtain ⟨w, hw⟩ := ih (potential u) (by omega) u rfl
      refine ⟨w.append hu.toWalk, ?_⟩
      rw [SimpleGraph.Walk.length_append, hw, SimpleGraph.Adj.length_toWalk, he]

private lemma distance_formula (v : ℤ × ℤ × ℤ) :
    teaGraph.dist (0, 0, 0) v = potential v := by
  obtain ⟨w, hw⟩ := geodesic v
  refine le_antisymm (hw ▸ SimpleGraph.dist_le w) ?_
  have hl := D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation.potential_dist
    teaGraph potential potential_step w.reachable.symm
  have hz : potential (0, 0, 0) = 0 := by rfl
  simpa only [hz, zero_add, SimpleGraph.dist_comm] using hl

private def regionShell (p q : ℤ) (d : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-q - d) (p + d)).product (Finset.Icc (-q - d) (p + d))).filter
    (fun z => residual z.1 z.2 p q = d)

private lemma region_shell_mem (p q i j : ℤ) (_hp : 0 ≤ p) (_hq : 0 ≤ q) (d : ℕ) :
    (i, j) ∈ regionShell p q d ↔ residual i j p q = d := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hb := (residual_le_iff i j p q d).mp h.le
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
       Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, h⟩

private def hexagon (p q : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-q) p).product (Finset.Icc (-q) p)).filter
    (fun z => -q ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ p)

private lemma hexagon_mem (p q i j : ℤ) :
    (i, j) ∈ hexagon p q ↔
      -q ≤ i ∧ i ≤ p ∧ -q ≤ j ∧ j ≤ p ∧ -q ≤ i + j ∧ i + j ≤ p := by
  constructor
  · intro h
    obtain ⟨hbox, hsum⟩ := Finset.mem_filter.mp h
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hbox
    obtain ⟨hi0, hi1⟩ := Finset.mem_Icc.mp hi
    obtain ⟨hj0, hj1⟩ := Finset.mem_Icc.mp hj
    exact ⟨hi0, hi1, hj0, hj1, hsum⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩,
       Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2.1⟩⟩, h.2.2.2.2⟩

private lemma twice_sum_interval (a b : ℤ) :
    2 * (∑ i ∈ Finset.Icc a b, i) = (a + b) * (Finset.Icc a b).card := by
  by_cases hab : a ≤ b
  · have h := D5.S3.VertexAlgebra.LatticeHalfFockBoundary.sum_Ico_id a (b + 1) (by omega)
    rw [Finset.Ico_add_one_right_eq_Icc] at h
    have hcard := Int.card_Icc_of_le a b (by omega)
    have hcardC : ((Finset.Icc a b).card : ℂ) = (b : ℂ) + 1 - a := by
      exact_mod_cast hcard
    have hh : (2 : ℂ) * (∑ i ∈ Finset.Icc a b, (i : ℂ)) =
        ((a : ℂ) + b) * ((Finset.Icc a b).card : ℂ) := by
      push_cast at h
      rw [hcardC, h]
      ring
    apply Int.cast_injective (α := ℂ)
    push_cast
    exact hh
  · rw [Finset.Icc_eq_empty_of_lt (by omega)]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero]

private lemma hexagon_card (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    2 * ((hexagon p q).card : ℤ) = p^2 + 4*p*q + q^2 + 3*p + 3*q + 2 := by
  let r := fun i : ℤ => Finset.Icc (max (-q) (-q - i)) (min p (p - i))
  have hc : (hexagon p q).card = ((Finset.Icc (-q) p).sigma r).card := by
    apply Finset.card_bij (fun z _ => (⟨z.1, z.2⟩ : Σ _ : ℤ, ℤ))
    · rintro ⟨i, j⟩ hz
      have hb := (hexagon_mem p q i j).mp hz
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hb.1, hb.2.1⟩, ?_⟩
      change j ∈ Finset.Icc _ _
      rw [Finset.mem_Icc]
      dsimp only
      omega
    · intro z hz w hw he
      exact (Equiv.sigmaEquivProd ℤ ℤ).symm.injective he
    · rintro ⟨i, j⟩ hz
      obtain ⟨hi, hj⟩ := Finset.mem_sigma.mp hz
      change i ∈ Finset.Icc (-q) p at hi
      change j ∈ r i at hj
      have hi' := Finset.mem_Icc.mp hi
      have hj' := Finset.mem_Icc.mp hj
      refine ⟨(i, j), (hexagon_mem p q i j).mpr ?_, rfl⟩
      omega
  rw [Finset.card_sigma] at hc
  have hneg : Finset.Ico (-q) 0 = Finset.Icc (-q) (-1) := by
    simpa only [neg_add_cancel] using (Finset.Ico_add_one_right_eq_Icc (-q) (-1))
  have hu : Finset.Icc (-q) p = Finset.Icc (-q) (-1) ∪ Finset.Icc 0 p := by
    simpa only [hneg, Finset.Ico_add_one_right_eq_Icc] using
      (Finset.Ico_union_Ico_eq_Ico (a := -q) (b := 0) (c := p + 1)
        (by omega) (by omega)).symm
  have hd : Disjoint (Finset.Icc (-q) (-1)) (Finset.Icc (0 : ℤ) p) := by
    simpa only [hneg, Finset.Ico_add_one_right_eq_Icc] using
      (Finset.Ico_disjoint_Ico_consecutive (-q) 0 (p + 1))
  have hs : ((hexagon p q).card : ℤ) =
      ∑ i ∈ Finset.Icc (-q) (-1), (p + q + 1 + i) +
      ∑ i ∈ Finset.Icc 0 p, (p + q + 1 - i) := by
    rw [hc, Nat.cast_sum, hu, Finset.sum_union hd]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      dsimp only [r]
      rw [Int.card_Icc_of_le (max (-q) (-q - i)) (min p (p - i)) (by omega)]
      omega
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      dsimp only [r]
      rw [Int.card_Icc_of_le (max (-q) (-q - i)) (min p (p - i)) (by omega)]
      omega
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.sum_const] at hs
  simp only [nsmul_eq_mul] at hs
  have hn := twice_sum_interval (-q) (-1)
  have hp' := twice_sum_interval 0 p
  have cn := Int.card_Icc_of_le (-q) (-1) (by omega)
  have cp := Int.card_Icc_of_le 0 p (by omega)
  simp only [cn, cp] at hs hn hp'
  nlinarith

private lemma region_shell_zero (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    2 * ((regionShell p q 0).card : ℤ) = p ^ 2 + 4 * p * q + q ^ 2 + 3*p + 3*q + 2 := by
  have he : regionShell p q 0 = hexagon p q := by
    ext z
    rcases z with ⟨i, j⟩
    rw [region_shell_mem p q i j hp hq, hexagon_mem]
    have hn : 0 ≤ residual i j p q := le_max_left _ _
    rw [show residual i j p q = (0 : ℕ) ↔ residual i j p q ≤ 0 by omega,
      residual_le_iff]
    omega
  rw [he]
  exact hexagon_card p q hp hq

private lemma region_shell_pos (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (d : ℕ) (hd : 0 < d) :
    ((regionShell p q d).card : ℤ) = 3 * (p + q) + 6 * d := by
  have he : regionShell p q d =
      hexagon (p + d) (q + d) \ hexagon (p + d - 1) (q + d - 1) := by
    ext z
    rcases z with ⟨i, j⟩
    rw [region_shell_mem p q i j hp hq, Finset.mem_sdiff, hexagon_mem, hexagon_mem]
    have h0 := (residual_le_iff i j p q (d : ℤ))
    have h1 := (residual_le_iff i j p q ((d : ℤ) - 1))
    omega
  have hsub : hexagon (p + d - 1) (q + d - 1) ⊆ hexagon (p + d) (q + d) := by
    rintro ⟨i, j⟩ hz
    have hb := (hexagon_mem _ _ _ _).mp hz
    apply (hexagon_mem _ _ _ _).mpr
    omega
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  have hc' := congrArg (fun t : ℕ => (t : ℤ)) hc
  rw [← he, Nat.cast_add] at hc'
  have hbig := hexagon_card (p + d) (q + d) (by omega) (by omega)
  have hsmall := hexagon_card (p + d - 1) (q + d - 1) (by omega) (by omega)
  nlinarith

private lemma layer_sum (n : ℕ) :
    shell n = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card := by
  let t := (Finset.Icc (-(n : ℤ)) n).sigma
    (fun k => regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs))
  let f : (Σ _ : ℤ, ℤ × ℤ) → ℤ × ℤ × ℤ := fun z => (z.2.1, z.2.2, z.1)
  have hf : Function.Injective f :=
    ((Equiv.sigmaEquivProd ℤ (ℤ × ℤ)).trans
      ((Equiv.prodComm ℤ (ℤ × ℤ)).trans (Equiv.prodAssoc ℤ ℤ ℤ))).injective
  have hs : {v | teaGraph.dist (0, 0, 0) v = n} = (↑(t.image f) : Set _) := by
    ext v
    rcases v with ⟨i, j, k⟩
    change teaGraph.dist (0, 0, 0) (i, j, k) = n ↔ (i, j, k) ∈ t.image f
    rw [distance_formula]
    constructor
    · intro h
      have hpq := slabs_nonneg k
      have hr : 0 ≤ residual i j (plusSlabs k) (minusSlabs k) := le_max_left _ _
      have hb : k.natAbs ≤ n := by dsimp only [potential] at h; omega
      refine Finset.mem_image.mpr ⟨⟨k, i, j⟩, ?_, rfl⟩
      apply Finset.mem_sigma.mpr
      change k ∈ Finset.Icc (-(n : ℤ)) n ∧
        (i, j) ∈ regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      apply (region_shell_mem _ _ _ _ hpq.1 hpq.2 _).mpr
      dsimp only [potential] at h
      omega
    · intro h
      obtain ⟨⟨l, a, b⟩, ht, he⟩ := Finset.mem_image.mp h
      have he' : (a, b, l) = (i, j, k) := he
      have hi := congrArg (fun z : ℤ × ℤ × ℤ => z.1) he'
      have hj := congrArg (fun z : ℤ × ℤ × ℤ => z.2.1) he'
      have hk := congrArg (fun z : ℤ × ℤ × ℤ => z.2.2) he'
      dsimp only at hi hj hk
      subst a; subst b; subst l
      obtain ⟨hk, hr⟩ := Finset.mem_sigma.mp ht
      change k ∈ Finset.Icc (-(n : ℤ)) n at hk
      change (i, j) ∈ regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs) at hr
      have hk' := Finset.mem_Icc.mp hk
      have hpq := slabs_nonneg k
      have hr' := (region_shell_mem _ _ _ _ hpq.1 hpq.2 _).mp hr
      dsimp only [potential]
      omega
  change Set.ncard _ = _
  rw [hs, Set.ncard_coe_finset, Finset.card_image_of_injective t hf]
  exact Finset.card_sigma _ _

private lemma paired_slabs (m : ℕ) :
    plusSlabs m + minusSlabs m + plusSlabs (-(m : ℤ)) + minusSlabs (-(m : ℤ)) = m := by
  by_cases hm : m = 0
  · subst m; rfl
  · dsimp only [plusSlabs, minusSlabs]
    simp only [ite_eq_left (Nat.cast_nonneg m),
      ite_eq_right (not_le.mpr (Int.neg_neg_of_pos (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hm))))]
    have hsum := Int.sum_range_add_ediv (m : ℤ) (n := 4) (by decide)
    norm_num [Finset.sum_range_succ] at hsum
    simpa only [neg_neg, add_comm, add_left_comm, add_assoc] using hsum

private lemma weighted_layer_sum (n : ℕ) (hn : 0 < n) :
    8 * ((∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card : ℕ) : ℤ) =
      60*(n : ℤ)^2 + 4 *
        ((plusSlabs n)^2 + 4 * plusSlabs n * minusSlabs n + (minusSlabs n)^2 +
         (plusSlabs (-(n : ℤ)))^2 +
         4 * plusSlabs (-(n : ℤ)) * minusSlabs (-(n : ℤ)) +
         (minusSlabs (-(n : ℤ)))^2) + 16 := by
  let f : ℤ → ℤ := fun k =>
    ((regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card : ℤ)
  let w : ℕ := ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
    (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card
  let a := plusSlabs (n : ℤ)
  let b := minusSlabs (n : ℤ)
  let c := plusSlabs (-(n : ℤ))
  let e := minusSlabs (-(n : ℤ))
  let Q := a^2 + 4*a*b + b^2 + c^2 + 4*c*e + e^2
  have hs : ∀ m : ℕ, (∑ k ∈ Finset.Icc (-(m : ℤ)) m, f k) + f 0 =
      ∑ r ∈ Finset.range (m + 1), (f (r : ℤ) + f (-(r : ℤ))) := by
    intro m
    rw [D5.S1.Recurrence.Bilateral.HannaThetaFourModFour.symmetric_pair,
      Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, neg_add, sub_eq_add_neg,
      Nat.cast_zero, neg_zero]
    ac_rfl
  have hsmall : ∀ m ∈ Finset.range n, f (m : ℤ) + f (-(m : ℤ)) =
      12 * (n : ℤ) - 9 * m := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    have hp := slabs_nonneg (m : ℤ)
    have hq := slabs_nonneg (-(m : ℤ))
    dsimp only [f]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rw [region_shell_pos _ _ hp.1 hp.2 _ (by omega),
      region_shell_pos _ _ hq.1 hq.2 _ (by omega)]
    have hd : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Nat.cast_sub (by omega)
    rw [hd]
    have hsl := paired_slabs m
    omega
  have hzero : f 0 = 6 * n := by
    change ((regionShell 0 0 n).card : ℤ) = 6 * n
    simpa only [zero_add, mul_zero] using region_shell_pos 0 0 (by omega) (by omega) n hn
  have hend : 2 * (f (n : ℤ) + f (-(n : ℤ))) = Q + 3 * n + 4 := by
    have hp := slabs_nonneg (n : ℤ)
    have hq := slabs_nonneg (-(n : ℤ))
    have hp' := region_shell_zero _ _ hp.1 hp.2
    have hq' := region_shell_zero _ _ hq.1 hq.2
    have hsl := paired_slabs n
    dsimp only [f, Q, a, b, c, e]
    simp only [Int.natAbs_neg, Int.natAbs_natCast, Nat.sub_self]
    nlinarith only [hp', hq', hsl]
  have hsmallSum : (∑ m ∈ Finset.range n, (f (m : ℤ) + f (-(m : ℤ)))) =
      ∑ m ∈ Finset.range n, (12 * (n : ℤ) - 9 * m) := Finset.sum_congr rfl hsmall
  have hsum := hs n
  rw [Finset.sum_range_succ, hsmallSum, Finset.sum_sub_distrib, Finset.sum_const,
    ← Finset.mul_sum, hzero] at hsum
  simp only [Finset.card_range, nsmul_eq_mul] at hsum
  have hgauss : 2 * (∑ m ∈ Finset.range n, (m : ℤ)) = (n : ℤ) * (n - 1) := by
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat,
      Nat.cast_sub (Nat.one_le_of_lt hn), Nat.cast_one, mul_comm] using
      congrArg (fun t : ℕ => (t : ℤ)) (Finset.sum_range_id_mul_two n)
  have hmain : 2 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n, f k) = 15*(n : ℤ)^2 + Q + 4 := by
    nlinarith only [hsum, hend, hgauss]
  have hw : 8 * (w : ℤ) = 60*(n : ℤ)^2 + 4*Q + 16 := by
    dsimp only [w]
    rw [Nat.cast_sum]
    change 8 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n, f k) = _
    nlinarith only [hmain]
  exact hw

private lemma period_four_sum (n : ℕ) (hn : 0 < n) :
    (n % 4 = 0 →
      8 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card) = 63*n^2+16) ∧
    (n % 4 = 1 →
      8 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card) = 63*n^2+17) ∧
    (n % 4 = 2 →
      8 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card) = 63*n^2+12) ∧
    (n % 4 = 3 →
      8 * (∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card) = 63*n^2+17) := by
  let w : ℕ := ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
    (regionShell (plusSlabs k) (minusSlabs k) (n - k.natAbs)).card
  let a := plusSlabs (n : ℤ)
  let b := minusSlabs (n : ℤ)
  let c := plusSlabs (-(n : ℤ))
  let e := minusSlabs (-(n : ℤ))
  have hw := weighted_layer_sum n hn
  change 8 * (w : ℤ) = 60*(n : ℤ)^2 +
    4*(a^2 + 4*a*b + b^2 + c^2 + 4*c*e + e^2) + 16 at hw
  change (n % 4 = 0 → 8*w = 63*n^2+16) ∧
    (n % 4 = 1 → 8*w = 63*n^2+17) ∧
    (n % 4 = 2 → 8*w = 63*n^2+12) ∧
    (n % 4 = 3 → 8*w = 63*n^2+17)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hr
    have hm : (n : ℤ) % 4 = 0 := by exact_mod_cast hr
    let t : ℤ := (n : ℤ) / 4
    have ha : a = t + 0 := by
      dsimp only [a, t, plusSlabs]
      rw [ite_eq_left (Nat.cast_nonneg n)]
      omega
    have hb : b = t + 0 := by
      dsimp only [b, t, minusSlabs]
      rw [ite_eq_left (Nat.cast_nonneg n)]
      omega
    have hc : c = t + 0 := by
      dsimp only [c, t, plusSlabs]
      rw [ite_eq_right (not_le.mpr (Int.neg_neg_of_pos (Int.natCast_pos.mpr hn)))]
      omega
    have he : e = t + 0 := by
      dsimp only [e, t, minusSlabs]
      rw [ite_eq_right (not_le.mpr (Int.neg_neg_of_pos (Int.natCast_pos.mpr hn)))]
      omega
    have hn' : (n : ℤ) = 4*t + 0 := by dsimp only [t]; omega
    rw [ha, hb, hc, he] at hw
    have hgoal : 8 * (w : ℤ) = 63*(n : ℤ)^2 + 16 := by
      nlinarith only [hw, congrArg (fun z : ℤ => z^2) hn']
    exact_mod_cast hgoal
  · intro hr
    have hm : (n : ℤ) % 4 = 1 := by exact_mod_cast hr
    let t : ℤ := (n : ℤ) / 4
    have ha : a = t + 1 := by
      dsimp only [a, t, plusSlabs]
      rw [ite_eq_left (Nat.cast_nonneg n)]
      omega
    have hb : b = t + 0 := by
      dsimp only [b, t, minusSlabs]
      rw [ite_eq_left (Nat.cast_nonneg n)]
      omega
    have hc : c = t + 0 := by
      dsimp only [c, t, plusSlabs]
      rw [ite_eq_right (not_le.mpr (Int.neg_neg_of_pos (Int.natCast_pos.mpr hn)))]
      omega
    have he : e = t + 0 := by
      dsimp only [e, t, minusSlabs]
      rw [ite_eq_right (not_le.mpr (Int.neg_neg_of_pos (Int.natCast_pos.mpr hn)))]
      omega
    have hn' : (n : ℤ) = 4*t + 1 := by dsimp only [t]; omega
    rw [ha, hb, hc, he] at hw
    have hgoal : 8 * (w : ℤ) = 63*(n : ℤ)^2 + 17 := by
      nlinarith only [hw, congrArg (fun z : ℤ => z^2) hn']
    exact_mod_cast hgoal
  · intro hr
    have hm : (n : ℤ) % 4 = 2 := by exact_mod_cast hr
    let t : ℤ := (n : ℤ) / 4
    have ha : a = t + 1 := by
      dsimp only [a, t, plusSlabs]
      rw [ite_eq_left (Nat.cast_nonneg n)]
      omega
    have hb : b = t + 0 := by
      dsimp only [b, t, minusSlabs]
      rw [ite_eq_left (Nat.cast_nonneg n)]
      omega
    have hc : c = t + 1 := by
      dsimp only [c, t, plusSlabs]
      rw [ite_eq_right (not_le.mpr (Int.neg_neg_of_pos (Int.natCast_pos.mpr hn)))]
      omega
    have he : e = t + 0 := by
      dsimp only [e, t, minusSlabs]
      rw [ite_eq_right (not_le.mpr (Int.neg_neg_of_pos (Int.natCast_pos.mpr hn)))]
      omega
    have hn' : (n : ℤ) = 4*t + 2 := by dsimp only [t]; omega
    rw [ha, hb, hc, he] at hw
    have hgoal : 8 * (w : ℤ) = 63*(n : ℤ)^2 + 12 := by
      nlinarith only [hw, congrArg (fun z : ℤ => z^2) hn']
    exact_mod_cast hgoal
  · intro hr
    have hm : (n : ℤ) % 4 = 3 := by exact_mod_cast hr
    let t : ℤ := (n : ℤ) / 4
    have ha : a = t + 1 := by
      dsimp only [a, t, plusSlabs]
      rw [ite_eq_left (Nat.cast_nonneg n)]
      omega
    have hb : b = t + 1 := by
      dsimp only [b, t, minusSlabs]
      rw [ite_eq_left (Nat.cast_nonneg n)]
      omega
    have hc : c = t + 1 := by
      dsimp only [c, t, plusSlabs]
      rw [ite_eq_right (not_le.mpr (Int.neg_neg_of_pos (Int.natCast_pos.mpr hn)))]
      omega
    have he : e = t + 0 := by
      dsimp only [e, t, minusSlabs]
      rw [ite_eq_right (not_le.mpr (Int.neg_neg_of_pos (Int.natCast_pos.mpr hn)))]
      omega
    have hn' : (n : ℤ) = 4*t + 3 := by dsimp only [t]; omega
    rw [ha, hb, hc, he] at hw
    have hgoal : 8 * (w : ℤ) = 63*(n : ℤ)^2 + 17 := by
      nlinarith only [hw, congrArg (fun z : ℤ => z^2) hn']
    exact_mod_cast hgoal

theorem result : claim := by
  intro n hn
  rw [layer_sum n]
  exact period_four_sum n hn

end D5.S3.StatisticalMechanics.TeaCoordinationSequence
