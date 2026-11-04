/- GID: D5/S3/StatisticalMechanics/TsiCoordinationSequence
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/TsiCoordinationSequence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barker's coordination sequence formulas for the alternating prism tiling tsi. -/

import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-! The alternating prism graph, its exact metric, and its coordination sequence. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.TsiCoordinationSequence

/-- The square layers and the alternating triangular prism slabs of the tsi net. -/
def tsiGraph : SimpleGraph (ℤ × ℤ × ℤ) where
  Adj u v :=
    (u.2.2 = v.2.2 ∧ u.2.1 = v.2.1 ∧ (u.1 = v.1 + 1 ∨ v.1 = u.1 + 1)) ∨
    (u.2.2 = v.2.2 ∧ u.1 = v.1 ∧ (u.2.1 = v.2.1 + 1 ∨ v.2.1 = u.2.1 + 1)) ∨
    (v.2.2 = u.2.2 + 1 ∧
      ((v.1 = u.1 ∧ v.2.1 = u.2.1) ∨
       (Even u.2.2 ∧ v.1 = u.1 + 1 ∧ v.2.1 = u.2.1) ∨
       (Odd u.2.2 ∧ v.1 = u.1 ∧ v.2.1 = u.2.1 + 1))) ∨
    (u.2.2 = v.2.2 + 1 ∧
      ((u.1 = v.1 ∧ u.2.1 = v.2.1) ∨
       (Even v.2.2 ∧ u.1 = v.1 + 1 ∧ u.2.1 = v.2.1) ∨
       (Odd v.2.2 ∧ u.1 = v.1 ∧ u.2.1 = v.2.1 + 1)))
  symm := ⟨by
    intro u v h
    rcases h with h | h | h | h
    · exact Or.inl ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
    · exact Or.inr (Or.inl ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by
    intro u h
    rcases h with h | h | h | h <;> omega⟩

/-- The coordination sequence, counted at the representative origin. -/
def shell (n : ℕ) : ℕ := Set.ncard {v | tsiGraph.dist (0, 0, 0) v = n}

def claim : Prop :=
  (∀ n : ℕ, 0 < n → Even n → 2 * shell n = 13 * n ^ 2 + 4) ∧
  (∀ n : ℕ, Odd n → 2 * shell n = 13 * n ^ 2 + 3)

private def gap (c i : ℤ) : ℕ :=
  (min 0 c - i).toNat + (i - max 0 c).toNat

private def potential (v : ℤ × ℤ × ℤ) : ℕ :=
  v.2.2.natAbs + gap ((v.2.2 + 1) / 2) v.1 + gap (v.2.2 / 2) v.2.1

private lemma potential_zero : potential (0, 0, 0) = 0 := by
  rfl

private lemma gap_horizontal (c i : ℤ) :
    gap c i ≤ gap c (i + 1) + 1 ∧ gap c (i + 1) ≤ gap c i + 1 := by
  dsimp only [gap]
  omega

private lemma gap_slab (c i d : ℤ) (hd : d = 0 ∨ d = 1) :
    (c.natAbs + gap c i ≤ (c + 1).natAbs + gap (c + 1) (i + d) + 1) ∧
    ((c + 1).natAbs + gap (c + 1) (i + d) ≤ c.natAbs + gap c i + 1) := by
  rcases hd with rfl | rfl <;> by_cases hc : 0 ≤ c <;> dsimp only [gap] <;> omega

private lemma potential_split (v : ℤ × ℤ × ℤ) :
    potential v = (((v.2.2 + 1) / 2).natAbs + gap ((v.2.2 + 1) / 2) v.1) +
      ((v.2.2 / 2).natAbs + gap (v.2.2 / 2) v.2.1) := by
  dsimp only [potential]
  omega

private lemma potential_slab (i j k a b : ℤ)
    (h : (a = i ∧ b = j) ∨ (Even k ∧ a = i + 1 ∧ b = j) ∨
      (Odd k ∧ a = i ∧ b = j + 1)) :
    (potential (i, j, k) ≤ potential (a, b, k + 1) + 1) ∧
    (potential (a, b, k + 1) ≤ potential (i, j, k) + 1) := by
  rcases Int.even_or_odd k with he | ho
  · have hy : (k + 1) / 2 = k / 2 := by
      simpa only [Int.ediv_eq_zero_of_lt (by decide : (0 : ℤ) ≤ 1)
        (by decide : (1 : ℤ) < 2), add_zero] using
        (@Int.add_ediv_of_dvd_left k 1 2 (even_iff_two_dvd.mp he))
    have hx : (k + 1 + 1) / 2 = (k + 1) / 2 + 1 := by
      simpa only [add_assoc, one_add_one_eq_two,
        Int.ediv_self (by decide : (2 : ℤ) ≠ 0), hy] using
        (@Int.add_ediv_of_dvd_right k 2 2 (dvd_refl 2))
    rw [potential_split, potential_split]
    dsimp only
    rw [hx]
    rcases h with ⟨ha, hb⟩ | ⟨he, ha, hb⟩ | ⟨ho, ha, hb⟩
    · subst a; subst b
      have hg := gap_slab ((k + 1) / 2) i 0 (Or.inl rfl)
      simp only [add_zero] at hg
      rw [hy] at hg ⊢
      omega
    · subst a; subst b
      have hg := gap_slab ((k + 1) / 2) i 1 (Or.inr rfl)
      rw [hy] at hg ⊢
      omega
    · exact ((Int.not_odd_iff_even.mpr he) ho).elim
  · have hx : (k + 1 + 1) / 2 = (k + 1) / 2 := by
      simpa only [Int.ediv_eq_zero_of_lt (by decide : (0 : ℤ) ≤ 1)
        (by decide : (1 : ℤ) < 2), add_zero] using
        (@Int.add_ediv_of_dvd_left (k + 1) 1 2
          (even_iff_two_dvd.mp (Int.even_add_one.mpr (Int.not_even_iff_odd.mpr ho))))
    have hy : (k + 1) / 2 = k / 2 + 1 := by
      rw [← hx]
      simpa only [add_assoc, one_add_one_eq_two,
        Int.ediv_self (by decide : (2 : ℤ) ≠ 0)] using
        (@Int.add_ediv_of_dvd_right k 2 2 (dvd_refl 2))
    rw [potential_split, potential_split]
    dsimp only
    rw [hx]
    rcases h with ⟨ha, hb⟩ | ⟨he, ha, hb⟩ | ⟨ho, ha, hb⟩
    · subst a; subst b
      have hg := gap_slab (k / 2) j 0 (Or.inl rfl)
      simp only [add_zero] at hg
      rw [hy]
      omega
    · exact ((Int.not_odd_iff_even.mpr he) ho).elim
    · subst a; subst b
      have hg := gap_slab (k / 2) j 1 (Or.inr rfl)
      rw [hy]
      omega

private lemma potential_step (u v : ℤ × ℤ × ℤ) (h : tsiGraph.Adj u v) :
    potential u ≤ potential v + 1 := by
  rcases u with ⟨i, j, k⟩
  rcases v with ⟨a, b, l⟩
  change _ ∨ _ ∨ _ ∨ _ at h
  dsimp only at h
  rcases h with ⟨hk, hj, hi⟩ | ⟨hk, hi, hj⟩ | ⟨hk, h⟩ | ⟨hk, h⟩
  · subst l; subst b
    rcases hi with hi | hi
    · subst i
      have hg := (gap_horizontal ((k + 1) / 2) a).2
      dsimp only [potential]; omega
    · subst a
      have hg := (gap_horizontal ((k + 1) / 2) i).1
      dsimp only [potential]; omega
  · subst l; subst a
    rcases hj with hj | hj
    · subst j
      have hg := (gap_horizontal (k / 2) b).2
      dsimp only [potential]; omega
    · subst b
      have hg := (gap_horizontal (k / 2) j).1
      dsimp only [potential]; omega
  · subst l
    exact (potential_slab i j k a b h).1
  · subst k
    exact (potential_slab a b l i j h).2

private lemma inside_potential (i j k : ℤ)
    (hi : min 0 ((k + 1) / 2) ≤ i ∧ i ≤ max 0 ((k + 1) / 2))
    (hj : min 0 (k / 2) ≤ j ∧ j ≤ max 0 (k / 2)) :
    potential (i, j, k) = k.natAbs := by
  dsimp only [potential, gap]
  omega

private lemma descent_even (i j k : ℤ) (hk : k ≠ 0)
    (hi : min 0 ((k + 1) / 2) ≤ i ∧ i ≤ max 0 ((k + 1) / 2))
    (hj : min 0 (k / 2) ≤ j ∧ j ≤ max 0 (k / 2)) (he : Even k) :
    ∃ u, tsiGraph.Adj u (i, j, k) ∧ potential u + 1 = potential (i, j, k) := by
  obtain ⟨t, ht⟩ := he
  by_cases hk' : 0 < k
  · by_cases hb : j = k / 2
    · refine ⟨(i, j - 1, k - 1), ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by (try dsimp only); omega,
          Or.inr (Or.inr ⟨⟨t - 1, by dsimp only; omega⟩,
            rfl, by dsimp only; omega⟩)⟩))
      · rw [inside_potential _ _ _ (by constructor <;> omega) (by constructor <;> omega),
          inside_potential i j k hi hj]
        omega
    · refine ⟨(i, j, k - 1), ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by (try dsimp only); omega, Or.inl ⟨rfl, rfl⟩⟩))
      · rw [inside_potential _ _ _ (by constructor <;> omega) (by constructor <;> omega),
          inside_potential i j k hi hj]
        omega
  · by_cases hb : i = (k + 1) / 2
    · refine ⟨(i + 1, j, k + 1), ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl,
          Or.inr (Or.inl ⟨⟨t, ht⟩, rfl, rfl⟩)⟩))
      · rw [inside_potential _ _ _ (by constructor <;> omega) (by constructor <;> omega),
          inside_potential i j k hi hj]
        omega
    · refine ⟨(i, j, k + 1), ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))
      · rw [inside_potential _ _ _ (by constructor <;> omega) (by constructor <;> omega),
          inside_potential i j k hi hj]
        omega

private lemma descent_odd (i j k : ℤ)
    (hi : min 0 ((k + 1) / 2) ≤ i ∧ i ≤ max 0 ((k + 1) / 2))
    (hj : min 0 (k / 2) ≤ j ∧ j ≤ max 0 (k / 2)) (ho : Odd k) :
    ∃ u, tsiGraph.Adj u (i, j, k) ∧ potential u + 1 = potential (i, j, k) := by
  obtain ⟨t, ht⟩ := ho
  by_cases hk' : 0 < k
  · by_cases hb : i = (k + 1) / 2
    · refine ⟨(i - 1, j, k - 1), ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by (try dsimp only); omega,
          Or.inr (Or.inl ⟨⟨t, by (try dsimp only); omega⟩, by omega, rfl⟩)⟩))
      · rw [inside_potential _ _ _ (by constructor <;> omega) (by constructor <;> omega),
          inside_potential i j k hi hj]
        omega
    · refine ⟨(i, j, k - 1), ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by (try dsimp only); omega, Or.inl ⟨rfl, rfl⟩⟩))
      · rw [inside_potential _ _ _ (by constructor <;> omega) (by constructor <;> omega),
          inside_potential i j k hi hj]
        omega
  · by_cases hb : j = k / 2
    · refine ⟨(i, j + 1, k + 1), ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl,
          Or.inr (Or.inr ⟨⟨t, ht⟩, rfl, rfl⟩)⟩))
      · rw [inside_potential _ _ _ (by constructor <;> omega) (by constructor <;> omega),
          inside_potential i j k hi hj]
        omega
    · refine ⟨(i, j, k + 1), ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))
      · rw [inside_potential _ _ _ (by constructor <;> omega) (by constructor <;> omega),
          inside_potential i j k hi hj]
        omega

private lemma potential_descent (v : ℤ × ℤ × ℤ) (h : 0 < potential v) :
    ∃ u, tsiGraph.Adj u v ∧ potential u + 1 = potential v := by
  rcases v with ⟨i, j, k⟩
  by_cases hi : i < min 0 ((k + 1) / 2)
  · refine ⟨(i + 1, j, k), Or.inl ⟨rfl, rfl, Or.inl rfl⟩, ?_⟩
    dsimp only [potential, gap]; omega
  by_cases hi' : max 0 ((k + 1) / 2) < i
  · refine ⟨(i - 1, j, k),
      Or.inl ⟨rfl, rfl, Or.inr (by dsimp only; omega)⟩, ?_⟩
    dsimp only [potential, gap]; omega
  by_cases hj : j < min 0 (k / 2)
  · refine ⟨(i, j + 1, k), Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩), ?_⟩
    dsimp only [potential, gap]; omega
  by_cases hj' : max 0 (k / 2) < j
  · refine ⟨(i, j - 1, k),
      Or.inr (Or.inl ⟨rfl, rfl, Or.inr (by dsimp only; omega)⟩), ?_⟩
    dsimp only [potential, gap]; omega
  have hk : k ≠ 0 := by
    dsimp only [potential, gap] at h
    omega
  rcases Int.even_or_odd k with he | ho
  · exact descent_even i j k hk ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
  · exact descent_odd i j k ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ho

private lemma geodesic (v : ℤ × ℤ × ℤ) :
    ∃ p : tsiGraph.Walk (0, 0, 0) v, p.length = potential v := by
  generalize ht : potential v = t
  induction t using Nat.strong_induction_on generalizing v with
  | h t ih =>
    by_cases hz : t = 0
    · have hv : v = (0, 0, 0) := by
        rcases v with ⟨i, j, k⟩
        dsimp only [potential, gap] at ht
        have hk : k = 0 := by omega
        subst k
        have hi : i = 0 := by omega
        have hj : j = 0 := by omega
        subst i; subst j; rfl
      subst v
      exact ⟨.nil, by simpa only [SimpleGraph.Walk.length_nil] using hz.symm⟩
    · obtain ⟨u, hu, hp⟩ := potential_descent v (by omega)
      obtain ⟨p, hl⟩ := ih (potential u) (by omega) u rfl
      refine ⟨p.append hu.toWalk, ?_⟩
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk, hl, hp]
      exact ht

private lemma distance_formula (v : ℤ × ℤ × ℤ) :
    tsiGraph.dist (0, 0, 0) v = potential v := by
  obtain ⟨p, hp⟩ := geodesic v
  apply le_antisymm
  · simpa only [hp] using SimpleGraph.dist_le p
  · have hl := D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation.potential_dist
      tsiGraph potential potential_step (SimpleGraph.Reachable.symm ⟨p⟩)
    simpa only [potential_zero, zero_add, SimpleGraph.dist_comm] using hl

private def intervalShell (c : ℤ) (d : ℕ) : Finset ℤ :=
  (Finset.Icc (min 0 c - d) (max 0 c + d)).filter (fun i => gap c i = d)

private lemma interval_shell_mem (c i : ℤ) (d : ℕ) :
    i ∈ intervalShell c d ↔ gap c i = d := by
  change i ∈ (Finset.Icc (min 0 c - d) (max 0 c + d)).filter (fun z => gap c z = d) ↔ _
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact And.right
  · intro h
    exact ⟨by dsimp only [gap] at h; omega, h⟩

private lemma interval_shell_card (c : ℤ) (d : ℕ) :
    (intervalShell c d).card = if d = 0 then c.natAbs + 1 else 2 := by
  by_cases hd : d = 0
  · subst d
    have hs : intervalShell c 0 = Finset.Icc (min 0 c) (max 0 c) := by
      ext i
      rw [interval_shell_mem, Finset.mem_Icc]
      dsimp only [gap]
      omega
    rw [hs, Int.card_Icc, ite_eq_left rfl]
    omega
  · have hs : intervalShell c d = {min 0 c - d, max 0 c + d} := by
      ext i
      rw [interval_shell_mem]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      dsimp only [gap]
      omega
    rw [hs, ite_eq_right hd, Finset.card_pair (by omega)]

private def rectangleShell (c e : ℤ) (d : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (d + 1)).biUnion
    (fun t => (intervalShell c t) ×ˢ (intervalShell e (d - t)))

private lemma rectangle_shell_mem (c e i j : ℤ) (d : ℕ) :
    (i, j) ∈ rectangleShell c e d ↔ gap c i + gap e j = d := by
  change (i, j) ∈ (Finset.range (d + 1)).biUnion
    (fun t => intervalShell c t ×ˢ intervalShell e (d - t)) ↔ _
  simp only [Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_product, interval_shell_mem]
  constructor
  · rintro ⟨t, ht, hx, hy⟩
    omega
  · intro h
    exact ⟨gap c i, by omega, rfl, by omega⟩

private lemma rectangle_shell_card_zero (c e : ℤ) :
    (rectangleShell c e 0).card = (c.natAbs + 1) * (e.natAbs + 1) := by
  change ((Finset.range (0 + 1)).biUnion
    (fun t => intervalShell c t ×ˢ intervalShell e (0 - t))).card = _
  simp only [Nat.zero_add, Finset.range_one, Finset.singleton_biUnion,
    Nat.sub_zero, Finset.card_product, interval_shell_card, ite_true]

private lemma rectangle_shell_card_pos (c e : ℤ) (d : ℕ) (hd : 0 < d) :
    (rectangleShell c e d).card = 2 * (c.natAbs + e.natAbs) + 4 * d := by
  have hdis : (↑(Finset.range (d + 1)) : Set ℕ).PairwiseDisjoint
      (fun t => (intervalShell c t) ×ˢ (intervalShell e (d - t))) := by
    rw [← Finset.pairwiseDisjoint_coe]
    exact (Set.pairwiseDisjoint_fiber (fun p : ℤ × ℤ => gap c p.1)
      (↑(Finset.range (d + 1)) : Set ℕ)).mono
      (fun t p hp => (interval_shell_mem c p.1 t).mp (Finset.mem_product.mp hp).1)
  change ((Finset.range (d + 1)).biUnion _).card = _
  rw [Finset.card_biUnion hdis]
  simp only [Finset.card_product, interval_shell_card]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hm : (∑ i ∈ Finset.range r,
      (if i + 1 = 0 then c.natAbs + 1 else 2) *
      (if r + 1 - (i + 1) = 0 then e.natAbs + 1 else 2)) = 4 * r := by
    calc
      _ = ∑ _i ∈ Finset.range r, 4 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      _ = 4 * r := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; omega
  rw [hm]
  simp only [Nat.succ_ne_zero, ite_false, Nat.sub_self, ite_true,
    Nat.sub_zero, Nat.succ_eq_add_one]
  ring

private lemma layer_sum (n : ℕ) :
    shell n = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
      (rectangleShell ((k + 1) / 2) (k / 2) (n - k.natAbs)).card := by
  let f := fun k : ℤ =>
    (rectangleShell ((k + 1) / 2) (k / 2) (n - k.natAbs)).image
      (fun p => (p.1, p.2, k))
  let s := (Finset.Icc (-(n : ℤ)) n).biUnion f
  have hs : {v | tsiGraph.dist (0, 0, 0) v = n} = (s : Set (ℤ × ℤ × ℤ)) := by
    ext v
    rcases v with ⟨i, j, k⟩
    simp only [Set.mem_ofPred_eq, distance_formula, Finset.mem_coe]
    constructor
    · intro h
      have hb : k.natAbs ≤ n := by dsimp only [potential] at h; omega
      apply Finset.mem_biUnion.mpr
      refine ⟨k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(i, j), ?_, rfl⟩
      apply (rectangle_shell_mem _ _ _ _ _).mpr
      dsimp only [potential] at h
      omega
    · intro h
      obtain ⟨l, hl, hp⟩ := Finset.mem_biUnion.mp h
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hp
      have hl' := Finset.mem_Icc.mp hl
      have hk : l = k := congrArg (fun v : ℤ × ℤ × ℤ => v.2.2) heq
      subst l
      have hi : p.1 = i := congrArg (fun v : ℤ × ℤ × ℤ => v.1) heq
      have hj : p.2 = j := congrArg (fun v : ℤ × ℤ × ℤ => v.2.1) heq
      have hp' := (rectangle_shell_mem _ _ _ _ _).mp hp
      rw [hi, hj] at hp'
      dsimp only [potential]
      omega
  change Set.ncard _ = _
  rw [hs, Set.ncard_coe_finset]
  have hdis : (↑(Finset.Icc (-(n : ℤ)) n) : Set ℤ).PairwiseDisjoint f := by
    rw [← Finset.pairwiseDisjoint_coe]
    apply (Set.pairwiseDisjoint_fiber (fun v : ℤ × ℤ × ℤ => v.2.2)
      (↑(Finset.Icc (-(n : ℤ)) n) : Set ℤ)).mono
    intro k v hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    rfl
  change ((Finset.Icc (-(n : ℤ)) n).biUnion f).card = _
  rw [Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro k hk
  exact Finset.card_image_of_injective _
    (Function.injective_id.prodMap (Prod.mk_left_injective k))

private lemma stack_sum (n : ℕ) (hn : 0 < n) :
    shell n + 2 * n = 6 * n ^ 2 +
      2 * ((n / 2 + 1) * ((n + 1) / 2 + 1)) := by
  let b := (n / 2 + 1) * ((n + 1) / 2 + 1)
  let f : ℤ → ℤ := fun k => if k.natAbs = n then (b : ℤ) else
    4 * (n : ℤ) - 2 * (k.natAbs : ℤ)
  have hv : ∀ k ∈ Finset.Icc (-(n : ℤ)) n,
      ((rectangleShell ((k + 1) / 2) (k / 2) (n - k.natAbs)).card : ℤ) = f k := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hab : ((k + 1) / 2).natAbs + (k / 2).natAbs = k.natAbs := by omega
    by_cases he : k.natAbs = n
    · have hz : n - k.natAbs = 0 := Nat.sub_eq_zero_of_le he.ge
      rw [hz, rectangle_shell_card_zero]
      change _ = if k.natAbs = n then (b : ℤ) else _
      rw [ite_eq_left he]
      have hp : (((k + 1) / 2).natAbs + 1) * ((k / 2).natAbs + 1) = b := by
        by_cases hk0 : 0 ≤ k
        · have hx : ((k + 1) / 2).natAbs = (n + 1) / 2 := by omega
          have hy : (k / 2).natAbs = n / 2 := by omega
          rw [hx, hy]
          dsimp only [b]
          ring
        · have hx : ((k + 1) / 2).natAbs = n / 2 := by omega
          have hy : (k / 2).natAbs = (n + 1) / 2 := by omega
          rw [hx, hy]
      exact_mod_cast hp
    · have hd : 0 < n - k.natAbs := by omega
      rw [rectangle_shell_card_pos _ _ _ hd]
      change _ = if k.natAbs = n then _ else _
      rw [ite_eq_right he]
      rw [hab]
      have ht : ((n - k.natAbs : ℕ) : ℤ) = (n : ℤ) - k.natAbs :=
        Nat.cast_sub (by omega)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ht]
      ring
  have hs : (shell n : ℤ) = ∑ k ∈ Finset.Icc (-(n : ℤ)) n, f k := by
    rw [layer_sum, Nat.cast_sum]
    exact Finset.sum_congr rfl hv
  have heven : f.Even := by
    intro k
    dsimp only [f]
    rw [Int.natAbs_neg]
  have hsum := Finset.sum_Icc_of_even_eq_range heven n
  have hf0 : f 0 = 4 * n := by
    dsimp only [f]
    rw [Int.natAbs_zero, ite_eq_right (by omega)]
    ring
  have hfn : f (n : ℤ) = b := by
    dsimp only [f]
    rw [Int.natAbs_natCast, ite_eq_left rfl]
  have hsmall : ∑ m ∈ Finset.range n, f (m : ℤ) =
      ∑ m ∈ Finset.range n, (4 * (n : ℤ) - 2 * (m : ℤ)) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hm' := Finset.mem_range.mp hm
    dsimp only [f]
    rw [Int.natAbs_natCast, ite_eq_right (by omega)]
  have hgauss : 2 * (∑ m ∈ Finset.range n, (m : ℤ)) = (n : ℤ) * (n - 1) := by
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat,
      Nat.cast_sub (Nat.one_le_of_lt hn), Nat.cast_one, mul_comm] using
      congrArg (fun t : ℕ => (t : ℤ)) (Finset.sum_range_id_mul_two n)
  rw [Finset.sum_range_succ, hfn, hsmall] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    ← Finset.mul_sum] at hsum
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hsum
  rw [hf0] at hsum
  have hmain : (shell n : ℤ) + 2 * n = 6 * (n : ℤ) ^ 2 + 2 * b := by
    rw [hs, hsum]
    nlinarith
  exact_mod_cast hmain

private lemma even_formula (n : ℕ) (hn : 0 < n) (he : Even n) :
    2 * shell n = 13 * n ^ 2 + 4 := by
  obtain ⟨t, ht⟩ := he
  have hs := stack_sum n hn
  have ha : n / 2 = t := by
    simpa only [ht, two_mul] using Nat.mul_div_cancel_left t (by decide : 0 < 2)
  have hb : (n + 1) / 2 = t := by
    rw [ht, ← two_mul, Nat.mul_add_div (by decide : 0 < 2)]
    rfl
  rw [ha, hb] at hs
  nlinarith

private lemma odd_formula (n : ℕ) (ho : Odd n) :
    2 * shell n = 13 * n ^ 2 + 3 := by
  obtain ⟨t, ht⟩ := ho
  have hs := stack_sum n (by omega)
  have ha : n / 2 = t := by
    rw [ht, Nat.mul_add_div (by decide : 0 < 2)]
    rfl
  have hb : (n + 1) / 2 = t + 1 := by
    rw [ht, add_assoc, one_add_one_eq_two, Nat.mul_add_div (by decide : 0 < 2)]
    rfl
  rw [ha, hb] at hs
  nlinarith

theorem result : claim := ⟨even_formula, odd_formula⟩

end D5.S3.StatisticalMechanics.TsiCoordinationSequence
