/- GID: D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: An eight-point ultrametric realizes two prescribed auxiliary distances and exact sphere counts. -/

import D5.S3.Combinatorics.Geometry.UltrametricConstantJoin

/-! The parameterized eight-point construction from Proposition 2.1 of the
pinned proof. The two independent gap distances are `u` and `v`. -/
noncomputable section
namespace SphereCountSharpness
open ConstantCrossDistance
open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

private instance unitUltra : IsUltrametricDist PUnit := ⟨by intros; simp⟩

private theorem unitBound (w : ℝ) (hw : 0 < w) :
    ∀ (_ : Fin 2) (x y : PUnit), dist x y ≤ w := by
  intro i x y
  simpa using hw.le

abbrev Pair (w : ℝ) (hw : 0 < w) :=
  Join (fun _ : Fin 2 => PUnit) w hw (unitBound w hw)

theorem pair_dist_lt_one (w : ℝ) (hw : 0 < w) (hw1 : w < 1)
    (p q : Pair w hw) : dist p q < 1 := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  by_cases h : i = j
  · subst j
    simp
  · simpa [dist_cross _ _ _ _ h] using hw1

private theorem pairBound (w : ℝ) (hw : 0 < w) (hw1 : w < 1) :
    ∀ (_ : Fin 2) (p q : Pair w hw), dist p q ≤ (1 : ℝ) :=
  fun _ p q => (pair_dist_lt_one w hw hw1 p q).le

abbrev Block (w : ℝ) (hw : 0 < w) (hw1 : w < 1) :=
  Join (fun _ : Fin 2 => Pair w hw) 1 (by norm_num) (pairBound w hw hw1)

theorem block_dist_lt_two (w : ℝ) (hw : 0 < w) (hw1 : w < 1)
    (p q : Block w hw hw1) : dist p q < 2 := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  by_cases h : i = j
  · subst j
    rw [dist_same]
    exact lt_trans (pair_dist_lt_one w hw hw1 x y) (by norm_num)
  · rw [dist_cross _ _ _ _ h]
    norm_num

variable (u v : ℝ) (hu : 0 < u) (huv : u < v) (hv : v < 1)

private def weight (i : Fin 2) : ℝ := if i = 0 then u else v
private theorem weight_pos (hu : 0 < u) (huv : u < v) (i : Fin 2) : 0 < weight u v i := by
  unfold weight
  split
  · exact hu
  · exact hu.trans huv
private theorem weight_lt_one (huv : u < v) (hv : v < 1) (i : Fin 2) : weight u v i < 1 := by
  unfold weight
  split
  · exact huv.trans hv
  · exact hv

abbrev Blocks (i : Fin 2) :=
  Block (weight u v i) (weight_pos u v hu huv i) (weight_lt_one u v huv hv i)

private theorem blockBound : ∀ (i : Fin 2) (p q : Blocks u v hu huv hv i),
    dist p q ≤ (2 : ℝ) :=
  fun _ p q => (block_dist_lt_two _ _ _ p q).le

/-- Two four-point blocks, each made of two two-point pairs. -/
abbrev Eight := Join (Blocks u v hu huv hv) 2 (by norm_num) (blockBound u v hu huv hv)

theorem pair_card (w : ℝ) (hw : 0 < w) : Nat.card (Pair w hw) = 2 := by
  rw [card_join_sum]
  norm_num

theorem block_card (w : ℝ) (hw : 0 < w) (hw1 : w < 1) :
    Nat.card (Block w hw hw1) = 4 := by
  rw [card_join_sum]
  simp [pair_card]

theorem eight_card : Nat.card (Eight u v hu huv hv) = 8 := by
  rw [card_join_sum]
  simp [Blocks, block_card]

theorem sphere_zero_card (p : Eight u v hu huv hv) :
    Nat.card (Metric.sphere p 0) = 1 := by
  simp [Metric.sphere, dist_eq_zero]

theorem sphere_one_card (p : Eight u v hu huv hv) :
    Nat.card (Metric.sphere p 1) = 2 := by
  rcases p with ⟨i, ⟨j, x⟩⟩
  rw [sphere_card _ _ _ _ i _ (by norm_num)]
  rw [sphere_top_card (fun _ : Fin 2 => Pair (weight u v i) (weight_pos u v hu huv i))
    1 (by norm_num) (pairBound _ _ (weight_lt_one u v huv hv i))
    (fun _ p q => pair_dist_lt_one _ _ (weight_lt_one u v huv hv i) p q)]
  rw [block_card _ _ (weight_lt_one u v huv hv i), pair_card]

theorem sphere_two_card (p : Eight u v hu huv hv) :
    Nat.card (Metric.sphere p 2) = 4 := by
  rcases p with ⟨i, x⟩
  rw [sphere_top_card (Blocks u v hu huv hv) 2 (by norm_num)
    (blockBound u v hu huv hv) (fun _ p q => block_dist_lt_two _ _ _ p q)]
  rw [eight_card u v hu huv hv, block_card]

private theorem pair_values (w : ℝ) (hw : 0 < w) (p q : Pair w hw) :
    dist p q = 0 ∨ dist p q = w := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  by_cases h : i = j
  · subst j
    left
    simp
  · right
    exact dist_cross (fun _ : Fin 2 => PUnit) w hw (unitBound w hw) h x y

private theorem block_values (w : ℝ) (hw : 0 < w) (hw1 : w < 1)
    (p q : Block w hw hw1) :
    dist p q = 0 ∨ dist p q = w ∨ dist p q = 1 := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  by_cases h : i = j
  · subst j
    rw [dist_same]
    exact (pair_values w hw x y).imp_right Or.inl
  · exact Or.inr (Or.inr (dist_cross (fun _ : Fin 2 => Pair w hw)
      1 (by norm_num) (pairBound w hw hw1) h x y))

/-- The eight-point model has exactly the prescribed center, for every
choice of two fixed gap distances `0 < u < v < 1`. -/
theorem eight_center : center (Eight u v hu huv hv) = ({0, 1, 2} : Set ℝ) := by
  ext t
  constructor
  · intro ht
    by_cases ht2 : t = 2
    · simp [ht2]
    · have hc := (mem_center_iff _ _ _ _ ht2).mp ht
      obtain ⟨p, hp⟩ := (hc.2 (0 : Fin 2)).2 ⟨0, ⟨0, PUnit.unit⟩⟩
      obtain ⟨q, hq⟩ := (hc.2 (1 : Fin 2)).2 ⟨0, ⟨0, PUnit.unit⟩⟩
      have hpu := block_values _ _ _ p (⟨0, ⟨0, PUnit.unit⟩⟩)
      have hqv := block_values _ _ _ q (⟨0, ⟨0, PUnit.unit⟩⟩)
      rw [hp] at hpu
      rw [hq] at hqv
      change t = 0 ∨ t = weight u v 0 ∨ t = 1 at hpu
      change t = 0 ∨ t = weight u v 1 ∨ t = 1 at hqv
      norm_num [weight] at hpu hqv
      rcases hpu with h | h | h
      · simp [h]
      · rcases hqv with h' | h' | h'
        · simp [h']
        · exact (huv.ne (h.symm.trans h')).elim
        · simp [h']
      · simp [h]
  · intro ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · refine ⟨le_rfl, fun p => ?_⟩
      have hn : 0 < Nat.card (Metric.sphere p 0) := by
        rw [sphere_zero_card u v hu huv hv p]
        norm_num
      obtain ⟨y⟩ := (Nat.card_pos_iff.mp hn).1
      exact ⟨y.val, y.property⟩
    · refine ⟨by norm_num, fun p => ?_⟩
      have hn : 0 < Nat.card (Metric.sphere p 1) := by
        rw [sphere_one_card u v hu huv hv p]
        norm_num
      obtain ⟨y⟩ := (Nat.card_pos_iff.mp hn).1
      exact ⟨y.val, y.property⟩
    · refine ⟨by norm_num, fun p => ?_⟩
      have hn : 0 < Nat.card (Metric.sphere p 2) := by
        rw [sphere_two_card u v hu huv hv p]
        norm_num
      obtain ⟨y⟩ := (Nat.card_pos_iff.mp hn).1
      exact ⟨y.val, y.property⟩

/-- No extra distance in either gap is introduced by the construction. -/
theorem distance_values (p q : Eight u v hu huv hv) :
    dist p q ∈ ({0, u, v, 1, 2} : Set ℝ) := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  by_cases h : i = j
  · subst j
    rw [dist_same]
    have hd := block_values _ _ (weight_lt_one u v huv hv i) x y
    rcases hd with hd | hd | hd
    · simp [hd]
    · rw [hd]
      fin_cases i <;> simp [weight]
    · simp [hd]
  · rw [dist_cross _ _ _ _ h]
    simp

end SphereCountSharpness
