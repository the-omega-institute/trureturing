/- GID: D5/S3/Combinatorics/Geometry/UltrametricCenterSphereSharpness
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: The counts (1, 2, 4) at radii (0, 1, 2) force order eight and two distinct distances below one. -/

import D5.S3.Combinatorics.Geometry.UltrametricCenterSphereOrders
import D5.S3.Combinatorics.Geometry.UltrametricCenterSphereEight

/-! Proposition 2.1 of the pinned written proof of #29039. -/

noncomputable section

namespace SphereCountSharpness

open Metric UltrametricCenterSphereOrders
open scoped BigOperators
open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

private def radii : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | _ => 2

private def counts : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | _ => 4

private theorem radii_strict : ∀ j < 2, radii j < radii (j + 1) := by
  intro j hj
  interval_cases j <;> norm_num [radii]

private theorem radii_image : radii '' Set.Iic 2 = ({0, 1, 2} : Set ℝ) := by
  ext d
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j ≤ 2 := hj
    interval_cases j <;> simp [radii]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · exact ⟨0, Set.mem_Iic.mpr (by decide), rfl⟩
    · exact ⟨1, Set.mem_Iic.mpr (by decide), rfl⟩
    · exact ⟨2, Set.mem_Iic.mpr (by decide), rfl⟩

private theorem orders_one : orders counts 1 = ({3, 4} : Set ℕ) := by
  ext n
  constructor
  · intro hn
    obtain ⟨t, hp, ht, _, hdiv, he⟩ :=
      (mem_orders_succ_iff_bounded counts 0 n (by decide)).mp hn
    change t ≤ 2 at ht
    change n = 2 + t at he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨1, ⟨0, fun _ => 1, by simp [orders], by simp⟩, by decide, rfl⟩
    · exact ⟨2, ⟨1, fun _ => 1, by simp [orders], by simp⟩, by decide, rfl⟩

private theorem orders_two : orders counts 2 = ({8} : Set ℕ) := by
  ext n
  constructor
  · intro hn
    obtain ⟨t, _, ht, ⟨k, s, hs, he⟩, ⟨m, hm⟩, hn'⟩ :=
      (mem_orders_succ_iff_bounded counts 1 n (by decide)).mp hn
    have hlo : 3 ≤ s 0 := by
      have h := hs 0
      rw [orders_one] at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      omega
    have hle : s 0 ≤ ∑ j, s j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (s j)) (Finset.mem_univ 0)
    change t ≤ 4 at ht
    change 4 = t * m at hm
    change n = 4 + t at hn'
    have ht' : t = 4 := by
      by_contra! h
      have h3 : t = 3 := by omega
      rw [h3] at hm
      omega
    simp [hn', ht']
  · intro hn
    have he : n = 8 := hn
    subst n
    exact ⟨4, ⟨0, fun _ => 4, by simp [orders_one], by simp⟩, by decide, rfl⟩

variable {X : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X] [Nonempty X]

/-- The order and lower bound in Proposition 2.1, for every realization. -/
theorem order_eight_and_two_gap_distances
    (hcenter : center X = ({0, 1, 2} : Set ℝ))
    (h1 : ∀ x : X, Nat.card (sphere x 1) = 2)
    (h2 : ∀ x : X, Nat.card (sphere x 2) = 4) :
    Nat.card X = 8 ∧
      ∃ p q r s : X, dist p q ∈ Set.Ioo (0 : ℝ) 1 ∧ dist r s ∈ Set.Ioo (0 : ℝ) 1 ∧
        dist p q ≠ dist r s := by
  classical
  have hc : ∀ j ≤ 2, ∀ x : X, Nat.card (sphere x (radii j)) = counts j := by
    intro j hj x
    interval_cases j
    · simp [radii, counts]
    · exact h1 x
    · exact h2 x
  have horder := (necessary radii counts 2 rfl radii_strict (hcenter.trans radii_image.symm) hc).2
  rw [orders_two] at horder
  refine ⟨horder, ?_⟩
  have hclose (x : X) : ∃ y : X, dist y x ∈ Set.Ioo (0 : ℝ) 1 := by
    have htwo : Nat.card (closedBall x 2) = 8 := by
      have h := closedBall_order radii counts 2 rfl radii_strict hc x
      rw [orders_two] at h
      exact h
    have hopen : Nat.card (ball x 2) = 4 := by
      rw [closedBall_card_eq, h2] at htwo
      omega
    obtain ⟨k, p, _, hcover, hsum⟩ :=
      lower_closedBalls (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2) x
    have hmin (j : Fin (k + 1)) : 3 ≤ Nat.card (closedBall (p j) 1) := by
      have h := closedBall_order radii counts 1 rfl (fun j hj => radii_strict j (by omega))
        (fun j hj => hc j (by omega)) (p j)
      rw [orders_one] at h
      change Nat.card (closedBall (p j) 1) ∈ ({3, 4} : Set ℕ) at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      omega
    have hk : k = 0 := by
      by_contra! h
      let j : Fin (k + 1) := ⟨1, by omega⟩
      have hj : j ≠ 0 := by intro he; have := congrArg Fin.val he; simp [j] at this
      have hl : Nat.card (closedBall (p 0) 1) + Nat.card (closedBall (p j) 1) ≤
          ∑ l, Nat.card (closedBall (p l) 1) := by
        calc
          _ = ∑ l ∈ ({0, j} : Finset (Fin (k + 1))), Nat.card (closedBall (p l) 1) := by
            simp [Ne.symm hj]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)
      have hmin0 := hmin 0
      have hminj := hmin j
      omega
    subst k
    obtain ⟨j, hj⟩ := hcover x (mem_ball_self (by norm_num))
    have hj0 : j = 0 := Fin.eq_zero j
    subst j
    have hfour : Nat.card (closedBall x 1) = 4 := by
      rw [← IsUltrametricDist.closedBall_eq_of_mem hj]
      simpa [hopen] using hsum
    have hpair : Nat.card (ball x 1) = 2 := by
      rw [closedBall_card_eq, h1] at hfour
      omega
    by_contra! h
    have hball : ball x 1 = {x} := by
      ext y
      constructor
      · intro hy
        have hzero : dist y x = 0 := by
          by_contra! hz
          exact h y ⟨lt_of_le_of_ne dist_nonneg (Ne.symm hz), hy⟩
        simpa using dist_eq_zero.mp hzero
      · rintro rfl
        exact mem_ball_self (by norm_num)
    simp [hball] at hpair
  let q : X := Classical.choice inferInstance
  obtain ⟨p, hp⟩ := hclose q
  have habs : dist p q ∉ center X := by
    rw [hcenter]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hpos := hp.1
    have hlt := hp.2
    rintro (h | h | h) <;> linarith
  have hw : ¬ ∀ s : X, ∃ r : X, dist r s = dist p q :=
    fun h => habs ⟨hp.1.le, h⟩
  obtain ⟨s, hs⟩ := not_forall.mp hw
  obtain ⟨r, hr⟩ := hclose s
  exact ⟨p, q, r, s, hp, hr, fun h => hs ⟨r, h.symm⟩⟩

omit [MetricSpace X] [IsUltrametricDist X] [Finite X] [Nonempty X] in
/-- Both selected distances occur, and the eight-point model has no extra distances. -/
theorem eight_exact_distance_values (u v : ℝ) (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    Set.range (fun p : Eight u v hu huv hv × Eight u v hu huv hv => dist p.1 p.2) =
      ({0, u, v, 1, 2} : Set ℝ) := by
  have hne : Nonempty (Eight u v hu huv hv) := ⟨⟨0, ⟨0, ⟨0, PUnit.unit⟩⟩⟩⟩
  obtain ⟨_, p, q, r, s, hp, hr, hpr⟩ := order_eight_and_two_gap_distances
    (eight_center u v hu huv hv) (sphere_one_card u v hu huv hv) (sphere_two_card u v hu huv hv)
  have only_gap (x y : Eight u v hu huv hv) (h : dist x y ∈ Set.Ioo (0 : ℝ) 1) :
      dist x y = u ∨ dist x y = v := by
    have hd := distance_values u v hu huv hv x y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    have hpos := h.1
    have hlt := h.2
    rcases hd with hd | hd | hd | hd | hd
    · exfalso; linarith
    · exact Or.inl hd
    · exact Or.inr hd
    · exfalso; linarith
    · exfalso; linarith
  refine Set.Subset.antisymm (by rintro _ ⟨⟨x, y⟩, rfl⟩; exact distance_values u v hu huv hv x y) ?_
  intro d hd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  have hcentral (t : ℝ) (ht : t ∈ ({0, 1, 2} : Set ℝ)) :
      t ∈ Set.range (fun z : Eight u v hu huv hv × Eight u v hu huv hv => dist z.1 z.2) := by
    rw [← eight_center u v hu huv hv] at ht
    let x := Classical.choice hne
    obtain ⟨y, hy⟩ := ht.2 x
    exact ⟨(y, x), hy⟩
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact hcentral 0 (by simp)
  · rcases only_gap p q hp with he | he
    · exact ⟨(p, q), he⟩
    · rcases only_gap r s hr with he' | he'
      · exact ⟨(r, s), he'⟩
      · exact (hpr (he.trans he'.symm)).elim
  · rcases only_gap p q hp with he | he
    · rcases only_gap r s hr with he' | he'
      · exact (hpr (he.trans he'.symm)).elim
      · exact ⟨(r, s), he'⟩
    · exact ⟨(p, q), he⟩
  · exact hcentral 1 (by simp)
  · exact hcentral 2 (by simp)

end SphereCountSharpness
