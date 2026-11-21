/- GID: D5/S3/Combinatorics/Geometry/Ultrametric/MCDSphereCounts
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/Ultrametric/MCDSphereCounts
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: A finite ultrametric with center {c_0 < ... < c_h} has sphere counts 1,1,2,...,2^(h-1) at every point exactly when it has 2^h points. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#327)
escape_witness: mcd_spheres (on a minimum-order space the two open balls below the diameter
  each carry exactly 2^(h-1) points and the lower center, so the counts follow by induction) and
  orders_pow (with counts 1,1,2,...,2^(h-1) the candidate orders of the sphere-order recursion
  collapse to 2^h).
proof_shape:
  sphereEquiv: definition; consumer: mcd_spheres.
  zero_mem_center, lower, mono_le, mono_lt: bind-only helpers; consumers: lower, mcd_spheres.
  mcd_spheres: content; consumer: result.
  orders_pow: content; consumer: result.
  result: content.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center);
  D5/S3/Combinatorics/Geometry/UltrametricCenterMinimumOrder (result, center_sub);
  D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders (orders, necessary).
Search record (§3.1): the frozen ultrametric modules prove the minimum order 2^(|C|-1), the
  sphere-order recursion and its necessity; center_sub of UltrametricCenterMinimumOrder is made
  public and reused; no D5 module or pinned Mathlib declaration states the sphere counts of a
  minimum-order ultrametric or their converse.
-/

import D5.S3.Combinatorics.Geometry.UltrametricCenterSphereOrders
import D5.S3.Combinatorics.Geometry.UltrametricCenterMinimumOrder

/-! # Sphere counts of minimum-order ultrametric spaces

For a finite ultrametric space `X` whose center is `{0 = c_0 < c_1 < ⋯ < c_h}`, every point has
`2^(i-1)` points at distance `c_i` for `1 ≤ i ≤ h` exactly when `|X| = 2^h`, that is, when `X`
attains the minimum order `2^(|C(X)|-1)` (MCD). The forward implication does not assume that
every distance is central.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts

open Metric
open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

private theorem zero_mem_center (Y : Type) [MetricSpace Y] : (0 : ℝ) ∈ center Y :=
  ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩

/-- The frozen lower bound `|Y| ≥ 2^(|C(Y)| - 1)`, for a finite center listed by a finset. -/
private theorem lower (Y : Type) [MetricSpace Y] [IsUltrametricDist Y] [Finite Y]
    (A : Finset ℝ) (hA : center Y = ↑A) : 2 ^ (A.card - 1) ≤ Nat.card Y := by
  have := Fintype.ofFinite Y
  have h0 : (0 : ℝ) ∈ A := by
    have := zero_mem_center Y
    rw [hA] at this
    exact this
  have hnn : ∀ a ∈ A, 0 ≤ a := fun a ha => by
    have : a ∈ center Y := by rw [hA]; exact ha
    exact this.1
  rw [Nat.card_eq_fintype_card]
  exact ((UltrametricCenterMinimumOrder.result A).2 h0 hnn).1.2
    ⟨Y, inferInstance, inferInstance, inferInstance, hA, rfl⟩

/-- A sphere of radius below `m` around a point of the open `m`-ball lies in that ball. -/
private def sphereEquiv {X : Type} [MetricSpace X] [IsUltrametricDist X] (p x : X) {m r : ℝ}
    (hx : dist p x < m) (hr : r < m) :
    sphere (⟨x, hx⟩ : {y : X // dist p y < m}) r ≃ sphere x r where
  toFun y := ⟨y.1.1, by
    have := y.2
    rw [mem_sphere] at this ⊢
    exact this⟩
  invFun y := ⟨⟨y.1, by
      have hy := mem_sphere.mp y.2
      calc dist p y.1 ≤ max (dist p x) (dist x y.1) := dist_triangle_max p x y.1
        _ < m := max_lt hx (by rw [dist_comm, hy]; exact hr)⟩, by
    rw [mem_sphere]
    exact mem_sphere.mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem mono_le (c : ℕ → ℝ) (H : ℕ) (hc : ∀ i < H, c i < c (i + 1)) :
    ∀ j k, j ≤ k → k ≤ H → c j ≤ c k := by
  intro j k hjk hk
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            exact le_rfl
  | succ k ihk =>
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · exact (ihk (by omega) (by omega)).trans (hc k (by omega)).le
    · obtain rfl : j = k + 1 := by omega
      exact le_rfl

private theorem mono_lt (c : ℕ → ℝ) (H : ℕ) (hc : ∀ i < H, c i < c (i + 1)) :
    ∀ j k, j < k → k ≤ H → c j < c k := fun j k hjk hk =>
  (mono_le c H hc j (k - 1) (by omega) (by omega)).trans_lt
    (by have := hc (k - 1) (by omega); rwa [show k - 1 + 1 = k by omega] at this)

/-- On an MCD ultrametric with center `{c 0 < ⋯ < c h}`, every point has `2^(i-1)` points at
distance `c i`, for `1 ≤ i ≤ h`. -/
private theorem mcd_spheres (h : ℕ) : ∀ (X : Type) [MetricSpace X] [IsUltrametricDist X]
    [Finite X] (c : ℕ → ℝ), c 0 = 0 → (∀ i < h, c i < c (i + 1)) →
    center X = c '' Set.Iic h → Nat.card X = 2 ^ h →
    ∀ i, 1 ≤ i → i ≤ h → ∀ x : X, Nat.card (sphere x (c i)) = 2 ^ (i - 1) := by
  induction h with
  | zero => intro X _ _ _ c _ _ _ _ i hi hih; omega
  | succ h ih =>
  intro X _ _ _ c hc0 hc hcen hcard i hi1 hih x
  have := Fintype.ofFinite X
  set m := c (h + 1) with hmdef
  have hmcen : m ∈ center X := by rw [hcen]; exact ⟨h + 1, Set.mem_Iic.mpr le_rfl, rfl⟩
  -- the diameter is the largest central value
  have hm : ∀ a b : X, dist a b ≤ m := by
    obtain ⟨⟨p0, q0⟩, -, hpq⟩ := Finset.exists_max_image (Finset.univ : Finset (X × X))
      (fun z => dist z.1 z.2) ⟨(x, x), Finset.mem_univ _⟩
    have hM : dist p0 q0 ∈ center X := by
      refine ⟨dist_nonneg, fun z => ?_⟩
      have h1 := hpq (z, p0) (Finset.mem_univ _)
      have h2 := hpq (z, q0) (Finset.mem_univ _)
      have h3 : dist p0 q0 ≤ max (dist p0 z) (dist z q0) := dist_triangle_max p0 z q0
      simp only at h1 h2
      rcases le_max_iff.mp h3 with h4 | h4
      · exact ⟨p0, le_antisymm (by rw [dist_comm]; exact h1) h4⟩
      · exact ⟨q0, le_antisymm (by rw [dist_comm]; exact h2)
          (by simpa [dist_comm] using h4)⟩
    rw [hcen] at hM
    obtain ⟨j, hj, hjeq⟩ := hM
    intro a b
    calc dist a b ≤ dist p0 q0 := hpq (a, b) (Finset.mem_univ _)
      _ = c j := hjeq.symm
      _ ≤ m := mono_le c (h + 1) hc j (h + 1) (Set.mem_Iic.mp hj) le_rfl
  have hmpos : 0 < m := by
    rw [hmdef, ← hc0]
    exact mono_lt c (h + 1) hc 0 (h + 1) (by omega) le_rfl
  obtain ⟨q, hq⟩ := hmcen.2 x
  -- both open balls carry the lower central values
  have ball_lower : ∀ r : X, 2 ^ h ≤ Nat.card {y : X // dist r y < m} ∧
      (Nat.card {y : X // dist r y < m} ≤ 2 ^ h →
        center {y : X // dist r y < m} = c '' Set.Iic h) := by
    intro r
    have hfin : (center {y : X // dist r y < m}).Finite := by
      apply (Set.finite_range (fun y : {y : X // dist r y < m} =>
        dist y (⟨r, by simpa using hmpos⟩ : {y : X // dist r y < m}))).subset
      rintro t ⟨-, ht⟩
      obtain ⟨y, hy⟩ := ht ⟨r, by simpa using hmpos⟩
      exact ⟨y, hy⟩
    have hsub : c '' Set.Iic h ⊆ center {y : X // dist r y < m} := by
      rintro t ⟨j, hj, rfl⟩
      apply UltrametricCenterMinimumOrder.center_sub r hm
      refine ⟨by rw [hcen]; exact ⟨j, Set.mem_Iic.mpr (by have := Set.mem_Iic.mp hj; omega), rfl⟩,
        ?_⟩
      rw [Set.mem_singleton_iff]
      exact (mono_lt c (h + 1) hc j (h + 1) (by have := Set.mem_Iic.mp hj; omega) le_rfl).ne
    have hinj : Set.InjOn c (Set.Iic h) := fun a ha b hb hab => by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact (mono_lt c (h + 1) hc a b hlt (by have := Set.mem_Iic.mp hb; omega)).ne hab
      · exact (mono_lt c (h + 1) hc b a hlt (by have := Set.mem_Iic.mp ha; omega)).ne hab.symm
    have himg : (c '' Set.Iic h).ncard = h + 1 := by
      rw [hinj.ncard_image, Set.ncard_eq_toFinset_card' (Set.Iic h)]
      simp
    have hA := lower {y : X // dist r y < m} hfin.toFinset (by simp)
    have hcardA : h + 1 ≤ hfin.toFinset.card := by
      rw [← himg, ← Set.ncard_eq_toFinset_card _ hfin]
      exact Set.ncard_le_ncard hsub hfin
    refine ⟨le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hA, fun hle => ?_⟩
    have hle' : hfin.toFinset.card ≤ h + 1 := by
      by_contra hc'
      have := (Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (show h + 1 ≤ hfin.toFinset.card - 1 by omega)).trans hA
      have : 2 ^ h < 2 ^ (h + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    symm
    apply Set.eq_of_subset_of_ncard_le hsub _ hfin
    rw [himg, Set.ncard_eq_toFinset_card _ hfin]
    exact hle'
  obtain ⟨hx1, hx2⟩ := ball_lower x
  obtain ⟨hq1, -⟩ := ball_lower q
  -- the two balls are disjoint
  have hsum : Nat.card {y : X // dist x y < m} + Nat.card {y : X // dist q y < m} ≤
      Nat.card X := by
    rw [← Nat.card_sum]
    refine Nat.card_le_card_of_injective (Sum.elim Subtype.val Subtype.val) ?_
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) hab <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · simp [hab]
    · subst hab
      have : dist x q < m := lt_of_le_of_lt (dist_triangle_max x a q)
        (max_lt ha (by rw [dist_comm]; exact hb))
      rw [dist_comm] at hq
      linarith
    · subst hab
      have : dist x q < m := lt_of_le_of_lt (dist_triangle_max x a q)
        (max_lt hb (by rw [dist_comm]; exact ha))
      rw [dist_comm] at hq
      linarith
    · simp [hab]
  have hBx : Nat.card {y : X // dist x y < m} = 2 ^ h := by
    rw [hcard, pow_succ] at hsum
    omega
  rcases Nat.lt_or_ge i (h + 1) with hlt | hge
  · -- a lower radius: the sphere lies in the ball around `x`
    have hcB := hx2 hBx.le
    have hrec := ih {y : X // dist x y < m} c hc0 (fun j hj => hc j (by omega)) hcB hBx i hi1
      (by omega) ⟨x, by simpa using hmpos⟩
    rw [← hrec]
    exact (Nat.card_congr (sphereEquiv x x (by simpa using hmpos)
      (mono_lt c (h + 1) hc i (h + 1) hlt le_rfl))).symm
  · -- the top radius: the sphere is the complement of the ball
    obtain rfl : i = h + 1 := by omega
    have hset : sphere x m = {y : X | dist x y < m}ᶜ := by
      ext y
      simp only [mem_sphere, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
      constructor
      · intro hy; rw [dist_comm, hy]
      · intro hy; exact le_antisymm (hm y x) (by rw [dist_comm]; exact hy)
    have hcompl := Set.ncard_add_ncard_compl {y : X | dist x y < m}
    rw [Nat.card_coe_set_eq, hset]
    rw [← Nat.card_coe_set_eq {y : X | dist x y < m}] at hcompl
    change Nat.card {y : X // dist x y < m} + _ = _ at hcompl
    rw [hBx, hcard, pow_succ] at hcompl
    simp only [Nat.add_sub_cancel]
    omega

/-- With sphere counts `1, 1, 2, …, 2^(i-1)` the candidate orders collapse to `2^i`. -/
private theorem orders_pow (b : ℕ → ℕ) (hb : ∀ i, 1 ≤ i → b i = 2 ^ (i - 1)) :
    ∀ i n, n ∈ UltrametricCenterSphereOrders.orders b i → n = 2 ^ i
  | 0, n, hn => by simpa [UltrametricCenterSphereOrders.orders] using hn
  | i + 1, n, hn => by
    obtain ⟨t, ⟨k, s, hs, hst⟩, hd, rfl⟩ := hn
    have hs' : ∀ j, s j = 2 ^ i := fun j => orders_pow b hb i _ (hs j)
    have ht : t = (k + 1) * 2 ^ i := by
      rw [← hst]
      simp [hs', Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [hb (i + 1) (by omega), Nat.add_sub_cancel] at hd ⊢
    have hle := Nat.le_of_dvd (by positivity) hd
    rw [ht] at hle ⊢
    have hk : k = 0 := by
      by_contra hk
      have : 2 * 2 ^ i ≤ (k + 1) * 2 ^ i := Nat.mul_le_mul_right _ (by omega)
      have : 0 < 2 ^ i := by positivity
      omega
    subst hk
    rw [pow_succ]
    ring

/-- For a finite ultrametric space whose center is exactly `{0 = c 0 < c 1 < ⋯ < c h}`, every
point has `2^(i-1)` points at distance `c i` for all `1 ≤ i ≤ h` if and only if the space has
`2^h` points, that is, is minimum-order with this center (MCD). Distances outside the center
are not excluded by hypothesis. -/
theorem result {X : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X] (c : ℕ → ℝ) (h : ℕ)
    (hc0 : c 0 = 0) (hc : ∀ i < h, c i < c (i + 1)) (hcenter : center X = c '' Set.Iic h) :
    (∀ i, 1 ≤ i → i ≤ h → ∀ x : X, Nat.card (sphere x (c i)) = 2 ^ (i - 1)) ↔
      Nat.card X = 2 ^ h := by
  constructor
  · intro hs
    have hne : Nonempty X := by
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      have hC : center X = Set.Ici 0 := by
        ext t
        simp [center, Set.mem_Ici]
      have hfin : (c '' Set.Iic h).Finite := (Set.finite_Iic h).image c
      rw [← hcenter, hC] at hfin
      exact Set.Ici_infinite 0 hfin
    let b : ℕ → ℕ := fun i => if i = 0 then 1 else 2 ^ (i - 1)
    have hb : ∀ i ≤ h, ∀ x : X, Nat.card (sphere x (c i)) = b i := by
      intro i hi x
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp [b, hc0, sphere_zero]
      · simp only [b, Nat.pos_iff_ne_zero.mp hpos, ite_false]
        exact hs i hpos hi x
    have hn := (UltrametricCenterSphereOrders.necessary c b h hc0 hc hcenter hb).2
    exact orders_pow b (fun i hi => by simp [b, Nat.pos_iff_ne_zero.mp hi]) h _ hn
  · intro hn i hi1 hih x
    exact mcd_spheres h X c hc0 hc hcenter hn i hi1 hih x


end D5.S3.Combinatorics.Geometry.Ultrametric.MCDSphereCounts
