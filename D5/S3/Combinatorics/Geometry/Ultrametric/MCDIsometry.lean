/- GID: D5/S3/Combinatorics/Geometry/Ultrametric/MCDIsometry
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/Ultrametric/MCDIsometry
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Minimum-order finite ultrametric spaces with equally many points are isometric exactly when their centers agree. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#453)
escape_witness: split (on a minimum-order space the two open balls below the diameter around
  points at the diameter cover the space disjointly, have 2^(n-1) points and the lower center)
  and iso (the isometries of the halves, given by induction, glue across the diameter).
proof_shape:
  zero_mem_center, lower, le_max_center, nonempty_of_card, isoOfIsometry, cross,
    center_sub_of_iso: bind-only helpers; consumers: split, iso, result.
  split: content; consumer: iso.
  iso: content; consumer: result.
  result: content.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center);
  D5/S3/Combinatorics/Geometry/UltrametricCenterMinimumOrder (result, center_sub, inner).
Search record (§3.1): the frozen ultrametric modules prove the minimum order and its
  realization; Mathlib has isometry equivalences but no classification of minimum-order
  ultrametric spaces; no D5 module proves their isometry rigidity.
-/

import D5.S3.Combinatorics.Geometry.UltrametricCenterMinimumOrder

/-! # Isometry rigidity of minimum-order ultrametric spaces

A finite ultrametric space `X` is minimum-order (MCD) when `|X| = 2^(|C(X)| - 1)`. If `X` is MCD
and `Y` has at most as many points as `X` or is itself MCD, then `C(X) = C(Y)` exactly when `X`
and `Y` are isometric. Around two points at the diameter the open balls below the diameter split an MCD
space into two MCD halves with the lower center; isometries of the halves glue across the
diameter.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

private theorem zero_mem_center (Y : Type) [MetricSpace Y] : (0 : ℝ) ∈ center Y :=
  ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩

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

/-- In a finite space every distance is at most the largest central value, which is the
diameter. -/
private theorem le_max_center (X : Type) [MetricSpace X] [IsUltrametricDist X] [Finite X]
    (A : Finset ℝ) (hA : center X = ↑A) (hne : A.Nonempty) (a b : X) :
    dist a b ≤ A.max' hne := by
  have := Fintype.ofFinite X
  obtain ⟨⟨p0, q0⟩, -, hpq⟩ := Finset.exists_max_image (Finset.univ : Finset (X × X))
    (fun z => dist z.1 z.2) ⟨(a, a), Finset.mem_univ _⟩
  have hM : dist p0 q0 ∈ center X := by
    refine ⟨dist_nonneg, fun z => ?_⟩
    have h1 := hpq (z, p0) (Finset.mem_univ _)
    have h2 := hpq (z, q0) (Finset.mem_univ _)
    have h3 : dist p0 q0 ≤ max (dist p0 z) (dist z q0) := dist_triangle_max p0 z q0
    simp only at h1 h2
    rcases le_max_iff.mp h3 with h4 | h4
    · exact ⟨p0, le_antisymm (by rw [dist_comm]; exact h1) h4⟩
    · exact ⟨q0, le_antisymm (by rw [dist_comm]; exact h2) (by simpa [dist_comm] using h4)⟩
  rw [hA] at hM
  exact (hpq (a, b) (Finset.mem_univ _)).trans (A.le_max' _ hM)

/-- Splitting a minimum-order space at its diameter `m`: around two points at distance `m` the
open `m`-balls are disjoint, cover the space, and are minimum-order with center `A ∖ {m}`. -/
private theorem split (X : Type) [MetricSpace X] [IsUltrametricDist X] [Finite X] (n : ℕ)
    (A : Finset ℝ) (hA : center X = ↑A) (hcard : A.card = n + 2)
    (hX : Nat.card X = 2 ^ (n + 1)) (p q : X)
    (hpq : dist q p = A.max' (Finset.card_pos.mp (by omega))) :
    (∀ r : X, dist p r = A.max' (Finset.card_pos.mp (by omega)) ∨
        dist q r = A.max' (Finset.card_pos.mp (by omega)) →
      Nat.card (UltrametricCenterMinimumOrder.inner r (A.max' (Finset.card_pos.mp (by omega))))
          = 2 ^ n ∧
        center (UltrametricCenterMinimumOrder.inner r (A.max' (Finset.card_pos.mp (by omega))))
          = ↑(A.erase (A.max' (Finset.card_pos.mp (by omega))))) ∧
    (∀ x : X, dist p x < A.max' (Finset.card_pos.mp (by omega)) ∨
      dist q x < A.max' (Finset.card_pos.mp (by omega))) ∧
    (∀ x : X, ¬ (dist p x < A.max' (Finset.card_pos.mp (by omega)) ∧
      dist q x < A.max' (Finset.card_pos.mp (by omega)))) := by
  classical
  set hne : A.Nonempty := Finset.card_pos.mp (by omega)
  set m := A.max' hne with hmdef
  have hm := le_max_center X A hA hne
  have hmpos : 0 < m := by
    obtain ⟨a, ha, hane⟩ : ∃ a ∈ A, a ≠ m := by
      by_contra hcon
      push Not at hcon
      have : A ⊆ {m} := fun a ha => Finset.mem_singleton.mpr (hcon a ha)
      have := Finset.card_le_card this
      simp at this
      omega
    have h0 : (0 : ℝ) ≤ a := by
      have : a ∈ center X := by rw [hA]; exact ha
      exact this.1
    exact lt_of_le_of_lt h0 (lt_of_le_of_ne (A.le_max' a ha) hane)
  have hball : ∀ r : X, 2 ^ n ≤ Nat.card (UltrametricCenterMinimumOrder.inner r m) ∧
      (Nat.card (UltrametricCenterMinimumOrder.inner r m) ≤ 2 ^ n →
        center (UltrametricCenterMinimumOrder.inner r m) = ↑(A.erase m)) := by
    intro r
    have hfin : (center (UltrametricCenterMinimumOrder.inner r m)).Finite := by
      apply (Set.finite_range (fun y : UltrametricCenterMinimumOrder.inner r m =>
        dist y (⟨r, by simpa using hmpos⟩ : UltrametricCenterMinimumOrder.inner r m))).subset
      rintro t ⟨-, ht⟩
      obtain ⟨y, hy⟩ := ht ⟨r, by simpa using hmpos⟩
      exact ⟨y, hy⟩
    have hsub : (↑(A.erase m) : Set ℝ) ⊆ center (UltrametricCenterMinimumOrder.inner r m) := by
      intro t ht
      rw [Finset.coe_erase] at ht
      apply UltrametricCenterMinimumOrder.center_sub r hm
      rw [hA]
      exact ht
    have hlow := lower (UltrametricCenterMinimumOrder.inner r m) hfin.toFinset (by simp)
    have hcardE : (A.erase m).card = n + 1 := by
      rw [Finset.card_erase_of_mem (A.max'_mem hne)]; omega
    have hge : n + 1 ≤ hfin.toFinset.card := by
      rw [← hcardE, ← Set.ncard_coe_finset, ← Set.ncard_eq_toFinset_card _ hfin]
      exact Set.ncard_le_ncard hsub hfin
    refine ⟨le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hlow, fun hle => ?_⟩
    have hle' : hfin.toFinset.card ≤ n + 1 := by
      by_contra hc'
      have := (Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (show n + 1 ≤ hfin.toFinset.card - 1 by omega)).trans hlow
      have : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    symm
    apply Set.eq_of_subset_of_ncard_le hsub _ hfin
    rw [Set.ncard_coe_finset, hcardE, Set.ncard_eq_toFinset_card _ hfin]
    exact hle'
  have hdisj : ∀ x : X, ¬ (dist p x < m ∧ dist q x < m) := by
    rintro x ⟨h1, h2⟩
    have : dist q p < m := lt_of_le_of_lt (dist_triangle_max q x p)
      (max_lt h2 (by rw [dist_comm]; exact h1))
    linarith
  have hinj : Function.Injective
      (Sum.elim (Subtype.val : UltrametricCenterMinimumOrder.inner p m → X)
        (Subtype.val : UltrametricCenterMinimumOrder.inner q m → X)) := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) hab <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · simp [hab]
    · subst hab; exact absurd ⟨ha, hb⟩ (hdisj a)
    · subst hab; exact absurd ⟨hb, ha⟩ (hdisj a)
    · simp [hab]
  have hsum : Nat.card (UltrametricCenterMinimumOrder.inner p m) +
      Nat.card (UltrametricCenterMinimumOrder.inner q m) ≤ Nat.card X := by
    rw [← Nat.card_sum]
    exact Nat.card_le_card_of_injective _ hinj
  have hp1 := (hball p).1
  have hq1 := (hball q).1
  have hpexact : Nat.card (UltrametricCenterMinimumOrder.inner p m) = 2 ^ n := by
    rw [hX, pow_succ] at hsum; omega
  have hqexact : Nat.card (UltrametricCenterMinimumOrder.inner q m) = 2 ^ n := by
    rw [hX, pow_succ] at hsum; omega
  have hcover : ∀ x : X, dist p x < m ∨ dist q x < m := by
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [Nat.card_sum, hpexact, hqexact, hX, pow_succ]; omega)
    intro x
    obtain ⟨y, hy⟩ := hbij.2 x
    rcases y with ⟨y, hy'⟩ | ⟨y, hy'⟩
    · left; simp only [Sum.elim_inl] at hy; rw [← hy]; exact hy'
    · right; simp only [Sum.elim_inr] at hy; rw [← hy]; exact hy'
  refine ⟨fun r hr => ?_, hcover, hdisj⟩
  -- a point at distance `m` from `p` or `q` lies in the other ball, which equals its own ball
  have hsame : ∀ s : X, (dist p s < m → ∀ x, dist s x < m ↔ dist p x < m) ∧
      (dist q s < m → ∀ x, dist s x < m ↔ dist q x < m) := by
    intro s
    constructor
    · intro hs x
      constructor
      · intro h
        exact lt_of_le_of_lt (dist_triangle_max p s x) (max_lt hs h)
      · intro h
        exact lt_of_le_of_lt (dist_triangle_max s p x)
          (max_lt (by rw [dist_comm]; exact hs) h)
    · intro hs x
      constructor
      · intro h
        exact lt_of_le_of_lt (dist_triangle_max q s x) (max_lt hs h)
      · intro h
        exact lt_of_le_of_lt (dist_triangle_max s q x)
          (max_lt (by rw [dist_comm]; exact hs) h)
  have hcardr : Nat.card (UltrametricCenterMinimumOrder.inner r m) = 2 ^ n := by
    rcases hcover r with hr' | hr'
    · rw [← hpexact]
      exact Nat.card_congr (Equiv.subtypeEquivRight ((hsame r).1 hr'))
    · rw [← hqexact]
      exact Nat.card_congr (Equiv.subtypeEquivRight ((hsame r).2 hr'))
  exact ⟨hcardr, (hball r).2 hcardr.le⟩

private theorem nonempty_of_card {X : Type} {k : ℕ} (h : Nat.card X = 2 ^ k) : Nonempty X :=
  (Nat.card_pos_iff.mp (by rw [h]; positivity)).1

/-- An isometric embedding into a space with no more points is an isometry onto. -/
private theorem isoOfIsometry {X Y : Type} [MetricSpace X] [MetricSpace Y] [Finite X] [Finite Y]
    (f : X → Y) (hf : ∀ x y, dist (f x) (f y) = dist x y) (hc : Nat.card Y ≤ Nat.card X) :
    Nonempty (X ≃ᵢ Y) := by
  have hiso : Isometry f := Isometry.of_dist_eq hf
  exact ⟨⟨Equiv.ofBijective f (hiso.injective.bijective_of_nat_card_le hc), hiso⟩⟩

/-- Two points on opposite sides of the diameter-`m` split are at distance `m`. -/
private theorem cross {X : Type} [MetricSpace X] [IsUltrametricDist X] {m : ℝ} (p a b : X)
    (hm : ∀ x y : X, dist x y ≤ m) (ha : dist p a < m) (hb : ¬ dist p b < m) : dist a b = m :=
  le_antisymm (hm a b) (not_lt.mp fun hlt =>
    hb (lt_of_le_of_lt (dist_triangle_max p a b) (max_lt ha hlt)))

/-- Two minimum-order spaces with the same center are isometric. -/
private theorem iso (n : ℕ) : ∀ (X Y : Type) [MetricSpace X] [IsUltrametricDist X] [Finite X]
    [MetricSpace Y] [IsUltrametricDist Y] [Finite Y] (A : Finset ℝ), A.card = n + 1 →
    center X = ↑A → center Y = ↑A → Nat.card X = 2 ^ n → Nat.card Y = 2 ^ n →
    Nonempty (X ≃ᵢ Y) := by
  induction n with
  | zero =>
    intro X Y _ _ _ _ _ _ A _ _ _ hX hY
    obtain ⟨hXs, -⟩ := Nat.card_eq_one_iff_unique.mp hX
    obtain ⟨-, ⟨y0⟩⟩ := Nat.card_eq_one_iff_unique.mp hY
    refine isoOfIsometry (fun _ => y0) (fun x y => ?_) (by rw [hX, hY])
    rw [Subsingleton.elim x y, dist_self, dist_self]
  | succ n ih =>
    intro X Y _ _ _ _ _ _ A hA hcX hcY hX hY
    have hcard : A.card = n + 2 := hA
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    have hmX : A.max' hne ∈ center X := by rw [hcX]; exact A.max'_mem hne
    have hmY : A.max' hne ∈ center Y := by rw [hcY]; exact A.max'_mem hne
    have hXne : Nonempty X := nonempty_of_card hX
    have hYne : Nonempty Y := nonempty_of_card hY
    obtain ⟨p⟩ := hXne
    obtain ⟨p'⟩ := hYne
    obtain ⟨q, hq⟩ := hmX.2 p
    obtain ⟨q', hq'⟩ := hmY.2 p'
    obtain ⟨hbX, hcovX, hdisX⟩ := split X n A hcX hcard hX p q hq
    obtain ⟨hbY, hcovY, hdisY⟩ := split Y n A hcY hcard hY p' q' hq'
    set m := A.max' hne with hmdef
    have hmX' := le_max_center X A hcX hne
    have hmY' := le_max_center Y A hcY hne
    have hEcard : (A.erase m).card = n + 1 := by
      rw [Finset.card_erase_of_mem (A.max'_mem hne)]; omega
    obtain ⟨hpX, hpcX⟩ := hbX p (Or.inr hq)
    obtain ⟨hqX, hqcX⟩ := hbX q (Or.inl (by rw [dist_comm]; exact hq))
    obtain ⟨hpY, hpcY⟩ := hbY p' (Or.inr hq')
    obtain ⟨hqY, hqcY⟩ := hbY q' (Or.inl (by rw [dist_comm]; exact hq'))
    obtain ⟨e1⟩ := ih _ _ (A.erase m) hEcard hpcX hpcY hpX hpY
    obtain ⟨e2⟩ := ih _ _ (A.erase m) hEcard hqcX hqcY hqX hqY
    classical
    let f : X → Y := fun x =>
      if h : dist p x < m then (e1 ⟨x, h⟩).1 else (e2 ⟨x, (hcovX x).resolve_left h⟩).1
    have hf1 : ∀ x (h : dist p x < m), f x = (e1 ⟨x, h⟩).1 := fun x h => by
      simp only [f, h, ↓reduceDIte]
    have hf2 : ∀ x (h : ¬ dist p x < m), f x = (e2 ⟨x, (hcovX x).resolve_left h⟩).1 :=
      fun x h => by simp only [f, h, ↓reduceDIte]
    have hin1 : ∀ x (h : dist p x < m), dist p' (f x) < m := fun x h => by
      rw [hf1 x h]; exact (e1 ⟨x, h⟩).2
    have hout2 : ∀ x (h : ¬ dist p x < m), ¬ dist p' (f x) < m := fun x h hlt => by
      rw [hf2 x h] at hlt
      exact hdisY _ ⟨hlt, (e2 ⟨x, (hcovX x).resolve_left h⟩).2⟩
    refine isoOfIsometry f (fun x y => ?_) (by rw [hX, hY])
    by_cases hx : dist p x < m <;> by_cases hy : dist p y < m
    · rw [hf1 x hx, hf1 y hy]
      exact e1.dist_eq ⟨x, hx⟩ ⟨y, hy⟩
    · rw [cross p x y hmX' hx hy, cross p' (f x) (f y) hmY' (hin1 x hx) (hout2 y hy)]
    · rw [dist_comm, dist_comm x, cross p y x hmX' hy hx,
        cross p' (f y) (f x) hmY' (hin1 y hy) (hout2 x hx)]
    · rw [hf2 x hx, hf2 y hy]
      exact e2.dist_eq ⟨x, _⟩ ⟨y, _⟩

/-- An isometry carries the center onto the center. -/
private theorem center_sub_of_iso {X Y : Type} [MetricSpace X] [MetricSpace Y] (e : X ≃ᵢ Y) :
    center X ⊆ center Y := by
  rintro t ⟨ht0, h⟩
  refine ⟨ht0, fun p' => ?_⟩
  obtain ⟨y, hy⟩ := h (e.symm p')
  exact ⟨e y, by rw [← e.apply_symm_apply p', e.dist_eq]; exact hy⟩

/-- Let `X` be a finite ultrametric space of minimum order `2^(|C(X)| - 1)` and `Y` a finite
ultrametric space that has at most as many points as `X` or is itself of minimum order. Then `X`
and `Y` have the same center exactly when they are isometric. -/
theorem result {X Y : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X]
    [MetricSpace Y] [IsUltrametricDist Y] [Finite Y]
    (hX : Nat.card X = 2 ^ ((center X).ncard - 1))
    (hYc : Nat.card Y ≤ Nat.card X ∨ Nat.card Y = 2 ^ ((center Y).ncard - 1)) :
    center X = center Y ↔ Nonempty (X ≃ᵢ Y) := by
  constructor
  · intro hC
    have hXne : Nonempty X := nonempty_of_card hX
    obtain ⟨p⟩ := hXne
    have hfin : (center X).Finite := by
      apply (Set.finite_range (fun y : X => dist y p)).subset
      rintro t ⟨-, ht⟩
      obtain ⟨y, hy⟩ := ht p
      exact ⟨y, hy⟩
    have hpos : 0 < (center X).ncard := (Set.ncard_pos hfin).mpr ⟨0, zero_mem_center X⟩
    have hA : center X = ↑hfin.toFinset := by simp
    have hAY : center Y = ↑hfin.toFinset := by rw [← hC]; exact hA
    have hcardA : hfin.toFinset.card = (center X).ncard - 1 + 1 := by
      rw [← Set.ncard_eq_toFinset_card _ hfin]; omega
    have hXY : Nat.card X = Nat.card Y := by
      rcases hYc with h | h
      · have hlow := lower Y hfin.toFinset hAY
        rw [hcardA, Nat.add_sub_cancel, ← hX] at hlow
        omega
      · rw [hX, h, hC]
    exact iso _ X Y hfin.toFinset hcardA hA hAY hX (by rw [← hXY, hX])
  · rintro ⟨e⟩
    exact le_antisymm (center_sub_of_iso e) (center_sub_of_iso e.symm)


end D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry
