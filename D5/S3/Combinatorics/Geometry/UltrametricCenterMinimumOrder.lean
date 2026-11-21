/- GID: D5/S3/Combinatorics/Geometry/UltrametricCenterMinimumOrder
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/UltrametricCenterMinimumOrder
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.Ultra.Basic]
   utility: none
   digest: A finite ultrametric with k central distances has at least 2^(k-1) points, sharply. -/

import D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Data.Finset.Sort

/-! The minimum order of finite ultrametric spaces with a prescribed center of distances, using
the center `C(X)` of `DovgosheyRovenskaCentralEdges` (O. Dovgoshey and O. Rovenska,
arXiv:2603.25850, Definition 1.1).

`lower_bound` is Corollary 3.12 of arXiv:2603.25850 with the attainment of Example 3.13: a finite
ultrametric space with `|C(X)| = k ≥ 1` has at least `2^(k-1)` points, and this order is attained
for every `k ≥ 1`. `result` is Conjecture 4.4 of arXiv:2603.25850, proved as Proposition 4.5 and
Corollary 4.6 of O. Dovgoshey, N. S. Jaiswal, S. P. S. Kainth, G. Kaur and O. Rovenska
(arXiv:2609.11384): for a finite set `A`, being the center of some finite ultrametric space, being
its distance set and center at once, and `0 ∈ A ⊆ [0, ∞)` are equivalent, and then the least order
of a finite ultrametric space with center `A` is `2^(|A|-1)`, attained with distance set `A` as
well.

The lower bound splits a finite ultrametric space at its diameter `m`: the open `m`-balls around
two points at distance `m` are disjoint and each has center containing `C(X) \ {m}`. The
realization uses binary words of length `|A| - 1`, the distance of two words being the element of
`A` indexed by one plus the highest position where they differ.

admission_basis: escape-witness. Escape witnesses: center_sub (the center of an open ball below
the diameter contains `C(X) \ {m}`), lower_aux (the strong induction on the order), level_ultra and
the metric on `Space` (the binary-word ultrametric), attained with center_space and dist_set
(every scale value is attained from every point). -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Geometry.UltrametricCenterMinimumOrder

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges


private theorem center_subset_dists {X : Type} [MetricSpace X] (p : X) :
    center X ⊆ Set.range (fun y : X => dist y p) := by
  rintro t ⟨-, h⟩
  obtain ⟨y, hy⟩ := h p
  exact ⟨y, hy⟩

private theorem center_finite {X : Type} [Finite X] [MetricSpace X] (p : X) : (center X).Finite :=
  (Set.finite_range _).subset (center_subset_dists p)

/-- Points within distance `< m` of `p`. -/
private abbrev inner {X : Type} [MetricSpace X] (p : X) (m : ℝ) : Type := {y : X // dist p y < m}

private theorem center_sub {X : Type} [MetricSpace X] [IsUltrametricDist X] (p : X) {m : ℝ}
    (hm : ∀ x y : X, dist x y ≤ m) :
    center X \ {m} ⊆ center (inner p m) := by
  rintro t ⟨⟨ht0, h⟩, htm⟩
  refine ⟨ht0, fun p' => ?_⟩
  obtain ⟨y, hy⟩ := h p'.1
  have htle : t < m := lt_of_le_of_ne (hy ▸ hm y p'.1) htm
  have hpy : dist p y < m := by
    calc dist p y ≤ max (dist p p'.1) (dist p'.1 y) := dist_triangle_max p p'.1 y
      _ < m := max_lt p'.2 (by rw [dist_comm]; linarith)
  exact ⟨⟨y, hpy⟩, hy⟩

private theorem lower_aux (n : ℕ) : ∀ (X : Type) [Fintype X] [MetricSpace X] [IsUltrametricDist X],
    Fintype.card X = n → ∀ k, Nat.card (center X) = k → 1 ≤ k → 2 ^ (k - 1) ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn k hk hk1
  -- X is nonempty: otherwise the center is infinite
  have hne : Nonempty X := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have : center X = Set.Ici 0 := by
      ext t; simp [center, Set.mem_Ici]
    rw [this, Nat.card_coe_set_eq, Set.Infinite.ncard (Set.Ici_infinite 0)] at hk
    omega
  obtain ⟨p0⟩ := hne
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- one point: the center is {0}
    have hcard : Nat.card (center X) ≤ 1 := by
      have hsub : center X ⊆ {0} := by
        intro t ht
        obtain ⟨y, hy⟩ := center_subset_dists p0 ht
        have : y = p0 := by
          have := Fintype.card_le_one_iff.mp (by omega) y p0; exact this
        simp [← hy, this]
      calc Nat.card (center X) ≤ Nat.card ({0} : Set ℝ) :=
            Nat.card_mono (Set.finite_singleton 0) hsub
        _ = 1 := by simp
    have : 1 ≤ n := by rw [← hn]; exact Fintype.card_pos_iff.mpr ⟨p0⟩
    have hk1' : k = 1 := by omega
    subst hk1'; simpa using this
  -- the diameter is attained
  obtain ⟨⟨p, q⟩, -, hpq⟩ := Finset.exists_max_image (Finset.univ : Finset (X × X))
    (fun z => dist z.1 z.2) ⟨(p0, p0), Finset.mem_univ _⟩
  set m := dist p q with hmdef
  have hm : ∀ x y : X, dist x y ≤ m := fun x y => hpq (x, y) (Finset.mem_univ _)
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    simp; omega
  have hmpos : 0 < m := by
    have : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact lt_of_lt_of_le (dist_pos.mpr hxy) (hm x y)
  -- each half has at least 2^(k-2) points
  have half : ∀ r : X, (∃ s : X, m ≤ dist r s) →
      2 ^ (k - 2) ≤ Fintype.card (inner r m) := by
    intro r ⟨s, hs⟩
    have hlt : Fintype.card (inner r m) < n := by
      rw [← hn]; exact Fintype.card_subtype_lt (x := s) (by simpa using hs)
    have hfin : (center (inner r m)).Finite := center_finite ⟨r, by simpa using hmpos⟩
    have hge : k - 1 ≤ Nat.card (center (inner r m)) := by
      have h1 : k - 1 ≤ Nat.card ↑(center X \ {m}) := by
        rw [← hk, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        exact Set.pred_ncard_le_ncard_sdiff_singleton _ _
      exact h1.trans (Nat.card_mono hfin (center_sub r hm))
    have := ih _ hlt (inner r m) rfl _ rfl (by omega)
    calc 2 ^ (k - 2) ≤ 2 ^ (Nat.card (center (inner r m)) - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := this
  have hp := half p ⟨q, le_rfl⟩
  have hq := half q ⟨p, by rw [dist_comm]⟩
  -- the two halves are disjoint
  have hsum : Fintype.card (inner p m) + Fintype.card (inner q m) ≤ n := by
    rw [← Fintype.card_sum, ← hn]
    refine Fintype.card_le_of_injective (Sum.elim Subtype.val Subtype.val) ?_
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · simp [h]
    · subst h
      have : dist p q < m := lt_of_le_of_lt (dist_triangle_max p a q)
        (max_lt ha (by rw [dist_comm]; exact hb))
      linarith
    · subst h
      have : dist p q < m := lt_of_le_of_lt (dist_triangle_max p a q)
        (max_lt hb (by rw [dist_comm]; exact ha))
      linarith
    · simp [h]
  calc 2 ^ (k - 1) = 2 ^ (k - 2) + 2 ^ (k - 2) := by
        rw [show k - 1 = k - 2 + 1 by omega, pow_succ]; ring
    _ ≤ n := by omega


/-- Binary words of length `k`. -/
@[ext] private structure Words (k : ℕ) where
  w : Fin k → Bool

private def wordsEquiv (k : ℕ) : Words k ≃ (Fin k → Bool) :=
  ⟨Words.w, Words.mk, fun _ => rfl, fun _ => rfl⟩

instance (k : ℕ) : Fintype (Words k) := Fintype.ofEquiv _ (wordsEquiv k).symm
instance (k : ℕ) : DecidableEq (Words k) := (wordsEquiv k).decidableEq

private theorem card_words (k : ℕ) : Fintype.card (Words k) = 2 ^ k := by
  rw [Fintype.card_congr (wordsEquiv k)]; simp

/-- One plus the highest position where two words differ, or `0` for equal words. -/
private def level {k : ℕ} (u v : Words k) : ℕ :=
  (Finset.univ.filter fun i => u.w i ≠ v.w i).sup fun i => i.val + 1

private theorem level_le {k : ℕ} (u v : Words k) : level u v ≤ k :=
  Finset.sup_le fun (i : Fin k) _ => i.isLt

private theorem level_eq_zero {k : ℕ} {u v : Words k} : level u v = 0 ↔ u = v := by
  constructor
  · intro h; ext i; by_contra hi
    have := Finset.le_sup (f := fun i : Fin k => i.val + 1)
      (by simpa using hi : i ∈ Finset.univ.filter fun i => u.w i ≠ v.w i)
    unfold level at h; omega
  · rintro rfl; simp [level]

private theorem level_comm {k : ℕ} (u v : Words k) : level u v = level v u := by
  unfold level; congr 1; ext i; simp [eq_comm]

private theorem level_ultra {k : ℕ} (u v w : Words k) :
    level u w ≤ max (level u v) (level v w) := by
  unfold level
  rw [← Finset.sup_union]
  apply Finset.sup_mono
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
  by_contra h; push Not at h; exact hi (h.1.trans h.2)

/-- Flip position `j`. -/
private def flip {k : ℕ} (u : Words k) (j : Fin k) : Words k := ⟨Function.update u.w j (!u.w j)⟩

private theorem level_flip {k : ℕ} (u : Words k) (j : Fin k) : level u (flip u j) = j.val + 1 := by
  have : (Finset.univ.filter fun i => u.w i ≠ (flip u j).w i) = {j} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun i hi => ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [flip, Function.update_self]
      cases u.w j <;> decide
    · rw [Finset.mem_filter] at hi
      by_contra h
      exact hi.2 (by simp only [flip, Function.update_of_ne h])
  simp [level, this]


/-- A strictly increasing list of distance values starting at `0`. -/
private structure Scale (k : ℕ) where
  a : Fin (k + 1) → ℝ
  mono : StrictMono a
  zero : a 0 = 0

/-- Words of length `k` carrying the level metric with values `s.a`. -/
@[ext] private structure Space (k : ℕ) (s : Scale k) where
  word : Words k

variable {k : ℕ} (s : Scale k)

private def spaceEquiv : Space k s ≃ Words k := ⟨Space.word, Space.mk, fun _ => rfl, fun _ => rfl⟩

instance : Fintype (Space k s) := Fintype.ofEquiv _ (spaceEquiv s).symm

/-- The level of a pair, as an index into the scale. -/
private def lvl (u v : Words k) : Fin (k + 1) := ⟨level u v, Nat.lt_succ_of_le (level_le u v)⟩

private theorem lvl_self (u : Words k) : lvl u u = 0 := Fin.ext (level_eq_zero.mpr rfl)

private theorem scale_nonneg (j : Fin (k + 1)) : 0 ≤ s.a j :=
  s.zero ▸ s.mono.monotone (Fin.zero_le j)

private theorem lvl_ultra (u v w : Words k) :
    s.a (lvl u w) ≤ max (s.a (lvl u v)) (s.a (lvl v w)) := by
  have hu : ∀ x y : Words k, (lvl x y).val = level x y := fun _ _ => rfl
  rcases le_total (lvl u v) (lvl v w) with h | h
  · rw [max_eq_right (s.mono.monotone h)]
    refine s.mono.monotone (Fin.le_def.mpr ?_)
    have := level_ultra u v w; rw [Fin.le_def, hu, hu] at h; rw [hu, hu]; omega
  · rw [max_eq_left (s.mono.monotone h)]
    refine s.mono.monotone (Fin.le_def.mpr ?_)
    have := level_ultra u v w; rw [Fin.le_def, hu, hu] at h; rw [hu, hu]; omega

noncomputable instance : MetricSpace (Space k s) where
  dist u v := s.a (lvl u.word v.word)
  dist_self u := by simp only [lvl_self, s.zero]
  dist_comm u v := by
    show s.a (lvl u.word v.word) = s.a (lvl v.word u.word)
    congr 1; exact Fin.ext (level_comm _ _)
  dist_triangle u v w := by
    have := lvl_ultra s u.word v.word w.word
    have h1 := scale_nonneg s (lvl u.word v.word)
    have h2 := scale_nonneg s (lvl v.word w.word)
    show s.a (lvl u.word w.word) ≤ s.a (lvl u.word v.word) + s.a (lvl v.word w.word)
    rcases le_total (s.a (lvl u.word v.word)) (s.a (lvl v.word w.word)) with h | h
    · rw [max_eq_right h] at this; linarith
    · rw [max_eq_left h] at this; linarith
  eq_of_dist_eq_zero {u v} h :=
    Space.ext (level_eq_zero.mp (Fin.mk.inj_iff.mp (s.mono.injective (h.trans s.zero.symm))))

private theorem dist_def (u v : Space k s) : dist u v = s.a (lvl u.word v.word) := rfl

instance : IsUltrametricDist (Space k s) :=
  ⟨fun u v w => lvl_ultra s u.word v.word w.word⟩

private theorem card_space : Fintype.card (Space k s) = 2 ^ k := by
  rw [Fintype.card_congr (spaceEquiv s), card_words]

/-- Every scale value is attained from every point. -/
private theorem attained (u : Space k s) (j : Fin (k + 1)) : ∃ v : Space k s, dist v u = s.a j := by
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
  · exact ⟨u, by rw [dist_self, s.zero]⟩
  · refine ⟨⟨flip u.word i⟩, ?_⟩
    rw [dist_def]; congr 1
    refine Fin.ext ?_
    show level (flip u.word i) u.word = (i.succ : Fin (k + 1)).val
    rw [level_comm, level_flip]; simp

private theorem dist_set : {r | ∃ u v : Space k s, dist u v = r} = Set.range s.a := by
  ext r; constructor
  · rintro ⟨u, v, rfl⟩; exact ⟨_, (dist_def s u v).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨v, hv⟩ := attained s ⟨⟨fun _ => false⟩⟩ j
    exact ⟨v, _, hv⟩

private theorem center_space : center (Space k s) = Set.range s.a := by
  ext t; constructor
  · rintro ⟨-, h⟩
    obtain ⟨v, hv⟩ := h ⟨⟨fun _ => false⟩⟩
    exact ⟨_, (dist_def s v _).symm.trans hv⟩
  · rintro ⟨j, rfl⟩
    exact ⟨scale_nonneg s j, fun u => attained s u j⟩

private theorem card_succ (A : Finset ℝ) (h0 : (0 : ℝ) ∈ A) : A.card - 1 + 1 = A.card := by
  have := Finset.card_pos.mpr ⟨0, h0⟩; omega

/-- The scale of a finite set `A ∋ 0` of nonnegative reals, listed increasingly. -/
private def scaleOf (A : Finset ℝ) (h0 : 0 ∈ A) (hnn : ∀ a ∈ A, 0 ≤ a) : Scale (A.card - 1) where
  a j := A.orderEmbOfFin rfl (Fin.cast (card_succ A h0) j)
  mono _ _ hij := (A.orderEmbOfFin rfl).strictMono (Fin.lt_def.mpr (Fin.lt_def.mp hij))
  zero := by
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨0, h0⟩
    have : (Fin.cast (card_succ A h0) (0 : Fin (A.card - 1 + 1)) : Fin A.card) = ⟨0, hpos⟩ := rfl
    simp only [this, Finset.orderEmbOfFin_zero rfl hpos]
    exact le_antisymm (Finset.min'_le _ _ h0) (hnn _ (Finset.min'_mem _ _))

private theorem range_scaleOf (A : Finset ℝ) (h0 : 0 ∈ A) (hnn : ∀ a ∈ A, 0 ≤ a) :
    Set.range (scaleOf A h0 hnn).a = ↑A := by
  rw [← Finset.range_orderEmbOfFin A rfl]
  ext t; constructor
  · rintro ⟨j, rfl⟩; exact ⟨Fin.cast (card_succ A h0) j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.cast (card_succ A h0).symm j, rfl⟩

/-- Corollary 3.12 and Example 3.13 of Dovgoshey–Rovenska (arXiv:2603.25850): a finite ultrametric
space with `k ≥ 1` central distances has at least `2^(k-1)` points, and this order is attained
for every `k ≥ 1`. -/
theorem lower_bound :
    (∀ (X : Type) [Fintype X] [MetricSpace X] [IsUltrametricDist X] (k : ℕ),
      Nat.card (center X) = k → 1 ≤ k → 2 ^ (k - 1) ≤ Fintype.card X) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X),
      IsUltrametricDist X ∧ Nat.card (center X) = k ∧ Fintype.card X = 2 ^ (k - 1) := by
  refine ⟨fun X _ _ _ k hk hk1 => lower_aux _ X rfl k hk hk1, fun k hk => ?_⟩
  let A : Finset ℝ := (Finset.range k).image (fun n : ℕ => (n : ℝ))
  have hA : A.card = k :=
    (Finset.card_image_of_injective (Finset.range k) Nat.cast_injective).trans (Finset.card_range k)
  have h0 : (0 : ℝ) ∈ A := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
  have hnn : ∀ a ∈ A, (0 : ℝ) ≤ a := by
    intro a ha; obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp ha; positivity
  let s := scaleOf A h0 hnn
  refine ⟨Space _ s, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [center_space, range_scaleOf, Nat.card_coe_set_eq, Set.ncard_coe_finset, hA]
  · rw [card_space, hA]

/-- Conjecture 4.4 of Dovgoshey–Rovenska (arXiv:2603.25850), proved as Proposition 4.5 and
Corollary 4.6 of Dovgoshey, Jaiswal, Kainth, Kaur and Rovenska (arXiv:2609.11384), with the
minimum order: for a finite set `A`, being the center of a finite ultrametric space, being its
distance set and center at once, and `0 ∈ A ⊆ [0, ∞)` are equivalent; then `2^(|A|-1)` is the
least order of a finite ultrametric space with center `A`, attained by one whose distance set is
also `A`. -/
theorem result (A : Finset ℝ) :
    List.TFAE [∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), IsUltrametricDist X ∧
        center X = ↑A,
      ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), IsUltrametricDist X ∧
        {r | ∃ x y : X, dist x y = r} = ↑A ∧ center X = ↑A,
      0 ∈ A ∧ ∀ a ∈ A, 0 ≤ a] ∧
    (0 ∈ A → (∀ a ∈ A, 0 ≤ a) →
      IsLeast {n | ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), IsUltrametricDist X ∧
          center X = ↑A ∧ Fintype.card X = n} (2 ^ (A.card - 1)) ∧
      ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), IsUltrametricDist X ∧
        {r | ∃ x y : X, dist x y = r} = ↑A ∧ center X = ↑A ∧
        Fintype.card X = 2 ^ (A.card - 1)) := by
  have build : 0 ∈ A → (∀ a ∈ A, 0 ≤ a) →
      ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), IsUltrametricDist X ∧
        {r | ∃ x y : X, dist x y = r} = ↑A ∧ center X = ↑A ∧
        Fintype.card X = 2 ^ (A.card - 1) := fun h0 hnn =>
    ⟨Space _ (scaleOf A h0 hnn), inferInstance, inferInstance, inferInstance,
      by rw [dist_set, range_scaleOf], by rw [center_space, range_scaleOf], card_space _⟩
  have tfae : List.TFAE [∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), IsUltrametricDist X ∧
        center X = ↑A,
      ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), IsUltrametricDist X ∧
        {r | ∃ x y : X, dist x y = r} = ↑A ∧ center X = ↑A,
      0 ∈ A ∧ ∀ a ∈ A, 0 ≤ a] := by
    tfae_have 2 → 1 := fun ⟨X, i1, i2, hu, _, hC⟩ => ⟨X, i1, i2, hu, hC⟩
    tfae_have 1 → 3 := by
      rintro ⟨X, _, _, _, hC⟩
      by_cases hX : Nonempty X
      · obtain ⟨x⟩ := hX
        refine ⟨?_, fun a ha => ?_⟩
        · rw [← Finset.mem_coe, ← hC]; exact ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩
        · rw [← Finset.mem_coe, ← hC] at ha; exact ha.1
      · rw [not_nonempty_iff] at hX
        have : center X = Set.Ici 0 := by ext t; simp [center, Set.mem_Ici]
        rw [this] at hC
        exact absurd (hC ▸ Finset.finite_toSet A) (Set.Ici_infinite 0)
    tfae_have 3 → 2 := fun ⟨h0, hnn⟩ => by
      obtain ⟨X, i1, i2, i3, hD, hC, -⟩ := build h0 hnn
      exact ⟨X, i1, i2, i3, hD, hC⟩
    tfae_finish
  refine ⟨tfae, fun h0 hnn => ⟨⟨?_, ?_⟩, build h0 hnn⟩⟩
  · obtain ⟨X, i1, i2, i3, -, hC, hcard⟩ := build h0 hnn
    exact ⟨X, i1, i2, i3, hC, hcard⟩
  · rintro n ⟨X, _, _, _, hC, rfl⟩
    have hk : Nat.card (center X) = A.card := by
      rw [hC, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact lower_aux _ X rfl _ hk (Finset.card_pos.mpr ⟨0, h0⟩)

end D5.S3.Combinatorics.Geometry.UltrametricCenterMinimumOrder
