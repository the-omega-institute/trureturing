/- GID: D5/S1/Dynamics/Shadowing/InvarianceGluedSheets
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/InvarianceGluedSheets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact positive expansivity order for finite graph sheets glued on an invariant set. -/

import D5.S1.Dynamics.Shadowing.IntervalObstruction.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
The graph-sheet construction uses the max metric on the product with the real line.
The distance between two labels over one base point is their index gap times the
height parameter. A uniform orbit escape threshold then gives positive expansivity.
In its absence arbitrarily small forward Bowen balls contain all the labels of a fibre.
-/

open Set Function

namespace D5.S1.Dynamics.Shadowing.InvarianceGluedSheets

variable {Y : Type*} {N : ℕ} {ρ : Y → ℝ} {g : Y → Y}

/-- The union of the graphs of the first `N` nonnegative integer multiples of `ρ`. -/
abbrev Space (N : ℕ) (ρ : Y → ℝ) :=
  {p : Y × ℝ // ∃ i : Fin N, p.2 = (i.val : ℝ) * ρ p.1}

/-- A point on a specified graph sheet. -/
def lift (ρ : Y → ℝ) (i : Fin N) (y : Y) : Space N ρ :=
  ⟨(y, (i.val : ℝ) * ρ y), i, rfl⟩

private theorem exists_lift (p : Space N ρ) :
    ∃ i : Fin N, lift ρ i p.val.1 = p := by
  obtain ⟨i, hi⟩ := p.property
  exact ⟨i, Subtype.ext (Prod.ext rfl hi.symm)⟩

private theorem label_eq_of_mul_eq {y : Y} (hy : ρ y ≠ 0) {i j : Fin N}
    (h : (i.val : ℝ) * ρ y = (j.val : ℝ) * ρ y) : i = j := by
  have hval : (i.val : ℝ) = (j.val : ℝ) := mul_right_cancel₀ hy h
  exact Fin.ext (by exact_mod_cast hval)

/-- Apply the base map on each sheet. Forward invariance makes the maps agree
where the sheets meet. -/
noncomputable def map (g : Y → Y) (_hzero : ∀ y, ρ y = 0 → ρ (g y) = 0)
    (p : Space N ρ) : Space N ρ :=
  lift ρ (exists_lift p).choose (g p.val.1)

@[simp] theorem map_lift (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0)
    (i : Fin N) (y : Y) : map g hzero (lift ρ i y) = lift ρ i (g y) := by
  let p := lift ρ i y
  let j := (exists_lift p).choose
  have hj : (j.val : ℝ) * ρ y = (i.val : ℝ) * ρ y :=
    congrArg (fun q : Space N ρ => q.val.2) (exists_lift p).choose_spec
  refine Subtype.ext (Prod.ext ?_ ?_)
  · rfl
  change (j.val : ℝ) * ρ (g y) = (i.val : ℝ) * ρ (g y)
  by_cases hy : ρ y = 0
  · simp [hzero y hy]
  · rw [label_eq_of_mul_eq hy hj]

theorem iterate_lift (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0)
    (n : ℕ) (i : Fin N) (y : Y) :
    (map g hzero)^[n] (lift ρ i y) = lift ρ i (g^[n] y) :=
  (show Semiconj (lift ρ i) g (map g hzero) from fun y => (map_lift hzero i y).symm)
    |>.iterate_right n y |>.symm

private theorem fst_semiconj (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0) :
    Semiconj (fun p : Space N ρ => p.val.1) (map g hzero) g := fun _ => rfl

private theorem iUnion_range_lift :
    (⋃ i : Fin N, range (lift ρ i)) = univ := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨i, hi⟩ := exists_lift p
  exact mem_iUnion.mpr ⟨i, p.val.1, hi⟩

variable [MetricSpace Y]

private theorem continuous_lift (hρ : Continuous ρ) (i : Fin N) :
    Continuous (lift ρ i) :=
  (continuous_id.prodMk (continuous_const.mul hρ)).subtype_mk _

private theorem isClosed_range_lift (hρ : Continuous ρ) (i : Fin N) :
    IsClosed (range (lift ρ i)) := by
  rw [show range (lift ρ i) =
      {p : Space N ρ | p.val.2 = (i.val : ℝ) * ρ p.val.1} by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro hp
      exact ⟨p.val.1, Subtype.ext (Prod.ext rfl hp.symm)⟩]
  exact isClosed_eq (continuous_snd.comp continuous_subtype_val)
    (continuous_const.mul (hρ.comp (continuous_fst.comp continuous_subtype_val)))

/-- Continuous sheet maps paste along the closed graphs. -/
theorem continuous_map (hρ : Continuous ρ) (hg : Continuous g)
    (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0) : Continuous (map (N := N) g hzero) := by
  let S := fun i : Fin N => range (lift ρ i)
  have hcover : ⋃ i, S i = univ := iUnion_range_lift
  apply (locallyFinite_of_finite S).continuous hcover (isClosed_range_lift hρ)
  intro i
  have hc := ((continuous_lift hρ i).comp (hg.comp
    (continuous_fst.comp continuous_subtype_val))).continuousOn (s := S i)
  apply hc.congr
  rintro _ ⟨y, rfl⟩
  exact map_lift hzero i y

omit [MetricSpace Y] in
/-- A preimage of the base point gives a preimage on the same sheet. -/
theorem surjective_map (hg : Surjective g)
    (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0) : Surjective (map (N := N) g hzero) := by
  intro p
  obtain ⟨i, hi⟩ := exists_lift p
  obtain ⟨y, hy⟩ := hg p.val.1
  exact ⟨lift ρ i y, by rw [map_lift, hy, hi]⟩

/-- Over a compact base the space is compact by its finite cover by graph images. -/
theorem compactSpace_space [CompactSpace Y] (hρ : Continuous ρ) :
    CompactSpace (Space N ρ) := by
  refine ⟨?_⟩
  rw [← iUnion_range_lift (N := N) (ρ := ρ)]
  exact isCompact_iUnion fun i => isCompact_range (continuous_lift hρ i)

/-- Exact forward distance within a projection fibre, including after coalescence. -/
theorem dist_iterate_lift (hρ : ∀ y, 0 ≤ ρ y)
    (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0) (n : ℕ) (i j : Fin N) (y : Y) :
    dist ((map g hzero)^[n] (lift ρ i y)) ((map g hzero)^[n] (lift ρ j y)) =
      |(i.val : ℝ) - (j.val : ℝ)| * ρ (g^[n] y) := by
  rw [iterate_lift, iterate_lift, Subtype.dist_eq, Prod.dist_eq]
  change max (dist (g^[n] y) (g^[n] y))
    (dist ((i.val : ℝ) * ρ (g^[n] y)) ((j.val : ℝ) * ρ (g^[n] y))) = _
  rw [dist_self, max_eq_right dist_nonneg, Real.dist_eq, ← sub_mul, abs_mul,
    abs_of_nonneg (hρ _)]

private theorem fst_eq_of_close
    (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0)
    {c ε : ℝ} (hεc : ε ≤ c)
    (hex : ∀ x y, (∀ n, dist (g^[n] x) (g^[n] y) < c) → x = y)
    {p q : Space N ρ} (hclose : q ∈ ForwardBowen (map g hzero) ε p) :
    p.val.1 = q.val.1 := by
  apply hex
  intro n
  let F := map (N := N) g hzero
  have hn : dist (F^[n] p) (F^[n] q) < ε := hclose n
  rw [← (fst_semiconj hzero).iterate_right n p, ← (fst_semiconj hzero).iterate_right n q]
  exact (le_max_left _ _).trans_lt (hn.trans_le hεc)

/-- A base expansivity constant bounds every forward Bowen ball by the number of sheets. -/
theorem forwardBowenBound_of_positivelyExpansive (hg : PositivelyExpansive g)
    (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0) :
    ∃ ε > 0, ForwardBowenBound (map (N := N) g hzero) univ ε N := by
  obtain ⟨c, hc, hex⟩ := hg
  refine ⟨c, hc, fun p _ => (Set.encard_mono (b := range (fun i : Fin N => lift ρ i p.val.1))
    ?_).trans ?_⟩
  · intro q hq
    have he := fst_eq_of_close hzero le_rfl hex hq.2
    obtain ⟨i, hi⟩ := exists_lift q
    exact ⟨i, he.symm ▸ hi⟩
  · simpa only [← image_univ, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      using Set.encard_image_le (fun i : Fin N => lift ρ i p.val.1) univ

/-- Every point off the zero set has a forward iterate at a common positive height. -/
def UniformOrbitEscape (g : Y → Y) (ρ : Y → ℝ) : Prop :=
  ∃ δ > 0, ∀ y, ρ y ≠ 0 → ∃ n : ℕ, δ ≤ ρ (g^[n] y)

private theorem one_le_label_gap {i j : Fin N} (hij : i ≠ j) :
    1 ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
  apply le_abs.mpr
  rcases lt_or_gt_of_ne hij with h | h
  · have h' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.mp h)
    right
    linarith
  · have h' : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.mp h)
    left
    linarith

private theorem label_gap_le {i j : Fin N} :
    |(i.val : ℝ) - (j.val : ℝ)| ≤ ((N - 1 : ℕ) : ℝ) := by
  have hi : (i.val : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show i.val ≤ N - 1 by have := i.isLt; omega)
  have hj : (j.val : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show j.val ≤ N - 1 by have := j.isLt; omega)
  exact abs_sub_le_iff.mpr
    ⟨(sub_le_self _ (Nat.cast_nonneg _)).trans hi,
      (sub_le_self _ (Nat.cast_nonneg _)).trans hj⟩

/-- With at least two sheets, positive expansivity is equivalent to uniform
escape from the gluing locus over a positively expansive base. -/
theorem positivelyExpansive_iff_uniformOrbitEscape (hN : 2 ≤ N)
    (hg : PositivelyExpansive g) (hρ : ∀ y, 0 ≤ ρ y)
    (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0) :
    PositivelyExpansive (map (N := N) g hzero) ↔ UniformOrbitEscape g ρ := by
  constructor
  · rintro ⟨c, hc, hex⟩
    refine ⟨c, hc, fun y hy => ?_⟩
    let i : Fin N := ⟨0, by omega⟩
    let j : Fin N := ⟨1, by omega⟩
    by_contra! h
    have he := hex (lift ρ i y) (lift ρ j y) (fun n => by
      rw [dist_iterate_lift hρ]
      simpa [i, j] using h n)
    have hval := label_eq_of_mul_eq hy
      (congrArg (fun p : Space N ρ => p.val.2) he)
    exact (by decide : (0 : ℕ) ≠ 1) (congrArg Fin.val hval)
  · rintro ⟨δ, hδ, hescape⟩
    obtain ⟨c, hc, hex⟩ := hg
    refine ⟨min c δ, lt_min hc hδ, fun p q hclose => ?_⟩
    have he := fst_eq_of_close hzero (min_le_left c δ) hex hclose
    obtain ⟨i, hi⟩ := exists_lift p
    obtain ⟨j, hj⟩ := exists_lift q
    rw [← hi, ← hj, ← he] at hclose ⊢
    by_cases hy : ρ p.val.1 = 0
    · exact Subtype.ext (Prod.ext rfl (by simp [lift, hy]))
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨n, hn⟩ := hescape p.val.1 hy
    have hstrict := hclose n
    rw [dist_iterate_lift hρ] at hstrict
    have hge : δ ≤ |(i.val : ℝ) - (j.val : ℝ)| * ρ (g^[n] p.val.1) := by
      calc
        δ ≤ ρ (g^[n] p.val.1) := hn
        _ = 1 * ρ (g^[n] p.val.1) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (one_le_label_gap hij) (hρ _)
    exact (not_lt_of_ge hge (hstrict.trans_le (min_le_right c δ))).elim

/-- In the absence of uniform escape, each positive radius admits a whole fibre
of distinct sheet points whose pairwise orbit distances stay strictly below the radius. -/
theorem exists_small_fibre (hN : 2 ≤ N) (hρ : ∀ y, 0 ≤ ρ y)
    (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0) (h : ¬ UniformOrbitEscape g ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Y, Injective (fun i : Fin N => lift ρ i y) ∧
      ∀ i j : Fin N, ∀ n : ℕ,
        dist ((map g hzero)^[n] (lift ρ i y)) ((map g hzero)^[n] (lift ρ j y)) < ε := by
  let m : ℝ := ((N - 1 : ℕ) : ℝ)
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (show 0 < N - 1 by omega)
  unfold UniformOrbitEscape at h
  push Not at h
  obtain ⟨y, hy, hsmall⟩ := h (ε / m) (div_pos hε hm)
  refine ⟨y, fun i j hij => label_eq_of_mul_eq hy
    (congrArg (fun p : Space N ρ => p.val.2) hij), fun i j n => ?_⟩
  rw [dist_iterate_lift hρ]
  calc
    _ ≤ m * ρ (g^[n] y) := mul_le_mul_of_nonneg_right label_gap_le (hρ _)
    _ < ε := by rw [mul_comm]; exact (lt_div_iff₀ hm).mp (hsmall n)

/-- Over a positively expansive base, every strict `N - 1` bound fails exactly
when there is no positive uniform orbit escape threshold. -/
theorem no_smaller_bound_iff_not_uniformOrbitEscape (hN : 2 ≤ N)
    (hg : PositivelyExpansive g) (hρ : ∀ y, 0 ≤ ρ y)
    (hzero : ∀ y, ρ y = 0 → ρ (g y) = 0) :
    (∀ ε > 0, ¬ ForwardBowenBound (map (N := N) g hzero) univ ε (N - 1)) ↔
      ¬ UniformOrbitEscape g ρ := by
  constructor
  · intro h hescape
    obtain ⟨c, hc, hex⟩ := (positivelyExpansive_iff_uniformOrbitEscape hN hg hρ hzero).mpr hescape
    apply h c hc
    intro p _
    have hsub : (univ ∩ ForwardBowen (map (N := N) g hzero) c p) ⊆ {p} := by
      intro q hq
      exact mem_singleton_iff.mpr (hex p q hq.2).symm
    calc
      _ ≤ ({p} : Set (Space N ρ)).encard := Set.encard_mono hsub
      _ ≤ ((N - 1 : ℕ) : ℕ∞) := by
        rw [Set.encard_singleton]
        exact_mod_cast (show 1 ≤ N - 1 by omega)
  · intro h ε hε hb
    obtain ⟨y, hi, hsmall⟩ := exists_small_fibre hN hρ hzero h hε
    let p := lift ρ (⟨0, by omega⟩ : Fin N) y
    have hle : (N : ℕ∞) ≤ (univ ∩ ForwardBowen (map g hzero) ε p).encard :=
      (Set.le_encard_iff_exists_fin_injective _ N).mpr
        ⟨fun i => lift ρ i y, fun i => ⟨mem_univ _, hsmall _ i⟩, hi⟩
    have hbad : N ≤ N - 1 := by exact_mod_cast hle.trans (hb p (mem_univ _))
    omega

section ClosedSet

variable {K : Set Y}

/-- Forward invariance of a nonempty closed set makes its distance-zero locus invariant. -/
theorem infDist_zero_invariant (hK : IsClosed K) (hne : K.Nonempty) (hmap : MapsTo g K K)
    (y : Y) (hy : Metric.infDist y K = 0) : Metric.infDist (g y) K = 0 :=
  Metric.infDist_zero_of_mem (hmap ((hK.mem_iff_infDist_zero hne).mpr hy))

/-- A compact gluing set has a positive uniform orbit escape threshold exactly
when it is the set of points with entire forward orbit in some open neighborhood. -/
theorem uniformOrbitEscape_infDist_iff (hK : IsCompact K) (hne : K.Nonempty)
    (hmap : MapsTo g K K) :
    UniformOrbitEscape g (fun y => Metric.infDist y K) ↔
      ∃ U : Set Y, IsOpen U ∧ K ⊆ U ∧ K = ⋂ n : ℕ, (g^[n]) ⁻¹' U := by
  constructor
  · rintro ⟨δ, hδ, hescape⟩
    let U := Metric.thickening δ K
    have hKU : K ⊆ U := Metric.self_subset_thickening hδ K
    refine ⟨U, Metric.isOpen_thickening, hKU, ?_⟩
    ext y
    rw [mem_iInter]
    constructor
    · intro hy n
      exact hKU (hmap.iterate n hy)
    · intro hy
      by_contra hyK
      obtain ⟨n, hn⟩ := hescape y (fun he => hyK ((hK.isClosed.mem_iff_infDist_zero hne).mpr he))
      exact (not_lt_of_ge hn) ((Metric.mem_thickening_iff_infDist_lt hne).mp (hy n))
  · rintro ⟨U, hU, hKU, he⟩
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hU hKU
    refine ⟨δ, hδ, fun y hy => ?_⟩
    by_contra! h
    apply hy
    apply Metric.infDist_zero_of_mem
    rw [he, mem_iInter]
    intro n
    exact hsub ((Metric.mem_thickening_iff_infDist_lt hne).mpr (h n))

/-- The complete rank alternative for finite sheets over a nonempty compact
invariant set, expressed by its isolating-neighborhood property. -/
theorem exact_order_infDist (hN : 2 ≤ N) (hg : PositivelyExpansive g)
    (hK : IsCompact K) (hne : K.Nonempty) (hmap : MapsTo g K K) :
    let F : Space N (fun y => Metric.infDist y K) → Space N (fun y => Metric.infDist y K) :=
      map g (infDist_zero_invariant hK.isClosed hne hmap)
    let isolates := ∃ U : Set Y, IsOpen U ∧ K ⊆ U ∧ K = ⋂ n : ℕ, (g^[n]) ⁻¹' U
    (∃ ε > 0, ForwardBowenBound F univ ε N) ∧
      (PositivelyExpansive F ↔ isolates) ∧
      ((∀ ε > 0, ¬ ForwardBowenBound F univ ε (N - 1)) ↔ ¬ isolates) := by
  let hzero := infDist_zero_invariant hK.isClosed hne hmap
  have hρ : ∀ y, 0 ≤ Metric.infDist y K := fun _ => Metric.infDist_nonneg
  have hiff := uniformOrbitEscape_infDist_iff hK hne hmap
  exact ⟨forwardBowenBound_of_positivelyExpansive hg hzero,
    (positivelyExpansive_iff_uniformOrbitEscape hN hg hρ hzero).trans hiff,
    (no_smaller_bound_iff_not_uniformOrbitEscape hN hg hρ hzero).trans (not_congr hiff)⟩

end ClosedSet

end D5.S1.Dynamics.Shadowing.InvarianceGluedSheets
