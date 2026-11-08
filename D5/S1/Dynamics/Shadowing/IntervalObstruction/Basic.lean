import D5.S1.Dynamics.Shadowing.UniformTracing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
Elementary interval obstruction.
All Bowen sets below use strict inequalities at every natural-number time.
-/

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing

/-- The strict forward Bowen set, including time zero. -/
def ForwardBowen {X : Type*} [PseudoMetricSpace X] (f : X → X)
    (ε : ℝ) (x : X) : Set X :=
  {y | ∀ t : ℕ, dist (f^[t] x) (f^[t] y) < ε}

/-- A uniform cardinal bound, with the actual infinite-time Bowen quantifier. -/
def ForwardBowenBound {X : Type*} [PseudoMetricSpace X] (f : X → X)
    (K : Set X) (ε : ℝ) (N : ℕ) : Prop :=
  ∀ x ∈ K, (K ∩ ForwardBowen f ε x).encard ≤ (N : ℕ∞)

/-- Finite positive expansivity on the given metric space. -/
def FinitelyPositiveExpansive {X : Type*} [MetricSpace X] (f : X → X) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, 1 ≤ N ∧ ForwardBowenBound f univ ε N

namespace IntervalObstruction

section Metric

variable {X : Type*} [MetricSpace X]
variable {f : X → X} {K : Set X} {ε η : ℝ} {N : ℕ}

/-- Equality at one terminal time propagates along the entire infinite tail. -/
theorem iterate_eq_of_terminal_eq {T t : ℕ} {x y : X}
    (hT : f^[T] x = f^[T] y) (ht : T ≤ t) : f^[t] x = f^[t] y := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le ht
  simpa only [Nat.add_comm T q, Function.iterate_add_apply, hT]

/-- Inclusive control through the terminal time and equality there suffice. -/
theorem mem_forwardBowen_of_terminal_eq {T : ℕ} {x y : X}
    (hε : 0 < ε) (hT : f^[T] x = f^[T] y)
    (hp : ∀ t ≤ T, dist (f^[t] x) (f^[t] y) < ε) :
    y ∈ ForwardBowen f ε x := by
  intro t
  by_cases ht : t ≤ T
  · exact hp t ht
  · rw [iterate_eq_of_terminal_eq hT (by omega), dist_self]
    exact hε

/-- A finite family of common-terminal histories gives distinct Bowen points. -/
theorem coalescing_witnesses {m T : ℕ} (x : Fin m → X)
    (hi : Injective x) (hK : ∀ i, x i ∈ K) (hε : 0 < ε)
    (hp : ∀ i j t, t ≤ T → dist (f^[t] (x i)) (f^[t] (x j)) < ε)
    (hT : ∀ i j, f^[T] (x i) = f^[T] (x j)) (i₀ : Fin m) :
    (Set.range x).encard ≤ (K ∩ ForwardBowen f ε (x i₀)).encard ∧
      (Set.range x).encard = m := by
  constructor
  · apply Set.encard_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨hK i, mem_forwardBowen_of_terminal_eq hε (hT i₀ i)
      (fun t ht => hp i₀ i t ht)⟩
  · rw [hi.encard_range]
    simp

/-- The finite-cardinal contradiction already contains the full infinite tail. -/
theorem no_coalescing_witnesses (hB : ForwardBowenBound f K ε N)
    (hε : 0 < ε) {m T : ℕ} (hm : N < m) (x : Fin m → X)
    (hi : Injective x) (hK : ∀ i, x i ∈ K)
    (hp : ∀ i j t, t ≤ T → dist (f^[t] (x i)) (f^[t] (x j)) < ε)
    (hT : ∀ i j, f^[T] (x i) = f^[T] (x j)) : False := by
  let i₀ : Fin m := ⟨0, by omega⟩
  obtain ⟨hsub, hc⟩ := coalescing_witnesses x hi hK hε hp hT i₀
  have hcard : (m : ℕ∞) ≤ (N : ℕ∞) := by
    rw [← hc]
    exact hsub.trans (hB (x i₀) (hK i₀))
  exact (not_le_of_gt hm) (by exact_mod_cast hcard)

/-- Finitely many continuous observations share one strictly positive scale. -/
theorem finite_block_scale (hK : IsCompact K) (hf : ContinuousOn f K)
    (hmap : MapsTo f K K) (hε : 0 < ε) (p : ℕ) :
    ∃ δ > 0, ∀ j < p, ∀ x ∈ K, ∀ y ∈ K,
      dist x y < δ → dist (f^[j] x) (f^[j] y) < ε := by
  induction p with
  | zero => exact ⟨1, zero_lt_one, by simp⟩
  | succ p ih =>
    obtain ⟨δ, hδ, hd⟩ := ih
    obtain ⟨γ, hγ, hg⟩ := Metric.uniformContinuousOn_iff.mp
      (hK.uniformContinuousOn_of_continuous (hf.iterate hmap p)) ε hε
    refine ⟨min δ γ, lt_min hδ hγ, ?_⟩
    intro j hj x hx y hy hxy
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hd j hj x hx y hy (hxy.trans_le (min_le_left _ _))
    · exact hg x hx y hy (hxy.trans_le (min_le_right _ _))

/-- Finite-block uniform continuity transfers the exact all-time bound to powers. -/
theorem forwardBowenBound_iterate (hK : IsCompact K) (hf : ContinuousOn f K)
    (hmap : MapsTo f K K) (hε : 0 < ε) (hB : ForwardBowenBound f K ε N)
    {p : ℕ} (hp : 0 < p) :
    ∃ δ > 0, ForwardBowenBound (f^[p]) K δ N := by
  obtain ⟨δ, hδ, hd⟩ := finite_block_scale hK hf hmap hε p
  refine ⟨δ, hδ, fun x hx => (Set.encard_mono ?_).trans (hB x hx)⟩
  rintro y ⟨hy, hxy⟩
  refine ⟨hy, fun t => ?_⟩
  have hq := hxy (t / p)
  have hxm := hmap.iterate (p * (t / p)) hx
  have hym := hmap.iterate (p * (t / p)) hy
  rw [← Function.iterate_mul] at hq
  have ht : t = t % p + p * (t / p) := (Nat.mod_add_div t p).symm
  rw [ht, Function.iterate_add_apply, Function.iterate_add_apply]
  exact hd (t % p) (Nat.mod_lt _ hp) _ hxm _ hym hq

/-- A set contained in one strict Bowen set is finite under the bound. -/
theorem finite_of_all_times_small (hB : ForwardBowenBound f K ε N)
    {S : Set X} (hSK : S ⊆ K) (x : X) (hx : x ∈ S)
    (hs : ∀ y ∈ S, ∀ t : ℕ, dist (f^[t] x) (f^[t] y) < ε) : S.Finite := by
  apply Set.finite_of_encard_le_coe (k := N)
  apply le_trans (Set.encard_mono (b := K ∩ ForwardBowen f ε x) ?_) (hB x (hSK hx))
  exact fun y hy => ⟨hSK hy, hs y hy⟩

/-- One small covering cell cuts every first fibre down to at most N points. -/
theorem fibre_cell_bound (hB : ForwardBowenBound f K ε N) (hε : 0 < ε)
    (c z : X) :
    (K ∩ Metric.ball c (ε / 3) ∩ f ⁻¹' {z}).encard ≤ (N : ℕ∞) := by
  let S := K ∩ Metric.ball c (ε / 3) ∩ f ⁻¹' {z}
  rcases S.eq_empty_or_nonempty with he | ⟨x, hx⟩
  · change S.encard ≤ (N : ℕ∞)
    simp [he]
  · apply le_trans (Set.encard_mono (b := K ∩ ForwardBowen f ε x) ?_) (hB x hx.1.1)
    intro y hy
    refine ⟨hy.1.1, ?_⟩
    apply mem_forwardBowen_of_terminal_eq hε (T := 1)
    · simpa only [Function.iterate_one] using hx.2.trans hy.2.symm
    · intro t ht
      rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
      · have hxc : dist x c < ε / 3 := hx.1.2
        have hyc : dist c y < ε / 3 := by simpa only [Metric.mem_ball, dist_comm] using hy.1.2
        simpa only [Function.iterate_zero_apply] using
          (show dist x y < ε by linarith [dist_triangle x c y])
      · simp only [Function.iterate_one]
        rw [show f x = f y from hx.2.trans hy.2.symm, dist_self]
        exact hε

/-- Compactness plus the strict all-time bound makes every first fibre finite. -/
theorem finite_fibres (hK : IsCompact K) (hB : ForwardBowenBound f K ε N)
    (hε : 0 < ε) (z : X) : (K ∩ f ⁻¹' {z}).Finite := by
  obtain ⟨C, _, hC, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 3 by positivity)
  have hu : (⋃ c ∈ C, K ∩ Metric.ball c (ε / 3) ∩ f ⁻¹' {z}).Finite :=
    hC.biUnion (fun c _ => Set.finite_of_encard_le_coe (fibre_cell_bound hB hε c z))
  apply hu.subset
  intro x hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcover hx.1)
  exact mem_iUnion₂.mpr ⟨c, hc, ⟨⟨hx.1, hxc⟩, hx.2⟩⟩

/-- Finite first fibres and invariance give finite fibres of every iterate. -/
theorem finite_iterate_fibres (hmap : MapsTo f K K)
    (hfib : ∀ z, (K ∩ f ⁻¹' {z}).Finite) (n : ℕ) (z : X) :
    (K ∩ (f^[n]) ⁻¹' {z}).Finite := by
  induction n generalizing z with
  | zero =>
    apply (Set.finite_singleton z).subset
    intro x hx
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.iterate_zero, id_eq] using hx.2
  | succ n ih =>
    have hu := (ih z).biUnion (fun y _ => hfib y)
    apply hu.subset
    intro x hx
    refine mem_iUnion₂.mpr ⟨f x, ⟨hmap hx.1, ?_⟩, ⟨hx.1, rfl⟩⟩
    simpa only [Set.mem_preimage, Set.mem_singleton_iff,
      Function.iterate_succ_apply] using hx.2

/-- Under finite iterate fibres an infinite set has an infinite image. -/
theorem infinite_iterate_image (hmap : MapsTo f K K)
    (hfib : ∀ z, (K ∩ f ⁻¹' {z}).Finite) {J : Set X}
    (hJK : J ⊆ K) (hJ : J.Infinite) (n : ℕ) : (f^[n] '' J).Infinite := by
  intro hi
  have hu := hi.biUnion (fun z _ => finite_iterate_fibres hmap hfib n z)
  apply hJ
  apply hu.subset
  intro x hx
  exact mem_iUnion₂.mpr ⟨f^[n] x, mem_image_of_mem _ hx, ⟨hJK hx, rfl⟩⟩

/-- An infinite set has arbitrarily late images containing an ε-separated pair.
This is stronger than the repeated macroscopic-image step at every ρ < ε. -/
theorem arbitrarily_late_separation (hB : ForwardBowenBound f K ε N)
    (hmap : MapsTo f K K) (hε : 0 < ε)
    (hfib : ∀ z, (K ∩ f ⁻¹' {z}).Finite) {J : Set X}
    (hJK : J ⊆ K) (hJ : J.Infinite) (M : ℕ) :
    ∃ n ≥ M, ∃ x ∈ J, ∃ y ∈ J, ε ≤ dist (f^[n] x) (f^[n] y) := by
  by_contra! h
  have hI : (f^[M] '' J).Infinite := infinite_iterate_image hmap hfib hJK hJ M
  obtain ⟨x, hx⟩ := hJ.nonempty
  apply hI
  apply finite_of_all_times_small hB
    (fun z hz => by rcases hz with ⟨y, hy, rfl⟩; exact hmap.iterate M (hJK hy))
    (f^[M] x) (mem_image_of_mem _ hx)
  rintro z ⟨y, hy, rfl⟩ t
  simpa only [← Function.iterate_add_apply, Nat.add_comm t M] using
    h (M + t) (by omega) x hx y hy

end Metric

section FiniteUnions

variable {X Y : Type*}

/-- A uniform cell bound survives a finite union without any disjointness premise. -/
theorem encard_finite_union_le (S : Y → Set X) (C : Finset Y) (N : ℕ)
    (h : ∀ c ∈ C, (S c).encard ≤ (N : ℕ∞)) :
    (⋃ c ∈ C, S c).encard ≤ ((C.card * N : ℕ) : ℕ∞) := by
  classical
  revert h
  induction C using Finset.induction_on with
  | empty => intro h; simp
  | @insert c C hc ih =>
    intro h
    have he : (⋃ d ∈ insert c C, S d) = S c ∪ ⋃ d ∈ C, S d := by
      ext x
      simp
    rw [he]
    calc
      _ ≤ (S c).encard + (⋃ d ∈ C, S d).encard := Set.encard_union_le _ _
      _ ≤ (N : ℕ∞) + ((C.card * N : ℕ) : ℕ∞) :=
        add_le_add (h c (Finset.mem_insert_self _ _))
          (ih (fun d hd => h d (Finset.mem_insert_of_mem hd)))
      _ = (((insert c C).card * N : ℕ) : ℕ∞) := by
        rw [Finset.card_insert_of_notMem hc]
        push_cast
        ring

end FiniteUnions

section UniformFibres

variable {X : Type*} [MetricSpace X] {f : X → X} {K : Set X} {ε : ℝ} {N : ℕ}

/-- The first-fibre bound is uniform in its target; onto dynamics is unnecessary. -/
theorem uniform_fibre_bound (hK : IsCompact K) (hB : ForwardBowenBound f K ε N)
    (hε : 0 < ε) : ∃ C : ℕ, ∀ z, (K ∩ f ⁻¹' {z}).encard ≤ (C : ℕ∞) := by
  classical
  obtain ⟨S, _, hS, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 3 by positivity)
  let C := hS.toFinset
  refine ⟨C.card * N, fun z => ?_⟩
  calc
    _ ≤ (⋃ c ∈ C, K ∩ Metric.ball c (ε / 3) ∩ f ⁻¹' {z}).encard := by
      apply Set.encard_mono
      intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcover hx.1)
      exact mem_iUnion₂.mpr ⟨c, by simpa [C] using hc, ⟨⟨hx.1, hxc⟩, hx.2⟩⟩
    _ ≤ ((C.card * N : ℕ) : ℕ∞) :=
      encard_finite_union_le _ C N (fun c _ => fibre_cell_bound hB hε c z)

/-- Every iterate has a target-independent finite bound, explicitly C^n. -/
theorem uniform_iterate_fibre_bound (hmap : MapsTo f K K) {C : ℕ}
    (hC : ∀ z, (K ∩ f ⁻¹' {z}).encard ≤ (C : ℕ∞)) (n : ℕ) :
    ∀ z, (K ∩ (f^[n]) ⁻¹' {z}).encard ≤ ((C ^ n : ℕ) : ℕ∞) := by
  classical
  induction n with
  | zero =>
    intro z
    calc
      _ ≤ ({z} : Set X).encard := by
        apply Set.encard_mono
        intro x hx
        simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.iterate_zero, id_eq] using hx.2
      _ = ((C ^ 0 : ℕ) : ℕ∞) := by simp
  | succ n ih =>
    intro z
    let S := K ∩ (f^[n]) ⁻¹' {z}
    have hS : S.Finite := Set.finite_of_encard_le_coe (ih z)
    let D := hS.toFinset
    have hD : D.card ≤ C ^ n := by
      have he : (D.card : ℕ∞) = S.encard := by
        simpa [D] using hS.encard_eq_coe_toFinset_card.symm
      exact_mod_cast (he.trans_le (ih z))
    calc
      _ ≤ (⋃ y ∈ D, K ∩ f ⁻¹' {y}).encard := by
        apply Set.encard_mono
        intro x hx
        refine mem_iUnion₂.mpr ⟨f x, ?_, ⟨hx.1, rfl⟩⟩
        change f x ∈ hS.toFinset
        rw [Set.Finite.mem_toFinset]
        refine ⟨hmap hx.1, ?_⟩
        simpa only [Set.mem_preimage, Set.mem_singleton_iff,
          Function.iterate_succ_apply] using hx.2
      _ ≤ ((D.card * C : ℕ) : ℕ∞) :=
        encard_finite_union_le _ D C (fun y _ => hC y)
      _ ≤ ((C ^ n * C : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.mul_le_mul_right C hD
      _ = ((C ^ (n + 1) : ℕ) : ℕ∞) := by rw [pow_succ]

end UniformFibres

/-- A selected, genuinely nondegenerate compact real interval. -/
structure Segment where
  left : ℝ
  right : ℝ
  proper : left < right

instance : Coe Segment (Set ℝ) := ⟨fun J => Icc J.left J.right⟩

namespace Segment

theorem nonempty (J : Segment) : (J : Set ℝ).Nonempty :=
  ⟨J.left, le_rfl, J.proper.le⟩

theorem infinite (J : Segment) : (J : Set ℝ).Infinite := Icc_infinite J.proper

theorem compact (J : Segment) : IsCompact (J : Set ℝ) := isCompact_Icc

end Segment

section ExactPullback

variable {G : ℝ → ℝ} {u v α β : ℝ}

/-- First upper-level hit followed by last lower-level hit selects an exact
interval pullback. The complete inverse image is never asserted to be an interval. -/
theorem exact_pullback_of_endpoint_values (huv : u < v) (hαβ : α < β)
    (hG : ContinuousOn G (Icc u v)) (hu : G u = α) (hv : G v = β) :
    ∃ J : Segment, (J : Set ℝ) ⊆ Icc u v ∧ G '' (J : Set ℝ) = Icc α β := by
  let S := Icc u v ∩ G ⁻¹' {β}
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hG.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hSn : S.Nonempty := ⟨v, ⟨⟨huv.le, le_rfl⟩, hv⟩⟩
  obtain ⟨s, hs⟩ := hSc.exists_isLeast hSn
  have hsu : u ≤ s := hs.1.1.1
  have hsv : s ≤ v := hs.1.1.2
  have hGs : G s = β := hs.1.2
  have hus : u < s := by
    rcases eq_or_lt_of_le hsu with he | he
    · have : α = β := hu.symm.trans ((congrArg G he).trans hGs)
      exact (hαβ.ne this).elim
    · exact he
  have hGus : ContinuousOn G (Icc u s) := hG.mono (Icc_subset_Icc le_rfl hsv)
  let R := Icc u s ∩ G ⁻¹' {α}
  have hRc : IsCompact R := isCompact_Icc.of_isClosed_subset
    (hGus.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨r, hr⟩ := hRc.exists_isGreatest ⟨u, ⟨⟨le_rfl, hus.le⟩, hu⟩⟩
  have hur : u ≤ r := hr.1.1.1
  have hrs : r ≤ s := hr.1.1.2
  have hGr : G r = α := hr.1.2
  have hrs' : r < s := by
    rcases eq_or_lt_of_le hrs with he | he
    · have : α = β := hGr.symm.trans ((congrArg G he).trans hGs)
      exact (hαβ.ne this).elim
    · exact he
  have hsub : Icc r s ⊆ Icc u v := Icc_subset_Icc hur hsv
  have hGrs : ContinuousOn G (Icc r s) := hG.mono hsub
  refine ⟨⟨r, s, hrs'⟩, hsub, subset_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · by_contra! hg
      have hrx : r < x := by
        rcases eq_or_lt_of_le hx.1 with he | he
        · subst x
          linarith
        · exact he
      have hxs : x ≤ s := hx.2
      have hGxs : ContinuousOn G (Icc x s) :=
        hG.mono (Icc_subset_Icc (hur.trans hx.1) hsv)
      have hvv : α ∈ Icc (G x) (G s) := ⟨hg.le, by rw [hGs]; exact hαβ.le⟩
      obtain ⟨y, hy, hGy⟩ := intermediate_value_Icc hxs hGxs hvv
      have hyr : y ≤ r := hr.2 ⟨⟨hur.trans (hx.1.trans hy.1), hy.2⟩, hGy⟩
      exact (not_lt_of_ge hyr) (hrx.trans_le hy.1)
    · by_contra! hg
      have hxs : x < s := by
        rcases eq_or_lt_of_le hx.2 with he | he
        · subst x
          linarith
        · exact he
      have hux : u ≤ x := hur.trans hx.1
      have hGux : ContinuousOn G (Icc u x) :=
        hG.mono (Icc_subset_Icc le_rfl (hx.2.trans hsv))
      have hvv : β ∈ Icc (G u) (G x) := ⟨by rw [hu]; exact hαβ.le, hg.le⟩
      obtain ⟨y, hy, hGy⟩ := intermediate_value_Icc hux hGux hvv
      have hsy : s ≤ y := hs.2 ⟨⟨hy.1, hy.2.trans (hx.2.trans hsv)⟩, hGy⟩
      exact (not_lt_of_ge hsy) (hy.2.trans_lt hxs)
  · simpa only [hGr, hGs] using intermediate_value_Icc hrs'.le hGrs

/-- Any nondegenerate compact target contained in an interval image has an
exact selected nondegenerate compact subinterval as pullback. -/
theorem exact_pullback (A D : Segment) (hG : ContinuousOn G (A : Set ℝ))
    (hD : (D : Set ℝ) ⊆ G '' (A : Set ℝ)) :
    ∃ J : Segment, (J : Set ℝ) ⊆ (A : Set ℝ) ∧
      G '' (J : Set ℝ) = (D : Set ℝ) := by
  obtain ⟨u, hu, hGu⟩ := hD (show D.left ∈ (D : Set ℝ) from ⟨le_rfl, D.proper.le⟩)
  obtain ⟨v, hv, hGv⟩ := hD (show D.right ∈ (D : Set ℝ) from ⟨D.proper.le, le_rfl⟩)
  rcases lt_trichotomy u v with huv | he | hvu
  · have hsub : Icc u v ⊆ (A : Set ℝ) := Icc_subset_Icc hu.1 hv.2
    obtain ⟨J, hJ, he⟩ := exact_pullback_of_endpoint_values huv D.proper
      (hG.mono hsub) hGu hGv
    exact ⟨J, hJ.trans hsub, he⟩
  · subst v
    exact (D.proper.ne (hGu.symm.trans hGv)).elim
  · have hsub : Icc v u ⊆ (A : Set ℝ) := Icc_subset_Icc hv.1 hu.2
    obtain ⟨J, hJ, he⟩ := exact_pullback_of_endpoint_values hvu
      (show -D.right < -D.left from neg_lt_neg D.proper) (hG.neg.mono hsub)
      (by change -G v = -D.right; rw [hGv]) (by change -G u = -D.left; rw [hGu])
    refine ⟨J, hJ.trans hsub, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hn : -G x ∈ Icc (-D.right) (-D.left) :=
        he.subset (mem_image_of_mem (fun x => -G x) hx)
      constructor <;> linarith [hn.1, hn.2]
    · intro hy
      have hn : -y ∈ Icc (-D.right) (-D.left) := by
        constructor <;> linarith [hy.1, hy.2]
      obtain ⟨x, hx, hxy⟩ := he.symm.subset hn
      exact ⟨x, hx, by change -G x = -y at hxy; linarith⟩

end ExactPullback

section MonotoneTrapping

variable {f : ℝ → ℝ}

/-- Monotonicity of iterates uses only the actual invariant set. -/
theorem monotoneOn_iterate {K : Set ℝ} (hm : MonotoneOn f K)
    (hmap : MapsTo f K K) (n : ℕ) : MonotoneOn (f^[n]) K := by
  induction n with
  | zero => exact fun _ _ _ _ h => h
  | succ n ih =>
    intro x hx y hy hxy
    simpa only [Function.iterate_succ_apply'] using
      hm (hmap.iterate n hx) (hmap.iterate n hy) (ih hx hy hxy)

/-- A strictly monotone bounded orbit has a whole tail of small gaps;
the individual gaps are not assumed monotone. -/
theorem increasing_orbit_small_segment (K : Segment)
    (hm : StrictMonoOn f (K : Set ℝ)) (hmap : MapsTo f (K : Set ℝ) (K : Set ℝ))
    {x ε : ℝ} (hx : x ∈ (K : Set ℝ)) (hstep₀ : x < f x) (hε : 0 < ε) :
    ∃ J : Segment, (J : Set ℝ) ⊆ (K : Set ℝ) ∧
      ∀ t : ℕ, ∀ u ∈ (J : Set ℝ), ∀ v ∈ (J : Set ℝ),
        dist (f^[t] u) (f^[t] v) < ε := by
  let a : ℕ → ℝ := fun n => f^[n] x
  have hamem : ∀ n, a n ∈ (K : Set ℝ) := fun n => hmap.iterate n hx
  have hastep : ∀ n, a n < a (n + 1) := by
    intro n
    induction n with
    | zero => simpa [a] using hstep₀
    | succ n ih =>
      simpa only [a, Function.iterate_succ_apply'] using
        hm (hamem n) (hamem (n + 1)) ih
  have ha : Monotone a := (strictMono_nat_of_lt_succ hastep).monotone
  have hb : BddAbove (Set.range a) := by
    refine ⟨K.right, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hamem n).2
  have hlim := tendsto_atTop_ciSup ha hb
  have hgap : Tendsto (fun n => a (n + 1) - a n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, sub_self] using (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
  obtain ⟨m, htail⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hgap).2 ε hε)
  let J : Segment := ⟨a m, a (m + 1), hastep m⟩
  have hJK : (J : Set ℝ) ⊆ (K : Set ℝ) :=
    Icc_subset_Icc (hamem m).1 (hamem (m + 1)).2
  refine ⟨J, hJK, ?_⟩
  intro t u hu v hv
  have hmono := monotoneOn_iterate hm.monotoneOn hmap t
  have hul := hmono (hamem m) (hJK hu) hu.1
  have huu := hmono (hJK hu) (hamem (m + 1)) hu.2
  have hvl := hmono (hamem m) (hJK hv) hv.1
  have hvu := hmono (hJK hv) (hamem (m + 1)) hv.2
  have hg := htail (t + m) (by omega)
  have hleft : f^[t] (a m) = a (t + m) := (Function.iterate_add_apply f t m x).symm
  have hright : f^[t] (a (m + 1)) = a (t + m + 1) := by
    simpa only [a, Nat.add_assoc] using (Function.iterate_add_apply f t (m + 1) x).symm
  rw [hleft] at hul hvl
  rw [hright] at huu hvu
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The downward-orbit case uses convergence to the infimum and positive gaps. -/
theorem decreasing_orbit_small_segment (K : Segment)
    (hm : StrictMonoOn f (K : Set ℝ)) (hmap : MapsTo f (K : Set ℝ) (K : Set ℝ))
    {x ε : ℝ} (hx : x ∈ (K : Set ℝ)) (hstep₀ : f x < x) (hε : 0 < ε) :
    ∃ J : Segment, (J : Set ℝ) ⊆ (K : Set ℝ) ∧
      ∀ t : ℕ, ∀ u ∈ (J : Set ℝ), ∀ v ∈ (J : Set ℝ),
        dist (f^[t] u) (f^[t] v) < ε := by
  let a : ℕ → ℝ := fun n => f^[n] x
  have hamem : ∀ n, a n ∈ (K : Set ℝ) := fun n => hmap.iterate n hx
  have hastep : ∀ n, a (n + 1) < a n := by
    intro n
    induction n with
    | zero => simpa [a] using hstep₀
    | succ n ih =>
      simpa only [a, Function.iterate_succ_apply'] using
        hm (hamem (n + 1)) (hamem n) ih
  have ha : Antitone a := (strictAnti_nat_of_succ_lt hastep).antitone
  have hb : BddBelow (Set.range a) := by
    refine ⟨K.left, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hamem n).1
  have hlim := tendsto_atTop_ciInf ha hb
  have hgap : Tendsto (fun n => a n - a (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, sub_self] using hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
  obtain ⟨m, htail⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hgap).2 ε hε)
  let J : Segment := ⟨a (m + 1), a m, hastep m⟩
  have hJK : (J : Set ℝ) ⊆ (K : Set ℝ) :=
    Icc_subset_Icc (hamem (m + 1)).1 (hamem m).2
  refine ⟨J, hJK, ?_⟩
  intro t u hu v hv
  have hmono := monotoneOn_iterate hm.monotoneOn hmap t
  have hul := hmono (hamem (m + 1)) (hJK hu) hu.1
  have huu := hmono (hJK hu) (hamem m) hu.2
  have hvl := hmono (hamem (m + 1)) (hJK hv) hv.1
  have hvu := hmono (hJK hv) (hamem m) hv.2
  have hg := htail (t + m) (by omega)
  have hleft : f^[t] (a m) = a (t + m) := (Function.iterate_add_apply f t m x).symm
  have hright : f^[t] (a (m + 1)) = a (t + m + 1) := by
    simpa only [a, Nat.add_assoc] using (Function.iterate_add_apply f t (m + 1) x).symm
  rw [hleft] at huu hvu
  rw [hright] at hul hvl
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Every increasing interval self-map has a nondegenerate interval whose
forward images are small at all times. No source-surjectivity is used. -/
theorem strictMonoOn_small_segment (K : Segment)
    (hm : StrictMonoOn f (K : Set ℝ)) (hmap : MapsTo f (K : Set ℝ) (K : Set ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : Segment, (J : Set ℝ) ⊆ (K : Set ℝ) ∧
      ∀ t : ℕ, ∀ u ∈ (J : Set ℝ), ∀ v ∈ (J : Set ℝ),
        dist (f^[t] u) (f^[t] v) < ε := by
  by_cases hid : ∀ x ∈ (K : Set ℝ), f x = x
  · let r := min K.right (K.left + ε / 2)
    have hlr : K.left < r := lt_min K.proper (by linarith)
    let J : Segment := ⟨K.left, r, hlr⟩
    have hJK : (J : Set ℝ) ⊆ (K : Set ℝ) := Icc_subset_Icc le_rfl (min_le_left _ _)
    refine ⟨J, hJK, ?_⟩
    intro t u hu v hv
    rw [Function.iterate_fixed (hid u (hJK hu)) t,
      Function.iterate_fixed (hid v (hJK hv)) t, Real.dist_eq, abs_lt]
    have hr : r ≤ K.left + ε / 2 := min_le_right _ _
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  · push_neg at hid
    obtain ⟨x, hx, hne⟩ := hid
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact decreasing_orbit_small_segment K hm hmap hx hlt hε
    · exact increasing_orbit_small_segment K hm hmap hx hgt hε

/-- Even images are controlled under f²; compact uniform continuity controls
all odd images, with the same strict requested scale. -/
theorem strictly_monotone_small_segment (K : Segment)
    (hf : ContinuousOn f (K : Set ℝ)) (hmap : MapsTo f (K : Set ℝ) (K : Set ℝ))
    (hm : StrictMonoOn f (K : Set ℝ) ∨ StrictAntiOn f (K : Set ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : Segment, (J : Set ℝ) ⊆ (K : Set ℝ) ∧
      ∀ t : ℕ, ∀ u ∈ (J : Set ℝ), ∀ v ∈ (J : Set ℝ),
        dist (f^[t] u) (f^[t] v) < ε := by
  rcases hm with hm | ha
  · exact strictMonoOn_small_segment K hm hmap hε
  · obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
      (K.compact.uniformContinuousOn_of_continuous hf) ε hε
    have hm₂ : StrictMonoOn (f^[2]) (K : Set ℝ) := by
      simpa [Function.iterate_succ] using ha.comp ha hmap
    obtain ⟨J, hJK, hJ⟩ := strictMonoOn_small_segment K hm₂ (hmap.iterate 2)
      (lt_min hδ hε)
    refine ⟨J, hJK, ?_⟩
    intro t u hu v hv
    have hpair : dist (f^[2 * (t / 2)] u) (f^[2 * (t / 2)] v) < min δ ε := by
      simpa only [Function.iterate_mul] using hJ (t / 2) u hu v hv
    have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hmod with hmod | hmod
    · have ht : t = 2 * (t / 2) := by omega
      rw [ht]
      exact hpair.trans_le (min_le_right _ _)
    · have ht : t = 1 + 2 * (t / 2) := by omega
      rw [ht, Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_one]
      exact hd _ (hmap.iterate _ (hJK hu)) _ (hmap.iterate _ (hJK hv))
        (hpair.trans_le (min_le_left _ _))

/-- Only monotone trapping intervals are excluded at this stage of the proof. -/
theorem no_strictly_monotone_trapping {I : Set ℝ} (hI : IsCompact I)
    (hf : ContinuousOn f I) (hmap : MapsTo f I I) {ε : ℝ} {N p : ℕ}
    (hε : 0 < ε) (hB : ForwardBowenBound f I ε N) (hp : 0 < p)
    (K : Segment) (hKI : (K : Set ℝ) ⊆ I)
    (htrap : MapsTo (f^[p]) (K : Set ℝ) (K : Set ℝ))
    (hm : StrictMonoOn (f^[p]) (K : Set ℝ) ∨
      StrictAntiOn (f^[p]) (K : Set ℝ)) : False := by
  obtain ⟨δ, hδ, hBδ⟩ := forwardBowenBound_iterate hI hf hmap hε hB hp
  obtain ⟨J, hJK, hJ⟩ := strictly_monotone_small_segment K
    ((hf.iterate hmap p).mono hKI) htrap hm hδ
  obtain ⟨x, hx⟩ := J.nonempty
  exact J.infinite (finite_of_all_times_small hBδ (hJK.trans hKI) x hx
    (fun y hy t => hJ t x hx y hy))

end MonotoneTrapping

section OverlapOrder

variable {F : ℝ → ℝ} {S T : Set ℝ}

/-- Strict monotonicity glues on order-connected sets that actually meet. -/
theorem strictMonoOn_union_overlap (hS : OrdConnected S) (hT : OrdConnected T)
    (hST : (S ∩ T).Nonempty) (hFS : StrictMonoOn F S) (hFT : StrictMonoOn F T) :
    StrictMonoOn F (S ∪ T) := by
  obtain ⟨z, hzS, hzT⟩ := hST
  have cross : ∀ {A B : Set ℝ}, OrdConnected A → OrdConnected B →
      z ∈ A → z ∈ B → StrictMonoOn F A → StrictMonoOn F B →
      ∀ {x y : ℝ}, x ∈ A → y ∈ B → x < y → F x < F y := by
    intro A B hA hB hzA hzB hFA hFB x y hx hy hxy
    by_cases hyA : y ∈ A
    · exact hFA hx hyA hxy
    by_cases hxB : x ∈ B
    · exact hFB hxB hy hxy
    have hxz : x < z := by
      by_contra! hz
      exact hxB (hB.out hzB hy ⟨hz, hxy.le⟩)
    have hzy : z < y := by
      by_contra! hyz
      exact hyA (hA.out hx hzA ⟨hxy.le, hyz⟩)
    exact (hFA hx hzA hxz).trans (hFB hzB hy hzy)
  intro x hx y hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hFS hx hy hxy
  · exact cross hS hT hzS hzT hFS hFT hx hy hxy
  · exact cross hT hS hzT hzS hFT hFS hx hy hxy
  · exact hFT hx hy hxy

/-- Nondegenerate overlap forces the orientations of two continuous injective
interval restrictions to agree; their actual union is then strictly monotone. -/
theorem strictly_monotone_union_of_injective (A B H : Segment)
    (hHA : (H : Set ℝ) ⊆ (A : Set ℝ)) (hHB : (H : Set ℝ) ⊆ (B : Set ℝ))
    (hFA : ContinuousOn F (A : Set ℝ)) (hFB : ContinuousOn F (B : Set ℝ))
    (hiA : InjOn F (A : Set ℝ)) (hiB : InjOn F (B : Set ℝ)) :
    StrictMonoOn F ((A : Set ℝ) ∪ (B : Set ℝ)) ∨
      StrictAntiOn F ((A : Set ℝ) ∪ (B : Set ℝ)) := by
  have huH : H.left ∈ (H : Set ℝ) := ⟨le_rfl, H.proper.le⟩
  have hvH : H.right ∈ (H : Set ℝ) := ⟨H.proper.le, le_rfl⟩
  have hmeet : ((A : Set ℝ) ∩ (B : Set ℝ)).Nonempty :=
    ⟨H.left, hHA huH, hHB huH⟩
  rcases hFA.strictMonoOn_of_injOn_Icc' A.proper.le hiA with hmA | haA
  · rcases hFB.strictMonoOn_of_injOn_Icc' B.proper.le hiB with hmB | haB
    · exact Or.inl (strictMonoOn_union_overlap ordConnected_Icc ordConnected_Icc hmeet hmA hmB)
    · exact (not_lt_of_gt (hmA (hHA huH) (hHA hvH) H.proper)
        (haB (hHB huH) (hHB hvH) H.proper)).elim
  · rcases hFB.strictMonoOn_of_injOn_Icc' B.proper.le hiB with hmB | haB
    · exact (not_lt_of_gt (hmB (hHB huH) (hHB hvH) H.proper)
        (haA (hHA huH) (hHA hvH) H.proper)).elim
    · have hnA : StrictMonoOn (fun x => -F x) (A : Set ℝ) :=
        fun x hx y hy hxy => neg_lt_neg (haA hx hy hxy)
      have hnB : StrictMonoOn (fun x => -F x) (B : Set ℝ) :=
        fun x hx y hy hxy => neg_lt_neg (haB hx hy hxy)
      have hn := strictMonoOn_union_overlap ordConnected_Icc ordConnected_Icc hmeet hnA hnB
      exact Or.inr (fun x hx y hy hxy => neg_lt_neg_iff.mp (hn hx hy hxy))

/-- Continuity extends order monotonicity from an actual set to its closure. -/
theorem monotoneOn_closure (hF : ContinuousOn F (closure S)) (hm : MonotoneOn F S) :
    MonotoneOn F (closure S) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with he | hxy
  · subst y
    exact le_rfl
  obtain ⟨a, haS, ha⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨b, hbS, hb⟩ := mem_closure_iff_seq_limit.mp hy
  have ha' : Tendsto a atTop (𝓝[closure S] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha, Filter.Eventually.of_forall
      (fun n => subset_closure (haS n))⟩
  have hb' : Tendsto b atTop (𝓝[closure S] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hb, Filter.Eventually.of_forall
      (fun n => subset_closure (hbS n))⟩
  apply le_of_tendsto_of_tendsto ((hF x hx).tendsto.comp ha') ((hF y hy).tendsto.comp hb')
  exact (ha.eventually_lt hb hxy).mono (fun n hn => hm (haS n) (hbS n) hn.le)

/-- A weakly monotone interval map with finite fibres is actually strict. -/
theorem strictMonoOn_of_monotoneOn_finite_fibres (hS : OrdConnected S)
    (hm : MonotoneOn F S) (hfib : ∀ z, (S ∩ F ⁻¹' {z}).Finite) : StrictMonoOn F S := by
  intro x hx y hy hxy
  apply lt_of_le_of_ne (hm hx hy hxy.le)
  intro he
  have hsub : Icc x y ⊆ S ∩ F ⁻¹' {F x} := by
    intro z hz
    have hzS := hS.out hx hy hz
    refine ⟨hzS, le_antisymm ?_ (hm hx hzS hz.1)⟩
    exact (hm hzS hy hz.2).trans he.symm.le
  exact Icc_infinite hxy ((hfib (F x)).subset hsub)

/-- The closure step keeps strictness by finite fibres, not by assuming the
extension of an injective map to its closure remains injective. -/
theorem strictly_monotone_closure (hS : OrdConnected (closure S))
    (hF : ContinuousOn F (closure S))
    (hfib : ∀ z, (closure S ∩ F ⁻¹' {z}).Finite)
    (hm : StrictMonoOn F S ∨ StrictAntiOn F S) :
    StrictMonoOn F (closure S) ∨ StrictAntiOn F (closure S) := by
  rcases hm with hm | ha
  · exact Or.inl (strictMonoOn_of_monotoneOn_finite_fibres hS
      (monotoneOn_closure hF hm.monotoneOn) hfib)
  · have hn : MonotoneOn (fun x => -F x) S :=
      fun x hx y hy hxy => neg_le_neg (ha.antitoneOn hx hy hxy)
    have hnfib : ∀ z, (closure S ∩ (fun x => -F x) ⁻¹' {z}).Finite := by
      intro z
      apply (hfib (-z)).subset
      intro x hx
      exact ⟨hx.1, by change F x = -z; have he : -F x = z := hx.2; linarith⟩
    have hs := strictMonoOn_of_monotoneOn_finite_fibres hS
      (monotoneOn_closure hF.neg hn) hnfib
    exact Or.inr (fun x hx y hy hxy => neg_lt_neg_iff.mp (hs hx hy hxy))

end OverlapOrder

end IntervalObstruction
end D5.S1.Dynamics.Shadowing
