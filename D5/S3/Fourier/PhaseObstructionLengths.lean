/- GID: D5/S3/Fourier/PhaseObstructionLengths
   generality: G
   mirror-B: D5/B/S3/Fourier/PhaseObstructionLengths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Aggregate weighted phase obstructions across integer relation lengths. -/

import D5.S3.Fourier.ShortPhaseRelations
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Dropping high-loss coordinates at a common time bounds the minimum omission
at each relation length. Telescoping weights let the resulting bounds be summed. -/

set_option autoImplicit false

open Set Filter
open scoped BigOperators Topology

namespace D5.S3.Fourier.PhaseObstructionLengths

open D5.S3.Fourier.ShortPhaseRelations (large_loss_of_short_relation)

noncomputable section

variable {J : Type*} [DecidableEq J]

/-- The total weight of a finite index set. -/
def mass (s : Finset J) (w : J → ℝ) : ℝ := ∑ j ∈ s, w j

/-- The normalized weighted sine score at one real time. -/
def average (s : Finset J) (g w : J → ℝ) (t : ℝ) : ℝ :=
  (∑ j ∈ s, w j * Real.sin (g j * t)) / mass s w

/-- The deficit of the best common-time average over the allowed times. -/
def deficit (s : Finset J) (g w : J → ℝ) (T : Set ℝ) : ℝ :=
  1 - sSup (average s g w '' T)

/-- All relations of length at most `h` on the retained set have sum divisible by four. -/
def Good (u : Finset J) (g : J → ℝ) (h : ℕ) : Prop :=
  ∀ k : J → ℤ, (∑ j ∈ u, (k j : ℝ) * g j) = 0 →
    (∑ j ∈ u, |(k j : ℝ)|) ≤ (h : ℝ) → (4 : ℤ) ∣ ∑ j ∈ u, k j

private def costs (s : Finset J) (g w : J → ℝ) (h : ℕ) : Set ℝ :=
  {p | ∃ u ⊆ s, Good u g h ∧ p = mass (s \ u) w / mass s w}

/-- The least weight fraction omitted to meet the length cutoff. -/
def omissionFraction (s : Finset J) (g w : J → ℝ) (h : ℕ) : ℝ := sInf (costs s g w h)

omit [DecidableEq J] in
private theorem empty_good (g : J → ℝ) (h : ℕ) : Good ∅ g h := by
  intro k _ _
  simp

private theorem costs_nonempty (s : Finset J) (g w : J → ℝ) (h : ℕ) :
    (costs s g w h).Nonempty :=
  ⟨_, ∅, Finset.empty_subset _, empty_good g h, rfl⟩

private theorem costs_nonneg (s : Finset J) (g w : J → ℝ) (h : ℕ)
    (hw : ∀ j ∈ s, 0 ≤ w j) : ∀ p ∈ costs s g w h, 0 ≤ p := by
  rintro _ ⟨u, _, _, rfl⟩
  exact div_nonneg (Finset.sum_nonneg fun j hj => hw j (Finset.mem_sdiff.mp hj).1)
    (Finset.sum_nonneg hw)

private theorem p_nonneg (s : Finset J) (g w : J → ℝ) (h : ℕ)
    (hw : ∀ j ∈ s, 0 ≤ w j) : 0 ≤ omissionFraction s g w h :=
  le_csInf (costs_nonempty s g w h) (costs_nonneg s g w h hw)

private theorem p_le_of_good {s u : Finset J} {g w : J → ℝ} {h : ℕ}
    (hw : ∀ j ∈ s, 0 ≤ w j) (hu : u ⊆ s) (hg : Good u g h) :
    omissionFraction s g w h ≤ mass (s \ u) w / mass s w :=
  csInf_le ⟨0, costs_nonneg s g w h hw⟩ ⟨u, hu, hg, rfl⟩

private theorem p_le_one (s : Finset J) (g w : J → ℝ) (h : ℕ)
    (hw : ∀ j ∈ s, 0 ≤ w j) : omissionFraction s g w h ≤ 1 := by
  refine (p_le_of_good hw (Finset.empty_subset s) (empty_good g h)).trans ?_
  simp only [Finset.sdiff_empty]
  by_cases hmass : mass s w = 0 <;> simp [hmass]

private theorem p_mono (s : Finset J) (g w : J → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j) :
    Monotone (omissionFraction s g w) := by
  intro h k hhk
  apply le_csInf (costs_nonempty s g w k)
  rintro _ ⟨u, hu, hg, rfl⟩
  apply p_le_of_good hw hu
  intro r hr hlen
  exact hg r hr (hlen.trans (by exact_mod_cast hhk))

private def scale (h : ℕ) : ℝ := 1 / (h : ℝ) ^ 2

/-- The inverse-square scale at length `n + 1`. -/
abbrev shiftedScale (n : ℕ) : ℝ := scale (n + 1)

/-- The difference between successive inverse-square scales. -/
def scaleDifference (n : ℕ) : ℝ := shiftedScale n - shiftedScale (n + 1)

/-- The length-`h` contribution to the simultaneous bound. -/
def summand (s : Finset J) (g w : J → ℝ) (h : ℕ) : ℝ :=
  (scale h - scale (h + 1)) * omissionFraction s g w h

private abbrev term (s : Finset J) (g w : J → ℝ) (n : ℕ) : ℝ :=
  summand s g w (n + 1)

/-- The bound obtained using length `h` alone. -/
def perScale (s : Finset J) (g w : J → ℝ) (h : ℕ) : ℝ :=
  omissionFraction s g w h / (h : ℝ) ^ 2

private abbrev single (s : Finset J) (g w : J → ℝ) (n : ℕ) : ℝ :=
  perScale s g w (n + 1)

/-- The single-length bound is the omission fraction times its inverse-square scale. -/
theorem perScale_eq_mul (s : Finset J) (g w : J → ℝ) (n : ℕ) :
    perScale s g w (n + 1) = shiftedScale n * omissionFraction s g w (n + 1) := by
  simp only [scale, perScale, div_mul_eq_mul_div, one_mul]

/-- Each inverse-square scale is nonnegative. -/
theorem shiftedScale_nonneg (n : ℕ) : 0 ≤ shiftedScale n := by
  change 0 ≤ scale (n + 1)
  unfold scale
  positivity

/-- The inverse-square scales decrease with the length index. -/
theorem shiftedScale_antitone : Antitone shiftedScale := by
  intro n m h
  simp only [scale, Nat.cast_add, Nat.cast_one]
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add_left (by exact_mod_cast h) 1

private theorem c_nonneg (n : ℕ) : 0 ≤ scaleDifference n :=
  sub_nonneg.mpr (shiftedScale_antitone (Nat.le_succ n))

private theorem term_nonneg (s : Finset J) (g w : J → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j)
    (n : ℕ) : 0 ≤ term s g w n := mul_nonneg (c_nonneg n) (p_nonneg s g w _ hw)

private theorem finite_layer (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (∑ n ∈ Finset.range N, if shiftedScale n ≤ x then scaleDifference n else 0) +
      (if shiftedScale N ≤ x then shiftedScale N else 0) ≤ x := by
  have aux (N : ℕ) :
      (∑ n ∈ Finset.range N, if shiftedScale n ≤ x then scaleDifference n else 0) ≤
        if shiftedScale N ≤ x then x - shiftedScale N else 0 := by
    induction N with
    | zero =>
      rw [Finset.sum_range_zero]
      split_ifs with h
      · exact sub_nonneg.mpr h
      · exact le_rfl
    | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : shiftedScale n ≤ x
      · have hnext := (shiftedScale_antitone (Nat.le_succ n)).trans h
        rw [ite_eq_left h] at ih
        rw [ite_eq_left h, ite_eq_left hnext, scaleDifference]
        linarith only [ih]
      · rw [ite_eq_right h] at ih
        rw [ite_eq_right h, add_zero]
        apply ih.trans
        split_ifs with hnext
        · exact sub_nonneg.mpr hnext
        · exact le_rfl
  have h := aux N
  split_ifs at h ⊢
  · linarith only [h]
  · simpa only [add_zero] using h.trans hx

private theorem partial_eq (s : Finset J) (g w : J → ℝ) (N : ℕ) :
    (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) =
      (∑ n ∈ Finset.range N, term s g w n) := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [Nat.add_comm 1]

/-- All lengths in the finite sum are controlled at the same time `t`. -/
theorem simultaneous_bound (s : Finset J) (g w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (t : ℝ) (N : ℕ) :
    let A := average s g w t
    (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) +
      perScale s g w (N + 1) ≤ 1 - A := by
  dsimp only
  rw [partial_eq]
  by_cases hzero : mass s w = 0
  · have hP (h : ℕ) : omissionFraction s g w h = 0 := by
      refine le_antisymm ((p_le_of_good hw (Finset.empty_subset s) (empty_good g h)).trans ?_)
        (p_nonneg s g w h hw)
      simp [hzero]
    simp [summand, perScale, average, hzero, hP]
  have hW : 0 < mass s w := lt_of_le_of_ne (Finset.sum_nonneg hw) (Ne.symm hzero)
  classical
  let loss (j : J) := 1 - Real.sin (g j * t)
  let cut (n : ℕ) := s.filter fun j => loss j < shiftedScale n
  have hcut (n : ℕ) : Good (cut n) g (n + 1) := by
    intro k hr hlen
    by_contra hb
    have hH : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    obtain ⟨j, hj, _, hjloss⟩ :=
      large_loss_of_short_relation (cut n) g k
        ((n : ℝ) + 1) t hH hr hb (by simpa only [Nat.cast_add, Nat.cast_one] using hlen)
    exact (not_lt_of_ge hjloss)
      (by simpa only [scale, Nat.cast_add, Nat.cast_one] using (Finset.mem_filter.mp hj).2)
  have hmass (n : ℕ) :
      mass (s \ cut n) w = ∑ j ∈ s, if shiftedScale n ≤ loss j then w j else 0 := by
    unfold mass
    rw [← Finset.sum_filter]
    congr 1
    ext j
    by_cases hj : j ∈ s <;> simp [cut, hj, not_lt]
  have hpoint (n : ℕ) (b : ℝ) (hb : 0 ≤ b) :
      (b * omissionFraction s g w (n + 1)) * mass s w ≤
        ∑ j ∈ s, w j * (if shiftedScale n ≤ loss j then b else 0) := by
    have hp := p_le_of_good hw (Finset.filter_subset _ _) (hcut n)
    calc
      _ ≤ b * mass (s \ cut n) w := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hW).mp hp) hb
      _ = _ := by
        rw [hmass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
  have hloss : (1 - average s g w t) * mass s w = ∑ j ∈ s, w j * loss j := by
    rw [average, sub_mul, one_mul, div_mul_cancel₀ _ hW.ne', mass, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [loss]
    ring
  apply le_of_mul_le_mul_right _ hW
  rw [hloss, add_mul, Finset.sum_mul, perScale_eq_mul]
  calc
    _ ≤ (∑ n ∈ Finset.range N, ∑ j ∈ s, w j * (if shiftedScale n ≤ loss j then scaleDifference n else 0)) +
        ∑ j ∈ s, w j * (if shiftedScale N ≤ loss j then shiftedScale N else 0) :=
      add_le_add (Finset.sum_le_sum fun n _ => hpoint n (scaleDifference n) (c_nonneg n))
        (hpoint N (shiftedScale N) (shiftedScale_nonneg N))
    _ = ∑ j ∈ s, w j * ((∑ n ∈ Finset.range N, if shiftedScale n ≤ loss j then scaleDifference n else 0) +
        (if shiftedScale N ≤ loss j then shiftedScale N else 0)) := by
      rw [Finset.sum_comm, ← Finset.sum_add_distrib]
      simp only [mul_add, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (finite_layer (loss j) (sub_nonneg.mpr (Real.sin_le_one _)) N)
        (hw j hj)

private theorem p_attained (s : Finset J) (g w : J → ℝ) (h : ℕ) :
    IsLeast (costs s g w h) (omissionFraction s g w h) := by
  have hfin : (costs s g w h).Finite := by
    refine ((Finset.finite_toSet s.powerset).image
      (fun u => mass (s \ u) w / mass s w)).subset ?_
    rintro _ ⟨u, hu, _, rfl⟩
    exact ⟨u, Finset.mem_powerset.mpr hu, rfl⟩
  have hn := costs_nonempty s g w h
  have hb := hfin.bddBelow
  exact ⟨hfin.isClosed.csInf_mem hn hb, (isGLB_csInf hn hb).1⟩

omit [DecidableEq J] in
private theorem good_iff_supported {s u : Finset J} (hu : u ⊆ s) (g : J → ℝ) (h : ℕ) :
    Good u g h ↔ ∀ k : J → ℤ, (∀ j ∉ u, k j = 0) →
      (∑ j ∈ s, (k j : ℝ) * g j) = 0 →
      (∑ j ∈ s, |k j|) ≤ (h : ℤ) → (4 : ℤ) ∣ ∑ j ∈ s, k j := by
  have heq (k : J → ℤ) (hz : ∀ j ∉ u, k j = 0) :
      (∑ j ∈ u, (k j : ℝ) * g j) = (∑ j ∈ s, (k j : ℝ) * g j) ∧
      (∑ j ∈ u, |k j|) = (∑ j ∈ s, |k j|) ∧
      (∑ j ∈ u, k j) = (∑ j ∈ s, k j) := by
    refine ⟨Finset.sum_subset hu ?_, Finset.sum_subset hu ?_, Finset.sum_subset hu ?_⟩
    · intro j _ hj
      simp [hz j hj]
    · intro j _ hj
      simp [hz j hj]
    · intro j _ hj
      exact hz j hj
  constructor
  · intro hg k hz hr hl
    have ⟨hrel, hnorm, hsum⟩ := heq k hz
    rw [← hsum]
    apply hg k (hrel.trans hr)
    have hnorm' := hnorm.trans_le hl
    exact_mod_cast hnorm'
  · intro hg k hr hl
    classical
    let k' (j : J) : ℤ := if j ∈ u then k j else 0
    have hz : ∀ j ∉ u, k' j = 0 := by intro j hj; simp [k', hj]
    have ⟨hrel, hnorm, hsum⟩ := heq k' hz
    have heq' (j : J) (hj : j ∈ u) : k' j = k j := by simp [k', hj]
    simp only [Finset.sum_congr rfl heq'] at hsum
    rw [hsum]
    apply hg k' hz
    · rw [← hrel, ← hr]
      exact Finset.sum_congr rfl fun j hj => by rw [heq' j hj]
    · rw [← hnorm]
      have hl' : (∑ j ∈ u, |(k' j : ℝ)|) ≤ (h : ℝ) := by
        convert hl using 1
        exact Finset.sum_congr rfl fun j hj => by rw [heq' j hj]
      exact_mod_cast hl'

/-- The infimum is attained for relations supported in the retained set. -/
theorem omissionFraction_isLeast (s : Finset J) (g w : J → ℝ) (h : ℕ) :
    let P := omissionFraction s g w h
    IsLeast {p | ∃ u ⊆ s, (∀ k : J → ℤ, (∀ j ∉ u, k j = 0) →
      (∑ j ∈ s, (k j : ℝ) * g j) = 0 →
      (∑ j ∈ s, |k j|) ≤ (h : ℤ) → (4 : ℤ) ∣ ∑ j ∈ s, k j) ∧
      p = mass (s \ u) w / mass s w} P := by
  dsimp only
  convert p_attained s g w h using 1
  ext p
  constructor
  · rintro ⟨u, hu, hg, rfl⟩
    exact ⟨u, hu, (good_iff_supported hu g h).mpr hg, rfl⟩
  · rintro ⟨u, hu, hg, rfl⟩
    exact ⟨u, hu, (good_iff_supported hu g h).mp hg, rfl⟩

private theorem shiftedScale_tendsto : Tendsto shiftedScale atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((↑(n + 1) : ℝ) ^ 2)) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_one, div_pow, one_pow,
    zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2

private theorem sum_c (m N : ℕ) :
    (∑ n ∈ Finset.range N, scaleDifference (n + m)) = shiftedScale m - shiftedScale (m + N) := by
  have h := Finset.sum_range_sub (fun n => -shiftedScale (n + m)) N
  simpa only [scaleDifference, Nat.add_comm m N, Nat.zero_add, Nat.add_right_comm, neg_sub_neg] using h

/-- The weights from a shifted length index sum to its scale. -/
theorem scaleDifference_hasSum (m : ℕ) : HasSum (fun n => scaleDifference (n + m)) (shiftedScale m) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => c_nonneg (n + m)) _).mpr
  simp_rw [sum_c, Nat.add_comm m]
  simpa only [Function.comp_def, sub_zero] using
    tendsto_const_nhds.sub (shiftedScale_tendsto.comp (tendsto_add_atTop_nat m))

private theorem term_le_c (s : Finset J) (g w : J → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j) (n : ℕ) :
    term s g w n ≤ scaleDifference n := by
  change scaleDifference n * omissionFraction s g w (n + 1) ≤ scaleDifference n
  exact mul_le_of_le_one_right (c_nonneg n) (p_le_one s g w _ hw)

private theorem finite_bound (s : Finset J) (g w : J → ℝ) (T : Set ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (N : ℕ) :
    (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) + perScale s g w (N + 1) ≤
      deficit s g w T := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · rw [deficit, Set.image_empty, Real.sSup_empty, sub_zero, partial_eq, perScale_eq_mul]
    calc
      _ ≤ (∑ n ∈ Finset.range N, scaleDifference n) + shiftedScale N :=
        add_le_add (Finset.sum_le_sum fun n _ => term_le_c s g w hw n)
          (mul_le_of_le_one_right (shiftedScale_nonneg N) (p_le_one s g w _ hw))
      _ = 1 := by
        have h := sum_c 0 N
        simp only [Nat.add_zero, Nat.zero_add] at h
        rw [h, sub_add_cancel]
        norm_num [scale]
  · rw [deficit, le_sub_comm]
    apply csSup_le (hT.image _)
    rintro _ ⟨t, _, rfl⟩
    exact le_sub_comm.mp (simultaneous_bound s g w hw t N)

private theorem term_tail_summable (s : Finset J) (g w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (m : ℕ) : Summable (fun n => term s g w (n + m)) :=
  Summable.of_nonneg_of_le (fun n => term_nonneg s g w hw (n + m))
    (fun n => term_le_c s g w hw (n + m)) (scaleDifference_hasSum m).summable

private theorem series_split (s : Finset J) (g w : J → ℝ) (m : ℕ)
    (hsum : Summable (fun n => term s g w (n + m))) :
    (∑ h ∈ Finset.Ico 1 (m + 1), summand s g w h) + (∑' n, term s g w (n + m)) =
      ∑' n, term s g w n := by
  rw [partial_eq]
  exact hsum.hasSum.sum_range_add.tsum_eq.symm

/-- The aggregate converges and its remainder is bounded at every cutoff. -/
theorem aggregate_bounds (s : Finset J) (g w : J → ℝ) (T : Set ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) :
    let D := deficit s g w T
    let L := ∑' n, summand s g w (n + 1)
    (∀ N : ℕ, (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) +
      perScale s g w (N + 1) ≤ D) ∧
      HasSum (fun n => summand s g w (n + 1)) L ∧
      sSup (perScale s g w '' Set.Ici 1) ≤ L ∧ L ≤ D ∧
      (∀ N : ℕ, let S := ∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h
        perScale s g w (N + 1) ≤ L - S ∧ L - S ≤ 1 / ((N + 1 : ℕ) : ℝ) ^ 2) := by
  dsimp only
  have hsum : Summable (term s g w) := by simpa using term_tail_summable s g w hw 0
  have hsingle (m : ℕ) : 0 ≤ perScale s g w (m + 1) := by
    rw [perScale_eq_mul s g w m]
    exact mul_nonneg (shiftedScale_nonneg m) (p_nonneg s g w _ hw)
  have hfinite := finite_bound s g w T hw
  have hpartial (N : ℕ) :
      (∑ n ∈ Finset.range N, term s g w n) ≤ deficit s g w T := by
    rw [← partial_eq]
    exact (le_add_of_nonneg_right (hsingle N)).trans (hfinite N)
  have htail (m : ℕ) :
      perScale s g w (m + 1) ≤ (∑' n, term s g w (n + m)) ∧
        (∑' n, term s g w (n + m)) ≤ shiftedScale m := by
    have ht := (term_tail_summable s g w hw m).hasSum
    refine ⟨?_, hasSum_le (fun n => term_le_c s g w hw (n + m)) ht (scaleDifference_hasSum m)⟩
    rw [perScale_eq_mul s g w m]
    refine hasSum_le (fun n => mul_le_mul_of_nonneg_left ?_ (c_nonneg (n + m)))
      ((scaleDifference_hasSum m).mul_right _) ht
    exact p_mono s g w hw (by omega)
  refine ⟨hfinite, hsum.hasSum, ?_, hsum.tsum_le_of_sum_range_le hpartial, ?_⟩
  · apply csSup_le (Set.nonempty_Ici.image _)
    rintro _ ⟨h, hh, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, (Nat.sub_add_cancel hh).symm⟩
    rw [← series_split s g w m (term_tail_summable s g w hw m)]
    rw [partial_eq]
    exact (htail m).1.trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun n _ => term_nonneg s g w hw n))
  · intro N
    rw [← series_split s g w N (term_tail_summable s g w hw N), add_sub_cancel_left]
    exact htail N

def exampleFreq (j : Fin 3) : ℝ := j.val

def exampleWeight (j : Fin 3) : ℝ := if j = 0 then 1 / 2 else 1 / 4

private theorem exampleWeights_pos (j : Fin 3) : 0 < exampleWeight j := by
  unfold exampleWeight
  split_ifs <;> norm_num

private theorem sum_on_fin3 {A : Type*} [AddCommMonoid A] (u : Finset (Fin 3))
    (f : Fin 3 → A) :
    (∑ j ∈ u, f j) =
      (if 0 ∈ u then f 0 else 0) + (if 1 ∈ u then f 1 else 0) +
        (if 2 ∈ u then f 2 else 0) := by
  have heq : u = Finset.univ.filter (fun j => j ∈ u) := by ext j; simp
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j => j ∈ u), f j := by rw [← heq]
    _ = _ := by rw [Finset.sum_filter, Fin.sum_univ_three]

private theorem exampleMass_univ : mass Finset.univ exampleWeight = 1 := by
  norm_num [mass, Fin.sum_univ_three, exampleWeight]

private theorem exampleOmitted (u : Finset (Fin 3)) :
    mass (Finset.univ \ u) exampleWeight / mass Finset.univ exampleWeight =
      (if 0 ∈ u then 0 else 1 / 2) +
        (if 1 ∈ u then 0 else 1 / 4) + (if 2 ∈ u then 0 else 1 / 4) := by
  rw [exampleMass_univ, div_one]
  simp only [mass, sum_on_fin3, Finset.mem_sdiff, Finset.mem_univ,
    true_and, ite_not]
  norm_num [exampleWeight]

private theorem zero_not_kept (u : Finset (Fin 3)) (h : ℕ) (hh : 1 ≤ h)
    (hg : Good u exampleFreq h) : (0 : Fin 3) ∉ u := by
  intro h0
  let k : Fin 3 → ℤ := ![1, 0, 0]
  have hr : (∑ j ∈ u, (k j : ℝ) * exampleFreq j) = 0 := by
    norm_num [sum_on_fin3, k, exampleFreq]
  have hl : (∑ j ∈ u, |(k j : ℝ)|) ≤ (h : ℝ) := by
    simpa [sum_on_fin3, k, h0] using (show (1 : ℝ) ≤ (h : ℝ) by exact_mod_cast hh)
  have hb := hg k hr hl
  norm_num [sum_on_fin3, k, h0] at hb

private theorem one_two_not_kept (u : Finset (Fin 3)) (h : ℕ) (hh : 3 ≤ h)
    (hg : Good u exampleFreq h) : ¬ ((1 : Fin 3) ∈ u ∧ (2 : Fin 3) ∈ u) := by
  rintro ⟨h1, h2⟩
  let k : Fin 3 → ℤ := ![0, 2, -1]
  have hr : (∑ j ∈ u, (k j : ℝ) * exampleFreq j) = 0 := by
    norm_num [sum_on_fin3, k, exampleFreq, h1, h2]
  have hl : (∑ j ∈ u, |(k j : ℝ)|) ≤ (h : ℝ) := by
    convert (show (3 : ℝ) ≤ (h : ℝ) by exact_mod_cast hh) using 1
    norm_num [sum_on_fin3, k, h1, h2]
  have hb := hg k hr hl
  norm_num [sum_on_fin3, k, h1, h2] at hb

private theorem pair_good (h : ℕ) (hh : h ≤ 2) :
    Good ({1, 2} : Finset (Fin 3)) exampleFreq h := by
  intro k hr hl
  have hr' : (k 1 : ℝ) + (k 2 : ℝ) * 2 = 0 := by
    simpa [sum_on_fin3, exampleFreq] using hr
  have hl' : |(k 1 : ℝ)| + |(k 2 : ℝ)| ≤ (h : ℝ) := by
    simpa [sum_on_fin3] using hl
  have hk2 : k 2 = 0 := by
    by_contra hne
    have habs : (1 : ℝ) ≤ |(k 2 : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have hk1eq : (k 1 : ℝ) = -(k 2 : ℝ) * 2 := by linarith only [hr']
    have hh' : (h : ℝ) ≤ 2 := by exact_mod_cast hh
    rw [hk1eq, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hl'
    linarith only [hl', habs, hh']
  have hk1 : k 1 = 0 := by
    have hzero : (k 1 : ℝ) = 0 := by simpa [hk2] using hr'
    exact_mod_cast hzero
  simp [hk1, hk2]

private theorem singleton_good (h : ℕ) : Good ({1} : Finset (Fin 3)) exampleFreq h := by
  intro k hr _
  have hk : k 1 = 0 := by
    simpa [exampleFreq] using hr
  simp [hk]

private theorem example_p_small (h : ℕ) (hh₁ : 1 ≤ h) (hh₂ : h ≤ 2) :
    omissionFraction Finset.univ exampleFreq exampleWeight h = 1 / 2 := by
  apply le_antisymm
  · have hp := p_le_of_good (w := exampleWeight) (fun j _ => (exampleWeights_pos j).le)
      (Finset.subset_univ _) (pair_good h hh₂)
    norm_num [exampleOmitted] at hp
    exact hp
  · apply le_csInf (costs_nonempty _ _ _ _)
    rintro _ ⟨u, _, hg, rfl⟩
    have h0 := zero_not_kept u h hh₁ hg
    rw [exampleOmitted, ite_eq_right h0]
    split_ifs <;> norm_num

private theorem example_p_large (h : ℕ) (hh : 3 ≤ h) :
    omissionFraction Finset.univ exampleFreq exampleWeight h = 3 / 4 := by
  apply le_antisymm
  · have hp := p_le_of_good (w := exampleWeight) (fun j _ => (exampleWeights_pos j).le)
      (Finset.subset_univ _) (singleton_good h)
    norm_num [exampleOmitted] at hp
    convert hp using 1
  · apply le_csInf (costs_nonempty _ _ _ _)
    rintro _ ⟨u, _, hg, rfl⟩
    have h0 := zero_not_kept u h (by omega) hg
    have h12 := one_two_not_kept u h hh hg
    rw [exampleOmitted, ite_eq_right h0]
    by_cases h1 : (1 : Fin 3) ∈ u
    · have h2 : (2 : Fin 3) ∉ u := fun h2 => h12 ⟨h1, h2⟩
      norm_num [h1, h2]
    · by_cases h2 : (2 : Fin 3) ∈ u <;> norm_num [h1, h2]

private theorem example_sup :
    sSup (perScale Finset.univ exampleFreq exampleWeight '' Set.Ici 1) = 1 / 2 := by
  have hsingle0 : single Finset.univ exampleFreq exampleWeight 0 = 1 / 2 := by
    norm_num [perScale, example_p_small]
  have hub (m : ℕ) : single Finset.univ exampleFreq exampleWeight m ≤ 1 / 2 := by
    cases m with
    | zero => rw [hsingle0]
    | succ n =>
      have hm : (2 : ℝ) ≤ (n.succ : ℝ) + 1 := by
        push_cast
        linarith only [Nat.cast_nonneg (α := ℝ) n]
      have hm2 : (4 : ℝ) ≤ ((n.succ : ℝ) + 1) ^ 2 := by
        convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm 2 using 1
        norm_num
      have hp := p_le_one Finset.univ exampleFreq exampleWeight (n.succ + 1)
        (fun j _ => (exampleWeights_pos j).le)
      change perScale Finset.univ exampleFreq exampleWeight (n.succ + 1) ≤ _
      rw [perScale, div_le_iff₀ (by positivity), Nat.cast_add, Nat.cast_one]
      linarith only [hm2, hp]
  have hupper : (1 / 2 : ℝ) ∈ upperBounds
      (perScale Finset.univ exampleFreq exampleWeight '' Set.Ici 1) := by
    rintro _ ⟨h, hh, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, (Nat.sub_add_cancel hh).symm⟩
    exact hub m
  apply le_antisymm (csSup_le (Set.nonempty_Ici.image _) hupper)
  exact le_csSup ⟨_, hupper⟩ ⟨1, Set.self_mem_Ici, hsingle0⟩

private theorem example_partial_two :
    (∑ n ∈ Finset.range 2, term Finset.univ exampleFreq exampleWeight n) = 4 / 9 := by
  have h1 := example_p_small 1 (by decide) (by decide)
  have h2 := example_p_small 2 (by decide) (by decide)
  norm_num [Finset.sum_range_succ, summand, scale, h1, h2]

private theorem example_term_tail (n : ℕ) :
    term Finset.univ exampleFreq exampleWeight (n + 2) = scaleDifference (n + 2) * (3 / 4) := by
  change scaleDifference (n + 2) * omissionFraction Finset.univ exampleFreq exampleWeight (n + 2 + 1) = _
  rw [example_p_large _ (by omega)]

private theorem example_partial (N : ℕ) (hN : 2 ≤ N) :
    (∑ h ∈ Finset.Ico 1 (N + 1), summand Finset.univ exampleFreq exampleWeight h) =
      19 / 36 - 3 / (4 * ((N + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = 2 + n := ⟨N - 2, by omega⟩
  rw [partial_eq, Finset.sum_range_add, example_partial_two]
  simp_rw [Nat.add_comm 2, example_term_tail, ← Finset.sum_mul, sum_c]
  norm_num [scale, div_mul_eq_div_div]
  ring

private theorem example_series :
    (∑' n, summand Finset.univ exampleFreq exampleWeight (n + 1)) = 19 / 36 := by
  have ht : HasSum (fun n => term Finset.univ exampleFreq exampleWeight (n + 2))
      (shiftedScale 2 * (3 / 4)) := by
    simpa only [example_term_tail] using (scaleDifference_hasSum 2).mul_right (3 / 4)
  rw [← series_split _ _ _ 2 ht.summable, ht.tsum_eq, partial_eq, example_partial_two]
  norm_num [scale]

/-- The three frequencies have an exact series and first improve at the fifth partial sum. -/
theorem strict_three_frequency_example :
    let g := exampleFreq
    (omissionFraction Finset.univ g exampleWeight 1 = 1 / 2 ∧
      omissionFraction Finset.univ g exampleWeight 2 = 1 / 2 ∧
      (∀ h : ℕ, 3 ≤ h →
        omissionFraction Finset.univ g exampleWeight h = 3 / 4)) ∧
    let B := sSup (perScale Finset.univ g exampleWeight '' Set.Ici 1)
    let S (N : ℕ) := ∑ h ∈ Finset.Ico 1 (N + 1), summand Finset.univ g exampleWeight h
    B = 1 / 2 ∧ S 5 = 73 / 144 ∧ B < S 5 ∧
      (∑' n, summand Finset.univ g exampleWeight (n + 1)) = 19 / 36 ∧
      (∀ N : ℕ, 2 ≤ N → S N = 19 / 36 - 3 / (4 * ((N + 1 : ℕ) : ℝ) ^ 2)) ∧
      IsLeast {N : ℕ | B < S N} 5 := by
  refine ⟨⟨example_p_small 1 (by decide) (by decide),
    example_p_small 2 (by decide) (by decide), example_p_large⟩, ?_⟩
  have hfive := example_partial 5 (by decide)
  norm_num at hfive
  have himproves : sSup (perScale Finset.univ exampleFreq exampleWeight '' Set.Ici 1) <
      ∑ h ∈ Finset.Ico 1 (5 + 1), summand Finset.univ exampleFreq exampleWeight h := by
    rw [example_sup, hfive]
    norm_num
  refine ⟨example_sup, hfive, himproves, example_series, example_partial, himproves, ?_⟩
  intro N hN
  change sSup (perScale Finset.univ exampleFreq exampleWeight '' Set.Ici 1) <
    ∑ h ∈ Finset.Ico 1 (N + 1), summand Finset.univ exampleFreq exampleWeight h at hN
  rw [example_sup, partial_eq] at hN
  by_contra! hlt
  have hle : (∑ n ∈ Finset.range N, term Finset.univ exampleFreq exampleWeight n) ≤
      ∑ n ∈ Finset.range 4, term Finset.univ exampleFreq exampleWeight n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun n _ _ =>
      term_nonneg _ _ _ (fun j _ => (exampleWeights_pos j).le) n
  have hfour := example_partial 4 (by decide)
  rw [partial_eq] at hfour
  norm_num at hfour
  linarith only [hN, hle, hfour]

end

end D5.S3.Fourier.PhaseObstructionLengths
