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

private def mass (s : Finset J) (w : J → ℝ) : ℝ := ∑ j ∈ s, w j

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

-- Index n represents scale h = n+1.
private def scale (h : ℕ) : ℝ := 1 / (h : ℝ) ^ 2

private abbrev a (n : ℕ) : ℝ := scale (n + 1)

private def c (n : ℕ) : ℝ := a n - a (n + 1)

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

private theorem a_nonneg (n : ℕ) : 0 ≤ a n := by
  change 0 ≤ scale (n + 1)
  unfold scale
  positivity

private theorem a_antitone : Antitone a := by
  intro n m h
  simp only [scale, Nat.cast_add, Nat.cast_one]
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add_left (by exact_mod_cast h) 1

private theorem c_nonneg (n : ℕ) : 0 ≤ c n :=
  sub_nonneg.mpr (a_antitone (Nat.le_succ n))

private theorem term_nonneg (s : Finset J) (g w : J → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j)
    (n : ℕ) : 0 ≤ term s g w n := mul_nonneg (c_nonneg n) (p_nonneg s g w _ hw)

private theorem finite_layer (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (∑ n ∈ Finset.range N, if a n ≤ x then c n else 0) ≤ x := by
  have aux (N : ℕ) :
      (∑ n ∈ Finset.range N, if a n ≤ x then c n else 0) ≤
        if a N ≤ x then x - a N else 0 := by
    induction N with
    | zero =>
      rw [Finset.sum_range_zero]
      split_ifs with h
      · exact sub_nonneg.mpr h
      · exact le_rfl
    | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : a n ≤ x
      · have hnext := (a_antitone (Nat.le_succ n)).trans h
        rw [ite_eq_left h] at ih
        rw [ite_eq_left h, ite_eq_left hnext, c]
        linarith only [ih]
      · rw [ite_eq_right h] at ih
        rw [ite_eq_right h, add_zero]
        apply ih.trans
        split_ifs with hnext
        · exact sub_nonneg.mpr hnext
        · exact le_rfl
  apply (aux N).trans
  split_ifs
  · exact sub_le_self _ (a_nonneg N)
  · exact hx

private theorem partial_eq (s : Finset J) (g w : J → ℝ) (N : ℕ) :
    (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) =
      (∑ n ∈ Finset.range N, term s g w n) := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [Nat.add_comm 1]

/-- All lengths in the finite sum are controlled at the same time `t`. -/
theorem simultaneous_bound (s : Finset J) (g w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (t : ℝ) (N : ℕ) :
    let A := average s g w t
    (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) ≤ 1 - A := by
  dsimp only
  rw [partial_eq]
  by_cases hzero : mass s w = 0
  · have hP (h : ℕ) : omissionFraction s g w h = 0 := by
      refine le_antisymm ((p_le_of_good hw (Finset.empty_subset s) (empty_good g h)).trans ?_)
        (p_nonneg s g w h hw)
      simp [hzero]
    simp [summand, average, hzero, hP]
  have hW : 0 < mass s w := lt_of_le_of_ne (Finset.sum_nonneg hw) (Ne.symm hzero)
  classical
  let loss (j : J) := 1 - Real.sin (g j * t)
  let cut (n : ℕ) := s.filter fun j => loss j < a n
  have hcut (n : ℕ) : Good (cut n) g (n + 1) := by
    intro k hr hlen
    by_contra hb
    have hH : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨j, hj, _, hjloss⟩ :=
      large_loss_of_short_relation (cut n) g k
        ((n : ℝ) + 1) t hH hr hb (by simpa only [Nat.cast_add, Nat.cast_one] using hlen)
    exact (not_lt_of_ge hjloss)
      (by simpa only [scale, Nat.cast_add, Nat.cast_one] using (Finset.mem_filter.mp hj).2)
  have hmass (n : ℕ) :
      mass (s \ cut n) w = ∑ j ∈ s, if a n ≤ loss j then w j else 0 := by
    unfold mass
    rw [← Finset.sum_filter]
    congr 1
    ext j
    by_cases hj : j ∈ s <;> simp [cut, hj, not_lt]
  have hpoint (n : ℕ) : term s g w n * mass s w ≤
      ∑ j ∈ s, w j * (if a n ≤ loss j then c n else 0) := by
    have hp := p_le_of_good hw (Finset.filter_subset _ _) (hcut n)
    have hp' := (le_div_iff₀ hW).1 hp
    calc
      _ ≤ c n * mass (s \ cut n) w := by
        change c n * omissionFraction s g w (n + 1) * mass s w ≤ _
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hp' (c_nonneg n)
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
  rw [hloss, Finset.sum_mul]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ∑ j ∈ s, w j * (if a n ≤ loss j then c n else 0) :=
      Finset.sum_le_sum fun n _ => hpoint n
    _ = ∑ j ∈ s, w j * (∑ n ∈ Finset.range N, if a n ≤ loss j then c n else 0) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (finite_layer (loss j) (sub_nonneg.mpr (Real.sin_le_one _)) N)
        (hw j hj)

private theorem finite_bound (s : Finset J) (g w : J → ℝ) (T : Set ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hT : T.Nonempty) (N : ℕ) :
    (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) ≤ deficit s g w T := by
  rw [deficit, le_sub_comm]
  apply csSup_le (hT.image _)
  rintro _ ⟨t, _, rfl⟩
  exact le_sub_comm.mp (simultaneous_bound s g w hw t N)

private theorem p_attained (s : Finset J) (g w : J → ℝ) (h : ℕ)
    (hw : ∀ j ∈ s, 0 ≤ w j) : IsLeast (costs s g w h) (omissionFraction s g w h) := by
  have hfin : (costs s g w h).Finite := by
    refine ((Finset.finite_toSet s.powerset).image
      (fun u => mass (s \ u) w / mass s w)).subset ?_
    rintro _ ⟨u, hu, _, rfl⟩
    exact ⟨u, Finset.mem_powerset.mpr hu, rfl⟩
  have hn := costs_nonempty s g w h
  have hb : BddBelow (costs s g w h) := ⟨0, costs_nonneg s g w h hw⟩
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
theorem omissionFraction_isLeast (s : Finset J) (g w : J → ℝ) (h : ℕ)
    (hw : ∀ j ∈ s, 0 ≤ w j) :
    let P := omissionFraction s g w h
    IsLeast {p | ∃ u ⊆ s, (∀ k : J → ℤ, (∀ j ∉ u, k j = 0) →
      (∑ j ∈ s, (k j : ℝ) * g j) = 0 →
      (∑ j ∈ s, |k j|) ≤ (h : ℤ) → (4 : ℤ) ∣ ∑ j ∈ s, k j) ∧
      p = mass (s \ u) w / mass s w} P := by
  dsimp only
  convert p_attained s g w h hw using 1
  ext p
  constructor
  · rintro ⟨u, hu, hg, rfl⟩
    exact ⟨u, hu, (good_iff_supported hu g h).mpr hg, rfl⟩
  · rintro ⟨u, hu, hg, rfl⟩
    exact ⟨u, hu, (good_iff_supported hu g h).mp hg, rfl⟩

private theorem a_tendsto : Tendsto a atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((↑(n + 1) : ℝ) ^ 2)) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_one, div_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2

private theorem tail_c (m N : ℕ) :
    (∑ n ∈ Finset.Ico m (m + N), c n) = a m - a (m + N) := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have h := Finset.sum_range_sub (fun n => -a (m + n)) N
  simpa only [c, Nat.add_assoc, Nat.add_zero, neg_sub_neg] using h

/-- The aggregate converges, bounds every single length, and is bounded by the deficit. -/
theorem aggregate_bounds (s : Finset J) (g w : J → ℝ) (T : Set ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hT : T.Nonempty) :
    let D := deficit s g w T
    let L := ∑' n, summand s g w (n + 1)
    (∀ N : ℕ, (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) ≤ D) ∧
      HasSum (fun n => summand s g w (n + 1)) L ∧
      sSup (perScale s g w '' Set.Ici 1) ≤ L ∧ L ≤ D := by
  have hnonneg := term_nonneg s g w hw
  have hfinite := finite_bound s g w T hw hT
  have hpartial (N : ℕ) :
      (∑ n ∈ Finset.range N, term s g w n) ≤ deficit s g w T := by
    rw [← partial_eq]
    exact hfinite N
  have hsum : Summable (term s g w) := summable_of_sum_range_le hnonneg hpartial
  refine ⟨hfinite, hsum.hasSum, ?_, hsum.tsum_le_of_sum_range_le hpartial⟩
  apply csSup_le (Set.nonempty_Ici.image _)
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, (Nat.sub_add_cancel hh).symm⟩
  have hshift : Tendsto (fun n : ℕ => m + n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hlim : Tendsto (fun N => (a m - a (m + N)) * omissionFraction s g w (m + 1))
      atTop (𝓝 (single s g w m)) := by
    have hconst : Tendsto (fun _ : ℕ => a m) atTop (𝓝 (a m)) := tendsto_const_nhds
    have hl := (hconst.sub (a_tendsto.comp hshift)).mul_const (omissionFraction s g w (m + 1))
    have heq : a m * omissionFraction s g w (m + 1) = single s g w m := by
      simp only [scale, perScale, div_mul_eq_mul_div, one_mul]
    simpa only [Function.comp_apply, sub_zero, heq] using hl
  apply le_of_tendsto hlim (Eventually.of_forall ?_)
  intro N
  calc
    _ = ∑ n ∈ Finset.Ico m (m + N), c n * omissionFraction s g w (m + 1) := by
      rw [← Finset.sum_mul, tail_c]
    _ ≤ ∑ n ∈ Finset.Ico m (m + N), term s g w n := by
      refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (c_nonneg n)
      exact p_mono s g w hw (Nat.succ_le_succ (Finset.mem_Ico.mp hn).1)
    _ ≤ _ := hsum.sum_le_tsum _ fun n _ => hnonneg n

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

private theorem example_partial_five :
    (∑ n ∈ Finset.range 5, term Finset.univ exampleFreq exampleWeight n) = 73 / 144 := by
  have h1 := example_p_small 1 (by decide) (by decide)
  have h2 := example_p_small 2 (by decide) (by decide)
  have h3 := example_p_large 3 (by decide)
  have h4 := example_p_large 4 (by decide)
  have h5 := example_p_large 5 (by decide)
  norm_num [Finset.sum_range_succ, summand, scale, h1, h2, h3, h4, h5]

/-- The frequencies 0, 1 and 2 give strict improvement at the fifth partial sum. -/
theorem strict_three_frequency_example :
    let g := exampleFreq
    (omissionFraction Finset.univ g exampleWeight 1 = 1 / 2 ∧
      omissionFraction Finset.univ g exampleWeight 2 = 1 / 2 ∧
      (∀ h : ℕ, 3 ≤ h →
        omissionFraction Finset.univ g exampleWeight h = 3 / 4)) ∧
    let B := sSup (perScale Finset.univ g exampleWeight '' Set.Ici 1)
    let S := ∑ h ∈ Finset.Ico 1 (5 + 1), summand Finset.univ g exampleWeight h
    B = 1 / 2 ∧ S = 73 / 144 ∧ B < S := by
  refine ⟨⟨example_p_small 1 (by decide) (by decide),
    example_p_small 2 (by decide) (by decide), example_p_large⟩, ?_⟩
  have hpartial : (∑ h ∈ Finset.Ico 1 (5 + 1),
      summand Finset.univ exampleFreq exampleWeight h) = 73 / 144 := by
    rw [partial_eq, example_partial_five]
  exact ⟨example_sup, hpartial, by rw [example_sup, hpartial]; norm_num⟩

end

end D5.S3.Fourier.PhaseObstructionLengths
