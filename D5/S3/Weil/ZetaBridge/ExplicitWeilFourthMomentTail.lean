/- GID: D5/S3/Weil/ZetaBridge/ExplicitWeilFourthMomentTail
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ExplicitWeilFourthMomentTail
   mirror-E: none(waiver:unconditional-rational-zero-tail)
   anchors: []
   digest: Derive summability and a fully rational fourth-moment tail for actual ZeroData from an explicit large-height count, preserving full multiplicities and cutoff endpoints. -/

import D5.S3.Weil.ZetaBridge.ExplicitLargeHeightZeroCount
import D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
import D5.S3.Weil.ZetaTail.TailCount
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Log

/-!
# Explicit scalar zero-tail budget

The analytic input is proved in ExplicitLargeHeightZeroCount, with numerical
coefficient 128. This file assumes no spectral-tail bound, summability, RH,
or externally asserted Lehman/BPT constant. It reuses the existing finite
unit-window telescoping estimate `Zeta23.Tail.one_side_sum_le`.

The positive side uses ceil(t)-1 and intervals (j,j+1]; the negative side
uses floor(-t) and intervals (-j-1,-j]. Thus endpoint zeros are counted once,
with their full analytic multiplicities, without importing a half-endpoint
convention. A complex-radius exclusion T+1 implies an ordinate exclusion T
using the actual critical-strip bound. T >= 5 avoids all small-height counts.

This is a conservative alternative to the sharper zero-sum acceleration in
Brent, Platt, Trudgian, Math. Comp. 90 (2021), 2923-2935, Theorem 1 (1)-(3).
Their numerical counting-error bounds are not asserted in this proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Weil.ZetaBridge.ExplicitWeilFourthMomentTail

/-- A natural logarithm upper enclosure computed using an integer logarithm. -/
def fourthTailLogCeiling (T : ℕ) : ℕ := Nat.log 2 (T + 4) + 1

/-- Rational arithmetic for the full two-sided tail. Soundness requires T>=5. -/
def rationalFourthMomentTail (T : ℕ) : ℚ :=
  256 * (T : ℚ)⁻¹ *
    ((2 * ((T : ℚ) ^ 3)⁻¹ + ((T : ℚ) ^ 2)⁻¹ / 2) * fourthTailLogCeiling T +
      (2 * ((T : ℚ) ^ 2)⁻¹ + (T : ℚ)⁻¹) / ((T : ℚ) + 4))

noncomputable section
open Finset Set
open D5.S3.Weil.Convention
open Zeta23
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
open D5.S3.Weil.ZetaBridge.ExplicitLargeHeightZeroCount
open Zeta23.Tail
open scoped BigOperators

/-- The real finite-window estimate before rounding its logarithm. -/
def fourthTailBudget (A T L : ℝ) : ℝ :=
  2 * A * T⁻¹ *
    ((2 * (T ^ 3)⁻¹ + (T ^ 2)⁻¹ / 2) * L + (2 * (T ^ 2)⁻¹ + T⁻¹) / (T + 4))

/-- The spectral ordinate is the imaginary part of the actual zeta zero. -/
theorem zeroData_gamma_re (Z : ZeroData) (n : ℕ) : (Z.gamma n).re = (Z.zero n).im := by
  simp [ZeroData.gamma, spectralParameter]

/-- Transport the numerical count through the faithful zero enumeration.
The finite sum contains each analytic multiplicity exactly once. -/
theorem zeroData_large_window_count (Z : ZeroData) (t : ℝ) (ht : 4 ≤ |t|)
    (s : Finset ℕ) (hs : ∀ n ∈ s, t < (Z.gamma n).re ∧ (Z.gamma n).re ≤ t + 1) :
    (∑ n ∈ s, (Z.multiplicity n : ℝ)) ≤ 128 * Real.log (|t| + 3) := by
  classical
  have hfin := Zeta23.zetaZeroConfig.finite_window t (t + 1)
  have hsub : s.image Z.zero ⊆ hfin.toFinset := by
    intro ρ hρ
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hρ
    rw [Set.Finite.mem_toFinset]
    have hz : Z.zero n ∈ Zeta23.zetaZeroConfig.carrier := (zeroEquiv Z n).property
    exact ⟨hz, by simpa only [zeroData_gamma_re] using hs n hn⟩
  have hn : (∑ n ∈ s, Z.multiplicity n) ≤ Zeta23.zetaZeroConfig.N t (t + 1) := by
    unfold Zeta23.ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have h := Finset.sum_le_sum_of_subset (f := Zeta23.zetaZeroConfig.mult) hsub
    rw [Finset.sum_image (fun a _ b _ hab => Z.zero_injective hab)] at h
    simpa only [multiplicity_eq_zeroMult] using h
  have hr : (∑ n ∈ s, (Z.multiplicity n : ℝ)) ≤
      (Zeta23.zetaZeroConfig.N t (t + 1) : ℝ) := by exact_mod_cast hn
  exact hr.trans (zetaZeroConfig_large_count_explicit t ht)

private theorem positive_cubic_tail_le {ι : Type*} (γ : ι → ℝ) (m : ι → ℕ)
    (A T : ℝ) (hA : 0 ≤ A) (hT : 5 ≤ T)
    (hc : ∀ t : ℝ, 4 ≤ |t| → ∀ s : Finset ι,
      (∀ n ∈ s, t < γ n ∧ γ n ≤ t + 1) →
      (∑ n ∈ s, (m n : ℝ)) ≤ A * Real.log (|t| + 3))
    (s : Finset ι) (hs : ∀ n ∈ s, T < γ n) :
    (∑ n ∈ s, (m n : ℝ) * ((γ n) ^ 3)⁻¹) ≤
      A * ((2 * (T ^ 3)⁻¹ + (T ^ 2)⁻¹ / 2) * Real.log (T + 4) +
        (2 * (T ^ 2)⁻¹ + T⁻¹) / (T + 4)) := by
  classical
  let key : ι → ℕ := fun n => ⌈γ n⌉₊ - 1
  have hceil (n : ι) (hn : n ∈ s) : 1 ≤ ⌈γ n⌉₊ :=
    Nat.one_le_ceil_iff.mpr (by linarith [hs n hn])
  have hcast (n : ι) (hn : n ∈ s) : (key n : ℝ) = (⌈γ n⌉₊ : ℝ) - 1 := by
    dsimp [key]
    rw [Nat.cast_sub (hceil n hn), Nat.cast_one]
  apply one_side_sum_le s γ m key (A₀ := A) (B := T + 4) (D₀ := T)
    hA (by linarith : 1 ≤ T + 4) (by linarith : 2 ≤ T)
  · intro n hn
    exact (hs n hn).le
  · intro n hn
    rw [hcast n hn]
    have h := Nat.ceil_lt_add_one (show 0 ≤ γ n by linarith [hs n hn])
    linarith
  · intro n hn
    rw [hcast n hn]
    have h := Nat.le_ceil (γ n)
    linarith
  · intro j
    have hwindow : ∀ n ∈ s.filter (fun n => key n = j), (j : ℝ) < γ n ∧ γ n ≤ j + 1 := by
      intro n hn
      obtain ⟨hns, hnj⟩ := Finset.mem_filter.mp hn
      have hceq : ⌈γ n⌉₊ = j + 1 := by
        have h := hceil n hns
        dsimp [key] at hnj
        omega
      have h := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hceq
      push_cast at h
      constructor <;> linarith [h.1, h.2]
    by_cases hex : ∃ n, n ∈ s ∧ key n = j
    · obtain ⟨n, hn, hnj⟩ := hex
      have hwin := hwindow n (Finset.mem_filter.mpr ⟨hn, hnj⟩)
      have hj : 4 ≤ |(j : ℝ)| := by
        rw [abs_of_nonneg (Nat.cast_nonneg j)]
        linarith [hs n hn]
      refine (hc j hj _ hwindow).trans ?_
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.log_le_log (by positivity)
      rw [abs_of_nonneg (Nat.cast_nonneg j)]
      linarith
    · have he : s.filter (fun n => key n = j) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        exact hex ⟨n, Finset.mem_filter.mp hn⟩
      rw [he, Finset.sum_empty]
      exact mul_nonneg hA (Real.log_nonneg (by linarith [Nat.cast_nonneg j]))

private theorem negative_cubic_tail_le {ι : Type*} (γ : ι → ℝ) (m : ι → ℕ)
    (A T : ℝ) (hA : 0 ≤ A) (hT : 5 ≤ T)
    (hc : ∀ t : ℝ, 4 ≤ |t| → ∀ s : Finset ι,
      (∀ n ∈ s, t < γ n ∧ γ n ≤ t + 1) →
      (∑ n ∈ s, (m n : ℝ)) ≤ A * Real.log (|t| + 3))
    (s : Finset ι) (hs : ∀ n ∈ s, T < -γ n) :
    (∑ n ∈ s, (m n : ℝ) * ((-γ n) ^ 3)⁻¹) ≤
      A * ((2 * (T ^ 3)⁻¹ + (T ^ 2)⁻¹ / 2) * Real.log (T + 4) +
        (2 * (T ^ 2)⁻¹ + T⁻¹) / (T + 4)) := by
  classical
  let key : ι → ℕ := fun n => ⌊-γ n⌋₊
  apply one_side_sum_le s (fun n => -γ n) m key (A₀ := A) (B := T + 4) (D₀ := T)
    hA (by linarith : 1 ≤ T + 4) (by linarith : 2 ≤ T)
  · intro n hn
    exact (hs n hn).le
  · intro n hn
    exact Nat.floor_le (by linarith [hs n hn])
  · intro n _
    exact (Nat.lt_floor_add_one (-γ n)).le
  · intro j
    have hwindow : ∀ n ∈ s.filter (fun n => key n = j),
        -(j : ℝ) - 1 < γ n ∧ γ n ≤ (-(j : ℝ) - 1) + 1 := by
      intro n hn
      obtain ⟨hns, hnj⟩ := Finset.mem_filter.mp hn
      change ⌊-γ n⌋₊ = j at hnj
      have h := (Nat.floor_eq_iff (show 0 ≤ -γ n by linarith [hs n hns])).mp hnj
      constructor <;> linarith [h.1, h.2]
    have habs : |-(j : ℝ) - 1| = (j : ℝ) + 1 := by
      rw [abs_of_neg (by linarith [Nat.cast_nonneg j])]
      ring
    by_cases hex : ∃ n, n ∈ s ∧ key n = j
    · obtain ⟨n, hn, hnj⟩ := hex
      have hwin := hwindow n (Finset.mem_filter.mpr ⟨hn, hnj⟩)
      have hj : 4 ≤ |-(j : ℝ) - 1| := by rw [habs]; linarith [hs n hn]
      refine (hc (-(j : ℝ) - 1) hj _ hwindow).trans ?_
      apply mul_le_mul_of_nonneg_left _ hA
      apply Real.log_le_log (by positivity)
      rw [habs]
      linarith
    · have he : s.filter (fun n => key n = j) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        exact hex ⟨n, Finset.mem_filter.mp hn⟩
      rw [he, Finset.sum_empty]
      exact mul_nonneg hA (Real.log_nonneg (by linarith [Nat.cast_nonneg j]))

/-- A two-sided fourth-power tail bound derived from local window counts.
The statement is finite; summability is a consequence below, never an input. -/
theorem finite_inverse_fourth_tail_le {ι : Type*} (γ : ι → ℝ) (m : ι → ℕ)
    (A T L : ℝ) (hA : 0 ≤ A) (hT : 5 ≤ T) (hL : Real.log (T + 4) ≤ L)
    (hc : ∀ t : ℝ, 4 ≤ |t| → ∀ s : Finset ι,
      (∀ n ∈ s, t < γ n ∧ γ n ≤ t + 1) →
      (∑ n ∈ s, (m n : ℝ)) ≤ A * Real.log (|t| + 3))
    (s : Finset ι) (hs : ∀ n ∈ s, T < |γ n|) :
    (∑ n ∈ s, (m n : ℝ) / (γ n) ^ 4) ≤ fourthTailBudget A T L := by
  classical
  have hT0 : 0 < T := by linarith
  let sp := s.filter (fun n => 0 < γ n)
  let sn := s.filter (fun n => ¬ 0 < γ n)
  have hp : ∀ n ∈ sp, T < γ n := by
    intro n hn
    obtain ⟨hns, hpos⟩ := Finset.mem_filter.mp hn
    simpa only [abs_of_pos hpos] using hs n hns
  have hm : ∀ n ∈ sn, T < -γ n := by
    intro n hn
    obtain ⟨hns, hneg⟩ := Finset.mem_filter.mp hn
    simpa only [abs_of_nonpos (le_of_not_gt hneg)] using hs n hns
  have hpSum := positive_cubic_tail_le γ m A T hA hT hc sp hp
  have hmSum := negative_cubic_tail_le γ m A T hA hT hc sn hm
  have hposEq : (∑ n ∈ sp, (m n : ℝ) * (|γ n| ^ 3)⁻¹) =
      ∑ n ∈ sp, (m n : ℝ) * ((γ n) ^ 3)⁻¹ := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [abs_of_pos (by linarith [hp n hn])]
  have hnegEq : (∑ n ∈ sn, (m n : ℝ) * (|γ n| ^ 3)⁻¹) =
      ∑ n ∈ sn, (m n : ℝ) * ((-γ n) ^ 3)⁻¹ := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [abs_of_neg (by linarith [hm n hn])]
  have hcubic : (∑ n ∈ s, (m n : ℝ) * (|γ n| ^ 3)⁻¹) ≤
      2 * A * ((2 * (T ^ 3)⁻¹ + (T ^ 2)⁻¹ / 2) * Real.log (T + 4) +
        (2 * (T ^ 2)⁻¹ + T⁻¹) / (T + 4)) := by
    have hsplit : (∑ n ∈ s, (m n : ℝ) * (|γ n| ^ 3)⁻¹) =
        (∑ n ∈ sp, (m n : ℝ) * (|γ n| ^ 3)⁻¹) +
        ∑ n ∈ sn, (m n : ℝ) * (|γ n| ^ 3)⁻¹ :=
      (Finset.sum_filter_add_sum_filter_not s (fun n => 0 < γ n)
        (fun n => (m n : ℝ) * (|γ n| ^ 3)⁻¹)).symm
    rw [hsplit, hposEq, hnegEq]
    linarith
  have hpoint (n : ι) (hn : n ∈ s) :
      (m n : ℝ) / (γ n) ^ 4 ≤ T⁻¹ * ((m n : ℝ) * (|γ n| ^ 3)⁻¹) := by
    have hx : 0 < |γ n| := hT0.trans (hs n hn)
    have hi : |γ n|⁻¹ ≤ T⁻¹ := inv_anti₀ hT0 (hs n hn).le
    have heq : (γ n) ^ 4 = |γ n| ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (γ n) ^ 4)]
    calc
      _ = ((m n : ℝ) * (|γ n| ^ 3)⁻¹) * |γ n|⁻¹ := by
        rw [heq]
        field_simp [ne_of_gt hx]
        <;> ring
      _ ≤ ((m n : ℝ) * (|γ n| ^ 3)⁻¹) * T⁻¹ :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by ring
  have hlogTerm :
      (2 * (T ^ 3)⁻¹ + (T ^ 2)⁻¹ / 2) * Real.log (T + 4) +
          (2 * (T ^ 2)⁻¹ + T⁻¹) / (T + 4) ≤
      (2 * (T ^ 3)⁻¹ + (T ^ 2)⁻¹ / 2) * L +
          (2 * (T ^ 2)⁻¹ + T⁻¹) / (T + 4) :=
    add_le_add_right (mul_le_mul_of_nonneg_left hL (by positivity)) _
  calc
    _ ≤ ∑ n ∈ s, T⁻¹ * ((m n : ℝ) * (|γ n| ^ 3)⁻¹) := Finset.sum_le_sum hpoint
    _ = T⁻¹ * ∑ n ∈ s, (m n : ℝ) * (|γ n| ^ 3)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ T⁻¹ * (2 * A *
        ((2 * (T ^ 3)⁻¹ + (T ^ 2)⁻¹ / 2) * Real.log (T + 4) +
          (2 * (T ^ 2)⁻¹ + T⁻¹) / (T + 4))) :=
      mul_le_mul_of_nonneg_left hcubic (inv_nonneg.mpr hT0.le)
    _ ≤ T⁻¹ * (2 * A *
        ((2 * (T ^ 3)⁻¹ + (T ^ 2)⁻¹ / 2) * L +
          (2 * (T ^ 2)⁻¹ + T⁻¹) / (T + 4))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogTerm (mul_nonneg (by norm_num) hA))
        (inv_nonneg.mpr hT0.le)
    _ = _ := by unfold fourthTailBudget; ring

/-- Convert the complex-radius cutoff into a strict actual ordinate cutoff. -/
theorem ordinate_large_outside_spectral_ball (Z : ZeroData) (T : ℝ)
    (E : Finset ℕ) (hE : Z.symmetricIndices (T + 1) ⊆ E)
    (n : ℕ) (hn : n ∉ E) : T < |(Z.gamma n).re| := by
  have him : |(Z.gamma n).im| ≤ (1 / 2 : ℝ) := by
    rw [ZeroData.gamma, ← gammaOf_eq_spectralParameter]
    exact (Zeta23.WeilEF.abs_gammaOf_im_lt (Z.zero_isNontrivial n).2).le
  have hnorm : T + 1 < ‖Z.gamma n‖ := by
    apply lt_of_not_ge
    intro h
    exact hn (hE (Z.mem_symmetricIndices.mpr h))
  have htriangle := Complex.norm_le_abs_re_add_abs_im (Z.gamma n)
  linarith

/-- Both actual summability and its numerical real bound are derived from
zeta's proved count. No infinite spectral premise is supplied. -/
theorem zeroData_fourth_moment_tail (Z : ZeroData) (T L : ℝ)
    (hT : 5 ≤ T) (hL : Real.log (T + 4) ≤ L)
    (E : Finset ℕ) (hE : Z.symmetricIndices (T + 1) ⊆ E) :
    Summable (fun n : {n : ℕ // n ∉ E} => fourthMomentSummand Z n.1) ∧
      (∑' n : {n : ℕ // n ∉ E}, fourthMomentSummand Z n.1) ≤ fourthTailBudget 128 T L := by
  classical
  have hfinite (s : Finset {n : ℕ // n ∉ E}) :
      (∑ n ∈ s, fourthMomentSummand Z n.1) ≤ fourthTailBudget 128 T L := by
    have hlarge (n : {n : ℕ // n ∉ E}) : T < |(Z.gamma n.1).re| :=
      ordinate_large_outside_spectral_ball Z T E hE n.1 n.2
    have hbound := finite_inverse_fourth_tail_le
      (fun n => (Z.gamma n).re) Z.multiplicity 128 T L (by norm_num) hT hL
      (fun t ht s hs => zeroData_large_window_count Z t ht s hs)
      (s.map (Function.Embedding.subtype (fun n => n ∉ E))) (by
        intro n hn
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
        exact hlarge a)
    rw [Finset.sum_map] at hbound
    have hpoint (n : {n : ℕ // n ∉ E}) :
        fourthMomentSummand Z n.1 ≤
          (Z.multiplicity n.1 : ℝ) / (Z.gamma n.1).re ^ 4 := by
      apply fourthMomentSummand_le_inverse_fourth
      intro hz
      have h := hlarge n
      rw [hz, abs_zero] at h
      linarith
    exact (Finset.sum_le_sum (fun n _ => hpoint n)).trans hbound
  have hs : Summable (fun n : {n : ℕ // n ∉ E} => fourthMomentSummand Z n.1) :=
    summable_of_sum_le (fun n => by
      unfold fourthMomentSummand inverseQuadraticEnvelope
      positivity) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

/-- Integer logarithms provide an exact upper enclosure for the real logarithm. -/
theorem fourthTailLogCeiling_sound (T : ℕ) :
    Real.log ((T : ℝ) + 4) ≤ (fourthTailLogCeiling T : ℝ) := by
  have hpow : T + 4 < 2 ^ fourthTailLogCeiling T :=
    Nat.lt_pow_of_log_lt (by decide : 1 < (2 : ℕ)) (Nat.lt_succ_self _)
  have hpowR : (T : ℝ) + 4 ≤ (2 : ℝ) ^ fourthTailLogCeiling T := by
    exact_mod_cast hpow.le
  have hlog := Real.log_le_log (by positivity : 0 < (T : ℝ) + 4) hpowR
  rw [Real.log_pow] at hlog
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  exact hlog.trans (by simpa using
    mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (fourthTailLogCeiling T)))

/-- Exact real semantics of the computable rational tail budget. -/
theorem rationalFourthMomentTail_cast (T : ℕ) :
    (rationalFourthMomentTail T : ℝ) = fourthTailBudget 128 T (fourthTailLogCeiling T) := by
  unfold rationalFourthMomentTail fourthTailBudget
  push_cast
  ring

/-- A numerical, rational, unconditional tail budget for the actual zero data.
The only cutoff condition is finite spectral-ball containment. -/
theorem zeroData_fourth_moment_tail_rational (Z : ZeroData) (T : ℕ) (hT : 5 ≤ T)
    (E : Finset ℕ) (hE : Z.symmetricIndices ((T : ℝ) + 1) ⊆ E) :
    Summable (fun n : {n : ℕ // n ∉ E} => fourthMomentSummand Z n.1) ∧
      (∑' n : {n : ℕ // n ∉ E}, fourthMomentSummand Z n.1) ≤ (rationalFourthMomentTail T : ℝ) := by
  rw [rationalFourthMomentTail_cast]
  exact zeroData_fourth_moment_tail Z T (fourthTailLogCeiling T)
    (by exact_mod_cast hT) (fourthTailLogCeiling_sound T) E hE

#print axioms zeroData_large_window_count
#print axioms finite_inverse_fourth_tail_le
#print axioms zeroData_fourth_moment_tail_rational
#print axioms rationalFourthMomentTail_cast

end
end D5.S3.Weil.ZetaBridge.ExplicitWeilFourthMomentTail
