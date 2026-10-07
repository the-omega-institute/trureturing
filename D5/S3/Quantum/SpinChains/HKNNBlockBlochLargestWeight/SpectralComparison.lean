/- GID: D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/SpectralComparison
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coefficient deficits imply strict normalized Bloch weight deficits. -/

/-
proof_shape: spectral_comparison: content
escape_witness: Form (2): spectral_comparison uses the constructed truncated state and
  its strict support estimate, and counts the distinct block translates.
admission_basis: escape-witness
Direct frozen dependencies: none on immutable baseline; foundation imports belong to this delivery.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight.ArcCoefficients
import D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight.PairingCoefficients
import D5.S1.Phase.SeatTowerCombinatorics
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open scoped BigOperators ComplexConjugate
open Fin.NatCast
open D5.S1.Phase.SeatTowerCombinatorics (Stationing)
open D5.S3.Zeros.Convolution.PerfectMatchingCount

namespace D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight

abbrev State (m : ℕ) := EuclideanSpace ℂ (Stationing (2 * m))

def psiVector (m : ℕ) : State m := WithLp.toLp 2 (fun σ => (psi m σ : ℂ))

def phase (m : ℕ) (t j : Fin (2 * m)) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t.val : ℂ) * (j.val : ℂ) /
    ((2 * m : ℕ) : ℂ))

def bloch (m : ℕ) (σ : Stationing (2 * m)) (t : Fin (2 * m)) : State m :=
  ∑ j : Fin (2 * m), phase m t j •
    EuclideanSpace.single (((shift m)^[j.val]) σ) (1 : ℂ)

def weight (m : ℕ) (σ : Stationing (2 * m)) (t : Fin (2 * m)) : ℝ :=
  ‖inner ℂ (bloch m σ t) (psiVector m)‖ ^ 2 /
    (‖bloch m σ t‖ ^ 2 * ‖psiVector m‖ ^ 2)

open Classical in
private def orbit (m : ℕ) (σ : Stationing (2 * m)) : Finset (Stationing (2 * m)) :=
  Finset.univ.image (fun j : Fin (2 * m) => ((shift m)^[j.val]) σ)

private def root (m : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 * m : ℕ) : ℂ))

theorem spectral_comparison (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) :
    (∀ t : Fin (2 * m), ‖bloch m (block m) t‖ ^ 2 = (2 * m : ℕ)) ∧
    (∀ t : Fin (2 * m), t.val = m →
      weight m (block m) t = (2 * m : ℕ) * (K m : ℝ) ^ 2 / ‖psiVector m‖ ^ 2) ∧
    (∀ (σ : Stationing (2 * m)) (t : Fin (2 * m)), bloch m σ t ≠ 0 → ¬ isArc m σ →
      weight m σ t < (2 * m : ℕ) * (K m : ℝ) ^ 2 / ‖psiVector m‖ ^ 2) ∧
    (∀ (σ : Stationing (2 * m)) (t : Fin (2 * m)), t.val ≠ m → weight m σ t = 0) := by
  classical
  have crossing_balanced (m : ℕ) := (pairing_data m).1
  have K_positive (m : ℕ) := (pairing_data m).2.1.1
  have abs_psi_block (m : ℕ) := (pairing_data m).2.1.2.1
  have psi_zero_of_unbalanced (m : ℕ) := (pairing_data m).2.1.2.2.1
  have strict_coefficient_interleaving (m : ℕ) := (pairing_data m).2.2.1
  have psi_shift (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (σ : Stationing (2 * m)) :
      psi m (shift m σ) = -psi m σ := (pairing_data m).2.2.2.1 hm σ
  have shift_iterate_apply (m : ℕ) := (pairing_data m).2.2.2.2.1
  have shift_iterate_sub (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (σ : Stationing (2 * m)) (j : ℕ) (i : Fin (2 * m)) :
      ((shift m)^[j]) σ i = σ (i - (j : Fin (2 * m))) :=
    (pairing_data m).2.2.2.2.2 hm σ j i
  have shift_periodic (m : ℕ) (σ : Stationing (2 * m)) :
      Function.IsPeriodicPt (shift m) (2 * m) σ := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_sub
    apply funext
    intro i
    rw [shift_iterate_apply]
    congr 1
    apply Fin.ext
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  have finite_support_strict_inner_bound {α : Type} [Fintype α] [DecidableEq α]
      (b p : EuclideanSpace ℂ α) (S : Finset α) (C : ℝ)
      (hb : b ≠ 0) (hbs : ∀ a, a ∉ S → b a = 0)
      (hp : ∀ a ∈ S, ‖p a‖ ^ 2 < C) :
      ‖inner ℂ b p‖ ^ 2 < ‖b‖ ^ 2 * (S.card * C) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic
    let q : EuclideanSpace ℂ α := WithLp.toLp 2 (fun a => if a ∈ S then p a else 0)
    have hi : inner ℂ b p = inner ℂ b q := by
      simp only [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hs : a ∈ S
      · simp [q, hs]
      · simp [q, hs, hbs a hs]
    have hq : ‖q‖ ^ 2 = ∑ a ∈ S, ‖p a‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc
        (∑ a, ‖q a‖ ^ 2) = ∑ a, if a ∈ S then ‖p a‖ ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hs : a ∈ S <;> simp [q, hs]
        _ = ∑ a ∈ S, ‖p a‖ ^ 2 := by rw [← Finset.sum_filter]; simp
    have hS : S.Nonempty := by
      by_contra hn
      have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      apply hb
      apply PiLp.ext
      intro a
      simpa using hbs a (by simp [he])
    have hsum : (∑ a ∈ S, ‖p a‖ ^ 2) < ∑ _a ∈ S, C :=
      Finset.sum_lt_sum_of_nonempty hS hp
    have hqc : ‖q‖ ^ 2 < S.card * C := by simpa [hq, nsmul_eq_mul] using hsum
    have hc := norm_inner_le_norm (𝕜 := ℂ) b q
    have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
    rw [hi]
    calc
      ‖inner ℂ b q‖ ^ 2 ≤ (‖b‖ * ‖q‖) ^ 2 := by
        nlinarith [norm_nonneg (inner ℂ b q), norm_nonneg b, norm_nonneg q]
      _ = ‖b‖ ^ 2 * ‖q‖ ^ 2 := by ring
      _ < ‖b‖ ^ 2 * (S.card * C) := mul_lt_mul_of_pos_left hqc (sq_pos_of_pos hbn)
  have orbit_card_le (m : ℕ) (σ : Stationing (2 * m)) : (orbit m σ).card ≤ 2 * m := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound
    exact (Finset.card_image_le).trans (by simp)
  have orbit_arc_iff (m : ℕ) (σ : Stationing (2 * m)) (j : ℕ) :
      isArc m (((shift m)^[j]) σ) ↔ isArc m σ := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      finite_support_strict_inner_bound orbit_card_le
    by_cases hm : m = 0
    · subst m
      constructor <;> intro h <;> exact ⟨0, by funext i; exact Fin.elim0 i⟩
    constructor
    · rintro ⟨k, hk⟩
      let r := j % (2 * m)
      have hmod := (shift_periodic m σ).iterate_mod_apply j
      have hr : r ≤ 2 * m := (Nat.mod_lt _ (by omega : 0 < 2 * m)).le
      have he := congrArg ((shift m)^[2 * m - r]) hk
      rw [← hmod, ← Function.iterate_add_apply, Nat.sub_add_cancel hr] at he
      rw [show ((shift m)^[2 * m]) σ = σ from shift_periodic m σ] at he
      refine ⟨2 * m - r + k, ?_⟩
      simpa only [Function.iterate_add_apply] using he
    · rintro ⟨k, rfl⟩
      exact ⟨j + k, (Function.iterate_add_apply _ _ _ _).symm⟩
  have psiVector_ne_zero (m : ℕ) : psiVector m ≠ 0 := by
    clear crossing_balanced psi_zero_of_unbalanced strict_coefficient_interleaving psi_shift
      shift_iterate_apply shift_iterate_sub shift_periodic finite_support_strict_inner_bound
      orbit_card_le orbit_arc_iff
    intro he
    have hc := congrArg (fun v : State m => v (block m)) he
    have hp : psi m (block m) = 0 := by
      have hh : (psi m (block m) : ℂ) = 0 := by simpa [psiVector] using hc
      exact_mod_cast hh
    have ha := abs_psi_block m
    rw [hp] at ha
    have hk := K_positive m
    norm_cast at ha
    omega
  have phase_as_pow (m : ℕ) (t j : Fin (2 * m)) :
      phase m t j = root m ^ (t.val * j.val) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero
    rw [root, ← Complex.exp_nat_mul]
    unfold phase
    congr 1
    push_cast
    ring
  have root_primitive (m : ℕ) (hm : 1 ≤ m) : IsPrimitiveRoot (root m) (2 * m) :=
    Complex.isPrimitiveRoot_exp _ (by omega)
  have root_middle (m : ℕ) (hm : 1 ≤ m) : root m ^ m = -1 := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero phase_as_pow root_primitive
    rw [root, ← Complex.exp_nat_mul]
    have hn : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have he : (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / ((2 * m : ℕ) : ℂ)) =
        (Real.pi : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [he, Complex.exp_pi_mul_I]
  have phase_middle (m : ℕ) (hm : 1 ≤ m) (t j : Fin (2 * m)) (ht : t.val = m) :
      phase m t j = (-1 : ℂ) ^ j.val := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero root_primitive
    rw [phase_as_pow, ht, pow_mul, root_middle m hm]
  have psi_shift_iterate (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (σ : Stationing (2 * m)) (j : ℕ) : psi m (((shift m)^[j]) σ) = (-1 : ℤ) ^ j * psi m σ := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving shift_iterate_apply shift_iterate_sub shift_periodic
      finite_support_strict_inner_bound orbit_card_le orbit_arc_iff psiVector_ne_zero phase_as_pow
      root_primitive root_middle phase_middle
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', psi_shift m hm, ih]
      rw [pow_succ]
      ring
  have bloch_inner (m : ℕ) (σ : Stationing (2 * m)) (t : Fin (2 * m)) :
      inner ℂ (bloch m σ t) (psiVector m) =
        ∑ j : Fin (2 * m), conj (phase m t j) * (psi m (((shift m)^[j.val]) σ) : ℂ) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero phase_as_pow root_primitive root_middle phase_middle psi_shift_iterate
    unfold bloch
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j hj
    rw [inner_smul_left, EuclideanSpace.inner_single_left]
    simp [psiVector]
  have bloch_inner_middle (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (σ : Stationing (2 * m)) (t : Fin (2 * m)) (ht : t.val = m) :
      inner ℂ (bloch m σ t) (psiVector m) = (2 * m : ℕ) * (psi m σ : ℂ) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero phase_as_pow root_primitive root_middle
    rw [bloch_inner]
    simp_rw [phase_middle m hm t _ ht, psi_shift_iterate m hm]
    have he (j : Fin (2 * m)) :
        conj ((-1 : ℂ) ^ j.val) * (((-1 : ℤ) ^ j.val * psi m σ : ℤ) : ℂ) = (psi m σ : ℂ) := by
      push_cast
      simp only [map_pow, map_neg, map_one]
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    simp_rw [he]
    simp [nsmul_eq_mul]
  have block_boundary (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (i : Fin (2 * m)) :
      (block m i = true ∧ block m (i - 1) = false) ↔ i = 0 := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero phase_as_pow root_primitive root_middle phase_middle psi_shift_iterate
      bloch_inner bloch_inner_middle
    by_cases hi : i = 0
    · subst i
      have hzero : 0 < m := by omega
      have hlast : ¬(2 * m - 1 < m) := by omega
      change (decide (0 < m) = true ∧ decide (((0 : Fin (2 * m)) - 1).val < m) = false) ↔ _
      rw [Fin.sub_def]
      simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * m),
        Nat.mod_eq_of_lt (by omega : 2 * m - 1 < 2 * m), hzero, hlast]
    · have hiv : i.val ≠ 0 := fun he => hi (Fin.ext he)
      simp only [block, decide_eq_true_eq, decide_eq_false_iff_not,
        Fin.val_sub_one_of_ne_zero hi, hi, iff_false]
      omega
  have shifted_block_boundary (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (j : ℕ) (i : Fin (2 * m)) :
      (((shift m)^[j]) (block m) i = true ∧
        ((shift m)^[j]) (block m) (i - 1) = false) ↔ i = (j : Fin (2 * m)) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_periodic
      finite_support_strict_inner_bound orbit_card_le orbit_arc_iff psiVector_ne_zero phase_as_pow
      root_primitive root_middle phase_middle psi_shift_iterate bloch_inner bloch_inner_middle
    rw [shift_iterate_sub m hm, shift_iterate_sub m hm]
    have he : (i - 1) - (j : Fin (2 * m)) = (i - (j : Fin (2 * m))) - 1 := by
      simp [sub_sub, add_comm]
    rw [he, block_boundary m hm, sub_eq_zero]
  have block_shifts_injective (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) :
      Function.Injective (fun j : Fin (2 * m) => ((shift m)^[j.val]) (block m)) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero phase_as_pow root_primitive root_middle phase_middle psi_shift_iterate
      bloch_inner bloch_inner_middle block_boundary
    intro a b hab
    change ((shift m)^[a.val]) (block m) = ((shift m)^[b.val]) (block m) at hab
    have ha : ((shift m)^[a.val]) (block m) a = true ∧
        ((shift m)^[a.val]) (block m) (a - 1) = false :=
      (shifted_block_boundary m hm a.val a).mpr (by simp)
    have hb : ((shift m)^[b.val]) (block m) a = true ∧
        ((shift m)^[b.val]) (block m) (a - 1) = false := by rw [← hab]; exact ha
    simpa using (shifted_block_boundary m hm b.val a).mp hb
  have phase_norm (m : ℕ) (t j : Fin (2 * m)) : ‖phase m t j‖ = 1 := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero root_primitive root_middle phase_middle psi_shift_iterate bloch_inner
      bloch_inner_middle block_boundary shifted_block_boundary block_shifts_injective
    rw [phase_as_pow, norm_pow]
    have hr : ‖root m‖ = 1 := by simp [root, Complex.norm_exp, Complex.div_re]
    rw [hr, one_pow]
  have block_bloch_norm_sq (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (t : Fin (2 * m)) : ‖bloch m (block m) t‖ ^ 2 = (2 * m : ℕ) := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero phase_as_pow root_primitive root_middle phase_middle psi_shift_iterate
      bloch_inner bloch_inner_middle block_boundary shifted_block_boundary
    classical
    have hi (j k : Fin (2 * m)) :
        inner ℂ (phase m t j • EuclideanSpace.single (((shift m)^[j.val]) (block m)) (1 : ℂ))
          (phase m t k • EuclideanSpace.single (((shift m)^[k.val]) (block m)) (1 : ℂ)) =
        if j = k then 1 else 0 := by
      by_cases he : j = k
      · subst k
        rw [inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left]
        simp [Complex.conj_mul', phase_norm]
      · have hc : ((shift m)^[j.val]) (block m) ≠ ((shift m)^[k.val]) (block m) :=
          fun h => he (block_shifts_injective m hm h)
        simp [inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left, hc, he]
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), bloch]
    simp only [sum_inner, inner_sum, hi]
    simp
  have fourier_sum_off_middle (m : ℕ) (hm : 1 ≤ m) (t : Fin (2 * m))
      (ht : t.val ≠ m) :
      (∑ j : Fin (2 * m), conj (phase m t j) * (-1 : ℂ) ^ j.val) = 0 := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero phase_middle psi_shift_iterate bloch_inner bloch_inner_middle
      block_boundary shifted_block_boundary block_shifts_injective phase_norm block_bloch_norm_sq
    let z : ℂ := conj (root m ^ t.val) * (-1)
    have hz : z ≠ 1 := by
      intro he
      have hc : conj (root m ^ t.val) = -1 := by
        simpa only [z, mul_neg_one, neg_eq_iff_eq_neg] using he
      have hr : root m ^ t.val = -1 := by
        simpa only [map_neg, map_one, starRingEnd_self_apply] using congrArg conj hc
      apply ht
      apply (root_primitive m hm).pow_inj t.isLt (by omega)
      rw [root_middle m hm]
      exact hr
    have hzp : z ^ (2 * m) = 1 := by
      dsimp [z]
      rw [mul_pow, ← map_pow, ← pow_mul, Nat.mul_comm t.val (2 * m), pow_mul,
        (root_primitive m hm).pow_eq_one]
      simp [pow_mul]
    have hf (j : Fin (2 * m)) : conj (phase m t j) * (-1 : ℂ) ^ j.val = z ^ j.val := by
      rw [phase_as_pow, pow_mul, map_pow, mul_pow]
    simp_rw [hf]
    rw [Fin.sum_univ_eq_sum_range]
    rw [geom_sum_eq hz, hzp]
    simp
  have bloch_inner_off_middle (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (σ : Stationing (2 * m)) (t : Fin (2 * m)) (ht : t.val ≠ m) :
      inner ℂ (bloch m σ t) (psiVector m) = 0 := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero phase_as_pow root_primitive root_middle phase_middle bloch_inner_middle
      block_boundary shifted_block_boundary block_shifts_injective phase_norm block_bloch_norm_sq
    rw [bloch_inner]
    simp_rw [psi_shift_iterate m hm]
    push_cast
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, fourier_sum_off_middle m hm t ht, zero_mul]
  have bloch_zero_outside_orbit (m : ℕ) (σ τ : Stationing (2 * m)) (t : Fin (2 * m))
      (hτ : τ ∉ orbit m σ) : bloch m σ t τ = 0 := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic finite_support_strict_inner_bound orbit_card_le orbit_arc_iff
      psiVector_ne_zero phase_as_pow root_primitive root_middle phase_middle psi_shift_iterate
      bloch_inner bloch_inner_middle block_boundary shifted_block_boundary block_shifts_injective
      phase_norm block_bloch_norm_sq fourier_sum_off_middle bloch_inner_off_middle
    have he (j : Fin (2 * m)) : τ ≠ ((shift m)^[j.val]) σ := by
      intro h
      apply hτ
      simp only [orbit, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, h.symm⟩
    simp [bloch, he]
  have non_arc_weight_bound (m : ℕ) (hm : 1 ≤ m) (σ : Stationing (2 * m))
      (t : Fin (2 * m)) (hb : bloch m σ t ≠ 0) (hσ : ¬ isArc m σ) :
      weight m σ t < (2 * m : ℕ) * (K m : ℝ) ^ 2 / ‖psiVector m‖ ^ 2 := by
    clear crossing_balanced K_positive abs_psi_block psi_zero_of_unbalanced
      strict_coefficient_interleaving psi_shift shift_iterate_apply shift_iterate_sub
      shift_periodic phase_as_pow root_primitive root_middle phase_middle psi_shift_iterate
      bloch_inner bloch_inner_middle block_boundary shifted_block_boundary block_shifts_injective
      phase_norm block_bloch_norm_sq fourier_sum_off_middle bloch_inner_off_middle
    classical
    have hc : ∀ τ ∈ orbit m σ, ‖psiVector m τ‖ ^ 2 < (K m : ℝ) ^ 2 := by
      intro τ hτ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hτ
      have hs : ¬ isArc m (((shift m)^[j.val]) σ) :=
        fun h => hσ ((orbit_arc_iff m σ j.val).mp h)
      have hlt := strict_coefficient_non_arc m hm (((shift m)^[j.val]) σ) hs
      have hr : ‖psiVector m (((shift m)^[j.val]) σ)‖ < (K m : ℝ) := by
        change ‖(psi m (((shift m)^[j.val]) σ) : ℂ)‖ < (K m : ℝ)
        rw [Complex.norm_intCast, ← Int.cast_abs]
        exact_mod_cast hlt
      nlinarith [norm_nonneg (psiVector m (((shift m)^[j.val]) σ))]
    have hinner := finite_support_strict_inner_bound (bloch m σ t) (psiVector m)
      (orbit m σ) ((K m : ℝ) ^ 2) hb (fun τ hτ => bloch_zero_outside_orbit m σ τ t hτ) hc
    have hcard : ((orbit m σ).card : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast orbit_card_le m σ
    have hn : 0 < ‖bloch m σ t‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
    have hp : 0 < ‖psiVector m‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (psiVector_ne_zero m))
    have hi : ‖inner ℂ (bloch m σ t) (psiVector m)‖ ^ 2 <
        ‖bloch m σ t‖ ^ 2 * ((2 * m : ℕ) * (K m : ℝ) ^ 2) := by
      apply hinner.trans_le
      gcongr
    unfold weight
    calc
      _ < (‖bloch m σ t‖ ^ 2 * ((2 * m : ℕ) * (K m : ℝ) ^ 2)) /
          (‖bloch m σ t‖ ^ 2 * ‖psiVector m‖ ^ 2) :=
        div_lt_div_of_pos_right hi (mul_pos hn hp)
      _ = _ := by field_simp
  have block_weight (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (t : Fin (2 * m)) (ht : t.val = m) :
      weight m (block m) t = (2 * m : ℕ) * (K m : ℝ) ^ 2 / ‖psiVector m‖ ^ 2 := by
    clear crossing_balanced K_positive psi_zero_of_unbalanced strict_coefficient_interleaving
      psi_shift shift_iterate_apply shift_iterate_sub shift_periodic
      finite_support_strict_inner_bound orbit_card_le orbit_arc_iff psiVector_ne_zero phase_as_pow
      root_primitive root_middle phase_middle psi_shift_iterate bloch_inner block_boundary
      shifted_block_boundary block_shifts_injective phase_norm fourier_sum_off_middle
      bloch_inner_off_middle bloch_zero_outside_orbit non_arc_weight_bound
    have hn : ((2 * m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 2 * m ≠ 0)
    have ha : ‖(psi m (block m) : ℂ)‖ = (K m : ℝ) := by
      rw [Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast abs_psi_block m
    unfold weight
    rw [bloch_inner_middle m hm _ t ht, block_bloch_norm_sq m hm, norm_mul,
      Complex.norm_natCast, ha]
    field_simp
  refine ⟨block_bloch_norm_sq m hm, fun t ht => block_weight m hm t ht,
    non_arc_weight_bound m hm, ?_⟩
  intro σ t ht
  rw [weight, bloch_inner_off_middle m hm σ t ht, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_div]

#print axioms spectral_comparison

end D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight
