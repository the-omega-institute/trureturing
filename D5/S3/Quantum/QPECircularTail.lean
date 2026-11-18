/- GID: D5/S3/Quantum/QPECircularTail
   generality: G
   mirror-B: D5/B/S3/Quantum/QPECircularTail
   mirror-E: none(waiver:analytic-finite-register-proof)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.AddCircle, mathlib/module/Mathlib.Analysis.PSeries]
   utility: none
   digest: Uniform single-phase circular-window tail for the existing QPE probability. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in
Library/Fourier/qudeleap2026qpetail.md. Authors: QudeLeap Team.
Adapted source transplant from QudeLeap/Lean-QuantumAlg at
971dc8be8a153a116b6d7cd748f984d545861b00:
QuantumAlg/Util/Real/ReciprocalSquareTail.lean and
QuantumAlg/Algorithms/QPE/Analysis.lean, high-confidence cyclic phase-window tail.
Modified for the receiver's existing amplitude and probability, private helpers,
canonical imports and receiving Lean/Mathlib pins. Source hashes and correspondence
are recorded in the cited Library note. No supplier QPE framework is imported.
Retire each slice when equivalent statements are available in pinned Mathlib or
an admitted compatible dependency, preserving the full telescope and constants.
-/

import D5.S3.Quantum.ShorCountingMarginal
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.PSeries

/-! # Single-phase circular QPE tails

The two-sided finite lattice estimate bounds the circular event for the existing
phase-register amplitude, with arbitrary real phase and every positive radius.
-/

noncomputable section
open scoped BigOperators
namespace QuantumPhaseEstimationGeneral

private lemma reciprocal_square_succ_le_telescope (x : Real) (hx : 0 < x) :
    1 / (x + 1) ^ 2 <= 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have hsub : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp [ne_of_gt hx, ne_of_gt hx1]
    ring
  rw [hsub]
  apply one_div_le_one_div_of_le (mul_pos hx hx1)
  nlinarith [sq_nonneg (x + 1)]

/-- A finite reciprocal-square progression with positive real first term is at
most its first term plus the corresponding infinite telescoping envelope. -/
lemma reciprocal_square_shifted_finite_tail_le (a : Real) (n : Nat)
    (ha : 0 < a) :
    (∑ k ∈ Finset.range n, 1 / (a + (k : Real)) ^ 2) <=
      1 / a ^ 2 + 1 / a := by
  cases n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ n =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, add_zero]
      have htail :
          (∑ k ∈ Finset.range n,
              1 / (a + ((k + 1 : Nat) : Real)) ^ 2) <=
            ∑ k ∈ Finset.range n,
              (1 / (a + (k : Real)) -
                1 / (a + ((k + 1 : Nat) : Real))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hx : 0 < a + (k : Real) := by positivity
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
          reciprocal_square_succ_le_telescope (a + (k : Real)) hx
      calc
        (∑ k ∈ Finset.range n,
              1 / (a + ((k + 1 : Nat) : Real)) ^ 2) +
            1 / a ^ 2 <=
          (∑ k ∈ Finset.range n,
              (1 / (a + (k : Real)) -
                1 / (a + ((k + 1 : Nat) : Real)))) +
            1 / a ^ 2 := by
          simpa using add_le_add_right htail (1 / a ^ 2)
        _ = 1 / a ^ 2 + (1 / a - 1 / (a + (n : Real))) := by
          rw [Finset.sum_range_sub']
          simp
          ring
        _ <= 1 / a ^ 2 + 1 / a := by
          have hnonneg : 0 <= 1 / (a + (n : Real)) := by positivity
          simpa [add_comm] using add_le_add_left
            (sub_le_self (1 / a) hnonneg) (1 / a ^ 2)

private lemma reciprocal_square_shifted_subset_le
    (s : Finset Nat) (a ρ : Real) (hrho : 0 < ρ)
    (hfar : ∀ k ∈ s, ρ <= a + (k : Real)) :
    (∑ k ∈ s, 1 / (a + (k : Real)) ^ 2) <=
      1 / ρ ^ 2 + 1 / ρ := by
  classical
  by_cases hs : s = ∅
  · subst s
    simp only [Finset.sum_empty]
    positivity
  let first := s.min' (Finset.nonempty_iff_ne_empty.mpr hs)
  let last := s.max' (Finset.nonempty_iff_ne_empty.mpr hs)
  have hfirst_mem : first ∈ s := by
    exact Finset.min'_mem s (Finset.nonempty_iff_ne_empty.mpr hs)
  have hfirst : ρ <= a + (first : Real) := hfar first hfirst_mem
  have hfirst_pos : 0 < a + (first : Real) := hrho.trans_le hfirst
  have hsubset : s ⊆ Finset.Icc first last := by
    intro k hk
    exact Finset.mem_Icc.mpr
      (And.intro (Finset.min'_le s k hk) (Finset.le_max' s k hk))
  calc
    (∑ k ∈ s, 1 / (a + (k : Real)) ^ 2) <=
        ∑ k ∈ Finset.Icc first last, 1 / (a + (k : Real)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro k hkIcc hks
      positivity
    _ = ∑ offset ∈ Finset.range (last + 1 - first),
          1 / ((a + (first : Real)) + (offset : Real)) ^ 2 := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro offset hoffset
      congr 2
      push_cast
      ring
    _ <= 1 / (a + (first : Real)) ^ 2 +
          1 / (a + (first : Real)) :=
      reciprocal_square_shifted_finite_tail_le
        (a + (first : Real)) (last + 1 - first) hfirst_pos
    _ <= 1 / ρ ^ 2 + 1 / ρ := by
      apply add_le_add
      · apply one_div_le_one_div_of_le (pow_pos hrho 2)
        exact (sq_le_sq₀ hrho.le hfirst_pos.le).2 hfirst
      · exact one_div_le_one_div_of_le hrho hfirst

/-- Two-sided finite integer reciprocal-square tail.  The first point on each
side contributes the endpoint term and the remaining points are bounded by
`reciprocal_square_shifted_finite_tail_le`. -/
private lemma integer_reciprocal_square_tail_le (s : Finset Int) (x ρ : Real)
    (hrho : 0 < ρ)
    (hfar : ∀ z ∈ s, ρ <= |x - (z : Real)|) :
    (∑ z ∈ s, 1 / |x - (z : Real)| ^ 2) <=
      2 / ρ + 2 / ρ ^ 2 := by
  classical
  let base : Int := Int.floor x
  let left := s.filter (fun z => z <= base)
  let right := s.filter (fun z => base < z)
  let leftOffset : Int -> Nat := fun z => (base - z).toNat
  let rightOffset : Int -> Nat := fun z => (z - (base + 1)).toNat
  let leftOffsets := left.image leftOffset
  let rightOffsets := right.image rightOffset
  have hleftOffset_injective : Set.InjOn leftOffset left := by
    intro z hz w hw hzw
    have hzle : z <= base := (Finset.mem_filter.mp hz).2
    have hwle : w <= base := (Finset.mem_filter.mp hw).2
    have hznonneg : 0 <= base - z := sub_nonneg.mpr hzle
    have hwnonneg : 0 <= base - w := sub_nonneg.mpr hwle
    have hcast : base - z = base - w := by
      rw [← Int.toNat_of_nonneg hznonneg,
        ← Int.toNat_of_nonneg hwnonneg]
      exact_mod_cast hzw
    omega
  have hrightOffset_injective : Set.InjOn rightOffset right := by
    intro z hz w hw hzw
    have hzgt : base < z := (Finset.mem_filter.mp hz).2
    have hwgt : base < w := (Finset.mem_filter.mp hw).2
    have hznonneg : 0 <= z - (base + 1) := by omega
    have hwnonneg : 0 <= w - (base + 1) := by omega
    have hcast : z - (base + 1) = w - (base + 1) := by
      rw [← Int.toNat_of_nonneg hznonneg,
        ← Int.toNat_of_nonneg hwnonneg]
      exact_mod_cast hzw
    omega
  have hleft_sum :
      (∑ z ∈ left, 1 / |x - (z : Real)| ^ 2) =
        ∑ k ∈ leftOffsets,
          1 / ((x - (base : Real)) + (k : Real)) ^ 2 := by
    rw [Finset.sum_image hleftOffset_injective]
    apply Finset.sum_congr rfl
    intro z hz
    have hzle : z <= base := (Finset.mem_filter.mp hz).2
    have hznonneg : 0 <= base - z := sub_nonneg.mpr hzle
    rw [abs_of_nonneg]
    · congr 2
      have hoffsetCast :
          (((base - z).toNat : Nat) : Real) = ((base - z : Int) : Real) := by
        exact_mod_cast Int.toNat_of_nonneg hznonneg
      rw [hoffsetCast]
      push_cast
      ring
    · exact sub_nonneg.mpr (by
        have hzcast : (z : Real) <= (base : Real) := by
          exact_mod_cast hzle
        have hfloor : (base : Real) <= x := by
          simpa [base] using Int.floor_le x
        exact hzcast.trans hfloor)
  have hright_sum :
      (∑ z ∈ right, 1 / |x - (z : Real)| ^ 2) =
        ∑ k ∈ rightOffsets,
          1 / ((((base + 1 : Int) : Real) - x) + (k : Real)) ^ 2 := by
    rw [Finset.sum_image hrightOffset_injective]
    apply Finset.sum_congr rfl
    intro z hz
    have hzgt : base < z := (Finset.mem_filter.mp hz).2
    have hznonneg : 0 <= z - (base + 1) := by omega
    rw [abs_of_nonpos]
    · congr 2
      have hoffsetCast :
          (((z - (base + 1)).toNat : Nat) : Real) =
            ((z - (base + 1) : Int) : Real) := by
        exact_mod_cast Int.toNat_of_nonneg hznonneg
      rw [hoffsetCast]
      push_cast
      ring
    · exact sub_nonpos.mpr (by
        have hxlt : x < ((base + 1 : Int) : Real) := by
          simpa only [base, Int.cast_add, Int.cast_one] using
            Int.lt_floor_add_one x
        have hstep : ((base + 1 : Int) : Real) <= (z : Real) := by
          exact_mod_cast (Int.add_one_le_iff.mpr hzgt)
        exact hxlt.le.trans hstep)
  have hleft_far :
      ∀ k ∈ leftOffsets, ρ <= (x - (base : Real)) + (k : Real) := by
    intro k hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
    have hzmem : z ∈ s := (Finset.mem_filter.mp hz).1
    have hzle : z <= base := (Finset.mem_filter.mp hz).2
    have hznonneg : 0 <= base - z := sub_nonneg.mpr hzle
    convert hfar z hzmem using 1
    rw [abs_of_nonneg]
    · have hoffsetCast :
          (((base - z).toNat : Nat) : Real) = ((base - z : Int) : Real) := by
        exact_mod_cast Int.toNat_of_nonneg hznonneg
      rw [hoffsetCast]
      push_cast
      ring
    · exact sub_nonneg.mpr (by
        have hfloor : (base : Real) <= x := by
          simpa [base] using Int.floor_le x
        have hzcast : (z : Real) <= (base : Real) := by
          exact_mod_cast hzle
        exact hzcast.trans hfloor)
  have hright_far :
      ∀ k ∈ rightOffsets,
        ρ <= (((base + 1 : Int) : Real) - x) + (k : Real) := by
    intro k hk
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
    have hzmem : z ∈ s := (Finset.mem_filter.mp hz).1
    have hzgt : base < z := (Finset.mem_filter.mp hz).2
    have hznonneg : 0 <= z - (base + 1) := by omega
    convert hfar z hzmem using 1
    rw [abs_of_nonpos]
    · have hoffsetCast :
          (((z - (base + 1)).toNat : Nat) : Real) =
            ((z - (base + 1) : Int) : Real) := by
        exact_mod_cast Int.toNat_of_nonneg hznonneg
      rw [hoffsetCast]
      push_cast
      ring
    · have hxlt : x < ((base + 1 : Int) : Real) := by
        simpa only [base, Int.cast_add, Int.cast_one] using
          Int.lt_floor_add_one x
      have hstep : ((base + 1 : Int) : Real) <= (z : Real) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hzgt)
      exact sub_nonpos.mpr
        (hxlt.le.trans hstep)
  have hleft_bound := reciprocal_square_shifted_subset_le leftOffsets
    (x - (base : Real)) ρ hrho hleft_far
  have hright_bound := reciprocal_square_shifted_subset_le rightOffsets
    (((base + 1 : Int) : Real) - x) ρ hrho hright_far
  have hsplit :
      (∑ z ∈ s, 1 / |x - (z : Real)| ^ 2) =
        (∑ z ∈ left, 1 / |x - (z : Real)| ^ 2) +
          ∑ z ∈ right, 1 / |x - (z : Real)| ^ 2 := by
    have hright_filter :
        right = s.filter (fun z : Int => ¬ z <= base) := by
      ext z
      simp [right]
    rw [hright_filter]
    dsimp [left]
    exact (Finset.sum_filter_add_sum_filter_not s
      (fun z : Int => z <= base)
      (fun z => 1 / |x - (z : Real)| ^ 2)).symm
  rw [hsplit, hleft_sum, hright_sum]
  calc
    (∑ k ∈ leftOffsets,
          1 / ((x - (base : Real)) + (k : Real)) ^ 2) +
        ∑ k ∈ rightOffsets,
          1 / ((((base + 1 : Int) : Real) - x) + (k : Real)) ^ 2 <=
      (1 / ρ ^ 2 + 1 / ρ) + (1 / ρ ^ 2 + 1 / ρ) :=
        add_le_add hleft_bound hright_bound
    _ = 2 / ρ + 2 / ρ ^ 2 := by ring

private def principal_error (t : ℕ) (φ : ℝ) (j : Fin (2 ^ t)) : ℝ :=
  let δ := φ - (j.val : ℝ) / (2 : ℝ) ^ t
  δ - round δ

private def phase_distance (t : ℕ) (φ : ℝ) (j : Fin (2 ^ t)) : ℝ :=
  ‖((φ - (j.val : ℝ) / (2 : ℝ) ^ t : ℝ) : UnitAddCircle)‖

private lemma phase_distance_eq_abs (t : ℕ) (φ : ℝ) (j : Fin (2 ^ t)) :
    phase_distance t φ j = |principal_error t φ j| := by
  rw [phase_distance, UnitAddCircle.norm_eq]
  rfl

private lemma amplitude_norm_le (t : ℕ) (φ : ℝ) (j : Fin (2 ^ t))
    (hdistance : 0 < phase_distance t φ j) :
    ‖amplitude (2 ^ t) φ j‖ ≤
      1 / (2 * (2 : ℝ) ^ t * phase_distance t φ j) := by
  let N : ℕ := 2 ^ t
  let δ := principal_error t φ j
  let z : ℤ := round (φ - (j.val : ℝ) / (2 : ℝ) ^ t)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hdelta_abs : |δ| ≤ 1 / 2 := by
    exact abs_sub_round (φ - (j.val : ℝ) / (2 : ℝ) ^ t)
  have hdelta_pos : 0 < |δ| := by
    simpa [phase_distance_eq_abs, δ] using hdistance
  have harg : |Real.pi * δ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hsin : 2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
    have he : (2 / Real.pi) * (Real.pi * |δ|) = 2 * |δ| := by
      field_simp [Real.pi_ne_zero]
    rwa [he] at hs
  have hphase : phase δ ≠ 1 := by
    have hp : 0 < ‖phase δ - 1‖ := by
      rw [phase_sub_one_norm]
      nlinarith
    exact sub_ne_zero.mp (norm_pos_iff.mp hp)
  have hdelta : (φ - (z : ℝ)) - (j.val : ℝ) / N = δ := by
    dsimp [δ, principal_error, z, N]
    push_cast
    ring
  have hc := qpe_geometric_sum_closed_form N hNpos (φ - z) j
    (by rw [hdelta]; exact mt (phase_eq_one_iff δ).mpr hphase)
  rw [hdelta] at hc
  have heq : amplitude N (φ - z) j = amplitude N φ j := by
    have h := amplitude_periodic N (φ - z) j z
    simpa using h.symm
  rw [heq] at hc
  rw [hc]
  calc
    |Real.sin (Real.pi * N * δ)| / (N * |Real.sin (Real.pi * δ)|) ≤
        1 / ((N : ℝ) * (2 * |δ|)) := by
      exact div_le_div₀ (by norm_num) (Real.abs_sin_le_one _)
        (mul_pos hNreal (mul_pos (by norm_num) hdelta_pos))
        (mul_le_mul_of_nonneg_left hsin hNreal.le)
    _ = 1 / (2 * (2 : ℝ) ^ t * phase_distance t φ j) := by
      rw [phase_distance_eq_abs]
      simp only [N, Nat.cast_pow, Nat.cast_ofNat]
      dsimp [δ]
      ring

private def lifted_grid_index (t : Nat) (φ : Real) (j : Fin (2 ^ t)) : Int :=
  (j.val : Int) + (2 ^ t : Nat) *
    round (φ - (j.val : Real) / (2 : Real) ^ t)

private lemma lifted_grid_index_emod (t : Nat) (φ : Real)
    (j : Fin (2 ^ t)) :
    lifted_grid_index t φ j % (2 ^ t : Nat) = (j.val : Int) := by
  rw [lifted_grid_index, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg j.val)
    (Int.ofNat_lt_ofNat_of_lt j.isLt)

private lemma lifted_grid_index_injective (t : Nat) (φ : Real) :
    Function.Injective (lifted_grid_index t φ) := by
  intro left right h
  apply Fin.ext
  have hmod := congrArg (fun z : Int => z % (2 ^ t : Nat)) h
  rw [lifted_grid_index_emod, lifted_grid_index_emod] at hmod
  exact_mod_cast hmod

private lemma principal_error_scaled (t : Nat) (φ : Real)
    (j : Fin (2 ^ t)) :
    (2 : Real) ^ t * principal_error t φ j =
      (2 : Real) ^ t * φ - (lifted_grid_index t φ j : Real) := by
  rw [principal_error, lifted_grid_index]
  norm_num [Nat.cast_pow]
  field_simp [pow_ne_zero t (by norm_num : (2 : Real) ≠ 0)]
  ring

/-- The total single-phase QPE probability outside any positive circular radius.
The bad event includes equality at the radius; the complementary window is strict. -/
theorem qpe_circular_tail_le (t : ℕ) (φ ρ : ℝ) (hrho : 0 < ρ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ t) =>
        ρ ≤ ‖((φ - (j.val : ℝ) / (2 : ℝ) ^ t : ℝ) : UnitAddCircle)‖),
      probability (2 ^ t) φ j) ≤
      1 / (2 * (2 : ℝ) ^ t * ρ) + 1 / (2 * ((2 : ℝ) ^ t * ρ) ^ 2) := by
  classical
  let bad := Finset.univ.filter (fun j : Fin (2 ^ t) =>
    ρ <= phase_distance t φ j)
  let lifted := bad.image (lifted_grid_index t φ)
  let T : Real := (2 : Real) ^ t
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  have hscaledDistance (j : Fin (2 ^ t)) :
      T * phase_distance t φ j =
        |T * φ - (lifted_grid_index t φ j : Real)| := by
    rw [phase_distance_eq_abs]
    have h := congrArg abs (principal_error_scaled t φ j)
    simpa [T, abs_mul, abs_of_pos hTpos] using h
  have hpointwise :
      (∑ j ∈ bad, ‖amplitude (2 ^ t) φ j‖ ^ 2) <=
        ∑ j ∈ bad,
          (1 / (4 * |T * φ - (lifted_grid_index t φ j : Real)| ^ 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hbad : ρ <= phase_distance t φ j :=
      (Finset.mem_filter.mp hj).2
    have hdistance : 0 < phase_distance t φ j := hrho.trans_le hbad
    have hamp := amplitude_norm_le t φ j hdistance
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hamp 2
    calc
      ‖amplitude (2 ^ t) φ j‖ ^ 2 <=
          (1 / (2 * T * phase_distance t φ j)) ^ 2 := by
        simpa [T] using hsquare
      _ = 1 / (4 * |T * φ - (lifted_grid_index t φ j : Real)| ^ 2) := by
        rw [← hscaledDistance]
        field_simp [ne_of_gt hTpos, ne_of_gt hdistance]
        ring
  have hfar : ∀ z ∈ lifted,
      T * ρ <= |T * φ - (z : Real)| := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hbad : ρ <= phase_distance t φ j :=
      (Finset.mem_filter.mp hj).2
    rw [← hscaledDistance]
    exact mul_le_mul_of_nonneg_left hbad hTpos.le
  have htail := integer_reciprocal_square_tail_le lifted (T * φ) (T * ρ)
    (mul_pos hTpos hrho) hfar
  have hsum_image :
      (∑ j ∈ bad,
          1 / |T * φ - (lifted_grid_index t φ j : Real)| ^ 2) =
        ∑ z ∈ lifted, 1 / |T * φ - (z : Real)| ^ 2 := by
    rw [Finset.sum_image (lifted_grid_index_injective t φ).injOn]
  calc
    (∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ t) => ρ ≤ phase_distance t φ j),
        probability (2 ^ t) φ j) =
        ∑ j ∈ bad, ‖amplitude (2 ^ t) φ j‖ ^ 2 := rfl
    _ <= ∑ j ∈ bad,
        1 / (4 * |T * φ - (lifted_grid_index t φ j : Real)| ^ 2) :=
      hpointwise
    _ = (1 / 4) *
        ∑ z ∈ lifted, 1 / |T * φ - (z : Real)| ^ 2 := by
      rw [← hsum_image, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ <= (1 / 4) * (2 / (T * ρ) + 2 / (T * ρ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 1 / (2 * (2 : Real) ^ t * ρ) +
        1 / (2 * ((2 : Real) ^ t * ρ) ^ 2) := by
      dsimp [T]
      field_simp [ne_of_gt hrho, pow_ne_zero t (by norm_num : (2 : Real) ≠ 0)]
      ring


end QuantumPhaseEstimationGeneral
