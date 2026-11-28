/- GID: D5/S3/Weil/ZeroData/ZetaOrdinateReflectionTransfer
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/ZetaOrdinateReflectionTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-height reflected zeros cancel the linear real-part displacement term. -/

import D5.S3.Weil.ZetaSeam.StatementSeamClosed
import D5.S3.Weil.ZetaRvm.Halving
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic
import OmegaBuild.Commands

/-! A multiplicity-weighted reflection bound for the positive zeta zero cutoff. -/

compile_only_with_mathlib

namespace D5.S3.Weil.ZeroData.ZetaOrdinateReflectionTransfer

open Finset

private theorem exp_sub_linear (z : ℂ) :
    ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp z 2
  simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, div_one, zero_add] at h
  convert h using 2
  ring

private theorem pairedExp_error (z : ℂ) :
    ‖(Complex.exp z + Complex.exp (-z)) / 2 - 1‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  have hp := exp_sub_linear z
  have hn := exp_sub_linear (-z)
  rw [norm_neg] at hn
  rw [show (Complex.exp z + Complex.exp (-z)) / 2 - 1 =
    ((Complex.exp z - 1 - z) + (Complex.exp (-z) - 1 - (-z))) / 2 by ring, norm_div]
  rw [Complex.norm_ofNat]
  exact (div_le_iff₀ (by norm_num)).2 <|
    (norm_add_le _ _).trans (by linarith)

private theorem reflection_transfer {ι : Type*} (s : Finset ι) (r : ι → ι)
    (hinv : Function.Involutive r) (hs : ∀ i ∈ s, r i ∈ s)
    (a z : ι → ℂ) (ha : ∀ i ∈ s, a (r i) = a i)
    (hz : ∀ i ∈ s, z (r i) = -z i) :
    ‖(∑ i ∈ s, a i * Complex.exp (z i)) - ∑ i ∈ s, a i‖ ≤
      ∑ i ∈ s, ‖a i‖ * (‖z i‖ ^ 2 * Real.exp ‖z i‖) := by
  have hsum : (∑ i ∈ s, a i * Complex.exp (z i)) =
      ∑ i ∈ s, a i * Complex.exp (-z i) := by
    symm
    apply sum_bij (fun i _ => r i)
    · exact hs
    · intro i _ j _ hij
      exact hinv.injective hij
    · intro j hj
      exact ⟨r j, hs j hj, hinv j⟩
    · intro i hi
      rw [ha i hi, hz i hi]
  have hrewrite : (∑ i ∈ s, a i * Complex.exp (z i)) - ∑ i ∈ s, a i =
      ∑ i ∈ s, a i * ((Complex.exp (z i) + Complex.exp (-z i)) / 2 - 1) := by
    simp_rw [mul_sub, ← mul_div_assoc, mul_add, sum_sub_distrib, ← sum_div,
      sum_add_distrib, ← hsum, mul_one]
    ring
  rw [hrewrite]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (pairedExp_error (z i)) (norm_nonneg _)



open Zeta23 in
/-- Pairing zeros of the same height bounds the transfer from the complex zero sum
to the ordinate sum by a quadratic displacement weight. -/
theorem actual_reflection_bound (v T : ℝ) :
    let s := (zerosIn_finite 0 T).toFinset
    ‖(∑ ρ ∈ s, (zeroMult ρ : ℂ) * Complex.exp ((v : ℂ) * (ρ - 1 / 2))) -
      ∑ ρ ∈ s, (zeroMult ρ : ℂ) * Complex.exp (Complex.I * ((v * ρ.im : ℝ) : ℂ))‖ ≤
        ∑ ρ ∈ s, (zeroMult ρ : ℝ) * (|v * (ρ.re - 1 / 2)| ^ 2 *
          Real.exp |v * (ρ.re - 1 / 2)|) := by
  classical
  let s := (zerosIn_finite 0 T).toFinset
  let phase (ρ : ℂ) := Complex.exp (Complex.I * ((v * ρ.im : ℝ) : ℂ))
  let a (ρ : ℂ) := (zeroMult ρ : ℂ) * phase ρ
  let z (ρ : ℂ) := ((v * (ρ.re - 1 / 2) : ℝ) : ℂ)
  have hmem (ρ : ℂ) : ρ ∈ s ↔ IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
    exact Set.Finite.mem_toFinset _
  have hs (ρ : ℂ) (hρ : ρ ∈ s) : reflect ρ ∈ s := by
    obtain ⟨hz, hpos, htop⟩ := (hmem ρ).mp hρ
    exact (hmem _).mpr ⟨zeta_reflect_zero _ hz, by simpa using hpos, by simpa using htop⟩
  have ha (ρ : ℂ) (hρ : ρ ∈ s) : a (reflect ρ) = a ρ := by
    simp [a, phase, zeta_mult_reflect _ ((hmem ρ).mp hρ).1]
  have hz (ρ : ℂ) (_ : ρ ∈ s) : z (reflect ρ) = -z ρ := by
    simp only [z, reflect_re, ← Complex.ofReal_neg]
    congr 1
    ring
  have h := reflection_transfer s reflect reflect_reflect hs a z ha hz
  have hsplit (ρ : ℂ) : (v : ℂ) * (ρ - 1 / 2) =
      Complex.I * ((v * ρ.im : ℝ) : ℂ) + z ρ := by
    conv_lhs => rw [← Complex.re_add_im ρ]
    dsimp [z]
    push_cast
    ring
  have hterm (ρ : ℂ) : a ρ * Complex.exp (z ρ) =
      (zeroMult ρ : ℂ) * Complex.exp ((v : ℂ) * (ρ - 1 / 2)) := by
    rw [hsplit, Complex.exp_add]
    dsimp [a, phase]
    ring
  simp_rw [hterm] at h
  change _ ≤ _
  convert h using 2
  rename_i ρ hρ
  have hu : ‖phase ρ‖ = 1 := by
    dsimp [phase]
    rw [mul_comm, Complex.norm_exp_mul_I, Complex.ofReal_im, neg_zero, Real.exp_zero]
  have hnorm : ‖z ρ‖ = |v * (ρ.re - 1 / 2)| := by
    change ‖((v * (ρ.re - 1 / 2) : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  simp only [a, norm_mul, Complex.norm_natCast, hu, mul_one]

end D5.S3.Weil.ZeroData.ZetaOrdinateReflectionTransfer
