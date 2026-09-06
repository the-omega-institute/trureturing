/- GID: D5/S3/Weil/GroundMode/NormalizedReadoutDisk
   generality: G
   mirror-B: D5/B/S3/Weil/GroundMode/NormalizedReadoutDisk
   mirror-E: none(waiver:symbolic-complex-ball-range-with-separate-interval-consumer)
   anchors: []
   digest: Construct the exact range of a ratio of two affine complex Hilbert readouts on an error ball, then apply it to an orthogonal projective eigenmode error. -/

import D5.S3.Weil.ZetaBridge.WeilProjectiveRayleighCapture
import Mathlib.Tactic.FieldSimp

/-!
# A joint disk for normalized readouts

Both observations depend on the same unknown error vector. The theorem
retains their complex covariance. Its converse constructs an attaining error
for every accepted ratio, including the degenerate residual-vector case.
This exactness concerns the Hilbert error ball, not the smaller set of errors
which also solve a particular eigenvalue equation.

The projective consumer removes the candidate direction from both readouts
and applies the existing Rayleigh enclosure. No concrete Fourier/domain
identification, all-scale gap, prolate identification or Xi limit is assumed
silently. Classical ingredients are Cauchy--Schwarz, a one-vector minimum-
norm solution and completing a complex square. No priority is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.GroundMode.NormalizedReadoutDisk

open Complex
open scoped InnerProductSpace ComplexConjugate
open D5.S3.Weil.ZetaBridge.WeilProjectiveRayleighCapture

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem inner_square_bound (b w : H) (e : ℝ) (hw : ‖w‖ ^ 2 ≤ e) :
    ‖⟪b, w⟫_ℂ‖ ^ 2 ≤ e * ‖b‖ ^ 2 := by
  calc
    _ ≤ (‖b‖ * ‖w‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm b w) 2
    _ = ‖b‖ ^ 2 * ‖w‖ ^ 2 := by ring
    _ ≤ ‖b‖ ^ 2 * e := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
    _ = _ := mul_comm _ _

/-- A uniform modulus floor for the same affine denominator. The square
budget comes from Cauchy--Schwarz; no denominator value is sampled. -/
theorem affine_anchor_modulus_lower (b w : H) (d : ℂ) (e : ℝ)
    (hw : ‖w‖ ^ 2 ≤ e) :
    ‖d‖ - Real.sqrt (e * ‖b‖ ^ 2) ≤ ‖d + ⟪b, w⟫_ℂ‖ := by
  have hb := inner_square_bound b w e hw
  have he : 0 ≤ e * ‖b‖ ^ 2 := (sq_nonneg _).trans hb
  have hs := Real.sq_sqrt he
  have hs0 := Real.sqrt_nonneg (e * ‖b‖ ^ 2)
  have hn : ‖⟪b, w⟫_ℂ‖ ≤ Real.sqrt (e * ‖b‖ ^ 2) := by
    nlinarith [norm_nonneg ⟪b, w⟫_ℂ]
  have ht := norm_sub_norm_le d (-⟪b, w⟫_ℂ)
  rw [norm_neg, sub_neg_eq_add] at ht
  linarith

/-- The denominator cannot vanish anywhere in the entire certified error
ball. Its strict margin is derived from the same denominator functional. -/
theorem affine_anchor_ne_zero (b w : H) (d : ℂ) (e : ℝ)
    (hw : ‖w‖ ^ 2 ≤ e) (hmargin : e * ‖b‖ ^ 2 < ‖d‖ ^ 2) :
    d + ⟪b, w⟫_ℂ ≠ 0 := by
  intro hz
  have hd : d = -⟪b, w⟫_ℂ := by
    calc
      d = (d + ⟪b, w⟫_ℂ) - ⟪b, w⟫_ℂ := by ring
      _ = -⟪b, w⟫_ℂ := by rw [hz]; simp
  have hb := inner_square_bound b w e hw
  have hn : ‖d‖ ^ 2 = ‖⟪b, w⟫_ℂ‖ ^ 2 := by rw [hd, norm_neg]
  rw [← hn] at hb
  exact (not_lt_of_ge hb) hmargin

private theorem residual_inner (b c w : H) (z : ℂ) :
    ⟪c - conj z • b, w⟫_ℂ = ⟪c, w⟫_ℂ - z * ⟪b, w⟫_ℂ := by
  rw [inner_sub_left, inner_smul_left]
  simp only [Complex.conj_conj]

/-- Exact attainability, not just a necessary norm bound. Any accepted ratio
is produced by a vector in the error ball. The construction uses the single
residual vector c-conj(z)b; it does not postulate a solver or an inverse. -/
theorem affine_ratio_range_iff (b c : H) (d a z : ℂ) (e : ℝ)
    (he : 0 ≤ e) (hmargin : e * ‖b‖ ^ 2 < ‖d‖ ^ 2) :
    (∃ w : H, ‖w‖ ^ 2 ≤ e ∧
      (a + ⟪c, w⟫_ℂ) / (d + ⟪b, w⟫_ℂ) = z) ↔
      ‖z * d - a‖ ^ 2 ≤ e * ‖c - conj z • b‖ ^ 2 := by
  constructor
  · rintro ⟨w, hw, hz⟩
    have hd := affine_anchor_ne_zero b w d e hw hmargin
    have hmul := (div_eq_iff hd).mp hz
    have hid : ⟪c - conj z • b, w⟫_ℂ = z * d - a := by
      rw [residual_inner]
      calc
        _ = (a + ⟪c, w⟫_ℂ) - z * ⟪b, w⟫_ℂ - a := by ring
        _ = z * d - a := by rw [hmul]; ring
    have hb := inner_square_bound (c - conj z • b) w e hw
    simpa only [hid] using hb
  · intro hball
    let s : H := c - conj z • b
    change ‖z * d - a‖ ^ 2 ≤ e * ‖s‖ ^ 2 at hball
    by_cases hs : s = 0
    · have hnum : z * d - a = 0 := by
        have hh : ‖z * d - a‖ ^ 2 ≤ 0 := by simpa only [hs, norm_zero,
          zero_pow (by decide : 2 ≠ 0), mul_zero] using hball
        have hn : ‖z * d - a‖ = 0 := by nlinarith [norm_nonneg (z * d - a)]
        exact norm_eq_zero.mp hn
      have hw : ‖(0 : H)‖ ^ 2 ≤ e := by simpa using he
      have hd := affine_anchor_ne_zero b (0 : H) d e hw hmargin
      refine ⟨0, hw, (div_eq_iff hd).mpr ?_⟩
      simpa using (sub_eq_zero.mp hnum).symm
    · have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs
      have hn2 : 0 < ‖s‖ ^ 2 := sq_pos_of_pos hn
      have hnc : ((‖s‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt hn2
      let w : H := ((z * d - a) / ((‖s‖ ^ 2 : ℝ) : ℂ)) • s
      have hinner : ⟪s, w⟫_ℂ = z * d - a := by
        rw [show w = ((z * d - a) / ((‖s‖ ^ 2 : ℝ) : ℂ)) • s from rfl,
          inner_smul_right, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
        exact div_mul_cancel₀ _ hnc
      have hnorm : ‖w‖ ^ 2 = ‖z * d - a‖ ^ 2 / ‖s‖ ^ 2 := by
        dsimp [w]
        rw [norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg ‖s‖)]
        field_simp [hn.ne']
        <;> ring
      have hw : ‖w‖ ^ 2 ≤ e := by
        rw [hnorm]
        apply (div_le_iff₀ hn2).mpr
        exact hball
      have hd := affine_anchor_ne_zero b w d e hw hmargin
      have hi : ⟪c, w⟫_ℂ - z * ⟪b, w⟫_ℂ = z * d - a := by
        rw [← residual_inner]
        exact hinner
      refine ⟨w, hw, (div_eq_iff hd).mpr ?_⟩
      calc
        a + ⟪c, w⟫_ℂ =
          a + (⟪c, w⟫_ℂ - z * ⟪b, w⟫_ℂ) + z * ⟪b, w⟫_ℂ := by ring
        _ = a + (z * d - a) + z * ⟪b, w⟫_ℂ := by rw [hi]
        _ = z * (d + ⟪b, w⟫_ℂ) := by ring

private theorem completed_square_identity (b c : H) (d a z : ℂ) (e : ℝ) :
    let D := ‖d‖ ^ 2 - e * ‖b‖ ^ 2
    let B := a * conj d - (e : ℂ) * ⟪c, b⟫_ℂ
    ‖(D : ℂ) * z - B‖ ^ 2 -
      (‖B‖ ^ 2 - D * (‖a‖ ^ 2 - e * ‖c‖ ^ 2)) =
      D * (‖z * d - a‖ ^ 2 - e * ‖c - conj z • b‖ ^ 2) := by
  dsimp
  rw [norm_sub_sq (𝕜 := ℂ) c (conj z • b), inner_smul_right]
  simp only [norm_smul, Complex.norm_conj, mul_pow]
  simp only [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The complete complex disk, expressed without a square root or a division
by the positive D. Its usual center is B/D and its squared radius is the
right-hand side divided by D^2. No correlation term has been discarded. -/
theorem affine_ratio_disk_iff (b c : H) (d a z : ℂ) (e : ℝ)
    (he : 0 ≤ e) (hmargin : e * ‖b‖ ^ 2 < ‖d‖ ^ 2) :
    let D := ‖d‖ ^ 2 - e * ‖b‖ ^ 2
    let B := a * conj d - (e : ℂ) * ⟪c, b⟫_ℂ
    (∃ w : H, ‖w‖ ^ 2 ≤ e ∧
      (a + ⟪c, w⟫_ℂ) / (d + ⟪b, w⟫_ℂ) = z) ↔
      ‖(D : ℂ) * z - B‖ ^ 2 ≤
        ‖B‖ ^ 2 - D * (‖a‖ ^ 2 - e * ‖c‖ ^ 2) := by
  dsimp
  rw [affine_ratio_range_iff b c d a z e he hmargin]
  have hD : 0 < ‖d‖ ^ 2 - e * ‖b‖ ^ 2 := sub_pos.mpr hmargin
  have hid := completed_square_identity b c d a z e
  dsimp at hid
  constructor
  · intro h
    have hp := mul_nonpos_of_nonneg_of_nonpos hD.le (sub_nonpos.mpr h)
    linarith
  · intro h
    have hp : (‖d‖ ^ 2 - e * ‖b‖ ^ 2) *
        (‖z * d - a‖ ^ 2 - e * ‖c - conj z • b‖ ^ 2) ≤ 0 := by linarith
    have hp' : ‖z * d - a‖ ^ 2 - e * ‖c - conj z • b‖ ^ 2 ≤ 0 := by
      apply (mul_le_mul_left hD).mp
      simpa only [mul_zero] using hp
    exact sub_nonpos.mp hp'

private theorem projected_gram_identity (k h0 h1 : H) (hk : ‖k‖ = 1) :
    ⟪h1 - ⟪k, h1⟫_ℂ • k, h0 - ⟪k, h0⟫_ℂ • k⟫_ℂ =
      ⟪h1, h0⟫_ℂ - ⟪h1, k⟫_ℂ * conj ⟪h0, k⟫_ℂ := by
  have hkself : ⟪k, k⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hk]
    norm_num
  have hc0 : ⟪k, h0⟫_ℂ = conj ⟪h0, k⟫_ℂ := (inner_conj_symm k h0).symm
  have hc1 : ⟪k, h1⟫_ℂ = conj ⟪h1, k⟫_ℂ := (inner_conj_symm k h1).symm
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hkself, hc0, hc1, Complex.conj_conj]
  ring

private theorem projected_norm_identity (k h : H) (hk : ‖k‖ = 1) :
    ‖h - ⟪k, h⟫_ℂ • k‖ ^ 2 = ‖h‖ ^ 2 - ‖⟪h, k⟫_ℂ‖ ^ 2 := by
  have hi := projected_gram_identity k h h hk
  calc
    _ = (⟪h - ⟪k, h⟫_ℂ • k, h - ⟪k, h⟫_ℂ • k⟫_ℂ).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _ = ‖h‖ ^ 2 - ‖⟪h, k⟫_ℂ‖ ^ 2 := by
      rw [hi, Complex.sub_re, inner_self_eq_norm_sq]
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring

/-- Project the two Riesz vectors, retaining their joint covariance. These
identities turn full Fourier Gram data into the error-space Gram data. -/
theorem orthogonal_readout_gram (k h0 h1 : H) (hk : ‖k‖ = 1) :
    let b := h0 - ⟪k, h0⟫_ℂ • k
    let c := h1 - ⟪k, h1⟫_ℂ • k
    ‖b‖ ^ 2 = ‖h0‖ ^ 2 - ‖⟪h0, k⟫_ℂ‖ ^ 2 ∧
      ‖c‖ ^ 2 = ‖h1‖ ^ 2 - ‖⟪h1, k⟫_ℂ‖ ^ 2 ∧
      ⟪c, b⟫_ℂ = ⟪h1, h0⟫_ℂ - ⟪h1, k⟫_ℂ * conj ⟪h0, k⟫_ℂ := by
  exact ⟨projected_norm_identity k h0 hk, projected_norm_identity k h1 hk,
    projected_gram_identity k h0 h1 hk⟩

private theorem projected_readout (k h w : H) (hw : ⟪k, w⟫_ℂ = 0) :
    ⟪h - ⟪k, h⟫_ℂ • k, w⟫_ℂ = ⟪h, w⟫_ℂ := by
  rw [inner_sub_left, inner_smul_left, hw, mul_zero, sub_zero]

/-- Apply the exact disk to a candidate-orthogonal error. The same error
controls numerator and denominator, and the denominator nonvanishing is
part of the conclusion rather than an additional input. -/
theorem orthogonal_error_readout_disk (k w h0 h1 : H) (e : ℝ)
    (he : 0 ≤ e) (hw : ‖w‖ ^ 2 ≤ e) (horth : ⟪k, w⟫_ℂ = 0)
    (hmargin : e * ‖h0 - ⟪k, h0⟫_ℂ • k‖ ^ 2 < ‖⟪h0, k⟫_ℂ‖ ^ 2) :
    let b := h0 - ⟪k, h0⟫_ℂ • k
    let c := h1 - ⟪k, h1⟫_ℂ • k
    let d := ⟪h0, k⟫_ℂ
    let a := ⟪h1, k⟫_ℂ
    let D := ‖d‖ ^ 2 - e * ‖b‖ ^ 2
    let B := a * conj d - (e : ℂ) * ⟪c, b⟫_ℂ
    ⟪h0, k + w⟫_ℂ ≠ 0 ∧
      ‖(D : ℂ) * (⟪h1, k + w⟫_ℂ / ⟪h0, k + w⟫_ℂ) - B‖ ^ 2 ≤
        ‖B‖ ^ 2 - D * (‖a‖ ^ 2 - e * ‖c‖ ^ 2) := by
  dsimp
  have hp0 := projected_readout k h0 w horth
  have hp1 := projected_readout k h1 w horth
  have hd := affine_anchor_ne_zero (h0 - ⟪k, h0⟫_ℂ • k) w
    ⟪h0, k⟫_ℂ e hw hmargin
  have hr := (affine_ratio_disk_iff (h0 - ⟪k, h0⟫_ℂ • k)
    (h1 - ⟪k, h1⟫_ℂ • k) ⟪h0, k⟫_ℂ ⟪h1, k⟫_ℂ
    (⟪h1, k + w⟫_ℂ / ⟪h0, k + w⟫_ℂ) e he hmargin).mp
      ⟨w, hw, by rw [hp0, hp1, inner_add_right, inner_add_right]⟩
  refine ⟨?_, hr⟩
  simpa only [hp0, inner_add_right] using hd

/-- The actual projectively normalized eigenvector supplies the error used
by the joint readout disk. The original variational hypotheses are consumed
by their existing owner, rather than supplied again as a norm-error oracle. -/
theorem projective_eigenmode_readout_disk
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (ι A : E →ₗ[ℂ] H) (k u : E) (lower upper threshold lam : ℝ)
    (hsymmetric : ∀ x y : E, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0)
    (heigen : A u = (lam : ℂ) • ι u)
    (hlower : lower ≤ lam) (hlam : lam < threshold)
    (hupper : (⟪ι k, A k⟫_ℂ).re ≤ upper) (hthreshold : upper < threshold)
    (hcoercive : ∀ f : E, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re)
    (h0 h1 : H)
    (hmargin : ((upper - lower) / (threshold - lower)) *
      ‖h0 - ⟪ι k, h0⟫_ℂ • ι k‖ ^ 2 < ‖⟪h0, ι k⟫_ℂ‖ ^ 2) :
    let p := ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u)
    let e := (upper - lower) / (threshold - lower)
    let b := h0 - ⟪ι k, h0⟫_ℂ • ι k
    let c := h1 - ⟪ι k, h1⟫_ℂ • ι k
    let d := ⟪h0, ι k⟫_ℂ
    let a := ⟪h1, ι k⟫_ℂ
    let D := ‖d‖ ^ 2 - e * ‖b‖ ^ 2
    let B := a * conj d - (e : ℂ) * ⟪c, b⟫_ℂ
    ⟪h0, p⟫_ℂ ≠ 0 ∧
      ‖(D : ℂ) * (⟪h1, p⟫_ℂ / ⟪h0, p⟫_ℂ) - B‖ ^ 2 ≤
        ‖B‖ ^ 2 - D * (‖a‖ ^ 2 - e * ‖c‖ ^ 2) := by
  obtain ⟨ha, _, _, _, he, he0, _⟩ :=
    projective_rayleigh_enclosure ι A k u lower upper threshold lam
      hsymmetric hk hu heigen hlower hlam hupper hthreshold hcoercive
  obtain ⟨horth, _⟩ :=
    projective_error_energy_identity ι A k u lam hsymmetric hk heigen ha
  have he' : ‖ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u) - ι k‖ ^ 2 ≤
      (upper - lower) / (threshold - lower) := by simpa only [map_sub] using he
  have horth' : ⟪ι k, ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u) - ι k⟫_ℂ = 0 := by
    simpa only [map_sub] using horth
  have hr := orthogonal_error_readout_disk (ι k)
    (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u) - ι k) h0 h1
    ((upper - lower) / (threshold - lower)) he0 he' horth' hmargin
  have hsum : ι k + (ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u) - ι k) =
      ι ((⟪ι k, ι u⟫_ℂ)⁻¹ • u) := by
    rw [sub_eq_add_neg, ← add_assoc, add_comm (ι k), add_assoc, add_neg_cancel, add_zero]
  simpa only [hsum] using hr

/-- Arithmetic transport of the newer Neumann-weighted certificate. The
spectral inequalities themselves remain owned by the independent verifier
and its separate analytic domain bridge. -/
theorem neumann_prime3_projective_ratio :
    (((560909 : ℝ) / 10000000000000 - 2252813807 / 40960000000000000) /
      (3 / 250000 - 2252813807 / 40960000000000000)) =
        44669457 / 489267186193 ∧
      (44669457 : ℝ) / 489267186193 < (1 / 100) ^ 2 := by
  constructor <;> norm_num

#print axioms affine_anchor_modulus_lower
#print axioms affine_anchor_ne_zero
#print axioms affine_ratio_range_iff
#print axioms affine_ratio_disk_iff
#print axioms orthogonal_readout_gram
#print axioms orthogonal_error_readout_disk
#print axioms projective_eigenmode_readout_disk
#print axioms neumann_prime3_projective_ratio

end D5.S3.Weil.GroundMode.NormalizedReadoutDisk
end
