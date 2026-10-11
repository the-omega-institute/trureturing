/- GID: D5/S3/Fourier/FullBispectrumStability
   generality: G
   mirror-B: D5/B/S3/Fourier/FullBispectrumStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recover a unique cyclic translation from calibrated noisy full bispectra. -/

import D5.S3.Fourier.FinitePoisson
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic

namespace D5.S3.Fourier.FullBispectrumStability

open Finset
open scoped BigOperators ComplexConjugate

noncomputable section

private lemma norm_sub_sq (z w : ℂ) :
    ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (z * conj w).re := by
  simpa only [Complex.normSq_eq_norm_sq] using Complex.normSq_sub z w

private lemma radial_identity (a b : ℝ) (z w : ℂ)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖(a : ℂ) * z - (b : ℂ) * w‖ ^ 2 =
      (a - b) ^ 2 + a * b * ‖z - w‖ ^ 2 := by
  rw [norm_sub_sq, norm_sub_sq, norm_mul, norm_mul, hz, hw]
  simp only [Complex.norm_real, Real.norm_eq_abs, mul_one, sq_abs,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

private def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

private lemma phase_norm (z : ℂ) (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp [phase, norm_ne_zero_iff.mpr hz]

private lemma phase_reconstruct (z : ℂ) (hz : z ≠ 0) :
    (‖z‖ : ℂ) * phase z = z := by
  unfold phase
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

section Characters

variable {A : Type*} [AddCommGroup A] [Fintype A]

private def coefficient (r : A → ℂ) (χ : AddChar A ℂ) : ℂ :=
  𝔼 k, conj (χ k) * r k

omit [AddCommGroup A] in
private lemma expect_re (u : A → ℂ) : (𝔼 k, u k).re = 𝔼 k, (u k).re :=
  map_expect (Complex.reLm.restrictScalars ℚ≥0) u Finset.univ

private lemma character_orthogonal (χ ψ : AddChar A ℂ) :
    (𝔼 k, conj (χ k) * ψ k) = if χ = ψ then 1 else 0 := by
  simpa only [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply'] using
    AddChar.wInner_cWeight_eq_boole χ ψ

private lemma character_expansion (r : A → ℂ) (k : A) :
    r k = ∑ χ : AddChar A ℂ, coefficient r χ * χ k := by
  classical
  let b := AddChar.complexBasis A
  have hb : r = ∑ ψ : AddChar A ℂ, (b.repr r ψ) • (ψ : A → ℂ) := by
    simpa only [b, AddChar.complexBasis_apply] using (b.sum_repr r).symm
  have hc (χ : AddChar A ℂ) : coefficient r χ = b.repr r χ := by
    unfold coefficient
    conv_lhs => arg 2; intro x; rw [congr_fun hb x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.expect_sum_comm]
    have hi (ψ : AddChar A ℂ) :
        (𝔼 x, conj (χ x) * (b.repr r ψ * ψ x)) =
          b.repr r ψ * (if χ = ψ then 1 else 0) := by
      rw [← character_orthogonal]
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    simp_rw [hi]
    simp [mul_ite]
  simp_rw [hc]
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congr_fun hb k

private lemma character_parseval (r : A → ℂ) :
    ∑ χ : AddChar A ℂ, ‖coefficient r χ‖ ^ 2 = 𝔼 k, ‖r k‖ ^ 2 := by
  classical
  have h : (𝔼 k, conj (r k) * r k) =
      ∑ χ : AddChar A ℂ, conj (coefficient r χ) * coefficient r χ := by
    conv_lhs => arg 2; intro k; arg 1; rw [character_expansion r k]
    simp only [map_sum, map_mul, Finset.sum_mul]
    rw [Finset.expect_sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    calc
      _ = conj (coefficient r χ) * (𝔼 k, conj (χ k) * r k) := by
        rw [Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro k _
        ring
      _ = _ := rfl
  have hreal := congrArg Complex.re h
  simpa only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.re_sum, expect_re, Complex.normSq_eq_norm_sq] using hreal.symm

private lemma shifted_coefficient (r : A → ℂ) (χ : AddChar A ℂ) (k : A) :
    (𝔼 l, conj (χ l) * r (k + l)) = χ k * coefficient r χ := by
  classical
  have hunit : conj (χ k) * χ k = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, χ.norm_apply]
    norm_num
  have hs : (𝔼 l, conj (χ (k + l)) * r (k + l)) = coefficient r χ := by
    exact Fintype.expect_equiv (Equiv.addLeft k) _ _ (fun _ => rfl)
  calc
    _ = χ k * (𝔼 l, conj (χ (k + l)) * r (k + l)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro l _
      rw [χ.map_add_eq_mul, map_mul]
      calc
        _ = (conj (χ k) * χ k) * (conj (χ l) * r (k + l)) := by rw [hunit, one_mul]
        _ = _ := by ring
    _ = _ := by rw [hs]

private lemma cubic_correlation (r : A → ℂ) :
    (𝔼 k, 𝔼 l, r k * r l * conj (r (k + l))) =
      ∑ χ : AddChar A ℂ, ((‖coefficient r χ‖ ^ 2 : ℝ) : ℂ) * coefficient r χ := by
  classical
  have hl (k : A) : (𝔼 l, r k * r l * conj (r (k + l))) =
      ∑ χ : AddChar A ℂ,
        ((‖coefficient r χ‖ ^ 2 : ℝ) : ℂ) * (conj (χ k) * r k) := by
    conv_lhs => arg 2; intro l; rw [character_expansion r (k + l)]
    simp only [map_sum, map_mul, Finset.mul_sum, AddChar.map_add_eq_mul]
    rw [Finset.expect_sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    calc
      _ = (conj (coefficient r χ) * conj (χ k) * r k) *
          (𝔼 l, conj (χ l) * r l) := by
        rw [Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro l _
        ring
      _ = _ := by
        change (conj (coefficient r χ) * conj (χ k) * r k) * coefficient r χ =
          conj (coefficient r χ) * coefficient r χ * (conj (χ k) * r k)
        ring
  simp_rw [hl]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [← Finset.mul_expect]
  rfl

private lemma select_character (r : A → ℂ) (hr : ∀ k, ‖r k‖ = 1)
    (hd : ∀ k l, ‖r k * r l - r (k + l)‖ ^ 2 ≤ 4 / 27) :
    ∃ χ : AddChar A ℂ, 8 / 9 ≤ ‖coefficient r χ‖ := by
  classical
  have hp : ∑ χ : AddChar A ℂ, ‖coefficient r χ‖ ^ 2 = 1 := by
    rw [character_parseval]
    simp_rw [hr, one_pow]
    exact Fintype.expect_const _
  have hd' : (𝔼 k, 𝔼 l, ‖r k * r l - r (k + l)‖ ^ 2) ≤ (4 : ℝ) / 27 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro k _
    exact Finset.expect_le Finset.univ_nonempty (fun l _ => hd k l)
  have he : (𝔼 k, 𝔼 l, ‖r k * r l - r (k + l)‖ ^ 2) =
      2 - 2 * (∑ χ : AddChar A ℂ,
        ‖coefficient r χ‖ ^ 2 * (coefficient r χ).re) := by
    simp_rw [norm_sub_sq, norm_mul, hr]
    simp only [one_mul, one_pow]
    simp_rw [Finset.expect_sub_distrib, Fintype.expect_const,
      ← Finset.mul_expect, ← expect_re]
    rw [cubic_correlation]
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    norm_num
  have hlow : 25 / 27 ≤ ∑ χ : AddChar A ℂ,
      ‖coefficient r χ‖ ^ 2 * (coefficient r χ).re := by
    rw [he] at hd'
    linarith
  obtain ⟨χ, _, hχ⟩ := Finset.exists_max_image Finset.univ
    (fun ψ : AddChar A ℂ => (coefficient r ψ).re) Finset.univ_nonempty
  have hmax : (∑ ψ : AddChar A ℂ,
      ‖coefficient r ψ‖ ^ 2 * (coefficient r ψ).re) ≤ (coefficient r χ).re := by
    calc
      _ ≤ ∑ ψ : AddChar A ℂ, ‖coefficient r ψ‖ ^ 2 * (coefficient r χ).re := by
        apply Finset.sum_le_sum
        intro ψ hψ
        exact mul_le_mul_of_nonneg_left (hχ ψ hψ) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, hp, one_mul]
  refine ⟨χ, ?_⟩
  have hre := Complex.re_le_norm (coefficient r χ)
  linarith

private lemma averaged_defect (r : A → ℂ) (χ : AddChar A ℂ) (k : A) :
    (𝔼 l, conj (χ l) * (r k * r l - r (k + l))) =
      coefficient r χ * (r k - χ k) := by
  simp_rw [mul_sub, Finset.expect_sub_distrib]
  rw [shifted_coefficient]
  have h : (𝔼 l, conj (χ l) * (r k * r l)) =
      r k * coefficient r χ := by
    change _ = r k * (𝔼 l, conj (χ l) * r l)
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro l _
    ring
  rw [h]
  ring

private lemma norm_expect_sq_le (u : A → ℂ) :
    ‖𝔼 k, u k‖ ^ 2 ≤ 𝔼 k, ‖u k‖ ^ 2 := by
  have h₁ := RCLike.norm_expect_le (K := ℂ) (s := Finset.univ) (f := u)
  have h₂ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => ‖u k‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const] at h₂
  exact (pow_le_pow_left₀ (norm_nonneg _) h₁ 2).trans (by simpa using h₂)

private lemma weighted_correction (r : A → ℂ) (p : A → ℝ) (q e : ℝ)
    (hq : 0 < q) (hp : ∀ k, q ≤ p k) (hr : ∀ k, ‖r k‖ = 1)
    (hd : ∀ k l, ‖r k * r l - r (k + l)‖ ^ 2 ≤ 4 / 27)
    (hw : ∀ k l, p k * p l * p (k + l) *
      ‖r k * r l - r (k + l)‖ ^ 2 ≤ e ^ 2) :
    ∃ χ : AddChar A ℂ, ∀ k,
      p k * ‖r k - χ k‖ ^ 2 ≤ (81 / 64) * e ^ 2 / q ^ 2 := by
  obtain ⟨χ, hχ⟩ := select_character r hr hd
  refine ⟨χ, fun k => ?_⟩
  have hp₀ : 0 ≤ p k := hq.le.trans (hp k)
  have hpoint (l : A) : p k * ‖r k * r l - r (k + l)‖ ^ 2 ≤ e ^ 2 / q ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hq)).mpr
    have hprod : q ^ 2 ≤ p l * p (k + l) := by
      simpa only [pow_two] using mul_le_mul (hp l) (hp (k + l)) hq.le
        (hq.le.trans (hp l))
    calc
      _ ≤ (p k * ‖r k * r l - r (k + l)‖ ^ 2) *
          (p l * p (k + l)) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg hp₀ (sq_nonneg _))
      _ = p k * p l * p (k + l) * ‖r k * r l - r (k + l)‖ ^ 2 := by ring
      _ ≤ _ := hw k l
  have hav := norm_expect_sq_le (fun l => conj (χ l) * (r k * r l - r (k + l)))
  rw [averaged_defect, norm_mul, mul_pow] at hav
  simp only [norm_mul, Complex.norm_conj, χ.norm_apply, one_mul] at hav
  have hbound : p k * (‖coefficient r χ‖ ^ 2 * ‖r k - χ k‖ ^ 2) ≤ e ^ 2 / q ^ 2 := by
    calc
      _ ≤ p k * (𝔼 l, ‖r k * r l - r (k + l)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hav hp₀
      _ = (𝔼 l, p k * ‖r k * r l - r (k + l)‖ ^ 2) := Finset.mul_expect _ _ _
      _ ≤ _ := Finset.expect_le Finset.univ_nonempty (fun l _ => hpoint l)
  have hχsq : (64 : ℝ) / 81 ≤ ‖coefficient r χ‖ ^ 2 := by nlinarith
  have hnonneg : 0 ≤ p k * ‖r k - χ k‖ ^ 2 := mul_nonneg hp₀ (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right hχsq hnonneg
  rw [mul_div_assoc]
  nlinarith

end Characters

private lemma unit_mul_conj (z : ℂ) (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
  norm_num

private lemma relative_phase_defect (u v : ℂ) (u' v' u'' v'' : ℂ)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hv'' : ‖v''‖ = 1) :
    ‖v * v' * conj v'' - u * u' * conj u''‖ =
      ‖(v * conj u) * (v' * conj u') - v'' * conj u''‖ := by
  have he : v * v' * conj v'' - u * u' * conj u'' =
      ((v * conj u) * (v' * conj u') - v'' * conj u'') *
        (u * u' * conj v'') := by
    have h₁ := unit_mul_conj u hu
    have h₂ := unit_mul_conj u' hu'
    have h₃ := unit_mul_conj v'' hv''
    linear_combination -(v * v' * conj u' * u' * conj v'') * h₁ -
      (v * v' * conj v'') * h₂ + (u * u' * conj u'') * h₃
  rw [he, norm_mul]
  simp only [norm_mul, Complex.norm_conj, hu, hu', hv'', mul_one]

private lemma raw_weighted_defect {A : Type*} [AddCommGroup A]
    (F J : A → ℂ) (hF : ∀ k, F k ≠ 0) (hJ : ∀ k, J k ≠ 0)
    (e : ℝ)
    (hb : ∀ k l, ‖J k * J l * conj (J (k + l)) -
      F k * F l * conj (F (k + l))‖ ≤ e) (k l : A) :
    (‖F k‖ * ‖J k‖) * (‖F l‖ * ‖J l‖) *
      (‖F (k + l)‖ * ‖J (k + l)‖) *
        ‖(phase (J k) * conj (phase (F k))) *
          (phase (J l) * conj (phase (F l))) -
          phase (J (k + l)) * conj (phase (F (k + l)))‖ ^ 2 ≤ e ^ 2 := by
  let U := phase (F k) * phase (F l) * conj (phase (F (k + l)))
  let V := phase (J k) * phase (J l) * conj (phase (J (k + l)))
  have hU : ‖U‖ = 1 := by
    simp only [U, norm_mul, Complex.norm_conj, phase_norm _ (hF k),
      phase_norm _ (hF l), phase_norm _ (hF (k + l)), mul_one]
  have hV : ‖V‖ = 1 := by
    simp only [V, norm_mul, Complex.norm_conj, phase_norm _ (hJ k),
      phase_norm _ (hJ l), phase_norm _ (hJ (k + l)), mul_one]
  have hrec (z : A → ℂ) (hz : ∀ x, z x ≠ 0) :
      ((‖z k‖ * ‖z l‖ * ‖z (k + l)‖ : ℝ) : ℂ) *
        (phase (z k) * phase (z l) * conj (phase (z (k + l)))) =
          z k * z l * conj (z (k + l)) := by
    push_cast
    have h₁ := phase_reconstruct (z k) (hz k)
    have h₂ := phase_reconstruct (z l) (hz l)
    have h₃ := congrArg conj (phase_reconstruct (z (k + l)) (hz (k + l)))
    simp only [map_mul, Complex.conj_ofReal] at h₃
    rw [show (‖z k‖ : ℂ) * ‖z l‖ * ‖z (k + l)‖ *
        (phase (z k) * phase (z l) * conj (phase (z (k + l)))) =
        ((‖z k‖ : ℂ) * phase (z k)) * ((‖z l‖ : ℂ) * phase (z l)) *
          ((‖z (k + l)‖ : ℂ) * conj (phase (z (k + l)))) by ring,
      h₁, h₂, h₃]
  have hid := radial_identity (‖J k‖ * ‖J l‖ * ‖J (k + l)‖)
    (‖F k‖ * ‖F l‖ * ‖F (k + l)‖) V U hV hU
  rw [show ((‖J k‖ * ‖J l‖ * ‖J (k + l)‖ : ℝ) : ℂ) * V =
      J k * J l * conj (J (k + l)) from hrec J hJ,
    show ((‖F k‖ * ‖F l‖ * ‖F (k + l)‖ : ℝ) : ℂ) * U =
      F k * F l * conj (F (k + l)) from hrec F hF] at hid
  have hphase : ‖V - U‖ =
      ‖(phase (J k) * conj (phase (F k))) *
        (phase (J l) * conj (phase (F l))) -
        phase (J (k + l)) * conj (phase (F (k + l)))‖ :=
    relative_phase_defect _ _ _ _ _ _ (phase_norm _ (hF _))
      (phase_norm _ (hF _)) (phase_norm _ (hJ _))
  rw [hphase] at hid
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hb k l) 2
  nlinarith [sq_nonneg (‖J k‖ * ‖J l‖ * ‖J (k + l)‖ -
    ‖F k‖ * ‖F l‖ * ‖F (k + l)‖)]

private lemma calibrated_amplitudes {A : Type*} [AddCommGroup A]
    (F J : A → ℂ) (m e : ℝ) (hm : 0 < m) (he : 0 ≤ e)
    (hsmall : e ≤ m ^ 3 / 4) (hdc : F 0 = J 0)
    (hF : ∀ k, m ≤ ‖F k‖)
    (hb : ∀ k l, ‖J k * J l * conj (J (k + l)) -
      F k * F l * conj (F (k + l))‖ ≤ e) :
    ∀ k, J k ≠ 0 ∧ 3 * m ^ 2 / 4 ≤ ‖F k‖ * ‖J k‖ ∧
      (‖J k‖ - ‖F k‖) ^ 2 ≤ e ^ 2 / m ^ 4 := by
  intro k
  have hdc0 := hF 0
  have hk := hF k
  have ha : 0 ≤ ‖F k‖ := norm_nonneg _
  have hb₀ : 0 ≤ ‖J k‖ := norm_nonneg _
  have hs : ‖F 0‖ * |‖J k‖ ^ 2 - ‖F k‖ ^ 2| ≤ e := by
    have hh := hb k 0
    rw [add_zero, ← hdc] at hh
    have hrew : J k * F 0 * conj (J k) - F k * F 0 * conj (F k) =
        F 0 * ((‖J k‖ ^ 2 - ‖F k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, ← Complex.normSq_eq_norm_sq,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_conj_mul_self]
      ring
    rw [hrew, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hh
    exact hh
  have hs' : m * |‖J k‖ ^ 2 - ‖F k‖ ^ 2| ≤ e :=
    (mul_le_mul_of_nonneg_right hdc0 (abs_nonneg _)).trans hs
  have hsq : 3 * m ^ 2 / 4 ≤ ‖J k‖ ^ 2 := by
    have h := le_abs_self (‖F k‖ ^ 2 - ‖J k‖ ^ 2)
    rw [abs_sub_comm] at h
    have ht := mul_le_mul_of_nonneg_left h hm.le
    have hmF : m ^ 2 ≤ ‖F k‖ ^ 2 := pow_le_pow_left₀ hm.le hk 2
    have hmF' := mul_le_mul_of_nonneg_left hmF hm.le
    apply (mul_le_mul_iff_right₀ hm).mp
    nlinarith
  have hJlower : 3 * m / 4 ≤ ‖J k‖ := by nlinarith
  have hJpos : 0 < ‖J k‖ := by linarith
  have hp : 3 * m ^ 2 / 4 ≤ ‖F k‖ * ‖J k‖ := by
    have hprod := mul_le_mul hk hJlower (by positivity : 0 ≤ 3 * m / 4) ha
    nlinarith
  have hdiff : m ^ 2 * |‖J k‖ - ‖F k‖| ≤ e := by
    have hid : |‖J k‖ ^ 2 - ‖F k‖ ^ 2| =
        |‖J k‖ - ‖F k‖| * (‖J k‖ + ‖F k‖) := by
      rw [show ‖J k‖ ^ 2 - ‖F k‖ ^ 2 =
        (‖J k‖ - ‖F k‖) * (‖J k‖ + ‖F k‖) by ring, abs_mul,
        abs_of_nonneg (add_nonneg hb₀ ha)]
    rw [hid] at hs'
    have hsum : m ≤ ‖J k‖ + ‖F k‖ := by linarith
    have hprod := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg hm.le (abs_nonneg (‖J k‖ - ‖F k‖)))
    nlinarith
  refine ⟨norm_ne_zero_iff.mp hJpos.ne', hp, ?_⟩
  apply (le_div_iff₀ (pow_pos hm 4)).mpr
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ m ^ 2 * |‖J k‖ - ‖F k‖|) hdiff 2
  have hp4 : (m ^ 2) ^ 2 = m ^ 4 := by ring
  rw [mul_pow, hp4, sq_abs] at hh
  nlinarith

private lemma coefficient_recovery {A : Type*} [AddCommGroup A] [Fintype A]
    (F J : A → ℂ) (m e : ℝ) (hm : 0 < m) (he : 0 ≤ e)
    (hsmall : e ≤ m ^ 3 / 4) (hdc : F 0 = J 0)
    (hF : ∀ k, m ≤ ‖F k‖)
    (hb : ∀ k l, ‖J k * J l * conj (J (k + l)) -
      F k * F l * conj (F (k + l))‖ ≤ e) :
    ∃ χ : AddChar A ℂ, ∀ k, ‖J k - χ k * F k‖ ≤ 2 * e / m ^ 2 := by
  have ha := calibrated_amplitudes F J m e hm he hsmall hdc hF hb
  have hFn (k : A) : F k ≠ 0 := norm_ne_zero_iff.mp (hm.trans_le (hF k)).ne'
  have hJn (k : A) : J k ≠ 0 := (ha k).1
  let p : A → ℝ := fun k => ‖F k‖ * ‖J k‖
  let r : A → ℂ := fun k => phase (J k) * conj (phase (F k))
  let q : ℝ := 3 * m ^ 2 / 4
  have hq : 0 < q := by dsimp [q]; positivity
  have hp (k : A) : q ≤ p k := (ha k).2.1
  have hr (k : A) : ‖r k‖ = 1 := by
    simp only [r, norm_mul, Complex.norm_conj,
      phase_norm _ (hFn k), phase_norm _ (hJn k), mul_one]
  have hw (k l : A) : p k * p l * p (k + l) * ‖r k * r l - r (k + l)‖ ^ 2 ≤ e ^ 2 :=
    raw_weighted_defect F J hFn hJn e hb k l
  have he2 : e ^ 2 ≤ m ^ 6 / 16 := by
    have h := pow_le_pow_left₀ he hsmall 2
    nlinarith
  have hd (k l : A) : ‖r k * r l - r (k + l)‖ ^ 2 ≤ 4 / 27 := by
    have hprod : q ^ 3 ≤ p k * p l * p (k + l) := by
      have h₂ := mul_le_mul (hp k) (hp l) hq.le (hq.le.trans (hp k))
      have h₃ := mul_le_mul h₂ (hp (k + l)) hq.le
        (mul_nonneg (hq.le.trans (hp k)) (hq.le.trans (hp l)))
      simpa only [pow_succ, pow_two, pow_zero, one_mul] using h₃
    have h := (mul_le_mul_of_nonneg_right hprod (sq_nonneg _)).trans (hw k l)
    have hq3 : q ^ 3 = 27 * m ^ 6 / 64 := by dsimp [q]; ring
    have hh : q ^ 3 * (4 / 27) ≥ e ^ 2 := by rw [hq3]; nlinarith
    exact (mul_le_mul_iff_right₀ (pow_pos hq 3)).mp (h.trans hh)
  obtain ⟨χ, hχ⟩ := weighted_correction r p q e hq hp hr hd hw
  refine ⟨χ, fun k => ?_⟩
  have hphase : ‖phase (J k) - χ k * phase (F k)‖ = ‖r k - χ k‖ := by
    have hid : phase (J k) - χ k * phase (F k) =
        (r k - χ k) * phase (F k) := by
      dsimp [r]
      have hu := unit_mul_conj (phase (F k)) (phase_norm _ (hFn k))
      linear_combination -(phase (J k)) * hu
    rw [hid, norm_mul, phase_norm _ (hFn k), mul_one]
  have hi := radial_identity ‖J k‖ ‖F k‖ (phase (J k)) (χ k * phase (F k))
    (phase_norm _ (hJn k)) (by rw [norm_mul, χ.norm_apply, phase_norm _ (hFn k), mul_one])
  have hrec : (‖F k‖ : ℂ) * (χ k * phase (F k)) = χ k * F k := by
    rw [mul_left_comm, phase_reconstruct _ (hFn k)]
  rw [phase_reconstruct _ (hJn k), hrec, hphase] at hi
  have hχ' : p k * ‖r k - χ k‖ ^ 2 ≤ 9 * e ^ 2 / (4 * m ^ 4) := by
    have hid : (81 / 64 : ℝ) * e ^ 2 / q ^ 2 = 9 * e ^ 2 / (4 * m ^ 4) := by
      dsimp [q]
      field_simp [hm.ne']
      <;> ring
    simpa only [hid] using hχ k
  have hbnd : ‖J k - χ k * F k‖ ^ 2 ≤ (2 * e / m ^ 2) ^ 2 := by
    have ha' := (ha k).2.2
    dsimp [p] at hχ'
    rw [hi]
    have hid : (2 * e / m ^ 2) ^ 2 = 4 * e ^ 2 / m ^ 4 := by ring
    rw [hid]
    have hden : 9 * e ^ 2 / (4 * m ^ 4) = (9 / 4 : ℝ) * (e ^ 2 / m ^ 4) := by ring
    rw [hden] at hχ'
    rw [mul_div_assoc]
    nlinarith [div_nonneg (sq_nonneg e) (pow_nonneg hm.le 4)]
  have hR : 0 ≤ 2 * e / m ^ 2 := by positivity
  nlinarith [norm_nonneg (J k - χ k * F k)]

section Cyclic

variable {N : ℕ} [NeZero N]

private lemma cyclic_parseval (f : ZMod N → ℂ) :
    ∑ x, ‖f x‖ ^ 2 = 𝔼 k, ‖ZMod.dft f k‖ ^ 2 := by
  classical
  let E := FinitePoisson.characterEquiv (m := N)
  have hc (t : ZMod N) : coefficient f (E t) = ZMod.dft f t / (N : ℂ) := by
    rw [coefficient, Fintype.expect_eq_sum_div_card, ZMod.card, ZMod.dft_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    simp only [E, FinitePoisson.characterEquiv_apply, FinitePoisson.character_apply,
      ← AddChar.map_neg_eq_conj, smul_eq_mul, mul_comm t x]
  have hp : (∑ t : ZMod N, ‖ZMod.dft f t / (N : ℂ)‖ ^ 2) =
      𝔼 x, ‖f x‖ ^ 2 := by
    calc
      _ = ∑ χ : AddChar (ZMod N) ℂ, ‖coefficient f χ‖ ^ 2 :=
        Fintype.sum_equiv E.toEquiv _ _ (fun t => by
          change ‖ZMod.dft f t / (N : ℂ)‖ ^ 2 = ‖coefficient f (E t)‖ ^ 2
          rw [hc])
      _ = _ := character_parseval f
  simp only [norm_div, Complex.norm_natCast, div_pow] at hp
  rw [Fintype.expect_eq_sum_div_card, ZMod.card, ← Finset.sum_div] at hp
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hN : (N : ℝ) ≠ 0 := NeZero.ne _
  field_simp at hp ⊢
  nlinarith

private lemma dft_translation (f : ZMod N → ℂ) (t k : ZMod N) :
    ZMod.dft (fun x => f (x - t)) k =
      ZMod.stdAddChar (-(k * t)) * ZMod.dft f k := by
  classical
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.subRight t)
  intro x
  simp only [Equiv.subRight_apply, smul_eq_mul]
  have he : -(x * k) = -(k * t) + -((x - t) * k) := by ring
  rw [he, AddChar.map_add_eq_mul]
  ring

private lemma cyclic_coefficient_recovery (f g : ZMod N → ℂ) (m e : ℝ)
    (hm : 0 < m) (he : 0 ≤ e) (hsmall : e ≤ m ^ 3 / 4)
    (hdc : ZMod.dft f 0 = ZMod.dft g 0)
    (hF : ∀ k, m ≤ ‖ZMod.dft f k‖)
    (hb : ∀ k l, ‖ZMod.dft g k * ZMod.dft g l * conj (ZMod.dft g (k + l)) -
      ZMod.dft f k * ZMod.dft f l * conj (ZMod.dft f (k + l))‖ ≤ e) :
    ∃ t : ZMod N, ∀ k, ‖ZMod.dft g k -
      ZMod.stdAddChar (-(k * t)) * ZMod.dft f k‖ ≤ 2 * e / m ^ 2 := by
  obtain ⟨χ, hχ⟩ := coefficient_recovery (ZMod.dft f) (ZMod.dft g) m e hm he hsmall hdc hF hb
  let t := -(FinitePoisson.characterEquiv (m := N)).symm χ
  refine ⟨t, fun k => ?_⟩
  have ht : ZMod.stdAddChar (-(k * t)) = χ k := by
    have h := DFunLike.congr_fun ((FinitePoisson.characterEquiv (m := N)).apply_symm_apply χ) k
    simpa only [FinitePoisson.characterEquiv_apply, FinitePoisson.character_apply,
      t, mul_neg, neg_neg, mul_comm] using h
  rw [ht]
  exact hχ k

private lemma character_translation_separation (s t : ZMod N) (hst : s ≠ t) :
    (𝔼 k : ZMod N, ‖ZMod.stdAddChar (-(k * s)) -
      ZMod.stdAddChar (-(k * t))‖ ^ 2) = 2 := by
  classical
  let χ := FinitePoisson.character (m := N) (-s)
  let ψ := FinitePoisson.character (m := N) (-t)
  have hne : ψ ≠ χ := by
    intro h
    have he : FinitePoisson.characterEquiv (m := N) (-t) =
        FinitePoisson.characterEquiv (m := N) (-s) := h
    have ht := (FinitePoisson.characterEquiv (m := N)).injective he
    exact hst (neg_injective ht).symm
  have horth : (𝔼 k, conj (ψ k) * χ k) = 0 := by
    rw [character_orthogonal, if_neg hne]
  have horth' : (𝔼 k, (χ k * conj (ψ k)).re) = 0 := by
    have hh := congrArg Complex.re horth
    rw [expect_re] at hh
    simpa only [mul_comm, Complex.zero_re] using hh
  have hχ (k : ZMod N) : ZMod.stdAddChar (-(k * s)) = χ k := by
    change ZMod.stdAddChar (-(k * s)) = ZMod.stdAddChar (-s * k)
    congr 1
    ring
  have hψ (k : ZMod N) : ZMod.stdAddChar (-(k * t)) = ψ k := by
    change ZMod.stdAddChar (-(k * t)) = ZMod.stdAddChar (-t * k)
    congr 1
    ring
  simp_rw [hχ, hψ, norm_sub_sq, χ.norm_apply, ψ.norm_apply]
  simp only [one_pow]
  rw [Finset.expect_sub_distrib, Fintype.expect_const, ← Finset.mul_expect, horth']
  norm_num

private lemma signal_translation_separation (f : ZMod N → ℂ) (m : ℝ)
    (hm : 0 ≤ m) (hF : ∀ k, m ≤ ‖ZMod.dft f k‖)
    (s t : ZMod N) (hst : s ≠ t) :
    2 * m ^ 2 ≤ ∑ x, ‖f (x - s) - f (x - t)‖ ^ 2 := by
  rw [cyclic_parseval]
  have hdf (k : ZMod N) : ZMod.dft (fun x => f (x - s) - f (x - t)) k =
      (ZMod.stdAddChar (-(k * s)) - ZMod.stdAddChar (-(k * t))) * ZMod.dft f k := by
    have hh := congr_fun (map_sub ZMod.dft (fun x => f (x - s)) (fun x => f (x - t))) k
    change ZMod.dft (fun x => f (x - s) - f (x - t)) k =
      ZMod.dft (fun x => f (x - s)) k - ZMod.dft (fun x => f (x - t)) k at hh
    rw [dft_translation, dft_translation] at hh
    simpa only [sub_mul] using hh
  simp_rw [hdf, norm_mul, mul_pow]
  calc
    2 * m ^ 2 = (𝔼 k : ZMod N,
        ‖ZMod.stdAddChar (-(k * s)) - ZMod.stdAddChar (-(k * t))‖ ^ 2) * m ^ 2 := by
      rw [character_translation_separation s t hst]
    _ = (𝔼 k : ZMod N,
        ‖ZMod.stdAddChar (-(k * s)) - ZMod.stdAddChar (-(k * t))‖ ^ 2 * m ^ 2) :=
      Finset.expect_mul _ _ _
    _ ≤ _ := by
      apply Finset.expect_le_expect
      intro k _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm (hF k) 2) (sq_nonneg _)

private lemma squared_triangle (a b c : ℂ) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a - c‖ ^ 2 + 2 * ‖c - b‖ ^ 2 := by
  have ht : ‖a - b‖ ≤ ‖a - c‖ + ‖c - b‖ := norm_sub_le_norm_sub_add_norm_sub a c b
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith [sq_nonneg (‖a - c‖ - ‖c - b‖)]

/-- Uniform full-bispectrum errors select a unique nearby cyclic translation.
The signal error uses counting measure, and the DFT is unnormalized. -/
theorem full_bispectrum_stability (f g : ZMod N → ℂ) (m ε : ℝ)
    (hm : 0 < m) (hε : 0 ≤ ε) (hsmall : ε ≤ m ^ 3 / 4)
    (hdc : ZMod.dft f 0 = ZMod.dft g 0)
    (hF : ∀ k, m ≤ ‖ZMod.dft f k‖)
    (hb : ∀ k l, ‖ZMod.dft g k * ZMod.dft g l * conj (ZMod.dft g (k + l)) -
      ZMod.dft f k * ZMod.dft f l * conj (ZMod.dft f (k + l))‖ ≤ ε) :
    ∃ t : ZMod N,
      (∑ x, ‖g x - f (x - t)‖ ^ 2) ≤ (2 * ε / m ^ 2) ^ 2 ∧
      (∀ k, ‖ZMod.dft g k - ZMod.stdAddChar (-(k * t)) * ZMod.dft f k‖ ≤
        2 * ε / m ^ 2) ∧
      (∀ s : ZMod N, (∑ x, ‖g x - f (x - s)‖ ^ 2) ≤
        (2 * ε / m ^ 2) ^ 2 → s = t) := by
  classical
  obtain ⟨t, ht⟩ := cyclic_coefficient_recovery f g m ε hm hε hsmall hdc hF hb
  let R := 2 * ε / m ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsignal : (∑ x, ‖g x - f (x - t)‖ ^ 2) ≤ R ^ 2 := by
    rw [cyclic_parseval]
    have hdf (k : ZMod N) : ZMod.dft (fun x => g x - f (x - t)) k =
        ZMod.dft g k - ZMod.stdAddChar (-(k * t)) * ZMod.dft f k := by
      have hh := congr_fun (map_sub ZMod.dft g (fun x => f (x - t))) k
      change ZMod.dft (fun x => g x - f (x - t)) k =
        ZMod.dft g k - ZMod.dft (fun x => f (x - t)) k at hh
      rw [dft_translation] at hh
      exact hh
    simp_rw [hdf]
    exact Finset.expect_le Finset.univ_nonempty
      (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (ht k) 2)
  refine ⟨t, hsignal, ht, fun s hs => ?_⟩
  by_contra hst
  have hsep := signal_translation_separation f m hm.le hF s t hst
  have htri : (∑ x, ‖f (x - s) - f (x - t)‖ ^ 2) ≤ 4 * R ^ 2 := by
    calc
      _ ≤ ∑ x, (2 * ‖f (x - s) - g x‖ ^ 2 + 2 * ‖g x - f (x - t)‖ ^ 2) :=
        Finset.sum_le_sum (fun x _ => squared_triangle _ _ _)
      _ = 2 * (∑ x, ‖g x - f (x - s)‖ ^ 2) +
          2 * (∑ x, ‖g x - f (x - t)‖ ^ 2) := by
        have hrev (x : ZMod N) : ‖f (x - s) - g x‖ = ‖g x - f (x - s)‖ :=
          norm_sub_rev _ _
        simp_rw [hrev]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by linarith
  have hRm : R ≤ m / 2 := by
    dsimp [R]
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    nlinarith
  have hsquare : R ^ 2 ≤ (m / 2) ^ 2 := pow_le_pow_left₀ hR hRm 2
  nlinarith [sq_pos_of_pos hm]

#check @full_bispectrum_stability
#print axioms full_bispectrum_stability

end Cyclic

end
end D5.S3.Fourier.FullBispectrumStability
