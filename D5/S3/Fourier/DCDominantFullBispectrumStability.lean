/- GID: D5/S3/Fourier/DCDominantFullBispectrumStability
   generality: G
   mirror-B: D5/B/S3/Fourier/DCDominantFullBispectrumStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uncalibrated full-bispectrum stability under source DC dominance. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Fourier.FullBispectrumStability

namespace D5.S3.Fourier.DCDominantFullBispectrumStability

open Finset
open scoped BigOperators ComplexConjugate

noncomputable section

open D5.S3.Fourier.FullBispectrumStability (cyclic_parseval dft_translation unit_mul_conj)

open private phase phase_norm phase_reconstruct radial_identity
  raw_weighted_defect weighted_correction
  signal_translation_separation squared_triangle from D5.S3.Fourier.FullBispectrumStability

set_option maxHeartbeats 800000 in
-- The cubic and mixed amplitude estimates require several nonlinear arithmetic steps.
private lemma dc_dominant_amplitudes {A : Type*} [AddCommGroup A]
    (F J : A → ℂ) (m e : ℝ) (hm : 0 < m)
    (hsmall : e ≤ m ^ 3 / 4) (hF : ∀ k, m ≤ ‖F k‖)
    (hdom : ∀ k, ‖F k‖ ≤ ‖F 0‖)
    (hb : ∀ k l, ‖J k * J l * conj (J (k + l)) -
      F k * F l * conj (F (k + l))‖ ≤ e) :
    ∀ k, J k ≠ 0 ∧ 3 * m ^ 2 / 4 ≤ ‖F k‖ * ‖J k‖ ∧
      (‖J k‖ - ‖F k‖) ^ 2 ≤ e ^ 2 / m ^ 4 := by
  intro k
  let a := ‖F 0‖
  let b := ‖J 0‖
  let r := ‖F k‖
  let s := ‖J k‖
  have ha : 0 < a := hm.trans_le (hF 0)
  have hr : 0 < r := hm.trans_le (hF k)
  have hb0 : 0 ≤ b := norm_nonneg _
  have hs0 : 0 ≤ s := norm_nonneg _
  have hma : m ≤ a := hF 0
  have hmr : m ≤ r := hF k
  have hra : r ≤ a := hdom k
  have hc : |b ^ 3 - a ^ 3| ≤ e := by
    have h := (abs_norm_sub_norm_le (J 0 * J 0 * conj (J (0 + 0)))
      (F 0 * F 0 * conj (F (0 + 0)))).trans (hb 0 0)
    simpa only [zero_add, norm_mul, Complex.norm_conj, a, b, pow_succ, pow_zero,
      one_mul] using h
  have hz : |b * s ^ 2 - a * r ^ 2| ≤ e := by
    have h := (abs_norm_sub_norm_le (J 0 * J k * conj (J (0 + k)))
      (F 0 * F k * conj (F (0 + k)))).trans (hb 0 k)
    simpa only [zero_add, norm_mul, Complex.norm_conj, a, b, r, s, pow_two,
      mul_assoc] using h
  have hea : e ≤ a ^ 3 / 4 := hsmall.trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hm.le hma 3) (by norm_num))
  have hear : e ≤ a * r ^ 2 / 4 := by
    have h₁ := mul_le_mul hma (pow_le_pow_left₀ hm.le hmr 2)
      (sq_nonneg m) ha.le
    nlinarith
  have hba : 3 * a / 4 ≤ b := by
    have hc' := (abs_le.mp hc).1
    by_contra h
    have hlt : b < 3 * a / 4 := lt_of_not_ge h
    have hh := pow_le_pow_left₀ hb0 hlt.le 3
    nlinarith [pow_pos ha 3]
  have hfac : |b - a| * (b ^ 2 + a * b + a ^ 2) ≤ e := by
    have hid : b ^ 3 - a ^ 3 = (b - a) * (b ^ 2 + a * b + a ^ 2) := by ring
    rw [hid, abs_mul, abs_of_nonneg
      (add_nonneg (add_nonneg (sq_nonneg b) (mul_nonneg ha.le hb0)) (sq_nonneg a))] at hc
    exact hc
  have heta : 2 * a ^ 2 * |b - a| ≤ e := by
    have hbb := mul_le_mul hba hba (by positivity : 0 ≤ 3 * a / 4) hb0
    have hab := mul_le_mul_of_nonneg_left hba ha.le
    have hsum : 2 * a ^ 2 ≤ b ^ 2 + a * b + a ^ 2 := by nlinarith
    exact (by nlinarith [mul_le_mul_of_nonneg_right hsum (abs_nonneg (b - a))] :
      2 * a ^ 2 * |b - a| ≤ |b - a| * (b ^ 2 + a * b + a ^ 2)).trans hfac
  have hbs2 : 3 * a * r ^ 2 / 4 ≤ b * s ^ 2 := by
    have hz' := (abs_le.mp hz).1
    linarith
  have hbs : 3 * a * r / 4 ≤ b * s := by
    have hprod := mul_le_mul hba hbs2 (by positivity : 0 ≤ 3 * a * r ^ 2 / 4) hb0
    apply (sq_le_sq₀ (by positivity : 0 ≤ 3 * a * r / 4) (mul_nonneg hb0 hs0)).mp
    nlinarith only [hprod]
  have hbr := mul_le_mul_of_nonneg_right hba hr.le
  have hsum : 3 * a * r / 2 ≤ b * (r + s) := by nlinarith
  have habsr : |b - a| * r ^ 2 ≤ e / 2 := by
    have hsq := pow_le_pow_left₀ hr.le hra 2
    have hh := mul_le_mul_of_nonneg_left hsq (abs_nonneg (b - a))
    nlinarith
  have hdiff : b * (r + s) * |s - r| ≤ e + |b - a| * r ^ 2 := by
    have hid : b * (s ^ 2 - r ^ 2) =
        (b * s ^ 2 - a * r ^ 2) + (a - b) * r ^ 2 := by ring
    have hh := abs_add_le (b * s ^ 2 - a * r ^ 2) ((a - b) * r ^ 2)
    rw [← hid, abs_mul, abs_of_nonneg hb0, abs_mul,
      abs_of_nonneg (sq_nonneg r), abs_sub_comm a b] at hh
    have hsq : |s ^ 2 - r ^ 2| = |s - r| * (r + s) := by
      rw [show s ^ 2 - r ^ 2 = (s - r) * (r + s) by ring, abs_mul,
        abs_of_nonneg (add_nonneg hr.le hs0)]
    rw [hsq] at hh
    nlinarith
  have hard : a * r * |s - r| ≤ e := by
    have hh := mul_le_mul_of_nonneg_right hsum (abs_nonneg (s - r))
    nlinarith
  have hmd : m ^ 2 * |s - r| ≤ e := by
    have hp := mul_le_mul hma hmr hm.le ha.le
    have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg (s - r))
    nlinarith
  have hdm : |s - r| ≤ m / 4 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hm)).mp
    nlinarith
  have hsl : 3 * r / 4 ≤ s := by
    have hh := (abs_le.mp hdm).1
    linarith
  have hspos : 0 < s := by linarith
  have hp : 3 * m ^ 2 / 4 ≤ r * s := by
    have h₁ := mul_le_mul_of_nonneg_left hsl hr.le
    have h₂ := pow_le_pow_left₀ hm.le hmr 2
    nlinarith
  refine ⟨norm_ne_zero_iff.mp hspos.ne', hp, ?_⟩
  change (s - r) ^ 2 ≤ e ^ 2 / m ^ 4
  apply (le_div_iff₀ (pow_pos hm 4)).mpr
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ m ^ 2 * |s - r|) hmd 2
  have hp4 : (m ^ 2) ^ 2 = m ^ 4 := by ring
  rw [mul_pow, hp4, sq_abs] at hh
  nlinarith

private lemma dc_dominant_coefficient_recovery {A : Type*} [AddCommGroup A] [Finite A]
    (F J : A → ℂ) (m e : ℝ) (hm : 0 < m) (he : 0 ≤ e)
    (hsmall : e ≤ m ^ 3 / 4) (hdom : ∀ k, ‖F k‖ ≤ ‖F 0‖)
    (hF : ∀ k, m ≤ ‖F k‖)
    (hb : ∀ k l, ‖J k * J l * conj (J (k + l)) -
      F k * F l * conj (F (k + l))‖ ≤ e) :
    ∃ χ : AddChar A ℂ, ∀ k, ‖J k - χ k * F k‖ ≤ 2 * e / m ^ 2 := by
  let : Fintype A := Fintype.ofFinite A
  have ha := dc_dominant_amplitudes F J m e hm hsmall hF hdom hb
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
      ring
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

/-- Uniform full-bispectrum errors select a unique nearby cyclic translation.
The signal error uses counting measure, and the DFT is unnormalized. -/
theorem full_bispectrum_stability_dc_dominant (f g : ZMod N → ℂ) (m ε : ℝ)
    (hm : 0 < m) (hε : 0 ≤ ε) (hsmall : ε ≤ m ^ 3 / 4)
    (hdom : ∀ k, ‖ZMod.dft f k‖ ≤ ‖ZMod.dft f 0‖)
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
  obtain ⟨χ, hχ⟩ := dc_dominant_coefficient_recovery (ZMod.dft f) (ZMod.dft g)
    m ε hm hε hsmall hdom hF hb
  let t := -(FinitePoisson.characterEquiv (m := N)).symm χ
  have ht (k : ZMod N) : ‖ZMod.dft g k -
      ZMod.stdAddChar (-(k * t)) * ZMod.dft f k‖ ≤ 2 * ε / m ^ 2 := by
    have h := DFunLike.congr_fun ((FinitePoisson.characterEquiv (m := N)).apply_symm_apply χ) k
    have heq : ZMod.stdAddChar (-(k * t)) = χ k := by
      simpa only [FinitePoisson.characterEquiv_apply, FinitePoisson.character_apply,
        t, mul_neg, neg_neg, mul_comm] using h
    rw [heq]
    exact hχ k
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


#check @full_bispectrum_stability_dc_dominant
#print axioms full_bispectrum_stability_dc_dominant

end Cyclic

end
end D5.S3.Fourier.DCDominantFullBispectrumStability
