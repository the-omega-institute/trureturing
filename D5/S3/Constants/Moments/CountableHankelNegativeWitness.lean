/- GID: D5/S3/Constants/Moments/CountableHankelNegativeWitness
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/CountableHankelNegativeWitness
   mirror-E: none(waiver:countable-spectrum-classical-analysis)
   anchors: []
   utility: none
   digest: Complete countable conjugate-spectrum integer negative polynomial witnesses. -/

import D5.S3.Constants.NewtonHankelRealRootCriterion
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Data.Fintype.EquivFin

/-! Complete head isolation and a quantitative bound on the full infinite tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Polynomial Filter
open scoped BigOperators ComplexConjugate Topology

namespace D5.S3.Constants.Moments.CountableHankelNegativeWitness

private theorem eval_bound (p : ℝ[X]) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖p.eval₂ Complex.ofRealHom z‖ ≤ ∑ k ∈ p.support, |p.coeff k| := by
  rw [Polynomial.eval₂_eq_sum]
  calc
    ‖∑ k ∈ p.support, (p.coeff k : ℂ) * z ^ k‖ ≤
        ∑ k ∈ p.support, ‖(p.coeff k : ℂ) * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ p.support, |p.coeff k| := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

theorem square_summable {ι : Type*} (z w : ι → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hw : Summable (fun i => ‖w i‖)) (p : ℝ[X]) :
    Summable (fun i => w i * (p.eval₂ Complex.ofRealHom (z i)) ^ 2) := by
  let C := ∑ k ∈ p.support, |p.coeff k|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply Summable.of_norm_bounded (hw.mul_right (C ^ 2))
  intro i
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (eval_bound p (hz i)) 2)
    (norm_nonneg _)

theorem pair_polynomial {ι : Type*} (z : ι → ℂ)
    (c : Equiv.Perm ι) (hc : ∀ i, z (c i) = conj (z i))
    (E : Finset ι) (hE : ∀ i, i ∈ E ↔ c i ∈ E)
    (i₀ : ι) (hi₀ : i₀ ∈ E) (hni : conj (z i₀) ≠ z i₀) :
    ∃ p : ℝ[X], ∀ i ∈ E, p.eval₂ Complex.ofRealHom (z i) =
      if z i = z i₀ then Complex.I else if z i = conj (z i₀) then -Complex.I else 0 := by
  classical
  let roots : Fin E.card → ℂ := fun j => z (E.equivFin.symm j).val
  have himage : Finset.univ.image roots = E.image z := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, (E.equivFin.symm j).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨E.equivFin ⟨i, hi⟩, by simp [roots]⟩
  have hclosed (x : ℂ) : x ∈ E.image z ↔ conj x ∈ E.image z := by
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨c i, (hE i).mp hi, hc i⟩
    · intro hx
      obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hx
      refine Finset.mem_image.mpr ⟨c i, (hE i).mp hi, ?_⟩
      rw [hc, hiz, Complex.conj_conj]
  obtain ⟨a, ha⟩ :=
    D5.S3.Constants.NewtonHankelRealRootCriterion.exists_real_pair_interpolant roots
      (z i₀) (by rw [himage]; exact Finset.mem_image.mpr ⟨i₀, hi₀, rfl⟩) hni
      (by simpa only [himage] using hclosed)
  refine ⟨∑ j : Fin E.card, Polynomial.monomial (j : ℕ) (a j), ?_⟩
  intro i hi
  simpa [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial,
    D5.S3.Constants.NewtonHankelRealRootCriterion.vectorPolynomialValue] using
    ha (z i) (by rw [himage]; exact Finset.mem_image.mpr ⟨i, hi, rfl⟩)

def peak (p : ℝ[X]) (z₀ b : ℂ) (m : ℕ) : ℝ[X] :=
  X ^ m * (C (-(b / z₀ ^ m).re) * p ^ 2 + C (b / z₀ ^ m).im * p)

theorem peak_at (p : ℝ[X]) (z₀ b : ℂ) (hz₀ : z₀ ≠ 0)
    (hp : p.eval₂ Complex.ofRealHom z₀ = Complex.I) (m : ℕ) :
    (peak p z₀ b m).eval₂ Complex.ofRealHom z₀ = b := by
  simp only [peak, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_add, Polynomial.eval₂_C, Complex.ofRealHom_eq_coe, Complex.ofReal_neg, hp]
  have hv : (-((b / z₀ ^ m).re) : ℂ) * Complex.I ^ 2 +
      ((b / z₀ ^ m).im : ℂ) * Complex.I = b / z₀ ^ m := by
    apply Complex.ext <;> simp <;> ring
  rw [hv, mul_div_cancel₀ _ (pow_ne_zero _ hz₀)]

theorem peak_bound (p : ℝ[X]) (z₀ b z : ℂ) (hz₀ : z₀ ≠ 0)
    (hz : ‖z‖ ≤ 1) (m : ℕ) :
    ‖(peak p z₀ b m).eval₂ Complex.ofRealHom z‖ ≤
      ‖b‖ * ((∑ k ∈ p.support, |p.coeff k|) ^ 2 +
        ∑ k ∈ p.support, |p.coeff k|) * (‖z‖ / ‖z₀‖) ^ m := by
  let C := ∑ k ∈ p.support, |p.coeff k|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hp : ‖p.eval₂ Complex.ofRealHom z‖ ≤ C := eval_bound p hz
  let v := b / z₀ ^ m
  have hvre : |v.re| ≤ ‖v‖ := Complex.abs_re_le_norm v
  have hvim : |v.im| ≤ ‖v‖ := Complex.abs_im_le_norm v
  have hinner : ‖(-(v.re) : ℂ) * (p.eval₂ Complex.ofRealHom z) ^ 2 +
      (v.im : ℂ) * p.eval₂ Complex.ofRealHom z‖ ≤ ‖v‖ * (C ^ 2 + C) := by
    calc
      _ ≤ ‖(-(v.re) : ℂ) * (p.eval₂ Complex.ofRealHom z) ^ 2‖ +
          ‖(v.im : ℂ) * p.eval₂ Complex.ofRealHom z‖ := norm_add_le _ _
      _ = |v.re| * ‖p.eval₂ Complex.ofRealHom z‖ ^ 2 +
          |v.im| * ‖p.eval₂ Complex.ofRealHom z‖ := by
        simp [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖v‖ * C ^ 2 + ‖v‖ * C := by
        gcongr
      _ = ‖v‖ * (C ^ 2 + C) := by ring
  calc
    _ = ‖z‖ ^ m * ‖(-(v.re) : ℂ) * (p.eval₂ Complex.ofRealHom z) ^ 2 +
        (v.im : ℂ) * p.eval₂ Complex.ofRealHom z‖ := by
      simp only [peak, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_add, Polynomial.eval₂_C, Complex.ofRealHom_eq_coe, Complex.ofReal_neg, norm_mul,
        norm_pow, v]
    _ ≤ ‖z‖ ^ m * (‖v‖ * (C ^ 2 + C)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = ‖b‖ * (C ^ 2 + C) * (‖z‖ / ‖z₀‖) ^ m := by
      dsimp [v]
      rw [norm_div, norm_pow, div_pow]
      ring

/-- A nonreal node of nonzero weight in a complete conjugate spectrum with
finite positive-radius cuts admits a finite real polynomial of strictly negative
weighted ordinary-square sum. The infinite complement is retained. -/
theorem exists_real_negative {ι : Type*} (z w : ι → ℂ)
    (c : Equiv.Perm ι) (hz : ∀ i, ‖z i‖ ≤ 1)
    (hzi : Function.Injective z) (hzc : ∀ i, z (c i) = conj (z i))
    (hwc : ∀ i, w (c i) = conj (w i))
    (hw : Summable (fun i => ‖w i‖))
    (hfinite : ∀ r : ℝ, 0 < r → {i | r ≤ ‖z i‖}.Finite)
    (i₀ : ι) (hni : conj (z i₀) ≠ z i₀) (hw₀ : w i₀ ≠ 0) :
    ∃ p : ℝ[X], (∑' i, w i * (p.eval₂ Complex.ofRealHom (z i)) ^ 2).re < 0 := by
  classical
  have hz₀ : z i₀ ≠ 0 := by intro h; apply hni; simp [h]
  have hr : 0 < ‖z i₀‖ / 4 := by positivity
  let E := (hfinite (‖z i₀‖ / 4) hr).toFinset
  have hE (i : ι) : i ∈ E ↔ ‖z i₀‖ / 4 ≤ ‖z i‖ := by simp [E]
  have hEc (i : ι) : i ∈ E ↔ c i ∈ E := by rw [hE, hE, hzc, Complex.norm_conj]
  have hi₀ : i₀ ∈ E := (hE i₀).mpr (by linarith [norm_nonneg (z i₀)])
  obtain ⟨p, hp⟩ := pair_polynomial z c hzc E hEc i₀ hi₀ hni
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (-1 / w i₀) (by omega : 0 < (2 : ℕ))
  have hwb : w i₀ * b ^ 2 = -1 := by rw [hb]; field_simp
  have hci : c i₀ ≠ i₀ := by intro h; apply hni; rw [← hzc, h]
  have hp₀ : p.eval₂ Complex.ofRealHom (z i₀) = Complex.I := by simpa using hp i₀ hi₀
  have hpeak (m : ℕ) : (peak p (z i₀) b m).eval₂ Complex.ofRealHom (z i₀) = b :=
    peak_at p (z i₀) b hz₀ hp₀ m
  have hconj (q : ℝ[X]) (i : ι) :
      q.eval₂ Complex.ofRealHom (z (c i)) = conj (q.eval₂ Complex.ofRealHom (z i)) := by
    rw [hzc]
    exact Polynomial.aeval_conj q (z i)
  have hhead (m : ℕ) :
      (∑ i ∈ E, w i * ((peak p (z i₀) b m).eval₂ Complex.ofRealHom (z i)) ^ 2) = -2 := by
    have hpair : ({i₀, c i₀} : Finset ι) ⊆ E := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hi₀
      · exact (hEc i₀).mp hi₀
    calc
      _ = ∑ i ∈ ({i₀, c i₀} : Finset ι),
          w i * ((peak p (z i₀) b m).eval₂ Complex.ofRealHom (z i)) ^ 2 := by
        symm
        apply Finset.sum_subset hpair
        intro i hi hnot
        have hiz : z i ≠ z i₀ := by
          intro h; apply hnot; simp [hzi h]
        have hic : z i ≠ conj (z i₀) := by
          intro h; apply hnot; rw [← hzc] at h; simp [hzi h]
        have hzero : p.eval₂ Complex.ofRealHom (z i) = 0 := by
          simpa [hiz, hic] using hp i hi
        simp [peak, Polynomial.eval₂_pow, hzero]
      _ = -2 := by
        rw [Finset.sum_pair (Ne.symm hci), hconj, hpeak, hwc]
        have hcb : conj (w i₀) * (conj b) ^ 2 = -1 := by
          simpa only [map_mul, map_pow, map_neg, map_one] using congrArg conj hwb
        rw [hwb, hcb]
        norm_num
  let C := ∑ k ∈ p.support, |p.coeff k|
  let B := ‖b‖ * (C ^ 2 + C)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB : 0 ≤ B := by positivity
  have htail (m : ℕ) (i : {i // i ∉ E}) :
      ‖(peak p (z i₀) b m).eval₂ Complex.ofRealHom (z i)‖ ≤ B * (1 / 4 : ℝ) ^ m := by
    have hsmall : ‖z i‖ < ‖z i₀‖ / 4 := lt_of_not_ge (by simpa only [← hE] using i.property)
    have hratio : ‖z i‖ / ‖z i₀‖ ≤ 1 / 4 := by
      apply (div_le_iff₀ (norm_pos_iff.mpr hz₀)).mpr
      linarith
    exact (peak_bound p (z i₀) b (z i) hz₀ (hz i) m).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio m) hB)
  let W := ∑' i : {i // i ∉ E}, ‖w i‖
  have hW : Summable (fun i : {i // i ∉ E} => ‖w i‖) := hw.subtype _
  have htail_sum (m : ℕ) :
      ‖∑' i : {i // i ∉ E}, w i * ((peak p (z i₀) b m).eval₂ Complex.ofRealHom (z i)) ^ 2‖ ≤
        W * B ^ 2 * (1 / 16 : ℝ) ^ m := by
    calc
      _ ≤ ∑' i : {i // i ∉ E}, ‖w i‖ * (B * (1 / 4 : ℝ) ^ m) ^ 2 := by
        apply tsum_of_norm_bounded (hW.mul_right _).hasSum
        intro i
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (htail m i) 2) (norm_nonneg _)
      _ = W * B ^ 2 * (1 / 16 : ℝ) ^ m := by
        rw [tsum_mul_right]
        dsimp [W]
        rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]
        norm_num
        ring
  have hlim : Tendsto (fun m : ℕ => W * B ^ 2 * (1 / 16 : ℝ) ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num : (1 / 16 : ℝ) < 1)).const_mul (W * B ^ 2)
  obtain ⟨m, hm⟩ := (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists
  refine ⟨peak p (z i₀) b m, ?_⟩
  have hsplit := (square_summable z w hz hw (peak p (z i₀) b m)).sum_add_tsum_subtype_compl E
  rw [← hsplit, hhead, Complex.add_re]
  have hnorm := (htail_sum m).trans_lt hm
  have hre := Complex.re_le_norm (∑' i : {i // i ∉ E},
    w i * ((peak p (z i₀) b m).eval₂ Complex.ofRealHom (z i)) ^ 2)
  norm_num at *
  linarith

/-- Strict negativity of a finite real quadratic form survives rational
approximation and clearing a common nonzero integer denominator. -/
theorem exists_integer_negative_quadratic {d : ℕ} (M : Fin d → Fin d → ℝ)
    (u : Fin d → ℝ) (hu : (∑ a, ∑ b, u a * u b * M a b) < 0) :
    ∃ v : Fin d → ℤ, (∑ a, ∑ b, (v a : ℝ) * (v b : ℝ) * M a b) < 0 := by
  classical
  let Q : (Fin d → ℝ) → ℝ := fun x => ∑ a, ∑ b, x a * x b * M a b
  have hQ : Continuous Q := by
    fun_prop
  have hd : DenseRange (fun r : Fin d → ℚ => fun a => (r a : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨r, hr⟩ := hd.exists_mem_open
    (isOpen_lt hQ continuous_const) ⟨u, hu⟩
  let A : Matrix (Fin d) Unit ℚ := fun a _ => r a
  have hD : (A.den : ℝ) ≠ 0 := by exact_mod_cast A.den_ne_zero
  have hscale (a : Fin d) : (A.num a () : ℝ) = (A.den : ℝ) * (r a : ℝ) := by
    have h := A.num_div_den a ()
    have h' : (A.num a () : ℝ) / (A.den : ℝ) = (r a : ℝ) := by
      exact_mod_cast h
    exact (div_eq_iff hD).mp h' |>.trans (mul_comm _ _)
  refine ⟨fun a => A.num a (), ?_⟩
  simp_rw [hscale]
  have heq : (∑ a, ∑ b, ((A.den : ℝ) * (r a : ℝ)) *
      ((A.den : ℝ) * (r b : ℝ)) * M a b) = (A.den : ℝ) ^ 2 * Q (fun a => (r a : ℝ)) := by
    dsimp [Q]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [heq]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hD) hr

end D5.S3.Constants.Moments.CountableHankelNegativeWitness
