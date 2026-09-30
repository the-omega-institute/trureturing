/- GID: D5/S3/Quantum/Tomography/ActualThreeSettingRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ActualThreeSettingRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual three-setting qubit reconstruction with sharp trace-distance noise. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ActualThreeSettingRecovery

open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option maxHeartbeats 1000000 in
theorem actual_three_setting_recovery :
    ∀ (p x y : ℝ),
      0 ≤ p → p ≤ 1 → x ^ 2 + y ^ 2 ≤ p * (1 - p) →
      let φ := Real.goldenRatio
      let r := φ⁻¹
      let s := Real.sqrt r
      let b := r * s
      let h := r ^ 2 - r
      let P : Matrix (Fin 2) (Fin 2) ℂ := !![⟨1, 0⟩, 0; 0, 0]
      let Q : Matrix (Fin 2) (Fin 2) ℂ :=
        !![⟨r ^ 2, 0⟩, ⟨b, 0⟩; ⟨b, 0⟩, ⟨r, 0⟩]
      let V : Matrix (Fin 2) (Fin 2) ℂ := !![⟨0, 1⟩, 0; 0, ⟨1, 0⟩]
      let ρ : Matrix (Fin 2) (Fin 2) ℂ :=
        !![⟨p, 0⟩, ⟨x, y⟩; ⟨x, -y⟩, ⟨1 - p, 0⟩]
      let m₀ := (Matrix.trace (P * ρ)).re
      let m₁ := (Matrix.trace (Q * ρ)).re
      let m₂ := (Matrix.trace (Q * V * ρ * V.conjTranspose)).re
      P.PosSemidef ∧ P * P = P ∧ Q.PosSemidef ∧ Q * Q = Q ∧
      V.conjTranspose * V = 1 ∧ ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      m₀ = p ∧
        m₁ = r + h * p + 2 * b * x ∧
        m₂ = r + h * p - 2 * b * y ∧
        (m₁ - r - h * m₀) / (2 * b) = x ∧
        (r + h * m₀ - m₂) / (2 * b) = y ∧
        (∀ (ε η₀ η₁ η₂ : ℝ), 0 ≤ ε →
          |η₀| ≤ ε → |η₁| ≤ ε → |η₂| ≤ ε →
          let n₀ := m₀ + η₀
          let n₁ := m₁ + η₁
          let n₂ := m₂ + η₂
          let pHat := n₀
          let xHat := (n₁ - r - h * n₀) / (2 * b)
          let yHat := (r + h * n₀ - n₂) / (2 * b)
          let rhoHat : Matrix (Fin 2) (Fin 2) ℂ :=
            !![⟨pHat, 0⟩, ⟨xHat, yHat⟩; ⟨xHat, -yHat⟩, ⟨1 - pHat, 0⟩]
          let radius := Real.sqrt ((pHat - 1 / 2) ^ 2 + xHat ^ 2 + yHat ^ 2)
          let scale := if radius ≤ 1 / 2 then 1 else (1 / 2) / radius
          let projP := 1 / 2 + scale * (pHat - 1 / 2)
          let projX := scale * xHat
          let projY := scale * yHat
          let rhoProj : Matrix (Fin 2) (Fin 2) ℂ :=
            !![⟨projP, 0⟩, ⟨projX, projY⟩; ⟨projX, -projY⟩, ⟨1 - projP, 0⟩]
          rhoHat.IsHermitian ∧ Matrix.trace rhoHat = 1 ∧
            traceNorm (rhoHat - ρ) / 2 ≤ Real.sqrt (1 + 2 * φ) * ε ∧
            rhoProj.PosSemidef ∧ Matrix.trace rhoProj = 1 ∧
            traceNorm (rhoProj - ρ) / 2 ≤ traceNorm (rhoHat - ρ) / 2) ∧
        (∀ ε : ℝ, 0 < ε →
          ε ≤ 1 / (2 * Real.sqrt (1 + 2 * φ)) →
          let rho₀ : Matrix (Fin 2) (Fin 2) ℂ :=
            !![⟨1 / 2, 0⟩, 0; 0, ⟨1 / 2, 0⟩]
          let n := 1 / 2 + ε
          let pHat := n
          let xHat := (n - r - h * n) / (2 * b)
          let yHat := (r + h * n - n) / (2 * b)
          let rhoHat : Matrix (Fin 2) (Fin 2) ℂ :=
            !![⟨pHat, 0⟩, ⟨xHat, yHat⟩; ⟨xHat, -yHat⟩, ⟨1 - pHat, 0⟩]
          rho₀.PosSemidef ∧ Matrix.trace rho₀ = 1 ∧
            (Matrix.trace (P * rho₀)).re = 1 / 2 ∧
            (Matrix.trace (Q * rho₀)).re = 1 / 2 ∧
            (Matrix.trace (Q * V * rho₀ * V.conjTranspose)).re = 1 / 2 ∧
            0 ≤ n ∧ n ≤ 1 ∧ rhoHat.PosSemidef ∧
            traceNorm (rhoHat - rho₀) / 2 = Real.sqrt (1 + 2 * φ) * ε) := by
  intro p x y hp0 hp1 hxy φ r s b h P Q V ρ m₀ m₁ m₂
  have htn (a u v : ℝ) :
      traceNorm ((!![⟨a, 0⟩, ⟨u, v⟩; ⟨u, -v⟩, ⟨-a, 0⟩]) : Matrix (Fin 2) (Fin 2) ℂ) =
        2 * Real.sqrt (a ^ 2 + u ^ 2 + v ^ 2) := by
    let D : Matrix (Fin 2) (Fin 2) ℂ :=
      !![⟨a, 0⟩, ⟨u, v⟩; ⟨u, -v⟩, ⟨-a, 0⟩]
    let t : ℝ := a ^ 2 + u ^ 2 + v ^ 2
    let S : Matrix (Fin 2) (Fin 2) ℂ :=
      !![⟨Real.sqrt t, 0⟩, 0; 0, ⟨Real.sqrt t, 0⟩]
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hD : Dᴴ * D =
        !![⟨t, 0⟩, 0; 0, ⟨t, 0⟩] := by
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [D, t, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
    have hS : S.PosSemidef := by
      rw [show S = Matrix.diagonal ![(Real.sqrt t : ℂ), (Real.sqrt t : ℂ)] by
        ext i j; fin_cases i <;> fin_cases j <;> simp [S, Matrix.diagonal]
        <;> rfl]
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i <;> simpa using (Complex.ofReal_nonneg.mpr (Real.sqrt_nonneg t))
    have hsq : S * S =
        !![⟨t, 0⟩, 0; 0, ⟨t, 0⟩] := by
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [S, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
      all_goals nlinarith [Real.sq_sqrt ht]
    have hsqrt : CFC.sqrt (Dᴴ * D) = S := by
      apply (CFC.sqrt_eq_iff _ _ (Matrix.posSemidef_conjTranspose_mul_self D).nonneg
        hS.nonneg).mpr
      rw [hD, hsq]
    unfold traceNorm
    rw [hsqrt]
    simp [S, t, Matrix.trace_fin_two]
    ring
  have hphysical (a u v : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
      (huv : u ^ 2 + v ^ 2 ≤ a * (1 - a)) :
      ((!![⟨a, 0⟩, ⟨u, v⟩; ⟨u, -v⟩, ⟨1 - a, 0⟩]) :
        Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := by
    by_cases ha : a = 0
    · have hu : u = 0 := by rw [ha] at huv; nlinarith [sq_nonneg v]
      have hv : v = 0 := by rw [ha] at huv; nlinarith [sq_nonneg u]
      subst a; subst u; subst v
      have hdg : (Matrix.diagonal ![(0 : ℂ), (1 : ℂ)]).PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro i; fin_cases i <;> norm_num
      convert hdg using 1
      ext i j; fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;> norm_num [Matrix.diagonal]
    · have ha : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
      let c : ℝ := Real.sqrt a
      let z : Fin 2 → ℂ := ![⟨c, 0⟩, ⟨u / c, -v / c⟩]
      let d : ℝ := 1 - a - (u ^ 2 + v ^ 2) / a
      have hc : 0 < c := Real.sqrt_pos.mpr ha
      have hc2 : c ^ 2 = a := Real.sq_sqrt ha.le
      have hd : 0 ≤ d := by
        dsimp [d]
        apply sub_nonneg.mpr
        apply (div_le_iff₀ ha).mpr
        nlinarith [huv]
      have hz : (Matrix.vecMulVec z (star z)).PosSemidef :=
        Matrix.posSemidef_vecMulVec_self_star z
      have hdg : (Matrix.diagonal ![(0 : ℂ), (d : ℂ)]).PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro i; fin_cases i <;> simp [hd]
      have hstar : star z = ![⟨c, 0⟩, ⟨u / c, v / c⟩] := by
        ext i; fin_cases i <;> apply Complex.ext <;>
          simp [Pi.star_apply, z, Complex.star_def] <;> ring
      have heq :
          ((!![⟨a, 0⟩, ⟨u, v⟩; ⟨u, -v⟩, ⟨1 - a, 0⟩]) :
            Matrix (Fin 2) (Fin 2) ℂ) =
          Matrix.vecMulVec z (star z) + Matrix.diagonal ![(0 : ℂ), (d : ℂ)] := by
        rw [hstar]
        ext i j
        fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
          simp [z, d, Matrix.vecMulVec, Matrix.diagonal,
            Complex.mul_re, Complex.mul_im, Complex.ofReal_pow, pow_two]
        all_goals field_simp [ne_of_gt hc, ne_of_gt ha] <;> nlinarith [hc2]
      rw [heq]
      exact hz.add hdg
  have hherm (a u v : ℝ) :
      ((!![⟨a, 0⟩, ⟨u, v⟩; ⟨u, -v⟩, ⟨1 - a, 0⟩]) :
        Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [Matrix.conjTranspose_apply, Complex.star_def] <;> ring
  have hproject (a u v A U W : ℝ)
      (htrue : a ^ 2 + u ^ 2 + v ^ 2 ≤ 1 / 4) :
      let R := Real.sqrt (A ^ 2 + U ^ 2 + W ^ 2)
      let t := if R ≤ 1 / 2 then 1 else (1 / 2) / R
      (t * A) ^ 2 + (t * U) ^ 2 + (t * W) ^ 2 ≤ 1 / 4 ∧
        Real.sqrt ((t * A - a) ^ 2 + (t * U - u) ^ 2 +
          (t * W - v) ^ 2) ≤
          Real.sqrt ((A - a) ^ 2 + (U - u) ^ 2 + (W - v) ^ 2) := by
    intro R t
    have hR0 : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R ^ 2 = A ^ 2 + U ^ 2 + W ^ 2 :=
      Real.sq_sqrt (by positivity)
    by_cases hsmall : R ≤ 1 / 2
    · have ht : t = 1 := by
        dsimp only [t]
        split_ifs <;> rfl
      rw [ht]
      have hR2le : R ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
        (sq_le_sq₀ hR0 (by norm_num)).mpr hsmall
      rw [hR2] at hR2le
      constructor
      · simpa only [one_mul] using (show A ^ 2 + U ^ 2 + W ^ 2 ≤ 1 / 4 by
          nlinarith [hR2le])
      · simp only [one_mul, le_refl]
    · have hRgt : 1 / 2 < R := lt_of_not_ge hsmall
      have ht : t = (1 / 2) / R := by
        dsimp only [t]
        split_ifs <;> rfl
      have ht0 : 0 ≤ t := by rw [ht]; positivity
      have ht1 : t ≤ 1 := by
        rw [ht]
        apply (div_le_iff₀ (by linarith : 0 < R)).mpr
        linarith
      have htR : t * R = 1 / 2 := by
        rw [ht]
        field_simp [ne_of_gt (by linarith : 0 < R)]
      let dot : ℝ := A * a + U * u + W * v
      have hdotSq : dot ^ 2 ≤ R ^ 2 * (a ^ 2 + u ^ 2 + v ^ 2) := by
        calc
          dot ^ 2 = R ^ 2 * (a ^ 2 + u ^ 2 + v ^ 2) -
              ((A * u - U * a) ^ 2 + (A * v - W * a) ^ 2 +
                (U * v - W * u) ^ 2) := by rw [hR2]; dsimp [dot]; ring
          _ ≤ _ := sub_le_self _ (by positivity)
      have hdotHalfSq : dot ^ 2 ≤ (R / 2) ^ 2 := by
        calc
          dot ^ 2 ≤ R ^ 2 * (a ^ 2 + u ^ 2 + v ^ 2) := hdotSq
          _ ≤ R ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left htrue (sq_nonneg R)
          _ = (R / 2) ^ 2 := by ring
      have hdotHalf : dot ≤ R / 2 := by nlinarith [hdotHalfSq, hR0]
      have hRquad : R / 2 ≤ R ^ 2 := by
        nlinarith [mul_nonneg hR0 (sub_nonneg.mpr hRgt.le)]
      have hfactor : 0 ≤ (1 + t) * R ^ 2 - 2 * dot := by
        nlinarith [hdotHalf, hRquad, mul_nonneg ht0 (sq_nonneg R)]
      have hball : (t * A) ^ 2 + (t * U) ^ 2 + (t * W) ^ 2 ≤ 1 / 4 := by
        have heq : (t * A) ^ 2 + (t * U) ^ 2 + (t * W) ^ 2 =
            (t * R) ^ 2 := by
          calc
            _ = t ^ 2 * (A ^ 2 + U ^ 2 + W ^ 2) := by ring
            _ = t ^ 2 * R ^ 2 := by rw [hR2]
            _ = (t * R) ^ 2 := by ring
        rw [heq, htR]
        norm_num
      have hdiffSq :
          ((A - a) ^ 2 + (U - u) ^ 2 + (W - v) ^ 2) -
            ((t * A - a) ^ 2 + (t * U - u) ^ 2 +
              (t * W - v) ^ 2) =
            (1 - t) * ((1 + t) * R ^ 2 - 2 * dot) := by
        rw [hR2]
        dsimp [dot]
        ring
      have hdistSq : (t * A - a) ^ 2 + (t * U - u) ^ 2 +
          (t * W - v) ^ 2 ≤
          (A - a) ^ 2 + (U - u) ^ 2 + (W - v) ^ 2 := by
        rw [← sub_nonneg, hdiffSq]
        exact mul_nonneg (sub_nonneg.mpr ht1) hfactor
      exact ⟨hball, Real.sqrt_le_sqrt hdistSq⟩
  have hrpos : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hrlt : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hrEq : r = Real.goldenRatio - 1 := by
    dsimp only [r, φ]
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hrquad : r ^ 2 + r = 1 := by
    rw [hrEq]
    nlinarith [Real.goldenRatio_sq]
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsquad : s ^ 2 = r := Real.sq_sqrt hrpos.le
  have hbpos : 0 < b := mul_pos hrpos hspos
  have hh : h = 1 - 2 * r := by dsimp [h]; linarith [hrquad]
  have hhneg : h < 0 := by
    rw [hh]
    nlinarith [hrquad, hrpos, hrlt]
  have hcoeff : (1 - h) / (2 * b) = Real.sqrt φ := by
    rw [hh]
    have hleft : (1 - (1 - 2 * r)) / (2 * b) = s⁻¹ := by
      dsimp [b]
      field_simp [ne_of_gt hrpos, ne_of_gt hspos]
      ring
    rw [hleft]
    have hsφ : s ^ 2 * φ = 1 := by
      rw [hsquad]
      dsimp [r, φ]
      field_simp [Real.goldenRatio_ne_zero]
    have hsqrtφ : (Real.sqrt φ) ^ 2 = φ := Real.sq_sqrt Real.goldenRatio_pos.le
    have hprod : s * Real.sqrt φ = 1 := by
      have hsq : (s * Real.sqrt φ) ^ 2 = 1 := by
        calc
          _ = s ^ 2 * (Real.sqrt φ) ^ 2 := by ring
          _ = 1 := by rw [hsqrtφ, hsφ]
      nlinarith [mul_pos hspos (Real.sqrt_pos.mpr Real.goldenRatio_pos), hsq]
    calc
      s⁻¹ = s⁻¹ * (s * Real.sqrt φ) := by rw [hprod]; ring
      _ = Real.sqrt φ := by field_simp [ne_of_gt hspos]
  have hnoise (ε η₀ η₁ η₂ : ℝ) (hε : 0 ≤ ε)
      (hη₀ : |η₀| ≤ ε) (hη₁ : |η₁| ≤ ε) (hη₂ : |η₂| ≤ ε) :
      Real.sqrt (η₀ ^ 2 + ((η₁ - h * η₀) / (2 * b)) ^ 2 +
          ((h * η₀ - η₂) / (2 * b)) ^ 2) ≤
        Real.sqrt (1 + 2 * φ) * ε := by
    have hnum₁ : |η₁ - h * η₀| ≤ (1 - h) * ε := by
      calc
        |η₁ - h * η₀| ≤ |η₁| + |h * η₀| := abs_sub _ _
        _ = |η₁| + (-h) * |η₀| := by rw [abs_mul, abs_of_neg hhneg]
        _ ≤ ε + (-h) * ε := by gcongr; linarith [hhneg]
        _ = (1 - h) * ε := by ring
    have hnum₂ : |h * η₀ - η₂| ≤ (1 - h) * ε := by
      calc
        |h * η₀ - η₂| ≤ |h * η₀| + |η₂| := abs_sub _ _
        _ = (-h) * |η₀| + |η₂| := by rw [abs_mul, abs_of_neg hhneg]
        _ ≤ (-h) * ε + ε := by gcongr; linarith [hhneg]
        _ = (1 - h) * ε := by ring
    have hδ₁ : |(η₁ - h * η₀) / (2 * b)| ≤ Real.sqrt φ * ε := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * b)]
      calc
        _ ≤ ((1 - h) * ε) / (2 * b) := div_le_div_of_nonneg_right hnum₁ (by positivity)
        _ = Real.sqrt φ * ε := by calc
          _ = ((1 - h) / (2 * b)) * ε := by ring
          _ = _ := by rw [hcoeff]
    have hδ₂ : |(h * η₀ - η₂) / (2 * b)| ≤ Real.sqrt φ * ε := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * b)]
      calc
        _ ≤ ((1 - h) * ε) / (2 * b) := div_le_div_of_nonneg_right hnum₂ (by positivity)
        _ = Real.sqrt φ * ε := by calc
          _ = ((1 - h) / (2 * b)) * ε := by ring
          _ = _ := by rw [hcoeff]
    have hφpos : 0 ≤ φ := Real.goldenRatio_pos.le
    have hroot : (Real.sqrt φ) ^ 2 = φ := Real.sq_sqrt hφpos
    have hsq₀ : η₀ ^ 2 ≤ ε ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg η₀) hε).mpr hη₀
    have hsq₁ : ((η₁ - h * η₀) / (2 * b)) ^ 2 ≤
        (Real.sqrt φ * ε) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hε)).mpr hδ₁
    have hsq₂ : ((h * η₀ - η₂) / (2 * b)) ^ 2 ≤
        (Real.sqrt φ * ε) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hε)).mpr hδ₂
    have hrad : η₀ ^ 2 + ((η₁ - h * η₀) / (2 * b)) ^ 2 +
        ((h * η₀ - η₂) / (2 * b)) ^ 2 ≤ (1 + 2 * φ) * ε ^ 2 := by
      calc
        _ ≤ ε ^ 2 + (Real.sqrt φ * ε) ^ 2 +
            (Real.sqrt φ * ε) ^ 2 := by gcongr
        _ = (1 + 2 * φ) * ε ^ 2 := by rw [mul_pow, hroot]; ring
    have hbound := Real.sqrt_le_sqrt hrad
    rw [Real.sqrt_mul (by positivity : 0 ≤ 1 + 2 * φ), Real.sqrt_sq hε] at hbound
    exact hbound
  have hread₀ : m₀ = p := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      m₀, P, ρ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hread₁ : m₁ = r + h * p + 2 * b * x := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      m₁, Q, ρ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hread₂ : m₂ = r + h * p - 2 * b * y := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      m₂, Q, V, ρ, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hP : P.PosSemidef := by
    have hdg : (Matrix.diagonal ![(1 : ℂ), (0 : ℂ)]).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i; fin_cases i <;> norm_num
    convert hdg using 1
    ext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> norm_num [P, Matrix.diagonal]
  have hPsq : P * P = P := by
    ext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [P, Matrix.mul_apply, Fin.sum_univ_two]
  have hQ : Q.PosSemidef := by
    let z : Fin 2 → ℂ := ![(r : ℂ), (s : ℂ)]
    have hz : (Matrix.vecMulVec z (star z)).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star z
    have hstar : star z = z := by
      ext i; fin_cases i <;> simp [Pi.star_apply, z]
    have heq : Q = Matrix.vecMulVec z (star z) := by
      rw [hstar]
      ext i j; fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        simp [Q, z, b, Matrix.vecMulVec, Complex.mul_re, Complex.mul_im,
          hsquad] <;> nlinarith [hsquad]
    rw [heq]
    exact hz
  have hQsq : Q * Q = Q := by
    have hb2 : b ^ 2 = r ^ 3 := by
      dsimp [b]
      rw [mul_pow, hsquad]
      ring
    have hdiag1 : r ^ 4 + b ^ 2 = r ^ 2 := by
      rw [hb2]
      calc
        r ^ 4 + r ^ 3 = r ^ 2 * (r ^ 2 + r) := by ring
        _ = r ^ 2 := by rw [hrquad]; ring
    have hdiag2 : b ^ 2 + r ^ 2 = r := by
      rw [hb2]
      calc
        r ^ 3 + r ^ 2 = r * (r ^ 2 + r) := by ring
        _ = r := by rw [hrquad]; ring
    have hoff : r ^ 2 * b + b * r = b := by
      calc
        r ^ 2 * b + b * r = b * (r ^ 2 + r) := by ring
        _ = b := by rw [hrquad]; ring
    ext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      simp [Q, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_pow]
    all_goals nlinarith only [hdiag1, hdiag2, hoff]
  have hVunit : V.conjTranspose * V = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;>
      norm_num [V, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Complex.star_def]
  have hρ : ρ.PosSemidef := by
    simpa only [ρ] using hphysical p x y hp0 hp1 hxy
  have hρtrace : Matrix.trace ρ = 1 := by
    apply Complex.ext <;> simp [ρ, Matrix.trace_fin_two] <;> ring
  have hinv₁ : (m₁ - r - h * m₀) / (2 * b) = x := by
    rw [hread₀, hread₁]
    field_simp [ne_of_gt hbpos]
    ring
  have hinv₂ : (r + h * m₀ - m₂) / (2 * b) = y := by
    rw [hread₀, hread₂]
    field_simp [ne_of_gt hbpos]
    ring
  refine ⟨hP, hPsq, hQ, hQsq, hVunit, hρ, hρtrace,
    hread₀, hread₁, hread₂, hinv₁, hinv₂, ?_, ?_⟩
  intro ε η₀ η₁ η₂ hε hη₀ hη₁ hη₂ n₀ n₁ n₂ pHat xHat yHat rhoHat
    radius scale projP projX projY rhoProj
  have hn₀ : n₀ = p + η₀ := by dsimp only [n₀]; rw [hread₀]
  have hn₁ : n₁ = r + h * p + 2 * b * x + η₁ := by
    dsimp only [n₁]; rw [hread₁]
  have hn₂ : n₂ = r + h * p - 2 * b * y + η₂ := by
    dsimp only [n₂]; rw [hread₂]
  have hcancel (d a t : ℝ) (hd : d ≠ 0) : (a + d * t) / d - t = a / d := by
    field_simp [hd]
    ring
  have hnumX (R H B P X E₀ E₁ : ℝ) :
      R + H * P + 2 * B * X + E₁ - R - H * (P + E₀) =
        (E₁ - H * E₀) + (2 * B) * X := by ring
  have hnumY (R H B P Y E₀ E₂ : ℝ) :
      R + H * (P + E₀) - (R + H * P - 2 * B * Y + E₂) =
        (H * E₀ - E₂) + (2 * B) * Y := by ring
  have hpHat : pHat - p = η₀ := by
    change n₀ - p = η₀
    rw [hn₀]
    ring
  have hxHat : xHat - x = (η₁ - h * η₀) / (2 * b) := by
    change (n₁ - r - h * n₀) / (2 * b) - x = _
    rw [hn₀, hn₁]
    calc
      (r + h * p + 2 * b * x + η₁ - r - h * (p + η₀)) / (2 * b) - x =
          ((η₁ - h * η₀) + (2 * b) * x) / (2 * b) - x :=
            congrArg (fun t : ℝ => t / (2 * b) - x) (hnumX r h b p x η₀ η₁)
      _ = (η₁ - h * η₀) / (2 * b) := hcancel (2 * b) _ _ (by positivity)
  have hyHat : yHat - y = (h * η₀ - η₂) / (2 * b) := by
    change (r + h * n₀ - n₂) / (2 * b) - y = _
    rw [hn₀, hn₂]
    calc
      (r + h * (p + η₀) - (r + h * p - 2 * b * y + η₂)) / (2 * b) - y =
          ((h * η₀ - η₂) + (2 * b) * y) / (2 * b) - y :=
            congrArg (fun t : ℝ => t / (2 * b) - y) (hnumY r h b p y η₀ η₂)
      _ = (h * η₀ - η₂) / (2 * b) := hcancel (2 * b) _ _ (by positivity)
  have hHerm : rhoHat.IsHermitian := by
    simpa only [rhoHat] using hherm pHat xHat yHat
  have htrace : Matrix.trace rhoHat = 1 := by
    apply Complex.ext <;> simp [rhoHat, Matrix.trace_fin_two] <;> ring
  have hdiff : rhoHat - ρ =
      ((!![⟨pHat - p, 0⟩, ⟨xHat - x, yHat - y⟩;
          ⟨xHat - x, -(yHat - y)⟩, ⟨-(pHat - p), 0⟩]) :
        Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> simp [rhoHat, ρ] <;> ring
  have hrawNorm : traceNorm (rhoHat - ρ) / 2 =
      Real.sqrt ((pHat - p) ^ 2 + (xHat - x) ^ 2 +
        (yHat - y) ^ 2) := by
    rw [hdiff, htn]
    ring
  have hraw : traceNorm (rhoHat - ρ) / 2 ≤
      Real.sqrt (1 + 2 * φ) * ε := by
    rw [hrawNorm, hpHat, hxHat, hyHat]
    exact hnoise ε η₀ η₁ η₂ hε hη₀ hη₁ hη₂
  have htrueBall : (p - 1 / 2) ^ 2 + x ^ 2 + y ^ 2 ≤ 1 / 4 := by
    nlinarith [hxy]
  have hproj := hproject (p - 1 / 2) x y (pHat - 1 / 2) xHat yHat htrueBall
  have hpcenter : projP - 1 / 2 = scale * (pHat - 1 / 2) := by
    dsimp only [projP]
    ring
  have hprojBall : (projP - 1 / 2) ^ 2 + projX ^ 2 + projY ^ 2 ≤ 1 / 4 := by
    rw [hpcenter]
    exact hproj.1
  have hpProj0 : 0 ≤ projP := by
    nlinarith [hprojBall, sq_nonneg projX, sq_nonneg projY]
  have hpProj1 : projP ≤ 1 := by
    nlinarith [hprojBall, sq_nonneg projX, sq_nonneg projY]
  have hballToDomain (a u v : ℝ)
      (hball : (a - 1 / 2) ^ 2 + u ^ 2 + v ^ 2 ≤ 1 / 4) :
      u ^ 2 + v ^ 2 ≤ a * (1 - a) := by
    nlinarith only [hball]
  have hprojDomain : projX ^ 2 + projY ^ 2 ≤ projP * (1 - projP) := by
    exact hballToDomain projP projX projY hprojBall
  have hprojPSD : rhoProj.PosSemidef := by
    simpa only [rhoProj] using
      hphysical projP projX projY hpProj0 hpProj1 hprojDomain
  have hprojTrace : Matrix.trace rhoProj = 1 := by
    apply Complex.ext <;> simp [rhoProj, Matrix.trace_fin_two] <;> ring
  have hprojDiff : rhoProj - ρ =
      ((!![⟨projP - p, 0⟩, ⟨projX - x, projY - y⟩;
          ⟨projX - x, -(projY - y)⟩, ⟨-(projP - p), 0⟩]) :
        Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> simp [rhoProj, ρ] <;> ring
  have hprojNorm : traceNorm (rhoProj - ρ) / 2 =
      Real.sqrt ((projP - p) ^ 2 + (projX - x) ^ 2 +
        (projY - y) ^ 2) := by
    rw [hprojDiff, htn]
    ring
  have hdist : Real.sqrt ((projP - p) ^ 2 + (projX - x) ^ 2 +
      (projY - y) ^ 2) ≤
      Real.sqrt ((pHat - p) ^ 2 + (xHat - x) ^ 2 +
        (yHat - y) ^ 2) := by
    have hpc : projP - p = scale * (pHat - 1 / 2) - (p - 1 / 2) := by
      rw [← hpcenter]
      ring
    have hrc : pHat - p = (pHat - 1 / 2) - (p - 1 / 2) := by ring
    rw [hpc, hrc]
    exact hproj.2
  refine ⟨hHerm, htrace, hraw, hprojPSD, hprojTrace, ?_⟩
  rw [hprojNorm, hrawNorm]
  exact hdist
  intro ε hε hsmall rho₀ n pHat xHat yHat rhoHat
  let K : ℝ := Real.sqrt (1 + 2 * φ)
  have hKpos : 0 < K := Real.sqrt_pos.mpr (by dsimp [φ]; positivity)
  have hKsq : K ^ 2 = 1 + 2 * φ := Real.sq_sqrt (by dsimp [φ]; positivity)
  have hφsq : (Real.sqrt φ) ^ 2 = φ := Real.sq_sqrt Real.goldenRatio_pos.le
  have hKeps : K * ε ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * K)).mp hsmall
    nlinarith
  have hKge : 1 ≤ K := by nlinarith [Real.goldenRatio_pos]
  have hεhalf : ε ≤ 1 / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hKge) hε.le]
  have hcenter : r + h / 2 = 1 / 2 := by rw [hh]; ring
  have hread₀₀ : (Matrix.trace (P * rho₀)).re = 1 / 2 := by
    simp [P, rho₀, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re]
  have hρ₀ : rho₀.PosSemidef := by
    convert hphysical (1 / 2) 0 0 (by norm_num)
      (by norm_num) (by norm_num) using 1
    ext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> norm_num [rho₀]
  have hρ₀trace : Matrix.trace rho₀ = 1 := by
    apply Complex.ext <;> simp [rho₀, Matrix.trace_fin_two] <;> ring
  have hread₁₀ : (Matrix.trace (Q * rho₀)).re = 1 / 2 := by
    simp [Q, rho₀, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re]
    nlinarith only [hrquad]
  have hread₂₀ : (Matrix.trace (Q * V * rho₀ * Vᴴ)).re = 1 / 2 := by
    simp [Q, V, rho₀, Matrix.trace_fin_two, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im]
    nlinarith only [hrquad]
  have hn : 0 ≤ n ∧ n ≤ 1 := by
    dsimp [n]
    constructor <;> linarith [hε.le, hεhalf]
  have hx : xHat = Real.sqrt φ * ε := by
    have hnum : n - r - h * n = (1 - h) * ε := by
      dsimp [n]
      linear_combination -hcenter
    change (n - r - h * n) / (2 * b) = _
    rw [hnum]
    calc
      ((1 - h) * ε) / (2 * b) = ((1 - h) / (2 * b)) * ε := by ring
      _ = _ := by rw [hcoeff]
  have hy : yHat = -(Real.sqrt φ * ε) := by
    have hnum : r + h * n - n = -(1 - h) * ε := by
      dsimp [n]
      linear_combination hcenter
    change (r + h * n - n) / (2 * b) = _
    rw [hnum]
    calc
      (-(1 - h) * ε) / (2 * b) = -(((1 - h) / (2 * b)) * ε) := by ring
      _ = _ := by rw [hcoeff]
  have hpHat : pHat = 1 / 2 + ε := rfl
  have hball : (Real.sqrt φ * ε) ^ 2 + (-(Real.sqrt φ * ε)) ^ 2 ≤
      (1 / 2 + ε) * (1 - (1 / 2 + ε)) := by
    have hsquare : (K * ε) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by norm_num)).mpr hKeps
    calc
      _ = (K * ε) ^ 2 - ε ^ 2 := by
        simp only [mul_pow, hKsq, hφsq, neg_sq]
        ring
      _ ≤ (1 / 2 : ℝ) ^ 2 - ε ^ 2 := sub_le_sub_right hsquare _
      _ = (1 / 2 + ε) * (1 - (1 / 2 + ε)) := by ring
  have hsharpPhysical : rhoHat.PosSemidef := by
    simpa only [rhoHat, hpHat, hx, hy] using
      hphysical (1 / 2 + ε) (Real.sqrt φ * ε) (-(Real.sqrt φ * ε))
        hn.1 hn.2 hball
  have hsharpDiff : rhoHat - rho₀ =
      ((!![⟨ε, 0⟩, ⟨Real.sqrt φ * ε, -(Real.sqrt φ * ε)⟩;
          ⟨Real.sqrt φ * ε, Real.sqrt φ * ε⟩, ⟨-ε, 0⟩]) :
        Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> simp [rhoHat, rho₀, hpHat, hx, hy] <;> ring
  have hsharpNorm : traceNorm (rhoHat - rho₀) / 2 = K * ε := by
    have htn₀ := htn ε (Real.sqrt φ * ε) (-(Real.sqrt φ * ε))
    simp only [neg_neg] at htn₀
    rw [hsharpDiff, htn₀]
    have hrad : ε ^ 2 + (Real.sqrt φ * ε) ^ 2 +
        (-(Real.sqrt φ * ε)) ^ 2 = (K * ε) ^ 2 := by
      simp only [mul_pow, hKsq, hφsq, neg_sq]
      ring
    rw [hrad, Real.sqrt_sq (mul_nonneg hKpos.le hε.le)]
    ring
  exact ⟨hρ₀, hρ₀trace, hread₀₀, hread₁₀, hread₂₀, hn.1, hn.2,
    hsharpPhysical, hsharpNorm⟩

end D5.S3.Quantum.Tomography.ActualThreeSettingRecovery
