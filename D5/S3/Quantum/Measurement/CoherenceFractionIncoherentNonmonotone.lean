/- GID: D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.claim; result=D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.result; claim=D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.claim
   digest: An incoherent operation increases the quantum coherence fraction. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Foundation.FiniteKrausChannel

/-! # Incoherent operations can increase the quantum coherence fraction

The coherence fraction is optimized over all vectors with unit-modulus coordinates.
A rank-two projection in dimension four gives a strict increase under a diagonal Kraus channel.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Set
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone

def IsIncoherentOperation {d m : ℕ}
    (k : Fin m → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∑ i, (k i)ᴴ * k i = 1) ∧
    ∀ i ρ, ρ.IsDiag → (k i * ρ * (k i)ᴴ).IsDiag

noncomputable def coherenceFraction {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ z : Fin d → ℂ, (∀ j, ‖z j‖ = 1) ∧
    r = (star z ⬝ᵥ (ρ *ᵥ z)).re / (d : ℝ)}

def claim : Prop := ∀ (d m : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (k : Fin m → Matrix (Fin d) (Fin d) ℂ),
    D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity ρ →
    IsIncoherentOperation k →
    coherenceFraction (∑ i, k i * ρ * (k i)ᴴ) ≤ coherenceFraction ρ

private def p : Matrix (Fin 4) (Fin 4) ℂ :=
  ![ ![(475 : ℂ) / 721, (-100 : ℂ) / 721 - (100 : ℂ) * Complex.I / 721,
      (205 : ℂ) / 721 - (80 : ℂ) * Complex.I / 721,
      (205 : ℂ) / 721 + (80 : ℂ) * Complex.I / 721],
    ![(-100 : ℂ) / 721 + (100 : ℂ) * Complex.I / 721, (1075 : ℂ) / 2163,
      (680 : ℂ) / 2163 + (60 : ℂ) * Complex.I / 721,
      (-60 : ℂ) / 721 - (680 : ℂ) * Complex.I / 2163],
    ![(205 : ℂ) / 721 + (80 : ℂ) * Complex.I / 721,
      (680 : ℂ) / 2163 - (60 : ℂ) * Complex.I / 721, (913 : ℂ) / 2163,
      (75 : ℂ) / 721 - (400 : ℂ) * Complex.I / 2163],
    ![(205 : ℂ) / 721 - (80 : ℂ) * Complex.I / 721,
      (-60 : ℂ) / 721 + (680 : ℂ) * Complex.I / 2163,
      (75 : ℂ) / 721 + (400 : ℂ) * Complex.I / 2163, (913 : ℂ) / 2163]]

private def rho : Matrix (Fin 4) (Fin 4) ℂ :=
  ![ ![(475 : ℂ) / 1442, (-50 : ℂ) / 721 - (50 : ℂ) * Complex.I / 721,
      (205 : ℂ) / 1442 - (40 : ℂ) * Complex.I / 721,
      (205 : ℂ) / 1442 + (40 : ℂ) * Complex.I / 721],
    ![(-50 : ℂ) / 721 + (50 : ℂ) * Complex.I / 721, (1075 : ℂ) / 4326,
      (340 : ℂ) / 2163 + (30 : ℂ) * Complex.I / 721,
      (-30 : ℂ) / 721 - (340 : ℂ) * Complex.I / 2163],
    ![(205 : ℂ) / 1442 + (40 : ℂ) * Complex.I / 721,
      (340 : ℂ) / 2163 - (30 : ℂ) * Complex.I / 721, (913 : ℂ) / 4326,
      (75 : ℂ) / 1442 - (200 : ℂ) * Complex.I / 2163],
    ![(205 : ℂ) / 1442 - (40 : ℂ) * Complex.I / 721,
      (-30 : ℂ) / 721 + (340 : ℂ) * Complex.I / 2163,
      (75 : ℂ) / 1442 + (200 : ℂ) * Complex.I / 2163, (913 : ℂ) / 4326]]

private def k : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![Matrix.diagonal ![1, 0, (3 : ℂ) / 5, (3 : ℂ) / 5],
    Matrix.diagonal ![0, 1, (4 : ℂ) / 5, (-4 : ℂ) * Complex.I / 5]]

private lemma p_star : pᴴ = p := by
  ext i j
  change star (p j i) = p i j
  fin_cases i <;> fin_cases j <;> delta p <;> simp <;> ring

private lemma p_square : p * p = p := by
  ext i j
  change (∑ t, p i t * p t j) = p i j
  fin_cases i <;> fin_cases j <;> delta p <;>
    simp [Fin.sum_univ_succ] <;> ring_nf <;>
      try rw [Complex.I_sq] <;> norm_num <;> ring

private lemma p_trace : trace p = 2 := by
  change ∑ i, p i i = 2
  delta p
  norm_num [Fin.sum_univ_succ]

private lemma p_pos : p.PosSemidef :=
  (show IsStarProjection p from ⟨p_square, p_star⟩).nonneg.posSemidef

private lemma rho_half : rho = (1 / 2 : ℝ) • p := by
  have hs (i j : Fin 4) : ((1 / 2 : ℝ) • p) i j = (1 / 2 : ℂ) * p i j := by
    change (1 / 2 : ℝ) • p i j = _
    rw [Algebra.smul_def]
    norm_num
  ext i j
  rw [hs]
  fin_cases i <;> fin_cases j <;> delta rho p <;>
    simp [Complex.ext_iff, div_eq_mul_inv] <;>
    norm_num <;> ring

private lemma rho_density :
    D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity rho := by
  rw [rho_half]
  constructor
  · simpa using p_pos.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · simp [Matrix.trace_smul, p_trace]

private lemma k_incoherent : IsIncoherentOperation k := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> delta k <;>
      simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        Fin.sum_univ_two, map_inv₀, map_ofNat, Complex.I_sq] <;>
      norm_num [Complex.ext_iff, Complex.I_sq, div_eq_mul_inv] <;> ring
  · intro i σ hσ
    rw [← hσ.diagonal_diag]
    fin_cases i <;> delta k <;>
      simp [Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose]

private lemma coherence_bddAbove (σ : Matrix (Fin 4) (Fin 4) ℂ) :
    BddAbove {r : ℝ | ∃ z : Fin 4 → ℂ, (∀ j, ‖z j‖ = 1) ∧
      r = (star z ⬝ᵥ (σ *ᵥ z)).re / (4 : ℝ)} := by
  let c : ℝ := ∑ i, ∑ j, ‖σ i j‖
  refine ⟨c, ?_⟩
  rintro r ⟨z, hz, rfl⟩
  have hnorm : ‖star z ⬝ᵥ (σ *ᵥ z)‖ ≤ c := by
    calc
      ‖star z ⬝ᵥ (σ *ᵥ z)‖ ≤ ∑ i, ‖star z i * (σ *ᵥ z) i‖ := by
        simpa [dotProduct] using (norm_sum_le (Finset.univ : Finset (Fin 4))
          (fun i => star z i * (σ *ᵥ z) i))
      _ = ∑ i, ‖(σ *ᵥ z) i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Pi.star_apply, norm_star, hz i]
      _ ≤ ∑ i, ∑ j, ‖σ i j * z j‖ := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Matrix.mulVec, dotProduct] using
          (norm_sum_le (Finset.univ : Finset (Fin 4))
            (fun j => σ i j * z j))
      _ = c := by
        simp [c, norm_mul, hz]
  have hre : (star z ⬝ᵥ (σ *ᵥ z)).re ≤ ‖star z ⬝ᵥ (σ *ᵥ z)‖ :=
    Complex.re_le_norm _
  have hc : 0 ≤ c := by
    exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => norm_nonneg _))
  nlinarith

private def q : Matrix (Fin 4) (Fin 4) ℂ :=
  ![ ![(1 / 2 : ℂ) * (475 / 721), 0,
      (3 / 10 : ℂ) * (205 / 721 - (80 : ℂ) * Complex.I / 721),
      (3 / 10 : ℂ) * (205 / 721 + (80 : ℂ) * Complex.I / 721)],
    ![0, (1 / 2 : ℂ) * (1075 / 2163),
      (2 / 5 : ℂ) * (680 / 2163 + (60 : ℂ) * Complex.I / 721),
      (2 / 5 : ℂ) * Complex.I * (-60 / 721 - (680 : ℂ) * Complex.I / 2163)],
    ![(3 / 10 : ℂ) * (205 / 721 + (80 : ℂ) * Complex.I / 721),
      (2 / 5 : ℂ) * (680 / 2163 - (60 : ℂ) * Complex.I / 721),
      (1 / 2 : ℂ) * (913 / 2163),
      (1 / 2 : ℂ) * ((9 / 25 : ℂ) + (16 / 25 : ℂ) * Complex.I) *
        (75 / 721 - (400 : ℂ) * Complex.I / 2163)],
    ![(3 / 10 : ℂ) * (205 / 721 - (80 : ℂ) * Complex.I / 721),
      -(2 / 5 : ℂ) * Complex.I * (-60 / 721 + (680 : ℂ) * Complex.I / 2163),
      (1 / 2 : ℂ) * ((9 / 25 : ℂ) - (16 / 25 : ℂ) * Complex.I) *
        (75 / 721 + (400 : ℂ) * Complex.I / 2163),
      (1 / 2 : ℂ) * (913 / 2163)]]

set_option maxHeartbeats 1000000 in
-- Both four-dimensional diagonal sandwiches require rational normalization.
private lemma phi_rho : MatrixMap.of_kraus k k rho = q := by
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_two, Matrix.add_apply] <;>
    delta k <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.diagonal_conjTranspose] <;>
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] <;>
    delta q rho <;>
    simp [Complex.ext_iff, div_eq_mul_inv] <;>
    norm_num <;> ring

private lemma output_at_ones :
    (star 1 ⬝ᵥ (MatrixMap.of_kraus k k rho *ᵥ 1)).re / (4 : ℝ) = 1 / 2 := by
  rw [phi_rho]
  delta q
  norm_num [Matrix.mulVec, Pi.star_apply, dotProduct, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, div_eq_mul_inv]

private lemma norm_defect (u w : ℂ) (hu : ‖u‖ ≤ 7 / 5) (hw : ‖w‖ = 1) :
    (‖u‖ ^ 2 - 1) ^ 2 ≤ 144 / 25 * ‖w - u‖ ^ 2 := by
  have hd : |‖u‖ - 1| ≤ ‖w - u‖ := by
    simpa [hw, norm_sub_rev] using abs_norm_sub_norm_le u w
  have hd2 : (‖u‖ - 1) ^ 2 ≤ ‖w - u‖ ^ 2 := by
    nlinarith [sq_abs (‖u‖ - 1), sq_le_sq₀ (abs_nonneg (‖u‖ - 1))
      (norm_nonneg (w - u)) |>.2 hd]
  have hs : (‖u‖ + 1) ^ 2 ≤ 144 / 25 := by nlinarith [norm_nonneg u]
  calc
    (‖u‖ ^ 2 - 1) ^ 2 = (‖u‖ - 1) ^ 2 * (‖u‖ + 1) ^ 2 := by ring
    _ ≤ ‖w - u‖ ^ 2 * (144 / 25) :=
      mul_le_mul hd2 hs (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

private lemma torus_defect (x y w t : ℂ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hw : ‖w‖ = 1) (ht : ‖t‖ = 1) :
    4 / 25 ≤ ‖w - (3 * x + 4 * y) / 5‖ ^ 2 +
      ‖t - (3 * x + 4 * Complex.I * y) / 5‖ ^ 2 := by
  let u := (3 * x + 4 * y) / 5
  let v := (3 * x + 4 * Complex.I * y) / 5
  have hu : ‖u‖ ≤ 7 / 5 := by
    calc
      ‖u‖ = ‖3 * x + 4 * y‖ / 5 := by simp [u, norm_div]
      _ ≤ (‖3 * x‖ + ‖4 * y‖) / 5 := div_le_div_of_nonneg_right
        (norm_add_le _ _) (by norm_num)
      _ = _ := by simp [norm_mul, hx, hy]; norm_num
  have hv : ‖v‖ ≤ 7 / 5 := by
    calc
      ‖v‖ = ‖3 * x + 4 * Complex.I * y‖ / 5 := by simp [v, norm_div]
      _ ≤ (‖3 * x‖ + ‖4 * Complex.I * y‖) / 5 := div_le_div_of_nonneg_right
        (norm_add_le _ _) (by norm_num)
      _ = _ := by simp [norm_mul, hx, hy]; norm_num
  have hsum : (‖u‖ ^ 2 - 1) ^ 2 + (‖v‖ ^ 2 - 1) ^ 2 = 576 / 625 := by
    have hx2 : x.re ^ 2 + x.im ^ 2 = 1 := by
      calc
        x.re ^ 2 + x.im ^ 2 = Complex.normSq x := by
          simp [Complex.normSq_apply]
          ring
        _ = ‖x‖ ^ 2 := (Complex.sq_norm x).symm
        _ = 1 := by rw [hx]; norm_num
    have hy2 : y.re ^ 2 + y.im ^ 2 = 1 := by
      calc
        y.re ^ 2 + y.im ^ 2 = Complex.normSq y := by
          simp [Complex.normSq_apply]
          ring
        _ = ‖y‖ ^ 2 := (Complex.sq_norm y).symm
        _ = 1 := by rw [hy]; norm_num
    have hu2 : ‖u‖ ^ 2 = 1 + 24 / 25 * (x.re * y.re + x.im * y.im) := by
      rw [Complex.sq_norm]
      simp [u, Complex.normSq_apply, div_eq_mul_inv]
      ring_nf
      nlinarith [hx2, hy2]
    have hv2 : ‖v‖ ^ 2 = 1 + 24 / 25 * (x.im * y.re - x.re * y.im) := by
      rw [Complex.sq_norm]
      simp [v, Complex.normSq_apply, div_eq_mul_inv]
      ring_nf
      nlinarith [hx2, hy2]
    have hxy : (x.re ^ 2 + x.im ^ 2) * (y.re ^ 2 + y.im ^ 2) = 1 := by
      rw [hx2, hy2]
      norm_num
    rw [hu2, hv2]
    nlinarith [hxy]
  have h₁ := norm_defect u w hu hw
  have h₂ := norm_defect v t hv ht
  change 4 / 25 ≤ ‖w - u‖ ^ 2 + ‖t - v‖ ^ 2
  nlinarith

private lemma residual_functional_bound (a b c d : ℂ) :
    ‖c - (3 * a + 4 * b) / 5‖ ^ 2 +
      ‖d - (3 * a + 4 * Complex.I * b) / 5‖ ^ 2 ≤
      4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h₁ : ‖c - (3 * a + 4 * b) / 5‖ ≤
      ‖c‖ + (3 * ‖a‖ + 4 * ‖b‖) / 5 := by
    calc
      ‖c - (3 * a + 4 * b) / 5‖ ≤ ‖c‖ + ‖(3 * a + 4 * b) / 5‖ := norm_sub_le _ _
      _ ≤ ‖c‖ + (3 * ‖a‖ + 4 * ‖b‖) / 5 := by
        norm_num only [norm_div, Complex.norm_ofNat]
        apply add_le_add_right
        apply div_le_div_of_nonneg_right
        · calc
            ‖3 * a + 4 * b‖ ≤ ‖3 * a‖ + ‖4 * b‖ := norm_add_le _ _
            _ = 3 * ‖a‖ + 4 * ‖b‖ := by simp
        · norm_num
  have h₂ : ‖d - (3 * a + 4 * Complex.I * b) / 5‖ ≤
      ‖d‖ + (3 * ‖a‖ + 4 * ‖b‖) / 5 := by
    calc
      ‖d - (3 * a + 4 * Complex.I * b) / 5‖ ≤
          ‖d‖ + ‖(3 * a + 4 * Complex.I * b) / 5‖ := norm_sub_le _ _
      _ ≤ ‖d‖ + (3 * ‖a‖ + 4 * ‖b‖) / 5 := by
        norm_num only [norm_div, Complex.norm_ofNat]
        apply add_le_add_right
        apply div_le_div_of_nonneg_right
        · calc
            ‖3 * a + 4 * Complex.I * b‖ ≤ ‖3 * a‖ + ‖4 * Complex.I * b‖ := norm_add_le _ _
            _ = 3 * ‖a‖ + 4 * ‖b‖ := by simp
        · norm_num
  have h₁s : ‖c - (3 * a + 4 * b) / 5‖ ^ 2 ≤
      (‖c‖ + (3 * ‖a‖ + 4 * ‖b‖) / 5) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 h₁
  have h₂s : ‖d - (3 * a + 4 * Complex.I * b) / 5‖ ^ 2 ≤
      (‖d‖ + (3 * ‖a‖ + 4 * ‖b‖) / 5) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 h₂
  have h₁c : (‖c‖ + (3 * ‖a‖ + 4 * ‖b‖) / 5) ^ 2 ≤
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (![‖c‖, ‖a‖, ‖b‖] : Fin 3 → ℝ) (![1, 3 / 5, 4 / 5] : Fin 3 → ℝ)
    norm_num [Fin.sum_univ_succ] at h
    nlinarith only [h]
  have h₂c : (‖d‖ + (3 * ‖a‖ + 4 * ‖b‖) / 5) ^ 2 ≤
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖d‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (![‖d‖, ‖a‖, ‖b‖] : Fin 3 → ℝ) (![1, 3 / 5, 4 / 5] : Fin 3 → ℝ)
    norm_num [Fin.sum_univ_succ] at h
    nlinarith only [h]
  nlinarith

private lemma projection_energy (z : Fin 4 → ℂ) :
    (star z ⬝ᵥ (p *ᵥ z)).re +
        ∑ i, ‖z i - (p *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  have hnorm := @norm_sub_sq ℂ (EuclideanSpace ℂ (Fin 4)) _ _ _
    (WithLp.toLp 2 z) (WithLp.toLp 2 (p *ᵥ z))
  simp only [EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_sub, Pi.sub_apply,
    dotProduct_comm (p *ᵥ z) (star z)] at hnorm
  have hp : star (p *ᵥ z) ⬝ᵥ (p *ᵥ z) = star z ⬝ᵥ (p *ᵥ z) := by
    rw [Matrix.star_mulVec, ← dotProduct_mulVec, p_star,
      Matrix.mulVec_mulVec, p_square]
  have hsq : ∑ i, ‖(p *ᵥ z) i‖ ^ 2 = (star z ⬝ᵥ (p *ᵥ z)).re := by
    rw [← hp]
    simp [dotProduct, Complex.re_sum, Complex.sq_norm, Complex.normSq_apply]
  rw [hsq] at hnorm
  change (∑ i, ‖z i - (p *ᵥ z) i‖ ^ 2) =
    (∑ i, ‖z i‖ ^ 2) - 2 * (star z ⬝ᵥ (p *ᵥ z)).re +
      (star z ⬝ᵥ (p *ᵥ z)).re at hnorm
  linarith

private lemma p_functionals (z : Fin 4 → ℂ) :
    ((p *ᵥ z) 2 - (3 * (p *ᵥ z) 0 + 4 * (p *ᵥ z) 1) / 5 = 0) ∧
      ((p *ᵥ z) 3 - (3 * (p *ᵥ z) 0 + 4 * Complex.I * (p *ᵥ z) 1) / 5 = 0) := by
  delta p
  constructor <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Complex.ext_iff,
      Complex.I_sq, div_eq_mul_inv] <;>
    norm_num <;> constructor <;> ring

private lemma defect_identities (z : Fin 4 → ℂ) :
    z 2 - (3 * z 0 + 4 * z 1) / 5 =
      ((z - p *ᵥ z) 2 - (3 * (z - p *ᵥ z) 0 + 4 * (z - p *ᵥ z) 1) / 5) ∧
    z 3 - (3 * z 0 + 4 * Complex.I * z 1) / 5 =
      ((z - p *ᵥ z) 3 -
        (3 * (z - p *ᵥ z) 0 + 4 * Complex.I * (z - p *ᵥ z) 1) / 5) := by
  rcases p_functionals z with ⟨h₁, h₂⟩
  constructor
  · calc
      z 2 - (3 * z 0 + 4 * z 1) / 5 =
          ((z - p *ᵥ z) 2 - (3 * (z - p *ᵥ z) 0 + 4 * (z - p *ᵥ z) 1) / 5) +
            ((p *ᵥ z) 2 - (3 * (p *ᵥ z) 0 + 4 * (p *ᵥ z) 1) / 5) := by
              simp only [Pi.sub_apply]
              ring
      _ = _ := by rw [h₁, add_zero]
  · calc
      z 3 - (3 * z 0 + 4 * Complex.I * z 1) / 5 =
          ((z - p *ᵥ z) 3 -
            (3 * (z - p *ᵥ z) 0 + 4 * Complex.I * (z - p *ᵥ z) 1) / 5) +
            ((p *ᵥ z) 3 -
              (3 * (p *ᵥ z) 0 + 4 * Complex.I * (p *ᵥ z) 1) / 5) := by
              simp only [Pi.sub_apply]
              ring
      _ = _ := by rw [h₂, add_zero]

private lemma input_bound (z : Fin 4 → ℂ) (hz : ∀ j, ‖z j‖ = 1) :
    (star z ⬝ᵥ (rho *ᵥ z)).re / (4 : ℝ) ≤ 1 / 2 - 1 / 200 := by
  have ht := torus_defect (z 0) (z 1) (z 2) (z 3) (hz 0) (hz 1) (hz 2) (hz 3)
  rcases defect_identities z with ⟨h₁, h₂⟩
  rw [h₁, h₂] at ht
  have hf := residual_functional_bound
    ((z - p *ᵥ z) 0) ((z - p *ᵥ z) 1) ((z - p *ᵥ z) 2) ((z - p *ᵥ z) 3)
  have he : 1 / 25 ≤ ∑ i, ‖z i - (p *ᵥ z) i‖ ^ 2 := by
    simp only [Pi.sub_apply] at ht hf
    norm_num [Fin.sum_univ_succ]
    linarith
  have hp := projection_energy z
  have hzsum : ∑ i, ‖z i‖ ^ 2 = 4 := by simp [hz]
  rw [hzsum] at hp
  have hr : (star z ⬝ᵥ (rho *ᵥ z)).re = (star z ⬝ᵥ (p *ᵥ z)).re / 2 := by
    rw [rho_half, Matrix.smul_mulVec, dotProduct_smul]
    simp [div_eq_mul_inv, mul_comm]
  rw [hr]
  linarith

private lemma output_lower : 1 / 2 ≤ coherenceFraction (MatrixMap.of_kraus k k rho) := by
  unfold coherenceFraction
  apply le_csSup (coherence_bddAbove (MatrixMap.of_kraus k k rho))
  refine ⟨1, ?_, output_at_ones.symm⟩
  intro j
  simp

private lemma input_upper : coherenceFraction rho ≤ 1 / 2 - 1 / 200 := by
  unfold coherenceFraction
  refine csSup_le ?_ ?_
  · exact ⟨_, 1, (by intro j; simp), rfl⟩
  rintro r ⟨z, hz, rfl⟩
  exact input_bound z hz

theorem result : ¬ claim := by
  intro h
  have hm := h 4 2 rho k rho_density k_incoherent
  have hlt : coherenceFraction (MatrixMap.of_kraus k k rho) > coherenceFraction rho :=
    lt_of_le_of_lt input_upper ?_
  · exact (not_lt_of_ge hm) hlt
  · exact lt_of_lt_of_le (by norm_num : (1 / 2 - 1 / 200 : ℝ) < 1 / 2) output_lower

end D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone
