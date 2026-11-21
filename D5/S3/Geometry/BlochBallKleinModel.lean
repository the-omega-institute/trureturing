/- GID: D5/S3/Geometry/BlochBallKleinModel
   generality: I
   mirror-B: D5/B/S3/Geometry/BlochBallKleinModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Open Bloch ball as the Klein model of hyperbolic three-space; filters are isometries. -/

import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.Information.ActualQubitChordObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace Matrix ComplexOrder
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (blochMatrix bloch blochMatrix_trace
  bloch_blochMatrix bloch_geometry_of_isHermitian)
open D5.S3.Quantum.Information.ActualQubitChordObstruction (det_bloch)
open D5.S3.Geometry.Hyperideal.LengthGramBody (lorentz)
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments (lift lift_unit lift_cosh lift_injective
  lift_of_coordinates lift_time project)
open D5.S3.Geometry.HyperbolicUpperHalfSpace (HyperbolicThreeSpace)

noncomputable section

namespace D5.S3.Geometry.BlochBallKleinModel

/-- The right-hand side of the Klein distance formula on the open Bloch ball:
`cosh d(r, s) = (1 - ⟪r, s⟫) / √((1 - ‖r‖²) (1 - ‖s‖²))`. -/
def kleinCosh (r s : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 - ⟪r, s⟫_ℝ) / √((1 - ‖r‖ ^ 2) * (1 - ‖s‖ ^ 2))

/-- The filter `ρ ↦ g ρ gᴴ / Tr (g ρ gᴴ)` written on Bloch vectors. -/
def filter (g : Matrix (Fin 2) (Fin 2) ℂ) (r : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  (Matrix.trace (g * blochMatrix 1 r * gᴴ)).re⁻¹ • bloch (g * blochMatrix 1 r * gᴴ)

private def normalizeBloch (M : Matrix (Fin 2) (Fin 2) ℂ) : EuclideanSpace ℝ (Fin 3) :=
  (Matrix.trace M).re⁻¹ • bloch M

private theorem bloch_smul (c : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    bloch ((c : ℂ) • M) = c • bloch M := by
  ext i
  fin_cases i <;> simp [bloch] <;> ring

private theorem normalize_smul (c : ℝ) (hc : c ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    normalizeBloch ((c : ℂ) • M) = normalizeBloch M := by
  unfold normalizeBloch
  rw [bloch_smul, Matrix.trace_smul, smul_smul]
  congr 1
  simp only [smul_eq_mul, Complex.re_ofReal_mul]
  rcases eq_or_ne (Matrix.trace M).re 0 with h | h
  · simp [h]
  · field_simp

private theorem normalize_blochMatrix (r : EuclideanSpace ℝ (Fin 3)) :
    normalizeBloch (blochMatrix 1 r) = r := by
  simp [normalizeBloch, blochMatrix_trace, bloch_blochMatrix]

private theorem blochMatrix_smul (c a : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    blochMatrix (c * a) (c • v) = (c : ℂ) • blochMatrix a v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochMatrix] <;> ring

private theorem blochMatrix_normalize (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian)
    (h : (Matrix.trace M).re ≠ 0) :
    blochMatrix 1 (normalizeBloch M) = (((Matrix.trace M).re⁻¹ : ℝ) : ℂ) • M := by
  have e := (bloch_geometry_of_isHermitian M hM).1
  calc blochMatrix 1 (normalizeBloch M)
      = blochMatrix ((Matrix.trace M).re⁻¹ * (Matrix.trace M).re)
          ((Matrix.trace M).re⁻¹ • bloch M) := by rw [inv_mul_cancel₀ h]; rfl
    _ = (((Matrix.trace M).re⁻¹ : ℝ) : ℂ) • blochMatrix (Matrix.trace M).re (bloch M) :=
        blochMatrix_smul _ _ _
    _ = _ := by rw [← e]

private theorem conjTranspose_blochMatrix (a : ℝ) (r : EuclideanSpace ℝ (Fin 3)) :
    (blochMatrix a r)ᴴ = blochMatrix a r := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochMatrix]

/-- The polarized determinant of two Bloch matrices of trace one. -/
private theorem trace_mul_adjugate (r s : EuclideanSpace ℝ (Fin 3)) :
    Matrix.trace (blochMatrix 1 r * Matrix.adjugate (blochMatrix 1 s)) =
      (((1 - ⟪r, s⟫_ℝ) / 2 : ℝ) : ℂ) := by
  rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]
  apply Complex.ext <;>
    simp [blochMatrix, Matrix.adjugate_fin_two, Matrix.trace_fin_two, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- Covariance of the polarized determinant: `tr (X adj Y)` is multiplied by `|det g|²` under
`X ↦ g X gᴴ`, `Y ↦ g Y gᴴ`. -/
private theorem trace_conj_mul_adjugate (g X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (g * X * gᴴ * Matrix.adjugate (g * Y * gᴴ)) =
      (g.det * star g.det) * Matrix.trace (X * Matrix.adjugate Y) := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
  have h1 : g * X * gᴴ * (Matrix.adjugate gᴴ * (Matrix.adjugate Y * Matrix.adjugate g)) =
      star g.det • (g * (X * Matrix.adjugate Y) * Matrix.adjugate g) := by
    rw [show g * X * gᴴ * (Matrix.adjugate gᴴ * (Matrix.adjugate Y * Matrix.adjugate g)) =
      g * X * (gᴴ * Matrix.adjugate gᴴ) * (Matrix.adjugate Y * Matrix.adjugate g) by
        simp only [Matrix.mul_assoc], Matrix.mul_adjugate, Matrix.det_conjTranspose]
    simp [Matrix.mul_assoc]
  rw [h1, Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.adjugate_mul]
  simp [Matrix.trace_smul, smul_eq_mul]
  ring

private theorem det_blochMatrix (a : ℝ) (r : EuclideanSpace ℝ (Fin 3)) :
    (blochMatrix a r).det = (((a ^ 2 - ‖r‖ ^ 2) / 4 : ℝ) : ℂ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Complex.ext <;>
    simp [blochMatrix, Matrix.det_fin_two, Fin.sum_univ_three, pow_two] <;> ring

/-- `blochMatrix (a + 2δ) r` is a square root of `(a + 2δ) • blochMatrix a r` when
`4 δ² = a² - ‖r‖²`. -/
private theorem blochMatrix_sq (a δ : ℝ) (r : EuclideanSpace ℝ (Fin 3))
    (hδ : 4 * δ ^ 2 = a ^ 2 - ‖r‖ ^ 2) :
    blochMatrix (a + 2 * δ) r * blochMatrix (a + 2 * δ) r =
      (((a + 2 * δ) : ℝ) : ℂ) • blochMatrix a r := by
  rw [EuclideanSpace.real_norm_sq_eq] at hδ
  simp only [Fin.sum_univ_three] at hδ
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [blochMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (-1/4 : ℝ) * hδ | linear_combination (1/4 : ℝ) * hδ

private theorem posSemidef_blochMatrix (a : ℝ) (r : EuclideanSpace ℝ (Fin 3)) (ha : 0 < a)
    (h : ‖r‖ ≤ a) : (blochMatrix a r).PosSemidef := by
  set δ := √(a ^ 2 - ‖r‖ ^ 2) / 2
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : 4 * δ ^ 2 = a ^ 2 - ‖r‖ ^ 2 := by
    simp only [δ, div_pow, Real.sq_sqrt (by nlinarith [norm_nonneg r] : 0 ≤ a ^ 2 - ‖r‖ ^ 2)]
    ring
  have hb : 0 < a + 2 * δ := by linarith
  have hps : (blochMatrix (a + 2 * δ) r * blochMatrix (a + 2 * δ) r).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (blochMatrix (a + 2 * δ) r)
    rwa [conjTranspose_blochMatrix] at this
  rw [blochMatrix_sq a δ r hδ] at hps
  have := hps.smul (a := (((a + 2 * δ)⁻¹ : ℝ) : ℂ))
    (by exact_mod_cast (inv_pos.mpr hb).le)
  rwa [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hb.ne', Complex.ofReal_one,
    one_smul] at this

private theorem posDef_blochMatrix (a : ℝ) (r : EuclideanSpace ℝ (Fin 3)) (h : ‖r‖ < a) :
    (blochMatrix a r).PosDef := by
  rw [(posSemidef_blochMatrix a r ((norm_nonneg r).trans_lt h) h.le).posDef_iff_det_ne_zero,
    det_blochMatrix]
  have : 0 < a ^ 2 - ‖r‖ ^ 2 := by nlinarith [norm_nonneg r]
  exact_mod_cast (by positivity : (a ^ 2 - ‖r‖ ^ 2) / 4 ≠ 0)

private theorem filter_eq (g : Matrix (Fin 2) (Fin 2) ℂ) (r : EuclideanSpace ℝ (Fin 3)) :
    filter g r = normalizeBloch (g * blochMatrix 1 r * gᴴ) := rfl

private theorem posDef_conj (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0)
    (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ < 1) :
    (g * blochMatrix 1 r * gᴴ).PosDef :=
  (posDef_blochMatrix 1 r hr).mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det g).mpr hg.isUnit))

private theorem trace_re_pos {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M.PosDef) :
    0 < (Matrix.trace M).re :=
  (Complex.pos_iff.mp hM.trace_pos).1

private theorem posSemidef_conj (g : Matrix (Fin 2) (Fin 2) ℂ) (r : EuclideanSpace ℝ (Fin 3))
    (hr : ‖r‖ ≤ 1) : (g * blochMatrix 1 r * gᴴ).PosSemidef :=
  (posSemidef_blochMatrix 1 r one_pos hr).mul_mul_conjTranspose_same g

/-- On the closed ball the trace of `g ρ gᴴ` has nonzero real part for invertible `g`: the matrix
is positive semidefinite, and it is nonzero because `ρ` has trace one. -/
private theorem trace_conj_re_ne_zero (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0)
    (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ ≤ 1) :
    (Matrix.trace (g * blochMatrix 1 r * gᴴ)).re ≠ 0 := by
  have hps := posSemidef_conj g r hr
  intro h0
  have htr : Matrix.trace (g * blochMatrix 1 r * gᴴ) = 0 :=
    Complex.ext h0 (Complex.nonneg_iff.mp hps.trace_nonneg).2.symm
  have hM := hps.trace_eq_zero_iff.1 htr
  have hgH : IsUnit gᴴ.det := by rw [Matrix.det_conjTranspose]; exact hg.isUnit.star
  have hX : blochMatrix 1 r = g⁻¹ * (g * blochMatrix 1 r * gᴴ) * gᴴ⁻¹ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg.isUnit,
      Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hgH, Matrix.mul_one]
  rw [hM, Matrix.mul_zero, Matrix.zero_mul] at hX
  have h1 := blochMatrix_trace 1 r
  rw [hX, Matrix.trace_zero] at h1
  simp at h1

private theorem blochMatrix_filter (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0)
    (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ ≤ 1) :
    blochMatrix 1 (filter g r) =
      (((Matrix.trace (g * blochMatrix 1 r * gᴴ)).re⁻¹ : ℝ) : ℂ) • (g * blochMatrix 1 r * gᴴ) :=
  blochMatrix_normalize _ (posSemidef_conj g r hr).isHermitian (trace_conj_re_ne_zero g hg r hr)

/-- Composition of filters on the closed ball. -/
private theorem filter_mul (g h : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0)
    (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ ≤ 1) :
    filter h (filter g r) = filter (h * g) r := by
  rw [filter_eq h, blochMatrix_filter g hg r hr, filter_eq, Matrix.conjTranspose_mul]
  rw [Matrix.mul_smul, Matrix.smul_mul,
    normalize_smul _ (inv_ne_zero (trace_conj_re_ne_zero g hg r hr))]
  simp only [Matrix.mul_assoc]

private theorem filter_one (r : EuclideanSpace ℝ (Fin 3)) : filter 1 r = r := by
  rw [filter_eq]; simpa using normalize_blochMatrix r

private theorem norm_filter_lt (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0)
    (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ < 1) : ‖filter g r‖ < 1 := by
  have hpos : (blochMatrix 1 (filter g r)).PosDef := by
    rw [blochMatrix_filter g hg r hr.le]
    exact (posDef_conj g hg r hr).smul (by
      exact_mod_cast (inv_pos.mpr (trace_re_pos (posDef_conj g hg r hr))))
  have hd := hpos.det_pos
  rw [det_bloch] at hd
  have : 0 < (1 - ‖filter g r‖ ^ 2) / 4 := by exact_mod_cast hd
  nlinarith [norm_nonneg (filter g r)]

private theorem pairing (r s : EuclideanSpace ℝ (Fin 3)) :
    (1 - ⟪r, s⟫_ℝ) =
      2 * (Matrix.trace (blochMatrix 1 r * Matrix.adjugate (blochMatrix 1 s))).re := by
  rw [trace_mul_adjugate, Complex.ofReal_re]; ring

private theorem pairing_filter (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0)
    (r s : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) :
    1 - ⟪filter g r, filter g s⟫_ℝ =
      ((Matrix.trace (g * blochMatrix 1 r * gᴴ)).re⁻¹ *
        (Matrix.trace (g * blochMatrix 1 s * gᴴ)).re⁻¹ * Complex.normSq g.det) *
        (1 - ⟪r, s⟫_ℝ) := by
  rw [pairing, pairing r s, blochMatrix_filter g hg r hr.le, blochMatrix_filter g hg s hs.le,
    Matrix.adjugate_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
    trace_conj_mul_adjugate, trace_mul_adjugate]
  have hd : g.det * star g.det = (Complex.normSq g.det : ℂ) := Complex.mul_conj g.det
  rw [hd]
  simp only [Fintype.card_fin, Nat.add_one_sub_one, pow_one, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
  ring

private theorem klein_scale (A B C l m D : ℝ) (hl : 0 < l) (hm : 0 < m) (hD : 0 < D) :
    (l * m * D * A) / √((l * l * D * B) * (m * m * D * C)) = A / √(B * C) := by
  have : (l * l * D * B) * (m * m * D * C) = (l * m * D) ^ 2 * (B * C) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    mul_div_mul_left _ _ (by positivity)]

private theorem kleinCosh_filter (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0)
    (r s : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) :
    kleinCosh (filter g r) (filter g s) = kleinCosh r s := by
  unfold kleinCosh
  have hsq (v : EuclideanSpace ℝ (Fin 3)) : ‖v‖ ^ 2 = ⟪v, v⟫_ℝ :=
    (real_inner_self_eq_norm_sq v).symm
  rw [hsq, hsq (filter g s), hsq r, hsq s, pairing_filter g hg r s hr hs,
    pairing_filter g hg r r hr hr, pairing_filter g hg s s hs hs]
  exact klein_scale _ _ _ _ _ _ (inv_pos.mpr (trace_re_pos (posDef_conj g hg r hr)))
    (inv_pos.mpr (trace_re_pos (posDef_conj g hg s hs)))
    (Complex.normSq_pos.mpr hg)

private theorem exists_posDef_det_one_filter (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ < 1) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℂ, g.PosDef ∧ g.det = 1 ∧ filter g 0 = r := by
  set δ := √(1 - ‖r‖ ^ 2) / 2
  have hδ0 : 0 ≤ δ := by positivity
  have hr2 : ‖r‖ ^ 2 < 1 := by nlinarith [norm_nonneg r]
  have hδ : 4 * δ ^ 2 = 1 ^ 2 - ‖r‖ ^ 2 := by
    simp only [δ, div_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - ‖r‖ ^ 2)]
    ring
  set M := blochMatrix (1 + 2 * δ) r
  set D := ((1 + 2 * δ) ^ 2 - ‖r‖ ^ 2) / 4
  have hD : 0 < D := by simp only [D]; nlinarith [hδ, hr2, hδ0]
  set c := (√D)⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hD)
  refine ⟨(c : ℂ) • M, (posDef_blochMatrix _ r (by linarith)).smul (by exact_mod_cast hc), ?_, ?_⟩
  · rw [Matrix.det_smul, det_blochMatrix, Fintype.card_fin, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul]
    have : c ^ 2 * D = 1 := by
      simp only [c, inv_pow, Real.sq_sqrt hD.le]; exact inv_mul_cancel₀ hD.ne'
    rw [this, Complex.ofReal_one]
  · have hconj : (c : ℂ) • M * blochMatrix 1 0 * ((c : ℂ) • M)ᴴ =
        ((c * c : ℝ) : ℂ) • (M * blochMatrix 1 0 * Mᴴ) := by
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.ofReal_mul]
    have h0 : blochMatrix 1 (0 : EuclideanSpace ℝ (Fin 3)) = (((1 / 2 : ℝ)) : ℂ) • 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [blochMatrix]
    rw [filter_eq, hconj, normalize_smul _ (by positivity), h0, conjTranspose_blochMatrix,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, blochMatrix_sq 1 δ r hδ, smul_smul,
      ← Complex.ofReal_mul, normalize_smul _ (by positivity), normalize_blochMatrix]

/-- The hyperboloid point `(r, 1) / √(1 - ‖r‖²)` of a Bloch vector. -/
private def kleinPoint (r : EuclideanSpace ℝ (Fin 3)) : Fin 4 → ℝ :=
  (√(1 - ‖r‖ ^ 2))⁻¹ • ![r 0, r 1, r 2, 1]

private theorem norm_sq_eq (r : EuclideanSpace ℝ (Fin 3)) :
    ‖r‖ ^ 2 = r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

private theorem inner_eq (r s : EuclideanSpace ℝ (Fin 3)) :
    ⟪r, s⟫_ℝ = r 0 * s 0 + r 1 * s 1 + r 2 * s 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private theorem lorentz_kleinPoint (r s : EuclideanSpace ℝ (Fin 3)) :
    lorentz (kleinPoint r) (kleinPoint s) =
      -((√(1 - ‖r‖ ^ 2))⁻¹ * (√(1 - ‖s‖ ^ 2))⁻¹ * (1 - ⟪r, s⟫_ℝ)) := by
  rw [inner_eq]
  simp [lorentz, kleinPoint, Fin.sum_univ_four]
  ring

private theorem lorentz_kleinPoint_self (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ < 1) :
    lorentz (kleinPoint r) (kleinPoint r) = -1 := by
  have h : 0 < 1 - ‖r‖ ^ 2 := by nlinarith [norm_nonneg r]
  rw [lorentz_kleinPoint, real_inner_self_eq_norm_sq, ← mul_inv, Real.mul_self_sqrt h.le,
    inv_mul_cancel₀ h.ne']

private theorem kleinPoint_time (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ < 1) :
    0 < kleinPoint r 3 := by
  have h : 0 < 1 - ‖r‖ ^ 2 := by nlinarith [norm_nonneg r]
  simpa [kleinPoint] using Real.sqrt_pos.mpr h

/-- The Klein chart of the open ball. -/
private def kleinChart (r : {r : EuclideanSpace ℝ (Fin 3) // ‖r‖ < 1}) : HyperbolicThreeSpace :=
  project (kleinPoint r) (lorentz_kleinPoint_self r r.2) (kleinPoint_time r r.2)

private theorem lift_kleinChart (r : {r : EuclideanSpace ℝ (Fin 3) // ‖r‖ < 1}) :
    lift (kleinChart r) = kleinPoint r :=
  lift_of_coordinates _ _ (lorentz_kleinPoint_self r r.2) (kleinPoint_time r r.2) rfl

/-- The spatial part of the hyperboloid lift divided by its time part. -/
private def kleinCoord (p : HyperbolicThreeSpace) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![lift p 0 / lift p 3, lift p 1 / lift p 3, lift p 2 / lift p 3]

private theorem one_sub_norm_kleinCoord (p : HyperbolicThreeSpace) :
    1 - ‖kleinCoord p‖ ^ 2 = (lift p 3 ^ 2)⁻¹ := by
  have hu := lift_unit p
  have ht := (lift_time p).ne'
  simp only [lorentz, Fin.sum_univ_four] at hu
  rw [norm_sq_eq]
  simp [kleinCoord]
  field_simp
  simp at hu
  linear_combination (-1 : ℝ) * hu

private theorem norm_kleinCoord_lt (p : HyperbolicThreeSpace) : ‖kleinCoord p‖ < 1 := by
  have h := one_sub_norm_kleinCoord p
  have : 0 < (lift p 3 ^ 2)⁻¹ := by have := lift_time p; positivity
  nlinarith [norm_nonneg (kleinCoord p)]

private theorem kleinPoint_kleinCoord (p : HyperbolicThreeSpace) :
    kleinPoint (kleinCoord p) = lift p := by
  have ht := lift_time p
  have hs : (√(1 - ‖kleinCoord p‖ ^ 2))⁻¹ = lift p 3 := by
    rw [one_sub_norm_kleinCoord, Real.sqrt_inv, Real.sqrt_sq ht.le, inv_inv]
  unfold kleinPoint
  rw [hs]
  ext k
  fin_cases k <;> simp [kleinCoord] <;> field_simp

private theorem kleinCoord_kleinChart (r : {r : EuclideanSpace ℝ (Fin 3) // ‖r‖ < 1}) :
    kleinCoord (kleinChart r) = r := by
  have h : 0 < √(1 - ‖(r : EuclideanSpace ℝ (Fin 3))‖ ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [norm_nonneg (r : EuclideanSpace ℝ (Fin 3)), r.2])
  ext k
  fin_cases k <;> simp [kleinCoord, lift_kleinChart, kleinPoint] <;> field_simp

private theorem exists_isometry :
    ∃ Φ : {r : EuclideanSpace ℝ (Fin 3) // ‖r‖ < 1} ≃ HyperbolicThreeSpace,
      ∀ r s, Real.cosh (dist (Φ r) (Φ s)) = kleinCosh r s := by
  refine ⟨⟨kleinChart, fun p => ⟨kleinCoord p, norm_kleinCoord_lt p⟩,
    fun r => Subtype.ext (kleinCoord_kleinChart r), fun p => ?_⟩, fun r s => ?_⟩
  · apply lift_injective
    rw [lift_kleinChart]
    exact kleinPoint_kleinCoord p
  · have hr : 0 < 1 - ‖(r : EuclideanSpace ℝ (Fin 3))‖ ^ 2 := by
      nlinarith [norm_nonneg (r : EuclideanSpace ℝ (Fin 3)), r.2]
    have hs : 0 < 1 - ‖(s : EuclideanSpace ℝ (Fin 3))‖ ^ 2 := by
      nlinarith [norm_nonneg (s : EuclideanSpace ℝ (Fin 3)), s.2]
    have h := lift_cosh (kleinChart r) (kleinChart s)
    simp only [Equiv.coe_fn_mk]
    rw [lift_kleinChart, lift_kleinChart, lorentz_kleinPoint] at h
    rw [kleinCosh, Real.sqrt_mul hr.le, div_eq_mul_inv, mul_inv]
    linarith

/-- The open Bloch ball is the Klein model of hyperbolic three-space: it is in bijection with the
upper half-space model `HyperbolicThreeSpace` so that `cosh` of the hyperbolic distance is
`kleinCosh`. The filter of the identity is the identity. Every invertible `g` maps the open ball
into itself; on the closed ball its filter composes with any further filter `h` as the filter of
`h * g`; and it preserves `kleinCosh` on the open ball. Every interior point is the image of the
centre under the filter of a positive definite matrix of determinant one. -/
theorem bloch_ball_hyperbolic :
    (∃ Φ : {r : EuclideanSpace ℝ (Fin 3) // ‖r‖ < 1} ≃ HyperbolicThreeSpace,
      ∀ r s, Real.cosh (dist (Φ r) (Φ s)) = kleinCosh r s) ∧
    (∀ r : EuclideanSpace ℝ (Fin 3), filter 1 r = r) ∧
    (∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.det ≠ 0 →
      (∀ r : EuclideanSpace ℝ (Fin 3), ‖r‖ < 1 → ‖filter g r‖ < 1) ∧
      (∀ r : EuclideanSpace ℝ (Fin 3), ‖r‖ ≤ 1 →
        ∀ h : Matrix (Fin 2) (Fin 2) ℂ, filter h (filter g r) = filter (h * g) r) ∧
      ∀ r s : EuclideanSpace ℝ (Fin 3), ‖r‖ < 1 → ‖s‖ < 1 →
        kleinCosh (filter g r) (filter g s) = kleinCosh r s) ∧
    ∀ r : EuclideanSpace ℝ (Fin 3), ‖r‖ < 1 →
      ∃ g : Matrix (Fin 2) (Fin 2) ℂ, g.PosDef ∧ g.det = 1 ∧ filter g 0 = r :=
  ⟨exists_isometry, filter_one, fun g hg =>
    ⟨norm_filter_lt g hg, fun r hr h => filter_mul g h hg r hr, kleinCosh_filter g hg⟩,
    exists_posDef_det_one_filter⟩

end D5.S3.Geometry.BlochBallKleinModel
