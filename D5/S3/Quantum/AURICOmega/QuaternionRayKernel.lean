/- GID: D5/S3/Quantum/AURICOmega/QuaternionRayKernel
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/QuaternionRayKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two-term squared quaternion reading factors through the Hopf map. -/

import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Observer.BornReduction

/-! The phase-blind ray kernel on the unit quaternions.

The reading `kappa x y = (1 + ⟪x, y⟫) / 2` of the quaternion comparison model separates a unit
quaternion from its antipode. Squaring `2 * kappa - 1` and adding the same square after a right
multiplication by `i` gives `⟪x, y⟫ ^ 2 + ⟪x, y * i⟫ ^ 2`. This two-term reading equals
`(1 + ⟪x i x⁻¹, y i y⁻¹⟫) / 2`, so it depends only on the Hopf images `x i x⁻¹` and `y i y⁻¹`. It
is unchanged by right multiplication by the phase circle spanned by `1` and `i`, and it equals one
exactly when the two unit quaternions differ by such a phase.

The real-linear isometry `a + b i + c j + d k ↦ (a + b I, -c + d I)` onto `ℂ²` turns right
multiplication by `i` into multiplication by the complex unit. Through it the Hopf image is the
Bloch vector of the rank-one projection onto the image vector, and the two-term reading is the
squared modulus of the complex transition amplitude, which is the trace pairing of the two
rank-one projections. -/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.QuaternionRayKernel

open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch)
open D5.S3.Quantum.FiniteDimensional (bornProbability)
open D5.S3.Observer.BornReduction (rank_one_pure_state_modulus_square_reduction)

/-- The Hopf image of a unit quaternion: the unit imaginary quaternion `x * i * x⁻¹`. -/
def hopf (x : unitary ℍ[ℝ]) : ℍ[ℝ] :=
  (x : ℍ[ℝ]) * (unitI : ℍ[ℝ]) * star (x : ℍ[ℝ])

/-- The two-term squared reading built from `kappa` and the chosen imaginary unit. -/
def rayKernel (x y : unitary ℍ[ℝ]) : ℝ :=
  (2 * quaternionModel.kappa x y - 1) ^ 2 + (2 * quaternionModel.kappa x (y * unitI) - 1) ^ 2

/-- A unit quaternion has squared norm one. -/
private lemma normSq_coe_unitary (x : unitary ℍ[ℝ]) : Quaternion.normSq (x : ℍ[ℝ]) = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, one_mul]

/-- The two-term reading is `⟪x, y⟫ ^ 2 + ⟪x, y * i⟫ ^ 2`. -/
private lemma rayKernel_eq_inner (x y : unitary ℍ[ℝ]) :
    rayKernel x y = ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ ^ 2 +
      ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ]) * (unitI : ℍ[ℝ])⟫_ℝ ^ 2 := by
  change (2 * ((1 + ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / 2) - 1) ^ 2 +
    (2 * ((1 + ⟪(x : ℍ[ℝ]), ((y * unitI : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / 2) - 1) ^ 2 = _
  rw [Submonoid.coe_mul]
  ring

/-- The homogeneous form of the Hopf identity on all quaternions:
`⟪p, q⟫ ^ 2 + ⟪p, q i⟫ ^ 2 = (|p| ^ 2 |q| ^ 2 + ⟪p i p*, q i q*⟫) / 2`. -/
private lemma inner_sq_add_inner_mul_sq (p q : ℍ[ℝ]) :
    ⟪p, q⟫_ℝ ^ 2 + ⟪p, q * (unitI : ℍ[ℝ])⟫_ℝ ^ 2 =
      (Quaternion.normSq p * Quaternion.normSq q +
        ⟪p * (unitI : ℍ[ℝ]) * star p, q * (unitI : ℍ[ℝ]) * star q⟫_ℝ) / 2 := by
  have hI : (unitI : ℍ[ℝ]) = ⟨0, 1, 0, 0⟩ := rfl
  rw [inner_eq_components, inner_eq_components, inner_eq_components, Quaternion.normSq_def',
    Quaternion.normSq_def', hI]
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- The components of `p* q` off the phase plane measure the defect of the two-term reading. -/
private lemma imJ_sq_add_imK_sq (p q : ℍ[ℝ]) :
    (star p * q).imJ ^ 2 + (star p * q).imK ^ 2 =
      Quaternion.normSq p * Quaternion.normSq q -
        (⟪p, q⟫_ℝ ^ 2 + ⟪p, q * (unitI : ℍ[ℝ])⟫_ℝ ^ 2) := by
  have hI : (unitI : ℍ[ℝ]) = ⟨0, 1, 0, 0⟩ := rfl
  rw [inner_eq_components, inner_eq_components, Quaternion.normSq_def', Quaternion.normSq_def', hI]
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- The two-term reading is the half-angle form of the inner product of the Hopf images. -/
theorem rayKernel_eq_hopf (x y : unitary ℍ[ℝ]) :
    rayKernel x y = (1 + ⟪hopf x, hopf y⟫_ℝ) / 2 := by
  rw [rayKernel_eq_inner, inner_sq_add_inner_mul_sq, normSq_coe_unitary, normSq_coe_unitary,
    one_mul, hopf, hopf]

/-- A quaternion in the real span of `1` and `i` commutes with `i`. -/
private lemma phase_mul_unitI (c : ℍ[ℝ]) (hc : c.imJ = 0 ∧ c.imK = 0) :
    c * (unitI : ℍ[ℝ]) = (unitI : ℍ[ℝ]) * c := by
  have hI : (unitI : ℍ[ℝ]) = ⟨0, 1, 0, 0⟩ := rfl
  rw [hI]
  ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, hc.1, hc.2] <;> ring

/-- Right multiplication by the phase circle does not move the Hopf image. -/
private lemma hopf_mul_phase (x c : unitary ℍ[ℝ])
    (hc : (c : ℍ[ℝ]).imJ = 0 ∧ (c : ℍ[ℝ]).imK = 0) : hopf (x * c) = hopf x := by
  rw [hopf, hopf, Submonoid.coe_mul, star_mul]
  calc (x : ℍ[ℝ]) * c * unitI * (star (c : ℍ[ℝ]) * star (x : ℍ[ℝ]))
      = x * ((c : ℍ[ℝ]) * unitI) * star (c : ℍ[ℝ]) * star (x : ℍ[ℝ]) := by
        simp only [mul_assoc]
    _ = x * ((unitI : ℍ[ℝ]) * c) * star (c : ℍ[ℝ]) * star (x : ℍ[ℝ]) := by
        rw [phase_mul_unitI _ hc]
    _ = x * unitI * ((c : ℍ[ℝ]) * star (c : ℍ[ℝ])) * star (x : ℍ[ℝ]) := by
        simp only [mul_assoc]
    _ = x * unitI * star (x : ℍ[ℝ]) := by
        rw [Unitary.mul_star_self_of_mem c.prop, mul_one]

/-- The two-term reading is blind to a phase on the left argument. -/
theorem rayKernel_mul_phase_left (x y c : unitary ℍ[ℝ])
    (hc : (c : ℍ[ℝ]).imJ = 0 ∧ (c : ℍ[ℝ]).imK = 0) : rayKernel (x * c) y = rayKernel x y := by
  rw [rayKernel_eq_hopf, rayKernel_eq_hopf, hopf_mul_phase x c hc]

/-- The two-term reading is blind to a phase on the right argument. -/
theorem rayKernel_mul_phase_right (x y c : unitary ℍ[ℝ])
    (hc : (c : ℍ[ℝ]).imJ = 0 ∧ (c : ℍ[ℝ]).imK = 0) : rayKernel x (y * c) = rayKernel x y := by
  rw [rayKernel_eq_hopf, rayKernel_eq_hopf, hopf_mul_phase y c hc]

/-- The two-term reading equals one exactly when the two unit quaternions differ by a right
phase in the real span of `1` and `i`. -/
theorem rayKernel_eq_one_iff (x y : unitary ℍ[ℝ]) :
    rayKernel x y = 1 ↔
      ∃ c : unitary ℍ[ℝ], ((c : ℍ[ℝ]).imJ = 0 ∧ (c : ℍ[ℝ]).imK = 0) ∧ y = x * c := by
  constructor
  · intro h
    refine ⟨x⁻¹ * y, ?_, (mul_inv_cancel_left x y).symm⟩
    have hdef := imJ_sq_add_imK_sq (x : ℍ[ℝ]) y
    rw [normSq_coe_unitary, normSq_coe_unitary, one_mul, ← rayKernel_eq_inner, h, sub_self,
      ← Unitary.coe_star, Unitary.star_eq_inv, ← Submonoid.coe_mul] at hdef
    have hJ := sq_nonneg ((x⁻¹ * y : unitary ℍ[ℝ]) : ℍ[ℝ]).imJ
    have hK := sq_nonneg ((x⁻¹ * y : unitary ℍ[ℝ]) : ℍ[ℝ]).imK
    exact ⟨pow_eq_zero_iff two_ne_zero |>.mp (by linarith),
      pow_eq_zero_iff two_ne_zero |>.mp (by linarith)⟩
  · rintro ⟨c, hc, rfl⟩
    have hnorm : ‖hopf x‖ = 1 := by
      rw [hopf, norm_mul, norm_mul, norm_star, CStarRing.norm_coe_unitary,
        CStarRing.norm_coe_unitary, mul_one, one_mul]
    rw [rayKernel_mul_phase_right x x c hc, rayKernel_eq_hopf, real_inner_self_eq_norm_sq, hnorm]
    norm_num

/-- The real-linear isometry `a + b i + c j + d k ↦ (a + b I, -c + d I)` from the quaternions
onto `ℂ²`. -/
def spinor : ℍ[ℝ] ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2) where
  toFun q := WithLp.toLp 2 ![⟨q.re, q.imI⟩, ⟨-q.imJ, q.imK⟩]
  invFun v := ⟨(v 0).re, (v 0).im, -(v 1).re, (v 1).im⟩
  map_add' p q := by
    ext i
    fin_cases i <;> apply Complex.ext <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, PiLp.add_apply, Complex.add_re, Complex.add_im,
        QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
        QuaternionAlgebra.imK_add, neg_add]
  map_smul' r q := by
    ext i
    fin_cases i <;> apply Complex.ext <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, PiLp.smul_apply, Real.ringHom_apply, Complex.real_smul,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
        QuaternionAlgebra.imK_smul, smul_eq_mul, mul_neg, zero_mul, sub_zero, add_zero, neg_zero]
  left_inv q := by
    ext <;> simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, neg_neg]
  right_inv v := by
    ext i
    fin_cases i <;> apply Complex.ext <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Complex.eta, neg_neg, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_map' q := by
    change ‖WithLp.toLp 2 ![(⟨q.re, q.imI⟩ : ℂ), ⟨-q.imJ, q.imK⟩]‖ = ‖q‖
    rw [EuclideanSpace.norm_eq, norm_eq_sqrt_real_inner, Quaternion.inner_self,
      Quaternion.normSq_def', Fin.sum_univ_two]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.sq_norm,
      Complex.normSq_mk]
    ring

/-- The coordinates of `spinor q`. -/
private lemma spinor_ofLp (q : ℍ[ℝ]) :
    (spinor q).ofLp = ![⟨q.re, q.imI⟩, ⟨-q.imJ, q.imK⟩] := rfl

/-- Under `spinor`, right multiplication by `i` is multiplication by the complex unit; the Hopf
image of `x` is the Bloch vector of the rank-one projection onto `spinor x`, with the imaginary
axes `k, j, i` read as the Bloch axes `0, 1, 2`; and the two-term reading is the squared modulus
of the complex transition amplitude between `spinor x` and `spinor y`, which is the trace pairing
of the two rank-one projections. -/
theorem rayKernel_eq_bornProbability_spinor (x y : unitary ℍ[ℝ]) :
    (∀ q : ℍ[ℝ], spinor (q * (unitI : ℍ[ℝ])) = Complex.I • spinor q) ∧
      bloch (Matrix.vecMulVec (spinor (x : ℍ[ℝ])).ofLp (star (spinor (x : ℍ[ℝ])).ofLp)) =
        WithLp.toLp 2 ![(hopf x).imK, (hopf x).imJ, (hopf x).imI] ∧
      rayKernel x y = ‖star (spinor (x : ℍ[ℝ])).ofLp ⬝ᵥ (spinor (y : ℍ[ℝ])).ofLp‖ ^ 2 ∧
      ((rayKernel x y : ℝ) : ℂ) =
        bornProbability
          (Matrix.vecMulVec (spinor (y : ℍ[ℝ])).ofLp (star (spinor (y : ℍ[ℝ])).ofLp))
          (Matrix.vecMulVec (spinor (x : ℍ[ℝ])).ofLp (star (spinor (x : ℍ[ℝ])).ofLp)) := by
  have hI : (unitI : ℍ[ℝ]) = ⟨0, 1, 0, 0⟩ := rfl
  have hmod : rayKernel x y =
      ‖star (spinor (x : ℍ[ℝ])).ofLp ⬝ᵥ (spinor (y : ℍ[ℝ])).ofLp‖ ^ 2 := by
    rw [rayKernel_eq_inner, inner_eq_components, inner_eq_components, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, spinor_ofLp, spinor_ofLp, hI]
    simp only [dotProduct, Fin.sum_univ_two, Fin.isValue, Pi.star_apply, RCLike.star_def,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
    ring
  refine ⟨fun q => ?_, ?_, hmod, ?_⟩
  · ext i
    fin_cases i <;> apply Complex.ext <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, spinor_ofLp, hI, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, PiLp.smul_apply, smul_eq_mul, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul, mul_zero, zero_mul, mul_one, one_mul, zero_add,
        add_zero, sub_zero, zero_sub, neg_zero, mul_neg]
  · ext i
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, bloch,
        hopf, hI, spinor_ofLp, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
        Quaternion.imJ_star, Quaternion.imK_star] <;> ring
  · rw [hmod]
    exact (rank_one_pure_state_modulus_square_reduction
      (fun _ : Unit => Matrix.vecMulVec (spinor (x : ℍ[ℝ])).ofLp (star (spinor (x : ℍ[ℝ])).ofLp))
      _ () _ _ rfl rfl).symm

end D5.S3.Quantum.AURICOmega.QuaternionRayKernel
