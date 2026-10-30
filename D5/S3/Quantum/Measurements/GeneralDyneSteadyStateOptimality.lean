/- GID: D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Aligned pure general-dyne monitoring attains the global thermal OPO optimum. -/

/-
proof_shape: result: bind-only; reason: Inlines the consumed helpers and combines normalized positivity, residual and root certificates with the explicit aligned covariance witness.
escape_witness: none
admission_basis: open-problem-resolution (#16522; Proved)
Direct frozen dependencies:
  D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov
    statement_id: sha256:410391e348afb0d9876bdf2548ca1782f14191e2ac259dd3c3d81d1876de06a4
  D5/S3/Quantum/Thermal/PositiveOneModeWilliamson.physicalJ2
    statement_id: sha256:a3c76f635d3fda80d5e5b8d7c1b2a552486e81143ead947af1e2bb7de3369327
  D5/S3/Observer/GoldenCoding/GoldenFactorCancellation.golden_factor_cancellation
    statement_id: sha256:d898d6e353a82771e931fb8d7ac3454428b2eb3b2b1780a27b64634cb72933e9
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16704
The source symplectic matrix is inlined literally in the public formulas;
proofs use the frozen physicalJ2 owner through the consumed omega_sq identity.
The scalar input and diffusion matrices are inlined literally, with no forwarding definitions.
proof_shape: omega_sq: bind-only; consumers: source_reduction; reason: Projects golden_factor_cancellation and normalizes the sign of physicalJ2.
proof_shape: source_reduction: bind-only; consumers: result; reason: Instantiates CFC.sqrt_mul_sqrt_self and sqrt_nonneg, then expands the matrix equation and cancels the nonzero damping scalar.
proof_shape: physical_forward: bind-only; consumers: physical_iff; reason: Applies the extracted frozen-owner physical_data theorem and posDef_iff_det_ne_zero with determinant nonzero by linarith.
proof_shape: physical_reverse: bind-only; consumers: physical_iff, opt_physical, aligned_attainment; reason: Instantiates positivity of C * Cᴴ, positive scaling and diagonal positivity; field_simp and ring verify the supplied factorization certificate.
proof_shape: physical_iff: bind-only; consumers: positive_branch_lower, dimensionless_lower, result; reason: After inlining both directions, combines the upstream positivity certificates and their normalized two-dimensional identities.
proof_shape: residual_eq: bind-only; consumers: covariance_factors, zero_pump_covariance; reason: Applies sub_eq_zero.mp to the unfolded stationary residual.
proof_shape: input_posDef: bind-only; consumers: n_posDef, covariance_factors, zero_pump_covariance, result; reason: Applies PosDef.one.smul and PosDef.add directly.
proof_shape: n_posDef: bind-only; consumers: covariance_factors; reason: Instantiates positive-definite congruence for the inverse of nu I + M; inverse cancellation normalizes its positive congruence certificate to nMat.
proof_shape: covariance_factors: bind-only; consumers: positive_branch_lower; reason: After inlining n_posDef, applies positive-semidefinite congruence twice and normalizes the determinant product with det_mul.
proof_shape: identity_one_ring: bind-only; consumers: identity_one; reason: Expands det_fin_two and finite matrix products and proves the polynomial identity by ring.
proof_shape: identity_one: bind-only; consumers: positive_branch_lower; reason: Substitutes the supplied determinant equality into the inlined ring identity and normalizes.
proof_shape: identity_two: bind-only; consumers: positive_branch_lower; reason: Expands the two scalar polynomials and combines the supplied determinant identity and square equalities by linear_combination.
proof_shape: quadratic_forms: bind-only; consumers: determinant_bound; reason: Expands the two specified quadratic forms, det_fin_two and finite sums; ring closes both equalities.
proof_shape: determinant_bound: bind-only; consumers: positive_branch_lower; reason: Instantiates re_dotProduct_nonneg at the two displayed vectors and normalizes their inlined quadratic identities before positive scalar cancellation and linarith.
proof_shape: trace_identity: bind-only; consumers: trace_bound; reason: Expands trWeight and det_fin_two, substitutes the supplied c squared equality, and applies ring.
proof_shape: trace_bound: bind-only; consumers: positive_branch_lower; reason: After inlining trace_identity, instantiates diag_pos and sq_nonneg; nlinarith combines those supplied atoms.
proof_shape: root_lower_bound: bind-only; consumers: positive_branch_lower; reason: Instantiates Real.sqrt_le_iff and normalizes the supplied nonnegative quadratic factor and square equality.
proof_shape: positive_branch_lower: bind-only; consumers: dimensionless_lower; reason: After inlining the positivity certificates and identities, square nonnegativity, positive scalar cancellation and polynomial normalization exclude the lower branch.
proof_shape: zero_pump_covariance: bind-only; consumers: dimensionless_lower; reason: Instantiates invertibility of positive-definite sums and inverses; expands the zero-pump residual and cancels both invertible right factors.
proof_shape: dimensionless_lower: bind-only; consumers: result; reason: Splits zero and positive pump; inlines both normalized branches and applies Real.sqrt_sq in the zero case.
proof_shape: vStar_properties: bind-only; consumers: aligned_attainment; reason: Instantiates Real.sq_sqrt and sqrt_nonneg; polynomial normalization proves the defining quadratic and the lower bound one.
proof_shape: diagonal_posDef: bind-only; consumers: opt_posDef, aligned_attainment; reason: Applies posDef_diagonal_iff after normalizing the displayed diagonal matrix.
proof_shape: opt_posDef: bind-only; consumers: opt_physical; reason: After inlining diagonal_posDef, applies div_pos to the two stable-pump diagonal entries.
proof_shape: opt_physical: bind-only; consumers: result; reason: After inlining physical_reverse and opt_posDef, verifies determinant one by field_simp and applies the normalized positivity certificate.
proof_shape: qMat_opt: bind-only; consumers: aligned_attainment; reason: Applies Matrix.inv_eq_left_inv and verifies the proposed inverse entrywise with field_simp.
proof_shape: aligned_attainment: bind-only; consumers: result; reason: For the already specified sStar matrix, inlines the physicality and root certificates and verifies the residual and determinant by field_simp and nlinarith.
definition: driftA; reason: Defines the source damping and pump drift matrix.
definition: coupling; reason: Defines the passive coupling using the literal physical symplectic matrix.
definition: eMat; reason: Defines the source correlated diffusion coefficient with its inverse matrix square root.
definition: bMat; reason: Defines the source monitoring coefficient with its inverse matrix square root.
definition: steadyEq; reason: Defines the literal stationary Riccati equation; its value is a proposition, not a proof of it.
definition: vStar; reason: Defines the explicit candidate minimum determinant square root.
definition: optMeas; reason: Defines the aligned pure measurement of the source equation.
definition: claim; reason: Defines the universal lower bound and existence of an aligned attainer; it does not prove them.
definition: qMat; reason: Defines the inverse thermal input plus measurement covariance used in the residual.
definition: dMat; reason: Defines the dimensionless drift matrix.
definition: dimResidual; reason: Defines the dimensionless stationary matrix residual.
definition: vMat; reason: Defines the displacement of the stationary covariance from the thermal input.
definition: rMat; reason: Defines the residual before its inverse-covariance factorization.
definition: nMat; reason: Defines the matrix appearing in the positive congruence certificate.
definition: wMat; reason: Defines the second residual matrix used in the determinant identity.
definition: trWeight; reason: Defines the drift-weighted sum of the covariance diagonal.
definition: fPlus; reason: Defines the scalar upper quadratic branch factor.
definition: fMinus; reason: Defines the scalar lower quadratic branch factor.
definition: sStar; reason: Specifies the constructed aligned stationary covariance used as the attainer.
The statement quantifies over every physical covariance solution and gives an aligned attainer;
it does not assert uniqueness of optimal measurements at zero pump or zero temperature.
-/

import D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation
import D5.S3.Quantum.Thermal.PositiveOneModeWilliamson
import D5.S3.Observer.GoldenCoding.GoldenFactorCancellation

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace D5.S3.Quantum.Measurements.GeneralDyneSteadyStateOptimality
open Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation

def driftA (κ χ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-κ / 2 - χ, 0; 0, -κ / 2 + χ]
def coupling (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Real.sqrt κ • (!![0, 1; -1, 0] : Matrix (Fin
  2) (Fin 2) ℝ)
def eMat (κ ν : ℝ) (σm : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * coupling κ * (ν • (1 : Matrix (Fin 2) (Fin 2)
    ℝ)) * CFC.sqrt ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + σm)⁻¹
def bMat (κ ν : ℝ) (σm : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  coupling κ * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * CFC.sqrt ((ν • (1 : Matrix (Fin 2)
    (Fin 2) ℝ)) + σm)⁻¹
def steadyEq (κ χ ν : ℝ) (σm σ : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (driftA κ χ + eMat κ ν σm * (bMat κ ν σm)ᵀ) * σ +
  σ * (driftA κ χ + eMat κ ν σm * (bMat κ ν σm)ᵀ)ᵀ +
  (((κ * ν) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) - eMat κ ν σm * (eMat κ ν σm)ᵀ) -
  σ * bMat κ ν σm * (bMat κ ν σm)ᵀ * σ = 0

def vStar (r ν : ℝ) : ℝ :=
  ((ν - 1) * Real.sqrt (1 - r ^ 2) +
  Real.sqrt ((ν - 1) ^ 2 * (1 - r ^ 2) + 4 * ν)) / 2
def optMeas (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 - r) / (1 + r), 0; 0, (1 + r) / (1 - r)]
def claim : Prop := ∀ κ χ nth : ℝ, 0 < κ → 0 ≤ χ → χ < κ / 2 → 0 ≤ nth →
  (∀ σm σ : Matrix (Fin 2) (Fin 2) ℝ, IsGaussianMeasurementCov (m := 1) σm →
  IsGaussianMeasurementCov (m := 1) σ → steadyEq κ χ (2 * nth + 1) σm σ →
  vStar (2 * χ / κ) (2 * nth + 1) ≤ Real.sqrt σ.det) ∧
  (∃ σ : Matrix (Fin 2) (Fin 2) ℝ, IsGaussianMeasurementCov (m := 1) σ ∧
  steadyEq κ χ (2 * nth + 1) (optMeas (2 * χ / κ)) σ ∧
  Real.sqrt σ.det = vStar (2 * χ / κ) (2 * nth + 1))

private def qMat (ν : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := ((ν • (1 :
  Matrix (Fin 2) (Fin 2) ℝ)) + M)⁻¹

private def dMat (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + r, 0; 0, 1 - r]

private def dimResidual (r ν : ℝ) (M S : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) - (1 / 2 : ℝ) • (dMat r * S + S * dMat r) -
  (S - (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ))) * qMat ν M * (S - (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)))


set_option maxHeartbeats 2000000 in
private lemma omega_sq :
    D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2 *
      D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2 = -1 := by
  have hJ : D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2 =
      -(!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2]
  rw [hJ, neg_mul_neg]
  exact D5.S3.Observer.GoldenCoding.GoldenFactorCancellation.golden_factor_cancellation.2.2.2.2

set_option maxHeartbeats 2000000 in
private lemma source_reduction (κ χ ν : ℝ) (M S : Matrix (Fin 2) (Fin 2) ℝ) (hκ : 0 < κ)
    (hU : ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M).PosSemidef) :
    steadyEq κ χ ν M S ↔ dimResidual (2 * χ / κ) ν M S = 0 := by
  let L := CFC.sqrt ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M)⁻¹
  have hLL : L * L = ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M)⁻¹ :=
    CFC.sqrt_mul_sqrt_self _ hU.inv.nonneg
  have hLT : Lᵀ = L := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg (((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M)⁻¹)).posSemidef.1.eq
  have hb : bMat κ ν M = (-Real.sqrt κ) • L := by
    change (Real.sqrt κ • D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2) *
        D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2 * L = _
    simp [omega_sq]
  have he : eMat κ ν M = ν • bMat κ ν M := by
    rw [hb]
    change D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2 *
        (Real.sqrt κ • D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2) *
        (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * L = _
    simp [omega_sq, smul_smul]
  have hbb : bMat κ ν M * (bMat κ ν M)ᵀ = κ • qMat ν M := by
    rw [hb, Matrix.transpose_smul, hLT, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [neg_mul_neg, Real.mul_self_sqrt hκ.le, hLL, qMat]
  have hqt : (qMat ν M)ᵀ = qMat ν M := by
    simpa [qMat, Matrix.conjTranspose_eq_transpose_of_trivial] using hU.inv.1.eq
  have hat : (driftA κ χ)ᵀ = driftA κ χ := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hA : driftA κ χ = (-κ / 2 : ℝ) • dMat (2 * χ / κ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [driftA, dMat] <;> field_simp [hκ.ne'] <;> ring
  have hprod : S * bMat κ ν M * (bMat κ ν M)ᵀ * S = κ • (S * qMat ν M * S) := by
    rw [Matrix.mul_assoc S, hbb, Matrix.mul_smul, Matrix.smul_mul]
  have hexp :
      (driftA κ χ + eMat κ ν M * (bMat κ ν M)ᵀ) * S +
      S * (driftA κ χ + eMat κ ν M * (bMat κ ν M)ᵀ)ᵀ +
      (((κ * ν) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) - eMat κ ν M * (eMat κ ν M)ᵀ) -
      S * bMat κ ν M * (bMat κ ν M)ᵀ * S = κ • dimResidual (2 * χ / κ) ν M S := by
    rw [hprod, he]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_add,
      Matrix.transpose_smul, smul_smul, hbb, hqt, hat]
    rw [hA]
    dsimp [dimResidual]
    simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, smul_add, smul_sub]
    have hsc : -κ / 2 = κ * (-(1 / 2 : ℝ)) := by ring
    rw [hsc]
    module
  unfold steadyEq
  rw [hexp]
  exact smul_eq_zero_iff_right hκ.ne'


set_option maxHeartbeats 2000000 in
lemma physical_forward (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsGaussianMeasurementCov (m
  := 1) M) :
    M.PosDef ∧ 1 ≤ M.det := by
  obtain ⟨hp, hd⟩ :=
    D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.physical_data M hM
  exact ⟨hp.posDef_iff_det_ne_zero.mpr (by linarith), hd⟩

set_option maxHeartbeats 2000000 in
private lemma physical_reverse (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.PosDef) (hd : 1 ≤ M.det) :
    IsGaussianMeasurementCov (m := 1) M := by
  refine ⟨by simpa using hM.1, ?_⟩
  have hx := hM.diag_pos (i := 0)
  have hsym : M 1 0 = M 0 1 := congrArg (fun A => A 0 1) hM.1
  let C : Matrix (Fin 2) (Fin 2) ℂ := !![(M 0 0 : ℂ), 0; (M 0 1 : ℂ) - Complex.I, 0]
  let D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, ((M.det - 1) / M 0 0 : ℝ)]
  have hfactor : (M.map Complex.ofReal) + Complex.I •
      ((-Matrix.J (Fin 1) ℂ).submatrix
        (fun i : Fin (2 * 1) => if i.val % 2 = 0 then
          Sum.inl ((Fin.cast (Nat.mul_comm 2 1) i).divNat)
        else Sum.inr ((Fin.cast (Nat.mul_comm 2 1) i).divNat))
        (fun i : Fin (2 * 1) => if i.val % 2 = 0 then
          Sum.inl ((Fin.cast (Nat.mul_comm 2 1) i).divNat)
        else Sum.inr ((Fin.cast (Nat.mul_comm 2 1) i).divNat))) =
        (M 0 0)⁻¹ • (C * Cᴴ) + D := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [C, D, Matrix.J, Matrix.fromBlocks, Matrix.submatrix, Fin.divNat,
        Matrix.one_apply, hsym, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.star_def, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.det_fin_two]
    all_goals field_simp [hx.ne']
    all_goals ring
  rw [hfactor]
  apply Matrix.PosSemidef.add
  · exact (Matrix.posSemidef_self_mul_conjTranspose C).smul (inv_nonneg.mpr hx.le)
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i; fin_cases i
    · norm_num
    · change (0 : ℂ) ≤ (((M.det - 1) / M 0 0 : ℝ) : ℂ)
      exact_mod_cast (div_nonneg (by linarith : 0 ≤ M.det - 1) hx.le)

set_option maxHeartbeats 2000000 in
private lemma physical_iff (M : Matrix (Fin 2) (Fin 2) ℝ) : IsGaussianMeasurementCov (m := 1) M ↔
    M.PosDef ∧ 1 ≤ M.det := ⟨physical_forward M, fun h => physical_reverse M h.1 h.2⟩


private def vMat (ν : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := S - (ν • (1
  : Matrix (Fin 2) (Fin 2) ℝ))
private def rMat (r ν : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (ν • (1 :
  Matrix (Fin 2) (Fin 2) ℝ)) - (1 / 2 : ℝ) • (dMat r * S + S * dMat r)
private def nMat (ν : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := 1 - ν •
  qMat ν M
private def wMat (r ν : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := vMat ν S
  * vMat ν S - ν • rMat r ν S
private def trWeight (r : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (1 + r) * S 0 0 + (1 - r) * S 1 1
private def fPlus (c ν v : ℝ) := v ^ 2 - (ν + 1) * c * v + ν
private def fMinus (c ν v : ℝ) := v ^ 2 - (ν - 1) * c * v - ν

set_option maxHeartbeats 2000000 in
private lemma residual_eq (r ν : ℝ) (M S : Matrix (Fin 2) (Fin 2) ℝ) (hs : dimResidual r ν M S =
  0) :
    rMat r ν S = vMat ν S * qMat ν M * vMat ν S := by
  exact sub_eq_zero.mp hs

set_option maxHeartbeats 2000000 in
private lemma input_posDef (ν : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (hν : 0 < ν) (hM : M.PosDef) :
    ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M).PosDef := (Matrix.PosDef.one.smul hν).add hM

set_option maxHeartbeats 2000000 in
private lemma n_posDef (ν : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (hν : 0 < ν) (hM : M.PosDef) :
    (nMat ν M).PosDef := by
  let U := (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M
  have hu : U.PosDef := input_posDef ν M hν hM
  have hq : (qMat ν M).PosDef := hu.inv
  have hUQ : U * qMat ν M = 1 := Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hu.isUnit)
  have hQU : qMat ν M * U = 1 := Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp hu.isUnit)
  have hMQ : M * qMat ν M = nMat ν M := by
    dsimp [U] at hUQ
    simp only [add_mul, Matrix.smul_mul, one_mul] at hUQ
    dsimp [nMat]
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hUQ
  have hQM : qMat ν M * M = nMat ν M := by
    dsimp [U] at hQU
    simp only [mul_add, Matrix.mul_smul, mul_one] at hQU
    dsimp [nMat]
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hQU
  have hm2 : (M * M).PosSemidef := by
    simpa only [hM.1.eq] using Matrix.posSemidef_self_mul_conjTranspose M
  have hk : (ν • M + M * M).PosDef := (hM.smul hν).add_posSemidef hm2
  have hid : qMat ν M * (ν • M + M * M) * qMat ν M = nMat ν M := by
    have he : ν • M + M * M = M * U := by
      dsimp [U]
      simp only [mul_add, Matrix.mul_smul, mul_one]
    rw [he, Matrix.mul_assoc, Matrix.mul_assoc M, hUQ, mul_one, hQM]
  rw [← hid]
  simpa only [hq.1.eq] using hk.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hq.isUnit)

set_option maxHeartbeats 2000000 in
private lemma covariance_factors (r ν : ℝ) (M S : Matrix (Fin 2) (Fin 2) ℝ) (hν : 0 < ν)
    (hM : M.PosDef) (hS : S.PosDef) (hs : dimResidual r ν M S = 0) :
    (rMat r ν S).PosSemidef ∧ (wMat r ν S).PosSemidef ∧
    (wMat r ν S).det = M.det * (rMat r ν S).det := by
  have hq := (input_posDef ν M hν hM).inv
  have hv : (vMat ν S)ᴴ = vMat ν S := by
    dsimp [vMat]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hS.1.eq, star_trivial]
  have hn := n_posDef ν M hν hM
  have hr := residual_eq r ν M S hs
  have hw : wMat r ν S = vMat ν S * nMat ν M * vMat ν S := by
    rw [wMat, hr]
    dsimp [nMat]
    simp only [mul_sub, sub_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  have hMQ : M * qMat ν M = nMat ν M := by
    have h := Matrix.mul_nonsing_inv ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M)
      ((Matrix.isUnit_iff_isUnit_det _).mp (input_posDef ν M hν hM).isUnit)
    simp only [add_mul, Matrix.smul_mul, one_mul] at h
    dsimp [nMat, qMat]
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using h
  refine ⟨?_, ?_, ?_⟩
  · rw [hr]
    simpa only [hv, qMat] using hq.posSemidef.mul_mul_conjTranspose_same (vMat ν S)
  · rw [hw]
    simpa only [hv] using hn.posSemidef.mul_mul_conjTranspose_same (vMat ν S)
  · rw [hw, ← hMQ, hr]
    simp only [Matrix.det_mul]
    ring

set_option maxHeartbeats 2000000 in
private lemma identity_one_ring (r ν : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.IsSymm) :
    (S.det - 1) * (S.det + ν ^ 2 - ν * trWeight r S) - (ν ^ 2 - 1) * r ^ 2 * S 0 0 * S 1 1 =
    (wMat r ν S).det - (rMat r ν S).det := by
  have hh : S 1 0 = S 0 1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hS
  simp [wMat, vMat, rMat, dMat, trWeight, Matrix.det_fin_two,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply, hh]
  ring

set_option maxHeartbeats 2000000 in
private lemma identity_one (r ν : ℝ) (M S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.IsSymm)
    (hd : (wMat r ν S).det = M.det * (rMat r ν S).det) :
    (S.det - 1) * (S.det + ν ^ 2 - ν * trWeight r S) =
    (ν ^ 2 - 1) * r ^ 2 * S 0 0 * S 1 1 + (M.det - 1) * (rMat r ν S).det := by
  have h := identity_one_ring r ν S hS
  rw [hd] at h
  nlinarith only [h]

set_option maxHeartbeats 2000000 in
private lemma identity_two (r ν c v : ℝ) (M S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.IsSymm)
    (hc : c ^ 2 = 1 - r ^ 2) (hv : v ^ 2 = S.det)
    (hi : (S.det - 1) * (S.det + ν ^ 2 - ν * trWeight r S) =
      (ν ^ 2 - 1) * r ^ 2 * S 0 0 * S 1 1 + (M.det - 1) * (rMat r ν S).det) :
    fPlus c ν v * fMinus c ν v = (ν ^ 2 - 1) * r ^ 2 * (S 0 1) ^ 2 +
      ν * (S.det - 1) * (trWeight r S - 2 * c * v) + (M.det - 1) * (rMat r ν S).det := by
  have hh : S 1 0 = S 0 1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hS
  have hd : S.det = S 0 0 * S 1 1 - (S 0 1) ^ 2 := by simp [Matrix.det_fin_two, hh, pow_two]
  have he : fPlus c ν v * fMinus c ν v =
      (v ^ 2 - 1) * (v ^ 2 + ν ^ 2 - 2 * ν * c * v) - (ν ^ 2 - 1) * r ^ 2 * v ^ 2 := by
    dsimp [fPlus, fMinus]
    ring_nf
    rw [hc]
    ring
  rw [he, hv]
  linear_combination hi - ((ν ^ 2 - 1) * r ^ 2) * hd


set_option maxHeartbeats 2000000 in
private lemma quadratic_forms (r ν : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.IsSymm) :
    (![S 1 1, -S 0 1] ⬝ᵥ ((wMat r ν S) *ᵥ ![S 1 1, -S 0 1])) =
      S.det * (S.det - ν * (1 - r) * S 1 1) ∧
    (![-S 0 1, S 0 0] ⬝ᵥ ((wMat r ν S) *ᵥ ![-S 0 1, S 0 0])) =
      S.det * (S.det - ν * (1 + r) * S 0 0) := by
  have hh : S 1 0 = S 0 1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hS
  constructor <;>
    simp [wMat, vMat, rMat, dMat, Matrix.det_fin_two,
      Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.one_apply, hh] <;> ring

set_option maxHeartbeats 2000000 in
private lemma determinant_bound (r ν : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.PosDef)
    (hd : 0 < S.det) (hW : (wMat r ν S).PosSemidef) :
    ν * trWeight r S ≤ 2 * S.det := by
  have hs : S.IsSymm := by simpa using hS.1
  have h1 := hW.re_dotProduct_nonneg ![S 1 1, -S 0 1]
  have h2 := hW.re_dotProduct_nonneg ![-S 0 1, S 0 0]
  simp only [star_trivial, RCLike.re_to_real] at h1 h2
  rw [(quadratic_forms r ν S hs).1] at h1
  rw [(quadratic_forms r ν S hs).2] at h2
  have hb1 := (mul_nonneg_iff_of_pos_left hd).mp h1
  have hb2 := (mul_nonneg_iff_of_pos_left hd).mp h2
  dsimp [trWeight]
  linarith

set_option maxHeartbeats 2000000 in
private lemma trace_identity (r c : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.IsSymm) (hc : c ^ 2
  = 1 - r ^ 2) :
    (trWeight r S) ^ 2 - 4 * c ^ 2 * S.det =
    ((1 + r) * S 0 0 - (1 - r) * S 1 1) ^ 2 + 4 * c ^ 2 * (S 0 1) ^ 2 := by
  have hh : S 1 0 = S 0 1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hS
  simp only [trWeight, Matrix.det_fin_two, hh]
  rw [hc]
  ring

set_option maxHeartbeats 2000000 in
private lemma trace_bound (r c v : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hc0 : 0 ≤ c) (hv0 : 0 ≤ v) (hc : c ^ 2 = 1 - r ^ 2) (hv : v ^ 2 = S.det)
    (hS : S.PosDef) : 2 * c * v ≤ trWeight r S := by
  have hs : S.IsSymm := by simpa using hS.1
  have he := trace_identity r c S hs hc
  have hT : 0 < trWeight r S := by
    dsimp [trWeight]
    have hx := hS.diag_pos (i := 0)
    have hy := hS.diag_pos (i := 1)
    have ha : 0 < 1 + r := by linarith
    have hb : 0 < 1 - r := by linarith
    positivity
  have hsquare := sq_nonneg ((1 + r) * S 0 0 - (1 - r) * S 1 1)
  have hh : 0 ≤ 4 * c ^ 2 * (S 0 1) ^ 2 := by positivity
  rw [← hv] at he
  nlinarith only [he, hsquare, hh, hT, mul_nonneg hc0 hv0]

set_option maxHeartbeats 2000000 in
private lemma root_lower_bound (r ν c v : ℝ) (hν : 1 ≤ ν) (hc0 : 0 ≤ c)
    (hc : c = Real.sqrt (1 - r ^ 2)) (hc2 : c ^ 2 = 1 - r ^ 2) (hv : ν * c ≤ v) (hf : 0 ≤ fMinus
      c ν v) :
    vStar r ν ≤ v := by
  have hnc : 0 ≤ (ν - 1) * c := mul_nonneg (by linarith) hc0
  have hn : 0 ≤ ν * c := mul_nonneg (by linarith) hc0
  have hleft : 0 ≤ 2 * v - (ν - 1) * c := by nlinarith
  have hs : Real.sqrt ((ν - 1) ^ 2 * (1 - r ^ 2) + 4 * ν) ≤ 2 * v - (ν - 1) * c := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hleft, ?_⟩
    dsimp [fMinus] at hf
    rw [← hc2]
    nlinarith only [hf]
  unfold vStar
  rw [← hc]
  linarith


set_option maxHeartbeats 2000000 in
private lemma positive_branch_lower (r ν : ℝ) (M S : Matrix (Fin 2) (Fin 2) ℝ) (hr : 0 < r) (hr1
  : r < 1)
    (hν : 1 ≤ ν) (hM : IsGaussianMeasurementCov (m := 1) M)
    (hS : IsGaussianMeasurementCov (m := 1) S) (hs : dimResidual r ν M S = 0) :
    vStar r ν ≤ Real.sqrt S.det := by
  obtain ⟨hMp,hMd⟩ := (physical_iff M).mp hM
  obtain ⟨hSp,hSd⟩ := (physical_iff S).mp hS
  have hν0 : 0 < ν := by linarith
  have hd : 0 < S.det := by linarith
  let c := Real.sqrt (1 - r ^ 2)
  let v := Real.sqrt S.det
  have hstable : 0 < 1 - r ^ 2 := by
    nlinarith only [mul_pos (by linarith : 0 < 1 - r) (by linarith : 0 < 1 + r)]
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hstable.le
  have hv0 : 0 < v := Real.sqrt_pos.mpr hd
  have hv2 : v ^ 2 = S.det := Real.sq_sqrt hd.le
  obtain ⟨hR,hW,hw⟩ := covariance_factors r ν M S hν0 hMp hSp hs
  have hdet := determinant_bound r ν S hSp hd hW
  have ht := trace_bound r c v S hr.le hr1 hc0 hv0.le hc2 hv2 hSp
  have hnt := mul_le_mul_of_nonneg_left ht hν0.le
  have hvnc : ν * c ≤ v := by
    have hp : 0 ≤ v * (v - ν * c) := by nlinarith only [hdet, hnt, hv2]
    have := (mul_nonneg_iff_of_pos_left hv0).mp hp
    linarith
  have he1 := identity_one r ν M S hS.1 hw
  have he2 := identity_two r ν c v M S hS.1 hc2 hv2 he1
  have hε : 0 ≤ (M.det - 1) * (rMat r ν S).det := mul_nonneg (by linarith) hR.det_nonneg
  have hnu2 : 0 ≤ ν ^ 2 - 1 := by nlinarith
  have hbalance : 0 ≤ trWeight r S - 2 * c * v := by linarith
  have hrhs : 0 ≤ (ν ^ 2 - 1) * r ^ 2 * (S 0 1) ^ 2 +
      ν * (S.det - 1) * (trWeight r S - 2 * c * v) + (M.det - 1) * (rMat r ν S).det := by
    positivity
  have hprod : 0 ≤ fPlus c ν v * fMinus c ν v := by rw [he2]; exact hrhs
  have hplus_id : fPlus c ν v = (v - ν * c) ^ 2 + (ν - 1) * c * (v - ν * c) + ν * r ^ 2 := by
    dsimp [fPlus]
    ring_nf
    rw [hc2]
    ring
  have hplus : 0 < fPlus c ν v := by
    rw [hplus_id]
    have hA : 0 ≤ (ν - 1) * c * (v - ν * c) := by positivity
    have hB : 0 < ν * r ^ 2 := by positivity
    nlinarith only [sq_nonneg (v - ν * c), hA, hB]
  have hminus : 0 ≤ fMinus c ν v := (mul_nonneg_iff_of_pos_left hplus).mp hprod
  exact root_lower_bound r ν c v hν hc0 rfl hc2 hvnc hminus

set_option maxHeartbeats 2000000 in
private lemma zero_pump_covariance (ν : ℝ) (M S : Matrix (Fin 2) (Fin 2) ℝ) (hν : 0 < ν)
    (hM : M.PosDef) (hS : S.PosDef) (hs : dimResidual 0 ν M S = 0) :
    S = (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hd0 : dMat 0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [dMat, Matrix.one_apply]
  have hr0 : rMat 0 ν S = -vMat ν S := by
    dsimp [rMat, vMat]
    rw [hd0]
    simp only [one_mul, mul_one]
    module
  have hR := residual_eq 0 ν M S hs
  rw [hr0] at hR
  have hU := input_posDef ν M hν hM
  have hQunit : IsUnit (qMat ν M).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU.inv.isUnit
  have hSMunit : IsUnit (S + M).det := (Matrix.isUnit_iff_isUnit_det _).mp (hS.add hM).isUnit
  have hQU : qMat ν M * ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M) = 1 := Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp hU.isUnit)
  have hSM : S + M = vMat ν S + ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M) := by dsimp [vMat]; abel
  have hzero : vMat ν S * qMat ν M * (S + M) = 0 := by
    rw [hSM, mul_add, Matrix.mul_assoc _ _ ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) + M), hQU,
      mul_one, ← hR]
    abel
  have h1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A * (S + M)⁻¹) hzero
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hSMunit, zero_mul] at h1
  have h2 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A * (qMat ν M)⁻¹) h1
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hQunit, zero_mul] at h2
  exact sub_eq_zero.mp h2

set_option maxHeartbeats 2000000 in
private lemma dimensionless_lower (r ν : ℝ) (M S : Matrix (Fin 2) (Fin 2) ℝ) (hr : 0 ≤ r) (hr1 :
  r < 1)
    (hν : 1 ≤ ν) (hM : IsGaussianMeasurementCov (m := 1) M)
    (hS : IsGaussianMeasurementCov (m := 1) S) (hs : dimResidual r ν M S = 0) :
    vStar r ν ≤ Real.sqrt S.det := by
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · subst r
    have hz := zero_pump_covariance ν M S (by linarith)
      ((physical_iff M).mp hM).1 ((physical_iff S).mp hS).1 hs
    rw [hz]
    have hdet : ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ))).det = ν ^ 2 := by simp []
    rw [hdet, Real.sqrt_sq (by linarith : 0 ≤ ν)]
    have hv : vStar 0 ν = ν := by
      have he : (ν - 1) ^ 2 + 4 * ν = (ν + 1) ^ 2 := by ring
      norm_num [vStar]
      rw [he, Real.sqrt_sq (by linarith : 0 ≤ ν + 1)]
      ring
    rw [hv]
  · exact positive_branch_lower r ν M S hr0 hr1 hν hM hS hs


set_option maxHeartbeats 2000000 in
private lemma vStar_properties (r ν : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (hν : 1 ≤ ν) :
    1 ≤ vStar r ν ∧ fMinus (Real.sqrt (1 - r ^ 2)) ν (vStar r ν) = 0 := by
  have hstable : 0 < 1 - r ^ 2 := by
    nlinarith only [mul_pos (by linarith : 0 < 1 - r) (by linarith : 0 < 1 + r)]
  have hc2 := Real.sq_sqrt hstable.le
  have hdelta : 0 ≤ (ν - 1) ^ 2 * (1 - r ^ 2) + 4 * ν := by positivity
  have hd : (Real.sqrt ((ν - 1) ^ 2 * (1 - r ^ 2) + 4 * ν)) ^ 2 =
      (ν - 1) ^ 2 * (Real.sqrt (1 - r ^ 2)) ^ 2 + 4 * ν := by
    rw [hc2]
    exact Real.sq_sqrt hdelta
  have hw0 : 0 ≤ vStar r ν := by dsimp [vStar]; positivity
  have hquad : fMinus (Real.sqrt (1 - r ^ 2)) ν (vStar r ν) = 0 := by
    dsimp [fMinus, vStar]
    nlinarith only [hd]
  refine ⟨?_, hquad⟩
  have ha : 0 ≤ (ν - 1) * Real.sqrt (1 - r ^ 2) * vStar r ν := by positivity
  dsimp [fMinus] at hquad
  nlinarith only [hquad, ha, hν, hw0]

set_option maxHeartbeats 2000000 in
private lemma diagonal_posDef (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (!![x,0;0,y] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  have he : (!![x,0;0,y] : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![x,y] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [he, Matrix.posDef_diagonal_iff]
  intro i; fin_cases i <;> assumption

set_option maxHeartbeats 2000000 in
private lemma opt_posDef (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : (optMeas r).PosDef := by
  apply diagonal_posDef
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos (by linarith) (by linarith)

set_option maxHeartbeats 2000000 in
private lemma opt_physical (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    IsGaussianMeasurementCov (m := 1) (optMeas r) := by
  have ha : 0 < 1 + r := by linarith
  have hb : 0 < 1 - r := by linarith
  have hd : (optMeas r).det = 1 := by
    simp [optMeas, Matrix.det_fin_two]
    field_simp [ha.ne', hb.ne']
  exact physical_reverse _ (opt_posDef r hr hr1) (by rw [hd])

set_option maxHeartbeats 2000000 in
private lemma qMat_opt (r ν : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (hν : 1 ≤ ν) :
    qMat ν (optMeas r)=
      !![(1 + r) / (ν * (1 + r) + (1 - r)),0;0,(1 - r) / (ν * (1 - r) + (1 + r))] := by
  have ha : 0 < 1 + r := by linarith
  have hb : 0 < 1 - r := by linarith
  have hA : 0 < ν * (1 + r) + (1 - r) := by positivity
  have hB : 0 < ν * (1 - r) + (1 + r) := by positivity
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [optMeas, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.one_apply]
  all_goals field_simp [ha.ne', hb.ne', hA.ne', hB.ne']

private def sStar (r ν : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt (1 - r ^ 2) * vStar r ν / (1 + r), 0;
      0, Real.sqrt (1 - r ^ 2) * vStar r ν / (1 - r)]

set_option maxHeartbeats 2000000 in
private lemma aligned_attainment (r ν : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (hν : 1 ≤ ν) :
    IsGaussianMeasurementCov (m := 1) (sStar r ν) ∧
    dimResidual r ν (optMeas r) (sStar r ν) = 0 ∧
    Real.sqrt (sStar r ν).det = vStar r ν := by
  have ha : 0 < 1 + r := by linarith
  have hb : 0 < 1 - r := by linarith
  have hstable : 0 < 1 - r ^ 2 := by nlinarith only [mul_pos hb ha]
  have hc : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr hstable
  have hc2 := Real.sq_sqrt hstable.le
  obtain ⟨hv,hquad⟩ := vStar_properties r ν hr hr1 hν
  have hv0 : 0 < vStar r ν := by linarith
  have hp : (sStar r ν).PosDef := diagonal_posDef _ _ (div_pos (mul_pos hc hv0) ha)
    (div_pos (mul_pos hc hv0) hb)
  have hd : (sStar r ν).det = (vStar r ν) ^ 2 := by
    simp [sStar, Matrix.det_fin_two]
    field_simp [ha.ne', hb.ne']
    nlinarith only [hc2]
  have ht : (Real.sqrt (1 - r ^ 2) * vStar r ν) ^ 2 -
      (ν - 1) * (1 - r ^ 2) * (Real.sqrt (1 - r ^ 2) * vStar r ν) - ν * (1 - r ^ 2) = 0 := by
    dsimp [fMinus] at hquad
    linear_combination (Real.sqrt (1 - r ^ 2)) ^ 2 * hquad +
      ((ν - 1) * Real.sqrt (1 - r ^ 2) * vStar r ν + ν) * hc2
  refine ⟨physical_reverse _ hp ?_, ?_, ?_⟩
  · rw [hd]; nlinarith only [hv]
  · rw [dimResidual, qMat_opt r ν hr hr1 hν]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sStar, dMat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.one_apply]
    all_goals have hA : 0 < ν * (1 + r) + (1 - r) := by positivity
    all_goals have hB : 0 < ν * (1 - r) + (1 + r) := by positivity
    all_goals field_simp [ha.ne', hb.ne', hA.ne', hB.ne']
    all_goals nlinarith only [ht]
  · rw [hd, Real.sqrt_sq hv0.le]

set_option maxHeartbeats 2000000 in
theorem result : claim := by
  intro κ χ nth hκ hχ hχ1 hnth
  let r := 2 * χ / κ
  let ν := 2 * nth + 1
  have hr : 0 ≤ r := div_nonneg (by positivity) hκ.le
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_one hκ).mpr
    linarith
  have hν : 1 ≤ ν := by dsimp [ν]; linarith
  constructor
  · intro M S hM hS hs
    apply dimensionless_lower r ν M S hr hr1 hν hM hS
    exact (source_reduction κ χ ν M S hκ
      (input_posDef ν M (by linarith) ((physical_iff M).mp hM).1).posSemidef).mp hs
  · obtain ⟨hS,hs,hv⟩ := aligned_attainment r ν hr hr1 hν
    refine ⟨sStar r ν, hS, ?_, hv⟩
    exact (source_reduction κ χ ν (optMeas r) (sStar r ν) hκ
      (input_posDef ν (optMeas r) (by linarith) ((physical_iff (optMeas r)).mp (opt_physical r hr
        hr1)).1).posSemidef).mpr hs

end D5.S3.Quantum.Measurements.GeneralDyneSteadyStateOptimality
