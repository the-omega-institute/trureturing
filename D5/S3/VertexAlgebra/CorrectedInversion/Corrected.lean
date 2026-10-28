/- GID: D5/S3/VertexAlgebra/CorrectedInversion/Corrected
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/CorrectedInversion/Corrected
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full original corrected-field inversion from normal transpose and finite L1 flow. -/
import D5.S3.VertexAlgebra.CorrectedInversion.SignedSource

/-!
# Original corrected-field inversion

The normal transpose is applied at the original coefficient e+2c. Exact Corr
bidegree transports source weight R to R-c, and original Corr covariance
exchanges the finite coefficient sums. The signed affine source coefficients
then give the finite exp(L1) formula on the original actualForm, in its given
orientation. No desired inversion, ground symmetry or positive norm is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.CorrectedInversion
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockFockNormalField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField TwistedGround.ActualChargedAdjoint
open MvPolynomial HalfFock

/- Reuse the original public coefficient evaluator as a linear map. -/

private def correctedLeft (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (e : ℤ) (x y : ActualTensor D hu) : Module.Dual ℂ (Oscillator D) where
  toFun p := actualForm D hu ((correctedPolynomial D hu a p).coeff e x) y
  map_add' p q :=
    (((actualForm D hu).flip y).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e x).comp (correctedPolynomial D hu a))).map_add p q
  map_smul' c p :=
    (((actualForm D hu).flip y).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e x).comp (correctedPolynomial D hu a))).map_smul c p

private def correctedRight (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (e : ℤ) (x y : ActualTensor D hu) : Module.Dual ℂ (Oscillator D) where
  toFun p := actualForm D hu x ((correctedPolynomial D hu a p).coeff e y)
  map_add' p q :=
    ((actualForm D hu x).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e y).comp (correctedPolynomial D hu a))).map_add p q
  map_smul' c p :=
    ((actualForm D hu x).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e y).comp (correctedPolynomial D hu a))).map_smul c p

@[simp] private theorem correctedField_single (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) :
    correctedField D hu (Finsupp.single a p) = correctedPolynomial D hu a p := by
  simp only [correctedField, Finsupp.lsum_single]

private def evaluateLeft (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x y : ActualTensor D hu) : NativeField D hu →ₗ[ℂ] ℂ where
  toFun F := actualForm D hu (F.coeff e x) y
  map_add' F G :=
    (((actualForm D hu).flip y).comp (LatticeHalfFockFockNormalField.coefficientAt D hu e x)).map_add F G
  map_smul' c F :=
    (((actualForm D hu).flip y).comp (LatticeHalfFockFockNormalField.coefficientAt D hu e x)).map_smul c F

private def evaluateRight (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x y : ActualTensor D hu) : NativeField D hu →ₗ[ℂ] ℂ where
  toFun F := actualForm D hu x (F.coeff e y)
  map_add' F G :=
    ((actualForm D hu x).comp (LatticeHalfFockFockNormalField.coefficientAt D hu e y)).map_add F G
  map_smul' c F :=
    ((actualForm D hu x).comp (LatticeHalfFockFockNormalField.coefficientAt D hu e y)).map_smul c F

private theorem correctedLeft_Corr (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (e : ℤ) (x y : ActualTensor D hu) :
    correctedLeft D hu a e x y p = ∑ c ∈ (Corr D a p).support,
      normalLeft D hu a (e+2*(c : ℤ)) x y (Corr D a p c) := by
  change evaluateLeft D hu e x y (correctedPolynomial D hu a p) = _
  simp only [correctedPolynomial, LinearMap.comp_apply, correctedSum,
    Finsupp.lsum_apply, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  change actualForm D hu ((shiftField D hu c
    (polynomialField D hu a (Corr D a p c))).coeff e x) y = _
  rw [shiftField_coefficient_public]
  rfl

private theorem correctedRight_Corr (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (e : ℤ) (x y : ActualTensor D hu) :
    correctedRight D hu a e x y p = ∑ c ∈ (Corr D a p).support,
      normalRight D hu a (e+2*(c : ℤ)) x y (Corr D a p c) := by
  change evaluateRight D hu e x y (correctedPolynomial D hu a p) = _
  simp only [correctedPolynomial, LinearMap.comp_apply, correctedSum,
    Finsupp.lsum_apply, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  change actualForm D hu x ((shiftField D hu c
    (polynomialField D hu a (Corr D a p c))).coeff e y) = _
  rw [shiftField_coefficient_public]
  rfl

/-- The native API gives exact bidegree, rather than the old proposed homogeneous
endpoint. This local, consumed implication also handles an identically zero
coefficient and shifts above R without using any extra public cutoff endpoint. -/
private theorem correction_coefficient_weight (D : LatticeData) (a : Charge D)
    (p : Oscillator D) (R : ℕ)
    (hp : IsWeightedHomogeneous (sourceWeight D) p R) (s : ℕ) :
    IsWeightedHomogeneous (sourceWeight D) (Corr D a p s) (R-s) := by
  intro m hm
  have h := ActualCorrCovariance.Corr_coefficient_bidegree D a p R hp s m hm
  omega

/-- Exact signed exponent transport; charge norm and exponent remain integers. -/
private theorem shifted_exponent (N e : ℤ) (R c t : ℕ) (hc : c ≤ R) :
    (-2*N-4*((R-c : ℕ) : ℤ)+2*(t : ℤ))-(e+2*(c : ℤ)) =
      -2*N-4*(R : ℤ)+2*((c+t : ℕ) : ℤ)-e := by
  rw [Int.ofNat_sub hc]
  push_cast
  ring

set_option maxHeartbeats 4000000 in
-- Normalize the original finite Corr coefficient convolution.
/-- The actual finite (c,t) assembly. Normal transpose is applied at e+2c;
Corr homogeneity transports its weight; original Corr covariance exchanges the
finite sums; the original shiftField rule reconstructs correctedPolynomial. -/
private theorem corrected_affine_support (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (R : ℕ)
    (hp : IsWeightedHomogeneous (sourceWeight D) p R)
    (e : ℤ) (x y : ActualTensor D hu) :
    correctedLeft D hu a e x y p = paritySign (chargeNorm D a / 2) *
      ∑ t ∈ (affineP D a p).support,
        correctedRight D hu a (shiftIndex D a R t-e) x y
          ((affineP D a p).coeff t) := by
  classical
  let ell : ℕ → Module.Dual ℂ (Oscillator D) := fun j =>
    normalRight D hu a (shiftIndex D a R j-e) x y
  have degree_le : weightedTotalDegree (sourceWeight D) p ≤ R := by
    apply Finset.sup_le
    intro m hm
    exact le_of_eq (hp (mem_support_iff.mp hm))
  rw [correctedLeft_Corr]
  calc
    _ = paritySign (chargeNorm D a / 2) *
        ∑ c ∈ (Corr D a p).support,
          ∑ t ∈ (normalP D (Corr D a p c)).support,
            ell (c+t) ((normalP D (Corr D a p c)).coeff t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hcR : c ≤ R := (Corr_shift_bound D a p c hc).trans degree_le
      rw [normal_homogeneous_readout D hu a (Corr D a p c) (R-c)
        (correction_coefficient_weight D a p R hp c) (e+2*(c : ℤ)) x y]
      change paritySign (chargeNorm D a / 2) *
        (∑ t ∈ (normalP D (Corr D a p c)).support,
          normalRight D hu a (shiftIndex D a (R-c) t-(e+2*(c : ℤ))) x y
            ((normalP D (Corr D a p c)).coeff t)) = _
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      dsimp [ell]
      have he : shiftIndex D a (R-c) t-(e+2*(c : ℤ)) =
          shiftIndex D a R (c+t)-e :=
        shifted_exponent (chargeNorm D a) e R c t hcR
      rw [he]
    _ = paritySign (chargeNorm D a / 2) *
        ∑ t ∈ (affineP D a p).support,
          ∑ c ∈ (Corr D a ((affineP D a p).coeff t)).support,
            ell (t+c) (Corr D a ((affineP D a p).coeff t) c) := by
      have reflection := ActualCorrCovariance.Corr_reflection_readout D a p ell
      -- The native theorem uses its private E and public embed/affineSource.
      -- These are definitionally the SAME original maps as normalP/affineP.
      change (∑ c ∈ (Corr D a p).support,
        ∑ t ∈ (normalP D (Corr D a p c)).support,
          ell (c+t) ((normalP D (Corr D a p c)).coeff t)) =
        ∑ t ∈ (affineP D a p).support,
          ∑ c ∈ (Corr D a ((affineP D a p).coeff t)).support,
            ell (t+c) (Corr D a ((affineP D a p).coeff t) c) at reflection
      exact congrArg (fun z : ℂ => paritySign (chargeNorm D a / 2) * z) reflection
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      rw [correctedRight_Corr]
      apply Finset.sum_congr rfl
      intro c hc
      dsimp [ell]
      congr 2
      simp only [shiftIndex, Nat.cast_add]
      ring

set_option maxHeartbeats 4000000 in
-- Normalize the original finite Corr coefficient convolution.
/-- Replace the actual affine support with the sharp finite interval. All
added terms are zero by native SourceMobius nilpotence and its finite expansion. -/
private theorem corrected_affine_range (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (R : ℕ)
    (hp : IsWeightedHomogeneous (sourceWeight D) p R)
    (e : ℤ) (x y : ActualTensor D hu) :
    correctedLeft D hu a e x y p = paritySign (chargeNorm D a / 2) *
      ∑ j ∈ Finset.range (R+1),
        correctedRight D hu a (shiftIndex D a R j-e) x y
          ((affineP D a p).coeff j) := by
  rw [corrected_affine_support D hu a p R hp]
  congr 1
  apply Finset.sum_subset
  · intro j hj
    apply Finset.mem_range.mpr
    by_contra h
    exact (Polynomial.mem_support_iff.mp hj)
      (affineP_above_weight D a p R j hp (by omega))
  · intro j hj absent
    rw [Polynomial.notMem_support_iff.mp absent, map_zero]

set_option maxHeartbeats 4000000 in
-- Normalize the original finite Corr coefficient convolution.
/-- Full original-field homogeneous inversion, including zero polynomials,
rank zero, all signed e and N, and arbitrary chosen actualForm orientation. -/
theorem actual_corrected_single_inversion (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (R : ℕ)
    (hp : IsWeightedHomogeneous (sourceWeight D) p R)
    (e : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu ((correctedField D hu (Finsupp.single a p)).coeff e x) y =
      paritySign (chargeNorm D a / 2) * (-1 : ℂ)^R *
        ∑ j ∈ Finset.range (R+1),
          actualForm D hu x ((correctedField D hu (Finsupp.single a
            ((j.factorial : ℂ)⁻¹ • (((SourceMobius.sectorL1 D a).toLinearMap^j) p)))).coeff
              (-e-2*chargeNorm D a-4*(R : ℤ)+2*(j : ℤ)) y) := by
  simp only [correctedField_single]
  change correctedLeft D hu a e x y p =
    paritySign (chargeNorm D a / 2) * (-1 : ℂ)^R *
      ∑ j ∈ Finset.range (R+1),
        correctedRight D hu a (-e-2*chargeNorm D a-4*(R : ℤ)+2*(j : ℤ)) x y
          ((j.factorial : ℂ)⁻¹ • (((SourceMobius.sectorL1 D a).toLinearMap^j) p))
  simp only [map_smul]
  have h := corrected_affine_range D hu a p R hp e x y
  simp_rw [affineP_coeff D a p R _ hp, map_smul] at h
  rw [← Finset.smul_sum] at h
  have he (j : ℕ) : shiftIndex D a R j-e =
      -e-2*chargeNorm D a-4*(R : ℤ)+2*(j : ℤ) := by
    dsimp [shiftIndex]
    ring
  simp_rw [he] at h
  simpa only [smul_eq_mul, mul_assoc] using h

/-- The requested monomial statement is a direct use of the stronger
homogeneous theorem. It introduces no additional premise. -/
theorem actual_corrected_monomial_inversion (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (m : Index D →₀ ℕ) (e : ℤ) (x y : ActualTensor D hu) :
    let R := Finsupp.weight (sourceWeight D) m
    actualForm D hu ((correctedField D hu
      (Finsupp.single a (monomial m (1 : ℂ)))).coeff e x) y =
      paritySign (chargeNorm D a / 2) * (-1 : ℂ)^R *
        ∑ j ∈ Finset.range (R+1),
          actualForm D hu x ((correctedField D hu (Finsupp.single a
            ((j.factorial : ℂ)⁻¹ •
              (((SourceMobius.sectorL1 D a).toLinearMap^j) (monomial m (1 : ℂ)))))).coeff
                (-e-2*chargeNorm D a-4*(R : ℤ)+2*(j : ℤ)) y) := by
  exact actual_corrected_single_inversion D hu a _ _
    (isWeightedHomogeneous_monomial (sourceWeight D) m 1 rfl) e x y

end D5.S3.VertexAlgebra.CorrectedInversion
