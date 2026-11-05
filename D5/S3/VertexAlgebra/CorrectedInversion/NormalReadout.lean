/- GID: D5/S3/VertexAlgebra/CorrectedInversion/NormalReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/CorrectedInversion/NormalReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original triangular normal transpose as finite polynomial coordinates. -/
import D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
import D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint

/-!
# Original normal reflection in finite polynomial coordinates

The actual signed current and normal transpose are those of
`HalfFock.NormalScalarTranspose`. The dependent JetTuple product expansion
identifies their original triangular sum with the original Corr normalReflection.
The form retains its given bilinear orientation, arbitrary signed coefficient
indices and charge norm. No symmetry or positivity assumption is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.CorrectedInversion
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockFiniteCorrection LatticeHalfFockCorrectedField
open TwistedGround.ActualChargedAdjoint HalfFock.NormalScalarTranspose
open HalfFock
open MvPolynomial

/-- Polynomial coordinates of the canonical normal reflection on the original
oscillator inclusion. No new reflection or correction operation is defined. -/
def normalP (D : LatticeData) : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D) :=
  (optionEquivLeft ℂ (Index D)).toAlgHom.comp
    ((ActualCorrCovariance.normalReflection D).comp (ActualCorrCovariance.embed D))

/-- Polynomial coordinates of the canonical affine SOURCE map. In particular,
this is not corrLift regarded as an algebra homomorphism. -/
def affineP (D : LatticeData) (a : Charge D) : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D) :=
  (optionEquivLeft ℂ (Index D)).toAlgHom.comp (ActualCorrCovariance.affineSource D a)

/- Reuse the original public coefficient evaluator as a linear map. -/

def normalRight (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (e : ℤ) (x y : ActualTensor D hu) : Module.Dual ℂ (Oscillator D) where
  toFun p := actualForm D hu x ((polynomialField D hu a p).coeff e y)
  map_add' p q :=
    ((actualForm D hu x).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e y).comp (polynomialField D hu a))).map_add p q
  map_smul' c p :=
    ((actualForm D hu x).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e y).comp (polynomialField D hu a))).map_smul c p

def normalLeft (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (e : ℤ) (x y : ActualTensor D hu) : Module.Dual ℂ (Oscillator D) where
  toFun p := actualForm D hu ((polynomialField D hu a p).coeff e x) y
  map_add' p q :=
    (((actualForm D hu).flip y).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e x).comp (polynomialField D hu a))).map_add p q
  map_smul' c p :=
    (((actualForm D hu).flip y).comp
      ((LatticeHalfFockFockNormalField.coefficientAt D hu e x).comp (polynomialField D hu a))).map_smul c p

def shiftIndex (D : LatticeData) (a : Charge D) (R j : ℕ) : ℤ :=
  -2 * chargeNorm D a - 4 * (R : ℤ) + 2 * (j : ℤ)

private theorem wordPolynomial_prod (D : LatticeData) (w : List (Index D)) :
    wordPolynomial D w = (w.map (fun i => (X i : Oscillator D))).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [wordPolynomial, ih]

/- Reuse the original public normal-transpose helper identities. -/

private theorem loss_cons (D : LatticeData) (i : Index D) (w : List (Index D))
    (s : Fin (i.2 + 1)) (t : JetTuple D w) :
    weightLoss D (i::w) (s,t) = i.2-s.val + weightLoss D w t := by
  have hs := s.isLt
  have ht := HalfFock.NormalScalarTranspose.lowerWord_weight_le D w t
  simp only [wordWeight] at ht
  simp only [weightLoss, wordWeight, lowerWord, List.map_cons, List.sum_cons,
    sourceWeight]
  omega

set_option maxHeartbeats 4000000 in
-- Allow normalization of the finite dependent polynomial sums.
/-- Restore exactly the signed lower jets of the original normal transpose as one
ordinary finite polynomial. No tuple choices are identified or discarded. -/
theorem normalP_X (D : LatticeData) (i : Index D) :
    normalP D (X i) = ∑ s : Fin (i.2+1),
      Polynomial.monomial (i.2-s.val)
        (((-1 : ℂ)^(i.2+1) * ((i.2+1).choose (s.val+1) : ℂ)) • X (i.1,s.val)) := by
  simp only [normalP, AlgHom.comp_apply, ActualCorrCovariance.embed, rename_X,
    ActualCorrCovariance.normalReflection, aeval_X, Option.elim_some]
  change optionEquivLeft ℂ (Index D) (∑ s ∈ Finset.range (i.2+1),
    C ((-1 : ℂ)^(i.2+1) * ((i.2+1).choose (s+1) : ℂ)) *
      X none ^ (i.2-s) * X (some (i.1,s))) = _
  simp only [map_sum, map_mul, map_pow, optionEquivLeft_C,
    optionEquivLeft_X_none, optionEquivLeft_X_some]
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ =>
    Polynomial.monomial (i.2-s)
      (((-1 : ℂ)^(i.2+1) * ((i.2+1).choose (s+1) : ℂ)) • (X (i.1,s) : Oscillator D)))]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, smul_eq_C_mul, map_mul, map_pow]
  ring

set_option maxHeartbeats 4000000 in
-- Allow normalization of the finite dependent polynomial sums.
/-- Genuine finite product expansion over the EXISTING dependent JetTuple.
Repeated source letters remain separate occurrences until polynomial addition. -/
private theorem normalP_word (D : LatticeData) (w : List (Index D)) :
    normalP D (wordPolynomial D w) =
      ∑ s : JetTuple D w, Polynomial.monomial (weightLoss D w s)
        (triangleCoefficient D w s • wordPolynomial D (lowerWord D w s)) := by
  induction w with
  | nil => simp [wordPolynomial, weightLoss, wordWeight, lowerWord, triangleCoefficient]
  | cons i w ih =>
    rw [wordPolynomial, map_mul, normalP_X, ih]
    simp only [Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    rw [Polynomial.monomial_mul_monomial, loss_cons]
    congr 1
    change (((-1 : ℂ)^(i.2+1) * ((i.2+1).choose (s.val+1) : ℂ)) • X (i.1,s.val)) *
      (triangleCoefficient D w t • wordPolynomial D (lowerWord D w t)) =
      (((-1 : ℂ)^(i.2+1) * ((i.2+1).choose (s.val+1) : ℂ)) *
        triangleCoefficient D w t) •
          (X (i.1,s.val) * wordPolynomial D (lowerWord D w t))
    simp only [smul_eq_C_mul, map_mul]
    ring

set_option maxHeartbeats 4000000 in
-- Allow normalization of the finite dependent polynomial sums.
/-- Group the original monomial transpose as coefficients of the canonical
normal-reflection polynomial. The triangular choices retain all occurrences. -/
theorem normal_homogeneous_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (p : Oscillator D) (R : ℕ)
    (hp : IsWeightedHomogeneous (sourceWeight D) p R)
    (e : ℤ) (x y : ActualTensor D hu) :
    normalLeft D hu a e x y p = paritySign (chargeNorm D a / 2) *
      ActualCorrCovariance.scalarReadout D (fun j => normalRight D hu a (shiftIndex D a R j-e) x y)
        (normalP D p) := by
  classical
  let ell := fun j => normalRight D hu a (shiftIndex D a R j-e) x y
  have single (m : Index D →₀ ℕ) (hm : m ∈ p.support) :
      normalLeft D hu a e x y (monomial m 1) =
        paritySign (chargeNorm D a / 2) *
          ActualCorrCovariance.scalarReadout D ell (normalP D (monomial m 1)) := by
    have hw : Finsupp.weight (sourceWeight D) m = R := hp (mem_support_iff.mp hm)
    have hw' : wordWeight D (LatticeHalfFockFockNormalField.occurrences D m) = R :=
      (LatticeHalfFockFiniteCorrection.wordWeight_occurrences D m).trans hw
    have hword : wordPolynomial D (LatticeHalfFockFockNormalField.occurrences D m) =
        monomial m (1 : ℂ) :=
      (wordPolynomial_prod D _).trans (LatticeAllStateField.occurrences_product D m)
    have hP := normalP_word D (LatticeHalfFockFockNormalField.occurrences D m)
    rw [hword] at hP
    rw [hP, map_sum, Finset.mul_sum]
    change actualForm D hu ((polynomialField D hu a (monomial m 1)).coeff e x) y = _
    rw [actual_polynomial_monomial_transpose]
    apply Finset.sum_congr rfl
    intro s hs
    rw [← Polynomial.C_mul_X_pow_eq_monomial,
      ActualCorrCovariance.scalarReadout_monomial, map_smul]
    have he : transposeExponent D a (LatticeHalfFockFockNormalField.occurrences D m) s e =
        shiftIndex D a R (weightLoss D (LatticeHalfFockFockNormalField.occurrences D m) s)-e := by
      have h := HalfFock.NormalScalarTranspose.transposeExponent_loss D a (LatticeHalfFockFockNormalField.occurrences D m) s e
      rw [hw'] at h
      calc
        _ = -e-2*chargeNorm D a-4*(R : ℤ)+
            2*(weightLoss D (LatticeHalfFockFockNormalField.occurrences D m) s : ℤ) := h
        _ = _ := by dsimp [shiftIndex]; ring
    rw [he]
    dsimp [ell, normalRight, chargeNorm]
    ring
  have expand : p = ∑ m ∈ p.support, p.coeff m • monomial m (1 : ℂ) := by
    simpa only [smul_monomial, smul_eq_mul, mul_one] using p.as_sum
  let F := normalLeft D hu a e x y
  let G := (ActualCorrCovariance.scalarReadout D ell).comp (normalP D).toLinearMap
  have hF := congrArg F expand
  have hG := congrArg G expand
  rw [map_sum] at hF hG
  change F p = paritySign (chargeNorm D a / 2) * G p
  rw [hF, hG, Finset.mul_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [single m hm]
  dsimp [G]
  ring

end D5.S3.VertexAlgebra.CorrectedInversion
