/- GID: D5/S3/VertexAlgebra/CorrectedInversion/SignedSource
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/CorrectedInversion/SignedSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original signed affine source coefficients as finite L1 divided powers. -/
import D5.S3.VertexAlgebra.CorrectedInversion.NormalReadout
import D5.S3.VertexAlgebra.SourceMobius.Coordinates

/-!
# Signed affine source and the original L1 flow

The original affineSource is identified with flowPolynomial after the
source-weight sign, by finite generator coordinates and algebra-homomorphism
extensionality. Homogeneity supplies the single sign (-1)^R, independent of
the divided-power index. Native SourceMobius supplies the original derivation,
factorial coefficients and nilpotence; no desired covariance is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.CorrectedInversion
open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection MvPolynomial
open HalfFock

/- Reuse the original public finite generator calculations. -/

set_option maxHeartbeats 4000000 in
-- Normalize the finite factorial and binomial coordinate sums.
/-- Finite polynomial-coordinate conversion of native coefficients. This is a
consumed helper, not a second flow definition or a polynomial ODE proof. -/
private theorem native_polynomial_X (D : LatticeData) (a : Charge D)
    (i : Fin D.rank) (r : ℕ) :
    SourceMobius.flowPolynomial D a (X (i,r)) =
      (∑ s : Fin (r+1), Polynomial.monomial (r-s.val)
        (((r+1).choose (s.val+1) : ℂ) • X (i,s.val))) +
      Polynomial.monomial (r+1) (C (bilinear D (unitCharge D i) a : ℂ)) := by
  classical
  have killed : ((SourceMobius.sectorL1 D a).toLinearMap ^ ((r+1)+1))
      (X (i,r)) = 0 := by
    simpa [MvPolynomial.X, Finsupp.weight_single, sourceWeight] using
      SourceMobius.sectorL1_monomial_bound D a (Finsupp.single (i,r) 1) (1 : ℂ)
  rw [SourceMobius.flowPolynomial_eq_sum D a (X (i,r)) (r+1) killed,
    Finset.sum_range_succ, SourceMobius.variable_power_charge]
  have hf : ((r+1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r+1)
  rw [smul_smul, inv_mul_cancel₀ hf, one_smul]
  congr 1
  calc
    _ = ∑ n ∈ Finset.range (r+1), Polynomial.monomial n
        (((r+1).choose n : ℂ) • X (i,r-n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [SourceMobius.variable_power D a i r n (by
        have := Finset.mem_range.mp hn
        omega), smul_smul, Nat.descFactorial_eq_factorial_mul_choose]
      congr 2
      push_cast
      have hn0 : (n.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp
    _ = _ := by
      rw [← Finset.sum_range_reflect (fun n => Polynomial.monomial n
        (((r+1).choose n : ℂ) • (X (i,r-n) : Oscillator D))) (r+1),
        Fin.sum_univ_eq_sum_range (fun s : ℕ => Polynomial.monomial (r-s)
          (((r+1).choose (s+1) : ℂ) • (X (i,s) : Oscillator D)))]
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : s ≤ r := by have := Finset.mem_range.mp hs; omega
      have reflected : r-(r-s) = s := by omega
      have chosen : (r+1).choose (r-s) = (r+1).choose (s+1) := by
        apply Nat.choose_symm_of_eq_add
        omega
      simp only [Nat.add_sub_cancel, reflected, chosen]

private def weightSign (D : LatticeData) : Oscillator D →ₐ[ℂ] Oscillator D :=
  aeval (fun i => (-1 : ℂ)^(sourceWeight D i) • X i)

set_option maxHeartbeats 4000000 in
-- Normalize the finite polynomial source substitution.
private theorem weightSign_monomial (D : LatticeData) (m : Index D →₀ ℕ) (z : ℂ) :
    weightSign D (monomial m z) =
      (-1 : ℂ)^(Finsupp.weight (sourceWeight D) m) • monomial m z := by
  induction m using Finsupp.induction with
  | zero => simp [weightSign]
  | single_add i n m hi hn ih =>
    rw [monomial_single_add, map_mul, map_pow, ih, map_add,
      Finsupp.weight_single]
    simp [weightSign, smul_pow, pow_add, pow_mul]
    rw [smul_smul]
    congr 1
    simp only [← pow_mul]
    rw [Nat.mul_comm]
    ring

private theorem weightSign_homogeneous (D : LatticeData) (p : Oscillator D) (R : ℕ)
    (hp : IsWeightedHomogeneous (sourceWeight D) p R) :
    weightSign D p = (-1 : ℂ)^R • p := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp_rw [weightSign_monomial]
  conv_rhs => rw [p.as_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hp (mem_support_iff.mp hm)]

set_option maxHeartbeats 4000000 in
-- Normalize the finite polynomial source substitution.
private theorem affineP_eq_native (D : LatticeData) (a : Charge D) (p : Oscillator D) :
    affineP D a p = SourceMobius.flowPolynomial D a (weightSign D p) := by
  have maps : affineP D a = (SourceMobius.flowPolynomial D a).comp (weightSign D) := by
    apply MvPolynomial.algHom_ext
    intro i
    have hx : affineP D a (X i) = normalP D (X i) +
        Polynomial.monomial (i.2+1)
          ((-1 : ℂ)^(i.2+1) • C (bilinear D (unitCharge D i.1) a : ℂ)) := by
      simp only [affineP, normalP, AlgHom.comp_apply,
        ActualCorrCovariance.affineSource, ActualCorrCovariance.embed, rename_X,
        ActualCorrCovariance.affineReflection, ActualCorrCovariance.normalReflection,
        aeval_X, Option.elim_some, map_add]
      congr 1
      change optionEquivLeft ℂ (Index D) (C ((-1 : ℂ)^(i.2+1) *
        (bilinear D (unitCharge D i.1) a : ℂ)) * X none ^ (i.2+1)) = _
      simp only [map_mul, map_pow, optionEquivLeft_C, optionEquivLeft_X_none]
      simp only [← Polynomial.C_mul_X_pow_eq_monomial, smul_eq_C_mul, map_mul, map_pow]
    change affineP D a (X i) = SourceMobius.flowPolynomial D a (weightSign D (X i))
    rw [hx, normalP_X]
    have native := native_polynomial_X D a i.1 i.2
    change SourceMobius.flowPolynomial D a (X i) = _ at native
    simp only [weightSign, aeval_X, map_smul]
    rw [native]
    simp only [smul_add, Finset.smul_sum, Polynomial.smul_monomial, smul_smul, sourceWeight]
  exact AlgHom.congr_fun maps p

/-- Exact signed divided powers, consuming native flowPolynomial_coeff directly. -/
theorem affineP_coeff (D : LatticeData) (a : Charge D) (p : Oscillator D) (R k : ℕ)
    (hp : IsWeightedHomogeneous (sourceWeight D) p R) :
    (affineP D a p).coeff k = (-1 : ℂ)^R •
      ((k.factorial : ℂ)⁻¹ • (((SourceMobius.sectorL1 D a).toLinearMap^k) p)) := by
  rw [affineP_eq_native, weightSign_homogeneous D p R hp, map_smul,
    Polynomial.coeff_smul, SourceMobius.flowPolynomial_coeff]

/-- Truncation uses the native finite polynomial expansion at its native
weighted-degree nilpotence bound. No Corr-private homogeneity or new nilpotence
induction is required, including when the homogeneous polynomial is zero. -/
theorem affineP_above_weight (D : LatticeData) (a : Charge D) (p : Oscillator D) (R k : ℕ)
    (hp : IsWeightedHomogeneous (sourceWeight D) p R) (hk : R < k) :
    (affineP D a p).coeff k = 0 := by
  classical
  have degree_le : weightedTotalDegree (sourceWeight D) p ≤ R := by
    apply Finset.sup_le
    intro m hm
    exact le_of_eq (hp (mem_support_iff.mp hm))
  rw [affineP_eq_native, weightSign_homogeneous D p R hp, map_smul,
    Polynomial.coeff_smul,
    SourceMobius.flowPolynomial_eq_sum D a p _ (SourceMobius.sectorL1_degree_bound D a p),
    Polynomial.finsetSum_coeff]
  have hz : (∑ n ∈ Finset.range (weightedTotalDegree (sourceWeight D) p + 1),
      (Polynomial.monomial n ((n.factorial : ℂ)⁻¹ •
        (((SourceMobius.sectorL1 D a).toLinearMap^n) p))).coeff k) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hne : n ≠ k := by have := Finset.mem_range.mp hn; omega
    simp [Polynomial.coeff_monomial, hne]
  rw [hz, smul_zero]

end D5.S3.VertexAlgebra.CorrectedInversion
