/- GID: D5/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Exact native environment transport retaining the outside right congruence. -/

import D5.S3.Quantum.TensorNetworks.InteriorSpectralCertificate
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments
open Matrix MvPolynomial
open scoped Matrix ComplexOrder
open PeriodicMPSParentIntersection (Bond)
open OpenBoundaryMPSInteriorCommonCore (dualTransfer)
open OpenBoundaryMPSDensityRecovery (transfer)
open OpenBoundaryMPSSpectralExtraction
open OpenBoundaryMPSInteriorRootRealization (leftTarget rightTarget G Regular)
open OpenBoundaryMPSQ2PolynomialFiber (coreCoordinates positiveRepresentative sigma eta)
open InteriorSpectralCertificate OpenBoundaryMPSInteriorSpectralNorm

private lemma native_core {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) (i : Fin 2) :
    OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) i =
      (u c e)⁻¹ • ((S c e)⁻¹ * A c i * S c e) := by
  have hu := (spectral_frame hc).2.2.2.2.2.2.1
  have hS := isUnit_iff_ne_zero.mpr (native_extraction hc).1
  have hh := (native_extraction hc).2.2.2.2.2.2.2.1 i
  rw [Matrix.mul_assoc,hh,Matrix.mul_smul,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hS,
    Matrix.one_mul,smul_smul,inv_mul_cancel₀ hu,one_smul]

private lemma dual_covariance (A C : Fin 2 → Bond) (T : Bond) (v : ℂ)
    (hT : IsUnit T.det) (hC : ∀ i, C i = v • (T⁻¹*A i*T)) (X : Bond) :
    dualTransfer C (Tᴴ*X*T) = (star v*v) • (Tᴴ*dualTransfer A X*T) := by
  have hcancel : (T⁻¹)ᴴ*Tᴴ = 1 := by
    rw [← conjTranspose_mul,Matrix.mul_nonsing_inv _ hT,conjTranspose_one]
  simp only [dualTransfer,hC,conjTranspose_smul,conjTranspose_mul,
    smul_mul_assoc,mul_smul_comm,smul_smul,Matrix.mul_sum,Matrix.sum_mul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  · ring
  · simp only [Matrix.mul_assoc,← Matrix.mul_assoc (T⁻¹)ᴴ Tᴴ,hcancel,Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_left _ _ hT]

private lemma right_covariance (A C : Fin 2 → Bond) (T : Bond) (v : ℂ)
    (hT : IsUnit T.det) (hC : ∀ i, C i = v • (T⁻¹*A i*T)) (X : Bond) :
    transfer C (T⁻¹*X*(T⁻¹)ᴴ) = (v*star v) • (T⁻¹*transfer A X*(T⁻¹)ᴴ) := by
  have hcancel : (T⁻¹)ᴴ*Tᴴ = 1 := by
    rw [← conjTranspose_mul,Matrix.mul_nonsing_inv _ hT,conjTranspose_one]
  simp only [transfer,hC,conjTranspose_smul,conjTranspose_mul,
    smul_mul_assoc,mul_smul_comm,smul_smul,Matrix.mul_sum,Matrix.sum_mul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  · ring
  · simp only [Matrix.mul_assoc,Matrix.mul_nonsing_inv_cancel_left _ _ hT,
      ← Matrix.mul_assoc (T⁻¹)ᴴ Tᴴ,hcancel,Matrix.one_mul]

private lemma dual_iterates (A C : Fin 2 → Bond) (T : Bond) (v : ℂ)
    (hT : IsUnit T.det) (hC : ∀ i, C i = v • (T⁻¹*A i*T)) (X : Bond) (k : ℕ) :
    (dualTransfer C)^[k] (Tᴴ*X*T) =
      (star v*v)^k • (Tᴴ*(dualTransfer A)^[k] X*T) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    have hlinear (a : ℂ) (Y : Bond) : dualTransfer C (a • Y) = a • dualTransfer C Y := by
      simp [dualTransfer]
    rw [hlinear,dual_covariance A C T v hT hC,smul_smul,pow_succ,
      Function.iterate_succ_apply']

private lemma right_iterates (A C : Fin 2 → Bond) (T : Bond) (v : ℂ)
    (hT : IsUnit T.det) (hC : ∀ i, C i = v • (T⁻¹*A i*T)) (X : Bond) (k : ℕ) :
    (transfer C)^[k] (T⁻¹*X*(T⁻¹)ᴴ) =
      (v*star v)^k • (T⁻¹*(transfer A)^[k] X*(T⁻¹)ᴴ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,
      OpenBoundaryMPSInteriorRootRealization.transfer_smul,
      right_covariance A C T v hT hC,smul_smul,pow_succ,
      Function.iterate_succ_apply']

/-- Both true native environments, with the central G-square kept outside the right iterate. -/
theorem native_environment_transport {c : Fin 5 → ℂ} {e : ℂ}
    (hc : Admissible c e) (l r : Fin 2 → ℂ) (N p q : ℕ) :
    leftTarget (sector c e) (z c e) (l ᵥ* S c e) p =
      ((Complex.normSq (u c e))^p)⁻¹ •
        ((S c e)ᴴ*(dualTransfer (A c))^[p] (vecMulVec (star l) l)*S c e) ∧
    rightTarget (sector c e) (z c e) (nativeRight c e N r) q =
      G (sector c e) (z c e)^2 *
        ((Complex.normSq (u c e)^N * (Complex.normSq (u c e)^q)⁻¹) •
          ((S c e)⁻¹*(transfer (A c))^[q] (vecMulVec r (star r))*((S c e)⁻¹)ᴴ)) *
        (G (sector c e) (z c e)^2)ᴴ := by
  have hS := isUnit_iff_ne_zero.mpr (native_extraction hc).1
  have hl : vecMulVec (star (l ᵥ* S c e)) (l ᵥ* S c e) =
      (S c e)ᴴ*vecMulVec (star l) l*S c e := by
    rw [mul_vecMulVec,vecMulVec_mul,← star_vecMul]
  have hr : vecMulVec (nativeRight c e N r) (star (nativeRight c e N r)) =
      (u c e^N*star (u c e^N)) •
        ((S c e)⁻¹*vecMulVec r (star r)*((S c e)⁻¹)ᴴ) := by
    rw [nativeRight,star_smul,smul_vecMulVec,vecMulVec_smul,smul_smul]
    rw [mul_vecMulVec,vecMulVec_mul,← star_mulVec]
  have hnorm : (u c e)⁻¹*star ((u c e)⁻¹) =
      ((Complex.normSq (u c e))⁻¹ : ℝ) := by
    rw [RCLike.star_def,Complex.mul_conj,map_inv₀,Complex.ofReal_inv]
  constructor
  · rw [leftTarget,hl,dual_iterates (A c) _ (S c e) (u c e)⁻¹ hS (native_core hc)]
    rw [mul_comm (star _),hnorm,← Complex.ofReal_pow,← inv_pow]
    rfl
  · rw [rightTarget,hr,OpenBoundaryMPSInteriorRootRealization.iterate_smul _
      (OpenBoundaryMPSInteriorRootRealization.transfer_smul _) q,
      right_iterates (A c) _ (S c e) (u c e)⁻¹ hS (native_core hc),smul_smul,
      hnorm,← Complex.ofReal_pow,← inv_pow]
    have hh : u c e^N*star (u c e^N) = (Complex.normSq (u c e)^N : ℝ) := by
      rw [RCLike.star_def,Complex.mul_conj,map_pow]
    rw [hh,← Complex.ofReal_mul]
    rfl

private lemma boundary_W (x : Fin 13 → ℝ) :
    Matrix.det (Matrix.of (fun a i : Fin 2 => (A (coreCoordinates x) i *ᵥ ![1,eta x]) a)) =
      eval (fun i => (x i : ℂ)) canonicalW := by
  have hc (i : Fin 5) : eval (fun j => (x j : ℂ)) (canonicalCorePoly i) = coreCoordinates x i := by
    apply Complex.ext <;> simp [canonicalCorePoly,
      OpenBoundaryMPSQ2PolynomialFiber.coreVariable,coreCoordinates]
  have he : eval (fun i => (x i : ℂ)) canonicalEtaPoly = eta x :=
    OpenBoundaryMPSQ2PolynomialFiber.evaluate_eta x
  rw [Matrix.det_fin_two]
  simp [canonicalW,hc,he,A,OpenBoundaryMPSTwoSiteMinimality.core,
    det_fin_two,Matrix.of_apply,mulVec,dotProduct,Fin.sum_univ_two]
  ring

/-- The same certificate supplies BOTH PosDef premises of the actual native ambiguity theorem. -/
theorem certificate_positive_targets (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (x : Fin 13 → ℝ) (e : ℂ) (hsigma : 0 < sigma x) (hP : eval x (P p q) ≠ 0)
    (he : e^2 = D (coreCoordinates x)) :
    (leftTarget (sector (coreCoordinates x) e) (z (coreCoordinates x) e)
      (nativeLeft (coreCoordinates x) e) p).PosDef ∧
    (rightTarget (sector (coreCoordinates x) e) (z (coreCoordinates x) e)
      (nativeRight (coreCoordinates x) e ((p+2)+q)
        ((Real.sqrt (sigma x) : ℂ) • ![1,eta x])) q).PosDef := by
  obtain ⟨hc,hs,hb⟩ := certificate_native p q x e hsigma hP he
  have hfactor : eval x (X 10)*eval x canonicalJden*eval x canonicalWnorm*
      eval x (normg (g p q) discrR discrI) ≠ 0 := by
    simpa only [P,spectralCertificate,map_mul] using hP
  have hw := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hfactor).1).2
  have hc2 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc.2).1).1).1
  have h0 : (OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 0).det ≠ 0 := by
    have hh : (OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 0).det =
        -coreCoordinates x 2 := by
      simp [OpenBoundaryMPSTwoSiteMinimality.core,positiveRepresentative,det_fin_two]
      ring
    rw [hh]
    exact neg_ne_zero.mpr hc2
  have hW : Matrix.det (Matrix.of (fun a i : Fin 2 =>
      (A (coreCoordinates x) i *ᵥ ![1,eta x]) a)) ≠ 0 := by
    intro hz
    rw [boundary_W] at hz
    apply hw
    simp only [canonicalWnorm,map_add,map_pow,(OpenBoundaryMPSDensityGenericity.coefficient_eval
      canonicalW x).1,(OpenBoundaryMPSDensityGenericity.coefficient_eval canonicalW x).2,hz]
    norm_num
  have hpos := OpenBoundaryMPSInteriorGenericity.positive_iterates x hsigma h0 hW
  have hl := (hpos p hp).1
  have hr := (hpos q hq).2
  have hright : OpenBoundaryMPSTwoSiteMinimality.right (positiveRepresentative x) =
      (Real.sqrt (sigma x) : ℂ) • ![1,eta x] := by
    ext i
    fin_cases i <;> simp [OpenBoundaryMPSTwoSiteMinimality.right,positiveRepresentative]
  rw [hright] at hr
  have hu := (spectral_frame hc).2.2.2.2.2.2.1
  have ha : 0 < Complex.normSq (u (coreCoordinates x) e) := Complex.normSq_pos.mpr hu
  have hS := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (native_extraction hc).1)
  have hSi : IsUnit (S (coreCoordinates x) e)⁻¹ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simpa only [det_nonsing_inv,Ring.inverse_eq_inv] using
      (isUnit_iff_ne_zero.mpr (native_extraction hc).1).inv
  have ht := native_environment_transport hc (L (coreCoordinates x))
    ((Real.sqrt (sigma x) : ℂ) • ![1,eta x]) ((p+2)+q) p q
  constructor
  · rw [nativeLeft,ht.1]
    exact (hl.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hS)).smul
      (inv_pos.mpr (pow_pos ha p))
  · rw [ht.2]
    have hinner := (hr.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit hSi)).smul
        (mul_pos (pow_pos ha ((p+2)+q)) (inv_pos.mpr (pow_pos ha q)))
    have hz := (native_extraction hc).2.1
    have hg : IsUnit (G (sector (coreCoordinates x) e) (z (coreCoordinates x) e)^2) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [det_pow]
      apply IsUnit.pow
      apply isUnit_iff_ne_zero.mpr
      have hd : (G (sector (coreCoordinates x) e) (z (coreCoordinates x) e)).det =
          OpenBoundaryMPSInteriorRootRealization.delta (sector (coreCoordinates x) e) *
            z (coreCoordinates x) e := by
        simp [G,OpenBoundaryMPSInteriorRootRealization.delta,
          OpenBoundaryMPSInteriorRootRealization.alpha,OpenBoundaryMPSInteriorRootRealization.beta,
          det_fin_two]
        ring
      rw [hd]
      exact mul_ne_zero (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs.1).1).1 hz
    exact hinner.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hg)

end D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments
