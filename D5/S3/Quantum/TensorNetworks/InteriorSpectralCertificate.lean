/- GID: D5/S3/Quantum/TensorNetworks/InteriorSpectralCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/InteriorSpectralCertificate
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Equiv]
   utility: none
   digest: The actual Jacobian clearing and literal canonical spectral exclusion certificate. -/

import D5.S3.Quantum.TensorNetworks.InteriorSpectralCoordinates
import D5.S3.Quantum.TensorNetworks.InteriorSpectralReduction

/-! Real clearing is applied only at physical admissible points. The full native
right column includes the scalar u to the complete state length. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.InteriorSpectralCertificate
open Matrix MvPolynomial
open scoped Matrix BigOperators ComplexOrder
open InteriorSpectralCoordinates
open OpenBoundaryMPSInteriorSpectralNorm
open OpenBoundaryMPSDensityGenericity (realCoeff imagCoeff coefficient_eval)
open OpenBoundaryMPSInteriorRootRealization
open OpenBoundaryMPSInteriorCommonCore (rawInterior)
open OpenBoundaryMPSMarginalBirationality (mpsState openBoundaryMPS)
open PeriodicMPSParentIntersection (Word)

private lemma clearing_exists (p q : ℕ) :
    ∃ H B : RP, ∀ a : Fin 15 → ℝ,
      (∀ i, eval a (denominator ((p+2)+q) i) ≠ 0) → eval a B ≠ 0 ∧
      eval (fun i => eval a (numerator ((p+2)+q) i) /
        eval a (denominator ((p+2)+q) i)) (OpenBoundaryMPSInteriorPolynomial.b p q) =
          eval a H / eval a B :=
  OpenBoundaryMPSQ2PolynomialFiber.clear_polynomial
    (OpenBoundaryMPSInteriorPolynomial.b p q) (numerator ((p+2)+q)) (denominator ((p+2)+q))

def H (p q : ℕ) : RP := (clearing_exists p q).choose
def Bclear (p q : ℕ) : RP := (clearing_exists p q).choose_spec.choose

/-- This is the existing real clearing theorem applied to the actual sixteen native entries. -/
theorem clearing_native (p q : ℕ) (x : Fin 13 → ℝ) (e : ℂ)
    (hc : OpenBoundaryMPSSpectralExtraction.Admissible
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) :
    eval (point x e) (Bclear p q) ≠ 0 ∧
    eval (OpenBoundaryMPSInteriorPolynomial.coordinates
      (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeLeft (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeRight
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e ((p+2)+q)
          ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x])
      (OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e))
      (OpenBoundaryMPSInteriorPolynomial.b p q) =
        eval (point x e) (H p q) / eval (point x e) (Bclear p q) := by
  obtain ⟨hd,hcoord⟩ := native_coordinates x e hc ((p+2)+q)
  have hh := (clearing_exists p q).choose_spec.choose_spec (point x e) hd
  rw [hcoord] at hh
  exact hh

def cross : CP :=
  4*c 2*map (starRingEnd ℂ) (c 2) +
    (map (starRingEnd ℂ) (c 4-c 1) + (X 0-C Complex.I*X 1)) * (c 4-c 1-root)

def crossNorm : RP := realCoeff cross ^ 2 + imagCoeff cross ^ 2

def g15 (p q : ℕ) : RP := H p q * crossNorm

def gIter (p q : ℕ) : InteriorSpectralReduction.GPoly :=
  sumRingEquiv ℝ (Fin 2) (Fin 13)
    (rename (finSumFinEquiv : Fin 2 ⊕ Fin 13 ≃ Fin 15).symm (g15 p q))

def discrR : CanonicalPoly := realCoeff canonicalD
def discrI : CanonicalPoly := imagCoeff canonicalD

def g (p q : ℕ) : Fin 4 → CanonicalPoly :=
  InteriorSpectralReduction.coefficients (gIter p q) discrR discrI

/-- A literal REAL13 certificate for each fixed pair of lengths. Nonvanishing is proved in
InteriorSpectralWitness. -/
def P (p q : ℕ) : CanonicalPoly := spectralCertificate (g p q) discrR discrI

private lemma bar_eval (a : Fin 15 → ℝ) (f : CP) :
    eval (fun i => (a i : ℂ)) (map (starRingEnd ℂ) f) =
      star (eval (fun i => (a i : ℂ)) f) := by
  simpa [Function.comp_def] using
    (MvPolynomial.map_eval (starRingEnd ℂ) (fun i => (a i : ℂ)) f).symm

private lemma cross_eval (x : Fin 13 → ℝ) (e : ℂ) :
    eval (fun i => (point x e i : ℂ)) cross =
      4*OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x 2 *
        star (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x 2) +
      (star (OpenBoundaryMPSSpectralExtraction.h
          (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)) + star e) *
        (OpenBoundaryMPSSpectralExtraction.h
          (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)-e) := by
  simp only [cross,map_add,map_sub,map_mul,map_ofNat,bar_eval]
  simp [c,liftBase,root,OpenBoundaryMPSQ2PolynomialFiber.coreVariable,
    OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates,OpenBoundaryMPSSpectralExtraction.h,
    point,Fin.append,Fin.addCases,eval_rename]
  apply Complex.ext <;> simp <;> ring

/-- The division-free cross is exactly the native Schur cross with its nonzero multiplier. -/
theorem cross_native (x : Fin 13 → ℝ) (e : ℂ)
    (hc2 : OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x 2 ≠ 0) :
    eval (fun i => (point x e i : ℂ)) cross =
      (4*Complex.normSq (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x 2) : ℂ) *
        (1+star (OpenBoundaryMPSSpectralExtraction.lam
          (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)*
          OpenBoundaryMPSSpectralExtraction.mu
            (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) := by
  rw [cross_eval]
  have hn (z : ℂ) : (Complex.normSq z : ℂ) = z*star z := by
    rw [RCLike.star_def,Complex.mul_conj]
  rw [hn]
  have hstar : star (OpenBoundaryMPSSpectralExtraction.lam
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) =
      (star (OpenBoundaryMPSSpectralExtraction.h
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)) + star e) /
        (2*star (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x 2)) := by
    change (starRingEnd ℂ) ((_+_)/(2*_)) = _
    simp only [map_div₀,map_add,map_mul,map_ofNat]
    rfl
  rw [hstar,OpenBoundaryMPSSpectralExtraction.mu]
  field_simp [hc2,star_ne_zero.mpr hc2]
  <;> ring

/-- The real polynomial is the actual complex squared modulus, on real physical points. -/
theorem crossNorm_eval (a : Fin 15 → ℝ) :
    eval a crossNorm = Complex.normSq (eval (fun i => (a i : ℂ)) cross) := by
  simp only [crossNorm,map_add,map_pow,(coefficient_eval cross a).1,
    (coefficient_eval cross a).2,Complex.normSq_apply]
  ring

private lemma split_evaluation (G : RP) (x : Fin 13 → ℝ) (e : ℂ) :
    eval₂ (eval x) ![e.re,e.im]
      (sumRingEquiv ℝ (Fin 2) (Fin 13)
        (rename (finSumFinEquiv : Fin 2 ⊕ Fin 13 ≃ Fin 15).symm G)) =
      eval (point x e) G := by
  have hs (F : MvPolynomial (Fin 2 ⊕ Fin 13) ℝ) :
      eval₂ (eval x) ![e.re,e.im] (sumRingEquiv ℝ (Fin 2) (Fin 13) F) =
        eval (Sum.elim ![e.re,e.im] x) F := by
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add a b ha hb => simp only [map_add,eval₂_add,ha,hb]
    | mul_X a i ha =>
      cases i <;> simp [map_mul,ha]
  rw [hs,eval_rename]
  have hv : (Sum.elim ![e.re,e.im] x ∘
      (finSumFinEquiv : Fin 2 ⊕ Fin 13 ≃ Fin 15).symm) = point x e := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> rfl
    · intro j
      change Sum.elim ![e.re,e.im] x
        ((finSumFinEquiv : Fin 2 ⊕ Fin 13 ≃ Fin 15).symm (Fin.natAdd 2 j)) = _
      rw [@finSumFinEquiv_symm_apply_natAdd 2 13 j]
      exact (Fin.append_right _ _ _).symm
  rw [hv]

private lemma discriminant_eval (x : Fin 13 → ℝ) :
    eval x discrR = (OpenBoundaryMPSSpectralExtraction.D
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)).re ∧
    eval x discrI = (OpenBoundaryMPSSpectralExtraction.D
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)).im := by
  have hd : eval (fun i => (x i : ℂ)) canonicalD =
      OpenBoundaryMPSSpectralExtraction.D (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) := by
    apply Complex.ext <;> simp [canonicalD,canonicalH,canonicalCorePoly,
      OpenBoundaryMPSQ2PolynomialFiber.coreVariable,
      OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates,OpenBoundaryMPSSpectralExtraction.D,
      OpenBoundaryMPSSpectralExtraction.h,pow_two,Complex.mul_re,Complex.mul_im]

  exact ⟨(coefficient_eval canonicalD x).1.trans (congrArg Complex.re hd),
    (coefficient_eval canonicalD x).2.trans (congrArg Complex.im hd)⟩

/-- The literal finite-support reduction evaluates to the actual REAL15 polynomial. -/
theorem g_evaluation (p q : ℕ) (x : Fin 13 → ℝ) (e : ℂ)
    (he : e^2 = OpenBoundaryMPSSpectralExtraction.D
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)) :
    eval (point x e) (g15 p q) = eval x (g p q 0) + eval x (g p q 1)*e.re +
      eval x (g p q 2)*e.im + eval x (g p q 3)*Complex.normSq e := by
  have hd := discriminant_eval x
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [pow_two,Complex.mul_re,Complex.mul_im] at hre him
  have hh := InteriorSpectralReduction.coefficients_evaluation (eval x) discrR discrI
    e.re e.im (Complex.normSq e) (gIter p q)
  rw [hd.1,hd.2] at hh
  have hxx : e.re*e.re = eval x (C (1/2)) *
      (Complex.normSq e + (OpenBoundaryMPSSpectralExtraction.D
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)).re) := by
    simp only [eval_C,Complex.normSq_apply]; nlinarith [hre]
  have hyy : e.im*e.im = eval x (C (1/2)) *
      (Complex.normSq e - (OpenBoundaryMPSSpectralExtraction.D
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)).re) := by
    simp only [eval_C,Complex.normSq_apply]; nlinarith [hre]
  have hxy : e.re*e.im = eval x (C (1/2)) *
      (OpenBoundaryMPSSpectralExtraction.D
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)).im := by
    simp only [eval_C]; nlinarith [him]
  have hrx : Complex.normSq e*e.re =
      (OpenBoundaryMPSSpectralExtraction.D
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)).re*e.re +
      (OpenBoundaryMPSSpectralExtraction.D
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)).im*e.im := by
    simp only [Complex.normSq_apply]
    linear_combination e.re*hre+e.im*him
  have hry : Complex.normSq e*e.im =
      (OpenBoundaryMPSSpectralExtraction.D
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)).im*e.re -
      (OpenBoundaryMPSSpectralExtraction.D
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)).re*e.im := by
    simp only [Complex.normSq_apply]
    linear_combination -e.im*hre+e.re*him
  simpa only [g,gIter,split_evaluation] using hh hxx hyy hxy hrx hry

private lemma character_physical (p q : ℕ) (x : Fin 13 → ℝ) (e : ℂ)
    (he : e^2 = OpenBoundaryMPSSpectralExtraction.D
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)) :
    character (fun i => (eval x (g p q i) : ℂ)) e (star e) =
      (eval (point x e) (g15 p q) : ℂ) := by
  rw [g_evaluation p q x e he]
  apply Complex.ext <;>
    simp [character,Complex.mul_re,Complex.mul_im,Complex.normSq_apply] <;> ring

private lemma g15_nonzero_of_norm (p q : ℕ) (x : Fin 13 → ℝ) (e : ℂ)
    (he : e^2 = OpenBoundaryMPSSpectralExtraction.D
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x))
    (hn : eval x (normg (g p q) discrR discrI) ≠ 0) :
    eval (point x e) (g15 p q) ≠ 0 := by
  have hd := discriminant_eval x
  have he' : e^2 = (eval x discrR : ℂ)+Complex.I*(eval x discrI : ℂ) := by
    rw [hd.1,hd.2,he]
    exact (Complex.re_add_im _).symm.trans (by ring)
  have hf' : (star e)^2 = (eval x discrR : ℂ)-Complex.I*(eval x discrI : ℂ) := by
    have hh := congrArg (starRingEnd ℂ) he'
    simpa only [map_pow,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,
      neg_mul,sub_eq_add_neg,RCLike.star_def] using hh
  have hh := character_four_factor (fun i => (eval x (g p q i) : ℂ))
    (eval x discrR : ℂ) (eval x discrI : ℂ) e (star e) he' hf'
  have heval : (eval x (normg (g p q) discrR discrI) : ℂ) =
      pairK (fun i => (eval x (g p q i) : ℂ)) (eval x discrR : ℂ) (eval x discrI : ℂ)^2 -
        ((eval x discrR : ℂ)^2+(eval x discrI : ℂ)^2)*
          pairH (fun i => (eval x (g p q i) : ℂ))^2 := by
    simp [normg,K0,H0,pairK,pairH]
  rw [← heval,character_physical p q x e he] at hh
  intro hz
  rw [hz,Complex.ofReal_zero,zero_mul,zero_mul,zero_mul] at hh
  exact (Complex.ofReal_ne_zero.mpr hn) hh.symm

private lemma base_eval (x : Fin 13 → ℝ) :
    eval (fun i => (x i : ℂ)) canonicalHbase =
      OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x 2 *
        OpenBoundaryMPSSpectralExtraction.D (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) *
        OpenBoundaryMPSSpectralExtraction.U (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) *
        (OpenBoundaryMPSSpectralExtraction.U (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) +
          OpenBoundaryMPSSpectralExtraction.D (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)) := by
  have hc (i : Fin 5) : eval (fun j => (x j : ℂ)) (canonicalCorePoly i) =
      OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x i := by
    apply Complex.ext <;> simp [canonicalCorePoly,OpenBoundaryMPSQ2PolynomialFiber.coreVariable,
      OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates]
  simp [canonicalHbase,canonicalD,canonicalH,canonicalU,canonicalT0,canonicalT1,hc,
    OpenBoundaryMPSSpectralExtraction.D,OpenBoundaryMPSSpectralExtraction.h,
    OpenBoundaryMPSSpectralExtraction.U,OpenBoundaryMPSSpectralExtraction.t0,
    OpenBoundaryMPSSpectralExtraction.t1]

private lemma admissible_of_Jden (x : Fin 13 → ℝ) (e : ℂ)
    (he : e^2 = OpenBoundaryMPSSpectralExtraction.D
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x))
    (hj : eval x canonicalJden ≠ 0) :
    OpenBoundaryMPSSpectralExtraction.Admissible
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e := by
  refine ⟨he,?_⟩
  intro hz
  have hb := base_eval x
  rw [hz] at hb
  apply hj
  simp only [canonicalJden,map_add,map_pow,(coefficient_eval canonicalHbase x).1,
    (coefficient_eval canonicalHbase x).2,hb,Complex.zero_re,Complex.zero_im]
  norm_num

/-- The nonzero certificate locus supplies actual Regular and b conditions for every root branch.
The right column is the physical square-root representative and retains u to the full length. -/
theorem certificate_native (p q : ℕ) (x : Fin 13 → ℝ) (e : ℂ)
    (hsigma : 0 < OpenBoundaryMPSQ2PolynomialFiber.sigma x)
    (hP : eval x (P p q) ≠ 0)
    (he : e^2 = OpenBoundaryMPSSpectralExtraction.D
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)) :
    OpenBoundaryMPSSpectralExtraction.Admissible
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e ∧
    Regular (OpenBoundaryMPSSpectralExtraction.sector
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) ∧
    eval (OpenBoundaryMPSInteriorPolynomial.coordinates
      (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeLeft (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeRight (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)
        e ((p+2)+q) ((Real.sqrt (OpenBoundaryMPSQ2PolynomialFiber.sigma x) : ℂ) •
          ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x]))
      (OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e))
      (OpenBoundaryMPSInteriorPolynomial.b p q) ≠ 0 := by
  have hp' : eval x (X 10) * eval x canonicalJden * eval x canonicalWnorm *
      eval x (normg (g p q) discrR discrI) ≠ 0 := by
    simpa only [P,spectralCertificate,map_mul] using hP
  have hj := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp').1).1).2
  have hn := (mul_ne_zero_iff.mp hp').2
  have hc := admissible_of_Jden x e he hj
  have hg := g15_nonzero_of_norm p q x e he hn
  have hhc : eval (point x e) (H p q) ≠ 0 ∧ eval (point x e) crossNorm ≠ 0 := by
    simpa only [g15,map_mul,mul_ne_zero_iff] using hg
  have hc2 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc.2).1).1).1
  have hcross : 1+star (OpenBoundaryMPSSpectralExtraction.lam
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)*
      OpenBoundaryMPSSpectralExtraction.mu
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e ≠ 0 := by
    intro hz
    apply hhc.2
    rw [crossNorm_eval,cross_native x e hc2,hz,mul_zero,Complex.normSq_zero]
  have hreg := (OpenBoundaryMPSSpectralExtraction.native_extraction hc).2.2.2.2.2.2.2.2.1.mpr hcross
  have hb0 : eval (OpenBoundaryMPSInteriorPolynomial.coordinates
      (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeLeft (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeRight (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)
        e ((p+2)+q) ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x])
      (OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e))
      (OpenBoundaryMPSInteriorPolynomial.b p q) ≠ 0 := by
    rw [(clearing_native p q x e hc).2]
    exact div_ne_zero hhc.1 (clearing_native p q x e hc).1
  refine ⟨hc,hreg,?_⟩
  have hcoord : OpenBoundaryMPSInteriorPolynomial.coordinates
      (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeLeft (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeRight (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)
        e ((p+2)+q) ((Real.sqrt (OpenBoundaryMPSQ2PolynomialFiber.sigma x) : ℂ) •
          ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x]))
      (OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) =
      OpenBoundaryMPSInteriorPolynomial.scaleRight (Real.sqrt (OpenBoundaryMPSQ2PolynomialFiber.sigma x))
        (OpenBoundaryMPSInteriorPolynomial.coordinates
          (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
          (OpenBoundaryMPSSpectralExtraction.nativeLeft (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
          (OpenBoundaryMPSSpectralExtraction.nativeRight (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)
            e ((p+2)+q) ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x])
          (OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)) := by
    funext i
    fin_cases i <;>
      simp [OpenBoundaryMPSInteriorPolynomial.coordinates,OpenBoundaryMPSInteriorPolynomial.scaleRight,
        OpenBoundaryMPSSpectralExtraction.nativeRight,Matrix.mulVec_smul,smul_smul,
        Complex.mul_re,Complex.mul_im] <;> ring
  rw [hcoord,OpenBoundaryMPSInteriorPolynomial.b_right_scale]
  exact mul_ne_zero (pow_ne_zero 4 (Real.sqrt_pos.mpr hsigma).ne') hb0

/-- Explicitly conditional native/canonical endpoint. The final theorem in
InteriorSpectralAmbiguity discharges positivity and b on the certificate locus. -/
theorem canonical_actual_ambiguity_of_native
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (x : Fin 13 → ℝ) (e : ℂ) (R : Fin 2 → ℂ)
    (hc : OpenBoundaryMPSSpectralExtraction.Admissible
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
    (hs : Regular (OpenBoundaryMPSSpectralExtraction.sector
      (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e))
    (hleft : (leftTarget
      (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeLeft
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) p).PosDef)
    (hright : (rightTarget
      (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeRight
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e ((p+2)+q) R) q).PosDef)
    (hb : eval (OpenBoundaryMPSInteriorPolynomial.coordinates
      (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeLeft (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
      (OpenBoundaryMPSSpectralExtraction.nativeRight
        (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e ((p+2)+q) R)
      (OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e))
      (OpenBoundaryMPSInteriorPolynomial.b p q) ≠ 0) :
    ∃ φ : Word ((p+2)+q) → ℂ,
      φ ∈ openBoundaryMPS ((p+2)+q) ∧ φ ≠ 0 ∧
      rawInterior p 2 q φ = rawInterior p 2 q
        (mpsState ((p+2)+q)
          (OpenBoundaryMPSSpectralExtraction.A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 0)
          (OpenBoundaryMPSSpectralExtraction.A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 1)
          (OpenBoundaryMPSSpectralExtraction.L (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)) R) ∧
      ¬ ∃ η : ℂ, ‖η‖ = 1 ∧ φ = η •
        mpsState ((p+2)+q)
          (OpenBoundaryMPSSpectralExtraction.A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 0)
          (OpenBoundaryMPSSpectralExtraction.A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 1)
          (OpenBoundaryMPSSpectralExtraction.L (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x)) R := by
  have hz := (OpenBoundaryMPSSpectralExtraction.native_extraction hc).2.1
  have ha := OpenBoundaryMPSSpectralExtraction.raw_amplitude hc ((p+2)+q) R
  rw [ha]
  exact OpenBoundaryMPSInteriorPolynomial.nonzero_locus_actual_ambiguity
    p q hp hq _ hs _ hz _ _ hleft hright hb
end D5.S3.Quantum.TensorNetworks.InteriorSpectralCertificate
