/- GID: D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/InteriorSpectralWitness
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The actual all-length native Jacobian witness survives real spectral clearing. -/

import D5.S3.Quantum.TensorNetworks.InteriorSpectralCertificate
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.Polynomial.Basic

/-! A nonzero physical character is needed for the free-orbit argument. It does
not assert that the eventual norm is nonzero at this same specialization. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 1024
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.InteriorSpectralWitness
open Matrix MvPolynomial
open scoped Matrix
open InteriorSpectralCoordinates InteriorSpectralCertificate
open OpenBoundaryMPSInteriorPolynomial
open OpenBoundaryMPSSpectralExtraction

def canonicalPoint : Fin 13 → ℝ := ![0,0,1/2,0,1,0,0,0,0,0,1,1,1]

private lemma canonical_core :
    OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates canonicalPoint = witnessC := by
  funext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates,canonicalPoint,witnessC]

private lemma canonical_eta : OpenBoundaryMPSQ2PolynomialFiber.eta canonicalPoint = 1+Complex.I := by
  apply Complex.ext <;> norm_num [OpenBoundaryMPSQ2PolynomialFiber.eta,canonicalPoint]

/-- Exact actual b nonvanishing after retaining the complete raw scalar for every length. -/
theorem native_b_witness (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    eval (coordinates (sector witnessC 1) (nativeLeft witnessC 1)
      (nativeRight witnessC 1 ((p+2)+q) ![1,1+Complex.I]) (z witnessC 1)) (b p q) ≠ 0 := by
  let N := (p+2)+q
  obtain ⟨_,_,_,_,_,_,_,hs,hz,hl,_,hr,_⟩ := fixed_witness_extraction N
  rw [hs,hz,hl,hr]
  have hcoords : coordinates witnessSector witnessLeft ((1/2 : ℂ)^N • witnessRight) 1 =
      scaleRight ((1/2 : ℝ)^N) (coordinates witnessSector witnessLeft witnessRight 1) := by
    have hhalf : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
    rw [hhalf,← Complex.ofReal_pow]
    funext i
    fin_cases i <;>
      simp [coordinates,scaleRight,Complex.mul_re,Complex.mul_im,
        -Complex.ofReal_pow,-Complex.ofReal_div,-Complex.ofReal_inv]
  rw [hcoords,b_right_scale]
  exact mul_ne_zero (pow_ne_zero 4 (pow_ne_zero N (by norm_num)))
    (b_nonzero p q hp hq).1

/-- H itself has a nonzero real physical evaluation for every fixed positive p,q. -/
theorem H_witness (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    eval (point canonicalPoint 1) (H p q) ≠ 0 := by
  have hc : Admissible (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates canonicalPoint) 1 := by
    rw [canonical_core]
    exact (fixed_witness_extraction 0).1
  have hh := (clearing_native p q canonicalPoint 1 hc).2
  rw [canonical_core,canonical_eta] at hh
  have hb := native_b_witness p q hp hq
  intro hz
  rw [hz,zero_div] at hh
  exact hb hh

open OpenBoundaryMPSInteriorSpectralNorm
open OpenBoundaryMPSDensityGenericity (realCoeff imagCoeff coefficient_eval)

local notation "Free" => MvPolynomial (Fin 13) ℂ

def freeCore : Fin 5 → Free :=
  ![X 0,X 1,X 2,-X 2*X 3*X 4,X 1+X 2*(X 3+X 4)]
def freeBarCore : Fin 5 → Free :=
  ![X 5,X 6,X 7,-X 7*X 8*X 9,X 6+X 7*(X 8+X 9)]
def baseAssignment : Fin 13 → Free :=
  let m : Free := C (1/2 : ℂ)
  let n : Free := C (-(Complex.I/2))
  ![m*(X 0+X 5),m*(X 1+X 6),m*(X 2+X 7),
    m*(-X 2*X 3*X 4-X 7*X 8*X 9),
    m*(X 1+X 2*(X 3+X 4)+X 6+X 7*(X 8+X 9)),
    n*(X 0-X 5),n*(X 1-X 6),n*(X 2-X 7),
    n*(-X 2*X 3*X 4+X 7*X 8*X 9),
    n*(X 1+X 2*(X 3+X 4)-X 6-X 7*(X 8+X 9)),
    X 12,m*(X 10+X 11),n*(X 10-X 11)]
def phi : CanonicalPoly →+* Free := eval₂Hom (C.comp Complex.ofRealHom) baseAssignment

def E : Free := X 2*(X 3-X 4)
def F : Free := X 7*(X 8-X 9)
def swapE : Free ≃ₐ[ℂ] Free := renameEquiv ℂ (Equiv.swap (3 : Fin 13) 4)
def swapF : Free ≃ₐ[ℂ] Free := renameEquiv ℂ (Equiv.swap (8 : Fin 13) 9)

private lemma discrR_literal : discrR =
    (X 4-X 1)^2-(X 9-X 6)^2+4*(X 2*X 3-X 7*X 8) := by
  apply MvPolynomial.funext
  intro x
  rw [discrR,(coefficient_eval canonicalD x).1]
  simp [canonicalD,canonicalH,canonicalCorePoly,
    OpenBoundaryMPSQ2PolynomialFiber.coreVariable,pow_two,Complex.mul_re,Complex.mul_im]
  ring

private lemma discrI_literal : discrI =
    2*(X 4-X 1)*(X 9-X 6)+4*(X 2*X 8+X 7*X 3) := by
  apply MvPolynomial.funext
  intro x
  rw [discrI,(coefficient_eval canonicalD x).2]
  simp [canonicalD,canonicalH,canonicalCorePoly,
    OpenBoundaryMPSQ2PolynomialFiber.coreVariable,pow_two,Complex.mul_re,Complex.mul_im]
  ring

private lemma free_discriminants :
    E^2 = phi discrR + C Complex.I * phi discrI ∧
    F^2 = phi discrR - C Complex.I * phi discrI := by
  rw [discrR_literal,discrI_literal]
  constructor <;> change @Eq (MvPolynomial (Fin 13) ℂ) _ _
  all_goals
    norm_num [phi,baseAssignment,E,F]
    polynomial_nf
    norm_num [Complex.I_sq] <;> polynomial

@[simp] private lemma swapE_C (a : ℂ) : swapE (C a) = C a := swapE.commutes a
@[simp] private lemma swapF_C (a : ℂ) : swapF (C a) = C a := swapF.commutes a

private lemma swapE_base (i : Fin 13) : swapE (baseAssignment i) = baseAssignment i := by
  fin_cases i <;>
    simp [swapE,baseAssignment,freeCore,freeBarCore,renameEquiv_apply,
      Equiv.swap_apply_def,Fin.append,Fin.addCases] <;> ring

private lemma swapF_base (i : Fin 13) : swapF (baseAssignment i) = baseAssignment i := by
  fin_cases i <;>
    simp [swapF,baseAssignment,freeCore,freeBarCore,renameEquiv_apply,
      Equiv.swap_apply_def,Fin.append,Fin.addCases] <;> ring

private lemma swapE_phi (G : CanonicalPoly) : swapE (phi G) = phi G := by
  have hh : swapE.toRingHom.comp phi = phi := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [phi,swapE,renameEquiv_apply]
    · intro i
      simpa [phi] using swapE_base i
  exact DFunLike.congr_fun hh G

private lemma swapF_phi (G : CanonicalPoly) : swapF (phi G) = phi G := by
  have hh : swapF.toRingHom.comp phi = phi := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [phi,swapF,renameEquiv_apply]
    · intro i
      simpa [phi] using swapF_base i
  exact DFunLike.congr_fun hh G

private lemma swap_roots :
    swapE E = -E ∧ swapE F = F ∧ swapF E = E ∧ swapF F = -F := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp [swapE,swapF,E,F,renameEquiv_apply,Equiv.swap_apply_def] <;> ring

private def freeWitness : Fin 13 → ℂ :=
  ![0,0,1/2,2,0,0,0,1/2,2,0,1+Complex.I,1-Complex.I,1]

private lemma witness_phi (G : CanonicalPoly) :
    eval freeWitness (phi G) = (eval canonicalPoint G : ℂ) := by
  have hh : (eval freeWitness).comp phi = Complex.ofRealHom.comp (eval canonicalPoint) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [phi]
    · intro i
      fin_cases i <;>
        norm_num [phi,baseAssignment,freeCore,freeBarCore,freeWitness,canonicalPoint,
          Fin.append,Fin.addCases,Complex.ext_iff]
  exact DFunLike.congr_fun hh G

private lemma cross_witness :
    eval (point canonicalPoint 1) crossNorm = 1 := by
  have hcross : eval (fun i => (point canonicalPoint 1 i : ℂ)) cross = 1 := by
    rw [cross_native canonicalPoint 1 (by
      norm_num [OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates,canonicalPoint,Complex.ext_iff])]
    rw [canonical_core]
    norm_num [lam,mu,h,witnessC,Complex.normSq_apply]
  rw [crossNorm_eval,hcross,Complex.normSq_one]

private lemma free_character_nonzero (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    character (phi ∘ g p q) E F ≠ 0 := by
  have he : (1 : ℂ)^2 = D (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates canonicalPoint) := by
    rw [canonical_core]
    exact (fixed_witness_extraction 0).1.1
  have hred := g_evaluation p q canonicalPoint 1 he
  have hH := H_witness p q hp hq
  have hcross := cross_witness
  have hv : eval freeWitness (character (phi ∘ g p q) E F) =
      (eval (point canonicalPoint 1) (H p q) : ℂ) := by
    simp only [character,Function.comp_apply,map_add,map_mul,map_sub,
      witness_phi,Algebra.algebraMap_self]
    norm_num [E,F,freeWitness]
    simp only [g15,map_mul,hcross,mul_one,Complex.one_re,Complex.one_im,
      Complex.normSq_one,mul_one,mul_zero,add_zero] at hred
    have hh := congrArg Complex.ofReal hred.symm
    push_cast at hh
    linear_combination hh
  intro hz
  rw [hz,map_zero] at hv
  exact (Complex.ofReal_ne_zero.mpr hH) hv.symm

/-- Free variable swaps prove the literal lengthwise norm nonzero, without a base-map injection. -/
theorem normg_nonzero (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    normg (g p q) discrR discrI ≠ 0 := by
  let hfree := character (phi ∘ g p q) E F
  have h0 : hfree ≠ 0 := free_character_nonzero p q hp hq
  have hs : swapE hfree = character (phi ∘ g p q) (-E) F := by
    simp [hfree,character,map_add,map_sub,map_mul,swapE_phi,swap_roots.1,
      swap_roots.2.1]
  have ht : swapF hfree = character (phi ∘ g p q) E (-F) := by
    simp [hfree,character,map_add,map_sub,map_mul,swapF_phi,swap_roots.2.2.1,
      swap_roots.2.2.2]
  have hst : swapE (swapF hfree) = character (phi ∘ g p q) (-E) (-F) := by
    rw [ht]
    simp [character,map_add,map_sub,map_mul,swapE_phi,swap_roots.1,swap_roots.2.1]
  have hn := character_four_factor (phi ∘ g p q) (phi discrR) (phi discrI) E F
    free_discriminants.1 free_discriminants.2
  have hm : phi (normg (g p q) discrR discrI) =
      hfree * swapE hfree * swapF hfree * swapE (swapF hfree) := by
    rw [hst,hs,ht]
    change phi (normg (g p q) discrR discrI) =
      character (phi ∘ g p q) E F * character (phi ∘ g p q) (-E) F *
        character (phi ∘ g p q) E (-F) * character (phi ∘ g p q) (-E) (-F)
    rw [hn]
    simp [normg,K0,H0,pairK,pairH,Function.comp_def,phi]
  intro hz
  have hs0 : swapE hfree ≠ 0 := by
    intro hh
    exact h0 (swapE.injective (hh.trans (map_zero swapE).symm))
  have ht0 : swapF hfree ≠ 0 := by
    intro hh
    exact h0 (swapF.injective (hh.trans (map_zero swapF).symm))
  have hst0 : swapE (swapF hfree) ≠ 0 := by
    intro hh
    exact ht0 (swapE.injective (hh.trans (map_zero swapE).symm))
  have hp0 : hfree * swapE hfree * swapF hfree * swapE (swapF hfree) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h0 hs0) ht0) hst0
  apply hp0
  rw [← hm,hz,map_zero]

private lemma factor_witness :
    eval canonicalPoint canonicalJden = 1/64 ∧
    eval canonicalPoint canonicalWnorm = 1 := by
  have hJ : eval (fun i => (canonicalPoint i : ℂ)) canonicalHbase = -1/8 := by
    norm_num [canonicalHbase,canonicalD,canonicalU,canonicalH,canonicalT0,canonicalT1,
      canonicalCorePoly,OpenBoundaryMPSQ2PolynomialFiber.coreVariable,canonicalPoint]
  have hW : eval (fun i => (canonicalPoint i : ℂ)) canonicalW = -1 := by
    apply Complex.ext <;> norm_num [canonicalW,canonicalCorePoly,canonicalEtaPoly,
      OpenBoundaryMPSQ2PolynomialFiber.coreVariable,
      OpenBoundaryMPSQ2PolynomialFiber.etaVariable,canonicalPoint,pow_two,Complex.mul_re,Complex.mul_im]
  constructor
  · simp only [canonicalJden,map_add,map_pow,
      (coefficient_eval canonicalHbase canonicalPoint).1,
      (coefficient_eval canonicalHbase canonicalPoint).2,hJ]
    norm_num
  · simp only [canonicalWnorm,map_add,map_pow,
      (coefficient_eval canonicalW canonicalPoint).1,
      (coefficient_eval canonicalW canonicalPoint).2,hW]
    norm_num

/-- A nonzero literal canonical REAL13 certificate for each fixed positive pair of lengths. -/
theorem P_nonzero (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) : P p q ≠ 0 := by
  have hj : canonicalJden ≠ 0 := by
    intro hz
    have hh := factor_witness.1
    rw [hz,map_zero] at hh
    norm_num at hh
  have hw : canonicalWnorm ≠ 0 := by
    intro hz
    have hh := factor_witness.2
    rw [hz,map_zero] at hh
    norm_num at hh
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (X_ne_zero (10 : Fin 13)) hj) hw)
    (normg_nonzero p q hp hq)

end D5.S3.Quantum.TensorNetworks.InteriorSpectralWitness
