/- GID: D5/S3/Quantum/Algebra/AuricActualOcticWindow
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/AuricActualOcticWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant]
   utility: none
   digest: Actual characteristic-zero octic field and its eight original embedding labels. -/

module

public import D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Algebra.AuricActualOcticWindow

open Polynomial

/-- The designated positive real eighth root, with its literal real definition. -/
def aR : ℝ := (2 : ℝ) ^ ((8 : ℝ)⁻¹)
def aC : ℂ := (aR : ℂ)
abbrev D : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {aC}
def alpha : D := IntermediateField.AdjoinSimple.gen ℚ aC
/-- The designated complex exponential, with no change of primitive root. -/
def zetaC : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I / 4)
abbrev K : IntermediateField D ℂ := IntermediateField.adjoin D {zetaC}
def aK : K := algebraMap D K alpha
def zetaK : K := IntermediateField.AdjoinSimple.gen D zetaC

lemma aR_positive : 0 < aR :=
  Real.rpow_pos_of_pos (by norm_num) _

lemma aR_pow : aR ^ 8 = (2 : ℝ) := by
  exact Real.rpow_inv_natCast_pow (by norm_num) (by decide : (8 : ℕ) ≠ 0)

lemma aC_pow : aC ^ 8 = (2 : ℂ) := by
  change (aR : ℂ) ^ 8 = (2 : ℂ)
  rw [← Complex.ofReal_pow, aR_pow]
  norm_num

lemma alpha_pow : alpha ^ 8 = (2 : D) := by
  apply D.val.injective
  change aC ^ 8 = (2 : ℂ)
  exact aC_pow

lemma aK_pow : aK ^ 8 = (2 : K) := by
  simpa only [aK, map_pow, map_ofNat] using congrArg (algebraMap D K) alpha_pow

lemma zetaC_primitive : IsPrimitiveRoot zetaC 8 := by
  have h := Complex.isPrimitiveRoot_exp 8 (by decide)
  have he : (2 : ℂ) * Real.pi * Complex.I / 8 = (Real.pi : ℂ) * Complex.I / 4 := by
    ring
  simpa only [he, zetaC] using h

lemma zetaK_primitive : IsPrimitiveRoot zetaK 8 := by
  exact zetaC_primitive.of_map_of_injective K.val.injective

abbrev octic : ℚ[X] := X ^ 8 - C 2

lemma octic_irreducible : Irreducible octic := by
  let f : ℤ[X] := X ^ 8 - C 2
  have hm : f.Monic := monic_X_pow_sub_C 2 (by decide)
  have hp : (Ideal.span ({2} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).2
      (by norm_num : Prime (2 : ℤ))
  have he : f.IsEisensteinAt (Ideal.span ({2} : Set ℤ)) := by
    apply hm.isEisensteinAt_of_mem_of_notMem hp.ne_top
    · intro i hi
      have hi8 : i < 8 := by simpa only [f, natDegree_X_pow_sub_C] using hi
      rw [Ideal.mem_span_singleton]
      interval_cases i <;> norm_num [f, coeff_sub, coeff_X_pow, coeff_C]
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      norm_num [f, coeff_sub, coeff_X_pow, coeff_C]
  have hf : Irreducible f := he.irreducible hp hm.isPrimitive
    (by simp only [f, natDegree_X_pow_sub_C]; decide)
  change Irreducible (X ^ 8 - C (2 : ℚ))
  simpa only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, map_ofNat, Polynomial.map_ofNat] using
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).mp hf

lemma aC_aeval : aeval aC octic = 0 := by
  simp only [octic, map_sub, map_pow, aeval_X, aeval_C, map_ofNat]
  exact sub_eq_zero.mpr aC_pow

lemma aC_integral : IsIntegral ℚ aC :=
  ⟨octic, monic_X_pow_sub_C 2 (by decide), aC_aeval⟩

lemma aC_minpoly : minpoly ℚ aC = octic :=
  (minpoly.eq_of_irreducible_of_monic octic_irreducible aC_aeval
    (monic_X_pow_sub_C 2 (by decide))).symm

lemma alpha_minpoly : minpoly ℚ alpha = octic := by
  rw [alpha, IntermediateField.minpoly_gen, aC_minpoly]

instance dFinite : FiniteDimensional ℚ D :=
  IntermediateField.adjoin.finiteDimensional aC_integral

lemma zetaC_integral : IsIntegral D zetaC := by
  refine ⟨X ^ 8 - C (1 : D), monic_X_pow_sub_C 1 (by decide), ?_⟩
  simpa only [map_sub, map_pow, aeval_X, aeval_C, map_one] using
    sub_eq_zero.mpr zetaC_primitive.pow_eq_one

instance kFiniteOverD : FiniteDimensional D K :=
  IntermediateField.adjoin.finiteDimensional zetaC_integral

instance kFinite : FiniteDimensional ℚ K := FiniteDimensional.trans ℚ D K

instance kAlgebraic : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K

/-- An unspecified algebraically closed coefficient field admits a common map;
a fixed supplied map remains the argument to all transport statements. -/
def commonMap (k : Type*) [Field k] [Algebra ℚ k] [IsAlgClosed k] : K →ₐ[ℚ] k :=
  IsAlgClosed.lift

def pb : PowerBasis ℚ D := IntermediateField.adjoin.powerBasis aC_integral

lemma pb_gen : pb.gen = alpha := rfl

lemma label_root (i : Fin 8) :
    aeval (aK * zetaK ^ i.val) (minpoly ℚ pb.gen) = 0 := by
  rw [pb_gen, alpha_minpoly]
  simp only [octic, map_sub, map_pow, aeval_X, aeval_C, map_ofNat]
  apply sub_eq_zero.mpr
  rw [mul_pow, aK_pow, ← pow_mul, Nat.mul_comm i.val 8, pow_mul,
    zetaK_primitive.pow_eq_one, one_pow, mul_one]

/-- Each original index is sent to its original power of the designated zeta. -/
def sigma (i : Fin 8) : D →ₐ[ℚ] K :=
  pb.lift (aK * zetaK ^ i.val) (label_root i)

lemma sigma_label (i : Fin 8) : sigma i alpha = aK * zetaK ^ i.val := by
  exact pb.lift_gen _ _

lemma sigma_zero : sigma 0 = IsScalarTower.toAlgHom ℚ D K := by
  apply pb.algHom_ext
  rw [pb_gen, sigma_label]
  simp only [Fin.val_zero, pow_zero, mul_one]
  rfl

lemma sigma_injective : Function.Injective sigma := by
  intro i j hij
  have ha0 : aK ≠ 0 := by
    intro h
    have h2 := aK_pow
    rw [h, zero_pow (by decide)] at h2
    norm_num at h2
  have hp : zetaK ^ i.val = zetaK ^ j.val := by
    apply mul_left_cancel₀ ha0
    simpa only [sigma_label] using congrArg (fun f : D →ₐ[ℚ] K => f alpha) hij
  exact Fin.ext (zetaK_primitive.pow_inj i.isLt j.isLt hp)

/-- Transport uses one common extension homomorphism for every original label. -/
def transported {k : Type*} [Field k] [Algebra ℚ k]
    (lambda : K →ₐ[ℚ] k) (i : Fin 8) : D →ₐ[ℚ] k :=
  lambda.comp (sigma i)

lemma transported_label {k : Type*} [Field k] [Algebra ℚ k]
    (lambda : K →ₐ[ℚ] k) (i : Fin 8) :
    transported lambda i alpha = lambda aK * (lambda zetaK) ^ i.val := by
  change lambda (sigma i alpha) = _
  rw [sigma_label, map_mul, map_pow]

lemma transported_zero {k : Type*} [Field k] [Algebra ℚ k]
    (lambda : K →ₐ[ℚ] k) (x : D) :
    transported lambda 0 x = lambda (algebraMap D K x) := by
  change lambda (sigma 0 x) = _
  rw [sigma_zero]
  rfl

lemma transported_primitive {k : Type*} [Field k] [Algebra ℚ k]
    (lambda : K →ₐ[ℚ] k) : IsPrimitiveRoot (lambda zetaK) 8 :=
  zetaK_primitive.map_of_injective lambda.injective

lemma transported_denominator {k : Type*} [Field k] [Algebra ℚ k]
    (lambda : K →ₐ[ℚ] k) (v : D) (hv : v ≠ 0) (i : Fin 8) :
    transported lambda i v ≠ 0 := by
  exact (map_ne_zero (transported lambda i)).mpr hv

lemma transported_quotient {k : Type*} [Field k] [Algebra ℚ k]
    (lambda : K →ₐ[ℚ] k) (u v : D) (i : Fin 8) :
    transported lambda i (u / v) =
      transported lambda i u / transported lambda i v :=
  map_div₀ _ _ _

/- The exact 43.2 classification remains open.  This source retains only the
   actual characteristic-zero degree-eight field, its original eight labels,
   and the proved transport facts consumed by the future cut-free bridge. -/

end D5.S3.Quantum.Algebra.AuricActualOcticWindow
