/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedExponentialReordering
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reordering the charged creation exponential through the oscillator translation. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
Oscillator reordering for the charged P48q fields in the cover coordinate.
The outer power series variable is the creation coordinate `y`.
The polynomial variable in each coefficient is the inverse cover coordinate `u`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice)
open ThirdEigenspacePairing (p48qAction p48qForm p48qBasis p48qOppositeBasis)
open P48qNativeContraction (complexPairing contractionExponent fourierComponent)
open Module
open scoped BigOperators

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem map_exp_subst {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) (p : PowerSeries R)
    (hp : PowerSeries.constantCoeff p = 0) :
    PowerSeries.map f ((PowerSeries.exp R).subst p) =
      (PowerSeries.exp S).subst (PowerSeries.map f p) := by
  calc
    _ = (PowerSeries.map f (PowerSeries.exp R)).subst (PowerSeries.map f p) :=
      PowerSeries.map_subst (a := p) (h := f)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hp) (PowerSeries.exp R)
    _ = _ := by rw [PowerSeries.map_exp]

private def formalExp {R : Type*} [CommRing R] [Algebra ℚ R] (p : PowerSeries R) :
    PowerSeries R :=
  (PowerSeries.exp R).subst p

section Exponential

open PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private theorem constantCoeff_formalExp {p : PowerSeries R} (hp : constantCoeff p = 0) :
    constantCoeff (formalExp p) = 1 := by
  rw [formalExp, constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero hp,
    constantCoeff_exp, map_one]

private theorem formalExp_mul_neg {p : PowerSeries R} (hp : constantCoeff p = 0) :
    formalExp p * formalExp (-p) = 1 := by
  have hs : HasSubst p := HasSubst.of_constantCoeff_zero' hp
  have hone : (1 : PowerSeries R).subst p = 1 := by
    rw [← coe_substAlgHom hs, map_one]
  have h := congrArg (fun f : PowerSeries R => f.subst p)
    (exp_mul_exp_eq_exp_add (1 : R) (-1))
  change (rescale 1 (exp R) * rescale (-1) (exp R)).subst p =
    (rescale (1 + -1) (exp R)).subst p at h
  rw [rescale_one, RingHom.id_apply, add_neg_cancel, rescale_zero_apply,
    constantCoeff_exp, map_one, hone, subst_mul hs, rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X' (-1 : R)) hs,
    subst_smul hs, subst_X hs, neg_one_smul] at h
  exact h

private theorem formalExp_add {p q : PowerSeries R}
    (hp : constantCoeff p = 0) (hq : constantCoeff q = 0) :
    formalExp (p + q) = formalExp p * formalExp q := by
  letI : HasUniqueDiv R := .of_module_rat R
  have hsum : constantCoeff (p + q) = 0 := by simp [hp, hq]
  have hneg : constantCoeff (-(p + q)) = 0 := by simp [hp, hq]
  have hderiv (v : PowerSeries R) (hv : constantCoeff v = 0) :
      derivative (formalExp v) = formalExp v * derivative v := by
    unfold formalExp
    rw [derivative_subst (HasSubst.of_constantCoeff_zero' hv), derivative_exp]
  have hprod : formalExp p * formalExp q * formalExp (-(p + q)) = 1 := by
    apply derivative.ext
    · simp only [Derivation.leibniz, hderiv p hp, hderiv q hq, hderiv _ hneg,
        derivative_one, smul_eq_mul, map_neg, map_add]
      ring
    · simp only [map_mul, constantCoeff_formalExp hp, constantCoeff_formalExp hq,
        constantCoeff_formalExp hneg, one_mul, map_one]
  calc
    formalExp (p + q) =
        (formalExp p * formalExp q * formalExp (-(p + q))) * formalExp (p + q) := by
          rw [hprod, one_mul]
    _ = _ := by
      rw [mul_assoc, mul_comm (formalExp (-(p + q))) (formalExp (p + q)),
        formalExp_mul_neg hsum, mul_one]

end Exponential

/-- Embed a scalar series by substituting `uy` for its variable.
Its `y^n` coefficient is the embedded scalar times `u^n`. -/
def atCoverRatio : PowerSeries ℂ →+* PowerSeries (Polynomial Fock) :=
  (PowerSeries.rescale (Polynomial.X : Polynomial Fock)).comp
    (PowerSeries.map (algebraMap ℂ (Polynomial Fock)))

theorem coeff_atCoverRatio (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (atCoverRatio f) =
      (Polynomial.X : Polynomial Fock) ^ n *
        algebraMap ℂ (Polynomial Fock) (PowerSeries.coeff n f) := by
  simp only [atCoverRatio, RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map]

theorem coeff_atCoverRatio_polynomial (f : PowerSeries ℂ) (n d : ℕ) :
    (PowerSeries.coeff n (atCoverRatio f)).coeff d =
      if d = n then algebraMap ℂ Fock (PowerSeries.coeff n f) else 0 := by
  rw [coeff_atCoverRatio, mul_comm, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul_X_pow]

/-- The scalar shift produced by translating each creator in the creation exponent.
The factor `-3/n` at positive cover degree `n` uses the native creation normalization
and the minus sign in the native generator substitution. -/
def translationShift (B : FixedDualBases) (a b : Charge lattice) : PowerSeries ℂ :=
  PowerSeries.mk fun
    | 0 => 0
    | m + 1 => -((((m + 1 : ℕ) : ℂ) / 3)⁻¹ *
        ∑ i : Fin 16, creationCoordinate B b (i, m) * annihilationPairing B a (i, m))

theorem coeff_translationShift_succ (B : FixedDualBases) (a b : Charge lattice) (m : ℕ) :
    PowerSeries.coeff (m + 1) (translationShift B a b) =
      -((((m + 1 : ℕ) : ℂ) / 3)⁻¹ *
        ∑ i : Fin 16, creationCoordinate B b (i, m) * annihilationPairing B a (i, m)) :=
  PowerSeries.coeff_mk _ _

@[simp] theorem constantCoeff_translationShift (B : FixedDualBases) (a b : Charge lattice) :
    PowerSeries.constantCoeff (translationShift B a b) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, translationShift, PowerSeries.coeff_mk]

private theorem constantCoeff_creationExponent (B : FixedDualBases) (b : Charge lattice) :
    PowerSeries.constantCoeff (creationSeries B b) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, creationSeries, PowerSeries.coeff_mk]

/-- The generator substitution splits the creation exponent into its constant-polynomial
image and the scalar shift at `uy`. -/
theorem translated_creationSeries (B : FixedDualBases) (a b : Charge lattice) :
    PowerSeries.mapAlgHom (translatedPolynomial B a) (creationSeries B b) =
      PowerSeries.mapAlgHom (Polynomial.CAlgHom : Fock →ₐ[ℂ] Polynomial Fock)
        (creationSeries B b) + atCoverRatio (translationShift B a b) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map, map_add,
      creationSeries, PowerSeries.coeff_mk, coeff_atCoverRatio, translationShift,
      map_zero, pow_zero, mul_zero, add_zero]
  | succ m =>
    let r : ℂ := (((m + 1 : ℕ) : ℂ) / 3)⁻¹
    let c (i : Fin 16) : ℂ := creationCoordinate B b (i, m)
    let d (i : Fin 16) : ℂ := annihilationPairing B a (i, m)
    let U : Polynomial Fock := Polynomial.X ^ (m + 1)
    have hscale (s t : ℂ) :
        s • (algebraMap ℂ (Polynomial Fock) t * U) =
          algebraMap ℂ (Polynomial Fock) (s * t) * U := by
      rw [Algebra.smul_def, ← mul_assoc, ← map_mul (algebraMap ℂ (Polynomial Fock))]
    have hterm (i : Fin 16) :
        c i • (Polynomial.C (d i • (1 : Fock)) * U) =
          algebraMap ℂ (Polynomial Fock) (c i * d i) * U := by
      rw [Algebra.smul_def (d i) (1 : Fock), mul_one,
        ← Polynomial.algebraMap_apply (R := ℂ), hscale]
    simp only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map, map_add,
      coeff_creationSeries_succ, coeff_atCoverRatio, coeff_translationShift_succ]
    change translatedPolynomial B a (r • ∑ i, c i • MvPolynomial.X (i, m)) =
      (Polynomial.CAlgHom : Fock →ₐ[ℂ] Polynomial Fock)
        (r • ∑ i, c i • MvPolynomial.X (i, m)) +
        U * algebraMap ℂ (Polynomial Fock) (-(r * ∑ i, c i * d i))
    simp only [map_smul, map_sum, translatedPolynomial, MvPolynomial.aeval_X,
      Polynomial.CAlgHom_apply, translationVariable, frequency]
    change r • (∑ i, c i • (Polynomial.C (MvPolynomial.X (i, m)) -
        Polynomial.C (d i • (1 : Fock)) * U)) =
      r • (∑ i, c i • Polynomial.C (MvPolynomial.X (i, m))) +
        U * algebraMap ℂ (Polynomial Fock) (-(r * ∑ i, c i * d i))
    simp only [smul_sub, Finset.sum_sub_distrib, hterm]
    rw [← Finset.sum_mul, ← map_sum (algebraMap ℂ (Polynomial Fock)), hscale,
      map_neg (algebraMap ℂ (Polynomial Fock))]
    ring

/-- Translating the native creation exponential factors as its constant-polynomial
image times the normalized scalar exponential of the translation shift at `uy`. -/
theorem translated_creationExponential (B : FixedDualBases) (a b : Charge lattice) :
    PowerSeries.mapAlgHom (translatedPolynomial B a) (creationExponential B b) =
      PowerSeries.mapAlgHom (Polynomial.CAlgHom : Fock →ₐ[ℂ] Polynomial Fock)
        (creationExponential B b) *
        atCoverRatio ((PowerSeries.exp ℂ).subst (translationShift B a b)) := by
  have hb := constantCoeff_creationExponent B b
  have hs := constantCoeff_translationShift B a b
  let C : Fock →ₐ[ℂ] Polynomial Fock := Polynomial.CAlgHom
  let p := PowerSeries.mapAlgHom C (creationSeries B b)
  let q := atCoverRatio (translationShift B a b)
  have hp : PowerSeries.constantCoeff p = 0 := by
    change C (PowerSeries.constantCoeff (creationSeries B b)) = 0
    rw [hb, map_zero]
  have hq : PowerSeries.constantCoeff q = 0 := by
    change PowerSeries.constantCoeff (atCoverRatio (translationShift B a b)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_atCoverRatio,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hs, map_zero, mul_zero]
  have hshift : atCoverRatio ((PowerSeries.exp ℂ).subst (translationShift B a b)) =
      formalExp q := by
    let s := PowerSeries.map (algebraMap ℂ (Polynomial Fock)) (translationShift B a b)
    have hs' : PowerSeries.constantCoeff s = 0 := by
      change algebraMap ℂ (Polynomial Fock)
        (PowerSeries.constantCoeff (translationShift B a b)) = 0
      rw [hs, map_zero]
    calc
      _ = PowerSeries.rescale (Polynomial.X : Polynomial Fock) (formalExp s) :=
        congrArg (PowerSeries.rescale (Polynomial.X : Polynomial Fock))
          (map_exp_subst (algebraMap ℂ (Polynomial Fock)) (translationShift B a b) hs)
      _ = _ := by
        change PowerSeries.rescale (Polynomial.X : Polynomial Fock) (formalExp s) =
          formalExp (PowerSeries.rescale (Polynomial.X : Polynomial Fock) s)
        simp only [formalExp, PowerSeries.rescale_eq_subst]
        exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hs')
          (PowerSeries.HasSubst.smul_X' (Polynomial.X : Polynomial Fock))
          (PowerSeries.exp (Polynomial Fock))
  have hcreation : PowerSeries.mapAlgHom C (creationExponential B b) = formalExp p :=
    map_exp_subst C.toRingHom (creationSeries B b) hb
  calc
    _ = formalExp (PowerSeries.mapAlgHom (translatedPolynomial B a) (creationSeries B b)) :=
      map_exp_subst (translatedPolynomial B a).toRingHom (creationSeries B b) hb
    _ = formalExp (p + q) := congrArg formalExp (translated_creationSeries B a b)
    _ = formalExp p * formalExp q := formalExp_add hp hq
    _ = _ := congrArg₂ (· * ·) hcreation.symm hshift.symm

private theorem sum_pairing_basis {S : Submodule ℂ Cartan}
    (e : Basis (Fin 16) ℂ S) (dual : Fin 16 → Cartan)
    (hdual : ∀ i j, p48qForm (e i : Cartan) (dual j) = if i = j then 1 else 0)
    (v : S) (w : Cartan) :
    (∑ i, p48qForm (v : Cartan) (dual i) * p48qForm w (e i : Cartan)) =
      p48qForm w (v : Cartan) := by
  have hv : (∑ i, e.repr v i • (e i : Cartan)) = (v : Cartan) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg (fun x : S => (x : Cartan)) (e.sum_repr v)
  have hcoord (i : Fin 16) : p48qForm (v : Cartan) (dual i) = e.repr v i := by
    calc
      _ = p48qForm (∑ j, e.repr v j • (e j : Cartan)) (dual i) :=
        congrArg (fun x => p48qForm x (dual i)) hv.symm
      _ = _ := by
        rw [map_sum, LinearMap.sum_apply]
        simp only [LinearMap.BilinForm.smul_left, hdual, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [hcoord, ← LinearMap.BilinForm.smul_right]
  rw [← map_sum, hv]

private theorem exists_creator_basis (B : FixedDualBases) (m : ℕ) :
    ∃ e : Basis (Fin 16) ℂ (p48qAction.eigenspace (ζ ^ ((m + 1) % 3))),
      ∀ i, (e i : Cartan) = creator B (i, m) := by
  have hζ : IsPrimitiveRoot ζ 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
  by_cases h0 : (m + 1) % 3 = 0
  · rw [h0, pow_zero]
    exact ⟨B.creators, fun i => by simp only [creator, frequency, if_pos h0]⟩
  by_cases h1 : (m + 1) % 3 = 1
  · rw [h1, pow_one]
    exact ⟨p48qBasis hζ, fun i => by simp only [creator, frequency, if_neg h0, if_pos h1]⟩
  have h2 : (m + 1) % 3 = 2 := by omega
  rw [h2]
  exact ⟨p48qOppositeBasis hζ, fun i => by simp only [creator, frequency, if_neg h0, if_neg h1]⟩

/-- Dual completeness at frequency `(m+1)/3` identifies the oscillator sum
with the pairing of the two complementary Fourier components. -/
theorem sum_creationCoordinate_mul_annihilationPairing
    (B : FixedDualBases) (a b : Charge lattice) (m : ℕ) :
    (∑ i : Fin 16, creationCoordinate B b (i, m) * annihilationPairing B a (i, m)) =
      complexPairing (fourierComponent (ζ ^ ((m + 1) % 3)) a)
        (fourierComponent ((ζ ^ ((m + 1) % 3)) ^ 2) b) := by
  let z : ℂ := ζ ^ ((m + 1) % 3)
  have hζ : ζ ^ 3 = 1 :=
    (IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive).pow_eq_one
  have hz : z ^ 3 = 1 := by
    dsimp [z]
    rw [pow_right_comm, hζ, one_pow]
  have hz2 : (z ^ 2) ^ 3 = 1 := by rw [pow_right_comm, hz, one_pow]
  have hz4 : (z ^ 2) ^ 2 = z := by
    calc
      (z ^ 2) ^ 2 = z ^ 3 * z := by ring
      _ = z := by rw [hz, one_mul]
  let v : p48qAction.eigenspace z :=
    ⟨fourierComponent (z ^ 2) b, by simpa only [hz4] using fourierComponent_mem b (z ^ 2) hz2⟩
  obtain ⟨e, he⟩ := exists_creator_basis B m
  have hdual (i j : Fin 16) :
      p48qForm (e i : Cartan) (annihilatorDual B (j, m)) = if i = j then 1 else 0 := by
    rw [he i, pair_modes]
  have hroot (i : Fin 16) : modeRoot (i, m) = z := rfl
  simp only [creationCoordinate_projected, annihilationPairing_projected, hroot]
  change (∑ i : Fin 16, p48qForm (v : Cartan) (annihilatorDual B (i, m)) *
      p48qForm (fourierComponent z a) (creator B (i, m))) =
    p48qForm (fourierComponent z a) (v : Cartan)
  simpa only [he] using
    (sum_pairing_basis e (fun i => annihilatorDual B (i, m)) hdual v (fourierComponent z a))

/-- The scalar shift equals the exponent of the native P48q contraction. -/
theorem translationShift_eq_contractionExponent (B : FixedDualBases) (a b : Charge lattice) :
    translationShift B a b = contractionExponent a b := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_translationShift,
      P48qNativeContraction.constantCoeff_contractionExponent]
  | succ m =>
    rw [coeff_translationShift_succ, sum_creationCoordinate_mul_annihilationPairing,
      P48qNativeContraction.coeff_contractionExponent_opposite a b (Nat.succ_ne_zero m)]
    let r : ℂ := (m.succ : ℂ) / 3
    let pairing : ℂ := complexPairing (fourierComponent (ζ ^ (m.succ % 3)) a)
      (fourierComponent ((ζ ^ (m.succ % 3)) ^ 2) b)
    change -(r⁻¹ * pairing) = -pairing / r
    calc
      _ = -(pairing * r⁻¹) := congrArg Neg.neg (mul_comm r⁻¹ pairing)
      _ = _ := by rw [div_eq_mul_inv (-pairing) r, neg_mul pairing r⁻¹]

/-- Two-variable oscillator reordering for the native charged P48q fields. -/
theorem translated_creationExponential_eq_contraction
    (B : FixedDualBases) (a b : Charge lattice) :
    PowerSeries.mapAlgHom (translatedPolynomial B a) (creationExponential B b) =
      PowerSeries.mapAlgHom (Polynomial.CAlgHom : Fock →ₐ[ℂ] Polynomial Fock)
        (creationExponential B b) *
        atCoverRatio ((PowerSeries.exp ℂ).subst (contractionExponent a b)) := by
  rw [translated_creationExponential, translationShift_eq_contractionExponent]

@[simp] theorem constantCoeff_contraction_atCoverRatio (a b : Charge lattice) :
    PowerSeries.constantCoeff
      (atCoverRatio ((PowerSeries.exp ℂ).subst (contractionExponent a b))) = 1 := by
  have h := constantCoeff_formalExp (P48qNativeContraction.constantCoeff_contractionExponent a b)
  change PowerSeries.constantCoeff ((PowerSeries.exp ℂ).subst (contractionExponent a b)) = 1 at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_atCoverRatio,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, h, pow_zero, map_one, one_mul]

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
