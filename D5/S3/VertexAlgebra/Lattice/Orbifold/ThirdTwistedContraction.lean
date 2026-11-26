/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized order-three lattice contraction and its complementary Fourier coefficient. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.PowerSeries.Log
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
The scalar exponential in Bojko Bakalov and Victor G. Kac,
*Twisted Modules over Lattice Vertex Algebras*, arXiv:math/0402315v3, Lemma 4.2.
In (4.34), factor `z^(1/3)` out of each binomial and write `X` for the
formal coordinate `(w/z)^(1/3)`. The resulting power series has constant
coefficient one. The integral exponents are the native orbit pairings.
The product identity holds for any complex phase. When the phase is a
cubic root of unity and the action is a cubic isometry, the coefficient
at frequency `n/3` pairs the complementary Fourier components.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open ThirdTwistedChargeCocycle (pairing_shift_one pairing_shift_two)
open PowerSeries
open scoped BigOperators

noncomputable section

variable (D : LatticeData) (g : Charge D ≃+ Charge D) (ζ : ℂ)

/-- The series in the scalar exponential, in the coordinate `X = (w/z)^(1/3)`. -/
def contractionExponent (a b : Charge D) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 0 else
    -(∑ j ∈ Finset.range 3,
      (bilinear D ((g^[j]) a) b : ℂ) * ζ ^ (j * n)) / (n : ℂ)

private theorem coeff_contractionExponent (a b : Charge D) (n : ℕ) :
    coeff n (contractionExponent D g ζ a b) = if n = 0 then 0 else
      -(∑ j ∈ Finset.range 3,
        (bilinear D ((g^[j]) a) b : ℂ) * ζ ^ (j * n)) / (n : ℂ) :=
  coeff_mk _ _

@[simp] theorem constantCoeff_contractionExponent (a b : Charge D) :
    constantCoeff (contractionExponent D g ζ a b) = 0 := by
  simp [contractionExponent]

/-- The unit with underlying series `1 - c X`. Its integer powers include inverse powers. -/
def binomialUnit (c : ℂ) : (PowerSeries ℂ)ˣ :=
  (isUnit_iff_constantCoeff.mpr
    (show IsUnit (constantCoeff (1 - C c * X)) by simp)).unit

@[simp] theorem coe_binomialUnit (c : ℂ) :
    (binomialUnit c : PowerSeries ℂ) = 1 - C c * X :=
  IsUnit.unit_spec _

private def formalExp (f : PowerSeries ℂ) : PowerSeries ℂ := (exp ℂ).subst f

private theorem formalExp_zero : formalExp 0 = 1 := by
  simp [formalExp, subst_zero_eq_C_constantCoeff]

private theorem constantCoeff_formalExp {f : PowerSeries ℂ} (hf : constantCoeff f = 0) :
    constantCoeff (formalExp f) = 1 := by
  rw [formalExp, constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero hf,
    constantCoeff_exp, map_one]

private theorem formalExp_mul_neg {f : PowerSeries ℂ} (hf : constantCoeff f = 0) :
    formalExp f * formalExp (-f) = 1 := by
  have hs : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  have hone : (1 : PowerSeries ℂ).subst f = 1 := by
    rw [← coe_substAlgHom hs, map_one]
  have h := congrArg (fun F : PowerSeries ℂ => F.subst f)
    (exp_mul_exp_eq_exp_add (1 : ℂ) (-1))
  change (rescale 1 (exp ℂ) * rescale (-1) (exp ℂ)).subst f =
    (rescale (1 + -1) (exp ℂ)).subst f at h
  rw [rescale_one, RingHom.id_apply, add_neg_cancel, rescale_zero_apply,
    constantCoeff_exp, map_one, hone, subst_mul hs, rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X' (-1 : ℂ)) hs,
    subst_smul hs, subst_X hs, neg_one_smul] at h
  exact h

-- Extend the exponential product law to substitutions by zero-constant series.
private theorem formalExp_add {f h : PowerSeries ℂ}
    (hf : constantCoeff f = 0) (hh : constantCoeff h = 0) :
    formalExp (f + h) = formalExp f * formalExp h := by
  letI : HasUniqueDiv ℂ := .of_module_rat ℂ
  have hsum : constantCoeff (f + h) = 0 := by simp [hf, hh]
  have hneg : constantCoeff (-(f + h)) = 0 := by simp [hf, hh]
  have hderiv (v : PowerSeries ℂ) (hv : constantCoeff v = 0) :
      derivative (formalExp v) = formalExp v * derivative v := by
    unfold formalExp
    rw [derivative_subst (HasSubst.of_constantCoeff_zero' hv), derivative_exp]
  have hprod : formalExp f * formalExp h * formalExp (-(f + h)) = 1 := by
    apply derivative.ext
    · simp only [Derivation.leibniz, hderiv f hf, hderiv h hh, hderiv _ hneg,
        derivative_one, smul_eq_mul, map_neg, map_add]
      ring
    · simp only [map_mul, constantCoeff_formalExp hf, constantCoeff_formalExp hh,
        constantCoeff_formalExp hneg, one_mul, map_one]
  calc
    formalExp (f + h) =
        (formalExp f * formalExp h * formalExp (-(f + h))) * formalExp (f + h) := by
          rw [hprod, one_mul]
    _ = _ := by
      rw [mul_assoc, mul_comm (formalExp (-(f + h))) (formalExp (f + h)),
        formalExp_mul_neg hsum, mul_one]

private theorem formalExp_zsmul {f : PowerSeries ℂ} (hf : constantCoeff f = 0)
    (u : (PowerSeries ℂ)ˣ) (hu : (u : PowerSeries ℂ) = formalExp f) (k : ℤ) :
    formalExp (k • f) = (↑(u ^ k) : PowerSeries ℂ) := by
  have hz (i : ℤ) : constantCoeff (i • f) = 0 := by simp [hf]
  have hunit (i : ℤ) : IsUnit (formalExp (i • f)) :=
    isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_formalExp (hz i)]; exact isUnit_one)
  let F : Multiplicative ℤ →* (PowerSeries ℂ)ˣ :=
    { toFun := fun i => (hunit i.toAdd).unit
      map_one' := by
        apply Units.ext
        change (↑(hunit 0).unit : PowerSeries ℂ) = 1
        rw [IsUnit.unit_spec, zero_smul, formalExp_zero]
      map_mul' := fun i j => by
        apply Units.ext
        change (↑(hunit (i.toAdd + j.toAdd)).unit : PowerSeries ℂ) =
          (↑((hunit i.toAdd).unit * (hunit j.toAdd).unit) : PowerSeries ℂ)
        simp only [Units.val_mul, IsUnit.unit_spec, add_smul,
          formalExp_add (hz i.toAdd) (hz j.toAdd)] }
  have hF : F (Multiplicative.ofAdd (1 : ℤ)) = u := by
    apply Units.ext
    change (↑(hunit 1).unit : PowerSeries ℂ) = (u : PowerSeries ℂ)
    rw [IsUnit.unit_spec, one_smul, hu]
  have hk : Multiplicative.ofAdd (1 : ℤ) ^ k = Multiplicative.ofAdd k := by
    change k • (1 : ℤ) = k
    simp
  have hpow := F.map_zpow (Multiplicative.ofAdd (1 : ℤ)) k
  rw [hk, hF] at hpow
  change (hunit k).unit = u ^ k at hpow
  simpa only [IsUnit.unit_spec] using congrArg (fun v : (PowerSeries ℂ)ˣ =>
    (v : PowerSeries ℂ)) hpow

private theorem formalExp_sum_range (f : ℕ → PowerSeries ℂ)
    (hf : ∀ j, constantCoeff (f j) = 0) (m : ℕ) :
    formalExp (∑ j ∈ Finset.range m, f j) = ∏ j ∈ Finset.range m, formalExp (f j) := by
  induction m with
  | zero => simp [formalExp_zero]
  | succ m ih =>
    have hsum : constantCoeff (∑ j ∈ Finset.range m, f j) = 0 := by simp [map_sum, hf]
    rw [Finset.sum_range_succ, Finset.prod_range_succ, formalExp_add hsum (hf m), ih]

private def logBinomial (c : ℂ) : PowerSeries ℂ := rescale (-c) (log ℂ)

private theorem coeff_logBinomial (c : ℂ) (n : ℕ) :
    coeff n (logBinomial c) = if n = 0 then 0 else -(c ^ n) / (n : ℂ) := by
  by_cases hn : n = 0
  · simp [logBinomial, hn]
  simp only [logBinomial, coeff_rescale, coeff_log, ite_eq_right hn, map_div₀, map_pow,
    map_neg, map_one, map_natCast]
  rw [neg_pow c n, pow_succ (-1 : ℂ) n]
  calc
    _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (-(c ^ n) / (n : ℂ)) := by ring
    _ = _ := by rw [← mul_pow]; simp

private theorem constantCoeff_logBinomial (c : ℂ) : constantCoeff (logBinomial c) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logBinomial, if_pos rfl]

private theorem formalExp_logBinomial (c : ℂ) :
    formalExp (logBinomial c) = (binomialUnit c : PowerSeries ℂ) := by
  rw [formalExp, logBinomial, rescale_eq_subst,
    ← subst_comp_subst_apply HasSubst.log (HasSubst.smul_X' (-c)), subst_exp_log,
    ← rescale_eq_subst, map_add, map_one, rescale_X, map_neg, neg_mul, ← sub_eq_add_neg,
    coe_binomialUnit]

/-- The normalized scalar contraction in Bakalov–Kac (4.34). Each factor is raised to
its native integral orbit pairing in the group of power-series units. -/
theorem scalar_contraction (a b : Charge D) :
    (exp ℂ).subst (contractionExponent D g ζ a b) =
      (↑(∏ j ∈ Finset.range 3,
        binomialUnit (ζ ^ j) ^ bilinear D ((g^[j]) a) b) : PowerSeries ℂ) := by
  let f (j : ℕ) : PowerSeries ℂ := bilinear D ((g^[j]) a) b • logBinomial (ζ ^ j)
  have hf (j : ℕ) : constantCoeff (f j) = 0 := by simp [f, constantCoeff_logBinomial]
  have hexponent : contractionExponent D g ζ a b = ∑ j ∈ Finset.range 3, f j := by
    apply PowerSeries.ext
    intro n
    rw [coeff_contractionExponent, map_sum]
    by_cases hn : n = 0
    · simp [f, coeff_logBinomial, hn]
    rw [ite_eq_right hn]
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [f]
    rw [zsmul_eq_mul, coeff_intCast_mul, coeff_logBinomial, ite_eq_right hn, ← pow_mul ζ j n]
    ring
  change formalExp (contractionExponent D g ζ a b) = _
  rw [hexponent, formalExp_sum_range f hf, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact formalExp_zsmul (constantCoeff_logBinomial (ζ ^ j)) (binomialUnit (ζ ^ j))
    (formalExp_logBinomial (ζ ^ j)).symm (bilinear D ((g^[j]) a) b)

/-- The complex scalar extension of the native lattice pairing. -/
def complexPairing : LinearMap.BilinForm ℂ (Fin D.rank → ℂ) :=
  (D.G.map (Int.castRingHom ℂ)).toBilin'

private def castCharge (a : Charge D) : Fin D.rank → ℂ := fun i => (a i : ℂ)

private theorem complexPairing_castCharge (a b : Charge D) :
    complexPairing D (castCharge D a) (castCharge D b) = (bilinear D a b : ℂ) := by
  simp only [complexPairing, Matrix.toBilin'_apply, Matrix.map_apply, Int.coe_castRingHom,
    castCharge, bilinear, Int.cast_sum, Int.cast_mul]

/-- The Fourier component lies in the `u⁻¹` eigenspace when `g ^ 3 = 1` and `u ^ 3 = 1`. -/
def fourierComponent (u : ℂ) (a : Charge D) : Fin D.rank → ℂ :=
  (3 : ℂ)⁻¹ • (castCharge D a + u • castCharge D (g a) + u ^ 2 • castCharge D (g (g a)))

variable (h3 : ∀ a, g (g (g a)) = a)
variable (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)

include h3 hg in
private theorem opposite_pairing (a b : Charge D) (u : ℂ) (hu : u ^ 3 = 1) :
    complexPairing D (fourierComponent D g u a) (fourierComponent D g (u ^ 2) b) =
      (3 : ℂ)⁻¹ * ((bilinear D a b : ℂ) + u * (bilinear D (g a) b : ℂ) +
        u ^ 2 * (bilinear D (g (g a)) b : ℂ)) := by
  have hu4 : u ^ 4 = u := by rw [show (4 : ℕ) = 3 + 1 by decide, pow_succ, hu, one_mul]
  have hsq : (u ^ 2) ^ 2 = u := by rw [← pow_mul]; exact hu4
  simp only [fourierComponent, hsq, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, complexPairing_castCharge]
  simp only [hg]
  simp only [pairing_shift_two D g hg h3, pairing_shift_one D g hg h3, h3]
  set p := (bilinear D a b : ℂ)
  set q := (bilinear D (g a) b : ℂ)
  set r := (bilinear D (g (g a)) b : ℂ)
  calc
    _ = (3 : ℂ)⁻¹ * (3 : ℂ)⁻¹ *
        ((1 + u ^ 3 + u ^ 3) * p + (u + u + u ^ 4) * q + (u ^ 2 + u ^ 2 + u ^ 2) * r) :=
      by ring
    _ = _ := by rw [hu, hu4]; ring

include h3 hg in
/-- At positive frequency `n/3`, the coefficient uses the pairing of complementary
Fourier components. For `u = ζ^(n % 3)`, the second component has eigenvalue `u`. -/
theorem coeff_contractionExponent_opposite (hζ : ζ ^ 3 = 1)
    (a b : Charge D) {n : ℕ} (hn : n ≠ 0) :
    coeff n (contractionExponent D g ζ a b) =
      -(complexPairing D (fourierComponent D g (ζ ^ (n % 3)) a)
        (fourierComponent D g ((ζ ^ (n % 3)) ^ 2) b)) / ((n : ℂ) / 3) := by
  let u : ℂ := ζ ^ (n % 3)
  have hu : u ^ 3 = 1 := by dsimp [u]; rw [pow_right_comm, hζ, one_pow]
  have hpow (j : ℕ) : ζ ^ (j * n) = u ^ j := by
    rw [pow_mul, pow_right_comm]
    exact congrArg (fun c : ℂ => c ^ j) (pow_eq_pow_mod n hζ)
  change coeff n (contractionExponent D g ζ a b) =
    -(complexPairing D (fourierComponent D g u a) (fourierComponent D g (u ^ 2) b)) / ((n : ℂ) / 3)
  rw [coeff_contractionExponent, if_neg hn, opposite_pairing D g h3 hg a b u hu]
  simp_rw [hpow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Function.iterate_succ_apply', Function.iterate_zero_apply, pow_zero, pow_one, mul_one]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp <;> ring

/--
info: 'D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction.scalar_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms scalar_contraction
/--
info: 'D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction.coeff_contractionExponent_opposite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coeff_contractionExponent_opposite

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction
