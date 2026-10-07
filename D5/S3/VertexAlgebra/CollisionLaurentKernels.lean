/- GID: D5/S3/VertexAlgebra/CollisionLaurentKernels
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/CollisionLaurentKernels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-integer Laurent collision kernels and rational residue base change. -/

/-
All-integer Laurent collision kernels and rational residue base change.

The proof uses the native mathlib Hahn/Laurent and polynomial kernels.
LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio;
HahnSeries: Aaron Anderson; partial fractions: Kevin Buzzard, Sidharth Hariharan,
Aaron Liu. These library sources are released under Apache 2.0.
Actual HVertexOperator and VertexOperator composition: Scott Carnahan, Apache 2.0.
The imported normal-product supplier attributes its adaptation to Carnahan's
vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea (Apache 2.0).
No actual Monster carrier or fused-state identification is asserted.
-/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.PartialFractions

import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.Algebra.Order.PUnit
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic.Abel
import D5.S3.VertexAlgebra.UniformGradedLocalCorrelator

noncomputable section
namespace D5.S3.VertexAlgebra

section
/- Laurent collision for generic fields; no Moonshine carrier identification.
   The inner polynomial variable is x; the outer polynomial variable is z.
   Iterated Laurent outer variables are the smaller variables in the expansion.
   Mathlib LaurentSeries: Anderson/de Frutos-Fernández/Nuccio;
   bivariate swap and binomial infrastructure are reused, not newly claimed. -/
namespace CollisionLaurentKernels.LaurentCollision
open scoped PowerSeries LaurentSeries
open HahnSeries

variable (K : Type*) [Field K]
abbrev Bivariate := Polynomial (Polynomial K)
abbrev Rational := FractionRing (Bivariate K)
abbrev ZX := LaurentSeries (LaurentSeries K) -- inner z, outer x: |z| > |x|
abbrev XZ := LaurentSeries (LaurentSeries K) -- inner x, outer z: |x| > |z|
abbrev Coefficients := ℤ → ℤ → K -- fixed labelled coordinates z,x

def polyXZ : Bivariate K →+* XZ K :=
  (algebraMap (Polynomial (LaurentSeries K)) (XZ K)).comp
    (Polynomial.mapRingHom (algebraMap (Polynomial K) (LaurentSeries K)))

theorem polyXZ_injective : Function.Injective (polyXZ K) := by
  exact (Polynomial.algebraMap_hahnSeries_injective ℤ).comp
    (Polynomial.map_injective _ (Polynomial.algebraMap_hahnSeries_injective ℤ))

def polyZX : Bivariate K →+* ZX K :=
  (polyXZ K).comp (Polynomial.Bivariate.swap (R := K)).toRingHom

theorem polyZX_injective : Function.Injective (polyZX K) :=
  (polyXZ_injective K).comp (Polynomial.Bivariate.swap (R := K)).injective

def iotaXZ : Rational K →+* XZ K := IsFractionRing.lift (polyXZ_injective K)
def iotaZX : Rational K →+* ZX K := IsFractionRing.lift (polyZX_injective K)

def coeffZX (F : ZX K) : Coefficients K := fun z x => (F.coeff x).coeff z

def resZ_XZ (F : XZ K) : LaurentSeries K := F.coeff (-1)
def resZ_ZX (F : ZX K) : LaurentSeries K :=
  F.map (HahnSeries.coeff.linearMap (R := K) (-1 : ℤ))

theorem coeff_resZ_ZX (F : ZX K) (x : ℤ) :
    (resZ_ZX K F).coeff x = coeffZX K F (-1) x := rfl


/-- The fused coordinate u is outer/smaller; x is inner. This is only a
polynomial coordinate change; no substitution on unrestricted series. -/
def fusedPoly : Bivariate K →+* XZ K :=
  (polyXZ K).comp
    (Polynomial.algEquivAevalXAddC (Polynomial.X : Polynomial K)).toRingHom

theorem fusedPoly_injective : Function.Injective (fusedPoly K) :=
  (polyXZ_injective K).comp
    (Polynomial.algEquivAevalXAddC (Polynomial.X : Polynomial K)).injective

def iotaFused : Rational K →+* XZ K := IsFractionRing.lift (fusedPoly_injective K)

/-- The binomial construction is a genuine supported power series for every
integer exponent. Its image is the field z-power, including negative powers. -/
def binomial (S : Type*) [Field S] (a : S) (k : ℤ) : LaurentSeries S :=
  HahnSeries.ofPowerSeries ℤ S
    (PowerSeries.rescale a (PowerSeries.binomialSeries S k))

lemma rescale_X (S : Type*) [Field S] (a : S) :
    PowerSeries.rescale a (PowerSeries.X : PowerSeries S) =
      PowerSeries.C a * PowerSeries.X := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  split_ifs with h
  · simp [h]
  · simp

lemma binomial_nat (S : Type*) [Field S] (a : S) (n : ℕ) :
    binomial S a (n : ℤ) = (1 + HahnSeries.single 1 a) ^ n := by
  simp only [binomial, PowerSeries.binomialSeries_nat, map_pow, map_add, map_one,
    rescale_X, map_mul, PowerSeries.coe_X, PowerSeries.coe_C,
    HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]

lemma binomial_add (S : Type*) [Field S] (a : S) (k l : ℤ) :
    binomial S a (k + l) = binomial S a k * binomial S a l := by
  simp only [binomial, PowerSeries.binomialSeries_add, map_mul]

lemma binomial_zero (S : Type*) [Field S] (a : S) : binomial S a 0 = 1 := by
  simpa using binomial_nat S a 0

lemma one_add_single_ne_zero (S : Type*) [Field S] (a : S) :
    (1 + HahnSeries.single (1 : ℤ) a : LaurentSeries S) ≠ 0 := by
  intro h
  have := congrArg (fun F : LaurentSeries S => F.coeff 0) h
  simpa using this

theorem binomial_zpow (S : Type*) [Field S] (a : S) (k : ℤ) :
    binomial S a k = (1 + HahnSeries.single 1 a) ^ k := by
  cases k with
  | ofNat n => simpa using binomial_nat S a n
  | negSucc n =>
    have prod := binomial_add S a (Int.negSucc n) (n + 1 : ℕ)
    rw [show Int.negSucc n + (n + 1 : ℕ) = 0 by omega,
      binomial_zero, binomial_nat] at prod
    have hn : (1 + HahnSeries.single (1 : ℤ) a : LaurentSeries S) ^ (n+1) ≠ 0 :=
      pow_ne_zero _ (one_add_single_ne_zero S a)
    apply (mul_right_inj' hn).mp
    rw [mul_comm _ (binomial S a (Int.negSucc n)), ← prod]
    rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ hn]

def T : LaurentSeries K := HahnSeries.single 1 1

lemma T_ne_zero : T K ≠ 0 := by simp [T]

def deltaZX : ZX K := HahnSeries.C (T K) - HahnSeries.single 1 1
def deltaXZ : XZ K := HahnSeries.single 1 1 - HahnSeries.C (T K)

def kernelZX (k : ℤ) : ZX K :=
  HahnSeries.C ((T K) ^ k) * binomial (LaurentSeries K) (-(T K)⁻¹) k

def kernelXZ (k : ℤ) : XZ K :=
  HahnSeries.C ((-T K) ^ k) * binomial (LaurentSeries K) (-(T K)⁻¹) k

lemma factorZX :
    HahnSeries.C (T K) * (1 + HahnSeries.single 1 (-(T K)⁻¹)) = deltaZX K := by
  simp [deltaZX, mul_add, HahnSeries.C_apply, HahnSeries.single_mul_single,
    mul_inv_cancel₀ (T_ne_zero K), sub_eq_add_neg, ← HahnSeries.single_neg]

lemma factorXZ :
    HahnSeries.C (-T K) * (1 + HahnSeries.single 1 (-(T K)⁻¹)) = deltaXZ K := by
  simp [deltaXZ, mul_add, HahnSeries.C_apply, HahnSeries.single_mul_single,
    mul_inv_cancel₀ (T_ne_zero K), sub_eq_add_neg, ← HahnSeries.single_neg, add_comm]

theorem kernelZX_zpow (k : ℤ) : kernelZX K k = deltaZX K ^ k := by
  rw [kernelZX, binomial_zpow, map_zpow₀, ← mul_zpow, factorZX]

theorem kernelXZ_zpow (k : ℤ) : kernelXZ K k = deltaXZ K ^ k := by
  rw [kernelXZ, binomial_zpow, map_zpow₀, ← mul_zpow, factorXZ]

lemma kernelZX_coeff_nat (k : ℤ) (n : ℕ) :
    (kernelZX K k).coeff n =
      HahnSeries.single (k - n) (((-1 : K) ^ n) * ((Ring.choose k n : ℤ) : K)) := by
  rw [kernelZX, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    binomial, LaurentSeries.coeff_coe_powerSeries]
  simp only [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
    zsmul_eq_mul, mul_one]
  dsimp only [T]
  rw [← RatFunc.single_zpow k, HahnSeries.inv_single, inv_one,
    ← HahnSeries.single_neg, HahnSeries.single_pow]
  have cast_eq : ((Ring.choose k n : ℤ) : LaurentSeries K) =
      HahnSeries.single 0 ((Ring.choose k n : ℤ) : K) := by
    rw [← map_intCast (HahnSeries.C : K →+* LaurentSeries K)]
    rfl
  rw [cast_eq, HahnSeries.single_mul_single, HahnSeries.single_mul_single]
  congr 1
  · simp [nsmul_eq_mul, sub_eq_add_neg]
  · simp

def z (K : Type*) [Field K] : Rational K :=
  algebraMap (Bivariate K) (Rational K) Polynomial.X

def x (K : Type*) [Field K] : Rational K :=
  algebraMap (Bivariate K) (Rational K) (Polynomial.C Polynomial.X)

def diagonal (K : Type*) [Field K] : Rational K := z K - x K

lemma polyXZ_X : polyXZ K Polynomial.X = HahnSeries.single 1 1 := by
  simp [polyXZ, Polynomial.algebraMap_hahnSeries_apply, PowerSeries.coe_X]

lemma polyXZ_C_X : polyXZ K (Polynomial.C Polynomial.X) = HahnSeries.C (T K) := by
  simp [polyXZ, Polynomial.algebraMap_hahnSeries_apply, T, Polynomial.map_C,
    PowerSeries.coe_X, PowerSeries.coe_C]

lemma iotaXZ_diagonal : iotaXZ K (diagonal K) = deltaXZ K := by
  simp only [diagonal, z, x, map_sub, iotaXZ, IsFractionRing.lift_algebraMap]
  rw [polyXZ_X, polyXZ_C_X]
  rfl

lemma iotaZX_diagonal : iotaZX K (diagonal K) = deltaZX K := by
  simp only [diagonal, z, x, map_sub, iotaZX, IsFractionRing.lift_algebraMap]
  change polyXZ K (Polynomial.Bivariate.swap Polynomial.X) -
    polyXZ K (Polynomial.Bivariate.swap (Polynomial.C Polynomial.X)) = _
  rw [Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_X,
    polyXZ_X, polyXZ_C_X]
  rfl

lemma iotaFused_diagonal : iotaFused K (diagonal K) = HahnSeries.single 1 1 := by
  simp only [diagonal, z, x, map_sub, iotaFused, IsFractionRing.lift_algebraMap,
    fusedPoly, RingHom.comp_apply]
  simp [Polynomial.algEquivAevalXAddC_apply, polyXZ_X, polyXZ_C_X]

lemma kernelZX_coeff_neg (k : ℤ) (n : ℤ) (hn : n < 0) :
    (kernelZX K k).coeff n = 0 := by
  rw [kernelZX, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  simp only [binomial, PowerSeries.coeff_coe, hn, ↓reduceIte, mul_zero]

theorem kernelXZ_residue (k : ℤ) : resZ_XZ K (kernelXZ K k) = 0 := by
  rw [resZ_XZ, kernelXZ, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  simp only [binomial, PowerSeries.coeff_coe, show (-1 : ℤ) < 0 by omega,
    ↓reduceIte, mul_zero]

lemma choose_boundary (n : ℕ) (hn : n ≠ 0) : Ring.choose ((n : ℤ) - 1) n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [show ((m + 1 : ℕ) : ℤ) - 1 = m by omega, Ring.choose_natCast,
    Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m)]
  rfl

theorem kernelZX_residue (k : ℤ) :
    resZ_ZX K (kernelZX K k) = if k = -1 then 1 else 0 := by
  ext n
  rw [coeff_resZ_ZX]
  change ((kernelZX K k).coeff n).coeff (-1) = _
  cases n with
  | negSucc n =>
    rw [kernelZX_coeff_neg K k _ (Int.negSucc_lt_zero n)]
    split_ifs <;> simp
  | ofNat n =>
    change ((kernelZX K k).coeff (n : ℤ)).coeff (-1) = _
    rw [kernelZX_coeff_nat, HahnSeries.coeff_single]
    by_cases h : k = -1
    · subst k
      by_cases hn : n = 0
      · simp [hn]
      · have ne : (-1 : ℤ) ≠ -1 - n := by omega
        simp [ne, hn]
    · simp only [h, ↓reduceIte, HahnSeries.coeff_zero]
      split_ifs with he
      · have hk : k = (n : ℤ) - 1 := by omega
        have hn : n ≠ 0 := by intro hzero; apply h; omega
        rw [hk, choose_boundary n hn]
        simp
      · rfl

/-- Arbitrary-order pure diagonal pole, with every integer residue weight.
This is a genuine identity of the two different rational embeddings. -/
theorem diagonal_pole_jump (p : ℕ) (r : ℤ) :
    resZ_ZX K (iotaZX K ((diagonal K) ^ (r - p))) -
      resZ_XZ K (iotaXZ K ((diagonal K) ^ (r - p))) =
    resZ_XZ K (iotaFused K ((diagonal K) ^ (r - p))) := by
  rw [map_zpow₀, map_zpow₀, map_zpow₀,
    iotaZX_diagonal, iotaXZ_diagonal, iotaFused_diagonal,
    ← kernelZX_zpow, ← kernelXZ_zpow, kernelZX_residue, kernelXZ_residue,
    sub_zero, resZ_XZ, ← RatFunc.single_zpow]
  simp [HahnSeries.coeff_single, eq_comm]

lemma resZX_add (F G : ZX K) :
    resZ_ZX K (F + G) = resZ_ZX K F + resZ_ZX K G := by
  ext n
  simp [resZ_ZX, HahnSeries.map_coeff]

lemma resXZ_add (F G : XZ K) :
    resZ_XZ K (F + G) = resZ_XZ K F + resZ_XZ K G := by
  simp [resZ_XZ]

lemma resZX_mul_outerT (F : ZX K) :
    resZ_ZX K (HahnSeries.single 1 1 * F) = T K * resZ_ZX K F := by
  ext n
  simp only [resZ_ZX, HahnSeries.map_coeff, HahnSeries.coeff.linearMap_apply,
    HahnSeries.coeff_single_mul, one_mul, T]

lemma resXZ_mul_innerT (F : XZ K) :
    resZ_XZ K (HahnSeries.C (T K) * F) = T K * resZ_XZ K F := by
  rw [resZ_XZ, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rfl

lemma deltaZX_ne_zero : deltaZX K ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : ZX K => f.coeff 0) h
  simpa [deltaZX, HahnSeries.C_apply, T_ne_zero K] using h0

lemma deltaXZ_ne_zero : deltaXZ K ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : XZ K => f.coeff 0) h
  simpa [deltaXZ, HahnSeries.C_apply, T_ne_zero K] using h0

lemma multiply_recurrence {S : Type*} [Field S] (t d a : S) (hd : d ≠ 0)
    (ht : t = d + a) (m : ℕ) (k : ℤ) :
    t ^ (m + 1) * d ^ k = t ^ m * d ^ (k + 1) + a * (t ^ m * d ^ k) := by
  rw [pow_succ, zpow_add₀ hd, zpow_one]
  nth_rw 2 [ht]
  ring

def numeratorZX (m : ℕ) (k : ℤ) : ZX K :=
  HahnSeries.C (T K) ^ m * deltaZX K ^ k

def numeratorXZ (m : ℕ) (k : ℤ) : XZ K :=
  (HahnSeries.single 1 1 : XZ K) ^ m * deltaXZ K ^ k

def numeratorFused (m : ℕ) (k : ℤ) : XZ K :=
  (HahnSeries.single 1 1 + HahnSeries.C (T K) : XZ K) ^ m *
    (HahnSeries.single 1 1 : XZ K) ^ k

lemma numeratorZX_rec (m : ℕ) (k : ℤ) :
    resZ_ZX K (numeratorZX K (m + 1) k) =
    resZ_ZX K (numeratorZX K m (k + 1)) + T K * resZ_ZX K (numeratorZX K m k) := by
  unfold numeratorZX
  rw [multiply_recurrence _ _ _ (deltaZX_ne_zero K)
    (show HahnSeries.C (T K) = deltaZX K + HahnSeries.single 1 1 by
      simp [deltaZX]), resZX_add, resZX_mul_outerT]

lemma numeratorXZ_rec (m : ℕ) (k : ℤ) :
    resZ_XZ K (numeratorXZ K (m + 1) k) =
    resZ_XZ K (numeratorXZ K m (k + 1)) + T K * resZ_XZ K (numeratorXZ K m k) := by
  unfold numeratorXZ
  rw [multiply_recurrence _ _ _ (deltaXZ_ne_zero K)
    (show (HahnSeries.single 1 1 : XZ K) = deltaXZ K + HahnSeries.C (T K) by
      simp [deltaXZ]), resXZ_add, resXZ_mul_innerT]

lemma numeratorFused_rec (m : ℕ) (k : ℤ) :
    resZ_XZ K (numeratorFused K (m + 1) k) =
    resZ_XZ K (numeratorFused K m (k + 1)) + T K * resZ_XZ K (numeratorFused K m k) := by
  unfold numeratorFused
  rw [multiply_recurrence
    (HahnSeries.single 1 1 + HahnSeries.C (T K) : XZ K)
    (HahnSeries.single 1 1 : XZ K) (HahnSeries.C (T K))
    (by simp) rfl m k, resXZ_add, resXZ_mul_innerT]

/-- All degrees of a polynomial z-numerator, all integer diagonal exponents.
The induction uses residue intertwining with x, not a desired jump premise. -/
theorem polynomial_monomial_jump (m : ℕ) (k : ℤ) :
    resZ_ZX K (numeratorZX K m k) - resZ_XZ K (numeratorXZ K m k) =
      resZ_XZ K (numeratorFused K m k) := by
  induction m generalizing k with
  | zero =>
    simpa [numeratorZX, numeratorXZ, numeratorFused, iotaZX_diagonal,
      iotaXZ_diagonal, iotaFused_diagonal] using
      diagonal_pole_jump K 0 k
  | succ m ih =>
    rw [numeratorZX_rec, numeratorXZ_rec, numeratorFused_rec,
      ← ih (k + 1), ← ih k]
    ring

lemma iotaZX_z : iotaZX K (z K) = HahnSeries.C (T K) := by
  rw [z, iotaZX, IsFractionRing.lift_algebraMap]
  change polyXZ K (Polynomial.Bivariate.swap Polynomial.X) = _
  rw [Polynomial.Bivariate.swap_Y, polyXZ_C_X]

lemma iotaXZ_z : iotaXZ K (z K) = HahnSeries.single 1 1 := by
  rw [z, iotaXZ, IsFractionRing.lift_algebraMap, polyXZ_X]

lemma iotaFused_z : iotaFused K (z K) =
    HahnSeries.single 1 1 + HahnSeries.C (T K) := by
  rw [z, iotaFused, IsFractionRing.lift_algebraMap]
  change polyXZ K ((Polynomial.algEquivAevalXAddC Polynomial.X) Polynomial.X) = _
  simp [Polynomial.algEquivAevalXAddC_apply, polyXZ_X, polyXZ_C_X]

/-- Genuine rational compatibility for arbitrary polynomial monomial z^m,
arbitrary pole order p, and every integer r. -/
theorem rational_monomial_jump (m p : ℕ) (r : ℤ) :
    resZ_ZX K (iotaZX K ((z K) ^ m * (diagonal K) ^ (r - p))) -
    resZ_XZ K (iotaXZ K ((z K) ^ m * (diagonal K) ^ (r - p))) =
    resZ_XZ K (iotaFused K ((z K) ^ m * (diagonal K) ^ (r - p))) := by
  simp only [map_mul, map_pow, map_zpow₀, iotaZX_z, iotaXZ_z, iotaFused_z,
    iotaZX_diagonal, iotaXZ_diagonal, iotaFused_diagonal]
  exact polynomial_monomial_jump K m (r - p)

end CollisionLaurentKernels.LaurentCollision
end

section
/- Exact coefficient-field base change for rational expansion at u=0.
No substitution of arbitrary Laurent series is assumed. -/
namespace CollisionLaurentKernels.ResidueBaseChange
open HahnSeries
open scoped RatFunc
variable {E F : Type*} [Field E] [Field F]

def seriesMap (f : E →+* F) : LaurentSeries E →+* LaurentSeries F where
  toFun g := g.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' g h := HahnSeries.map_add f.toAddMonoidHom
  map_mul' g h := HahnSeries.map_mul f.toNonUnitalRingHom

def polynomialMap (f : E →+* F) : Polynomial E →+* RatFunc F :=
  (algebraMap (Polynomial F) (RatFunc F)).comp (Polynomial.mapRingHom f)

lemma polynomialMap_injective (f : E →+* F) : Function.Injective (polynomialMap f) :=
  (RatFunc.algebraMap_injective F).comp (Polynomial.map_injective f f.injective)

def rationalMap (f : E →+* F) : RatFunc E →+* RatFunc F :=
  IsFractionRing.lift (polynomialMap_injective f)

end CollisionLaurentKernels.ResidueBaseChange
end

section
namespace CollisionLaurentKernels.PolynomialCollision
open CollisionLaurentKernels.LaurentCollision
variable (K : Type*) [Field K]

lemma resZX_outer_monomial (q : ℤ) (F : ZX K) :
    resZ_ZX K (HahnSeries.single q 1 * F) =
      HahnSeries.single q 1 * resZ_ZX K F := by
  ext n
  simp only [resZ_ZX, HahnSeries.map_coeff, HahnSeries.coeff.linearMap_apply,
    HahnSeries.coeff_single_mul, one_mul]

lemma resXZ_inner_scalar (a : LaurentSeries K) (F : XZ K) :
    resZ_XZ K (HahnSeries.C a * F) = a * resZ_XZ K F := by
  rw [resZ_XZ, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rfl

lemma iotaZX_x : iotaZX K (x K) = HahnSeries.single 1 1 := by
  rw [x, iotaZX, IsFractionRing.lift_algebraMap]
  change polyXZ K (Polynomial.Bivariate.swap (Polynomial.C Polynomial.X)) = _
  rw [Polynomial.Bivariate.swap_X, polyXZ_X]

lemma iotaXZ_x : iotaXZ K (x K) = HahnSeries.C (T K) := by
  rw [x, iotaXZ, IsFractionRing.lift_algebraMap, polyXZ_C_X]

lemma iotaFused_x : iotaFused K (x K) = HahnSeries.C (T K) := by
  rw [x, iotaFused, IsFractionRing.lift_algebraMap]
  change polyXZ K ((Polynomial.algEquivAevalXAddC Polynomial.X)
    (Polynomial.C Polynomial.X)) = _
  simp [Polynomial.algEquivAevalXAddC_apply, polyXZ_C_X]

/-- Includes all integer Laurent monomials in x, all polynomial degrees in z,
and every integer diagonal exponent. -/
theorem laurent_monomial_collision (q : ℤ) (m p : ℕ) (r : ℤ) :
    resZ_ZX K (iotaZX K (x K ^ q * (z K ^ m * diagonal K ^ (r-p)))) -
    resZ_XZ K (iotaXZ K (x K ^ q * (z K ^ m * diagonal K ^ (r-p)))) =
    resZ_XZ K (iotaFused K (x K ^ q * (z K ^ m * diagonal K ^ (r-p)))) := by
  simp only [map_mul, map_zpow₀, iotaZX_x, iotaXZ_x, iotaFused_x]
  rw [← map_zpow₀ (HahnSeries.C : LaurentSeries K →+* XZ K) (T K) q]
  rw [← RatFunc.single_zpow, resZX_outer_monomial, resXZ_inner_scalar,
    resXZ_inner_scalar]
  rw [RatFunc.single_zpow]
  change T K ^ q * resZ_ZX K
    (iotaZX K (z K ^ m) * iotaZX K (diagonal K) ^ (r-p)) -
    T K ^ q * resZ_XZ K
    (iotaXZ K (z K ^ m) * iotaXZ K (diagonal K) ^ (r-p)) = _
  rw [← mul_sub]
  congr 1
  simpa only [map_mul, map_zpow₀] using rational_monomial_jump K m p r

def constantR (a : K) : Rational K :=
  algebraMap (Bivariate K) (Rational K) (Polynomial.C (Polynomial.C a))

lemma polyXZ_constant (a : K) :
    polyXZ K (Polynomial.C (Polynomial.C a)) = HahnSeries.C (HahnSeries.C a) := by
  simp [polyXZ, Polynomial.algebraMap_hahnSeries_apply]

lemma iotaXZ_constant (a : K) :
    iotaXZ K (constantR K a) = HahnSeries.C (HahnSeries.C a) := by
  rw [constantR, iotaXZ, IsFractionRing.lift_algebraMap, polyXZ_constant]

lemma iotaZX_constant (a : K) :
    iotaZX K (constantR K a) = HahnSeries.C (HahnSeries.C a) := by
  rw [constantR, iotaZX, IsFractionRing.lift_algebraMap]
  change polyXZ K (Polynomial.Bivariate.swap (Polynomial.C (Polynomial.C a))) = _
  rw [Polynomial.Bivariate.swap_C_C, polyXZ_constant]

lemma iotaFused_constant (a : K) :
    iotaFused K (constantR K a) = HahnSeries.C (HahnSeries.C a) := by
  rw [constantR, iotaFused, IsFractionRing.lift_algebraMap]
  change polyXZ K ((Polynomial.algEquivAevalXAddC Polynomial.X)
    (Polynomial.C (Polynomial.C a))) = _
  simp [Polynomial.algEquivAevalXAddC_apply, polyXZ_constant]

lemma resZX_inner_constant (a : K) (F : ZX K) :
    resZ_ZX K (HahnSeries.C (HahnSeries.C a) * F) =
      HahnSeries.C a * resZ_ZX K F := by
  ext n
  change ((HahnSeries.C (HahnSeries.C a) * F).coeff n).coeff (-1) =
    (HahnSeries.C a * resZ_ZX K F).coeff n
  simp only [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  rfl

/-- Arbitrary finite Laurent-polynomial numerator in x and polynomial in z,
with any diagonal pole order and any integer residue weight. -/
theorem finite_numerator_collision {I : Type*} (s : Finset I) (a : I → K)
    (q : I → ℤ) (m : I → ℕ) (p : ℕ) (r : ℤ) :
    let R : Rational K := ∑ i ∈ s,
      constantR K (a i) * (x K ^ q i * (z K ^ m i * diagonal K ^ (r-p)))
    resZ_ZX K (iotaZX K R) - resZ_XZ K (iotaXZ K R) =
      resZ_XZ K (iotaFused K R) := by
  classical
  dsimp only
  simp only [map_sum]
  have hz : ∀ (Fs : I → ZX K), resZ_ZX K (∑ i ∈ s, Fs i) =
      ∑ i ∈ s, resZ_ZX K (Fs i) := by
    intro Fs
    induction s using Finset.induction with
    | empty => ext n; simp [resZ_ZX, HahnSeries.map_coeff]
    | @insert i s hi ih => simp [Finset.sum_insert hi, resZX_add, ih]
  have hx : ∀ (Fs : I → XZ K), resZ_XZ K (∑ i ∈ s, Fs i) =
      ∑ i ∈ s, resZ_XZ K (Fs i) := by
    intro Fs
    simp [resZ_XZ, HahnSeries.coeff_sum]
  rw [hz, hx, hx, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_mul, iotaZX_constant, iotaXZ_constant, iotaFused_constant]
  rw [resZX_inner_constant, resXZ_inner_scalar, resXZ_inner_scalar, ← mul_sub]
  congr 1
  simpa only [map_mul] using laurent_monomial_collision K (q i) (m i) p r

end CollisionLaurentKernels.PolynomialCollision
end

section
namespace CollisionLaurentKernels.RationalFusedResidue
open CollisionLaurentKernels.LaurentCollision CollisionLaurentKernels.ResidueBaseChange
open scoped RatFunc
variable (K : Type*) [Field K]

abbrev CoefficientField := RatFunc K -- x and any spectators already in K

def toCoefficientPoly : Bivariate K →+* Polynomial (CoefficientField K) :=
  Polynomial.mapRingHom (algebraMap (Polynomial K) (CoefficientField K))

def translatedPoly : Bivariate K →+* Polynomial (CoefficientField K) :=
  (Polynomial.algEquivAevalXAddC (RatFunc.X : CoefficientField K)).toRingHom.comp
    (toCoefficientPoly K)

lemma translatedPoly_injective : Function.Injective (translatedPoly K) :=
  (Polynomial.algEquivAevalXAddC (RatFunc.X : CoefficientField K)).injective.comp
    (Polynomial.map_injective _ (RatFunc.algebraMap_injective K))

def localPolynomial : Bivariate K →+* RatFunc (CoefficientField K) :=
  (algebraMap (Polynomial (CoefficientField K)) (RatFunc (CoefficientField K))).comp
    (translatedPoly K)

lemma localPolynomial_injective : Function.Injective (localPolynomial K) :=
  (RatFunc.algebraMap_injective (CoefficientField K)).comp (translatedPoly_injective K)

/-- R(z,x) is translated only at the rational level, z=u+x. -/
def localRational : Rational K →+* RatFunc (CoefficientField K) :=
  IsFractionRing.lift (localPolynomial_injective K)

def expandX : CoefficientField K →+* LaurentSeries K :=
  algebraMap (RatFunc K) (LaurentSeries K)

def fusedViaCoefficientField : Rational K →+* XZ K :=
  (seriesMap (expandX K)).comp
    ((algebraMap (RatFunc (CoefficientField K)) (LaurentSeries (CoefficientField K))).comp
      (localRational K))

/-- The rational u-residue belongs to the spectator-and-x coefficient field. -/
def localResidue (R : Rational K) : CoefficientField K :=
  (algebraMap (RatFunc (CoefficientField K)) (LaurentSeries (CoefficientField K))
    (localRational K R)).coeff (-1)

lemma translated_poly_square :
    (Polynomial.mapRingHom (expandX K)).comp (translatedPoly K) =
    (Polynomial.mapRingHom (algebraMap (Polynomial K) (LaurentSeries K))).comp
      (Polynomial.algEquivAevalXAddC (Polynomial.X : Polynomial K)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [translatedPoly, toCoefficientPoly, RingHom.comp_apply,
      Polynomial.algEquivAevalXAddC_apply, expandX,
      ← IsScalarTower.algebraMap_apply]
  · simp [translatedPoly, toCoefficientPoly, RingHom.comp_apply,
      Polynomial.algEquivAevalXAddC_apply, expandX, RatFunc.coe_X,
      Polynomial.algebraMap_hahnSeries_apply]

lemma fused_poly_square (p : Bivariate K) :
    fusedViaCoefficientField K (algebraMap (Bivariate K) (Rational K) p) =
    fusedPoly K p := by
  simp only [fusedViaCoefficientField, RingHom.comp_apply, localRational,
    IsFractionRing.lift_algebraMap, localPolynomial, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply (Polynomial (CoefficientField K))
    (RatFunc (CoefficientField K)) (LaurentSeries (CoefficientField K))]
  have mapped : seriesMap (expandX K)
      (algebraMap (Polynomial (CoefficientField K)) (LaurentSeries (CoefficientField K))
        (translatedPoly K p)) =
      algebraMap (Polynomial (LaurentSeries K)) (XZ K)
        ((translatedPoly K p).map (expandX K)) := by
    apply HahnSeries.ext
    funext n
    change expandX K
        ((algebraMap (Polynomial (CoefficientField K)) (LaurentSeries (CoefficientField K))
          (translatedPoly K p)).coeff n) = _
    simp only [Polynomial.algebraMap_hahnSeries_apply, PowerSeries.coeff_coe]
    split_ifs <;> simp [Polynomial.coeff_coe, Polynomial.coeff_map]
  rw [mapped]
  change algebraMap (Polynomial (LaurentSeries K)) (XZ K)
      (((Polynomial.mapRingHom (expandX K)).comp (translatedPoly K)) p) =
    algebraMap (Polynomial (LaurentSeries K)) (XZ K)
      (((Polynomial.mapRingHom (algebraMap (Polynomial K) (LaurentSeries K))).comp
        (Polynomial.algEquivAevalXAddC Polynomial.X).toRingHom) p)
  rw [translated_poly_square]

/-- The fused embedding constructed from the bivariate fraction field equals
translation in RatFunc(K(x)) followed by coefficient-field expansion. -/
theorem fused_embedding_square : fusedViaCoefficientField K = iotaFused K := by
  apply IsFractionRing.ringHom_ext (A := Bivariate K)
  intro p
  rw [iotaFused, IsFractionRing.lift_algebraMap]
  exact fused_poly_square K p

/-- Exact left-hand interface of the collision obligation, for every R. -/
theorem fused_residue_commutes (R : Rational K) :
    resZ_XZ K (iotaFused K R) = expandX K (localResidue K R) := by
  rw [← fused_embedding_square]
  rfl

/-- All m,p,r from the genuine scalar jump now have a rational u-residue,
expanded only after residue has been taken. -/
theorem rational_monomial_collision (m p : ℕ) (r : ℤ) :
    expandX K (localResidue K ((z K) ^ m * diagonal K ^ (r - p))) =
    resZ_ZX K (iotaZX K ((z K) ^ m * diagonal K ^ (r - p))) -
    resZ_XZ K (iotaXZ K ((z K) ^ m * diagonal K ^ (r - p))) := by
  rw [← fused_residue_commutes]
  exact (rational_monomial_jump K m p r).symm

end CollisionLaurentKernels.RationalFusedResidue
end

section
/- Adjacent residue cancellation for separated spectator-pole terms.
The coefficient field K is held fixed; this lemma does not silently reorder
spectator variables that occur inside a larger Laurent tower. -/
namespace CollisionLaurentKernels.SeparatedResidue
open CollisionLaurentKernels.LaurentCollision CollisionLaurentKernels.ResidueBaseChange
variable (K : Type*) [Field K]

def outerSeries (h : LaurentSeries K) : LaurentSeries (LaurentSeries K) :=
  seriesMap (HahnSeries.C : K →+* LaurentSeries K) h

/-- For every supported g(z) and h(x), both ordered expansions of the
separated product have the same z residue. No pole-order bound is imposed. -/
theorem separated_residue_cancel (g h : LaurentSeries K) :
    resZ_ZX K (HahnSeries.C g * outerSeries K h) =
    resZ_XZ K (HahnSeries.C h * outerSeries K g) := by
  ext n
  change ((HahnSeries.C g * outerSeries K h).coeff n).coeff (-1) =
    ((HahnSeries.C h * outerSeries K g).coeff (-1)).coeff n
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  change (g * HahnSeries.C (h.coeff n)).coeff (-1) =
    (h * HahnSeries.C (g.coeff (-1))).coeff n
  rw [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
    HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero, mul_comm]


lemma outerSeries_support_subset (h : LaurentSeries K) :
    (outerSeries K h).support ⊆ h.support := by
  intro n hn
  contrapose! hn
  simp only [HahnSeries.mem_support, not_not] at hn ⊢
  change h.coeff n = 0 at hn
  change HahnSeries.C (h.coeff n) = 0
  rw [hn, map_zero]

lemma residue_support_subset (F : ZX K) : (resZ_ZX K F).support ⊆ F.support := by
  intro n hn
  contrapose! hn
  simp only [HahnSeries.mem_support, not_not] at hn ⊢
  change F.coeff n = 0 at hn
  change (F.coeff n).coeff (-1) = 0
  rw [hn]
  rfl

/-- Arbitrary supported rational x-coefficients may be pulled through the
z-residue. The proof uses finite Hahn antidiagonals and their support bounds. -/
theorem residue_outerSeries_mul (h : LaurentSeries K) (F : ZX K) :
    resZ_ZX K (outerSeries K h * F) = h * resZ_ZX K F := by
  ext n
  change ((outerSeries K h * F).coeff n).coeff (-1) = (h * resZ_ZX K F).coeff n
  rw [HahnSeries.coeff_mul_left' h.isPWO_support (outerSeries_support_subset K h),
    HahnSeries.coeff_mul_right' F.isPWO_support (residue_support_subset K F)]
  rw [HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  change (HahnSeries.C (h.coeff ab.1) * F.coeff ab.2).coeff (-1) =
    h.coeff ab.1 * (F.coeff ab.2).coeff (-1)
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

end CollisionLaurentKernels.SeparatedResidue
end

end D5.S3.VertexAlgebra

/-
Actual supported field words and finite labelled convolution.

The proof uses the native mathlib Hahn/Laurent and polynomial kernels.
LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio;
HahnSeries: Aaron Anderson; partial fractions: Kevin Buzzard, Sidharth Hariharan,
Aaron Liu. These library sources are released under Apache 2.0.
Actual HVertexOperator and VertexOperator composition: Scott Carnahan, Apache 2.0.
The imported normal-product supplier attributes its adaptation to Carnahan's
vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea (Apache 2.0).
No actual Monster carrier or fused-state identification is asserted.
-/


noncomputable section
namespace D5.S3.VertexAlgebra

section
/- Binding of Carnahan's actual HVertexOperator composition, at arbitrary
finite rank. Coefficients remain actual products on the fixed suffix vector. -/
namespace SupportedFieldWords.OrderedWords
set_option backward.isDefEq.respectTransparency false
open scoped VertexOperator

def Indices : ℕ → Type
  | 0 => Unit
  | n + 1 => ℤ ×ₗ Indices n

instance indicesOrder (n : ℕ) : LinearOrder (Indices n) := by
  induction n with
  | zero => exact inferInstanceAs (LinearOrder Unit)
  | succ n ih => exact inferInstanceAs (LinearOrder (ℤ ×ₗ Indices n))

instance indicesGroup (n : ℕ) : AddCommGroup (Indices n) := by
  induction n with
  | zero => exact inferInstanceAs (AddCommGroup Unit)
  | succ n ih => exact inferInstanceAs (AddCommGroup (ℤ ×ₗ Indices n))

instance indicesOrdered (n : ℕ) : IsOrderedAddMonoid (Indices n) := by
  induction n with
  | zero => exact inferInstanceAs (IsOrderedAddMonoid Unit)
  | succ n ih => exact inferInstanceAs (IsOrderedAddMonoid (ℤ ×ₗ Indices n))

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def emptyField : HVertexOperator Unit K V V where
  toFun v := HahnModule.of K (HahnSeries.single () v)
  map_add' := by intros; ext g; simp
  map_smul' := by
    intro a v
    ext g
    cases g
    rw [HahnModule.of_symm_smul]
    simp

def ordered : (n : ℕ) → (Fin n → VertexOperator K V) → HVertexOperator (Indices n) K V V
  | 0, _ => emptyField
  | n + 1, A => HVertexOperator.comp
      (ordered n (fun i => A i.castSucc)) (A (Fin.last n))

def exponents : (n : ℕ) → (Fin n → ℤ) → Indices n
  | 0, _ => ()
  | n + 1, e => toLex (e (Fin.last n), exponents n (fun i => e i.castSucc))

def actualWord : (n : ℕ) → (Fin n → VertexOperator K V) → (Fin n → ℤ) → V → V
  | 0, _, _, c => c
  | n + 1, A, e, c => actualWord n (fun i => A i.castSucc) (fun i => e i.castSucc)
      ((A (Fin.last n) [[-e (Fin.last n) - 1]]) c)

/-- Every finite actual mode word embeds into the chosen ordered supported
Hahn carrier. Outer/smaller exponents have priority, from the word's right. -/
theorem ordered_coeff (n : ℕ) (A : Fin n → VertexOperator K V) (e : Fin n → ℤ) (c : V) :
    HVertexOperator.coeff (ordered n A) (exponents n e) c = actualWord n A e c := by
  induction n generalizing c with
  | zero =>
    change (HahnSeries.single () c).coeff () = c
    exact HahnSeries.coeff_single_same _ _
  | succ n ih =>
    change HVertexOperator.coeff
      (HVertexOperator.comp (ordered n (fun i => A i.castSucc)) (A (Fin.last n)))
      (toLex (e (Fin.last n), exponents n (fun i => e i.castSucc))) c = _
    rw [HVertexOperator.coeff_comp]
    simp only [LinearMap.comp_apply, VertexOperator.coeff_eq_ncoeff]
    exact ih _ _ _

/-- A prefix scalar functional and a grade selector compose at the terminal
coefficient; they do not change the supported input word. -/
def scalarOrdered (n : ℕ) (A : Fin n → VertexOperator K V) (c : V)
    (phi : V →ₗ[K] K) : HahnSeries (Indices n) K :=
  ((HahnModule.of K).symm (ordered n A c)).map phi

theorem scalarOrdered_coeff (n : ℕ) (A : Fin n → VertexOperator K V) (e : Fin n → ℤ)
    (c : V) (phi : V →ₗ[K] K) :
    (scalarOrdered n A c phi).coeff (exponents n e) = phi (actualWord n A e c) := by
  change phi (HVertexOperator.coeff (ordered n A) (exponents n e) c) = _
  rw [ordered_coeff]

end SupportedFieldWords.OrderedWords
end

section
/- Finite-convolution interface adapted from native
UniformGradedLocalCorrelator.shift/polynomialAction, with arbitrary ordered
exponent group and scalar field. No cancellation is used on unrestricted
coefficient distributions. Cancellation occurs only in HahnModule. -/
namespace SupportedFieldWords.FiniteConvolution
variable {Γ K V : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [AddCommGroup V] [Module K V]

abbrev Polynomial := AddMonoidAlgebra K Γ
abbrev Distribution := Γ → V

def shift (b : Γ) : Module.End K (Distribution (Γ := Γ) (V := V)) where
  toFun F := fun e => F (e-b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def shifts : Multiplicative Γ →* Module.End K (Distribution (Γ := Γ) (V := V)) where
  toFun b := shift b.toAdd
  map_one' := by ext F e; simp [shift]
  map_mul' b c := by
    ext F e
    change F (e-(b.toAdd+c.toAdd)) = F ((e-b.toAdd)-c.toAdd)
    congr 1
    abel

def distributionAction : Polynomial (Γ := Γ) (K := K) →ₐ[K]
    Module.End K (Distribution (Γ := Γ) (V := V)) :=
  AddMonoidAlgebra.lift K _ _ shifts

def scalarMonomials : Multiplicative Γ →* HahnSeries Γ K where
  toFun b := HahnSeries.single b.toAdd 1
  map_one' := by simp [← HahnSeries.C_apply]
  map_mul' b c := by simp [HahnSeries.single_mul_single]

def scalarPolynomial : Polynomial (Γ := Γ) (K := K) →ₐ[K] HahnSeries Γ K :=
  AddMonoidAlgebra.lift K _ _ scalarMonomials

def coefficients (F : HahnModule Γ K V) : Distribution (Γ := Γ) (V := V) :=
  ((HahnModule.of K).symm F).coeff

lemma scalarPolynomial_single (b : Γ) (a : K) :
    scalarPolynomial (AddMonoidAlgebra.single b a) = HahnSeries.single b a := by
  simp only [scalarPolynomial, AddMonoidAlgebra.lift_single, scalarMonomials,
    MonoidHom.coe_mk, OneHom.coe_mk]
  ext e
  simp [HahnSeries.coeff_smul, HahnSeries.coeff_single]

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
lemma distributionAction_single (b : Γ) (a : K) (F : Distribution (Γ := Γ) (V := V)) (e : Γ) :
    distributionAction (AddMonoidAlgebra.single b a) F e = a • F (e-b) := by
  simp [distributionAction, AddMonoidAlgebra.lift_single, shifts, shift]

theorem scalarPolynomial_coeff (Q : Polynomial (Γ := Γ) (K := K)) (e : Γ) :
    (scalarPolynomial Q).coeff e = Q.coeff e := by
  classical
  induction Q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp [hP, hQ]
  | single b a => simp [scalarPolynomial_single, HahnSeries.coeff_single, Finsupp.single_apply, eq_comm]

end SupportedFieldWords.FiniteConvolution
end

section
namespace SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.OrderedWords SupportedFieldWords.FiniteConvolution
set_option backward.isDefEq.respectTransparency false

def inverseExponents : (n : ℕ) → Indices n → (Fin n → ℤ)
  | 0, _ => fun i => Fin.elim0 i
  | n+1, g => Fin.lastCases (ofLex g).1 (inverseExponents n (ofLex g).2)

lemma inverse_exponents (n : ℕ) (e : Fin n → ℤ) :
    inverseExponents n (exponents n e) = e := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [exponents, inverseExponents, ofLex_toLex, ih]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma exponents_inverse (n : ℕ) (g : Indices n) :
    exponents n (inverseExponents n g) = g := by
  induction n with
  | zero => change () = g; cases g; rfl
  | succ n ih =>
    change toLex ((inverseExponents (n+1) g) (Fin.last n),
      exponents n (fun i => inverseExponents (n+1) g i.castSucc)) = g
    simp only [inverseExponents, Fin.lastCases_last, Fin.lastCases_castSucc, ih]
    rfl

lemma exponents_add (n : ℕ) (e f : Fin n → ℤ) :
    exponents n (e+f) = exponents n e + exponents n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change toLex (e (Fin.last n)+f (Fin.last n),
      exponents n ((fun i => e i.castSucc)+(fun i => f i.castSucc))) = _
    rw [ih]
    rfl

/-- Exact additive reindexing from the native distribution exponent type.
The last word variable becomes the first/outer lex exponent. -/
def exponentAddEquiv (n : ℕ) : (Fin n → ℤ) ≃+ Indices n where
  toFun := exponents n
  invFun := inverseExponents n
  left_inv := inverse_exponents n
  right_inv := exponents_inverse n
  map_add' := exponents_add n

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def labelledPolynomial (n : ℕ) :
    AddMonoidAlgebra K (Fin n → ℤ) →ₐ[K] AddMonoidAlgebra K (Indices n) :=
  AddMonoidAlgebra.mapDomainAlgHom K K (exponentAddEquiv n).toAddMonoidHom

def transportDistribution (n : ℕ) (F : (Fin n → ℤ) → V) : Indices n → V :=
  fun g => F ((exponentAddEquiv n).symm g)

end SupportedFieldWords.OrderedDistribution
end

end D5.S3.VertexAlgebra
end
