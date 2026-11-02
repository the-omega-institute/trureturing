/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPairKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianPairKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Binomial,
     mathlib/module/Mathlib.RingTheory.MvPowerSeries.Equiv]
   utility: none
   digest: The elementary regular two-current kernel has the original Corr pair coefficients. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic

/-!
Candidate adapted from the hash-pinned 2026-11-02 source supplier.
This module concerns formal scalar power series only; it makes no analytic
sewn-curve or infinite-resolvent correspondence claim.

The kernel is defined first by elementary formal root/inverse algebra. The
coefficient series is a separate comparison object. Equality is proved by the
cleared-diagonal equation and cancellation of the nonzero series `(a-b)^2`.
Thus no desired coefficient formula is used as the definition of the kernel.

`none` is the a coordinate and `some ()` the b coordinate. Iterated series are
only a coefficient interface; both variables belong to the same multivariate
power-series ring. All coefficients, including the diagonal and the two
lowest-degree boundaries, occur in the proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPairKernel

open LatticeHalfFockFiniteCorrection

abbrev OneSeries := PowerSeries ℂ
abbrev Series := MvPowerSeries (Option Unit) ℂ

private abbrev iter : Series ≃ₐ[ℂ] PowerSeries OneSeries :=
  MvPowerSeries.optionEquivLeft Unit ℂ

/-- The actual coefficient of a^m b^n. -/
def coeff₂ (m n : ℕ) (f : Series) : ℂ :=
  PowerSeries.coeff n (PowerSeries.coeff m (iter f))

private theorem coeff₂_constant (f : Series) :
    coeff₂ 0 0 f = MvPowerSeries.constantCoeff f := by
  change MvPowerSeries.coeff (Finsupp.single () 0)
    (PowerSeries.coeff 0 (MvPowerSeries.optionEquivLeft Unit ℂ f)) = _
  rw [MvPowerSeries.coeff_coeff_optionEquivLeft]
  simp only [Finsupp.single_zero, Finsupp.optionElim_zero,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

private theorem series_ext {f g : Series}
    (h : ∀ m n, coeff₂ m n f = coeff₂ m n g) : f = g := by
  apply iter.injective
  apply PowerSeries.ext
  intro m
  apply PowerSeries.ext
  intro n
  exact h m n

private def scalar (c : ℂ) : Series := MvPowerSeries.C c
private def inA (f : OneSeries) : Series :=
  iter.symm (PowerSeries.map PowerSeries.C f)
private def inB (f : OneSeries) : Series := iter.symm (PowerSeries.C f)

def a : Series := MvPowerSeries.X none
def b : Series := MvPowerSeries.X (some ())

@[simp] private theorem iter_a : iter a = PowerSeries.X := by
  exact MvPowerSeries.optionEquivLeft_X_none
@[simp] private theorem iter_b : iter b = PowerSeries.C PowerSeries.X := by
  exact MvPowerSeries.optionEquivLeft_X_some ()
@[simp] private theorem iter_scalar (c : ℂ) :
    iter (scalar c) = PowerSeries.C (PowerSeries.C c) := by
  exact MvPowerSeries.optionEquivLeft_C c
@[simp] private theorem iter_inA (f : OneSeries) :
    iter (inA f) = PowerSeries.map PowerSeries.C f := by simp [inA]
@[simp] private theorem iter_inB (f : OneSeries) :
    iter (inB f) = PowerSeries.C f := by simp [inB]

@[simp] private theorem inA_mul (f g : OneSeries) :
    inA (f * g) = inA f * inA g := by simp [inA, map_mul]
@[simp] private theorem inB_mul (f g : OneSeries) :
    inB (f * g) = inB f * inB g := by simp [inB, map_mul]
@[simp] private theorem inA_one : inA 1 = 1 := by simp [inA]
@[simp] private theorem inB_one : inB 1 = 1 := by simp [inB]

@[simp] private theorem coeff₂_add (m n : ℕ) (f g : Series) :
    coeff₂ m n (f + g) = coeff₂ m n f + coeff₂ m n g := by simp [coeff₂]
@[simp] private theorem coeff₂_sub (m n : ℕ) (f g : Series) :
    coeff₂ m n (f - g) = coeff₂ m n f - coeff₂ m n g := by simp [coeff₂]
@[simp] private theorem coeff₂_zero (m n : ℕ) : coeff₂ m n 0 = 0 := by simp [coeff₂]
@[simp] private theorem coeff₂_one (m n : ℕ) :
    coeff₂ m n 1 = if m = 0 ∧ n = 0 then 1 else 0 := by
  by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [coeff₂, hm, hn]
@[simp] private theorem coeff₂_scalar_mul (m n : ℕ) (c : ℂ) (f : Series) :
    coeff₂ m n (scalar c * f) = c * coeff₂ m n f := by
  simp only [coeff₂, map_mul, iter_scalar, PowerSeries.coeff_C_mul]
@[simp] private theorem coeff₂_a_zero (n : ℕ) (f : Series) :
    coeff₂ 0 n (a * f) = 0 := by simp [coeff₂]
@[simp] private theorem coeff₂_a_succ (m n : ℕ) (f : Series) :
    coeff₂ (m + 1) n (a * f) = coeff₂ m n f := by
  simp only [coeff₂, map_mul, iter_a, PowerSeries.coeff_succ_X_mul]
@[simp] private theorem coeff₂_b_zero (m : ℕ) (f : Series) :
    coeff₂ m 0 (b * f) = 0 := by
  simp only [coeff₂, map_mul, iter_b, PowerSeries.coeff_C_mul]
  exact PowerSeries.coeff_zero_X_mul _
@[simp] private theorem coeff₂_b_succ (m n : ℕ) (f : Series) :
    coeff₂ m (n + 1) (b * f) = coeff₂ m n f := by
  simp only [coeff₂, map_mul, iter_b, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul]

private theorem coeff₂_separated (m n : ℕ) (f g : OneSeries) :
    coeff₂ m n (inA f * inB g) = PowerSeries.coeff m f * PowerSeries.coeff n g := by
  simp only [coeff₂, map_mul, iter_inA, iter_inB, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_map, PowerSeries.coeff_C_mul]

/-- The formal root with constant coefficient one, from the native binomial series. -/
def root : OneSeries := PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)
def inverseRoot : OneSeries := PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ)

private theorem root_square : root * root = 1 + PowerSeries.X := by
  rw [root, ← PowerSeries.binomialSeries_add,
    show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num]
  simpa using (PowerSeries.binomialSeries_nat (R := ℂ) (A := ℂ) 1)

private theorem root_inverseRoot : root * inverseRoot = 1 := by
  rw [root, inverseRoot, ← PowerSeries.binomialSeries_add,
    show (1 / 2 : ℂ) + -1 / 2 = 0 by norm_num,
    PowerSeries.binomialSeries_zero]

private theorem inverseRoot_coeff (n : ℕ) :
    PowerSeries.coeff n inverseRoot = halfBinomial n := by
  simp [inverseRoot, PowerSeries.binomialSeries_coeff, halfBinomial_choose]

def rootA : Series := inA root
def rootB : Series := inB root
private def invRootA : Series := inA inverseRoot
private def invRootB : Series := inB inverseRoot

private theorem rootA_square : rootA ^ 2 = 1 + a := by
  apply iter.injective
  simp only [map_pow, rootA, iter_inA, iter_a, map_add, map_one]
  rw [pow_two, ← map_mul, root_square]
  simp
private theorem rootB_square : rootB ^ 2 = 1 + b := by
  apply iter.injective
  simp only [map_pow, rootB, iter_inB, iter_b, map_add, map_one]
  rw [pow_two, ← map_mul, root_square]
  simp
private theorem rootA_inv : rootA * invRootA = 1 := by
  rw [rootA, invRootA, ← inA_mul, root_inverseRoot, inA_one]
private theorem rootB_inv : rootB * invRootB = 1 := by
  rw [rootB, invRootB, ← inB_mul, root_inverseRoot, inB_one]

private def sumInverse : Series := (rootA + rootB)⁻¹
private theorem sum_inverse : (rootA + rootB) * sumInverse = 1 := by
  apply MvPowerSeries.mul_inv_cancel
  rw [map_add, ← coeff₂_constant rootA, ← coeff₂_constant rootB]
  norm_num [coeff₂, rootA, rootB, root, PowerSeries.coeff_map,
    PowerSeries.binomialSeries_coeff]

/-- Independent elementary definition: 1 / (2 sqrt(1+a) sqrt(1+b)
    (sqrt(1+a)+sqrt(1+b))^2). -/
def kernel : Series :=
  scalar (1 / 2) * invRootA * invRootB * sumInverse ^ 2

private def regularNumerator : Series :=
  let p := invRootA * invRootB
  p + scalar (1 / 2) * (a * p) + scalar (1 / 2) * (b * p) - 1

private theorem kernel_cleared : (a - b) ^ 2 * kernel = regularNumerator := by
  have hab : a - b = (rootA - rootB) * (rootA + rootB) := by
    have ha := rootA_square
    have hb := rootB_square
    linear_combination -ha + hb
  have hc : (2 : Series) * scalar (1 / 2) = 1 := by
    simpa only [scalar, map_mul, map_ofNat, map_one] using
      congrArg (MvPowerSeries.C (σ := Option Unit))
        (by norm_num : (2 : ℂ) * (1 / 2) = 1)
  have hp : rootA * rootB * (invRootA * invRootB) = 1 := by
    calc
      _ = (rootA * invRootA) * (rootB * invRootB) := by ring
      _ = 1 := by rw [rootA_inv, rootB_inv]; ring
  calc
    (a - b) ^ 2 * kernel = scalar (1 / 2) * invRootA * invRootB *
        (rootA - rootB) ^ 2 * ((rootA + rootB) * sumInverse) ^ 2 := by
      rw [hab]
      unfold kernel
      ring
    _ = scalar (1 / 2) * (rootA ^ 2 + rootB ^ 2) *
        (invRootA * invRootB) - 1 := by
      rw [sum_inverse]
      linear_combination -(rootA * rootB * (invRootA * invRootB)) * hc - hp
    _ = regularNumerator := by
      rw [rootA_square, rootB_square]
      unfold regularNumerator
      linear_combination (invRootA * invRootB) * hc

/- The comparison series occurs only after the independent kernel construction. -/
private def originalSeries : Series :=
  iter.symm (PowerSeries.mk fun m => PowerSeries.mk fun n => pairScalar (m + 1) (n + 1))

@[simp] private theorem originalSeries_coeff (m n : ℕ) :
    coeff₂ m n originalSeries = pairScalar (m + 1) (n + 1) := by
  simp [coeff₂, originalSeries, PowerSeries.coeff_mk]

private theorem half_zero : halfBinomial 0 = 1 := by simp [halfBinomial]
private theorem half_one : halfBinomial 1 = -1 / 2 := by norm_num [halfBinomial]

/- This is the exact scalar second-difference identity behind clearing the
diagonal. Its denominator is m+n+2, so there is no omitted origin case. -/
private theorem scalar_second_difference (m n : ℕ) :
    pairScalar m (n + 2) - 2 * pairScalar (m + 1) (n + 1) + pairScalar (m + 2) n =
      halfBinomial (m + 1) * halfBinomial (n + 1) +
        halfBinomial m * halfBinomial (n + 1) / 2 +
        halfBinomial (m + 1) * halfBinomial n / 2 := by
  have hm : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hm2 : (m + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  have hn2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  have htotal : ((m : ℂ) + n + 2) ≠ 0 := by
    exact_mod_cast (by omega : m + n + 2 ≠ 0)
  rw [show m + 2 = (m + 1) + 1 by omega,
    show n + 2 = (n + 1) + 1 by omega]
  simp only [pairScalar, half_successor, Nat.cast_add, Nat.cast_one]
  ring_nf at hm hn hm2 hn2 htotal ⊢
  field_simp [hm, hn, hm2, hn2, htotal]
  <;> ring

private theorem scalar_axis (n : ℕ) :
    pairScalar 1 (n + 1) = halfBinomial (n + 2) + halfBinomial (n + 1) / 2 := by
  have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  rw [show n + 2 = (n + 1) + 1 by omega, half_successor]
  simp only [pairScalar, half_one, Nat.cast_one, Nat.cast_add]
  have heq : (1 : ℂ) + (n + 1) = n + 1 + 1 := by ring
  rw [heq]
  have hn' : (n + 1 + 1 : ℂ) ≠ 0 := by convert hn using 1 <;> ring
  field_simp [hn']
  <;> ring

private theorem pairScalar_symm (m n : ℕ) : pairScalar m n = pairScalar n m := by
  unfold pairScalar
  congr 1 <;> ring

private theorem originalSeries_cleared : (a - b) ^ 2 * originalSeries = regularNumerator := by
  have expand : (a - b) ^ 2 * originalSeries =
      a * (a * originalSeries) - scalar 2 * (a * (b * originalSeries)) +
        b * (b * originalSeries) := by
    change (a - b) ^ 2 * originalSeries =
      a * (a * originalSeries) - (2 : Series) * (a * (b * originalSeries)) +
        b * (b * originalSeries)
    ring
  have hp (m n : ℕ) : coeff₂ m n (invRootA * invRootB) =
      halfBinomial m * halfBinomial n := by
    rw [invRootA, invRootB, coeff₂_separated, inverseRoot_coeff, inverseRoot_coeff]
  have haa (m n : ℕ) : coeff₂ (m + 1) n (a * (a * originalSeries)) =
      pairScalar m (n + 1) := by
    rw [coeff₂_a_succ]
    cases m with
    | zero => simp [pairScalar]
    | succ m => simp
  have hbb (m n : ℕ) : coeff₂ m (n + 1) (b * (b * originalSeries)) =
      pairScalar (m + 1) n := by
    rw [coeff₂_b_succ]
    cases n with
    | zero => simp [pairScalar]
    | succ n => simp
  apply series_ext
  intro m n
  rw [expand]
  unfold regularNumerator
  cases m with
  | zero =>
    cases n with
    | zero => simp [hp, half_zero]
    | succ n =>
      cases n with
      | zero => norm_num [hp, half_zero, half_one]
      | succ n =>
        simp only [coeff₂_add, coeff₂_sub, coeff₂_scalar_mul]
        simp only [haa, hbb]
        simp only [coeff₂_a_zero, coeff₂_b_zero, coeff₂_a_succ, coeff₂_b_succ,
          originalSeries_coeff, hp, coeff₂_one]
        simpa [hp, half_zero, Nat.add_assoc, div_eq_mul_inv,
          mul_assoc, mul_left_comm, mul_comm] using scalar_axis n
  | succ m =>
    cases n with
    | zero =>
      cases m with
      | zero => norm_num [hp, half_zero, half_one]
      | succ m =>
        simp only [coeff₂_add, coeff₂_sub, coeff₂_scalar_mul]
        simp only [haa, hbb]
        simp only [coeff₂_a_zero, coeff₂_b_zero, coeff₂_a_succ, coeff₂_b_succ,
          originalSeries_coeff, hp, coeff₂_one]
        simpa [hp, half_zero, pairScalar_symm, Nat.add_assoc, div_eq_mul_inv,
          mul_assoc, mul_left_comm, mul_comm] using scalar_axis m
    | succ n =>
      simp only [coeff₂_add, coeff₂_sub, coeff₂_scalar_mul]
      simp only [haa, hbb]
      simp only [coeff₂_a_zero, coeff₂_b_zero, coeff₂_a_succ, coeff₂_b_succ,
        originalSeries_coeff, hp, coeff₂_one]
      simpa [haa, hbb, hp, Nat.add_assoc, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using scalar_second_difference m n

private theorem a_sub_b_ne_zero : a - b ≠ 0 := by
  intro h
  have hc := congrArg (coeff₂ 1 0) h
  norm_num [coeff₂] at hc

/- proof_shape: kernel_coeff: content
   admission_basis: escape-witness
   escape_witness: An independently defined elementary root/inverse expression
     is identified with the original all-index coefficient series by a
     cleared-diagonal recurrence and nonzero polynomial cancellation. -/
/-- Every coefficient of the actual elementary regular neck kernel is the original Corr scalar. -/
theorem kernel_coeff (m n : ℕ) : coeff₂ m n kernel = pairScalar (m + 1) (n + 1) := by
  have heq : kernel = originalSeries := by
    apply mul_left_cancel₀ (pow_ne_zero 2 a_sub_b_ne_zero)
    exact kernel_cleared.trans originalSeries_cleared.symm
  rw [heq, originalSeries_coeff]

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPairKernel
