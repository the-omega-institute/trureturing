/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original annular moments and signed infinite sewing equations. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianWeightedResolvent
import D5.S3.VertexAlgebra.TwistedGround.GaussianExternalBlock
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Tactic

/-!
SOURCE ONLY, UNCOMPILED. Authored against the supplied c53a0cec sources and
read-only Mathlib APIs. No kernel verification or integration is claimed.

This module does NOT identify the explicit cubic with the original resolvent.
Its uncompiled proof terms address these pieces of that missing argument:
* the annular moments, using the ORIGINAL halfBinomial, determine the proposed
  scalar from the ORIGINAL analytic period, without an A-period certificate;
* the ORIGINAL infinite signed coefficient equations have a unique solution,
  with self M(1-M²)⁻¹ and NEGATIVE mixed -(1-M²)⁻¹ on the actual lp carrier.
* every finite original mixture of input and detector half-modes supplies an
  actual H row, including external n=0, with the original signs and weights.

The unproved bridge, including all indices, is recorded at the end as a
proposition, NOT a theorem, an axiom, an input field or an assumed certificate.
No theorem below takes that proposition as a hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open OriginalGaussianMatrix OriginalGaussianResolvent

private abbrev F := D5.S3.Analytic.OriginalHalfBinomialPeriod.period

/- The coefficient of x^n in da/w is h_n a^(-n-1) H(a), where
   H(a) = sum h_j a^j. These are honest Laurent series coefficient by
   coefficient in x; no nonexistent uniform lower bound in a is imposed. -/
def halfSeries : PowerSeries ℂ := PowerSeries.mk halfBinomial

def omegaCoefficient (n : ℕ) : LaurentSeries ℂ :=
  HahnSeries.single (-(n : ℤ) - 1) (halfBinomial n) *
    (halfSeries : LaurentSeries ℂ)

private lemma omega_coefficient (n : ℕ) (k : ℤ) :
    (omegaCoefficient n).coeff k =
      halfBinomial n * (halfSeries : LaurentSeries ℂ).coeff (k + n + 1) := by
  rw [omegaCoefficient, HahnSeries.coeff_single_mul]
  congr 2
  omega

/-- The exact annular residue of da/w, at every modulus degree. -/
private lemma omega_residue (n : ℕ) :
    (omegaCoefficient n).coeff (-1) = halfBinomial n ^ 2 := by
  rw [omega_coefficient]
  have he : (-1 : ℤ) + n + 1 = (n : ℤ) := by omega
  rw [he, LaurentSeries.coeff_coe_powerSeries]
  simp [halfSeries, pow_two]

/-- The degree n+1 residue of a da/w, with the original negative h_(n+1). -/
private lemma first_moment_residue (n : ℕ) :
    (omegaCoefficient (n + 1)).coeff (-2) =
      halfBinomial n * halfBinomial (n + 1) := by
  rw [omega_coefficient]
  have he : (-2 : ℤ) + (n + 1 : ℕ) + 1 = (n : ℤ) := by omega
  rw [he, LaurentSeries.coeff_coe_powerSeries]
  simp [halfSeries, mul_comm]

private lemma first_moment_residue_zero :
    (omegaCoefficient 0).coeff (-2) = 0 := by
  simp [omegaCoefficient, HahnSeries.coeff_single_mul,
    PowerSeries.coeff_coe, halfSeries]

private lemma moment_coefficient_recurrence (n : ℕ) :
    halfBinomial n * halfBinomial (n + 1) =
      2 * (n + 1 : ℂ) * halfBinomial (n + 1) ^ 2 -
        (2 * (n : ℂ) + 1) * halfBinomial n ^ 2 := by
  rw [half_successor]
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  field_simp [hn]
  ring

def scalarC (x : ℂ) : ℂ := x / 2 - x * (1 - x) * deriv F x / F x

/- Actual original signed Gaussian, including the identity term of the
mixed block. H is indexed by n : Nat for original positive index n+1. -/
def squareResolvent (z : ℂ) : H →L[ℂ] H := ∑' k : ℕ, (operator z ^ 2) ^ k

def selfOperator (z : ℂ) : H →L[ℂ] H := operator z * squareResolvent z

def mixedOperator (z : ℂ) : H →L[ℂ] H := -squareResolvent z

private lemma square_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    ‖operator z ^ 2‖ < 1 := by
  exact (norm_pow_le _ _).trans_lt
    (pow_lt_one₀ (norm_nonneg _) (OriginalGaussianWeightedResolvent.operator_norm_lt_one hz)
      (by norm_num : (2 : ℕ) ≠ 0))

private lemma square_resolvent_left {z : ℂ} (hz : ‖z‖ < 1) :
    squareResolvent z * (1 - operator z ^ 2) = 1 :=
  (summable_geometric_of_norm_lt_one (square_norm_lt_one hz)).tsum_pow_mul_one_sub

private lemma square_resolvent_right {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - operator z ^ 2) * squareResolvent z = 1 :=
  (summable_geometric_of_norm_lt_one (square_norm_lt_one hz)).one_sub_mul_tsum_pow

private lemma signed_block_equations {z : ℂ} (hz : ‖z‖ < 1) :
    selfOperator z + operator z * mixedOperator z = 0 ∧
      mixedOperator z + operator z * selfOperator z = -1 := by
  constructor
  · dsimp [selfOperator, mixedOperator]
    noncomm_ring
  · calc
      _ = -((1 - operator z ^ 2) * squareResolvent z) := by
        dsimp [selfOperator, mixedOperator]
        noncomm_ring
      _ = -1 := by rw [square_resolvent_right hz]

private lemma solution_equations {z : ℂ} (hz : ‖z‖ < 1) (e f : H) :
    (selfOperator z e + mixedOperator z f) +
        operator z (mixedOperator z e + selfOperator z f) = -f ∧
      (mixedOperator z e + selfOperator z f) +
        operator z (selfOperator z e + mixedOperator z f) = -e := by
  obtain ⟨h0, h1⟩ := signed_block_equations hz
  constructor
  · calc
      _ = (selfOperator z + operator z * mixedOperator z) e +
          (mixedOperator z + operator z * selfOperator z) f := by
            simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, map_add]
            abel
      _ = -f := by rw [h0, h1]; simp
  · calc
      _ = (mixedOperator z + operator z * selfOperator z) e +
          (selfOperator z + operator z * mixedOperator z) f := by
            simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, map_add]
            abel
      _ = -e := by rw [h0, h1]; simp

private lemma sewing_unique {z : ℂ} (hz : ‖z‖ < 1) (e f p q p' q' : H)
    (hp : p + operator z q = -f) (hq : q + operator z p = -e)
    (hp' : p' + operator z q' = -f) (hq' : q' + operator z p' = -e) :
    p = p' ∧ q = q' := by
  have elim (u v : H) (hu : u + operator z v = -f)
      (hv : v + operator z u = -e) :
      ((1 : H →L[ℂ] H) - operator z ^ 2) u = operator z e - f := by
    calc
      _ = (u + operator z v) - operator z (v + operator z u) := by
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
          pow_two, ContinuousLinearMap.mul_apply, map_add]
        abel
      _ = operator z e - f := by rw [hu, hv]; simp; abel
  have hu := congrArg (fun v : H => squareResolvent z v)
    ((elim p q hp hq).trans (elim p' q' hp' hq').symm)
  have hmul := square_resolvent_left hz
  have hpp : p = p' := by
    change (squareResolvent z * ((1 : H →L[ℂ] H) - operator z ^ 2)) p =
      (squareResolvent z * ((1 : H →L[ℂ] H) - operator z ^ 2)) p' at hu
    simpa only [hmul, ContinuousLinearMap.one_apply] using hu
  refine ⟨hpp, ?_⟩
  have hh := hq.trans hq'.symm
  rw [hpp] at hh
  exact add_right_cancel hh

/-- Necessary and sufficient ORIGINAL all-positive-index sewing equations.
No finite cutoff, no scalar/weighted special column, and no Hilbert adjoint.
The source vectors e and f are completely arbitrary elements of the actual H. -/
theorem original_coefficient_equations_iff {z : ℂ} (hz : ‖z‖ < 1) (e f p q : H) :
    ((∀ n : ℕ, p n + (∑' m : ℕ,
        matrixEntry z (n + 1) (m + 1) * q m) = -f n) ∧
      (∀ n : ℕ, q n + (∑' m : ℕ,
        matrixEntry z (n + 1) (m + 1) * p m) = -e n)) ↔
    (p = selfOperator z e + mixedOperator z f ∧
      q = mixedOperator z e + selfOperator z f) := by
  constructor
  · rintro ⟨hp, hq⟩
    have hpH : p + operator z q = -f := by
      ext n
      simpa only [lp.coeFn_add, Pi.add_apply, lp.coeFn_neg, Pi.neg_apply,
        operator_apply hz] using hp n
    have hqH : q + operator z p = -e := by
      ext n
      simpa only [lp.coeFn_add, Pi.add_apply, lp.coeFn_neg, Pi.neg_apply,
        operator_apply hz] using hq n
    obtain ⟨ha, hb⟩ := solution_equations hz e f
    exact sewing_unique hz e f _ _ _ _ hpH hqH ha hb
  · rintro ⟨rfl, rfl⟩
    obtain ⟨ha, hb⟩ := solution_equations hz e f
    constructor
    · intro n
      simpa only [lp.coeFn_add, Pi.add_apply, lp.coeFn_neg, Pi.neg_apply,
        operator_apply hz] using congrArg (fun v : H => v n) ha
    · intro n
      simpa only [lp.coeFn_add, Pi.add_apply, lp.coeFn_neg, Pi.neg_apply,
        operator_apply hz] using congrArg (fun v : H => v n) hb

/- Restore a general finite colour form, with its ORIGINAL bilinear rather
than sesquilinear contraction. No replacement by a unit Gram form occurs. -/
def colourBilinear {I : Type*} [Fintype I] (G : Matrix I I ℂ)
    (v w : I → H) : ℂ :=
  ∑ i, ∑ j, G i j * GaussianExternalBlock.bilinear (v i) (w j)

/- A block contraction target, not a redefinition of original E or a theorem
identifying a geometric covariance with it. The final extraction is open. -/
def resolventBlockContraction {I : Type*} [Fintype I] (G : Matrix I I ℂ)
    (z : ℂ) (e f : I → H) : ℂ :=
  colourBilinear G e (fun i => selfOperator z (e i)) / 2 +
    colourBilinear G f (fun i => selfOperator z (f i)) / 2 +
      colourBilinear G e (fun i => mixedOperator z (f i))

/- Literal finite original half-mode source rows. The external n=0 mode
and BOTH input/detector signs are included. Internal s must be positive. -/
def halfMode (n : ℕ) : ℂ := (n : ℂ) + 1 / 2

/- [a^s] of the original f_T(a), using the binomial expansion of BOTH
T^(-2r_n) alpha_n (1+a)^(-r_n) and T^(2r_n) beta_n (1+a)^(r_n). -/
def originalSourceCoefficient {I : Type*} (T : ℂ) (alpha beta : ℕ →₀ (I → ℂ))
    (s : ℕ) (i : I) : ℂ :=
  (∑ n ∈ alpha.support, Ring.choose (-halfMode n) s *
    (T ^ (2 * n + 1))⁻¹ * alpha n i) +
  ∑ n ∈ beta.support, Ring.choose (halfMode n) s * T ^ (2 * n + 1) * beta n i

def originalJet {I : Type*} (T : ℂ) (alpha beta : ℕ →₀ (I → ℂ))
    (s : ℕ) (i : I) : ℂ :=
  -(s : ℂ) * originalSourceCoefficient T alpha beta s i

private lemma original_jet_formula {I : Type*} (T : ℂ)
    (alpha beta : ℕ →₀ (I → ℂ)) (s : ℕ) (i : I) (hs : 0 < s) :
    originalJet T alpha beta s i =
  (∑ n ∈ alpha.support, halfMode n * Ring.choose (-halfMode n - 1) (s - 1) *
    (T ^ (2 * n + 1))⁻¹ * alpha n i) -
  ∑ n ∈ beta.support, halfMode n * Ring.choose (halfMode n - 1) (s - 1) *
    T ^ (2 * n + 1) * beta n i := by
  have hchoose (r : ℂ) :
      (s : ℂ) * Ring.choose r s = r * Ring.choose (r - 1) (s - 1) := by
    simpa only [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right,
      Nat.cast_one] using (Ring.choose_smul_choose r (n := s) (k := 1) (by omega))
  dsimp only [originalJet, originalSourceCoefficient]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    linear_combination -((T ^ (2 * n + 1))⁻¹ * alpha n i) * hchoose (-halfMode n)
  · apply Finset.sum_congr rfl
    intro n hn
    linear_combination -(T ^ (2 * n + 1) * beta n i) * hchoose (halfMode n)

def originalRowValue {I : Type*} (z T : ℂ) (alpha beta : ℕ →₀ (I → ℂ))
    (i : I) (n : ℕ) : ℂ :=
  z ^ (n + 1) * originalJet T alpha beta (n + 1) i /
    (Real.sqrt (n + 1 : ℝ) : ℂ)

private def binomialRow (r z : ℂ) (n : ℕ) : ℂ :=
  z ^ (n + 1) * Ring.choose r n / (Real.sqrt (n + 1 : ℝ) : ℂ)

private lemma binomial_row_mem (r : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Memℓp (binomialRow r z) 2 := by
  have hzball : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one]
    exact hz
  have hzrad : z ∈ Metric.eball (0 : ℂ) (binomialSeries ℂ r).radius :=
    Metric.eball_subset_eball (binomialSeries_radius_ge_one (a := r)) hzball
  have hs : Summable (fun n : ℕ => ‖Ring.choose r n * z ^ n‖) := by
    simpa [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      (binomialSeries ℂ r).summable_norm_apply hzrad
  have hsrow : Summable (fun n : ℕ => ‖binomialRow r z n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ?_) (hs.mul_left ‖z‖)
    have hden : 1 ≤ ‖(Real.sqrt (n + 1 : ℝ) : ℂ)‖ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using
        (Real.one_le_sqrt.mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ n + 1))
    rw [binomialRow, norm_div]
    calc
      _ ≤ ‖z ^ (n + 1) * Ring.choose r n‖ := div_le_self (norm_nonneg _) hden
      _ = ‖z‖ * ‖Ring.choose r n * z ^ n‖ := by
        rw [pow_succ]
        simp only [norm_mul]
        ring
  have hm : Memℓp (binomialRow r z) 1 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one] using hsrow
  exact hm.of_exponent_ge (by norm_num)

/-- Every finite original mixture of input AND detector half-modes supplies
an actual square-summable row; no finite cutoff on the internal index occurs.
This includes external half-mode n=0 and arbitrary complex coefficients. -/
theorem original_row_mem {I : Type*} {z : ℂ} (hz : ‖z‖ < 1)
    (T : ℂ) (alpha beta : ℕ →₀ (I → ℂ)) (i : I) :
    Memℓp (originalRowValue z T alpha beta i) 2 := by
  classical
  have ha : Memℓp (fun n : ℕ => ∑ k ∈ alpha.support,
      (halfMode k * (T ^ (2 * k + 1))⁻¹ * alpha k i) *
        binomialRow (-halfMode k - 1) z n) 2 := by
    apply Memℓp.finsetSum
    intro k _
    exact (binomial_row_mem (-halfMode k - 1) hz).const_mul _
  have hb : Memℓp (fun n : ℕ => ∑ k ∈ beta.support,
      (halfMode k * T ^ (2 * k + 1) * beta k i) *
        binomialRow (halfMode k - 1) z n) 2 := by
    apply Memℓp.finsetSum
    intro k _
    exact (binomial_row_mem (halfMode k - 1) hz).const_mul _
  convert ha.sub hb using 1
  funext n
  rw [originalRowValue, original_jet_formula T alpha beta (n + 1) i (by omega)]
  simp only [Nat.add_sub_cancel, mul_sub, sub_div,
    Finset.mul_sum, Finset.sum_div, Pi.sub_apply]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;>
    dsimp only [binomialRow] <;> ring

def originalRow {I : Type*} {z : ℂ} (hz : ‖z‖ < 1) (T : ℂ)
    (alpha beta : ℕ →₀ (I → ℂ)) (i : I) : H :=
  ⟨originalRowValue z T alpha beta i, original_row_mem hz T alpha beta i⟩

def originalWick {I : Type*} [Fintype I] (G : Matrix I I ℂ)
    (alpha beta : ℕ →₀ (I → ℂ)) : ℂ :=
  -∑ n ∈ alpha.support ∪ beta.support,
    halfMode n * ∑ i, ∑ j, beta n i * G i j * alpha n j

/- The full finite-source target keeps the original Gram form and both local
Wick constants. Equality to branch extraction of the cubic is NOT asserted. -/
def finiteOriginalBlockTarget {I : Type*} [Fintype I] (G : Matrix I I ℂ)
    {z : ℂ} (hz : ‖z‖ < 1) (T U : ℂ)
    (alpha beta kappa epsilon : ℕ →₀ (I → ℂ)) : ℂ :=
  originalWick G alpha beta + originalWick G kappa epsilon +
    resolventBlockContraction G z (originalRow hz T alpha beta)
      (originalRow hz U kappa epsilon)

/- Independently defined cubic, not a definition by resolvent. The caller
supplies the neck branches of w only for evaluating this scalar expression;
there is no theorem below that assumes these values identify a resolvent. -/
def polar (x a b : ℂ) : ℂ :=
  a * b * (a + b) + 2 * (1 + x) * a * b + x * (a + b)

def cubicKernelValue (x a b wa wb : ℂ) : ℂ :=
  (polar x a b / (2 * (a - b) ^ 2) + scalarC x) / (wa * wb)

/- A second, purely formal presentation makes the missing identity completely
typed. The OUTER PowerSeries variable is x; the INNER LaurentSeries variable
is the original neck a. This order is essential: the a-pole order grows with
the modulus degree. Neither object is defined by an original resolvent. -/
def periodSeries : PowerSeries ℂ := PowerSeries.mk (fun n => halfBinomial n ^ 2)

def momentSeries : PowerSeries ℂ :=
  PowerSeries.mk (fun n => (omegaCoefficient n).coeff (-2))

private lemma formal_moment_identity :
    momentSeries = -PowerSeries.X * periodSeries +
      2 * PowerSeries.X * (1 - PowerSeries.X) * PowerSeries.derivative periodSeries := by
  have hinner : PowerSeries.mk (fun n => (omegaCoefficient (n + 1)).coeff (-2)) =
      -periodSeries + 2 * PowerSeries.derivative periodSeries -
        2 * (PowerSeries.X * PowerSeries.derivative periodSeries) := by
    ext n
    cases n with
    | zero =>
        simp only [PowerSeries.coeff_mk, first_moment_residue, map_sub, map_add,
          map_neg, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_zero_X_mul,
          zero_mul, PowerSeries.coeff_derivative, periodSeries, PowerSeries.coeff_mk]
        norm_num [halfBinomial]
    | succ n =>
        simp only [PowerSeries.coeff_mk, first_moment_residue, map_sub, map_add,
          map_neg, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_derivative, periodSeries, PowerSeries.coeff_mk]
        convert moment_coefficient_recurrence (n + 1) using 1 <;> push_cast <;> ring
  have hshift : momentSeries = PowerSeries.X * PowerSeries.mk
      (fun n => (omegaCoefficient (n + 1)).coeff (-2)) := by
    ext n
    cases n with
    | zero => simp [momentSeries, first_moment_residue_zero]
    | succ n => simp [momentSeries]
  rw [hshift, hinner]
  ring

def scalarCSeries : PowerSeries ℂ :=
  PowerSeries.C (1 / 2) * PowerSeries.X -
    PowerSeries.X * (1 - PowerSeries.X) * PowerSeries.derivative periodSeries *
      periodSeries⁻¹

/-- All-order formal normalization of the independently specified scalar,
using the original Laurent residues. This is a live supplier for the formal
cubic below; it asserts no covariance or resolvent identification. -/
theorem formal_scalar_normalization :
    PowerSeries.C (1 / 2 : ℂ) * momentSeries + scalarCSeries * periodSeries = 0 := by
  have hF : PowerSeries.constantCoeff periodSeries ≠ 0 := by
    simp [periodSeries, halfBinomial]
  have hinv := PowerSeries.inv_mul_cancel periodSeries hF
  rw [scalarCSeries, formal_moment_identity]
  calc
    _ = PowerSeries.X * (1 - PowerSeries.X) * PowerSeries.derivative periodSeries *
        (1 - periodSeries⁻¹ * periodSeries) := by
          have hh : (2 : PowerSeries ℂ) * PowerSeries.C (1 / 2 : ℂ) = 1 := by
            rw [show (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) by rfl,
              ← map_mul]
            norm_num
          linear_combination
            PowerSeries.X * (1 - PowerSeries.X) * PowerSeries.derivative periodSeries * hh
    _ = 0 := by rw [hinv]; ring

abbrev AnnulusSeries := PowerSeries (LaurentSeries ℂ)

private def neckVariable : LaurentSeries ℂ := HahnSeries.single 1 1

private def aSeries : AnnulusSeries := PowerSeries.C neckVariable

private def bSeries (b : ℂ) : AnnulusSeries := PowerSeries.C (HahnSeries.C b)

def formalOmega : AnnulusSeries := PowerSeries.mk omegaCoefficient

def formalExternalOmega (b hb : ℂ) : AnnulusSeries :=
  PowerSeries.mk (fun n => HahnSeries.C (hb * halfBinomial n / b ^ (n + 1)))

private def formalScalarC : AnnulusSeries :=
  PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries

/-- Literal original T,T cubic expansion; hb is the external 1/sqrt(1+b).
The two factors formalOmega and formalExternalOmega are da/w_a and db/w_b.
All inverses here are formal series over the Laurent SERIES FIELD. -/
def cubicTTSeries (b hb : ℂ) : AnnulusSeries :=
  let a := aSeries
  let B := bSeries b
  let x : AnnulusSeries := PowerSeries.X
  formalOmega * formalExternalOmega b hb *
    ((a * B * (a + B) + 2 * (1 + x) * a * B + x * (a + B)) *
      (2 * (a - B) ^ 2)⁻¹ + formalScalarC)

/-- Literal U,T pullback with global a=x/u. The overall MINUS is the factor
da=-x/u² du; after division by w(x/u), da/w=-du/(u sqrt(1+u)sqrt(1+x/u)).
The polynomial numerator is obtained by substituting into the SAME polar. -/
def cubicUTSeries (b hb : ℂ) : AnnulusSeries :=
  let u := aSeries
  let B := bSeries b
  let x : AnnulusSeries := PowerSeries.X;
  -(formalOmega * formalExternalOmega b hb) *
    (x * (u * B * (u + B + 2) + x * (u + B + 2 * u * B)) *
      (2 * (u * B - x) ^ 2)⁻¹ + formalScalarC)

def negativeCoefficient (K : AnnulusSeries) (s d : ℕ) : ℂ :=
  (PowerSeries.coeff d K).coeff (-(s : ℤ) - 1)

def currentRow (b hb : ℂ) (s : ℕ) : ℂ :=
  (s : ℂ) * hb * ∑ k ∈ Finset.range (s + 1),
    Ring.choose (1 / 2 : ℂ) k * b ^ k / b ^ (s + 1)

/-- OPEN statement, not a theorem or a premise of any theorem. Every modulus
degree d, every positive original s, every original kappa_st, both blocks.
The finite bound t<=d-s follows from energy, not an internal-mode cutoff.
It is precisely the formal counterpart of the TWO coefficient equations in
original_coefficient_equations_iff after multiplying by sqrt(s) z^s, x=z². -/
def CubicOriginalCoefficientIdentity : Prop :=
  ∀ b hb : ℂ, b ≠ 0 → (1 + b) * hb ^ 2 = 1 →
    ∀ s d : ℕ, 0 < s →
      (negativeCoefficient (cubicTTSeries b hb) s d =
        if s ≤ d then
          -(∑ t ∈ Finset.Icc 1 (d - s),
            pairScalar s t / (t : ℂ) *
              negativeCoefficient (cubicUTSeries b hb) t (d - s))
        else 0) ∧
      (negativeCoefficient (cubicUTSeries b hb) s d =
        if s ≤ d then
          -(if d = s then currentRow b hb s else 0) -
            ∑ t ∈ Finset.Icc 1 (d - s),
              pairScalar s t / (t : ℂ) *
                negativeCoefficient (cubicTTSeries b hb) t (d - s)
        else 0)

/- FIRST UNPROVED IDENTITY, with its complete internal telescope:

For every 0<|z|<1 sufficiently small, every external T/U neck point Q
outside a chosen sewing circle |z|<rho<1, on |x|<|a|<rho, x=z²,
expand the INDEPENDENT cubicKernelValue with the constant-one neck roots
 w_T(a)=a sqrt(1+a) sqrt(1+x/a), and on U pull back a=x/u,
 da=-x/u² du. For Q on T let p_s and q_s (s>=1) be its negative Laurent
coefficients divided by sqrt(s) z^s, respectively on T and U. Put
 e_(s-1)=z^s l_s(Q)/sqrt(s), f=0, with
 l_s(Q)=s/sqrt(1+Q) sum_(k=0)^s binom(1/2,k) Q^(k-s-1).
Then the two coefficient sequences belong to H and, for EVERY n:Nat,

 p_n + sum_(m>=0) matrixEntry z (n+1) (m+1) q_m = 0,
 q_n + sum_(m>=0) matrixEntry z (n+1) (m+1) p_m = -e_n.

For Q on U interchange e,f and T,U, keeping the same NEGATIVE pullback.
Prove the corresponding all-order formal-in-x statements (all modulus
degrees, not a fixed truncation) and local normal convergence. The native
theorem original_coefficient_equations_iff would then identify the actual
M-blocks, without an assumed correspondence or period certificate.

EXTERNAL CONSUMER still needed: for every finite colour set I, original
Gram matrix G, nonzero T,U, and FOUR arbitrary finitely supported sequences
 alpha,beta,kappa,epsilon : Nat ->₀ (I -> Complex), use original_row_mem
to obtain the actual H rows, and extract the cubic at ALL their
input/detector branch half-mode coefficient functionals. This must give the
ORIGINAL d_T+d_U+E (the block expression finiteOriginalBlockTarget),
with d_T=-sum_n (n+1/2) beta_n^t G alpha_n and the U counterpart,
including same-branch half-current subtraction, diagonal terms, and all
finite mixed derivatives. The equality of that block expression to the
pre-existing original E must also be connected explicitly; a definition
alone proves none of these identifications. No restriction to vacuum or
input-only sources. original_row_mem itself still needs native compilation.

These are open obligations, not hypotheses of a claimed identification.
The full Monster/VOA/CFT/BRST goal remains unfinished.
-/

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel




#print axioms D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel.original_coefficient_equations_iff

#print axioms D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel.original_row_mem

#print axioms D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel.formal_scalar_normalization
