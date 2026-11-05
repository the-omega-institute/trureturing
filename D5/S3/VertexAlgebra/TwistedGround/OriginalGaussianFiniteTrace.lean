/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite trace differentiation for the original signed Gaussian sections. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianWeightedResolvent
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Analytic identities for the original signed Gaussian operator and its literal cutoffs. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace

open OriginalGaussianMatrix OriginalGaussianResolvent
open OriginalGaussianWeightedResolvent OriginalGaussianDeterminant
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

/- Entrywise differentiation avoids choosing a matrix norm for calculus.
   The noncommutative power differential is retained until AFTER taking trace. -/
private def tracePowerDifferential {n : Type*} [Fintype n] [DecidableEq n]
    (A D : Matrix n n ℂ) (p : ℕ) : Matrix n n ℂ :=
  ∑ j ∈ Finset.range p, A ^ (p - 1 - j) * D * A ^ j

private lemma tracePowerDifferential_succ {n : Type*} [Fintype n] [DecidableEq n]
    (A D : Matrix n n ℂ) (p : ℕ) :
    tracePowerDifferential A D (p + 1) =
      D * A ^ p + A * tracePowerDifferential A D p := by
  classical
  unfold tracePowerDifferential
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hsum :
      (∑ j ∈ Finset.range p, A ^ (p + 1 - 1 - j) * D * A ^ j) =
      ∑ j ∈ Finset.range p, A * (A ^ (p - 1 - j) * D * A ^ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have he : p + 1 - 1 - j = (p - 1 - j) + 1 := by omega
    rw [he, pow_succ']
    simp only [Matrix.mul_assoc]
  rw [hsum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.one_mul]
  exact add_comm _ _

private lemma traceMatrixProduct_hasDerivAt {n : Type*} [Fintype n]
    {A B : ℝ → Matrix n n ℂ} {D E : Matrix n n ℂ} {r : ℝ}
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (D i j) r)
    (hB : ∀ i j, HasDerivAt (fun t => B t i j) (E i j) r) (i j : n) :
    HasDerivAt (fun t => (A t * B t) i j)
      ((D * B r + A r * E) i j) r := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => (hA i k).mul (hB k j))
  simpa only [Pi.mul_apply, Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using hd

private lemma traceMatrixPower_hasDerivAt {n : Type*} [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix n n ℂ} {D : Matrix n n ℂ} {r : ℝ}
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (D i j) r)
    (p : ℕ) (i j : n) :
    HasDerivAt (fun t => (A t ^ p) i j)
      (tracePowerDifferential (A r) D p i j) r := by
  induction p generalizing i j with
  | zero =>
      simpa [tracePowerDifferential] using
        (hasDerivAt_const r ((1 : Matrix n n ℂ) i j))
  | succ p ih =>
      rw [tracePowerDifferential_succ]
      simpa only [pow_succ'] using
        traceMatrixProduct_hasDerivAt hA (fun i j => ih i j) i j

private lemma tracePowerDifferential_trace {n : Type*} [Fintype n] [DecidableEq n]
    (A D : Matrix n n ℂ) (p : ℕ) :
    Matrix.trace (tracePowerDifferential A D p) =
      (p : ℂ) * Matrix.trace (A ^ (p - 1) * D) := by
  classical
  rw [tracePowerDifferential, Matrix.trace_sum]
  have he : ∀ j ∈ Finset.range p,
      Matrix.trace (A ^ (p - 1 - j) * D * A ^ j) =
        Matrix.trace (A ^ (p - 1) * D) := by
    intro j hj
    have hjp : j < p := Finset.mem_range.mp hj
    have hjle : j ≤ p - 1 := by omega
    have he : j + (p - 1 - j) = p - 1 := by omega
    rw [Matrix.trace_mul_cycle, ← pow_add, he]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/- This is the actual finite trace differentiation, including p=0.
   No commutation between A and A' is assumed. -/
private lemma tracePower_hasDerivAt {n : Type*} [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix n n ℂ} {D : Matrix n n ℂ} {r : ℝ}
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (D i j) r) (p : ℕ) :
    HasDerivAt (fun t => Matrix.trace (A t ^ p))
      ((p : ℂ) * Matrix.trace (A r ^ (p - 1) * D)) r := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => traceMatrixPower_hasDerivAt hA p i i)
  change HasDerivAt (fun t => Matrix.trace (A t ^ p))
    (Matrix.trace (tracePowerDifferential (A r) D p)) r at hd
  rw [tracePowerDifferential_trace] at hd
  exact hd

/- Physical index is n+1; signs are exactly those of sourceValue. -/
def traceFiniteWeight (N : ℕ) (r : ℝ) (i : Fin N) : ℂ :=
  (i.val + 1 : ℂ) * sourceValue r i.val

/-- Literal finite bilinear moment, with no conjugation and no modified square. -/
def finiteTraceMoment (N p : ℕ) (r : ℝ) : ℂ :=
  ∑ i : Fin N, ∑ j : Fin N,
    traceFiniteWeight N r i *
      (finiteSection N (Real.sqrt r : ℂ) ^ p) i j * traceFiniteWeight N r j

private lemma trace_rankOne (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (w : Fin N → ℂ) :
    Matrix.trace (A * Matrix.vecMulVec w w) =
      ∑ i : Fin N, ∑ j : Fin N, w i * A i j * w j := by
  classical
  change (∑ i : Fin N, (A * Matrix.vecMulVec w w) i i) = _
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma trace_radial_entry_hasDerivAt {r : ℝ} (hr : 0 < r) (n m : ℕ) :
    HasDerivAt
      (fun t : ℝ => matrixEntry (Real.sqrt t : ℂ) (n + 1) (m + 1))
      ((1 / (2 * (r : ℂ))) *
        (((n + 1 : ℂ) * sourceValue r n) * ((m + 1 : ℂ) * sourceValue r m))) r := by
  let e : ℕ := (n + 1) + (m + 1)
  let z : ℂ := (Real.sqrt r : ℂ)
  let c : ℂ := pairScalar (n + 1) (m + 1) /
    ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * (Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))
  have hz : z ≠ 0 := by
    dsimp [z]
    exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have hz2 : z ^ 2 = (r : ℂ) := by
    dsimp [z]
    exact_mod_cast Real.sq_sqrt hr.le
  have hs := (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
  have hd := (hs.pow e).const_mul c
  have hc : c * ((e : ℂ) * z ^ (e - 1) *
      (((1 / (2 * Real.sqrt r) : ℝ)) : ℂ)) =
      (1 / (2 * (r : ℂ))) * ((e : ℂ) * matrixEntry z (n + 1) (m + 1)) := by
    change c * ((e : ℂ) * z ^ (e - 1) *
      (((1 / (2 * Real.sqrt r) : ℝ)) : ℂ)) =
      (1 / (2 * (r : ℂ))) * ((e : ℂ) * (c * z ^ e))
    have he : e = (e - 1) + 1 := by dsimp [e]; omega
    have hp : z ^ e = z ^ (e - 1) * z := by
      conv_lhs => rw [he]
      rw [pow_succ]
    push_cast
    change c * ((e : ℂ) * z ^ (e - 1) * (1 / (2 * z))) =
      (1 / (2 * (r : ℂ))) * ((e : ℂ) * (c * z ^ e))
    rw [← hz2, hp]
    field_simp [hz]
    <;> ring
  have ha := original_coordinate_anticommutator r n m
  have he : (e : ℂ) = (n + 1 : ℂ) + (m + 1 : ℂ) := by
    dsimp [e]
    push_cast
    rfl
  rw [he, ha] at hc
  convert hd using 1 <;> first | (funext t; rfl) | simpa only [he, z] using hc.symm

private lemma trace_radial_section_hasDerivAt (N : ℕ) {r : ℝ} (hr : 0 < r)
    (i j : Fin N) :
    HasDerivAt (fun t : ℝ => finiteSection N (Real.sqrt t : ℂ) i j)
      (((1 / (2 * (r : ℂ))) •
        Matrix.vecMulVec (traceFiniteWeight N r) (traceFiniteWeight N r)) i j) r := by
  simpa only [finiteSection, traceFiniteWeight, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply] using trace_radial_entry_hasDerivAt hr i.val j.val

private lemma finiteTraceTerm_hasDerivAt (N k : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ =>
      Matrix.trace (finiteSection N (Real.sqrt t : ℂ) ^ (2 * (k + 1))) /
        (k + 1 : ℂ))
      ((1 / (r : ℂ)) * finiteTraceMoment N (2 * k + 1) r) r := by
  have hd := (tracePower_hasDerivAt
    (trace_radial_section_hasDerivAt N hr) (2 * (k + 1))).div_const (k + 1 : ℂ)
  have he : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hk0 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  convert hd using 1
  rw [he, Matrix.mul_smul, Matrix.trace_smul, trace_rankOne]
  push_cast
  change (1 / (r : ℂ)) * finiteTraceMoment N (2 * k + 1) r =
    (2 * (k + 1) : ℂ) * ((1 / (2 * (r : ℂ))) *
      finiteTraceMoment N (2 * k + 1) r) / (k + 1 : ℂ)
  field_simp [hr0, hk0]
  <;> ring

/-- An l1 majorant for the original weighted l2 vector on 0<=r<=R<1. -/
def traceWeightBound (R : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * Real.sqrt R ^ (n + 1)

def traceWeightMass (R : ℝ) : ℝ := ∑' n : ℕ, traceWeightBound R n

private lemma traceWeightBound_nonneg (R : ℝ) (n : ℕ) :
    0 ≤ traceWeightBound R n := by unfold traceWeightBound; positivity

theorem traceWeightBound_summable {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    Summable (traceWeightBound R) := by
  have hs : ‖Real.sqrt R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_lt hR zero_le_one).mpr (by simpa using hR1)
  have ht := summable_pow_mul_geometric_of_norm_lt_one 1 (r := Real.sqrt R) hs
  have hu : Summable (fun n : ℕ => (n : ℝ) * Real.sqrt R ^ n) := by simpa using ht
  change Summable (fun n : ℕ => (n + 1 : ℝ) * Real.sqrt R ^ (n + 1))
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hu

theorem traceWeightValue_bound {R r : ℝ} (hrR : r ≤ R) (n : ℕ) :
    ‖(n + 1 : ℂ) * sourceValue r n‖ ≤ traceWeightBound R n := by
  rw [norm_mul]
  have hn : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  rw [hn]
  exact mul_le_mul_of_nonneg_left
    ((sourceValue_bound r n).trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hrR) _))
    (by positivity)

private lemma trace_finite_power_bound (N p : ℕ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR1 : R < 1) (i j : Fin N) :
    ‖(finiteSection N (Real.sqrt r : ℂ) ^ p) i j‖ ≤ R ^ p := by
  have hz : ‖(Real.sqrt r : ℂ)‖ < 1 := radial_norm_lt_one (hrR.trans_lt hR1)
  have hop : ‖sectionOp N (Real.sqrt r : ℂ)‖ ≤ R := by
    have hs : ‖(Real.sqrt r : ℂ)‖ ^ 2 = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sq_sqrt hr
    exact (sectionOp_norm_le N hz).trans (by simpa only [hs] using hrR)
  rw [← unit1Section_power_coordinate N (Real.sqrt r : ℂ) p j i]
  exact (unit1Power_coordinate_bound _ _ _ _).trans
    (pow_le_pow_left₀ (norm_nonneg _) hop p)

/-- The bound has no dimension factor. It applies to the literal finite power. -/
theorem finiteTraceMoment_bound (N p : ℕ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR1 : R < 1) :
    ‖finiteTraceMoment N p r‖ ≤ traceWeightMass R ^ 2 * R ^ p := by
  classical
  have hR : 0 ≤ R := hr.trans hrR
  have hs := traceWeightBound_summable hR hR1
  let S : ℝ := ∑ i : Fin N, traceWeightBound R i.val
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => traceWeightBound_nonneg _ _)
  have hmass : S ≤ traceWeightMass R := by
    change (∑ i : Fin N, traceWeightBound R i.val) ≤ ∑' n : ℕ, traceWeightBound R n
    rw [← Finset.sum_range]
    exact hs.sum_le_tsum _ (fun n _ => traceWeightBound_nonneg R n)
  calc
    _ ≤ ∑ i : Fin N, ∑ j : Fin N,
        traceWeightBound R i.val * R ^ p * traceWeightBound R j.val := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_mul]
      exact mul_le_mul
        (mul_le_mul (traceWeightValue_bound hrR i.val)
          (trace_finite_power_bound N p hr hrR hR1 i j)
          (norm_nonneg _) (traceWeightBound_nonneg _ _))
        (traceWeightValue_bound hrR j.val) (norm_nonneg _)
        (mul_nonneg (traceWeightBound_nonneg R i.val) (pow_nonneg hR p))
    _ = S ^ 2 * R ^ p := by
      dsimp [S]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    _ ≤ traceWeightMass R ^ 2 * R ^ p := by
      gcongr

private def finiteTraceDerivativeBound (a R : ℝ) (k : ℕ) : ℝ :=
  (traceWeightMass R ^ 2 / a) * R ^ (2 * k + 1)

private lemma finiteTraceDerivativeBound_summable {a R : ℝ}
    (hR : 0 ≤ R) (hR1 : R < 1) : Summable (finiteTraceDerivativeBound a R) := by
  have hR2 : R ^ 2 < 1 := pow_lt_one₀ hR hR1 (by norm_num : (2 : ℕ) ≠ 0)
  convert (summable_geometric_of_lt_one (sq_nonneg R) hR2).mul_left
    (traceWeightMass R ^ 2 / a * R) using 1
  ext k
  dsimp [finiteTraceDerivativeBound]
  rw [pow_add, pow_one, pow_mul]
  ring

private lemma finiteTraceTerm_derivative_bound (N k : ℕ) {a r R : ℝ}
    (ha : 0 < a) (har : a ≤ r) (hrR : r ≤ R) (hR1 : R < 1) :
    ‖(1 / (r : ℂ)) * finiteTraceMoment N (2 * k + 1) r‖ ≤
      finiteTraceDerivativeBound a R k := by
  have hr : 0 < r := ha.trans_le har
  rw [norm_mul, norm_div, norm_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]
  calc
    _ ≤ (1 / a) * (traceWeightMass R ^ 2 * R ^ (2 * k + 1)) :=
      mul_le_mul (one_div_le_one_div_of_le ha har)
        (finiteTraceMoment_bound N _ hr.le hrR hR1) (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [finiteTraceDerivativeBound]; ring

/-- Finite trace-log differentiation, paid by an N-independent derivative M-test.
    The result is still a finite-section moment series, not formula (5.6). -/
theorem finiteLog_hasDerivAt_traceMoments (N : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun t : ℝ => finiteLog N (Real.sqrt t : ℂ))
      (-((1 / (r : ℂ)) * ∑' k : ℕ, finiteTraceMoment N (2 * k + 1) r)) r := by
  let a : ℝ := r / 2
  let R : ℝ := (r + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hm : r ∈ Set.Ioo a R := by dsimp [a, R]; constructor <;> linarith
  have hz : ‖(Real.sqrt r : ℂ)‖ < 1 := radial_norm_lt_one hr1
  have hb : Summable (fun k : ℕ =>
      Matrix.trace (finiteSection N (Real.sqrt r : ℂ) ^ (2 * (k + 1))) /
        (k + 1 : ℂ)) := by
    exact (unit1Majorant_summable (norm_nonneg _) hz).of_norm_bounded
      (fun k => finiteLogTerm_bound (norm_nonneg _) hz le_rfl N k)
  have hd := hasDerivAt_tsum_of_isPreconnected
    (finiteTraceDerivativeBound_summable (a := a) hR hR1)
    isOpen_Ioo (convex_Ioo a R).isPreconnected
    (fun k t ht => finiteTraceTerm_hasDerivAt N k (ha.trans ht.1))
    (fun k t ht => finiteTraceTerm_derivative_bound N k ha ht.1.le ht.2.le hR1)
    hm hb hm
  simpa only [finiteLog, tsum_mul_left] using hd.fun_neg

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace
