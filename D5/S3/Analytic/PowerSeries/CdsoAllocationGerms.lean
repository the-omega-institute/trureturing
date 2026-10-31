/- GID: D5/S3/Analytic/PowerSeries/CdsoAllocationGerms
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual analytic allocation germs and their quadratic Taylor cutoff. -/

import D5.S3.Analytic.PowerSeries.RadicalMultiplicity
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Nat.Choose.Cast

/-! Actual real functions and their genuine Taylor series at zero. -/

noncomputable section
open Filter Set Polynomial
open scoped Topology PowerSeries

namespace CdsoPeriodic

/-- The genuine Taylor coefficients of a real function at zero. -/
def taylor (f : ℝ → ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun n => iteratedDeriv n f 0 / n.factorial

private theorem taylor_congr {f g : ℝ → ℝ} (h : f =ᶠ[𝓝 0] g) : taylor f = taylor g := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, h.iteratedDeriv_eq n]

private theorem taylor_add {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    taylor (fun u => f u + g u) = taylor f + taylor g := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, map_add,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, add_div]

private theorem taylor_mul {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    taylor (fun u => f u * g u) = taylor f * taylor g := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_choose ℝ (by simpa using Finset.mem_range.mp hi)]
  field_simp
  <;> ring

private theorem taylor_const (c : ℝ) : taylor (fun _ => c) = PowerSeries.C c := by
  ext n
  cases n with
  | zero => simp [taylor]
  | succ n => simp [taylor, iteratedDeriv_succ]

private theorem taylor_id : taylor (fun u : ℝ => u) = PowerSeries.X := by
  ext n
  simp [taylor, iteratedDeriv_id, PowerSeries.coeff_X]

private theorem taylor_poly (p : ℝ[X]) : taylor p.eval = (p : ℝ⟦X⟧) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, Polynomial.coe_add, hp, hq] using
      taylor_add (AnalyticOnNhd.eval_polynomial p 0 (Set.mem_univ 0))
        (AnalyticOnNhd.eval_polynomial q 0 (Set.mem_univ 0))
  | monomial n c =>
    have hx (k : ℕ) : taylor (fun u : ℝ => u ^ k) = PowerSeries.X ^ k := by
      induction k with
      | zero => simpa using taylor_const 1
      | succ k ih =>
        simpa only [pow_succ, ih, taylor_id] using
          taylor_mul (f := fun u : ℝ => u ^ k) (g := fun u : ℝ => u)
            (by fun_prop) (by fun_prop)
    simpa only [Polynomial.eval_monomial, Polynomial.coe_monomial,
      PowerSeries.monomial_eq_C_mul_X_pow, taylor_const, hx] using
      taylor_mul (f := fun _ : ℝ => c) (g := fun u : ℝ => u ^ n)
        (by fun_prop) (by fun_prop)

private theorem taylor_eq_zero_iff {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    taylor f = 0 ↔ f =ᶠ[𝓝 0] 0 := by
  constructor
  · intro h
    have hp := hf.hasFPowerSeriesAt
    have hs : FormalMultilinearSeries.ofScalars ℝ
        (fun n => iteratedDeriv n f 0 / n.factorial) = 0 := by
      ext n v
      have hc := congrArg (PowerSeries.coeff n) h
      simp only [taylor, PowerSeries.coeff_mk, map_zero] at hc
      simp [FormalMultilinearSeries.ofScalars, hc]
    rw [hs] at hp
    exact hp.eventually_eq_zero
  · intro h
    rw [taylor_congr h, taylor_const]
    simp

private theorem analytic_sqrt {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (h0 : 0 < f 0) :
    AnalyticAt ℝ (fun u => Real.sqrt (f u)) 0 := by
  have hbase : AnalyticAt ℝ (fun y : ℝ => Real.sqrt (1 + y)) 0 := by
    simpa only [Real.sqrt_eq_rpow] using
      (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := (1 : ℝ) / 2)).analyticAt
  have hg : AnalyticAt ℝ (fun u => f u / f 0 - 1) 0 :=
    hf.div_const.sub analyticAt_const
  have hg0 : f 0 / f 0 - 1 = 0 := by simp [ne_of_gt h0]
  have hh := (hbase.comp 0 (hg0 ▸ hg)).const_mul (Real.sqrt (f 0))
  convert hh using 1
  funext u
  rw [← Real.sqrt_mul h0.le]
  congr 1
  field_simp
  <;> ring

/-- Source radical quotient with the positive real square root. -/
def radicalR (b δ k u : ℝ) : ℝ :=
  Real.sqrt ((b + δ * u) ^ 2 + k ^ 2 * u ^ 2) / (b + δ * u) - 1

/-- Rationalized removable extension of the quotient by the square of the parameter. -/
def radicalExtension (b δ k u : ℝ) : ℝ :=
  k ^ 2 / ((b + δ * u) *
    (Real.sqrt ((b + δ * u) ^ 2 + k ^ 2 * u ^ 2) + (b + δ * u)))

private theorem radical_rationalization (b δ k u : ℝ) (hb : 0 < b + δ * u) :
    radicalR b δ k u = u ^ 2 * radicalExtension b δ k u := by
  have hp : 0 ≤ (b + δ * u) ^ 2 + k ^ 2 * u ^ 2 := by positivity
  have hs := Real.sq_sqrt hp
  have hden : Real.sqrt ((b + δ * u) ^ 2 + k ^ 2 * u ^ 2) + (b + δ * u) ≠ 0 := by
    positivity
  unfold radicalR radicalExtension
  field_simp
  <;> nlinarith

private theorem analytic_radicalExtension (b δ k : ℝ) (hb : 0 < b) :
    AnalyticAt ℝ (radicalExtension b δ k) 0 := by
  have hpoly : AnalyticAt ℝ (fun u : ℝ => (b + δ * u) ^ 2 + k ^ 2 * u ^ 2) 0 := by
    fun_prop
  have hpos : 0 < (b + δ * (0 : ℝ)) ^ 2 + k ^ 2 * (0 : ℝ) ^ 2 := by
    simpa using sq_pos_of_pos hb
  apply analyticAt_const.div
    (((by fun_prop : AnalyticAt ℝ (fun u : ℝ => b + δ * u) 0)).mul
      ((analytic_sqrt hpoly hpos).add (by fun_prop)))
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
  positivity


private theorem taylor_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, AnalyticAt ℝ (f i) 0) :
    taylor (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, taylor (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using taylor_const 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [taylor_add (hf i (by simp)) (by
      exact analyticAt_finset_sum _ fun j hj => hf j (by simp [hj])),
      ih (fun j hj => hf j (by simp [hj]))]

private theorem taylor_neg {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    taylor (fun u => -f u) = -taylor f := by
  have h := taylor_mul (f := fun _ : ℝ => -1) (g := f) analyticAt_const hf
  simpa [taylor_const] using h

private theorem taylor_sub {f g : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hg : AnalyticAt ℝ g 0) : taylor (fun u => f u - g u) = taylor f - taylor g := by
  simpa [sub_eq_add_neg, taylor_neg hg] using taylor_add hf hg.neg

/-- A single rational affine weight multiplying a source radical. Real weights include every
rational source weight, including negative and zero weights. -/
structure RadicalTerm where
  base : ℝ
  offset : ℝ
  frequency : ℝ
  weight0 : ℝ
  weight1 : ℝ
  base_pos : 0 < base

namespace RadicalTerm

def affine (q : RadicalTerm) : ℝ[X] := C q.base + C q.offset * X
def weight (q : RadicalTerm) : ℝ[X] := C q.weight0 + C q.weight1 * X
def radicand (q : RadicalTerm) : ℝ[X] := q.affine ^ 2 + C (q.frequency ^ 2) * X ^ 2
def root (q : RadicalTerm) (u : ℝ) : ℝ := Real.sqrt (q.radicand.eval u)

private theorem eval_affine (q : RadicalTerm) (u : ℝ) :
    q.affine.eval u = q.base + q.offset * u := by simp [affine]
private theorem eval_weight (q : RadicalTerm) (u : ℝ) :
    q.weight.eval u = q.weight0 + q.weight1 * u := by simp [weight]
private theorem eval_radicand (q : RadicalTerm) (u : ℝ) :
    q.radicand.eval u = (q.base + q.offset * u)^2 + q.frequency^2*u^2 := by
  simp [radicand, eval_affine]
private theorem affine_degree (q : RadicalTerm) : q.affine.natDegree ≤ 1 := by
  unfold affine
  compute_degree
private theorem weight_degree (q : RadicalTerm) : q.weight.natDegree ≤ 1 := by
  unfold weight
  compute_degree
private theorem radicand_degree (q : RadicalTerm) : q.radicand.natDegree ≤ 2 := by
  unfold radicand
  compute_degree
private theorem root_analytic (q : RadicalTerm) : AnalyticAt ℝ q.root 0 := by
  apply analytic_sqrt (by fun_prop)
  simp only [eval_radicand, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  exact sq_pos_of_pos q.base_pos
private theorem root_sq (q : RadicalTerm) (u : ℝ) : q.root u ^ 2 = q.radicand.eval u := by
  apply Real.sq_sqrt
  rw [eval_radicand]
  positivity
private theorem root_taylor_sq (q : RadicalTerm) :
    taylor q.root ^ 2 = (q.radicand : ℝ⟦X⟧) := by
  rw [pow_two, ← taylor_mul q.root_analytic q.root_analytic,
    taylor_congr (Eventually.of_forall fun u => by simpa [pow_two] using q.root_sq u),
    taylor_poly]
private theorem root_taylor_unit (q : RadicalTerm) :
    PowerSeries.constantCoeff (taylor q.root) ≠ 0 := by
  simpa [taylor, PowerSeries.constantCoeff, root, eval_radicand,
    Real.sqrt_sq_eq_abs, abs_of_pos q.base_pos] using ne_of_gt q.base_pos
end RadicalTerm

private def familyProduct {ι : Type*} [Fintype ι] (q : ι → RadicalTerm) : ℝ[X] :=
  ∏ i, (q i).affine
private def clearedCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → RadicalTerm) : Option ι → ℝ[X]
  | none => -(∑ i, (q i).weight) * familyProduct q
  | some i => (q i).weight * ∏ j ∈ Finset.univ.erase i, (q j).affine
private def clearedRadicand {ι : Type*} (q : ι → RadicalTerm) : Option ι → ℝ[X]
  | none => 1
  | some i => (q i).radicand
private def clearedRoot {ι : Type*} (q : ι → RadicalTerm) : Option ι → ℝ → ℝ
  | none => fun _ => 1
  | some i => (q i).root
private def familyExtension {ι : Type*} [Fintype ι] (q : ι → RadicalTerm) (u : ℝ) : ℝ :=
  2 * ∑ i, (q i).weight.eval u *
    radicalExtension (q i).base (q i).offset (q i).frequency u
private def clearedFunction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → RadicalTerm) (u : ℝ) : ℝ :=
  ∑ i : Option ι, (clearedCoefficient q i).eval u * clearedRoot q i u

private theorem clearedCoefficient_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → RadicalTerm) (i : Option ι) :
    (clearedCoefficient q i).natDegree ≤ Fintype.card (Option ι) := by
  classical
  have hprod : (familyProduct q).natDegree ≤ Fintype.card ι := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => (q j).affine_degree)
  cases i with
  | none =>
    have hsum : (∑ i, (q i).weight).natDegree ≤ 1 :=
      Polynomial.natDegree_sum_le_of_forall_le _ fun i _ => (q i).weight_degree
    have hmul := Polynomial.natDegree_mul_le
      (p := -(∑ i, (q i).weight)) (q := familyProduct q)
    simp only [Polynomial.natDegree_neg] at hmul
    simpa only [clearedCoefficient, Fintype.card_option] using hmul.trans (by omega)
  | some i =>
    have hprod' : (∏ j ∈ Finset.univ.erase i, (q j).affine).natDegree ≤
        (Finset.univ.erase i).card := by
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      simpa using Finset.sum_le_sum (s := Finset.univ.erase i)
        (fun j _ => (q j).affine_degree)
    have hmul := Polynomial.natDegree_mul_le
      (p := (q i).weight) (q := ∏ j ∈ Finset.univ.erase i, (q j).affine)
    have hw := (q i).weight_degree
    have hc : (Finset.univ.erase i).card ≤ Fintype.card ι := Finset.card_le_card (Finset.erase_subset _ _)
    simp only [clearedCoefficient, Fintype.card_option]
    omega

private theorem familyExtension_analytic {ι : Type*} [Fintype ι] (q : ι → RadicalTerm) :
    AnalyticAt ℝ (familyExtension q) 0 := by
  apply AnalyticAt.const_mul
  apply analyticAt_finset_sum
  intro i _
  exact (by fun_prop : AnalyticAt ℝ (q i).weight.eval 0).mul
    (analytic_radicalExtension _ _ _ (q i).base_pos)

private theorem cleared_analytic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → RadicalTerm) : AnalyticAt ℝ (clearedFunction q) 0 := by
  apply analyticAt_finset_sum
  intro i _
  apply AnalyticAt.mul (by fun_prop)
  cases i with
  | none => exact analyticAt_const
  | some i => exact (q i).root_analytic

private theorem cleared_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → RadicalTerm) :
    clearedFunction q =ᶠ[𝓝 0]
      (fun u => (familyProduct q).eval u * (u^2 / 2 * familyExtension q u)) := by
  classical
  have hpos : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ i, 0 < (q i).base + (q i).offset * u := by
    apply Filter.Eventually.all_finite
    intro i
    exact (by fun_prop : ContinuousAt (fun u : ℝ => (q i).base + (q i).offset*u) 0)
      |>.eventually_pos (by simpa using (q i).base_pos)
  filter_upwards [hpos] with u hu
  have hR (i : ι) := radical_rationalization (q i).base (q i).offset (q i).frequency u (hu i)
  have hdiv (i : ι) :
      (familyProduct q).eval u / (q i).affine.eval u =
        (∏ j ∈ Finset.univ.erase i, (q j).affine).eval u := by
    apply (div_eq_iff (ne_of_gt (by simpa [RadicalTerm.eval_affine] using hu i))).2
    simp only [familyProduct, Polynomial.eval_prod]
    exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  simp only [clearedFunction, Fintype.sum_option, clearedCoefficient, clearedRoot,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sum, mul_one,
    familyExtension]
  rw [mul_comm (u^2/2), mul_assoc, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  simp_rw [Finset.mul_sum, ← mul_assoc, ← hR]
  unfold radicalR
  simp_rw [← RadicalTerm.eval_affine, ← RadicalTerm.eval_radicand,
    mul_sub, mul_div_assoc, mul_one, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← sub_eq_add_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← hdiv]
  unfold RadicalTerm.root
  ring
private theorem coeff_mul_zero {f g : ℝ⟦X⟧} {B : ℕ}
    (hg : ∀ k ≤ B, PowerSeries.coeff k g = 0) :
    ∀ k ≤ B, PowerSeries.coeff k (f * g) = 0 := by
  intro k hk
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hij' := Finset.mem_antidiagonal.mp hij
  rw [hg ij.2 (by omega), mul_zero]

private theorem familyExtension_zero_of_coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → RadicalTerm)
    (hcoeff : ∀ k ≤ 3 * (Fintype.card (Option ι))^2,
      PowerSeries.coeff k (taylor (familyExtension q)) = 0) :
    familyExtension q =ᶠ[𝓝 0] 0 := by
  classical
  let A := clearedCoefficient q
  let p := clearedRadicand q
  let S : Option ι → ℝ⟦X⟧ := fun i => taylor (clearedRoot q i)
  have hroot (i : Option ι) : AnalyticAt ℝ (clearedRoot q i) 0 := by
    cases i with
    | none => exact analyticAt_const
    | some i => exact (q i).root_analytic
  have hS0 (i : Option ι) : PowerSeries.constantCoeff (S i) ≠ 0 := by
    cases i with
    | none => simp [S, clearedRoot, taylor_const]
    | some i => exact (q i).root_taylor_unit
  have hsq (i : Option ι) : S i ^ 2 = (p i : ℝ⟦X⟧) := by
    cases i with
    | none => simp [S, p, clearedRoot, clearedRadicand, taylor_const]
    | some i => exact (q i).root_taylor_sq
  have hp (i : Option ι) : (p i).natDegree ≤ 2 := by
    cases i with
    | none => simp [p, clearedRadicand]
    | some i => exact (q i).radicand_degree
  have ht : taylor (clearedFunction q) = ∑ i, (A i : ℝ⟦X⟧) * S i := by
    have h := taylor_sum Finset.univ
      (fun i u => (A i).eval u * clearedRoot q i u)
      (fun i _ => (by fun_prop : AnalyticAt ℝ (A i).eval 0).mul (hroot i))
    simp only [Finset.mem_univ, Finset.sum_const_zero, Finset.sum_const, Finset.sum_attach] at h
    change taylor (clearedFunction q) = _ at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    rw [taylor_mul (by fun_prop) (hroot i), taylor_poly]
  let U : ℝ[X] := C (1/2 : ℝ) * X^2
  have hU : U.eval = fun u : ℝ => u^2/2 := by
    funext u
    simp only [U, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    ring
  have hfactor : taylor (clearedFunction q) =
      (familyProduct q : ℝ⟦X⟧) * ((U : ℝ⟦X⟧) * taylor (familyExtension q)) := by
    rw [taylor_congr (cleared_identity q)]
    rw [taylor_mul (by fun_prop)
      ((by fun_prop : AnalyticAt ℝ U.eval 0).mul (familyExtension_analytic q))]
    rw [← hU, taylor_mul (by fun_prop) (familyExtension_analytic q),
      taylor_poly, taylor_poly]
  have hzero : taylor (clearedFunction q) = 0 := by
    rw [ht]
    apply CdsoRadical.sum_eq_zero_of_coeff_eq_zero S p A hS0 hsq hp
      (clearedCoefficient_degree q)
    rw [← ht, hfactor]
    exact coeff_mul_zero (coeff_mul_zero hcoeff)
  have hprod : (familyProduct q : ℝ⟦X⟧) ≠ 0 := by
    have h0 : PowerSeries.constantCoeff (familyProduct q : ℝ⟦X⟧) ≠ 0 := by
      simpa [familyProduct, Polynomial.coe_prod, Polynomial.coe_mul, RadicalTerm.affine]
        using Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (q i).base_pos)
    exact fun h => h0 (by rw [h, map_zero])
  have hUne : (U : ℝ⟦X⟧) ≠ 0 := by
    simp [U]
  have hz : taylor (familyExtension q) = 0 := by
    rw [hfactor] at hzero
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hprod)).resolve_left hUne
  exact (taylor_eq_zero_iff (familyExtension_analytic q)).mp hz

/-- Source branch, residue remainders, and an integer allocation vector.
The analytic conclusions also apply to vectors outside the allocation inequalities. -/
structure AllocationData (a h : ℕ) where
  j : ℕ
  j_pos : 0 < j
  j_le : j ≤ h
  d : ℕ
  d_lt : d < a + j - 1
  t : ℕ
  t_lt : t < h + 1 - j
  z : Fin (a + j) → ℤ

namespace AllocationData

variable {a h : ℕ}

def m (b : AllocationData a h) : ℕ := a + b.j
def r (b : AllocationData a h) : ℕ := b.m - 1
def n (b : AllocationData a h) : ℕ := h + 1 - b.j
def alpha (b : AllocationData a h) : ℝ := ((a : ℝ) - 1) / b.r
def beta (b : AllocationData a h) : ℝ := (b.j : ℝ) / ((b.r : ℝ) * b.n)
def phi (b : AllocationData a h) : ℝ :=
  -((b.n : ℝ) + ((b.r : ℝ) - 1) * b.d) / b.r
def sigma (b : AllocationData a h) : ℝ := ((b.d : ℝ) - b.n) / b.r
def gamma (b : AllocationData a h) : ℝ := ((b.n : ℝ) - b.d) / ((b.r : ℝ) * b.n)
def vminus (b : AllocationData a h) : ℝ := b.gamma - (b.t : ℝ) / b.n
def vplus (b : AllocationData a h) : ℝ := b.vminus + 1

def zplus (b : AllocationData a h) (i : Fin (a + b.j)) : ℝ := max (b.z i : ℝ) 0
def zminus (b : AllocationData a h) (i : Fin (a + b.j)) : ℝ := max (-(b.z i : ℝ)) 0
def L (b : AllocationData a h) : ℝ := b.n - ∑ i, b.zplus i

def zmin (b : AllocationData a h) : ℤ := by
  letI : Nonempty (Fin (a + b.j)) := ⟨⟨0, by have := b.j_pos; omega⟩⟩
  exact Finset.univ.inf' Finset.univ_nonempty b.z

def delta (b : AllocationData a h) (i : Fin (a + b.j)) : ℝ := b.sigma + b.z i
def delta0 (b : AllocationData a h) : ℝ := b.sigma + b.zmin

/-- The source allocation inequalities. They are not separation hypotheses. -/
def Admissible (b : AllocationData a h) : Prop :=
  (∑ i, b.z i) = (b.n : ℤ) - b.d ∧
    (∑ i, max (b.z i) 0) ≤ b.n ∧ (∑ i, max (-b.z i) 0) ≤ b.d

private theorem alpha_pos (b : AllocationData a h) (ha : 2 ≤ a) : 0 < b.alpha := by
  have hr : 0 < b.r := by unfold r m; have := b.j_pos; omega
  unfold alpha
  positivity

private theorem beta_pos (b : AllocationData a h) (ha : 2 ≤ a) : 0 < b.beta := by
  have hr : 0 < b.r := by unfold r m; have := b.j_pos; omega
  have hn : 0 < b.n := by unfold n; have := b.j_le; omega
  unfold beta
  have := b.j_pos
  positivity

/-- The full bracket in source formula (8.4), parametrized by its radical function. -/
def combination (H : ℝ → ℝ → ℝ → ℝ → ℝ) (b : AllocationData a h) (u : ℝ) : ℝ :=
  (∑ i, ((b.alpha + b.phi * u) * H b.alpha (b.delta i) b.m u +
    u * ((b.d : ℝ) - b.zminus i) * H b.alpha (b.delta i) b.r u +
    u * b.zplus i * H b.alpha (b.delta i) 2 u)) +
  u * b.L * (H b.alpha b.delta0 2 u - H b.alpha b.delta0 b.r u) +
  ((b.n : ℝ) - b.t) * ((b.beta + (b.vminus - 1) * u) * H b.beta b.vminus 1 u +
    u * H b.beta b.vminus 2 u) +
  (b.t : ℝ) * ((b.beta + (b.vplus - 1) * u) * H b.beta b.vplus 1 u +
    u * H b.beta b.vplus 2 u)

/-- The actual positive-parameter function in (8.4). -/
def actual (b : AllocationData a h) (u : ℝ) : ℝ :=
  2 / u ^ 2 * b.combination radicalR u

/-- Its removable analytic extension at zero. -/
def extension (b : AllocationData a h) (u : ℝ) : ℝ :=
  2 * b.combination radicalExtension u

private theorem analytic_extension (b : AllocationData a h) (ha : 2 ≤ a) :
    AnalyticAt ℝ b.extension 0 := by
  have hα := b.alpha_pos ha
  have hβ := b.beta_pos ha
  have hcore (i : Fin (a + b.j)) (k : ℝ) :=
    analytic_radicalExtension b.alpha (b.delta i) k hα
  have hmin (k : ℝ) := analytic_radicalExtension b.alpha b.delta0 k hα
  have hminus (k : ℝ) := analytic_radicalExtension b.beta b.vminus k hβ
  have hplus (k : ℝ) := analytic_radicalExtension b.beta b.vplus k hβ
  unfold extension combination
  fun_prop

end AllocationData

end CdsoPeriodic
