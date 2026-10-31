/- GID: D5/S3/Analytic/PowerSeries/CdsoAllocationGerms
   generality: G
   mirror-B: D5/B/S3/Analytic/PowerSeries/CdsoAllocationGerms
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

set_option maxHeartbeats 800000

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
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

private theorem taylor_mul {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    taylor (fun u => f u * g u) = taylor f * taylor g := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_choose ℝ (by simpa using Finset.mem_range.mp hi)]
  field_simp
  <;> ring

private theorem taylor_const (c : ℝ) : taylor (fun _ => c) = PowerSeries.C c := by
  ext n
  cases n with
  | zero => simp [taylor]
  | succ n => simp [taylor, iteratedDeriv_const]

private theorem taylor_id : taylor (fun u : ℝ => u) = PowerSeries.X := by
  ext n
  simp only [taylor, PowerSeries.coeff_mk, iteratedDeriv_fun_id_zero, PowerSeries.coeff_X]
  split_ifs with h
  · subst n; norm_num
  · simp

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
    rw [taylor_congr h]
    simpa only [Pi.zero_def, map_zero] using taylor_const 0

private theorem analytic_sqrt {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (h0 : 0 < f 0) :
    AnalyticAt ℝ (fun u => Real.sqrt (f u)) 0 := by
  have hbase : AnalyticAt ℝ (fun y : ℝ => Real.sqrt (1 + y)) 0 := by
    simpa only [Real.sqrt_eq_rpow] using
      (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := (1 : ℝ) / 2)).analyticAt
  have hg : AnalyticAt ℝ (fun u => f u / f 0 - 1) 0 :=
    hf.div_const.sub analyticAt_const
  have hg0 : f 0 / f 0 - 1 = 0 := by simp [ne_of_gt h0]
  have hbase' : AnalyticAt ℝ (fun y : ℝ => Real.sqrt (1+y)) (f 0/f 0-1) := by
    simpa only [hg0] using hbase
  have hh := (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => Real.sqrt (f 0)) 0).mul
    (hbase'.comp (f := fun u => f u / f 0 - 1) hg)
  convert hh using 1
  funext u
  change Real.sqrt (f u) = Real.sqrt (f 0) * Real.sqrt (1+(f u/f 0-1))
  rw [← Real.sqrt_mul h0.le]
  congr 1
  field_simp [ne_of_gt h0]
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
  generalize hy : Real.sqrt ((b+δ*u)^2+k^2*u^2) = y at hs hden ⊢
  field_simp [ne_of_gt hb, hden]
  <;> nlinarith [hs]

private theorem analytic_radicalExtension (b δ k : ℝ) (hb : 0 < b) :
    AnalyticAt ℝ (radicalExtension b δ k) 0 := by
  have hpoly : AnalyticAt ℝ (fun u : ℝ => (b + δ * u) ^ 2 + k ^ 2 * u ^ 2) 0 := by
    fun_prop
  have hpos : 0 < (b + δ * (0 : ℝ)) ^ 2 + k ^ 2 * (0 : ℝ) ^ 2 := by
    simpa using sq_pos_of_pos hb
  apply analyticAt_const.div
    (((by fun_prop : AnalyticAt ℝ (fun u : ℝ => b + δ * u) 0)).mul
      ((analytic_sqrt hpoly hpos).add (by fun_prop)))
  simp only [Pi.mul_apply, Pi.add_apply, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
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
      exact Finset.analyticAt_fun_sum _ fun j hj => hf j (by simp [hj])),
      ih (fun j hj => hf j (by simp [hj]))]

private theorem taylor_neg {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    taylor (fun u => -f u) = -taylor f := by
  have h := taylor_mul (f := fun _ : ℝ => -1) (g := f) analyticAt_const hf
  simpa [taylor_const] using h

private theorem taylor_sub {f g : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hg : AnalyticAt ℝ g 0) : taylor (fun u => f u - g u) = taylor f - taylor g := by
  change taylor (fun u => f u + -g u) = _
  rw [taylor_add (f := f) (g := fun u => -g u) hf hg.neg, taylor_neg hg]
  rfl

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
  have h := q.affine_degree
  unfold radicand
  compute_degree <;> omega
private theorem root_analytic (q : RadicalTerm) : AnalyticAt ℝ q.root 0 := by
  apply analytic_sqrt (AnalyticOnNhd.eval_polynomial q.radicand 0 (Set.mem_univ 0))
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
  simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, taylor, root, eval_radicand,
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
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => (q i).weight_degree
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
  apply (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (2 : ℝ)) 0).mul
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (AnalyticOnNhd.eval_polynomial (q i).weight 0 (Set.mem_univ 0)).mul
    (analytic_radicalExtension _ _ _ (q i).base_pos)

private theorem cleared_analytic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → RadicalTerm) : AnalyticAt ℝ (clearedFunction q) 0 := by
  apply Finset.analyticAt_fun_sum
  intro i _
  apply AnalyticAt.mul (AnalyticOnNhd.eval_polynomial (clearedCoefficient q i) 0 (Set.mem_univ 0))
  cases i with
  | none => exact analyticAt_const
  | some i => exact (q i).root_analytic

private theorem cleared_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → RadicalTerm) :
    clearedFunction q =ᶠ[𝓝 0]
      (fun u => (familyProduct q).eval u * (u^2 / 2 * familyExtension q u)) := by
  classical
  have hpos : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ i, 0 < (q i).base + (q i).offset * u := by
    apply Filter.eventually_all.mpr
    intro i
    exact (by fun_prop : ContinuousAt (fun u : ℝ => (q i).base + (q i).offset*u) 0)
      |>.eventually (Ioi_mem_nhds (by simpa using (q i).base_pos))
  filter_upwards [hpos] with u hu
  have hR (i : ι) := radical_rationalization (q i).base (q i).offset (q i).frequency u (hu i)
  have hdiv (i : ι) :
      (familyProduct q).eval u / (q i).affine.eval u =
        (∏ j ∈ Finset.univ.erase i, (q j).affine).eval u := by
    apply (div_eq_iff (ne_of_gt (by simpa [RadicalTerm.eval_affine] using hu i))).2
    simp only [familyProduct, Polynomial.eval_prod]
    exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  have hF : u^2/2 * familyExtension q u =
      ∑ i, (q i).weight.eval u * radicalR (q i).base (q i).offset (q i).frequency u := by
    simp only [familyExtension, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hR i]
    ring
  rw [hF]
  simp only [clearedFunction, Fintype.sum_option, clearedCoefficient, clearedRoot,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sum, mul_one]
  rw [Finset.mul_sum]
  have hterm (i : ι) :
      (familyProduct q).eval u * ((q i).weight.eval u *
        radicalR (q i).base (q i).offset (q i).frequency u) =
      (q i).weight.eval u * (∏ j ∈ Finset.univ.erase i, (q j).affine).eval u *
        (q i).root u - (q i).weight.eval u * (familyProduct q).eval u := by
    unfold radicalR RadicalTerm.root
    rw [← RadicalTerm.eval_radicand, ← RadicalTerm.eval_affine, ← hdiv]
    ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [Polynomial.eval_finset_sum]
  ring

private theorem coeff_mul_zero {f g : ℝ⟦X⟧} {B : ℕ}
    (hg : ∀ k ≤ B, PowerSeries.coeff k g = 0) :
    ∀ k ≤ B, PowerSeries.coeff k (f * g) = 0 := by
  intro k hk
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
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
      (fun i _ => (AnalyticOnNhd.eval_polynomial (A i) 0 (Set.mem_univ 0)).mul (hroot i))
    change taylor (clearedFunction q) = _ at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    rw [taylor_mul (AnalyticOnNhd.eval_polynomial (A i) 0 (Set.mem_univ 0)) (hroot i), taylor_poly]
  let U : ℝ[X] := C (1/2 : ℝ) * X^2
  have hU : U.eval = fun u : ℝ => u^2/2 := by
    funext u
    simp only [U, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    ring
  have hfactor : taylor (clearedFunction q) =
      (familyProduct q : ℝ⟦X⟧) * ((U : ℝ⟦X⟧) * taylor (familyExtension q)) := by
    rw [taylor_congr (cleared_identity q)]
    have hU' (u : ℝ) : U.eval u = u^2/2 := congrFun hU u
    simp_rw [← hU']
    rw [taylor_mul (f := (familyProduct q).eval) (g := fun u => U.eval u * familyExtension q u)
      (AnalyticOnNhd.eval_polynomial (familyProduct q) 0 (Set.mem_univ 0))
      ((AnalyticOnNhd.eval_polynomial U 0 (Set.mem_univ 0)).mul (familyExtension_analytic q))]
    rw [taylor_mul (f := U.eval) (g := familyExtension q)
      (AnalyticOnNhd.eval_polynomial U 0 (Set.mem_univ 0))
      (familyExtension_analytic q), taylor_poly, taylor_poly]
  have hzero : taylor (clearedFunction q) = 0 := by
    rw [ht]
    apply CdsoRadical.sum_eq_zero_of_coeff_eq_zero S p A hS0 hsq hp
      (clearedCoefficient_degree q)
    rw [← ht, hfactor]
    exact coeff_mul_zero (coeff_mul_zero hcoeff)
  have hprod : (familyProduct q : ℝ⟦X⟧) ≠ 0 := by
    have h0 : PowerSeries.constantCoeff (familyProduct q : ℝ⟦X⟧) ≠ 0 := by
      rw [Polynomial.constantCoeff_coe, ← Polynomial.eval_zero]
      simp only [familyProduct, Polynomial.eval_prod, RadicalTerm.eval_affine, mul_zero, add_zero]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (q i).base_pos)
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
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  unfold alpha
  exact div_pos (by linarith) (by exact_mod_cast hr)

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

private abbrev TermIndex (b : AllocationData a h) :=
  (Fin (a+b.j) × Fin 3) ⊕ (Fin 2 ⊕ ((Fin (b.n-b.t) ⊕ Fin b.t) × Fin 2))

private def term (b : AllocationData a h) (ha : 2 ≤ a) : b.TermIndex → RadicalTerm
  | .inl (i,k) =>
    { base := b.alpha, offset := b.delta i,
      frequency := if k = 0 then b.m else if k = 1 then b.r else 2
      weight0 := if k = 0 then b.alpha else 0
      weight1 := if k = 0 then b.phi else if k = 1 then (b.d : ℝ)-b.zminus i else b.zplus i
      base_pos := b.alpha_pos ha }
  | .inr (.inl k) =>
    { base := b.alpha, offset := b.delta0,
      frequency := if k = 0 then 2 else b.r
      weight0 := 0
      weight1 := if k = 0 then b.L else -b.L
      base_pos := b.alpha_pos ha }
  | .inr (.inr (side,k)) =>
    let v := Sum.elim (fun _ => b.vminus) (fun _ => b.vplus) side
    { base := b.beta, offset := v,
      frequency := if k = 0 then 1 else 2
      weight0 := if k = 0 then b.beta else 0
      weight1 := if k = 0 then v-1 else 1
      base_pos := b.beta_pos ha }

private theorem term_card (b : AllocationData a h) :
    Fintype.card b.TermIndex ≤ 3*(a+1+h)+2 := by
  have ht : b.t ≤ b.n := Nat.le_of_lt b.t_lt
  have hmn : b.m+b.n = a+1+h := by
    unfold m n
    have := b.j_le
    omega
  simp only [TermIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  dsimp only [m] at hmn
  omega

private theorem extension_as_family (b : AllocationData a h) (ha : 2 ≤ a) :
    b.extension = familyExtension (b.term ha) := by
  funext u
  have ht : b.t ≤ b.n := Nat.le_of_lt b.t_lt
  simp only [familyExtension, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, term, RadicalTerm.eval_weight]
  norm_num only [↓reduceIte, Sum.elim_inl, Sum.elim_inr, zero_add, zero_mul, one_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub ht]
  unfold extension combination
  congr 1
  simp_rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  ring_nf

private theorem analytic_extension (b : AllocationData a h) (ha : 2 ≤ a) :
    AnalyticAt ℝ b.extension 0 := by
  rw [b.extension_as_family ha]
  exact familyExtension_analytic _

private theorem actual_extension (b : AllocationData a h) (ha : 2 ≤ a) :
    b.actual =ᶠ[𝓝[>] 0] b.extension := by
  have hpos (δ : ℝ) : ∀ᶠ u in 𝓝 (0:ℝ), 0 < b.alpha + δ*u :=
    (by fun_prop : ContinuousAt (fun u : ℝ => b.alpha + δ*u) 0).eventually
      (Ioi_mem_nhds (by simpa using b.alpha_pos ha))
  have hpos' (δ : ℝ) : ∀ᶠ u in 𝓝 (0:ℝ), 0 < b.beta + δ*u :=
    (by fun_prop : ContinuousAt (fun u : ℝ => b.beta + δ*u) 0).eventually
      (Ioi_mem_nhds (by simpa using b.beta_pos ha))
  have hall : ∀ᶠ u in 𝓝 (0:ℝ), ∀ i : Fin (a+b.j), 0 < b.alpha+b.delta i*u :=
    Filter.eventually_all.mpr fun i => hpos (b.delta i)
  filter_upwards [hall.filter_mono nhdsWithin_le_nhds,
    (hpos b.delta0).filter_mono nhdsWithin_le_nhds,
    (hpos' b.vminus).filter_mono nhdsWithin_le_nhds,
    (hpos' b.vplus).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hi h0 hm hp hu
  have hR (i : Fin (a+b.j)) (k : ℝ) := radical_rationalization b.alpha (b.delta i) k u (hi i)
  have h0R (k : ℝ) := radical_rationalization b.alpha b.delta0 k u h0
  have hmR (k : ℝ) := radical_rationalization b.beta b.vminus k u hm
  have hpR (k : ℝ) := radical_rationalization b.beta b.vplus k u hp
  unfold actual extension combination
  simp_rw [hR, h0R, hmR, hpR]
  have hun : u ≠ 0 := ne_of_gt hu
  field_simp
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  ring

end AllocationData

private def pairTerms {a h : ℕ} (b c : AllocationData a h) (ha : 2 ≤ a) :
    b.TermIndex ⊕ c.TermIndex → RadicalTerm
  | .inl i => b.term ha i
  | .inr i => { c.term ha i with
      weight0 := -(c.term ha i).weight0
      weight1 := -(c.term ha i).weight1 }

private theorem pair_family {a h : ℕ} (b c : AllocationData a h) (ha : 2 ≤ a) :
    familyExtension (pairTerms b c ha) = fun u => b.extension u-c.extension u := by
  rw [b.extension_as_family ha, c.extension_as_family ha]
  funext u
  simp only [familyExtension, Fintype.sum_sum_type, pairTerms, RadicalTerm.eval_weight]
  simp_rw [neg_mul, ← neg_add, neg_mul, Finset.sum_neg_distrib]
  ring

private theorem positive_germ_eq_iff {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    f =ᶠ[𝓝[>] 0] g ↔ f =ᶠ[𝓝 0] g := by
  constructor
  · intro h
    rcases hf.eventually_eq_or_eventually_ne hg with heq | hne
    · exact heq
    · have hle : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (by
        intro x hx
        exact ne_of_gt hx)
      have hfals : ∀ᶠ u in 𝓝[>] (0:ℝ), False :=
        (h.and (hne.filter_mono hle)).mono fun u hu => hu.2 hu.1
      exact False.elim (Filter.Eventually.exists hfals |>.choose_spec)
  · exact fun h => h.filter_mono nhdsWithin_le_nhds

/-- For every fixed source branch/residue/allocation data, (8.4) has its rationalized
removable analytic extension, and two actual positive-near-zero functions have the same germ
exactly when their genuine Taylor coefficients from zero through `3*(6*s+5)^2` agree.
Here `s=a+1+h`. The theorem applies to all integer vectors, hence to every source-admissible one. -/
theorem allocation_germ_iff_taylor {a h : ℕ} (ha : 2 ≤ a)
    (b c : AllocationData a h) :
    AnalyticAt ℝ b.extension 0 ∧ AnalyticAt ℝ c.extension 0 ∧
    b.actual =ᶠ[𝓝[>] 0] b.extension ∧ c.actual =ᶠ[𝓝[>] 0] c.extension ∧
    (b.actual =ᶠ[𝓝[>] 0] c.actual ↔
      ∀ k ≤ 3*(6*(a+1+h)+5)^2,
        iteratedDeriv k b.extension 0 / k.factorial =
          iteratedDeriv k c.extension 0 / k.factorial) := by
  classical
  have hb := b.analytic_extension ha
  have hc := c.analytic_extension ha
  have hbe := b.actual_extension ha
  have hce := c.actual_extension ha
  refine ⟨hb, hc, hbe, hce, ?_⟩
  have heq : b.actual =ᶠ[𝓝[>] 0] c.actual ↔ b.extension =ᶠ[𝓝 0] c.extension := by
    rw [← positive_germ_eq_iff hb hc]
    exact ⟨fun h => hbe.symm.trans (h.trans hce), fun h => hbe.trans (h.trans hce.symm)⟩
  rw [heq]
  constructor
  · intro he k hk
    have ht := congrArg (PowerSeries.coeff k) (taylor_congr he)
    simpa [taylor] using ht
  · intro hcoeff
    let q := pairTerms b c ha
    have hsize : Fintype.card (Option (b.TermIndex ⊕ c.TermIndex)) ≤ 6*(a+1+h)+5 := by
      have h1 := b.term_card
      have h2 := c.term_card
      rw [Fintype.card_option, Fintype.card_sum]
      omega
    have hbound : 3 * (Fintype.card (Option (b.TermIndex ⊕ c.TermIndex)))^2 ≤
        3*(6*(a+1+h)+5)^2 := by nlinarith
    have hz := familyExtension_zero_of_coeff q (fun k hk => by
      rw [pair_family, taylor_sub hb hc]
      simp only [map_sub, sub_eq_zero, taylor, PowerSeries.coeff_mk]
      exact hcoeff k (hk.trans hbound))
    rw [pair_family] at hz
    exact hz.mono fun u hu => sub_eq_zero.mp hu

end CdsoPeriodic
