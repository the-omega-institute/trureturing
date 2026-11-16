import D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal
noncomputable section
open D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment
open D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder

example {I : Type*} (w a gamma : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1 / 2)
    (hgamma : ∀ i, 0 < gamma i)
    (hbudget : Summable (fun i => w i * (a i)^2 / (gamma i)^2))
    (T : ℝ) (hT : 1 ≤ T) :
    Summable (fun i => w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ∧
    -(∑' i, w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ≤
      integratedDefect w a gamma T -
        2 * (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) ∧
    integratedDefect w a gamma T -
        2 * (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) ≤
      (4 / 9 : ℝ) * (∑' i, w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ∧
    (∑' i, w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ≤
      (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) / (4 * T^2) := by
  exact integrated_defect_poisson_remainder w a gamma hw ha0 ha1 hgamma hbudget T hT

example : integratedDefect (fun _ : Empty => (0 : ℝ)) (fun _ => 0) (fun _ => 1) 1 = 0 := by
  have h := integrated_defect_poisson_remainder
    (fun _ : Empty => (0 : ℝ)) (fun _ => 0) (fun _ => 1)
    (by intro i; exact Empty.elim i) (by intro i; exact Empty.elim i)
    (by intro i; exact Empty.elim i) (by intro i; exact Empty.elim i)
    (by simp) 1 le_rfl
  simp only [tsum_empty, mul_zero, neg_zero, sub_zero] at h
  exact le_antisymm h.2.2.1 h.2.1

example {I : Type*} (a gamma : I → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1 / 2) (hg : ∀ i, 0 < gamma i) :
    integratedDefect (fun _ : I => 0) a gamma 1 = 0 := by
  have h := integrated_defect_poisson_remainder (fun _ : I => 0) a gamma
    (fun _ => le_rfl) ha0 ha1 hg (by simp) 1 le_rfl
  have hl : 0 ≤ integratedDefect (fun _ : I => 0) a gamma 1 := by
    simpa only [zero_mul, zero_div, tsum_zero, mul_zero, neg_zero, sub_zero] using h.2.1
  have hu : integratedDefect (fun _ : I => 0) a gamma 1 ≤ 0 := by
    simpa only [zero_mul, zero_div, tsum_zero, mul_zero, sub_zero] using h.2.2.1
  exact le_antisymm hu hl

example :
    Summable (fun _ : Unit => (2 : ℝ) * (1/2 : ℝ)^4 * (1 : ℝ) / ((1 : ℝ)^2 + (1/1000000 : ℝ)^2)^2) ∧
    -(∑' _ : Unit, (2 : ℝ) * (1/2 : ℝ)^4 * (1 : ℝ) / ((1 : ℝ)^2 + (1/1000000 : ℝ)^2)^2) ≤
      integratedDefect (fun _ : Unit => (2 : ℝ)) (fun _ => 1/2) (fun _ => 1/1000000) 1 -
        2 * (∑' _ : Unit, (2 : ℝ) * (1/2 : ℝ)^2 * (1 : ℝ) / ((1 : ℝ)^2 + (1/1000000 : ℝ)^2)) ∧
    integratedDefect (fun _ : Unit => (2 : ℝ)) (fun _ => 1/2) (fun _ => 1/1000000) 1 -
        2 * (∑' _ : Unit, (2 : ℝ) * (1/2 : ℝ)^2 * (1 : ℝ) / ((1 : ℝ)^2 + (1/1000000 : ℝ)^2)) ≤
      (4 / 9 : ℝ) * (∑' _ : Unit, (2 : ℝ) * (1/2 : ℝ)^4 * (1 : ℝ) / ((1 : ℝ)^2 + (1/1000000 : ℝ)^2)^2) ∧
    (∑' _ : Unit, (2 : ℝ) * (1/2 : ℝ)^4 * (1 : ℝ) / ((1 : ℝ)^2 + (1/1000000 : ℝ)^2)^2) ≤
      (∑' _ : Unit, (2 : ℝ) * (1/2 : ℝ)^2 * (1 : ℝ) / ((1 : ℝ)^2 + (1/1000000 : ℝ)^2)) / (4 * (1 : ℝ)^2) := by
  exact integrated_defect_poisson_remainder (fun _ : Unit => (2 : ℝ))
    (fun _ => 1/2) (fun _ => 1/1000000)
    (by intro i; norm_num) (by intro i; norm_num) (by intro i; norm_num)
    (by intro i; norm_num) Summable.of_finite 1 le_rfl

example (T : ℝ) (hT : 1 ≤ T) :
    Summable (fun n : ℕ => (1 : ℝ) * (1/2)^2 / ((n : ℝ)+1)^2) ∧
    (∑' _ : ℕ, ENNReal.ofReal ((1 : ℝ) * (1/2)^2)) = ⊤ ∧
    Summable (fun i : ℕ => (1 : ℝ) * (1/2 : ℝ)^4 * T / (T^2 + ((i : ℝ)+1)^2)^2) ∧
    -(∑' i : ℕ, (1 : ℝ) * (1/2 : ℝ)^4 * T / (T^2 + ((i : ℝ)+1)^2)^2) ≤
      integratedDefect (fun _ : ℕ => (1 : ℝ)) (fun _ => 1/2) (fun n => (n : ℝ)+1) T -
        2 * (∑' i : ℕ, (1 : ℝ) * (1/2 : ℝ)^2 * T / (T^2 + ((i : ℝ)+1)^2)) ∧
    integratedDefect (fun _ : ℕ => (1 : ℝ)) (fun _ => 1/2) (fun n => (n : ℝ)+1) T -
        2 * (∑' i : ℕ, (1 : ℝ) * (1/2 : ℝ)^2 * T / (T^2 + ((i : ℝ)+1)^2)) ≤
      (4 / 9 : ℝ) * (∑' i : ℕ, (1 : ℝ) * (1/2 : ℝ)^4 * T / (T^2 + ((i : ℝ)+1)^2)^2) ∧
    (∑' i : ℕ, (1 : ℝ) * (1/2 : ℝ)^4 * T / (T^2 + ((i : ℝ)+1)^2)^2) ≤
      (∑' i : ℕ, (1 : ℝ) * (1/2 : ℝ)^2 * T / (T^2 + ((i : ℝ)+1)^2)) / (4 * T^2) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs' : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hs
  have hb : Summable (fun n : ℕ => (1 : ℝ) * (1/2)^2 / ((n : ℝ)+1)^2) := by
    convert hs'.mul_left (1/4 : ℝ) using 1 <;> (try funext n) <;> ring
  have hinf : (∑' _ : ℕ, ENNReal.ofReal ((1 : ℝ) * (1/2)^2)) = ⊤ :=
    ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)
  refine ⟨hb, hinf, ?_⟩
  exact integrated_defect_poisson_remainder (fun _ : ℕ => (1 : ℝ))
    (fun _ => 1/2) (fun n => (n : ℝ)+1)
    (by intro n; norm_num) (by intro n; norm_num) (by intro n; norm_num)
    (by intro n; positivity) hb T hT

set_option pp.all true in
#check @integrated_defect_poisson_remainder
#print axioms integrated_defect_poisson_remainder

run_cmd do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    if n.toString.startsWith "_private.D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder." ||
        n == ``integrated_defect_poisson_remainder then
      let deps := ci.value!.getUsedConstants.toList.map (fun x => Lean.Json.str x.toString)
      Lean.logInfo m!"NATIVE_DEPS {Lean.Json.compress (Lean.Json.mkObj [("name", Lean.Json.str n.toString), ("deps", Lean.Json.arr deps.toArray)])}"
