/- GID: D5/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples
   generality: G
   mirror-B: D5/B/S3/Analytic/PrimeProducts/FormalFactorTableCounterexamples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Divergence, zero limits, local nonuniformity, admission, and degenerates are checked. -/
/- Library-search audit trail (2026-08-25):
   * Repository searches for `EulerProduct`, `EulerGerm`, `tprod`, `Multipliable`,
     and `HasProd` found the golden-specific Euler-germ convergence,
     nonvanishing, and analyticity modules. They do not state the generic
     counterexamples below, so no repository theorem is duplicated.
   * Pinned Mathlib searches found `HasProd`, `Multipliable`, the totalized
     fallback `tprod_eq_one_of_not_multipliable`, `tendsto_card_atTop_atTop`,
     `HasProdLocallyUniformlyOn`, and
     `Real.multipliable_one_add_of_summable`. These are reused below.
   * The prime predicate is not used: the negative examples concern arbitrary
     countably infinite products. `PrimeLocalFactorTable` records the intended
     specialization, while `Nat` supplies the smallest concrete index type.
   * Out of scope: differentiability/holomorphy and continuation are not
     covered. Searches for `Differentiable`, `AnalyticOnNhd`, and continuation
     in the repository and pinned Mathlib found APIs only after a parameter
     domain and a function on that domain are specified. A parameter-free
     factor table has neither such a domain nor a larger domain with an
     agreement map, so those two claims require additional source data. -/

import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.PrimeProducts.FormalFactorTableCounterexamples

open Filter Set Topology

noncomputable section

/-- A local-factor table is only an indexed family of real numbers. -/
abbrev LocalFactorTable (ι : Type*) := ι → ℝ

/-- Prime-indexed local factors are the Euler-data specialization. -/
abbrev PrimeLocalFactorTable := LocalFactorTable Nat.Primes

/-- A parameterized table is an indexed family of real-valued functions. -/
abbrev ParameterizedLocalFactorTable (ι X : Type*) := ι → X → ℝ

/-- The constant local-factor table with value `c`. -/
def constantFactorTable {ι : Type*} (c : ℝ) : LocalFactorTable ι := fun _ => c

/-- The parameter family whose every local factor at `x` is `x`. -/
def parameterFactorTable : ParameterizedLocalFactorTable ℕ ℝ := fun _ x => x

/-- The pointwise limit of the powers `x ^ n` on the closed unit interval. -/
def endpointProductLimit (x : ℝ) : ℝ := if x = 1 then 1 else 0

/-- A concrete convergence admission: the deviations from one are absolutely summable. -/
def AbsoluteConvergenceAdmission {ι : Type*} (f : LocalFactorTable ι) : Prop :=
  Summable fun i => |f i - 1|

/-- The completely legal constant table `2` has no unconditional infinite product. -/
theorem constant_two_not_multipliable :
    ¬Multipliable (constantFactorTable (ι := ℕ) 2) := by
  rintro ⟨a, ha⟩
  have ha' : Tendsto (fun s : Finset ℕ => (2 : ℝ) ^ s.card) atTop (𝓝 a) := by
    simpa [HasProd, constantFactorTable] using ha
  have hinfinite : Tendsto (fun s : Finset ℕ => (2 : ℝ) ^ s.card) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp
      (tendsto_card_atTop_atTop (α := ℕ))
  exact not_tendsto_nhds_of_tendsto_atTop hinfinite a ha'
#print axioms constant_two_not_multipliable

/-- The constant table `1 / 2` converges as an infinite product, but its limit is zero. -/
theorem constant_half_hasProd_zero :
    HasProd (constantFactorTable (ι := ℕ) (1 / 2)) 0 := by
  rw [HasProd]
  simpa [constantFactorTable, Function.comp_def] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)).comp
        (tendsto_card_atTop_atTop (α := ℕ))
#print axioms constant_half_hasProd_zero

/-- For `|x| < 1`, or at the endpoint `x = 1`, the parameter family has its stated product. -/
theorem parameter_factor_hasProd_pointwise (x : ℝ) (hx : |x| < 1 ∨ x = 1) :
    HasProd (fun n => parameterFactorTable n x) (endpointProductLimit x) := by
  rcases hx with hcontract | rfl
  · have hxne : x ≠ 1 := by
      intro hx
      subst x
      norm_num at hcontract
    rw [HasProd]
    simpa [parameterFactorTable, endpointProductLimit, hxne, Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hcontract).comp
        (tendsto_card_atTop_atTop (α := ℕ))
  · simp [parameterFactorTable, endpointProductLimit]
#print axioms parameter_factor_hasProd_pointwise

/-- Without the pointwise-domain hypothesis, the claimed product can fail at `x = 2`. -/
theorem pointwise_domain_hypothesis_is_necessary :
    ¬HasProd (fun n => parameterFactorTable n 2) (endpointProductLimit 2) := by
  intro hprod
  apply constant_two_not_multipliable
  refine ⟨endpointProductLimit 2, ?_⟩
  exact hprod.congr (fun _ => rfl)
#print axioms pointwise_domain_hypothesis_is_necessary

/-- The pointwise product above is not locally uniform on the closed unit interval. -/
theorem parameter_factor_not_locally_uniform :
    ¬HasProdLocallyUniformlyOn parameterFactorTable endpointProductLimit (Icc 0 1) := by
  intro hlocal
  have hcontinuous : ContinuousOn endpointProductLimit (Icc (0 : ℝ) 1) := by
    apply hlocal.continuousOn
    exact (Filter.Eventually.of_forall fun s : Finset ℕ => by
      simpa [parameterFactorTable] using (continuous_id.pow s.card).continuousOn).frequently
  have happroach : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 (1 : ℝ)) := by
    have heq : (fun n : ℕ => (n : ℝ) / (n + 1)) =
        fun n : ℕ => 1 - 1 / ((n : ℝ) + 1) := by
      funext n
      field_simp
      ring
    rw [heq]
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmem : ∀ n : ℕ, (n : ℝ) / (n + 1) ∈ Icc (0 : ℝ) 1 := by
    intro n
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 (by norm_num)
  have hwithin :
      Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝[Icc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨happroach, Filter.Eventually.of_forall hmem⟩
  have hlimit :=
    (hcontinuous.continuousWithinAt
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)).tendsto.comp hwithin
  have hnotone (n : ℕ) : (n : ℝ) / (n + 1) ≠ 1 := by
    exact ne_of_lt ((div_lt_one (by positivity)).2 (by norm_num))
  have hzero :
      Tendsto (fun n : ℕ => endpointProductLimit ((n : ℝ) / (n + 1))) atTop (𝓝 0) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1
    ext n
    simp [endpointProductLimit, hnotone n]
  have hone :
      Tendsto (fun n : ℕ => endpointProductLimit ((n : ℝ) / (n + 1))) atTop (𝓝 1) := by
    simpa [endpointProductLimit, Function.comp_def] using hlimit
  have hfalse : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at hfalse
#print axioms parameter_factor_not_locally_uniform

/-- Absolute summability of deviations is an explicit admission that produces a product. -/
theorem absolute_convergence_admission_gives_multipliable {ι : Type*}
    (f : LocalFactorTable ι) (h : AbsoluteConvergenceAdmission f) : Multipliable f := by
  have hnorm : Summable fun i => ‖f i - 1‖ := by
    simpa only [AbsoluteConvergenceAdmission, Real.norm_eq_abs] using h
  have hdeviation : Summable fun i => f i - 1 := hnorm.of_norm
  apply (Real.multipliable_one_add_of_summable hdeviation).congr
  intro i
  ring
#print axioms absolute_convergence_admission_gives_multipliable

/- Degenerate-input audit. These kernel-checked examples show that the empty
   product is one, a singleton product is its factor, constant one has product
   one, a zero factor forces product zero on `Nat`, finite non-one support is
   harmless, and the range product at `n = 0` is one. -/
example : HasProd (constantFactorTable (ι := Empty) 0) 1 := by
  convert hasProd_fintype (constantFactorTable (ι := Empty) 0) using 1
  simp [constantFactorTable]

example : HasProd (constantFactorTable (ι := Fin 1) 2) 2 := by
  simpa [constantFactorTable] using
    (hasProd_fintype (constantFactorTable (ι := Fin 1) 2))

example (ι : Type*) : HasProd (constantFactorTable (ι := ι) 1) 1 := by
  change HasProd (fun _ : ι => (1 : ℝ)) 1
  exact hasProd_one

example : HasProd (constantFactorTable (ι := ℕ) 0) 0 := by
  apply hasProd_zero_of_exists_eq_zero
  exact ⟨0, rfl⟩

example : HasProd (fun n : ℕ => if n = 0 then (2 : ℝ) else 1) 2 := by
  simpa using (hasProd_ite_eq (α := ℝ) 0 2)

example (x : ℝ) : (∏ n ∈ Finset.range 0, parameterFactorTable n x) = 1 := by
  simp

end

end D5.S3.Analytic.PrimeProducts.FormalFactorTableCounterexamples
