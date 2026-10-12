import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature

open Filter Topology
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenLocalThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- The parameter is the price `λ`; the state is the inverse temperature `β`. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

namespace Summability

def actual : Realization signature :=
  realize signature (fun _ lambda beta => beta * lambda) (fun e => nomatch e)

/-- Shifting the convergence threshold by one. -/
def rejected : Realization signature :=
  realize signature (fun _ lambda beta => beta * lambda + 1) (fun e => nomatch e)

/-- The convergence statement with the threshold `β λ` read out. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lambda beta : ℝ}, 0 < beta →
    (Summable (fun n : ℕ => Real.exp (beta * goldenResourceObjective lambda (n + 1))) ↔
      1 < R.readout () lambda beta)

/-- At `λ = 1/2`, `β = 1` the weights are not summable, yet the shifted threshold holds. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := @h (1 / 2) 1 one_pos
  change _ ↔ (1 : ℝ) < 1 * (1 / 2) + 1 at hbad
  have hgood := @boltzmann_summable_iff (1 / 2) 1 one_pos
  have hcontra := hgood.mp (hbad.mpr (by norm_num))
  norm_num at hcontra

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
  change (0 : ℝ) * 1 ≠ 1 * 1
  norm_num

def registration : Registration arena
    (∀ {lambda beta : ℝ}, 0 < beta →
      (Summable (fun n : ℕ => Real.exp (beta * goldenResourceObjective lambda (n + 1))) ↔
        1 < beta * lambda)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun hbeta => boltzmann_summable_iff hbeta, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- The record binds the threshold `β λ` through its raw source path. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@boltzmann_summable_iff)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ lambda beta => beta * lambda)
      (fun e => nomatch e))) Unit Unit where
  unitName :=
    `D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature.boltzmann_summable_iff.audit
  realizationName :=
    `Reg.D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature.Summability.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ lambda beta => beta * lambda)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Summability

namespace EulerProduct

def actual : Realization signature :=
  realize signature (fun _ lambda beta => boltzmannSum lambda beta) (fun e => nomatch e)

/-- Adding one to the Boltzmann sum. -/
def rejected : Realization signature :=
  realize signature (fun _ lambda beta => boltzmannSum lambda beta + 1) (fun e => nomatch e)

/-- The Euler product statement with the Boltzmann sum read out. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lambda beta : ℝ}, 0 < beta → 1 < beta * lambda →
    R.readout () lambda beta =
      ∏' p : Nat.Primes, ∑' e : ℕ, Real.exp (beta * goldenPrimeLocalObjective lambda p e)

/-- At `λ = 2`, `β = 1` the shifted sum cannot equal the same Euler product. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := @h 2 1 one_pos (by norm_num : (1 : ℝ) < 1 * 2)
  change boltzmannSum 2 1 + 1 = _ at hbad
  have hgood := @boltzmann_sum_euler_product 2 1 one_pos (by norm_num : (1 : ℝ) < 1 * 2)
  rw [← hgood] at hbad
  linarith

/-- Below the convergence threshold the sum is zero; above it the sum is positive. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(2 : ℝ), (1 / 4 : ℝ), (1 : ℝ), ?_⟩
  change boltzmannSum 2 (1 / 4) ≠ boltzmannSum 2 1
  have hzero : boltzmannSum 2 (1 / 4) = 0 := by
    unfold boltzmannSum
    apply tsum_eq_zero_of_not_summable
    rw [boltzmann_summable_iff (by norm_num)]
    norm_num
  have hpos : 0 < boltzmannSum 2 1 := by
    unfold boltzmannSum
    exact Summable.tsum_pos ((boltzmann_summable_iff one_pos).mpr (by norm_num))
      (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  rw [hzero]
  exact hpos.ne

def registration : Registration arena
    (∀ {lambda beta : ℝ}, 0 < beta → 1 < beta * lambda →
      boltzmannSum lambda beta =
        ∏' p : Nat.Primes, ∑' e : ℕ,
          Real.exp (beta * goldenPrimeLocalObjective lambda p e)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun hbeta hconv => boltzmann_sum_euler_product hbeta hconv, rejected,
    rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- The record binds the Boltzmann sum through its raw source path. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@boltzmann_sum_euler_product)
    (type_of% (realize.{0, 0, 0, 0, 0} signature
      (fun _ lambda beta => boltzmannSum lambda beta) (fun e => nomatch e))) Unit Unit where
  unitName :=
    `D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature.boltzmann_sum_euler_product.audit
  realizationName :=
    `Reg.D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature.EulerProduct.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ lambda beta => boltzmannSum lambda beta) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EulerProduct

namespace ZeroTemperature

def actual : Realization signature :=
  realize signature (fun _ lambda beta => Real.log (boltzmannSum lambda beta) / beta)
    (fun e => nomatch e)

/-- Shifting the free energy by one. -/
def rejected : Realization signature :=
  realize signature (fun _ lambda beta => Real.log (boltzmannSum lambda beta) / beta + 1)
    (fun e => nomatch e)

/-- The zero-temperature statement with the free energy `log Z / β` read out. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {lambda : ℝ} (hlambda : 0 < lambda),
    1 ≤ {n : ℕ | 1 ≤ n ∧ goldenResourceObjective lambda n = groundValue hlambda}.ncard ∧
      Tendsto (fun beta => boltzmannSum lambda beta *
          Real.exp (-(beta * groundValue hlambda))) atTop
        (𝓝 ({n : ℕ | 1 ≤ n ∧
          goldenResourceObjective lambda n = groundValue hlambda}.ncard : ℝ)) ∧
      Tendsto (fun beta => R.readout () lambda beta) atTop (𝓝 (groundValue hlambda))

/-- A shifted free energy would converge to the optimum plus one. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (@h 1 one_pos).2.2
  have hgood := (zero_temperature_limit (one_pos : (0 : ℝ) < 1)).2.2
  have hshift : Tendsto (fun beta => Real.log (boltzmannSum 1 beta) / beta + 1) atTop
      (𝓝 (groundValue (one_pos : (0 : ℝ) < 1) + 1)) := hgood.add_const 1
  have heq := tendsto_nhds_unique hbad hshift
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), ?_⟩
  change Real.log (boltzmannSum 1 0) / 0 ≠ Real.log (boltzmannSum 1 2) / 2
  rw [div_zero]
  have hs : Summable (fun n : ℕ => Real.exp (2 * goldenResourceObjective 1 (n + 1))) :=
    (boltzmann_summable_iff (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num)
  have hJ1 : goldenResourceObjective 1 1 = 0 := by simp [goldenResourceObjective]
  have h1 : 1 < boltzmannSum 1 2 := by
    unfold boltzmannSum
    have hsub := Summable.sum_le_tsum (Finset.range 2) (fun n _ => (Real.exp_pos _).le) hs
    rw [Finset.sum_range_succ, Finset.sum_range_one, zero_add, hJ1, mul_zero,
      Real.exp_zero] at hsub
    have := Real.exp_pos (2 * goldenResourceObjective 1 (1 + 1))
    linarith
  have hlog : 0 < Real.log (boltzmannSum 1 2) / 2 := div_pos (Real.log_pos h1) (by norm_num)
  exact hlog.ne

def registration : Registration arena
    (∀ {lambda : ℝ} (hlambda : 0 < lambda),
      1 ≤ {n : ℕ | 1 ≤ n ∧ goldenResourceObjective lambda n = groundValue hlambda}.ncard ∧
        Tendsto (fun beta => boltzmannSum lambda beta *
            Real.exp (-(beta * groundValue hlambda))) atTop
          (𝓝 ({n : ℕ | 1 ≤ n ∧
            goldenResourceObjective lambda n = groundValue hlambda}.ncard : ℝ)) ∧
        Tendsto (fun beta => Real.log (boltzmannSum lambda beta) / beta) atTop
          (𝓝 (groundValue hlambda))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun hlambda => zero_temperature_limit hlambda, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- The record binds the free energy through its raw source path. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@zero_temperature_limit)
    (type_of% (realize.{0, 0, 0, 0, 0} signature
      (fun _ lambda beta => Real.log (boltzmannSum lambda beta) / beta)
      (fun e => nomatch e))) Unit Unit where
  unitName :=
    `D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature.zero_temperature_limit.audit
  realizationName :=
    `Reg.D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature.ZeroTemperature.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ lambda beta => Real.log (boltzmannSum lambda beta) / beta)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "fn", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ZeroTemperature

end

end Reg.D5.S3.Arith.GoldenResource.GoldenResourceZeroTemperature
