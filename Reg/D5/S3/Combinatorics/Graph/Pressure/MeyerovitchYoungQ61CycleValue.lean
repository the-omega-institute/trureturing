import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61CycleValue
import Reg.Support.DependentFamily

/-! The free-endpoint maximin readout as a function of the horizon. -/

open LeanInformationAudit Filter Maths Maths.AdditiveTransport Maths.MaxPlusPotential
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.MeyerovitchYoungQ61Subcritical
open scoped Topology

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61CycleValue

noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c n => maximin c n) (fun e => nomatch e)

def quadratic : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ) ^ 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℝ} (_ : 0 ≤ c) (_ : 2 * c < circumference),
    ∃ x : State c, ∃ cycle : (reachableGraph c).Walk x x, IsSimpleCycle cycle ∧
      let μ := walkWeight (edgeWeight c) cycle / (cycle.length : ℝ)
      (∀ y (p : (reachableGraph c).Walk y y),
        walkWeight (edgeWeight c) p ≤ (p.length : ℝ) * μ) ∧
      Tendsto (fun n : ℕ => r.readout () c n / (n : ℝ)) atTop (𝓝 μ)

private theorem quadratic_fails : ¬ arena.Law quadratic := by
  intro h
  have hW : 2 * (0 : ℝ) < circumference := by simpa using circumference_pos
  obtain ⟨_, _, _, _, hlim⟩ := h (c := 0) le_rfl hW
  have hdiverges : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (n : ℝ)) atTop atTop := by
    apply (tendsto_natCast_atTop_atTop (R := ℝ)).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [pow_two, mul_div_cancel_right₀ _ hn']
  exact not_tendsto_nhds_of_tendsto_atTop hdiverges _ hlim

private theorem actual_depends_on_horizon : ObservationalDependence signature actual := by
  intro _
  refine ⟨0, 0, 1, ?_⟩
  change maximin 0 0 ≠ maximin 0 1
  have hzero : maximin 0 0 = 0 := by
    obtain ⟨w, hw⟩ := (maximin_spec 0 0).1
    obtain ⟨p, hp⟩ := (freeMinimum_spec 0 w).1
    rw [← hw, ← hp]
    simp [walkCost]
  rw [hzero]
  obtain ⟨w, hw⟩ := (maximin_spec 0 1).1
  have hnegative : maximin 0 1 < 0 := by
    rw [← hw]
    cases hb : w 0 with
    | false =>
      refine ((freeMinimum_spec 0 w).2 (fun _ => false)).trans_lt ?_
      norm_num [walkCost, edgePayoff, PrimitivePayoffSwitching.sgn, increment, hb]
    | true =>
      refine ((freeMinimum_spec 0 w).2 (fun _ => true)).trans_lt ?_
      simpa [walkCost, edgePayoff, PrimitivePayoffSwitching.sgn, increment, hb] using
        (div_neg_of_neg_of_pos (neg_neg_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
          (by norm_num : (0 : ℝ) < 2))
  exact hnegative.ne.symm

def cycleValueFamily : Registration arena (type_of% (@maximin_tendsto_cycleMean_subcritical)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@maximin_tendsto_cycleMean_subcritical, quadratic, quadratic_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨quadratic, ?_, rfl, quadratic_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_depends_on_horizon

def cycleValueRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@maximin_tendsto_cycleMean_subcritical) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61CycleValue.cycleValueUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61CycleValue.cycleValueFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨cycleValueFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c n => maximin c n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61CycleValue
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "fn", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.Pressure.MeyerovitchYoungQ61CycleValue
