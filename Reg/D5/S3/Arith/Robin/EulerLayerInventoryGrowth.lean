import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.EulerLayerInventoryGrowth
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth

open _root_.D5.S3.Arith.Robin.EulerLayerInventoryGrowth
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Chebyshev

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => Real.log U) (fun e => nomatch e)

def finiteRejected : Realization signature :=
  realize signature (fun _ _ _ => -(|θ 2 - Real.log 2| + 1)) (fun e => nomatch e)

def growthRejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev finiteArena : Arena where
  signature := signature
  Law R := ∀ {t : ℝ}, 2 ≤ t → ∀ {U : ℕ}, 0 < U →
    (∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
    θ t - Real.log t ≤ R.readout () () U ∧
      Real.log U ≤ θ t + ψ (t * Real.log t / Real.log 2) -
        θ (t * Real.log t / Real.log 2)

private theorem finite_rejected : ¬ finiteArena.Law finiteRejected := by
  intro h
  have hp : 0 < 1 / ((2 : ℝ) * Real.log 2) :=
    one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  obtain ⟨U, hU, hstrict, _⟩ := optimal_layer_count_spec hp
  have hh := (h (t := 2) (by norm_num) (U := U) (by omega)
    (fun q _ => hstrict q)).1
  change θ 2 - Real.log 2 ≤ -(|θ 2 - Real.log 2| + 1) at hh
  linarith [neg_abs_le (θ 2 - Real.log 2)]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log (1 : ℕ) ≠ Real.log (2 : ℕ)
  norm_cast
  simp only [Real.log_one, ne_eq]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

def finiteFamily : Registration finiteArena (type_of% @strict_inventory_chebyshev_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strict_inventory_chebyshev_bounds, finiteRejected, finite_rejected⟩
  sensitivity := ⟨fun i => ⟨finiteRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, finite_rejected⟩,
    fun i => nomatch i⟩
  dependence := dependence

abbrev growthArena : Arena where
  signature := signature
  Law R := ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t → ∀ U : ℕ, 0 < U →
    (∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
    |R.readout () () U / t - 1| < ε

private theorem growth_rejected : ¬ growthArena.Law growthRejected := by
  intro h
  obtain ⟨T, _, hT⟩ := h 1 (by norm_num)
  let t := max T 2
  have ht : 1 < t := lt_of_lt_of_le (by norm_num) (le_max_right T 2)
  have hp : 0 < 1 / (t * Real.log t) :=
    one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos ht))
  obtain ⟨U, hU, hstrict, _⟩ := optimal_layer_count_spec hp
  have hh := hT t (le_max_left T 2) U (by omega) (fun q _ => hstrict q)
  change |(0 : ℝ) / t - 1| < 1 at hh
  norm_num at hh

def growthFamily : Registration growthArena (type_of% strict_inventory_uniform_growth) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strict_inventory_uniform_growth, growthRejected, growth_rejected⟩
  sensitivity := ⟨fun i => ⟨growthRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, growth_rejected⟩,
    fun i => nomatch i⟩
  dependence := dependence

def finiteAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_inventory_chebyshev_bounds) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth.strict_inventory_chebyshev_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth.finiteFamily
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def growthAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_inventory_uniform_growth) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth.strict_inventory_uniform_growth.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth.growthFamily
  realizationSource := none
  generated := false
  arena := .source ⟨growthArena⟩
  objectArena := .source ⟨growthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source growthArena ⟨growthFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms finiteFamily
#print axioms growthFamily

end
end Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth
