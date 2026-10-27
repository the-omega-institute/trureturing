import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError
import Reg.Support.DependentFamily

/-! Full-source family audit attempts for the actual row obstruction and sharpness. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError
open _root_.D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph Finset
open scoped BigOperators
noncomputable section
universe u v

structure LowerParameters where
  V : Type u
  B : Type v
  finiteV : Fintype V
  finiteB : Fintype B
  T : TreeData V
  π : V → B

abbrev lowerSignature : Signature where
  Params := LowerParameters.{u,v}
  State p := KilledGenerator p.B
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev lowerActual : Realization lowerSignature.{u,v} :=
  realize lowerSignature (fun _ p Q =>
    letI := p.finiteV
    letI := p.finiteB
    delta p.T p.π Q) (fun e => nomatch e)

abbrev lowerArena : Arena where
  signature := lowerSignature.{u,v}
  Law R := ∀ p : LowerParameters.{u,v},
    letI := p.finiteV
    letI := p.finiteB
    Function.Surjective p.π → ∀ (Q : KilledGenerator p.B) (η : ℝ),
      0 < η → CycleRates Q η → η ≤ R.readout () p Q

theorem lower_bridge : (type_of% (@cycle_row_error_lower_bound.{u,v})) ↔
    lowerArena.{u,v}.Law lowerActual := by
  constructor
  · intro h p hπ Q η hη hc
    exact @h p.V p.B p.finiteV p.finiteB p.T p.π hπ Q η hη hc
  · intro h V B fv fb T π hπ Q η hη hc
    exact h ⟨V,B,fv,fb,T,π⟩ hπ Q η hη hc

private def oneRate (B : Type*) : KilledGenerator B where
  rate _ _ := 1
  rate_nonneg _ _ _ := zero_le_one
  killing _ := 0
  killing_nonneg _ := le_rfl

private def zeroRate (B : Type*) : KilledGenerator B where
  rate _ _ := 0
  rate_nonneg _ _ _ := le_rfl
  killing _ := 0
  killing_nonneg _ := le_rfl

private def liftedPath : TreeData (ULift.{u} (Fin 4)) where
  graph := (pathGraph 4).comap ULift.down
  tree := (SimpleGraph.Iso.comap Equiv.ulift (pathGraph 4)).isTree_iff.mpr
    (isTree_pathGraph_add_one 3)
  mass _ := 1
  mass_pos _ := zero_lt_one
  conductance _ _ := 1
  conductance_symm _ _ := rfl
  conductance_pos _ _ _ := zero_lt_one
  killing _ := 0
  killing_nonneg _ := le_rfl

private def cycleParameters : LowerParameters.{u,v} where
  V := ULift.{u} (Fin 4)
  B := ULift.{v} (Fin 3)
  finiteV := inferInstance
  finiteB := inferInstance
  T := liftedPath
  π x := ULift.up (endpointFold 3 (by decide) x.down)

private theorem cycleParameters_onto : Function.Surjective cycleParameters.{u,v}.π := by
  intro a
  refine ⟨ULift.up a.down.castSucc, ?_⟩
  cases a
  simp [cycleParameters, endpointFold, Fin.isLt]

private theorem oneRate_cycle : CycleRates (oneRate (ULift.{v} (Fin 3))) 1 := by
  refine ⟨0, ULift.up, ?_, ?_⟩
  · intro a b h
    exact congrArg ULift.down h
  · intro a b _
    exact le_rfl

private def lowerRejected : Realization lowerSignature.{u,v} :=
  realize lowerSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem lower_rejected : ¬ lowerArena.{u,v}.Law lowerRejected := by
  intro h
  have hh := h cycleParameters cycleParameters_onto
    (oneRate (ULift.{v} (Fin 3))) 1 (by norm_num) oneRate_cycle
  change (1 : ℝ) ≤ -1 at hh
  norm_num at hh

private def singletonParameters : LowerParameters.{u,v} where
  V := ULift.{u} PUnit
  B := ULift.{v} Bool
  finiteV := inferInstance
  finiteB := inferInstance
  T := {
    graph := ⊥
    tree := SimpleGraph.IsTree.of_subsingleton
    mass := fun _ => 1
    mass_pos := fun _ => zero_lt_one
    conductance := fun _ _ => 1
    conductance_symm := fun _ _ => rfl
    conductance_pos := fun _ _ _ => zero_lt_one
    killing := fun _ => 0
    killing_nonneg := fun _ => le_rfl }
  π _ := ULift.up false

private theorem lower_dependence : ObservationalDependence lowerSignature.{u,v} lowerActual := by
  classical
  intro i
  letI := singletonParameters.{u,v}.finiteV
  letI := singletonParameters.{u,v}.finiteB
  refine ⟨singletonParameters, zeroRate _, oneRate _, ?_⟩
  change delta singletonParameters.T singletonParameters.π (zeroRate _) ≠
    delta singletonParameters.T singletonParameters.π (oneRate _)
  have hz : delta singletonParameters.T singletonParameters.π (zeroRate _) = 0 := by
    simp [delta, labelRate, singletonParameters, zeroRate]
  rw [hz]
  intro he
  have hh := Finset.le_sup (f := fun p : ULift.{u} PUnit × ULift.{v} Bool =>
    if p.2 ≠ singletonParameters.π p.1 then
      ‖labelRate singletonParameters.T singletonParameters.π p.1 p.2 -
        (oneRate _).rate (singletonParameters.π p.1) p.2‖₊ else 0)
    (Finset.mem_univ (ULift.up PUnit.unit, ULift.up true))
  have hne : (ULift.up true : ULift.{v} Bool) ≠
      singletonParameters.π (ULift.up PUnit.unit) := by
    change ULift.up true ≠ ULift.up false
    decide
  have hrow : labelRate singletonParameters.T singletonParameters.π
      (ULift.up PUnit.unit) (ULift.up true) = 0 := by
    unfold labelRate
    apply Finset.sum_eq_zero
    intro y _
    have hf : ¬ singletonParameters.T.graph.Adj (ULift.up PUnit.unit) y := not_false
    simp only [hf, false_and, ite_false]
  have hentry : (if (ULift.up true : ULift.{v} Bool) ≠
      singletonParameters.π (ULift.up PUnit.unit) then
      ‖labelRate singletonParameters.T singletonParameters.π (ULift.up PUnit.unit)
        (ULift.up true) - (oneRate _).rate (singletonParameters.π (ULift.up PUnit.unit))
          (ULift.up true)‖₊ else 0) = 1 := by
    rw [ite_eq_left hne, hrow]
    norm_num [oneRate]
    apply NNReal.coe_injective
    change ‖(1 : ℝ)‖ = 1
    rw [Real.norm_eq_abs]
    norm_num
  have hc := NNReal.coe_le_coe.mpr hh
  rw [hentry] at hc
  change (1 : ℝ) ≤ delta singletonParameters.T singletonParameters.π (oneRate _) at hc
  rw [← he] at hc
  norm_num at hc

def lowerEvidence : Registration lowerArena.{u,v}
    (type_of% (@cycle_row_error_lower_bound.{u,v})) where
  actual := lowerActual
  bridge := lower_bridge
  variation := ⟨lower_bridge.mp (@cycle_row_error_lower_bound.{u,v}), lowerRejected, lower_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lowerRejected, ?_, rfl, lower_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := lower_dependence

def registration_lower : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cycle_row_error_lower_bound.{u,v}) (Realization lowerSignature.{u,v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError.lowerUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError.lowerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source lowerArena ⟨lowerEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lowerSignature (fun _ p Q =>
    letI := p.finiteV
    letI := p.finiteB
    delta p.T p.π Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError
    definition := none
    coordinates := #[0,1,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

structure SharpParameters where
  k : ℕ
  hk : 3 ≤ k
  η : ℝ
  hη : 0 < η
  a : Fin k

abbrev sharpSignature : Signature where
  Params := SharpParameters
  State p := Fin p.k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev sharpActual : Realization sharpSignature :=
  realize sharpSignature (fun _ p b =>
    (compression (sharpPath p.k p.η p.hη) (endpointFold p.k (lt_of_lt_of_le (by decide : 0 < 3) p.hk))).rate p.a b)
    (fun e => nomatch e)

abbrev sharpArena : Arena where
  signature := sharpSignature
  Law R := ∀ (k : ℕ) (hk : 3 ≤ k) (η : ℝ) (hη : 0 < η),
    let T := sharpPath k η hη
    let π := endpointFold k (by omega)
    let Q := compression T π
    Function.Surjective π ∧
    (∀ a, inducedMass T π a = if a = (⟨0, by omega⟩ : Fin k) then 2 else 1) ∧
    (∀ a b, inducedConductance T π a b = if (cycleGraph k).Adj a b then 2 * η else 0) ∧
    (∀ a b, R.readout () ⟨k,hk,η,hη,a⟩ b = if (cycleGraph k).Adj a b then
      (if a = (⟨0, by omega⟩ : Fin k) then η else 2 * η) else 0) ∧
    (∀ a, Q.killing a = 0) ∧
    CycleRates Q η ∧
    (∃ a b, (cycleGraph k).Adj a b ∧ Q.rate a b = η) ∧
    (∀ x b, |labelRate T π x b - Q.rate (π x) b| ≤ η) ∧
    (∀ a b, a ≠ (⟨0, by omega⟩ : Fin k) → labelRate T π a.castSucc b = Q.rate a b) ∧
    (∀ b, labelRate T π (⟨0, by omega⟩ : Fin (k + 1)) b =
      if b.val = 1 then 2 * η else 0) ∧
    (∀ b, labelRate T π (Fin.last k) b = if b.val + 1 = k then 2 * η else 0) ∧
    (∀ f a, coarseAction Q f a = massAverage T π (generator T (f ∘ π)) a) ∧
    delta T π Q = η

theorem sharp_bridge : (type_of% (@endpoint_folding_sharpness)) ↔
    sharpArena.Law sharpActual := Iff.rfl

private def sharpRejected : Realization sharpSignature :=
  realize sharpSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem sharp_rejected : ¬ sharpArena.Law sharpRejected := by
  intro h
  have hh := (h 3 (by decide) 1 (by norm_num)).2.2.2.1 0 1
  change (0 : ℝ) = if (cycleGraph 3).Adj 0 1 then (if (0 : Fin 3) = 0 then 1 else 2 * 1) else 0 at hh
  norm_num [show (cycleGraph 3).Adj 0 1 by decide] at hh

private theorem sharp_dependence : ObservationalDependence sharpSignature sharpActual := by
  intro i
  refine ⟨⟨3,by decide,1,by norm_num,0⟩,0,1,?_⟩
  have h := (endpoint_folding_sharpness 3 (by decide) 1 (by norm_num)).2.2.2.1
  change (compression (sharpPath 3 1 _) (endpointFold 3 _)).rate 0 0 ≠
    (compression (sharpPath 3 1 _) (endpointFold 3 _)).rate 0 1
  rw [h 0 0, h 0 1]
  norm_num [show ¬ (cycleGraph 3).Adj 0 0 from (cycleGraph 3).irrefl,
    show (cycleGraph 3).Adj 0 1 by decide]

def sharpEvidence : Registration sharpArena (type_of% (@endpoint_folding_sharpness)) where
  actual := sharpActual
  bridge := sharp_bridge
  variation := ⟨sharp_bridge.mp endpoint_folding_sharpness, sharpRejected, sharp_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sharpRejected, ?_, rfl, sharp_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := sharp_dependence

def registration_sharp : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_folding_sharpness) (Realization sharpSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError.sharpUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError.sharpEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨sharpArena⟩
  objectArena := .source ⟨sharpArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source sharpArena ⟨sharpEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sharpSignature (fun _ p b =>
    (compression (sharpPath p.k p.η p.hη) (endpointFold p.k (lt_of_lt_of_le (by decide : 0 < 3) p.hk))).rate p.a b)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError
    definition := none
    coordinates := #[0,2,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body",
        "arg","arg","arg","fn","arg","body","body","fn","arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms lowerEvidence
#print axioms sharpEvidence


abbrev completeArena : Arena where
  signature := lowerSignature.{u,v}
  Law R := lowerArena.Law R ∧ (type_of% (@endpoint_folding_sharpness))

theorem complete_bridge : (type_of% (@cycle_row_error_and_sharpness.{u,v})) ↔
    completeArena.{u,v}.Law lowerActual := by
  constructor
  · intro h
    exact ⟨lower_bridge.mp h.1, h.2⟩
  · intro h
    exact ⟨lower_bridge.mpr h.1, h.2⟩

private theorem complete_rejected : ¬ completeArena.{u,v}.Law lowerRejected :=
  fun h => lower_rejected h.1

def completeEvidence : Registration completeArena.{u,v}
    (type_of% (@cycle_row_error_and_sharpness.{u,v})) where
  actual := lowerActual
  bridge := complete_bridge
  variation := ⟨complete_bridge.mp (@cycle_row_error_and_sharpness.{u,v}),
    lowerRejected, complete_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lowerRejected, ?_, rfl, complete_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := lower_dependence

def registration_complete : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cycle_row_error_and_sharpness.{u,v}) (Realization lowerSignature.{u,v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError.completeUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError.completeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨completeArena⟩
  objectArena := .source ⟨completeArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source completeArena ⟨completeEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lowerSignature (fun _ p Q =>
    letI := p.finiteV
    letI := p.finiteB
    delta p.T p.π Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError
    definition := none
    coordinates := #[0,1,4,5]
    readouts := #[{
      path := #["fn","arg","body","body","body","body","body","body",
        "body","body","body","body","body","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms completeEvidence

end
end Reg.D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError
