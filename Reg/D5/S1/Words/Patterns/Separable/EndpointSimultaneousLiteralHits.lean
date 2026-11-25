import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.EndpointSimultaneousLiteralHits
import Reg.Support.DependentFamily

/-! The actual readout is the probability of hitting every specified offset. -/

namespace Reg.D5.S1.Words.Patterns.Separable.EndpointSimultaneousLiteralHits


open _root_.D5.S1.Words.Patterns.Separable.EndpointSimultaneousLiteralHits
open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.ActualCycleLaw
open _root_.D5.S1.Words.Patterns.Separable.CutFactorization
open _root_.D5.S1.Words.Patterns.Separable.MinimumCutKernel
open _root_.D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
open _root_.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
open _root_.D5.S1.Words.Patterns.Separable.EndpointCycleHazard
open _root_.D5.S1.Words.Patterns.Separable.EndpointHistoryKernel (indecomposableWitness)
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => simultaneousLiteralHitProbability S) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ S : Finset ℤ, Tendsto (R.readout () () S) atTop (𝓝 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h ∅
  change Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 1) at hz
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hz)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), ∅, {1}, ?_⟩
  intro h
  have he := congrFun h 1
  change simultaneousLiteralHitProbability ∅ 1 = simultaneousLiteralHitProbability {1} 1 at he
  classical
  let : Nonempty (Avoider 1) := ⟨identityAvoider 1⟩
  let p := uniformPmf (Avoider 1)
  let U : Set (Avoider 1) := {π | ∀ e ∈ (∅ : Finset ℤ), hitsDiagonal π.val e}
  let V : Set (Avoider 1) := {π | ∀ e ∈ ({1} : Finset ℤ), hitsDiagonal π.val e}
  have hU : p.toOuterMeasure U = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (by simp [U])
  have hV : p.toOuterMeasure V = 0 := (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 <|
    Set.disjoint_left.2 fun π _ hp => by
      have hhit := hp 1 (Finset.mem_singleton_self 1)
      obtain ⟨j, hj⟩ := hhit
      rw [show π.val j = j from Subsingleton.elim _ _, sub_self] at hj
      exact zero_ne_one hj
  change (p.toOuterMeasure U).toReal = (p.toOuterMeasure V).toReal at he
  rw [hU, hV, ENNReal.toReal_one, ENNReal.toReal_zero] at he
  exact one_ne_zero he

def family : Registration arena (type_of% @simultaneous_literal_hits_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨simultaneous_literal_hits_limit, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@simultaneous_literal_hits_limit) (Realization signature) (Type) Unit where
  unitName :=
    `Reg.D5.S1.Words.Patterns.Separable.EndpointSimultaneousLiteralHits.unit
  realizationName :=
    `Reg.D5.S1.Words.Patterns.Separable.EndpointSimultaneousLiteralHits.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => simultaneousLiteralHitProbability S)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.EndpointSimultaneousLiteralHits
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Words.Patterns.Separable.EndpointSimultaneousLiteralHits
