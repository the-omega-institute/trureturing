import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/- Audit evidence for the two original Boolean SCM source statements. No new D5
mathematical claim is introduced: the laws reuse their canonical proofs. -/
noncomputable section
namespace Reg.Support.CausalSourceFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner

/-- `false` observes Int; `true` observes CF, on the very same source model. -/
def signature : Signature where
  Params := Unit
  State := fun _ => DeterministicBoolSCM
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun role _ => if role then CFTable else IntTable
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role _ => match role with | false => Int | true => CF)
    (fun e => nomatch e)

def Separation (r : Realization signature) : Prop :=
  ∃ M N : DeterministicBoolSCM,
    r.readout false () M = r.readout false () N ∧
      r.readout true () M ≠ r.readout true () N

/-- Both clauses vary with the supplied readouts; inclusion is not frozen at actual. -/
def Strictness (r : Realization signature) : Prop :=
  (∀ M N : DeterministicBoolSCM,
    r.readout true () M = r.readout true () N →
      r.readout false () M = r.readout false () N) ∧ Separation r

def separationArena : Arena := ⟨signature, Separation⟩
def strictnessArena : Arena := ⟨signature, Strictness⟩

def constantCF : Realization signature :=
  realize signature (fun role _ => match role with
    | false => Int
    | true => fun _ _ _ _ => false) (fun e => nomatch e)

/-- An injective Nat encoding of the complete outcome table fits the original
Int output type, but removes every collision. Only the Int role is replaced. -/
def encodedInt (M : DeterministicBoolSCM) : IntTable :=
  fun _ _ => (Fintype.equivFin (Bool → Bool → Bool) M.outcome).val

def injectiveInt : Realization signature :=
  realize signature (fun role _ => match role with
    | false => encodedInt
    | true => CF) (fun e => nomatch e)

theorem constantCF_not_separation : ¬ Separation constantCF := by
  rintro ⟨M, N, _, h⟩
  exact h rfl

theorem injectiveInt_not_separation : ¬ Separation injectiveInt := by
  rintro ⟨M, N, same, different⟩
  have code := congrFun (congrFun same false) false
  have outcomes : M.outcome = N.outcome :=
    (Fintype.equivFin (Bool → Bool → Bool)).injective (Fin.val_injective code)
  apply different
  change CF M = CF N
  exact congrArg (fun outcome => fun u (_ : Bool) t => outcome u t) outcomes

/-- This pair has equal Int; actual Int dependence therefore uses a different pair below. -/
theorem named_separation :
    Int noEffectModel = Int flipEffectModel ∧ CF noEffectModel ≠ CF flipEffectModel := by
  constructor
  · funext treatment result
    cases treatment <;> cases result <;> rfl
  · intro h
    have impossible := congrFun (congrFun (congrFun h false) false) true
    cases impossible

theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  · refine ⟨(), noEffectModel, ⟨fun _ _ => false⟩, ?_⟩
    intro h
    have impossible := congrFun (congrFun h false) false
    change 1 = 2 at impossible
    omega
  · exact ⟨(), noEffectModel, flipEffectModel, named_separation.2⟩

theorem separation_variation : Variation separationArena actual :=
  ⟨intervention_strictly_weaker_than_counterfactual, constantCF, constantCF_not_separation⟩

theorem separation_sensitivity : Sensitivity separationArena actual := by
  constructor
  · intro role
    cases role
    · refine ⟨injectiveInt, ?_, rfl, injectiveInt_not_separation⟩
      intro other h
      cases other
      · exact (h rfl).elim
      · rfl
    · refine ⟨constantCF, ?_, rfl, constantCF_not_separation⟩
      intro other h
      cases other
      · rfl
      · exact (h rfl).elim
  · intro anchor
    exact nomatch anchor

theorem strictness_variation : Variation strictnessArena actual :=
  ⟨counterfactual_kernel_strictly_finer, constantCF, fun h => constantCF_not_separation h.2⟩

theorem strictness_sensitivity : Sensitivity strictnessArena actual := by
  obtain ⟨roles, anchors⟩ := separation_sensitivity
  constructor
  · intro role
    obtain ⟨bad, fixed, anchored, rejected⟩ := roles role
    exact ⟨bad, fixed, anchored, fun h => rejected h.2⟩
  · intro anchor
    exact nomatch anchor

#print axioms separation_variation
#print axioms separation_sensitivity
#print axioms strictness_variation
#print axioms strictness_sensitivity
#print axioms dependence
end Reg.Support.CausalSourceFamily
