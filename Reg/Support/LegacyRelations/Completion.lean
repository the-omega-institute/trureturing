import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange

/- Full original laws transported to a parameterized family. These support proofs
are not registration certificates: source-selection acceptance is tested separately. -/
namespace Reg.Support.LegacyRelations.Completion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange

abbrev signature : Signature where
  Params := Unit
  State _ := FourState
  Role := CompletionReadout
  finiteRole := inferInstance
  nonemptyRole := ⟨.flowF⟩
  Output i _ := completionSignature.Output i
  Anchor := Fin 0
  finiteAnchor := inferInstance

def toLegacy (r : Realization signature) :
    _root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization completionSignature where
  readout i := r.readout i ()
  anchor i := r.anchor i ()

/-- The Unit parameter changes no realization: both directions are inverse. -/
def fromLegacy (r :
    _root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization completionSignature) :
    Realization signature :=
  realize signature (fun i _ => r.readout i) (fun i _ => r.anchor i)

theorem to_from_legacy (r :
    _root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization completionSignature) :
    toLegacy (fromLegacy r) = r := by
  cases r
  rfl

theorem from_to_legacy (r : Realization signature) : fromLegacy (toLegacy r) = r := by
  cases r with
  | mk readout anchor =>
    congr 1 <;> funext i p <;> cases p <;> rfl

def arena : Arena := ⟨signature, fun r => commutingCompletionArena.Law (toLegacy r)⟩

def actual : Realization signature :=
  realize signature (fun i _ => commutingCompletionRealization.readout i)
    (fun i _ => commutingCompletionRealization.anchor i)

theorem full_law_transport (r : Realization signature) :
    arena.Law r ↔ commutingCompletionArena.Law (toLegacy r) := Iff.rfl

theorem bridge : CommutativityNecessaryStatement ↔ arena.Law actual :=
  commutativity_hypothesis_is_necessary_realization.equivalence

open _root_.D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient

def without_flowF : Realization signature where
  readout i _ := match i with
    | .flowF => id
    | .flowG => commutingCompletionRealization.readout .flowG
    | .cut => commutingCompletionRealization.readout .cut
  anchor := actual.anchor

def without_flowG : Realization signature where
  readout i _ := match i with
    | .flowF => commutingCompletionRealization.readout .flowF
    | .flowG => id
    | .cut => commutingCompletionRealization.readout .cut
  anchor := actual.anchor

def without_cut : Realization signature where
  readout i _ := match i with
    | .flowF => commutingCompletionRealization.readout .flowF
    | .flowG => commutingCompletionRealization.readout .flowG
    | .cut => fun _ => false
  anchor := actual.anchor

theorem rejects_flowF : ¬ arena.Law without_flowF := by
  intro h
  exact h.1 (fun _ => rfl)

theorem rejects_flowG : ¬ arena.Law without_flowG := by
  intro h
  exact h.1 (fun _ => rfl)

theorem rejects_cut : ¬ arena.Law without_cut := by
  intro h
  apply h.2
  change KernelEquivalent
    (predictiveProjection counterexampleF (predictiveProjection counterexampleG (fun _ => false)))
    (predictiveProjection counterexampleG (predictiveProjection counterexampleF (fun _ => false)))
  unfold KernelEquivalent
  simp only [predictive_projection_kernel]
  ext pair
  constructor <;> intro _ n m <;> rfl

theorem variation : Variation arena actual :=
  ⟨commutativity_hypothesis_is_necessary, without_flowF, rejects_flowF⟩

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    cases i
    · refine ⟨without_flowF, ?_, rfl, rejects_flowF⟩
      intro j h
      cases j <;> first | exact (h rfl).elim | rfl
    · refine ⟨without_flowG, ?_, rfl, rejects_flowG⟩
      intro j h
      cases j <;> first | exact (h rfl).elim | rfl
    · refine ⟨without_cut, ?_, rfl, rejects_cut⟩
      intro j h
      cases j <;> first | exact (h rfl).elim | rfl
  · intro i
    exact Fin.elim0 i

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  · exact ⟨(), FourState.a, FourState.c, by decide⟩
  · exact ⟨(), FourState.a, FourState.b, by decide⟩
  · exact ⟨(), FourState.a, FourState.d, by decide⟩

def registration : Registration arena CommutativityNecessaryStatement where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

#print axioms registration
end Reg.Support.LegacyRelations.Completion
