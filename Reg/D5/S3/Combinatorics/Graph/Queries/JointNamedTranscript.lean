import D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Cardinality readouts for transcript naming counts and graph posteriors. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
open _root_.D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript

noncomputable section
universe u v w k

private abbrev countSignature : Signature where
  Params := Type v
  State N := Set N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def bannedCard : Realization countSignature.{v} :=
  realize countSignature (fun _ _ names => names.ncard) (fun e => nomatch e)

private def oneBan : Realization countSignature.{v} :=
  realize countSignature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev countArena : Arena where
  signature := countSignature.{v}
  Law R := ∀ {V : Type u} {N : Type v} [Fintype V] [Fintype N]
    (p : PassiveProtocol N (fun _ => Option (Set N)))
    (ref : SimpleGraph V × (V ↪ N)) (G : SimpleGraph V)
    (base : V ↪ N) (initial : Set N) (_hInit : initial ⊆ Set.range base)
    (_hRef : ∀ v, base v ∈ initial → ref.2 v = base v),
    let T := runPassiveProtocol readWorld p ref
    let seen := initial ∪ revealedNames T
    let banned := absentNames T
    let bannedCount := R.readout () N banned
    Nat.card {f : V ↪ N // runPassiveProtocol readWorld p (G, f) = T ∧
      ∀ v, base v ∈ initial → f v = base v} =
      Nat.card (Feasible T G base initial) *
        (Fintype.card N - seen.ncard - bannedCount).descFactorial (Fintype.card V - seen.ncard)

private def singletonNaming : ULift.{u} Unit ↪ ULift.{v} Unit :=
  ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩

private theorem oneBan_invalid : ¬ countArena.{u, v}.Law oneBan := by
  intro h
  let f := singletonNaming.{u, v}
  let G : SimpleGraph (ULift.{u} Unit) := ⊥
  have hbad := h .stop (G, f) G f ∅ (Set.empty_subset _) (fun _ _ => rfl)
  dsimp only [oneBan, realize] at hbad
  have hseen : (∅ ∪ revealedNames (runPassiveProtocol readWorld .stop (G, f))).ncard = 0 := by
    simp [runPassiveProtocol, revealedNames]
  simp only [hseen, Fintype.card_ulift, Fintype.card_unit, Nat.sub_zero, Nat.sub_self,
    Nat.descFactorial_one, Nat.mul_zero] at hbad
  have hNonempty : Nonempty {g : ULift.{u} Unit ↪ ULift.{v} Unit //
      runPassiveProtocol readWorld .stop (G, g) = runPassiveProtocol readWorld .stop (G, f) ∧
        ∀ v, f v ∈ (∅ : Set (ULift.{v} Unit)) → g v = f v} :=
    ⟨⟨f, rfl, fun _ _ => rfl⟩⟩
  exact Nat.card_ne_zero.mpr ⟨hNonempty, inferInstance⟩ hbad

private theorem bannedCard_varies :
    bannedCard.{v}.readout () (ULift.{v} Unit) ∅ ≠
      bannedCard.{v}.readout () (ULift.{v} Unit) Set.univ := by
  simp [bannedCard, realize, Nat.card_eq_fintype_card]

def countEvidence : Registration countArena.{u, v} (type_of% (@transcript_naming_count.{u, v})) where
  actual := bannedCard
  bridge := Iff.rfl
  variation := ⟨@transcript_naming_count.{u, v}, oneBan, oneBan_invalid⟩
  sensitivity := ⟨fun i => ⟨oneBan, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl,
    oneBan_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ =>
    ⟨ULift.{v} Unit, ∅, Set.univ, bannedCard_varies⟩

private abbrev placementSignature : Signature where
  Params := Unit
  State _ := Type k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def placementCard : Realization placementSignature.{k} :=
  realize placementSignature (fun _ _ placements => Nat.card placements) (fun e => nomatch e)

private def zeroPlacements : Realization placementSignature.{k} :=
  realize placementSignature (fun _ _ _ => 0) (fun e => nomatch e)

set_option linter.checkUnivs false in
private abbrev posteriorArena : Arena where
  signature := placementSignature.{max u v}
  Law R := ∀ {V : Type u} {N : Type v} [Fintype V] [Fintype N]
    {W : Type w} (π : PMF W) (graph : W → SimpleGraph V)
    (p : PassiveProtocol N (fun _ => Option (Set N)))
    (ref : SimpleGraph V × (V ↪ N)) (base : V ↪ N)
    (initial : Set N) (_hInit : initial ⊆ Set.range base)
    (_hRef : ∀ v, base v ∈ initial → ref.2 v = base v),
    let T := runPassiveProtocol readWorld p ref
    let X := {f : V ↪ N // ∀ v, base v ∈ initial → f v = base v}
    let : Fintype X := Fintype.ofFinite X
    let : Nonempty X := ⟨⟨base, fun _ _ => rfl⟩⟩
    let μ : PMF (W × X) := π.bind fun y => (uniformPmf X).map (Prod.mk y)
    let H : Set (W × X) := {x | runPassiveProtocol readWorld p (graph x.1, x.2.1) = T}
    let weight (y : W) : ℝ≥0∞ := π y * ↑(R.readout () () (Feasible T (graph y) base initial))
    μ.toOuterMeasure H ≠ 0 →
      ∀ y, μ.toOuterMeasure (H ∩ {x | x.1 = y}) / μ.toOuterMeasure H =
        weight y / ∑' z, weight z

private theorem zeroPlacements_invalid : ¬ posteriorArena.{u, v, w}.Law zeroPlacements.{max u v} := by
  intro h
  let f := singletonNaming.{u, v}
  let G : SimpleGraph (ULift.{u} Unit) := ⊥
  let Y := ULift.{w} Unit
  let y : Y := ⟨()⟩
  let X := {g : ULift.{u} Unit ↪ ULift.{v} Unit //
    ∀ v, f v ∈ (∅ : Set (ULift.{v} Unit)) → g v = f v}
  let : Fintype X := Fintype.ofFinite X
  let : Nonempty X := ⟨⟨f, fun _ _ => rfl⟩⟩
  let μ : PMF (Y × X) := (PMF.pure y).bind fun z => (uniformPmf X).map (Prod.mk z)
  have hMass : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)
  have hEq : ({x : Y × X | x.1 = y} : Set (Y × X)) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim x.1 y
  have hbad := h (PMF.pure y) (fun _ => G) .stop (G, f) f ∅ (Set.empty_subset _)
    (fun _ _ => rfl)
  dsimp only [zeroPlacements, realize, runPassiveProtocol] at hbad
  have hbad' := hbad (by
    change μ.toOuterMeasure {x | ([] : History (ULift.{v} Unit)) = []} ≠ 0
    simpa only [Set.ofPred_true, eq_self_iff_true, hMass] using one_ne_zero) y
  simp only [eq_self_iff_true, Set.ofPred_true, Nat.cast_zero] at hbad'
  change μ.toOuterMeasure (Set.univ ∩ {x | x.1 = y}) / μ.toOuterMeasure Set.univ =
    (PMF.pure y) y * (0 : ℝ≥0∞) / ∑' z, (PMF.pure y) z * (0 : ℝ≥0∞) at hbad'
  simp [hEq, hMass] at hbad'

private theorem placementCard_varies :
    placementCard.{k}.readout () () (ULift.{k} Empty) ≠
      placementCard.{k}.readout () () (ULift.{k} Unit) := by
  simp [placementCard, realize, Nat.card_eq_fintype_card]

def posteriorEvidence : Registration posteriorArena.{u, v, w}
    (type_of% (@graph_posterior.{u, v, w})) where
  actual := placementCard.{max u v}
  bridge := Iff.rfl
  variation := ⟨@graph_posterior.{u, v, w}, zeroPlacements.{max u v}, zeroPlacements_invalid⟩
  sensitivity := ⟨fun i => ⟨zeroPlacements.{max u v}, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl,
    zeroPlacements_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ =>
    ⟨(), ULift.{max u v} Empty, ULift.{max u v} Unit, placementCard_varies⟩


def countRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@transcript_naming_count.{u, v}) (Realization countSignature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript.transcript_naming_count
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript.countEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨countArena.{u, v}⟩
  objectArena := .source ⟨countArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena.{u, v} ⟨countEvidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature (fun _ _ names => names.ncard) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


def posteriorRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@graph_posterior.{u, v, w}) (Realization placementSignature.{max u v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript.graph_posterior
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript.posteriorEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨posteriorArena.{u, v, w}⟩
  objectArena := .source ⟨posteriorArena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source posteriorArena.{u, v, w} ⟨posteriorEvidence.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize placementSignature.{max u v} (fun _ _ placements => Nat.card placements)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "value", "body",
        "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Queries.JointNamedTranscript
