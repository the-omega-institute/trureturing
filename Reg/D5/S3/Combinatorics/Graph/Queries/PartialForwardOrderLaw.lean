import D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Readouts for the observed position count and the compatible worlds. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw

noncomputable section
universe u v w

attribute [local instance] Classical.propDecidable

private def emptyObserved (P : Type u) (V : Type v) : P → Bool → Option V :=
  fun _ _ => none

private def bitChoices : ULift.{u} Unit → Bool → ULift.{v} Bool :=
  fun _ b => ⟨b⟩

private theorem bitChoices_injective (p : ULift.{u} Unit) :
    Function.Injective (bitChoices.{u,v} p) :=
  fun _ _ h => congrArg ULift.down h

private theorem matches_emptyObserved {P : Type u} {V : Type v} (choices : P → Bool → V)
    (f : P → Equiv.Perm Bool) : Matches choices (emptyObserved P V) f := by
  simp [Matches, emptyObserved]

private theorem compatible_emptyObserved {P : Type u} {V : Type v} (choices : P → Bool → V) :
    Compatible choices (emptyObserved P V) := by
  simp [Compatible, emptyObserved]

private abbrev countSignature : Signature where
  Params := Type u
  State P := Finset P
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def observedCard : Realization countSignature.{u} :=
  realize countSignature (fun _ _ s => s.card) (fun e => nomatch e)

private def alwaysOne : Realization countSignature.{u} :=
  realize countSignature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev likelihoodArena : Arena where
  signature := countSignature.{u}
  Law R := ∀ {P : Type u} {V : Type v} [Fintype P] [DecidableEq P]
    (choices : P → Bool → V) (_hChoice : ∀ p, Function.Injective (choices p))
    (observed : P → Bool → Option V)
    (s : Finset P) (_hS : ∀ p, p ∈ s ↔ ∃ b v, observed p b = some v),
    let observedCount := R.readout () P s
    (uniformPmf (P → Equiv.Perm Bool)).toOuterMeasure {f | Matches choices observed f} =
      if Compatible choices observed then ((2 ^ observedCount : ℕ) : ℝ≥0∞)⁻¹ else 0

private theorem alwaysOne_invalid : ¬ likelihoodArena.{u,v}.Law alwaysOne := by
  intro h
  let P := ULift.{u} Unit
  let V := ULift.{v} Bool
  let μ := uniformPmf (P → Equiv.Perm Bool)
  have hbad := h bitChoices.{u,v} bitChoices_injective (emptyObserved P V) ∅
    (fun _ => by simp [emptyObserved])
  have he : {f | Matches bitChoices (emptyObserved P V) f} = Set.univ :=
    Set.eq_univ_of_forall fun f => matches_emptyObserved bitChoices f
  change μ.toOuterMeasure {f | Matches bitChoices (emptyObserved P V) f} =
    (if Compatible bitChoices (emptyObserved P V) then (2 : ℝ≥0∞)⁻¹ else 0) at hbad
  rw [he, (μ.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _),
    ite_eq_left (compatible_emptyObserved bitChoices)] at hbad
  have hone : (1 : ℝ≥0∞) = 2 := by
    simpa only [inv_one, inv_inv] using congrArg (Inv.inv : ℝ≥0∞ → ℝ≥0∞) hbad
  have impossible : (1 : ℕ) = 2 := by exact_mod_cast hone
  omega

private theorem observedCard_varies :
    observedCard.{u}.readout () (ULift.{u} Unit) ∅ ≠
      observedCard.{u}.readout () (ULift.{u} Unit) {⟨()⟩} := by
  simp [observedCard, realize]

def likelihoodEvidence : Registration likelihoodArena.{u,v}
    (type_of% (@partial_forward_order_likelihood.{u,v})) where
  actual := observedCard
  bridge := Iff.rfl
  variation := ⟨@partial_forward_order_likelihood.{u,v}, alwaysOne, alwaysOne_invalid⟩
  sensitivity := ⟨fun i => ⟨alwaysOne, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, alwaysOne_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{u} Unit, ∅, {⟨()⟩}, observedCard_varies⟩

def likelihoodRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@partial_forward_order_likelihood.{u,v}) (Realization countSignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw.partial_forward_order_likelihood
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw.likelihoodEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨likelihoodArena.{u,v}⟩
  objectArena := .source ⟨likelihoodArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source likelihoodArena.{u,v} ⟨likelihoodEvidence.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature (fun _ _ s => s.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

private abbrev worldSignature : Signature where
  Params := Σ P : Type u, Σ V : Type v, Σ W : Type w, W → P → Bool → V
  State params := params.1 → Bool → Option params.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ params := Set params.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def compatibleWorlds : Realization worldSignature.{u,v,w} :=
  realize worldSignature (fun _ params observed =>
    {world | Compatible (params.2.2.2 world) observed}) (fun e => nomatch e)

private def emptyWorlds : Realization worldSignature.{u,v,w} :=
  realize worldSignature (fun _ _ _ => ∅) (fun e => nomatch e)

private abbrev posteriorArena : Arena where
  signature := worldSignature.{u,v,w}
  Law R := ∀ {P : Type u} {V : Type v} {W : Type w} [Fintype P] [DecidableEq P]
    (π : PMF W) (choices : W → P → Bool → V)
    (_hChoice : ∀ world p, Function.Injective (choices world p))
    (observed : P → Bool → Option V)
    (s : Finset P) (_hS : ∀ p, p ∈ s ↔ ∃ b v, observed p b = some v),
    let Ω := P → Equiv.Perm Bool
    let μ : PMF (W × Ω) := π.bind fun world => (uniformPmf Ω).map (Prod.mk world)
    let H : Set (W × Ω) := {x | Matches (choices x.1) observed x.2}
    let feasible := R.readout () ⟨P,V,W,choices⟩ observed
    μ.toOuterMeasure H ≠ 0 →
      ∀ B : Set W, μ.toOuterMeasure (H ∩ Prod.fst ⁻¹' B) / μ.toOuterMeasure H =
        π.toOuterMeasure (feasible ∩ B) / π.toOuterMeasure feasible

private theorem emptyWorlds_invalid : ¬ posteriorArena.{u,v,w}.Law emptyWorlds := by
  intro h
  let P := ULift.{u} Unit
  let V := ULift.{v} Bool
  let W := ULift.{w} Unit
  let world : W := ⟨()⟩
  let π := PMF.pure world
  let μ := π.bind fun w => (uniformPmf (P → Equiv.Perm Bool)).map (Prod.mk w)
  let H : Set (W × (P → Equiv.Perm Bool)) :=
    {x | Matches bitChoices (emptyObserved P V) x.2}
  have hH : H = Set.univ := Set.eq_univ_of_forall fun x => matches_emptyObserved bitChoices x.2
  have hμ : μ.toOuterMeasure H = 1 := by
    rw [hH]
    exact (μ.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)
  have hBad := h π (fun _ => bitChoices.{u,v}) (fun _ => bitChoices_injective)
    (emptyObserved P V) ∅ (fun _ => by simp [emptyObserved])
    (show μ.toOuterMeasure H ≠ 0 by rw [hμ]; exact one_ne_zero) Set.univ
  change μ.toOuterMeasure (H ∩ Prod.fst ⁻¹' Set.univ) / μ.toOuterMeasure H =
    π.toOuterMeasure (∅ ∩ Set.univ) / π.toOuterMeasure ∅ at hBad
  simp [hμ] at hBad

private theorem compatibleWorlds_varies :
    compatibleWorlds.{u,v,w}.readout ()
      ⟨ULift.{u} Unit, ULift.{v} Bool, ULift.{w} Unit, fun _ => bitChoices.{u,v}⟩
      (emptyObserved _ _) ≠
    compatibleWorlds.{u,v,w}.readout ()
      ⟨ULift.{u} Unit, ULift.{v} Bool, ULift.{w} Unit, fun _ => bitChoices.{u,v}⟩
      (fun _ _ => some ⟨false⟩) := by
  intro h
  have hGood : (⟨()⟩ : ULift.{w} Unit) ∈ compatibleWorlds.{u,v,w}.readout ()
      ⟨ULift.{u} Unit, ULift.{v} Bool, ULift.{w} Unit, fun _ => bitChoices.{u,v}⟩
      (emptyObserved _ _) := compatible_emptyObserved _
  rw [h] at hGood
  change Compatible bitChoices.{u,v} (fun _ _ => some ⟨false⟩) at hGood
  exact hGood.2 ⟨()⟩ ⟨false⟩ rfl rfl

def posteriorEvidence : Registration posteriorArena.{u,v,w}
    (type_of% (@partial_forward_order_posterior.{u,v,w})) where
  actual := compatibleWorlds
  bridge := Iff.rfl
  variation := ⟨@partial_forward_order_posterior.{u,v,w}, emptyWorlds, emptyWorlds_invalid⟩
  sensitivity := ⟨fun i => ⟨emptyWorlds, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, emptyWorlds_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ =>
    ⟨⟨ULift.{u} Unit, ULift.{v} Bool, ULift.{w} Unit, fun _ => bitChoices.{u,v}⟩,
      emptyObserved _ _, fun _ _ => some ⟨false⟩, compatibleWorlds_varies⟩

def posteriorRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@partial_forward_order_posterior.{u,v,w}) (Realization worldSignature.{u,v,w}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw.partial_forward_order_posterior
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw.posteriorEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨posteriorArena.{u,v,w}⟩
  objectArena := .source ⟨posteriorArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source posteriorArena.{u,v,w} ⟨posteriorEvidence.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize worldSignature (fun _ params observed =>
    {world | Compatible (params.2.2.2 world) observed}) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
    definition := none
    coordinates := #[0, 1, 2, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
