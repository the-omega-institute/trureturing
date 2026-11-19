import D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The cardinality of a possible successor set. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
open _root_.D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound

noncomputable section
universe u

private abbrev targetSignature : Signature where
  Params := Type u
  State C := Finset C
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def targetCard : Realization targetSignature.{u} :=
  realize targetSignature (fun _ _ targets => targets.card) (fun e => nomatch e)

private def zeroCard : Realization targetSignature.{u} :=
  realize targetSignature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev targetArena : Arena where
  signature := targetSignature.{u}
  Law R := ∀ {C : Type u} [Finite C] (s d : C → Bool) (x : C) (targets : Finset C)
    (_not_self : x ∉ targets) (_hcolors : ∀ c, 2 ≤ Nat.card (Side s c))
    (μ : PMF (Compatible s d)) (_hμ : ∀ σ, μ σ = (Nat.card (Compatible s d) : ℝ≥0∞)⁻¹),
    let choices := Nat.card (Side s (d x)) - 1
    let targetCount := R.readout () C targets
    μ.toOuterMeasure {σ | σ.1 x ∈ targets} ≤ (targetCount : ℝ≥0∞) / choices

private def fourColors (x : ULift.{u} (Fin 4)) : Bool :=
  decide (x.down.val < 2)

private theorem fourColors_count (b : Bool) : Nat.card (Side fourColors.{u} b) = 2 := by
  let e : Side fourColors.{u} b ≃ {x : Fin 4 // decide (x.val < 2) = b} :=
    Equiv.subtypeEquiv Equiv.ulift (fun _ => Iff.rfl)
  rw [Nat.card_congr e]
  cases b <;> rw [Nat.card_eq_fintype_card] <;> decide

private theorem rejectsZero : ¬ targetArena.{u}.Law zeroCard := by
  classical
  intro h
  let C := ULift.{u} (Fin 4)
  let s := fourColors.{u}
  let d : C → Bool := fun x => !(s x)
  let x : C := ⟨0⟩
  have hCount (b : Bool) : Nat.card (Side s b) = 2 := fourColors_count b
  have h01 : inventory s d false true = 2 := by
    rw [show inventory s d false true = Nat.card (Side s false) from cross_inventory s false]
    exact hCount false
  have h10 : inventory s d true false = 2 := by
    rw [show inventory s d true false = Nat.card (Side s true) from cross_inventory s true]
    exact hCount true
  have hC : Nat.card C = 4 := by simp [C, Nat.card_eq_fintype_card]
  have hK : Nat.card (Compatible s d) = 2 := by
    rw [compatible_cycle_card s d (h01.trans h10.symm), hC, h01, hCount, hCount]
    decide
  let : Fintype (Compatible s d) := Fintype.ofFinite _
  let : Nonempty (Compatible s d) := (Nat.card_pos_iff.mp (hK ▸ (by decide : 0 < 2))).1
  let μ := uniformPmf (Compatible s d)
  have hμ (σ : Compatible s d) : μ σ = (Nat.card (Compatible s d) : ℝ≥0∞)⁻¹ := by
    rw [Nat.card_eq_fintype_card]
    rfl
  let targets := Finset.univ.filter (fun y => s y = d x)
  have hx : x ∉ targets := by
    simp [targets, d]
  have hEvent : {σ : Compatible s d | σ.1 x ∈ targets} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro σ
    simpa [targets] using (σ.2.2.2 x).symm
  have hMass : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)
  have hbad := h s d x targets hx (fun b => (hCount b).ge) μ hμ
  change μ.toOuterMeasure {σ : Compatible s d | σ.1 x ∈ targets} ≤
    (zeroCard.readout () C targets : ℝ≥0∞) / ((Nat.card (Side s (d x)) - 1 : ℕ) : ℝ≥0∞) at hbad
  simp [hEvent, hMass, zeroCard, realize] at hbad

private theorem targetCard_varies :
    targetCard.{u}.readout () (ULift.{u} Unit) ∅ ≠
      targetCard.{u}.readout () (ULift.{u} Unit) {⟨()⟩} := by
  simp [targetCard, realize]

def targetEvidence : Registration targetArena.{u} (type_of% (@successor_set_mass_le.{u})) where
  actual := targetCard
  bridge := Iff.rfl
  variation := ⟨@successor_set_mass_le.{u}, zeroCard, rejectsZero⟩
  sensitivity := ⟨fun i =>
    ⟨zeroCard, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsZero⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{u} Unit, ∅, {⟨()⟩}, targetCard_varies⟩

def targetRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@successor_set_mass_le.{u}) (Realization targetSignature.{u}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound.successor_set_mass_le
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound.targetEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨targetArena.{u}⟩
  objectArena := .source ⟨targetArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source targetArena.{u} ⟨targetEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize targetSignature (fun _ _ targets => targets.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound
