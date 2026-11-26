import D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The number of positions constrained for the first time by the suffix. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw
open _root_.D5.S3.Combinatorics.Graph.Queries.PartialForwardOrderLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw

noncomputable section
universe u v

attribute [local instance] Classical.propDecidable

private abbrev CountSignature : Signature where
  Params := Type u
  State P := Finset P
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actualCount : Realization CountSignature.{u} :=
  realize CountSignature (fun _ _ s => s.card) (fun e => nomatch e)

private def extraPosition : Realization CountSignature.{u} :=
  realize CountSignature (fun _ _ s => s.card + 1) (fun e => nomatch e)

private abbrev CountArena : Arena where
  signature := CountSignature.{u}
  Law R := ∀ {P : Type u} {V : Type v} [Fintype P] [DecidableEq P]
    (choices : P → Bool → V)
    (_hChoice : ∀ p, Function.Injective (choices p))
    (earlier later : P → Bool → Option V) (seen fresh : Finset P)
    (_hDisjoint : Disjoint seen fresh)
    (_hSeen : ∀ p, p ∈ seen ↔ ∃ b v, earlier p b = some v)
    (_hFresh : ∀ p, p ∈ fresh ↔ ∃ b v, later p b = some v)
    (_hCompatible : Compatible choices earlier),
    let μ := uniformPmf (P → Equiv.Perm Bool)
    let E : Set (P → Equiv.Perm Bool) := {f | Matches choices earlier f}
    let F : Set (P → Equiv.Perm Bool) := {f | Matches choices later f}
    let freshCount := R.readout () P fresh
    μ.toOuterMeasure (E ∩ F) / μ.toOuterMeasure E =
      if Compatible choices later then ((2 ^ freshCount : ℕ) : ℝ≥0∞)⁻¹ else 0

private abbrev Position := ULift.{u} Unit
private abbrev Value := ULift.{v} Bool

private def bitChoices : Position.{u} → Bool → Value.{v} :=
  fun _ b => ⟨b⟩

private theorem bitChoices_injective (p : Position.{u}) :
    Function.Injective (bitChoices.{u,v} p) :=
  fun _ _ h => congrArg ULift.down h

private theorem extraPosition_invalid : ¬ CountArena.{u,v}.Law extraPosition := by
  intro h
  let o : Position.{u} → Bool → Option Value.{v} := fun _ _ => none
  let μ := uniformPmf (Position.{u} → Equiv.Perm Bool)
  let E : Set (Position.{u} → Equiv.Perm Bool) := {f | Matches bitChoices.{u,v} o f}
  have hCompatible : Compatible bitChoices.{u,v} o := by simp [Compatible, o]
  have hBad := h bitChoices.{u,v} bitChoices_injective o o ∅ ∅
    (by simp) (by simp [o]) (by simp [o]) hCompatible
  have hAll : E = Set.univ := by ext f; simp [E, Matches, o]
  have hMass : μ.toOuterMeasure E = 1 := by
    rw [hAll]
    exact (μ.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _)
  change μ.toOuterMeasure (E ∩ E) / μ.toOuterMeasure E =
    if Compatible bitChoices.{u,v} o then ((2 ^ (0 + 1) : ℕ) : ℝ≥0∞)⁻¹ else 0 at hBad
  rw [Set.inter_self, hMass, ite_eq_left hCompatible] at hBad
  have hUnequal : (1 : ℝ≥0∞) ≠ 2 := by norm_num
  apply hUnequal
  simpa using congrArg (fun x : ℝ≥0∞ => x⁻¹) hBad

private theorem count_varies :
    actualCount.{u}.readout () Position.{u} ∅ ≠
      actualCount.{u}.readout () Position.{u} {⟨()⟩} := by
  change 0 ≠ 1
  decide

def evidence : Registration CountArena.{u,v} (type_of% (@suffix_after_prefix.{u,v})) where
  actual := actualCount
  bridge := Iff.rfl
  variation := ⟨@suffix_after_prefix.{u,v}, extraPosition, extraPosition_invalid⟩
  sensitivity := ⟨fun i => ⟨extraPosition,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, extraPosition_invalid⟩,
    fun e => nomatch e⟩
  dependence := fun _ => ⟨Position.{u}, ∅, {⟨()⟩}, count_varies⟩

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@suffix_after_prefix.{u,v}) (Realization CountSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw.suffix_after_prefix
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨CountArena.{u,v}⟩
  objectArena := .source ⟨CountArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source CountArena.{u,v} ⟨evidence.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize CountSignature (fun _ _ s => s.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Queries.ForwardSuffixLaw
