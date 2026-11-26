import D5.S3.Combinatorics.Probability.PartialNameAssignment
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The conditional hit probability depends on the available name count. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Probability.PartialNameAssignment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open Function
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Probability.PartialNameAssignment

noncomputable section
universe u v

private abbrev signature : Signature where
  Params := Type v
  State N := Finset N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{v} :=
  realize signature (fun _ _ names => names.card) (fun e => nomatch e)

private def augmented : Realization signature.{v} :=
  realize signature (fun _ _ names => names.card + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {V : Type u} {N : Type v} [DecidableEq V] [Fintype V] [Fintype N]
    (K : Finset V) (A : Finset N) (knownNames : K ↪ N)
    (_hsep : ∀ x, knownNames x ∉ A) (h : Nonempty (Candidates K A knownNames)),
    let availableCount := R.readout () N A
    let : Nonempty (V ↪ N) := h.map Subtype.val
    ∃ ν : PMF (Candidates K A knownNames),
      (∀ f, ν f = (Nat.card (Candidates K A knownNames) : ℝ≥0∞)⁻¹) ∧
      (∀ hs, (uniformPmf (V ↪ N)).filter
        {f | (∀ x : K, f x = knownNames x) ∧ ∀ x : {v // v ∉ K}, f x ∈ A} hs =
          ν.map Subtype.val) ∧
      (∀ a : A, ν.toOuterMeasure {f | ∃ x : {v // v ∉ K}, f.1 x = a.1} =
        (Nat.card {v // v ∉ K} : ℝ≥0∞) / availableCount)

private theorem rejectsAugmented : ¬ arena.{u, v}.Law augmented := by
  classical
  intro h
  let V := ULift.{u} Unit
  let N := ULift.{v} Unit
  let K : Finset V := ∅
  let A : Finset N := {⟨()⟩}
  let knownNames : K ↪ N := ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  have hsep (x : K) : knownNames x ∉ A := False.elim (Finset.notMem_empty x.1 x.2)
  let a : A := ⟨⟨()⟩, Finset.mem_singleton_self _⟩
  have hCandidates : Nonempty (Candidates K A knownNames) :=
    ⟨⟨⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩,
      fun _ => rfl, fun _ => a.2⟩⟩
  obtain ⟨ν, hν, _, hActual⟩ := uniform_remaining_name_hit K A knownNames hsep hCandidates
  obtain ⟨μ, hμ, _, hAugmented⟩ := h K A knownNames hsep hCandidates
  have heq : ν = μ := PMF.ext fun f => (hν f).trans (hμ f).symm
  have hmass := (hActual a).symm.trans (heq ▸ hAugmented a)
  have hV : Nat.card {v : V // v ∉ K} = 1 := by simp [V, K, Nat.card_eq_fintype_card]
  have hA : A.card = 1 := Finset.card_singleton _
  have hOne : (1 : ℝ≥0∞) / 1 = 1 / 2 := by
    simpa only [augmented, realize, hV, hA, Nat.cast_one, show (1 + 1 : ℕ) = 2 by rfl,
      Nat.cast_ofNat] using hmass
  have hbad : (2 : ℝ≥0∞) = 1 := calc
    _ = 2 * (1 / 1) := by simp
    _ = 2 * (1 / 2) := congrArg (fun t : ℝ≥0∞ => 2 * t) hOne
    _ = 1 := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  norm_num at hbad

private theorem actualVaries :
    actual.{v}.readout () (ULift.{v} Unit) ∅ ≠
      actual.{v}.readout () (ULift.{v} Unit) {⟨()⟩} := by
  simp [actual, realize]

def evidence : Registration arena.{u, v} (type_of% (@uniform_remaining_name_hit.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_remaining_name_hit.{u, v}, augmented, rejectsAugmented⟩
  sensitivity := ⟨fun i => ⟨augmented,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsAugmented⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{v} Unit, ∅, {⟨()⟩}, actualVaries⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@uniform_remaining_name_hit.{u, v}) (Realization signature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Probability.PartialNameAssignment.uniform_remaining_name_hit
  realizationName := `Reg.D5.S3.Combinatorics.Probability.PartialNameAssignment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨evidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ names => names.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Probability.PartialNameAssignment
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Probability.PartialNameAssignment
