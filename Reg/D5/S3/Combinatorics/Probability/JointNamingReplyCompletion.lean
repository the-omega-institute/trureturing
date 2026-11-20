import D5.S3.Combinatorics.Probability.JointNamingReplyCompletion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The positive mass of a consistent ordered reply depends on the number of fresh injections. -/

open LeanInformationAudit
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open _root_.D5.S3.Combinatorics.Probability.NamingRestrictionLaw (namingMass)
open _root_.D5.S3.Combinatorics.Probability.OrderedNamingReply
open _root_.D5.S3.Combinatorics.Probability.JointNamingReplyCompletion
open _root_.D5.S3.Combinatorics.Probability.NamingUpdate (unused)
open _root_.D5.S3.Combinatorics.Probability.PartialNameAssignment (Candidates)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Probability.JointNamingReplyCompletion

noncomputable section
universe u v w

private abbrev signature : Signature where
  Params := Type w
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{w} :=
  realize signature (fun _ _ size => namingMass size) (fun e => nomatch e)

private def zeroMass : Realization signature.{w} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{w}
  Law R := ∀ {V : Type u} {N : Type v} {I : Type w} [DecidableEq V] [Fintype V] [Finite N]
    (K : Finset V) (A : Finset N) (known : K ↪ N) (_hsep : ∀ x, known x ∉ A)
    (h : Nonempty (Candidates K A known)) (read : I → V),
    let L := namedAfter K read
    let _ : Fintype (Candidates K A known) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A known) := h
    let μ := uniformPmf (Candidates K A known)
    let q := μ.map (fun f i => f.1 (read i))
    let mass := R.readout () I (Nat.card (FreshVertices K read ↪ A))
    (∀ reply : I → N, q reply =
      @ite ℝ≥0∞ (IsConsistentReply K A known read reply) (Classical.propDecidable _) mass 0) ∧
    ∃ kernel : ∀ reply ∈ q.support, PMF (V ↪ N),
      (∀ reply hp, ∃ expanded : L ↪ N,
        (∀ i (hi : read i ∈ L), expanded ⟨read i, hi⟩ = reply i) ∧
        ∃ h : Nonempty (Candidates L (unused A L expanded) expanded),
          let _ : Fintype (Candidates L (unused A L expanded) expanded) := Fintype.ofFinite _
          let _ : Nonempty (Candidates L (unused A L expanded) expanded) := h
          kernel reply hp =
            (uniformPmf (Candidates L (unused A L expanded) expanded)).map Subtype.val) ∧
      (q.bindOnSupport fun reply hp => (kernel reply hp).map (Prod.mk reply)) =
        μ.map (fun f => ((fun i => f.1 (read i)), f.1))

private theorem zeroMass_invalid : ¬ arena.{u, v, w}.Law zeroMass := by
  classical
  intro h
  let I := ULift.{w} Empty
  let V := ULift.{u} Empty
  let N := ULift.{v} Empty
  let K : Finset V := ∅
  let A : Finset N := ∅
  let known : K ↪ N := Function.Embedding.ofIsEmpty
  have hsep (x : K) : known x ∉ A := isEmptyElim x.1
  have hCandidates : Nonempty (Candidates K A known) :=
    ⟨⟨Function.Embedding.ofIsEmpty, fun x => isEmptyElim x.1, fun x => isEmptyElim x.1⟩⟩
  let read : I → V := isEmptyElim
  let _ : Fintype (Candidates K A known) := Fintype.ofFinite _
  let _ : Nonempty (Candidates K A known) := hCandidates
  let ν := (uniformPmf (Candidates K A known)).map (fun f i => f.1 (read i))
  have hZero (reply : I → N) : ν reply = 0 := by
    have hMass := (h K A known hsep hCandidates read).1 reply
    change ν reply =
      @ite ℝ≥0∞ (IsConsistentReply K A known read reply) (Classical.propDecidable _) 0 0 at hMass
    simpa only [ite_self] using hMass
  simpa only [hZero, tsum_zero, zero_ne_one] using ν.tsum_coe

private theorem actual_varies :
    actual.{w}.readout () (ULift.{w} Unit) 1 ≠ actual.{w}.readout () (ULift.{w} Unit) 2 := by
  change namingMass 1 ≠ namingMass 2
  simp only [namingMass, Nat.cast_one, Nat.cast_ofNat, inv_one]
  intro h
  have hInv := congrArg Inv.inv h
  norm_num at hInv

def evidence : Registration arena.{u, v, w} (type_of% (@joint_ordered_reply_completion.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@joint_ordered_reply_completion.{u, v, w}, zeroMass, zeroMass_invalid⟩
  sensitivity := ⟨fun i => ⟨zeroMass, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, zeroMass_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{w} Unit, 1, 2, actual_varies.{w}⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@joint_ordered_reply_completion.{u, v, w}) (Realization signature.{w}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Probability.JointNamingReplyCompletion.joint_ordered_reply_completion
  realizationName := `Reg.D5.S3.Combinatorics.Probability.JointNamingReplyCompletion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, w}⟩
  objectArena := .source ⟨arena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, w} ⟨evidence.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ size => namingMass size) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Probability.JointNamingReplyCompletion
    definition := none
    coordinates := #[2]
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
end Reg.D5.S3.Combinatorics.Probability.JointNamingReplyCompletion
