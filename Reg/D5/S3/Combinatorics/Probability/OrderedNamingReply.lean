import D5.S3.Combinatorics.Probability.OrderedNamingReply
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The positive mass of a consistent ordered reply depends on the number of fresh injections. -/

open LeanInformationAudit
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open _root_.D5.S3.Combinatorics.Probability.NamingRestrictionLaw (namingMass)
open _root_.D5.S3.Combinatorics.Probability.OrderedNamingReply
open _root_.D5.S3.Combinatorics.Probability.PartialNameAssignment (Candidates)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Probability.OrderedNamingReply

noncomputable section
universe u v w

private abbrev signature : Signature where
  Params := Type u
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ size => namingMass size) (fun e => nomatch e)

private def zeroMass : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} {V : Type v} {N : Type w}
    [DecidableEq V] [Finite V] [Finite N]
    (K : Finset V) (A : Finset N) (known : K ↪ N) (_hsep : ∀ v, known v ∉ A)
    (h : Nonempty (Candidates K A known)) (read : I → V),
    let _ : Fintype (Candidates K A known) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A known) := h
    let mass := R.readout () I (Nat.card (FreshVertices K read ↪ A))
    ∀ reply : I → N,
      ((uniformPmf (Candidates K A known)).map (fun f i => f.1 (read i))) reply =
        @ite ℝ≥0∞ (IsConsistentReply K A known read reply) (Classical.propDecidable _) mass 0

private theorem zeroMass_invalid : ¬ arena.{u, v, w}.Law zeroMass := by
  classical
  intro h
  let I := ULift.{u} Empty
  let V := ULift.{v} Empty
  let N := ULift.{w} Empty
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
    have hMass := h K A known hsep hCandidates read reply
    change ν reply =
      @ite ℝ≥0∞ (IsConsistentReply K A known read reply) (Classical.propDecidable _) 0 0 at hMass
    simpa only [ite_self] using hMass
  simpa only [hZero, tsum_zero, zero_ne_one] using ν.tsum_coe

private theorem actual_varies :
    actual.{u}.readout () (ULift.{u} Unit) 1 ≠ actual.{u}.readout () (ULift.{u} Unit) 2 := by
  change namingMass 1 ≠ namingMass 2
  simp only [namingMass, Nat.cast_one, Nat.cast_ofNat, inv_one]
  intro h
  have hInv := congrArg Inv.inv h
  norm_num at hInv

def evidence : Registration arena.{u, v, w} (type_of% (@ordered_reply_mass.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordered_reply_mass.{u, v, w}, zeroMass, zeroMass_invalid⟩
  sensitivity := ⟨fun i => ⟨zeroMass, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, zeroMass_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{u} Unit, 1, 2, actual_varies.{u}⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@ordered_reply_mass.{u, v, w}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Probability.OrderedNamingReply.ordered_reply_mass
  realizationName := `Reg.D5.S3.Combinatorics.Probability.OrderedNamingReply.evidence
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
    owner := `D5.S3.Combinatorics.Probability.OrderedNamingReply
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Probability.OrderedNamingReply
