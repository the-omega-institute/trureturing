import D5.S3.Combinatorics.Probability.NamingRestrictionLaw
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The mass of a restricted naming depends on the size of its injective naming space. -/

open LeanInformationAudit
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open _root_.D5.S3.Combinatorics.Probability.NamingRestrictionLaw
open _root_.D5.S3.Combinatorics.Probability.PartialNameAssignment (Candidates residualEmbedding)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Probability.NamingRestrictionLaw

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
  Law R := ∀ {V : Type u} {N : Type v} {Z : Type w}
    [DecidableEq V] [Finite V] [Finite N] [Finite Z]
    (K : Finset V) (A : Finset N) (knownNames : K ↪ N)
    (hsep : ∀ x, knownNames x ∉ A) (h : Nonempty (Candidates K A knownNames))
    (ι : Z ↪ {v // v ∉ K}),
    let _ : Fintype (Candidates K A knownNames) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A knownNames) := h
    let mass := R.readout () Z (Nat.card (Z ↪ A))
    ∀ g : Z ↪ A, ((uniformPmf (Candidates K A knownNames)).map
      (fun f => ι.trans (residualEmbedding K A knownNames hsep f))) g = mass

private theorem zeroMass_invalid : ¬ arena.{u, v, w}.Law zeroMass := by
  classical
  intro h
  let V := ULift.{u} Empty
  let N := ULift.{v} Empty
  let Z := ULift.{w} Empty
  let K : Finset V := ∅
  let A : Finset N := ∅
  let knownNames : K ↪ N := Function.Embedding.ofIsEmpty
  have hsep (x : K) : knownNames x ∉ A := isEmptyElim x.1
  have hCandidates : Nonempty (Candidates K A knownNames) :=
    ⟨⟨Function.Embedding.ofIsEmpty, fun x => isEmptyElim x.1, fun x => isEmptyElim x.1⟩⟩
  let ι : Z ↪ {v // v ∉ K} := Function.Embedding.ofIsEmpty
  let _ : Fintype (Candidates K A knownNames) := Fintype.ofFinite _
  let _ : Nonempty (Candidates K A knownNames) := hCandidates
  let ν := (uniformPmf (Candidates K A knownNames)).map
    (fun f => ι.trans (residualEmbedding K A knownNames hsep f))
  have hZero (g : Z ↪ A) : ν g = 0 := h K A knownNames hsep hCandidates ι g
  simpa only [hZero, tsum_zero, zero_ne_one] using ν.tsum_coe

private theorem actual_varies :
    actual.{w}.readout () (ULift.{w} Empty) 1 ≠ actual.{w}.readout () (ULift.{w} Empty) 2 := by
  change namingMass 1 ≠ namingMass 2
  simp only [namingMass, Nat.cast_one, Nat.cast_ofNat, inv_one]
  intro h
  have hInv := congrArg Inv.inv h
  norm_num at hInv

def evidence : Registration arena.{u, v, w} (type_of% (@uniform_residual_restriction.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_residual_restriction.{u, v, w}, zeroMass, zeroMass_invalid⟩
  sensitivity := ⟨fun i => ⟨zeroMass, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, zeroMass_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{w} Empty, 1, 2, actual_varies.{w}⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@uniform_residual_restriction.{u, v, w}) (Realization signature.{w}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Probability.NamingRestrictionLaw.uniform_residual_restriction
  realizationName := `Reg.D5.S3.Combinatorics.Probability.NamingRestrictionLaw.evidence
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
    owner := `D5.S3.Combinatorics.Probability.NamingRestrictionLaw
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Probability.NamingRestrictionLaw
