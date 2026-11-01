import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.RationalRouting.TwoReplyProfile

/-! Source-owned full-profile variation, sensitivity and dependence. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.RationalRouting
open _root_.D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced

noncomputable section
namespace Reg.D5.S3.Observer.RationalRouting.TwoReplyProfile

abbrev signature : Signature where
  Params := Σ _u : List Bool, Σ _I : ProfileCell, ℕ
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ProfileCell
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p x => (acquireProfile (wordMatrix p.1.reverse) p.2.1 p.2.2).execute (attain p.1 x)) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => ⟨0,1⟩) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  let I : ProfileCell := ⟨0,3⟩
  refine ⟨⟨[],I,1⟩,1,2,?_⟩
  have h₁ := (acquired_original_profile [] I 1 le_rfl (by norm_num [I])
    (x := 1) (by norm_num [I,ProfileCell.Contains])).1
  have h₂ := (acquired_original_profile [] I 1 le_rfl (by norm_num [I])
    (x := 2) (by norm_num [I,ProfileCell.Contains])).1
  intro he
  change (acquireProfile (wordMatrix [].reverse) I 1).execute (attain [] 1) =
    (acquireProfile (wordMatrix [].reverse) I 1).execute (attain [] 2) at he
  rw [h₁,h₂] at he
  have hh := congrArg ProfileCell.lower he
  norm_num [containingCell,reply] at hh

def arena : Arena where
  signature := signature
  Law R := ∀ (u : List Bool) (I : ProfileCell) (B : ℕ)
    (hB : 1 ≤ B) (hl : 0 ≤ I.lower) {x : ℚ} (hx : I.Contains x),
    let A := wordMatrix u.reverse
    let z := attain u x
    let program := acquireProfile A I B
    let C := R.readout () ⟨u,I,B⟩ x
    let Q := profileScale A I B
    let J := firstInterval A (Q ^ 2) I (reply (Q ^ 2) z)
    let V := A.a * originalUpper I + A.b + 1
    C = containingCell B x ∧
      (∀ y : ℚ, C.Contains y ↔ 0 < y ∧ SameFuture B y x) ∧
      (∀ v : List Bool, ∀ m : ℕ, 1 ≤ m → m ≤ B →
        C.evaluate v m = reply m (attain v x)) ∧
      TwoReplyTrace Q z (program.actualReads z) ∧
      (findCut B I = none ↔ ∀ y : ℚ, I.Contains y → SameFuture B y x) ∧
      (∀ r : ℤ, determinedReply A I (Q ^ 2) = some r ↔
        ∀ y : ℚ, I.Contains y → reply (Q ^ 2) (mobius A y) = r) ∧
      (∀ s : ℕ, 1 ≤ s → ∀ r : ℤ, determinedReply A J s = some r ↔
        ∀ y : ℚ, J.Contains y → reply s (mobius A y) = r) ∧
      AcquisitionScans A I B z C ∧
      BoundedReplies Q V (program.actualReads z) ∧
      C.lower.den ≤ B ∧ C.upper.den ≤ B ∧
      replyWidths (program.actualReads z) ≤ 6*Nat.size Q + 2*Nat.size V + 4 ∧
      C.lower.num.natAbs ≤ B*originalUpper I ∧ C.upper.num.natAbs ≤ B*originalUpper I ∧
      J.width ≤ max I.width (max (Nat.size (Q^2)) (integerWidth (reply (Q^2) z)) +
        Nat.size (max (max A.a A.b) (max A.c A.d)) + 3) ∧
      (∀ e : ℕ, I.width ≤ e → 4*J.width ≤ acquisitionWidth A I B e ∧
        CutOperandWidths B I (acquisitionWidth A I B e) ∧
        CutOperandWidths B J (acquisitionWidth A I B e))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let I : ProfileCell := ⟨0,3⟩
  have hh := (h [] I 1 le_rfl (by norm_num [I])
    (x := 1) (by norm_num [I,ProfileCell.Contains])).1
  have hb := congrArg ProfileCell.lower hh
  norm_num [rejected,realize,containingCell,reply] at hb

def family : Registration arena (type_of% (@acquired_original_profile)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@acquired_original_profile,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@acquired_original_profile) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.acquired_original_profile.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.TwoReplyProfile.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => (acquireProfile (wordMatrix p.1.reverse) p.2.1 p.2.2).execute (attain p.1 x)) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.TwoReplyProfile
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.RationalRouting.TwoReplyProfile

