import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.InversionSeq.ClassCInsertion
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.InversionSeq ClassCSites ClassCPaths ClassCInsertion

namespace Reg.D5.S3.Combinatorics.InversionSeq.ClassCInsertion

private theorem phi_one (q : State) : phi 1 q = q.p.length + q.s := by
  classical
  simp [phi, Path, Nat.card_sigma, Nat.card_eq_fintype_card,
    Fintype.card_sum, Fintype.card_fin]

namespace empty_difference

abbrev signature : Signature where
  Params := {s : ℕ // 1 ≤ s}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ s r => b r s.val s.property) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law x := ∀ s : {s : ℕ // 1 ≤ s}, ∀ r : ℕ,
    phi r (lowerState 0 s.val s.property) ≤ x.readout () s r ∧
      x.readout () s r - phi r (lowerState 0 s.val s.property) =
        Nat.card (RepeatComplement r s.val s.property)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := (h ⟨1, by omega⟩ 0).1
  simp [phi, Path, rejected, realize] at hx

noncomputable def registration : Registration arena
    (∀ r s : ℕ, ∀ hs : 1 ≤ s,
      phi r (lowerState 0 s hs) ≤ b r s hs ∧
        b r s hs - phi r (lowerState 0 s hs) = Nat.card (RepeatComplement r s hs)) where
  actual := actual
  bridge := by
    constructor
    · intro h s r; exact h r s.val s.property
    · intro h r s hs; exact h ⟨s, hs⟩ r
  variation := ⟨by
    intro s r
    exact _root_.D5.S3.Combinatorics.InversionSeq.ClassCInsertion.empty_difference r s.val s.property,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro ⟨⟩
    refine ⟨⟨1, by omega⟩, 0, 1, ?_⟩
    change b 0 1 (by omega) ≠ b 1 1 (by omega)
    simp [b, phi_one, repeatState, phi, Path]

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.InversionSeq.ClassCInsertion.empty_difference)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCInsertion.empty_difference.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCInsertion.empty_difference.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end empty_difference

namespace unused_difference

abbrev signature : Signature where
  Params := {s : ℕ // 1 ≤ s} × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ sk r => phi r (lowerState (sk.2 + 1) sk.1.val sk.1.property))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law x := ∀ sk : {s : ℕ // 1 ≤ s} × ℕ, ∀ r : ℕ,
    phi r (lowerState sk.2 sk.1.val sk.1.property) ≤ x.readout () sk r ∧
      x.readout () sk r - phi r (lowerState sk.2 sk.1.val sk.1.property) =
        Nat.card (LowerComplement r sk.1.val sk.2 sk.1.property)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := (h (⟨1, by omega⟩, 0) 0).1
  simp [phi, Path, rejected, realize] at hx

noncomputable def registration : Registration arena
    (∀ r s k : ℕ, ∀ hs : 1 ≤ s,
      phi r (lowerState k s hs) ≤ phi r (lowerState (k + 1) s hs) ∧
        phi r (lowerState (k + 1) s hs) - phi r (lowerState k s hs) =
          Nat.card (LowerComplement r s k hs)) where
  actual := actual
  bridge := by
    constructor
    · intro h sk r; exact h r sk.1.val sk.2 sk.1.property
    · intro h r s k hs; exact h (⟨s, hs⟩, k) r
  variation := ⟨by
    intro sk r
    exact _root_.D5.S3.Combinatorics.InversionSeq.ClassCInsertion.unused_difference
      r sk.1.val sk.2 sk.1.property,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro ⟨⟩
    refine ⟨(⟨1, by omega⟩, 0), 0, 1, ?_⟩
    change phi 0 (lowerState 1 1 (by omega)) ≠ phi 1 (lowerState 1 1 (by omega))
    simp [phi_one, lowerState, phi, Path]

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.InversionSeq.ClassCInsertion.unused_difference)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCInsertion.unused_difference.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCInsertion.unused_difference.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end unused_difference

end Reg.D5.S3.Combinatorics.InversionSeq.ClassCInsertion
