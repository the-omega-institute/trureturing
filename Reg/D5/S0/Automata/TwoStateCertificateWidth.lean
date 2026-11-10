import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Automata.TwoStateCertificateWidth
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! The upper-bound readout is observed over the complete dependent theorem family. -/

namespace Reg.D5.S0.Automata.TwoStateCertificateWidth

open _root_.D5.S0.Automata.DFAOStateLowerBound
open _root_.D5.S0.Automata.FiniteSampleRestriction
open _root_.D5.S0.Automata.TwoStateCertificateWidth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (_hk : 6 ≤ k),
    (∀ (D : Finset (List (Fin k))) (t : {w // w ∈ D} → Bool),
      Realizable D (completeLabel D t) ↔
      ∃ (S : Type) (_ : Fintype S) (M : DFAO (Fin k) Bool S),
        Fintype.card S ≤ 2 ∧ CorrectOnFamily M Subtype.val t) ∧
    (∀ (D : Finset (List (Fin k))) (t : List (Fin k) → Bool),
      (Realizable D t → omega2 D t = ⊤ ∧
        ∀ E : Finset (List (Fin k)), E ⊆ D → Realizable E t) ∧
      (¬ Realizable D t → ∃ E : Finset (List (Fin k)), E ⊆ D ∧ ¬ Realizable E t ∧
        omega2 D t = (E.card : ℕ∞) ∧
        ∀ F : Finset (List (Fin k)), F ⊆ D → ¬ Realizable F t → E.card ≤ F.card)) ∧
    {w : List (Fin k) | w.length ≤ 2}.Finite ∧
    (obstructionRange k).Finite ∧ (obstructionRange k).Nonempty ∧
    ∃ h : ℕ, IsGreatest (obstructionRange k) h ∧ H2 k = (h : ℕ∞) ∧
      (k-2)/4 ≤ h ∧ h ≤ R.readout () () k

def actual : Realization signature :=
  realize signature (fun _ _ k => 16 * (k+1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem actual_bridge : (type_of% @two_state_certificate_width) ↔ arena.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨v, _, _, lower, upper⟩ := (h 6 (by decide)).2.2.2.2.2
  change v ≤ 0 at upper
  norm_num at lower
  omega

def registration : Registration arena (type_of% @two_state_certificate_width) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.mp two_state_certificate_width, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change (16 : ℕ) ≠ 32; decide⟩

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_state_certificate_width)
    (type_of% (realize signature (fun _ _ k => 16 * (k+1)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S0.Automata.TwoStateCertificateWidth.two_state_certificate_width "__information_unit",
  realizationName := `Reg.D5.S0.Automata.TwoStateCertificateWidth.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ k => 16 * (k+1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Automata.TwoStateCertificateWidth,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "body",
        "arg", "arg", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg", "fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration

end Reg.D5.S0.Automata.TwoStateCertificateWidth

namespace Reg.D5.S0.Automata.TwoStateCertificateWidth.RotateNe

open _root_.D5.S0.Automata.TwoStateCertificateWidth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

/-- Observe cyclic rotation on the theorem's full finite-index domain. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ Fin Fin

def actual : Realization signature :=
  realize signature (fun _ m i => finRotate m i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ i => i) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, 2 ≤ m → ∀ i : Fin m, R.readout () m i ≠ i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (m := 2) (by decide) 0 rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  change finRotate 2 0 ≠ finRotate 2 1
  exact fun h => (by decide : (0 : Fin 2) ≠ 1) ((finRotate 2).injective h)

def source_registration : Registration arena (type_of% @rotate_ne) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rotate_ne, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rotate_ne) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S0.Automata.TwoStateCertificateWidth.RotateNe.unit
  realizationName := `Reg.D5.S0.Automata.TwoStateCertificateWidth.RotateNe.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m i => finRotate m i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Automata.TwoStateCertificateWidth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S0.Automata.TwoStateCertificateWidth.RotateNe
