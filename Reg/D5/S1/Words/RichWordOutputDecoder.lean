import D5.S1.Words.RichWordOutputDecoder
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The complete marker-decoder telescope with its actual position readout. -/
open _root_.D5.S1.Words.RichWordOutputDecoder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.RichWordOutputDecoder.occurrence_decoder

abbrev signature : Signature where
  Params := List Input × List Output × List Output
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p A => Occ (decorated p.1 p.2.1 p.2.2) A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : List Input) (s t : List Output) (A : ℕ),
    (0 : Output) ∉ s → (0 : Output) ∉ t →
    (R.readout () (w,s,t) A ↔ ∃! j,
      A+s.length=E j ∧ _root_.D5.S1.Words.RichWordTypeIOccurrence.Occ w j ∧
        Left s j ∧ Right t w j)

private theorem marker_reads :
    Occ (decorated [] [] []) 0 ∧ ¬ Occ (decorated [] [] []) 2 := by
  have hge : ∀ j, j ≤ E j := by
    intro j
    induction j with
    | zero => simp [E]
    | succ j ih =>
      have hpos : ∀ c : Input, 0 < (eta c).length := by decide
      have := hpos (u j)
      simp only [E]
      omega
  constructor
  · apply (_root_.D5.S1.Words.RichWordOutputDecoder.occurrence_decoder
      [] [] [] 0 (by simp) (by simp)).mpr
    refine ⟨0, ?_, ?_⟩
    · simp [E, _root_.D5.S1.Words.RichWordTypeIOccurrence.Occ,
        _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Left, Right]
    · intro j hj
      have := hge j
      simp only [List.length_nil, Nat.add_zero] at hj
      omega
  · intro ho
    obtain ⟨j,hj,_⟩ := (_root_.D5.S1.Words.RichWordOutputDecoder.occurrence_decoder
      [] [] [] 2 (by simp) (by simp)).mp ho
    have he : E j = 2 := by simpa using hj.1.symm
    have hjlt : j < 3 := by have := hge j; omega
    have htable : ∀ i : Fin 3, E i.val ≠ 2 := by decide
    exact htable ⟨j,hjlt⟩ he

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ho := marker_reads.1
  have hr := (_root_.D5.S1.Words.RichWordOutputDecoder.occurrence_decoder
    [] [] [] 0 (by simp) (by simp)).mp ho
  exact (h [] [] [] 0 (by simp) (by simp)).mpr hr

def family : Registration arena
    (type_of% (@_root_.D5.S1.Words.RichWordOutputDecoder.occurrence_decoder)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.RichWordOutputDecoder.occurrence_decoder,
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨([],[],[]),0,2,?_⟩
    change Occ (decorated [] [] []) 0 ≠ Occ (decorated [] [] []) 2
    intro h
    exact marker_reads.2 (Eq.mp h marker_reads.1)

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.RichWordOutputDecoder.occurrence_decoder)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.RichWordOutputDecoder.occurrence_decoder.__information_unit,
  realizationName := `Reg.D5.S1.Words.RichWordOutputDecoder.occurrence_decoder.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.RichWordOutputDecoder, definition := none,
    coordinates := #[0,1,2],
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S1.Words.RichWordOutputDecoder.occurrence_decoder
