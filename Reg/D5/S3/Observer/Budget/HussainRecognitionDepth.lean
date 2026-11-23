import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Observer.Budget.HussainRecognitionDepth

/-! The exact minimum depth as an observation of the length at each alphabet and language. -/

namespace Reg.D5.S3.Observer.Budget.HussainRecognitionDepth

open _root_.D5.S3.Observer.Budget.HussainRecognitionDepth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

abbrev Parameters := Σ Alphabet : Type u, Fintype Alphabet × Set (List Alphabet)

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Parameters.{u} (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p n => @recognitionDepth p.1 p.2.1 p.2.2 n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (Alphabet : Type u) [finite : Fintype Alphabet] (language : Set (List Alphabet)),
    2 ≤ Fintype.card Alphabet → SubwordClosed language →
    (HomExponents language).Finite → (HetExponents language).Finite →
    ∃ N d : Nat, 1 ≤ N ∧ ∀ n ≥ N, r.readout () ⟨Alphabet, finite, language⟩ n = d

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro bad
  have size : 2 ≤ Fintype.card (ULift.{u} Bool) := by simp
  have closed : SubwordClosed (∅ : Set (List (ULift.{u} Bool))) := by
    intro _ _ _ impossible
    exact impossible.elim
  have hom : HomExponents (∅ : Set (List (ULift.{u} Bool))) = ∅ := by
    ext e
    simp [HomExponents]
  have het : HetExponents (∅ : Set (List (ULift.{u} Bool))) = ∅ := by
    ext e
    simp [HetExponents]
  obtain ⟨N, d, _, stable⟩ := bad (ULift.{u} Bool) ∅ size closed
    (hom ▸ Set.finite_empty) (het ▸ Set.finite_empty)
  have first : N = d := stable N le_rfl
  have next : N + 1 = d := stable (N + 1) (Nat.le_succ _)
  omega

private def shortLanguage : Set (List (ULift.{u} Bool)) := {word | word.length ≤ 1}

private theorem depth_two_zero : recognitionDepth shortLanguage.{u} 2 = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  unfold recognitionDepth
  apply Nat.find_min'
  apply Or.inl
  constructor
  intro word
  have length : (List.ofFn word.val).length ≤ 1 := word.property
  simp at length

private theorem depth_one_ne_zero : recognitionDepth shortLanguage.{u} 1 ≠ 0 := by
  classical
  let left : Promise shortLanguage.{u} 1 := ⟨fun _ => ⟨false⟩, by simp [shortLanguage]⟩
  let right : Promise shortLanguage.{u} 1 := ⟨fun _ => ⟨true⟩, by simp [shortLanguage]⟩
  have distinct : left ≠ right := by
    intro equal
    exact Bool.false_ne_true (congrArg (fun word : Promise shortLanguage 1 =>
      (word.val 0).down) equal)
  have feasible : SourceExactAtDepth coordinateReadout (recognitionDepth shortLanguage.{u} 1) := by
    unfold recognitionDepth
    exact Nat.find_spec _
  intro zero
  rw [zero] at feasible
  rcases feasible with empty | ⟨tree, bound, covers, sound⟩
  · exact empty.false left
  · cases tree with
    | terminal label =>
        have identifies (state : Promise shortLanguage 1) : label = state :=
          sound state [] label (.terminal label) (by simp [Compatible])
        exact distinct ((identifies left).symm.trans (identifies right))
    | query coordinate letters present children =>
        obtain ⟨path, label, complete, _⟩ := covers left
        cases complete with
        | step answer tail =>
            exact Nat.not_succ_le_zero _ (bound (CompletePath.step answer tail))

def sourceRegistration : Registration arena.{u} claim.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    exact ⟨⟨ULift.{u} Bool, inferInstance, shortLanguage⟩, 1, 2,
      fun equal => depth_one_ne_zero (equal.trans depth_two_zero)⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Observer.Budget.HussainRecognitionDepth.unit
  realizationName := `Reg.D5.S3.Observer.Budget.HussainRecognitionDepth.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p n =>
    @recognitionDepth p.1 p.2.1 p.2.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Budget.HussainRecognitionDepth
    definition := some {
      owner := `D5.S3.Observer.Budget.HussainRecognitionDepth
      name := `D5.S3.Observer.Budget.HussainRecognitionDepth.claim
      path := #[] }
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Observer.Budget.HussainRecognitionDepth
