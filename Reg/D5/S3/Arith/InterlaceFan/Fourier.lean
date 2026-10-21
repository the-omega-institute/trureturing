import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.InterlaceFan.Fourier
import Reg.Support.DependentFamily

/-! Source realizations of the interlace Fourier statements. -/

namespace Reg.D5.S3.Arith.InterlaceFan.Fourier
open _root_.D5.S3.Arith.InterlaceFan.Defs
open _root_.D5.S3.Arith.InterlaceFan.Fourier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset
noncomputable section

abbrev valueSignature : Signature where
  Params := Σ n : ℕ, Fin (n / 2) → ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def valueActual : Realization valueSignature :=
  realize valueSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e)

def valueZero : Realization valueSignature :=
  realize valueSignature (fun _ _ _ => 0) (fun e => nomatch e)

def valueOne : Realization valueSignature :=
  realize valueSignature (fun _ _ _ => 1) (fun e => nomatch e)

private lemma valueDependence : ObservationalDependence valueSignature valueActual := by
  intro i
  refine ⟨⟨2, fun _ => 1⟩, 0, 1, ?_⟩
  norm_num [valueActual, realize, I, Fin.sum_univ_succ]

abbrev constantArena : Arena where
  signature := valueSignature
  Law R := ∀ (n : ℕ), 2 ≤ n → ∀ (x : Fin (n / 2) → ℝ) (c : ℝ),
    (∀ j ∈ certIdx n, R.readout () ⟨n, x⟩ j = c) → x = 0

private lemma constantRejected : ¬ constantArena.Law valueZero := by
  intro h
  have he := h 2 (by omega) (fun _ => 1) 0 (by intro j hj; rfl)
  have hz := congrFun he 0
  norm_num at hz

abbrev meanArena : Arena where
  signature := valueSignature
  Law R := ∀ (n : ℕ), 2 ≤ n → ∀ (x : Fin (n / 2) → ℝ),
    ∑ j ∈ certIdx n, certWeight n j * R.readout () ⟨n, x⟩ j = 0

private lemma meanRejected : ¬ meanArena.Law valueOne := by
  intro h
  have he := h 2 (by omega) (fun _ => 0)
  norm_num [valueOne, realize, certIdx, certWeight, sum_range_succ] at he

abbrev valuesArena : Arena where
  signature := valueSignature
  Law R := ∀ (n : ℕ), 2 ≤ n → ∀ (y : ℕ → ℝ),
    (∑ j ∈ certIdx n, certWeight n j * y j = 0) →
    ∃ x : Fin (n / 2) → ℝ, ∀ j ∈ certIdx n, R.readout () ⟨n, x⟩ j = y j

private lemma valuesRejected : ¬ valuesArena.Law valueZero := by
  intro h
  obtain ⟨x, hx⟩ := h 2 (by omega) (fun j => if j = 0 then -1 else 1)
    (by norm_num [certIdx, certWeight, sum_range_succ])
  have he := hx 0 (by simp [certIdx])
  norm_num [valueZero, realize] at he

def constantSource : Registration constantArena (type_of% @eq_zero_of_I_const) where
  actual := valueActual
  bridge := Iff.rfl
  variation := ⟨eq_zero_of_I_const, valueZero, constantRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨valueZero, ?_, rfl, constantRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := valueDependence

def constantAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eq_zero_of_I_const) (Realization valueSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.constantUnit
  realizationName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.constantSource
  realizationSource := none
  generated := false
  arena := .source ⟨constantArena⟩
  objectArena := .source ⟨constantArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source constantArena ⟨constantSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize valueSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.InterlaceFan.Fourier
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def meanSource : Registration meanArena (type_of% @I_weighted_sum) where
  actual := valueActual
  bridge := Iff.rfl
  variation := ⟨I_weighted_sum, valueOne, meanRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨valueOne, ?_, rfl, meanRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := valueDependence

def meanAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@I_weighted_sum) (Realization valueSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.meanUnit
  realizationName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.meanSource
  realizationSource := none
  generated := false
  arena := .source ⟨meanArena⟩
  objectArena := .source ⟨meanArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source meanArena ⟨meanSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize valueSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.InterlaceFan.Fourier
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def valuesSource : Registration valuesArena (type_of% @exists_of_I_values) where
  actual := valueActual
  bridge := Iff.rfl
  variation := ⟨exists_of_I_values, valueZero, valuesRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨valueZero, ?_, rfl, valuesRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := valueDependence

def valuesAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_of_I_values) (Realization valueSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.valuesUnit
  realizationName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.valuesSource
  realizationSource := none
  generated := false
  arena := .source ⟨valuesArena⟩
  objectArena := .source ⟨valuesArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source valuesArena ⟨valuesSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize valueSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.InterlaceFan.Fourier
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev faceSignature : Signature where
  Params := ℕ
  State _ := Finset ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Set (Fin (n / 2) → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def faceActual : Realization faceSignature :=
  realize faceSignature (fun _ n S => face n S) (fun e => nomatch e)

def faceBadLeft : Realization faceSignature :=
  realize faceSignature (fun i n S => if i then face n S else Set.univ) (fun e => nomatch e)

def faceBadRight : Realization faceSignature :=
  realize faceSignature (fun i n S => if i then ∅ else face n S) (fun e => nomatch e)

abbrev faceArena : Arena where
  signature := faceSignature
  Law R := ∀ (n : ℕ) {S T : Finset ℕ}, S ⊆ T →
    R.readout false n T ⊆ R.readout true n S

private lemma faceBadLeftRejected : ¬ faceArena.Law faceBadLeft := by
  intro h
  have he := @h 2 {0} {0} Subset.rfl (fun _ => 1) (by trivial)
  have hi := he 0 (by simp) 1 (by simp [certIdx])
  norm_num [I, Fin.sum_univ_succ] at hi

private lemma faceBadRightRejected : ¬ faceArena.Law faceBadRight := by
  intro h
  have he := @h 2 ∅ ∅ Subset.rfl 0 (by simp [faceBadRight, realize, face])
  exact he

private lemma faceDependence : ObservationalDependence faceSignature faceActual := by
  intro i
  refine ⟨2, ∅, {0}, ?_⟩
  intro he
  have hx : (fun _ : Fin (2 / 2) => (1 : ℝ)) ∈ face 2 {0} := by
    rw [← show face 2 ∅ = face 2 {0} from he]
    simp [face]
  have hi := hx 0 (by simp) 1 (by simp [certIdx])
  norm_num [I, Fin.sum_univ_succ] at hi

def faceSource : Registration faceArena (type_of% @face_antitone) where
  actual := faceActual
  bridge := Iff.rfl
  variation := ⟨face_antitone, faceBadRight, faceBadRightRejected⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      · refine ⟨faceBadLeft, ?_, rfl, faceBadLeftRejected⟩
        intro j hj
        cases j
        · exact (hj rfl).elim
        · rfl
      · refine ⟨faceBadRight, ?_, rfl, faceBadRightRejected⟩
        intro j hj
        cases j
        · rfl
        · exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := faceDependence

def faceAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@face_antitone) (Realization faceSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.faceUnit
  realizationName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.faceSource
  realizationSource := none
  generated := false
  arena := .source ⟨faceArena⟩
  objectArena := .source ⟨faceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source faceArena ⟨faceSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize faceSignature (fun _ n S => face n S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.InterlaceFan.Fourier
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev exactSignature : Signature where
  Params := Σ n : ℕ, Fin (n / 2) → ℝ
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def exactActual : Realization exactSignature :=
  realize exactSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e)

def exactBadFirst : Realization exactSignature :=
  realize exactSignature (fun i p j => if i then I p.1 j p.2 else 0) (fun e => nomatch e)

def exactBadSecond : Realization exactSignature :=
  realize exactSignature (fun i p j =>
    if i then interlaceNumber p.1 p.2 else I p.1 j p.2) (fun e => nomatch e)

abbrev exactArena : Arena where
  signature := exactSignature
  Law R := ∀ (n : ℕ), 2 ≤ n → ∀ (S : Finset ℕ), S ⊆ certIdx n →
    S.Nonempty → S ≠ certIdx n →
    ∃ x ∈ face n S, x ≠ 0 ∧
      (∀ j ∈ certIdx n, R.readout false ⟨n, x⟩ j = interlaceNumber n x ↔ j ∈ S) ∧
      (∀ j ∈ certIdx n \ S, R.readout true ⟨n, x⟩ j < interlaceNumber n x)

private lemma exactBadFirstRejected : ¬ exactArena.Law exactBadFirst := by
  intro h
  obtain ⟨x, hxf, hx0, hx, hlt⟩ := h 2 (by omega) {0}
    (by simp [certIdx]) (by simp) (by decide)
  have h0 := (hx 0 (by simp [certIdx])).mpr (by simp)
  have h1 := (hx 1 (by simp [certIdx])).mp
  simp only [exactBadFirst, realize, Bool.false_eq_true, ite_false] at h0 h1
  have he := h1 h0
  norm_num at he

private lemma exactBadSecondRejected : ¬ exactArena.Law exactBadSecond := by
  intro h
  obtain ⟨x, hxf, hx0, hx, hlt⟩ := h 2 (by omega) {0}
    (by simp [certIdx]) (by simp) (by decide)
  have he := hlt 1 (by simp [certIdx])
  simpa [exactBadSecond, realize] using he

private lemma exactDependence : ObservationalDependence exactSignature exactActual := by
  intro i
  refine ⟨⟨2, fun _ => 1⟩, 0, 1, ?_⟩
  norm_num [exactActual, realize, I, Fin.sum_univ_succ]

def exactSource : Registration exactArena (type_of% @exists_face_exact) where
  actual := exactActual
  bridge := Iff.rfl
  variation := ⟨exists_face_exact, exactBadFirst, exactBadFirstRejected⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      · refine ⟨exactBadFirst, ?_, rfl, exactBadFirstRejected⟩
        intro j hj
        cases j
        · exact (hj rfl).elim
        · rfl
      · refine ⟨exactBadSecond, ?_, rfl, exactBadSecondRejected⟩
        intro j hj
        cases j
        · rfl
        · exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := exactDependence

def exactAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_face_exact) (Realization exactSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.exactUnit
  realizationName := `Reg.D5.S3.Arith.InterlaceFan.Fourier.exactSource
  realizationSource := none
  generated := false
  arena := .source ⟨exactArena⟩
  objectArena := .source ⟨exactArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exactArena ⟨exactSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize exactSignature (fun _ p j => I p.1 j p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.InterlaceFan.Fourier
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "arg", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.InterlaceFan.Fourier
