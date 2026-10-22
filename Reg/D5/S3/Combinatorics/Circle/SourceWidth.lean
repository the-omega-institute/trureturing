import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.SourceWidth
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.SourceWidth

/-- Every residue is a state. The output retains every physical label. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin k → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 3 ≤ k → ∀ t : ℕ,
    ∃ word : List (Fin k), word.Nodup ∧ word.toFinset = Finset.univ ∧
      ∀ n : ℕ, n ≤ k →
        ((word.take n).map (R.readout () k t)).sum ∈ Set.Icc (0 : ℤ) (capacity k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨word, hnodup, hcomplete, hheight⟩ := h 3 (by decide) 0
  have hmem : (0 : Fin 3) ∈ word := List.mem_toFinset.mp (by rw [hcomplete]; simp)
  cases word with
  | nil => simp at hmem
  | cons x xs =>
    have hh := hheight 1 (by decide)
    change ([-1] : List ℤ).sum ∈ Set.Icc (0 : ℤ) (capacity 3) at hh
    norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 3)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def source_registration : Registration arena (type_of% (@universal_source_width)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨universal_source_width, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.SourceWidth.universal_source_width)
    (type_of% (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.SourceWidth.universal_source_width.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.SourceWidth.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.SourceWidth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration

namespace GeometricRelocation

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
  State p := Fin (p.1 * p.2.1 + p.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p => actualSource (p.1 * p.2.1 + p.2.2)
    (((2 ^ p.2.1) ^ p.1 - 1) / (2 ^ p.2.1 - 1))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r m d : ℕ) (_hr : 1 ≤ r) (_hm : 1 ≤ m) (_hd : 1 ≤ d),
    let B : ℕ := 2 ^ m
    let k : ℕ := r * m + d
    let t : ℕ := (B ^ r - 1) / (B - 1)
    let A : ℤ := 2 ^ (d - 1)
    let C : ℤ := (2 : ℤ) ^ (k - 1) - 1
    let W : ℤ := C - min (A - 1) (((t : ℤ) - 1) / 2)
    let f : Fin k → ℤ := R.readout () ⟨r, ⟨m, d⟩⟩
    let word : List (Fin k) :=
      (((List.finRange k).take (k - 1)).rotate (d - 1)) ++
        (List.finRange k).drop (k - 1)
    word.Perm (List.finRange k) ∧
      W ≤ C ∧
      (∀ n : ℕ, ((word.take n).map f).sum ∈ Set.Icc (0 : ℤ) W) ∧
      (word.map f).sum = 0 ∧
      (∃ n : ℕ, n ≤ k ∧ ((word.take n).map f).sum = W)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := (h 1 1 1 (by decide) (by decide) (by decide)).2.2.1 1
  norm_num [rejected, realize] at hp

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, ⟨1, 1⟩⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩
  norm_num [actual, realize, actualSource, centered, modulus]

def source_registration : Registration arena (type_of% (@geometric_source_relocation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨geometric_source_relocation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.SourceWidth.geometric_source_relocation)
    (type_of% (realize signature (fun _ p => actualSource (p.1 * p.2.1 + p.2.2)
      (((2 ^ p.2.1) ^ p.1 - 1) / (2 ^ p.2.1 - 1))) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.SourceWidth.geometric_source_relocation.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.SourceWidth.GeometricRelocation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => actualSource (p.1 * p.2.1 + p.2.2)
    (((2 ^ p.2.1) ^ p.1 - 1) / (2 ^ p.2.1 - 1))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.SourceWidth
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


#print axioms source_registration

end GeometricRelocation

end Reg.D5.S3.Combinatorics.Circle.SourceWidth
