import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.WeightedIntegerRelations

/-! An audit of the character chord using the norm of the product difference. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace Reg.D5.S3.Fourier.WeightedIntegerRelations

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.WeightedIntegerRelations
open _root_.Reg.Support

universe u v

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

theorem norm_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0 : ℂ), 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  simp

def chordArena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} (columns : Finset J) (z q : J → Circle) (k : J → ℤ),
    R.readout () () (((∏ j ∈ columns, z j ^ k j : Circle) : ℂ) -
      ((∏ j ∈ columns, q j ^ k j : Circle) : ℂ)) ≤
      ∑ j ∈ columns, |(k j : ℝ)| * ‖(z j : ℂ) - (q j : ℂ)‖

private theorem chord_rejected : ¬ chordArena.{u}.Law rejected := by
  intro h
  have hbad := h (J := ULift.{u} Unit) ∅ (fun _ => 1) (fun _ => 1) (fun _ => 0)
  change (2 : ℝ) ≤ ∑ j ∈ (∅ : Finset (ULift.{u} Unit)),
    |((0 : ℤ) : ℝ)| * ‖((1 : Circle) : ℂ) - ((1 : Circle) : ℂ)‖ at hbad
  simp only [Finset.sum_empty] at hbad
  norm_num at hbad

def chordFamily : Registration chordArena.{u} (type_of% @chord_prod_zpow.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨chord_prod_zpow, rejected, chord_rejected⟩
  sensitivity := SingleDependentReadout.sensitivity chordArena.Law actual rejected chord_rejected
  dependence := norm_dependence

def chordAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@chord_prod_zpow.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Fourier.WeightedIntegerRelations.chord_prod_zpow.__information_unit
  realizationName := `Reg.D5.S3.Fourier.WeightedIntegerRelations.chordFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chordArena⟩
  objectArena := .source ⟨chordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chordArena ⟨chordFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedIntegerRelations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms chordAudit

def weightedChordArena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} {A : Type v} (columns : Finset J) (rows : Finset A)
    (z q : J → Circle) (w : J → ℝ) (k : A → J → ℤ) (lam : A → ℝ)
    (_hw : ∀ j ∈ columns, 0 < w j) (_hlam : ∀ a ∈ rows, 0 ≤ lam a),
    (∑ a ∈ rows, lam a *
      R.readout () () (((∏ j ∈ columns, z j ^ k a j : Circle) : ℂ) -
        ((∏ j ∈ columns, q j ^ k a j : Circle) : ℂ))) ^ 2 ≤
      (∑ j ∈ columns, (∑ a ∈ rows, lam a * |(k a j : ℝ)|) ^ 2 / w j) *
        ∑ j ∈ columns, w j * ‖(z j : ℂ) - (q j : ℂ)‖ ^ 2

private theorem weighted_chord_rejected : ¬ weightedChordArena.{u,v}.Law rejected := by
  intro h
  let columns : Finset (ULift.{u} Unit) := {⟨()⟩}
  let rows : Finset (ULift.{v} Unit) := {⟨()⟩}
  have hbad := h columns rows (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ _ => 0) (fun _ => 1) (by simp) (by simp)
  norm_num [columns, rows, rejected, realize, signature] at hbad

def weightedChordFamily : Registration weightedChordArena.{u,v} (type_of% @weighted_character_chord.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_character_chord, rejected, weighted_chord_rejected⟩
  sensitivity := SingleDependentReadout.sensitivity weightedChordArena.Law actual rejected
    weighted_chord_rejected
  dependence := norm_dependence

def multiplierArena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} {A : Type v} (columns : Finset J) (rows : Finset A)
    (gamma w : J → ℝ) (k : A → J → ℤ) (lam : A → ℝ)
    (_hw : ∀ j ∈ columns, 0 < w j) (_hlam : ∀ a ∈ rows, 0 ≤ lam a)
    (_hrel : ∀ a ∈ rows, ∑ j ∈ columns, (k a j : ℝ) * gamma j = 0),
    let W := ∑ j ∈ columns, w j
    let C := ∑ j ∈ columns, (∑ a ∈ rows, lam a * |(k a j : ℝ)|) ^ 2 / w j
    0 < C →
      let N := ∑ a ∈ rows, lam a * R.readout () () ((1 : ℂ) - Complex.I ^ (∑ j ∈ columns, k a j))
      N ^ 2 / (2 * W * C) ≤
        1 - sSup (Set.range (fun t : ℝ => ∑ j ∈ columns, w j * Real.sin (gamma j * t))) / W

private theorem multiplier_rejected : ¬ multiplierArena.{u,v}.Law rejected := by
  intro h
  let columns : Finset (ULift.{u} Unit) := {⟨()⟩}
  let rows : Finset (ULift.{v} Unit) := {⟨()⟩}
  have hbad := h columns rows (fun _ => 0) (fun _ => 1) (fun _ _ => 1)
    (fun _ => 1) (by simp) (by simp) (by simp)
    (by norm_num [columns, rows])
  norm_num [columns, rows, rejected, realize, signature, Set.range_const, csSup_singleton] at hbad

def multiplierFamily : Registration multiplierArena.{u,v} (type_of% @weighted_phase_deficit.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_phase_deficit, rejected, multiplier_rejected⟩
  sensitivity := SingleDependentReadout.sensitivity multiplierArena.Law actual rejected multiplier_rejected
  dependence := norm_dependence

def disjointArena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} {A : Type v} (columns : Finset J) (rows : Finset A)
    (gamma w : J → ℝ) (k : A → J → ℤ)
    (_hw : ∀ j ∈ columns, 0 < w j)
    (_hrel : ∀ a ∈ rows, ∑ j ∈ columns, (k a j : ℝ) * gamma j = 0)
    (_hrow : ∀ a ∈ rows, ∃ j ∈ columns, k a j ≠ 0)
    (_hdisj : ∀ a ∈ rows, ∀ b ∈ rows, a ≠ b →
      ∀ j ∈ columns, k a j = 0 ∨ k b j = 0),
    let W := ∑ j ∈ columns, w j
    0 < W →
      (1 / (2 * W)) * ∑ a ∈ rows,
        (R.readout () () ((1 : ℂ) - Complex.I ^ (∑ j ∈ columns, k a j))) ^ 2 /
          (∑ j ∈ columns, (k a j : ℝ) ^ 2 / w j) ≤
        1 - sSup (Set.range (fun t : ℝ => ∑ j ∈ columns, w j * Real.sin (gamma j * t))) / W

private theorem disjoint_rejected : ¬ disjointArena.{u,v}.Law rejected := by
  intro h
  let columns : Finset (ULift.{u} Unit) := {⟨()⟩}
  let rows : Finset (ULift.{v} Unit) := {⟨()⟩}
  have hbad := h columns rows (fun _ => 0) (fun _ => 1) (fun _ _ => 1)
    (by simp) (by simp) (by simp [columns])
    (fun a _ b _ hne => (hne (Subsingleton.elim a b)).elim) (by norm_num [columns])
  norm_num [columns, rows, rejected, realize, signature, Set.range_const, csSup_singleton] at hbad

def disjointFamily : Registration disjointArena.{u,v} (type_of% @weighted_phase_deficit_disjoint.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_phase_deficit_disjoint, rejected, disjoint_rejected⟩
  sensitivity := SingleDependentReadout.sensitivity disjointArena.Law actual rejected disjoint_rejected
  dependence := norm_dependence

def weightedChordAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@weighted_character_chord.{u,v}) (Realization signature) Type Unit where
  unitName := `D5.S3.Fourier.WeightedIntegerRelations.weighted_character_chord.__information_unit
  realizationName := `Reg.D5.S3.Fourier.WeightedIntegerRelations.weightedChordFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weightedChordArena⟩
  objectArena := .source ⟨weightedChordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightedChordArena ⟨weightedChordFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedIntegerRelations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def multiplierAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@weighted_phase_deficit.{u,v}) (Realization signature) Type Unit where
  unitName := `D5.S3.Fourier.WeightedIntegerRelations.weighted_phase_deficit.__information_unit
  realizationName := `Reg.D5.S3.Fourier.WeightedIntegerRelations.multiplierFamily
  realizationSource := none
  generated := false
  arena := .source ⟨multiplierArena⟩
  objectArena := .source ⟨multiplierArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source multiplierArena ⟨multiplierFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedIntegerRelations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def disjointAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@weighted_phase_deficit_disjoint.{u,v}) (Realization signature) Type Unit where
  unitName := `D5.S3.Fourier.WeightedIntegerRelations.weighted_phase_deficit_disjoint.__information_unit
  realizationName := `Reg.D5.S3.Fourier.WeightedIntegerRelations.disjointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨disjointArena⟩
  objectArena := .source ⟨disjointArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source disjointArena ⟨disjointFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedIntegerRelations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms weightedChordAudit
#print axioms multiplierAudit
#print axioms disjointAudit

end Reg.D5.S3.Fourier.WeightedIntegerRelations
