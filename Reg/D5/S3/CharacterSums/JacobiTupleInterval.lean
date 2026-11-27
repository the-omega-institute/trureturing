import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.JacobiTupleInterval
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset
open _root_.D5.S3.CharacterSums.JacobiTupleInterval
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.JacobiTupleInterval

namespace Tuple

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ L => (L : ℝ)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {k : ℕ} (P : Finset ℕ) (f : Fin k → ℕ) (_ : ∀ j, f j ∈ P)
    (_ : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (b m A L : ℕ) (_ : b%4=3) (_ : 4 ∣ m),
    let Q := ∏ p ∈ P, p
    |block (row f b m) A L - V.readout () () L * (block (row f b m) 0 Q / Q)| ≤
      2 * (∏ j, (f j : ℝ))

private theorem reject_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h (k := 0) ∅ Fin.elim0 (fun j => j.elim0) (by simp) 3 4 0 3 (by decide) (by decide)
  norm_num [rejected, realize, block, row] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @tuple_interval_mean) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tuple_interval_mean, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tuple_interval_mean) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.JacobiTupleInterval.tuple_interval_mean
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.JacobiTupleInterval.Tuple "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ L => (L : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.JacobiTupleInterval
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Tuple

namespace Moment

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ ell => ell) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime ∧ p≠2)
    (b m A ell : ℕ) (_ : b%4=3) (_ : 4∣m) (_ : ∀ p ∈ P, m.Coprime p) (a : P → ℝ),
    letI : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hp p p.2).1.ne_zero⟩
    (∑ i ∈ range (∏ p ∈ P,p), (∑ p : P, a p * (jacobiSym (p:ℤ) (b+m*(A+i)) : ℝ))^(V.readout () () ell)) =
      ∑ z : ((p : P) → ZMod (p:ℕ)), (∑ p : P, a p * coordinate (hp p p.2).1 (z p))^ell

private theorem reject_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h ∅ (by simp) 3 4 0 0 (by decide) (by decide) (by simp) (fun _ => 0)
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual,realize]

def family : Registration arena (type_of% @affine_complete_crt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@affine_complete_crt, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@affine_complete_crt) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.JacobiTupleInterval.affine_complete_crt
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.JacobiTupleInterval.Moment "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ ell => ell) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.JacobiTupleInterval
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Moment

namespace Coordinate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun p => ZMod p) (fun p => ZMod p)

def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (p : ℕ) (hp : p.Prime) (_ : p ≠ 2),
    letI : NeZero p := ⟨hp.ne_zero⟩
    (∀ z : ZMod p, coordinate hp z = -1 ∨ coordinate hp z = 0 ∨ coordinate hp z = 1) ∧
      ∑ z : ZMod p, coordinate hp (V.readout () p z) = 0

private theorem reject_fails : ¬ arena.Law rejected := by
  intro h
  have hh := (h 3 (by decide) (by decide)).2
  norm_num [rejected,realize,coordinate,Finset.sum_const,ZMod.card] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨3, 0, 1, ?_⟩
  change (0 : ZMod 3) ≠ 1
  decide

def family : Registration arena (type_of% @coordinate_laws) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coordinate_laws, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coordinate_laws) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.JacobiTupleInterval.coordinate_laws
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.JacobiTupleInterval.Coordinate "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.JacobiTupleInterval
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Coordinate

end Reg.D5.S3.CharacterSums.JacobiTupleInterval
