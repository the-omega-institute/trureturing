import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
import Reg.Support.DependentFamily

/-! Full-telescope audit of the physical rotational stabilizer. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer

open scoped BigOperators
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Sigma (fun _ : ℕ => ℕ)
  State p := Finset (Fin (3 * (18 * p.1 + 12)))
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role p A => if !role then
    ∑ i ∈ A.image ((finRotate (3 * (18 * p.1 + 12)) : Equiv.Perm (Fin (3 * (18 * p.1 + 12)))) ^ p.2),
      actualSource (3 * (18 * p.1 + 12))
        ((2 ^ (18 * p.1 + 12) - 1) * (2 ^ (18 * p.1 + 12 + 1) - 3)) i
    else ∑ i ∈ A,
      actualSource (3 * (18 * p.1 + 12))
        ((2 ^ (18 * p.1 + 12) - 1) * (2 ^ (18 * p.1 + 12 + 1) - 3)) i)
    (fun e => nomatch e)

def rejected (role : Bool) : Realization signature :=
  realize signature (fun j p A => if j = role then 1 else actual.readout j p A)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r a : ℕ), let d := 18 * r + 12
    (∀ A : Finset (Fin (3 * d)),
      R.readout false (⟨r, a⟩ : signature.Params) A = 0 ↔ R.readout true (⟨r, a⟩ : signature.Params) A = 0) ↔
      (3 * d) ∣ a

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro hall
  have hp := (hall 0 0).mpr (by simp)
  have he := hp ∅
  cases role <;> norm_num [rejected, actual, realize] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(⟨0, 0⟩ : signature.Params), ∅, {⟨0, by decide⟩}, ?_⟩
  cases i <;> simp [actual, realize] <;> norm_num [actualSource, centered, modulus]

def family : Registration arena (type_of% (@actual_zero_family_rotation_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zero_family_rotation_iff, rejected true, rejected_law true⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      simp only [rejected, realize, ite_eq_right hji]
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_zero_family_rotation_iff) (Realization signature) Nat Bool where
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer.actual_zero_family_rotation_iff
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun role p A => if !role then
    ∑ i ∈ A.image ((finRotate (3 * (18 * p.1 + 12)) : Equiv.Perm (Fin (3 * (18 * p.1 + 12)))) ^ p.2),
      actualSource (3 * (18 * p.1 + 12))
        ((2 ^ (18 * p.1 + 12) - 1) * (2 ^ (18 * p.1 + 12 + 1) - 3)) i
    else ∑ i ∈ A,
      actualSource (3 * (18 * p.1 + 12))
        ((2 ^ (18 * p.1 + 12) - 1) * (2 ^ (18 * p.1 + 12 + 1) - 3)) i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
