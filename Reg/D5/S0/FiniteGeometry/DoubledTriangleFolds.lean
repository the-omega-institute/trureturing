import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S0.FiniteGeometry.DoubledTriangleFolds

namespace Reg.D5.S0.FiniteGeometry.DoubledTriangleFolds

open _root_.D5.S0.FiniteGeometry.DoubledTriangleFolds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false

abbrev signature : Signature where
  Params := ℕ
  State := Coloring
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ C => foldCount C) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Observe the native fold count in the complete positive-size characterization. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (_ : 0 < n) (C : Coloring n),
    (Good C ∧ R.readout () n C = 3 * n) ↔
      ∃ front : Bool, (∀ t : Cell n, C (false, t) = front) ∧
        (∀ t : Cell n, C (true, t) = !front)

abbrev sourceScope := type_of% (@minimum_fold_uniqueness)

private theorem two_sided_at_one : foldCount (twoSided (n := 1) true) = 3 :=
  ((minimum_fold_uniqueness (by decide) (twoSided true)).mpr
    ⟨true, fun _ => rfl, fun _ => rfl⟩).2

private theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hd := h (n := 1) (by decide) (twoSided true)
  have he := (hd.mpr ⟨true, fun _ => rfl, fun _ => rfl⟩).2
  change (0 : ℕ) = 3 at he
  exact Nat.noConfusion he

noncomputable def family : Registration arena sourceScope where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@minimum_fold_uniqueness, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨1, twoSided true, fun _ => false, ?_⟩
    change foldCount (twoSided (n := 1) true) ≠ foldCount (n := 1) (fun _ => false)
    rw [two_sided_at_one]
    have hempty : folds (n := 1) (fun _ => false) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun _ _ h => h rfl)
    simp [foldCount, hempty]

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@minimum_fold_uniqueness) (Realization signature) Unit Unit where
  unitName := `D5.S0.FiniteGeometry.DoubledTriangleFolds.minimum_fold_uniqueness.__information_unit
  realizationName := `Reg.D5.S0.FiniteGeometry.DoubledTriangleFolds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ C => foldCount C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.FiniteGeometry.DoubledTriangleFolds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S0.FiniteGeometry.DoubledTriangleFolds
