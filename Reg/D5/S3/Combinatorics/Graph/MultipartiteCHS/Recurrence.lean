import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
import Reg.Support.DependentFamily

/-! Source-family registrations for reciprocal coefficients and positivity. -/

namespace Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section

namespace Zero

abbrev signature : Signature where
  Params := Σ r : ℕ, Fin r → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r} (a : Fin r → ℕ), R.readout () ⟨r, a⟩ 0 = 1

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h (r := 0) Fin.elim0
  norm_num [arena, rejected, realize] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Fin.elim0⟩, 0, 1, ?_⟩
  change recH (r := 0) Fin.elim0 0 ≠ recH (r := 0) Fin.elim0 1
  rw [recH_zero, recH_eq _ (show 1 ≤ (1 : ℕ) by decide)]
  norm_num

def source : Registration arena (type_of% @recH_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recH_zero, rejected, rejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_not_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@recH_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.Zero.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.Zero.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Zero

namespace Equation

abbrev signature : Signature where
  Params := Σ r : ℕ, Fin r → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r} (a : Fin r → ℕ) {d : ℕ}, 1 ≤ d →
    R.readout () ⟨r, a⟩ d = ∑ j ∈ Finset.Icc 2 d,
      ((j : ℝ) - 1) * (esymmParts a j : ℝ) * recH a (d - j)

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h (r := 0) Fin.elim0 (d := 1) (by decide)
  norm_num [arena, rejected, realize] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Fin.elim0⟩, 0, 1, ?_⟩
  change recH (r := 0) Fin.elim0 0 ≠ recH (r := 0) Fin.elim0 1
  rw [recH_zero, recH_eq _ (show 1 ≤ (1 : ℕ) by decide)]
  norm_num

def source : Registration arena (type_of% @recH_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recH_eq, rejected, rejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_not_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@recH_eq) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.Equation.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.Equation.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Equation

namespace Nonnegative

abbrev signature : Signature where
  Params := Σ r : ℕ, Fin r → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r} (a : Fin r → ℕ), ∀ d, 0 ≤ R.readout () ⟨r, a⟩ d

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h (r := 0) Fin.elim0 0
  norm_num [arena, rejected, realize] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Fin.elim0⟩, 0, 1, ?_⟩
  change recH (r := 0) Fin.elim0 0 ≠ recH (r := 0) Fin.elim0 1
  rw [recH_zero, recH_eq _ (show 1 ≤ (1 : ℕ) by decide)]
  norm_num

def source : Registration arena (type_of% @recH_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recH_nonneg, rejected, rejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_not_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@recH_nonneg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.Nonnegative.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.Nonnegative.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Nonnegative

namespace ElementaryPositive

abbrev signature : Signature where
  Params := Σ r : ℕ, Fin r → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d => (esymmParts p.2 d : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r} (_hr : 2 ≤ r) (a : Fin r → ℕ),
    (∀ i, 0 < a i) → 0 < R.readout () ⟨r, a⟩ 2

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h (r := 2) (by decide) (fun _ => 1) (by intro i; decide)
  norm_num [arena, rejected, realize] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Fin.elim0⟩, 0, 1, ?_⟩
  have hp : (∅ : Finset (Fin 0)).powersetCard 1 = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simp)
  norm_num [actual, realize, esymmParts, hp]

def source : Registration arena (type_of% @esymmParts_two_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@esymmParts_two_pos, rejected, rejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_not_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@esymmParts_two_pos) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.ElementaryPositive.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.ElementaryPositive.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => (esymmParts p.2 d : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ElementaryPositive

namespace EvenPositive

abbrev signature : Signature where
  Params := Σ r : ℕ, Fin r → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r m} (_hr : 2 ≤ r) (a : Fin r → ℕ),
    (∀ i, 0 < a i) → 1 ≤ m → 0 < R.readout () ⟨r, a⟩ (2 * m)

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h (r := 2) (m := 1) (by decide) (fun _ => 1)
    (by intro i; decide) (by decide)
  norm_num [arena, rejected, realize] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Fin.elim0⟩, 0, 1, ?_⟩
  change recH (r := 0) Fin.elim0 0 ≠ recH (r := 0) Fin.elim0 1
  rw [recH_zero, recH_eq _ (show 1 ≤ (1 : ℕ) by decide)]
  norm_num

def source : Registration arena (type_of% @recH_two_mul_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recH_two_mul_pos, rejected, rejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_not_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@recH_two_mul_pos) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.EvenPositive.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence.EvenPositive.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EvenPositive

end
end Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
