import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.LowDimensionalBorsukUlam
import Reg.Support.DependentFamily

/-! Source-bound audits of the Borsuk--Ulam theorem in dimensions at most two and of the
exclusion of continuous injections of open sets.

The antipodal coincidence `f x = f (-x)` is audited through the value of the map `f` at the
antipodal point `x`; the rejected reading `f x + f x` fails for a nonzero constant map into
`ℝ¹`. The non-injectivity is audited through the open set `U` on which injectivity fails; the
rejected reading `∅` fails because every map is injective on the empty set. -/

namespace Reg.D5.S3.Topology.LowDimensionalBorsukUlam

open _root_.D5.S3.Topology.LowDimensionalBorsukUlam
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-! The value `f x` in the conclusion `f x = f (-x)` of `exists_eq_neg_of_le_two`, against the
point `x` of the sphere. -/
namespace Antipodal

abbrev signature : Signature where
  Params := Σ d : ℕ, EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin d)
  State p := EuclideanSpace ℝ (Fin (p.1 + 1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := EuclideanSpace ℝ (Fin p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => p.2 s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p s => p.2 s + p.2 s) (fun e => nomatch e)

/-- Retain the complete dimension, map and continuity telescope of `exists_eq_neg_of_le_two`. -/
abbrev arena : Arena where
  signature := signature
  Law rd := ∀ {d : ℕ} (_ : d ≤ 2) (f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin d)),
    ContinuousOn f (Metric.sphere 0 1) →
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1,
      rd.readout () ⟨d, f⟩ x = f (-x)

/-- The unit vector of `ℝ¹`. -/
def unitLine : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

theorem unitLine_ne_zero : unitLine ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
  simp [unitLine] at h0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, -, hx⟩ := h (d := 1) (by norm_num) (fun _ => unitLine) continuousOn_const
  change unitLine + unitLine = unitLine at hx
  exact unitLine_ne_zero (by simpa using hx)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1, fun v => EuclideanSpace.single 0 (v 0)⟩, 0, EuclideanSpace.single 0 1, ?_⟩
  change EuclideanSpace.single (0 : Fin 1) ((0 : EuclideanSpace ℝ (Fin 2)) 0) ≠
    EuclideanSpace.single (0 : Fin 1) ((EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0)
  intro h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
  simp at h0

abbrev sourceStatement : Prop := type_of% @exists_eq_neg_of_le_two

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_eq_neg_of_le_two, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Antipodal

/-! The open set `U` in the conclusion `¬ Set.InjOn f U` of `not_injOn_of_lt`. -/
namespace OpenSet

abbrev signature : Signature where
  Params := ℕ
  State m := Set (EuclideanSpace ℝ (Fin m))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := Set (EuclideanSpace ℝ (Fin m))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

/-- Retain the complete dimension, set, map and continuity telescope of `not_injOn_of_lt`. -/
abbrev arena : Arena where
  signature := signature
  Law rd := ∀ {m d : ℕ}, d ≤ 2 → d < m → ∀ {U : Set (EuclideanSpace ℝ (Fin m))}, IsOpen U →
    U.Nonempty → ∀ (f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d)), ContinuousOn f U →
    ¬ Set.InjOn f (rd.readout () m U)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (m := 1) (d := 0) (by norm_num) (by norm_num) isOpen_univ Set.univ_nonempty
    (fun _ => 0) continuousOn_const (Set.injOn_empty _)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨0, ∅, Set.univ, ?_⟩
  change (∅ : Set (EuclideanSpace ℝ (Fin 0))) ≠ Set.univ
  exact Set.empty_ne_univ

abbrev sourceStatement : Prop := type_of% @not_injOn_of_lt

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@not_injOn_of_lt, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end OpenSet

def exists_eq_neg_of_le_two_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_eq_neg_of_le_two) (Realization Antipodal.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Topology.LowDimensionalBorsukUlam.exists_eq_neg_of_le_two_unit
  realizationName := `Reg.D5.S3.Topology.LowDimensionalBorsukUlam.Antipodal.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Antipodal.arena⟩
  objectArena := .source ⟨Antipodal.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Antipodal.arena ⟨Antipodal.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Antipodal.signature (fun _ p s => p.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.LowDimensionalBorsukUlam
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def not_injOn_of_lt_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@not_injOn_of_lt) (Realization OpenSet.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Topology.LowDimensionalBorsukUlam.not_injOn_of_lt_unit
  realizationName := `Reg.D5.S3.Topology.LowDimensionalBorsukUlam.OpenSet.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨OpenSet.arena⟩
  objectArena := .source ⟨OpenSet.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source OpenSet.arena ⟨OpenSet.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize OpenSet.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.LowDimensionalBorsukUlam
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Topology.LowDimensionalBorsukUlam
