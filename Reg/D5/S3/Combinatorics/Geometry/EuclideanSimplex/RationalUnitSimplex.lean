import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex
import Mathlib.Data.Nat.Sqrt

/-! The successor dimension in the even-dimensional simplex criterion. -/

namespace Reg.D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex (rational_unit_simplex_iff)
open LeanInformationAudit

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => n + 1) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_ : 0 < n),
    (∃ c : ℚ, c ≠ 1 ∧ ∃ p : Fin (n+1) → Fin n → ℚ, ∀ j k,
      p j ⬝ᵥ p k = if j = k then 1 else c) ↔
    (Odd n ∧ IsSquare n) ∨ (Even n ∧ IsSquare (R.readout () () n))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have existsTriangle := (h 2 (by decide)).mpr (Or.inr ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩)
  rcases (rational_unit_simplex_iff 2 (by decide)).mp existsTriangle with ho | hs
  · exact (by decide : ¬ Odd 2) ho.1
  · obtain ⟨m, hm⟩ := hs.2
    have hlt : m < 2 := by
      by_contra! hge
      nlinarith
    interval_cases m <;> norm_num at hm

def family : Registration arena (type_of% @rational_unit_simplex_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_unit_simplex_iff, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 1, 2, by decide⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rational_unit_simplex_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex.unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n + 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex
