import D5.S3.Geometry.FiniteGeometry.AffineBlockingBound
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

namespace Reg.D5.S3.Geometry.FiniteGeometry.AffineBlockingBound

open _root_.D5.S3.Geometry.FiniteGeometry.AffinePlaneLines
open _root_.D5.S3.Geometry.FiniteGeometry.AffineBlockingBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u
noncomputable section

abbrev signature : Signature where
  Params := Type u
  State F := Finset (F × F)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ B => B.card) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The original field telescope and all-line incidence are preserved.
Only the cardinality of the proposed blocking set is observed differently. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {F : Type u} [Field F] [Fintype F],
    IsLeast {n : ℕ | ∃ B : Finset (F × F),
      (∀ ℓ : AffineLine F, ∃ p ∈ B, p ∈ ℓ) ∧ R.readout () F B = n}
      (2 * Fintype.card F - 1)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let F := ULift.{u} (ZMod 2)
  obtain ⟨B, _, hcard⟩ := (h (F := F)).1
  have hq : Fintype.card F = 2 := by simp [F]
  change 0 = 2 * Fintype.card F - 1 at hcard
  rw [hq] at hcard
  omega

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨affine_blocking_minimum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨ULift.{u} (ZMod 2), ∅, {(0, 0)}, ?_⟩
    simp [actual, realize]

register_information_theorem affine_blocking_minimum in arena
  readout via (realize signature.{u} (fun _ _ B => B.card) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.FiniteGeometry.AffineBlockingBound
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg",
        "body", "arg", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Geometry.FiniteGeometry.AffineBlockingBound
