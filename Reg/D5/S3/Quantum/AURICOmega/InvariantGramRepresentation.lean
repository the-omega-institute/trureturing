import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.InvariantGramRepresentation
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Source-bound audit of the orthogonal representation of an invariant Gram kernel.

The kernel clause `ρ g = 1 ↔ ∀ x, φ (g * x) = φ x` is audited through the value `φ (g * x)` of
the family on its stabilizer side. The rejected reading `0` fails on the sign family `u ↦ u • e`
of the group of units `{1, -1}` of the integers in a Euclidean line: there `ρ 1 = 1`, while the
family does not vanish at `1`. -/

namespace Reg.D5.S3.Quantum.AURICOmega.InvariantGramRepresentation

open _root_.D5.S3.Quantum.AURICOmega.InvariantGramRepresentation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v

/-- The one-dimensional Euclidean line in universe `v`. -/
abbrev Line : Type v := EuclideanSpace ℝ (ULift.{v} Unit)

/-- The unit vector of the line. -/
def unitVector : Line.{v} := EuclideanSpace.single ⟨()⟩ 1

theorem unitVector_ne_zero : unitVector.{v} ≠ 0 := by
  intro h
  have hn := congrArg norm h
  rw [unitVector, PiLp.norm_single, norm_zero] at hn
  norm_num at hn

/-- The group of units `{1, -1}` of the integers, in universe `u`. -/
abbrev Sign : Type u := ULift.{u} ℤˣ

/-- The sign family `u ↦ u • e` on the line. -/
def signFamily (g : Sign.{u}) : Line.{v} := (((g.down : ℤˣ) : ℤ) : ℝ) • unitVector.{v}

theorem signFamily_mul (g x : Sign.{u}) :
    signFamily.{u, v} (g * x) = (((g.down : ℤˣ) : ℤ) : ℝ) • signFamily.{u, v} x := by
  simp only [signFamily, smul_smul]
  congr 1
  change (((g.down * x.down : ℤˣ) : ℤ) : ℝ) = _
  push_cast
  ring

theorem sign_mul_self (g : Sign.{u}) : (((g.down : ℤˣ) : ℤ) : ℝ) * (((g.down : ℤˣ) : ℤ) : ℝ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem signFamily_gram (g x y : Sign.{u}) :
    ⟪signFamily.{u, v} (g * x), signFamily.{u, v} (g * y)⟫_ℝ =
      ⟪signFamily.{u, v} x, signFamily.{u, v} y⟫_ℝ := by
  rw [signFamily_mul, signFamily_mul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    sign_mul_self, one_mul]

theorem signFamily_continuous (x : Sign.{u}) :
    @Continuous Sign.{u} Line.{v} ⊥ _ fun g : Sign.{u} => signFamily.{u, v} (g * x) :=
  continuous_bot

/-- The element `-1`. -/
def negOne : Sign.{u} := ⟨-1⟩

theorem negOne_moves : signFamily.{u, v} (negOne.{u} * 1) ≠ signFamily.{u, v} 1 := by
  intro h
  have h' : (-1 : ℝ) • unitVector.{v} = (1 : ℝ) • unitVector.{v} := by
    simpa [signFamily, negOne] using h
  have h2 : (2 : ℝ) • unitVector.{v} = 0 := by
    have h3 : (1 : ℝ) • unitVector.{v} - (-1 : ℝ) • unitVector.{v} = 0 := by
      rw [h', sub_self]
    rw [← sub_smul] at h3
    norm_num at h3
    exact absurd h3 unitVector_ne_zero
  exact unitVector_ne_zero ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-! The value `φ (g * x)` of the family in the stabilizer side of the kernel clause of
`exists_orthogonal_rep_ker_eq`, against the translated point `g * x`. -/
namespace Kernel

/-- The group, the space with its norm and the family. -/
abbrev Params := Σ G : Type u, Σ V : Type v, Σ _ : NormedAddCommGroup V, G → V

abbrev signature : Signature where
  Params := Params.{u, v}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p s => p.2.2.2 s) (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ p _ => letI := p.2.2.1; 0) (fun e => nomatch e)

/-- Retain the complete group, space, family, continuity and invariance telescope of
`exists_orthogonal_rep_ker_eq`. -/
abbrev arena : Arena where
  signature := signature.{u, v}
  Law rd := ∀ {G : Type u} {V : Type v} [TopologicalSpace G] [Group G]
    [nacg : NormedAddCommGroup V] [InnerProductSpace ℝ V] (φ : G → V)
    [FiniteDimensional ℝ (Submodule.span ℝ (Set.range φ))],
    (∀ x : G, Continuous fun g => φ (g * x)) →
    (∀ g x y : G, ⟪φ (g * x), φ (g * y)⟫_ℝ = ⟪φ x, φ y⟫_ℝ) →
    ∃ ρ : G →* Matrix.orthogonalGroup
        (Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range φ)))) ℝ,
      Continuous ρ ∧ ∀ g : G, ρ g = 1 ↔ ∀ x : G, rd.readout () ⟨G, V, nacg, φ⟩ (g * x) = φ x

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  obtain ⟨ρ, -, hρ⟩ := @h Sign.{u} Line.{v} ⊥ _ _ _ signFamily.{u, v} _
    signFamily_continuous.{u, v} signFamily_gram.{u, v}
  have h0 : (0 : Line.{v}) = signFamily.{u, v} 1 := (hρ 1).1 (map_one ρ) 1
  have h1 : signFamily.{u, v} (1 : Sign.{u}) = unitVector.{v} := by
    simp [signFamily]
  exact unitVector_ne_zero.{v} (h1 ▸ h0).symm

theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  cases i
  refine ⟨⟨Sign.{u}, Line.{v}, inferInstance, signFamily.{u, v}⟩, negOne * 1, 1, ?_⟩
  exact negOne_moves.{u, v}

abbrev sourceStatement : Prop := type_of% @exists_orthogonal_rep_ker_eq.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_orthogonal_rep_ker_eq.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Kernel

def exists_orthogonal_rep_ker_eq_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_orthogonal_rep_ker_eq.{u, v}) (Realization Kernel.signature.{u, v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.InvariantGramRepresentation.exists_orthogonal_rep_ker_eq_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.InvariantGramRepresentation.Kernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Kernel.arena.{u, v}⟩
  objectArena := .source ⟨Kernel.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Kernel.arena.{u, v} ⟨Kernel.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Kernel.signature.{u, v} (fun _ p s => p.2.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.InvariantGramRepresentation
    definition := none
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.InvariantGramRepresentation
