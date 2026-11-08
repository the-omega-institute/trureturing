import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings
import Reg.Support.SingleDependentReadout

/-! The original complete telescope, observing the first coefficient body's convexity. -/

namespace Reg.D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings

open _root_.D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix Set
open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Set (Coeff 1)) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ C => Convex ℝ C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} (b : Label → X → ℝ)
    (r₁ : Fin 1 → X → ℝ) (r₂ : Fin 2 → X → ℝ),
    R.readout () () (body b r₁) ∧ Convex ℝ (body b r₂) ∧
    ((∃ A ∈ body b r₁, A.rank = 1) ↔ ¬ body b r₁ ⊆ {0}) ∧
    ((¬ ∃ A ∈ body b r₂, A.rank = 2) ↔ Rulings (body b r₂)) ∧
    ((∃ A ∈ body b r₂, A.rank = 2) ↔ ¬ Rulings (body b r₂)) ∧
    ((∃ A ∈ body b r₂, A.rank = 2) ↔
      ∃ A ∈ body b r₂, ∃ B ∈ body b r₂,
        ∃ i k j l, minor (blend (1 / 2) A B) i k j l ≠ 0) ∧
    ((∀ A ∈ body b r₂, ∀ B ∈ body b r₂, ∀ i k j l,
      minor (blend (1 / 2) A B) i k j l = 0) → Rulings (body b r₂)) ∧
    (∀ A : Coeff 2, ZeroSum A → A ≠ 0 → A.rank = 1 →
      ∃ u ∈ H, ∃ v : Fin 2 → ℝ, u ≠ 0 ∧ v ≠ 0 ∧ A = vecMulVec u v) ∧
    (∀ (u s : Label → ℝ) (v t : Fin 2 → ℝ) (θ : ℝ)
      (i k : Label) (j l : Fin 2),
      minor (blend θ (vecMulVec u v) (vecMulVec s t)) i k j l =
        θ * (1 - θ) * wedge u s i k * wedge v t j l) ∧
    (∀ (u s : Label → ℝ) (v t : Fin 2 → ℝ) (θ : ℝ), 0 < θ → θ < 1 →
      ((blend θ (vecMulVec u v) (vecMulVec s t)).rank = 2 ↔ Transverse u s v t)) ∧
    (∀ (u s u' s' : Label → ℝ) (v t v' t' : Fin 2 → ℝ),
      vecMulVec u v = vecMulVec u' v' → vecMulVec s t = vecMulVec s' t' →
      (Transverse u s v t ↔ Transverse u' s' v' t')) ∧
    (∀ A ∈ body b r₂, ∀ B ∈ body b r₂, ∀ θ : ℝ, 0 < θ → θ < 1 →
      blend θ A B ∈ body b r₂ ∧
      (A ≠ 0 → B ≠ 0 → A.rank = 1 → B.rank = 1 →
        ((blend θ A B).rank = 2 ↔ TransversePair A B))) ∧
    ((∀ A ∈ body b r₂, A.rank ≤ 1) →
      (¬ ∃ A ∈ body b r₂, ∃ B ∈ body b r₂, ∃ θ : ℝ,
        0 < θ ∧ θ < 1 ∧ (blend θ A B).rank = 2) ∧
      (¬ ∃ A ∈ body b r₂, ∃ B ∈ body b r₂, TransversePair A B) ∧
      ((∃ A ∈ body b r₂, ∃ B ∈ body b r₂, ∃ θ : ℝ,
        0 < θ ∧ θ < 1 ∧ (blend θ A B).rank = 2) ↔
        ∃ A ∈ body b r₂, ∃ B ∈ body b r₂, TransversePair A B) ∧
      Rulings (body b r₂)) ∧
    (∀ C : Set (Coeff 2), Convex ℝ C → (∀ A ∈ C, ZeroSum A) →
      ((∀ A ∈ C, A.rank ≤ 1) ↔ Rulings C)) ∧
    (∀ A : Coeff 2, A.rank = 2 ↔ ∃ i k j l, minor A i k j l ≠ 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (X := ULift.{u} Unit) 0 0 0).1

private theorem nonconvex_pair :
    ¬ Convex ℝ ({0, (fun _ _ => 1)} : Set (Coeff 1)) := by
  let M : Coeff 1 := fun _ _ => 1
  change ¬ Convex ℝ ({0, M} : Set (Coeff 1))
  intro h
  have hm := h (by exact Or.inl rfl : (0 : Coeff 1) ∈ ({0, M} : Set (Coeff 1)))
    (by exact Or.inr rfl : M ∈ ({0, M} : Set (Coeff 1)))
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  rcases hm with hm | hm
  · have he := congrArg (fun A : Coeff 1 => A Label.zero 0) hm
    change (1/2 : ℝ) * 0 + (1/2 : ℝ) * 1 = 0 at he
    norm_num at he
  · change (1/2 : ℝ) • 0 + (1/2 : ℝ) • M = M at hm
    have he := congrArg (fun A : Coeff 1 => A Label.zero 0) hm
    change (1/2 : ℝ) * 0 + (1/2 : ℝ) * 1 = 1 at he
    norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ∅, {0, (fun _ _ => 1)}, ?_⟩
  intro h
  exact nonconvex_pair (Eq.mp h (convex_empty : Convex ℝ (∅ : Set (Coeff 1))))

def source_registration : Registration arena.{u} (type_of% @result.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings.result.__information_unit
  realizationName := `Reg.D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ C => Convex ℝ C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings
