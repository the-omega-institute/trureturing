import D5.S3.Quantum.Foundation.OriginalStateCover
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source reconstruction on arbitrary original carriers and full effects.
The complete family variation and sensitivity obligations are separate from
the positive mathematical source bridges. -/

noncomputable section
universe v
open Set

namespace Reg.D5.S3.Quantum.Foundation.OriginalStateCover

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OriginalStateCover
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Centered

structure Inputs where
  E : Type v
  [add : NormedAddCommGroup E]
  [space : NormedSpace ℝ E]
  body : Set E

attribute [instance] Inputs.add Inputs.space

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := (P.E →L[ℝ] ℝ) × P.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ x => x.1 x.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsCompact P.body → Convex ℝ P.body → (0 : P.E) ∈ interior P.body →
    (∃ z ∈ P.body, z ≠ 0) →
    ∃ (t : ℝ) (z : P.E) (f : P.E →L[ℝ] ℝ),
      0 < t ∧ z ∈ P.body ∧ (-t) • z ∈ P.body ∧
      0 < O.readout () P (f,(-t) • z) ∧ O.readout () P (f,z) < 0 ∧
      (∀ w ∈ P.body, O.readout () P (f,z) ≤ O.readout () P (f,w)) ∧
      (∀ w ∈ P.body, O.readout () P (f,w) ≤ O.readout () P (f,(-t) • z))

abbrev sourceScope : Prop := type_of% (@centered_affine_diameter.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.E P.add P.space P.body
  · intro h E add space L
    exact h (@Inputs.mk E add space L)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@centered_affine_diameter.{v})

end Centered

namespace Cover

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  [nontrivial : Nontrivial V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite Inputs.nontrivial

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := (P.V →ₗ[ℝ] ℝ) × P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ x => x.1 x.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    Function.Injective (fun p : pure C u => exclusion C u p) →
    base C u = ⋃ p : pure C u, convexHull ℝ (insert (p : P.V) (exclusion C u p)) ∧
    ∀ x ∈ base C u,
      ∃ (p : pure C u) (y : P.V) (s : ℝ) (f : P.V →ₗ[ℝ] ℝ),
        y ∈ exclusion C u p ∧ s ∈ Icc (0 : ℝ) 1 ∧ proper C u f ∧
        O.readout () P (f,p) = 1 ∧ O.readout () P (f,y) = 0 ∧
        x = s • (p : P.V) + (1-s) • y ∧
        (x ∈ intrinsicInterior ℝ (base C u) → s ∈ Ioo (0 : ℝ) 1) ∧
        ∀ b : ExclusionChart C u p,
          ∃ (q r : pure C u) (t : ℝ),
            (q : P.V) ∈ exclusion C u p ∧ (r : P.V) ∈ exclusion C u p ∧
            t ∈ Icc (0 : ℝ) 1 ∧ (r : P.V) = (2 : ℝ) • b.param 0 - (q : P.V) ∧
            y = t • (q : P.V) + (1-t) • (r : P.V) ∧
            x = s • (p : P.V) + (1-s) • (t • (q : P.V) + (1-t) • (r : P.V))

abbrev sourceScope : Prop := type_of% (@original_state_cover.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.nontrivial
  · intro h V add space finite C u nontrivial
    exact h (@Inputs.mk V add space finite nontrivial C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@original_state_cover.{v})

def erased : Realization signature.{v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The same full source law rejects zero readout at every actual complete input. -/
theorem erased_negative_of_input (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hB : exclusionBalls P.cone P.unit)
    (hinj : Function.Injective (fun p : pure P.cone P.unit => exclusion P.cone P.unit p)) :
    ¬ arena.{v}.Law erased.{v} := by
  intro h
  obtain ⟨p⟩ := _root_.D5.S3.Quantum.Foundation.OriginalFacePolarity.pure_nonempty hc hs hg
  obtain ⟨_,hh⟩ := h P hc hs hg hB hinj
  obtain ⟨q,y,s,f,_,_,_,hfp,_⟩ := hh p (pure_mem p)
  exact zero_ne_one hfp

end Cover

end Reg.D5.S3.Quantum.Foundation.OriginalStateCover
