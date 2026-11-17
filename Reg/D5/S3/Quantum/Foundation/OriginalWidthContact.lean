import D5.S3.Quantum.Foundation.OriginalWidthContact
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full source reconstruction for actual original contact-effect readings.
Whole-family intervention and sensitivity are separate mathematical obligations. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.OriginalWidthContact

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OriginalWidthContact
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  effect : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P x => P.effect x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    let b := P.effect
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    Function.Injective (fun p : pure C u => exclusion C u p) →
    ∀ (p : pure C u) {M : ℝ}, 0 < M →
    WidthBound C u (exclusion C u p) M → proper C u b →
    ∀ {q r : P.V}, q ∈ exclusion C u p → r ∈ exclusion C u p → b q - b r = M →
    ∃ xy : P.V × P.V,
      (xy.1 ∈ base C u ∧ xy.2 ∈ base C u ∧
        O.readout () P xy.1 = 1 ∧ O.readout () P xy.2 = 0 ∧
        q - r = M • (xy.1 - xy.2)) ∧
      (∀ zw : P.V × P.V, zw.1 ∈ base C u → zw.2 ∈ base C u →
        O.readout () P zw.1 = 1 → O.readout () P zw.2 = 0 →
        q - r = M • (zw.1 - zw.2) → zw = xy) ∧
      (M < 1 → ∀ e : P.V →ₗ[ℝ] ℝ, confirms C u p e →
        (∀ z ∈ exclusion C u p, e z = 0) →
        0 < e xy.1 ∧ e xy.1 = e xy.2 ∧ e xy.2 < 1 ∧
          xy.1 ∉ exclusion C u p ∧ xy.2 ∉ exclusion C u p)

abbrev sourceScope : Prop := type_of% (@original_width_contact.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit P.effect
  · intro h V add space finite C u b
    exact h (@Inputs.mk V add space finite C u b)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@original_width_contact.{v})

def erased : Realization signature.{v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- A zero intervention fails at every original admissible attained-width input.
Existence of such a full original input remains a separate global obligation. -/
theorem erased_negative_of_input (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hu : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hB : exclusionBalls P.cone P.unit)
    (hinj : Function.Injective (fun p : pure P.cone P.unit => exclusion P.cone P.unit p))
    (p : pure P.cone P.unit) {M : ℝ} (hM : 0 < M)
    (hw : WidthBound P.cone P.unit (exclusion P.cone P.unit p) M)
    (hb : proper P.cone P.unit P.effect)
    {q r : P.V} (hq : q ∈ exclusion P.cone P.unit p)
    (hr : r ∈ exclusion P.cone P.unit p) (heq : P.effect q - P.effect r = M) :
    ¬ arena.{v}.Law erased.{v} := by
  intro h
  obtain ⟨xy, hxy, _⟩ := h P hc hu hg hB hinj p hM hw hb hq hr heq
  have hh : (0 : ℝ) = 1 := hxy.2.2.1
  exact zero_ne_one hh

end Reg.D5.S3.Quantum.Foundation.OriginalWidthContact
