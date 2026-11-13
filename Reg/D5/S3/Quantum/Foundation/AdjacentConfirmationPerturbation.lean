import D5.S3.Quantum.Foundation.AdjacentConfirmationPerturbation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact original telescopes and the actual perturbation evaluation readout.
Whole-family intervention, sensitivity and occurrence-bound source selection
are not supplied by these source reconstruction proofs. -/

noncomputable section
open Set
universe v

namespace Reg.D5.S3.Quantum.Foundation.AdjacentConfirmationPerturbation

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OriginalWidthContact
open _root_.D5.S3.Quantum.Foundation.ExclusionWidthCompactness
open _root_.D5.S3.Quantum.Foundation.AdjacentConfirmationPerturbation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := (P.V →ₗ[ℝ] ℝ) × (P.V →ₗ[ℝ] ℝ) × ℝ × P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ s => (s.1 + s.2.2.1 • s.2.1) s.2.2.2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let V := P.V
    let C := P.cone
    let u := P.unit
    ∀ (a e : V →ₗ[ℝ] ℝ)
      (hc : IsClosed (C : Set V)) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
      (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
      (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
      (p q : pure C u) (hq : (q : V) ∈ exclusion C u p)
      (ha : confirms C u q a) (ha0 : ∀ x ∈ exclusion C u q, a x = 0)
      (he : confirms C u p e) (he0 : ∀ x ∈ exclusion C u p, e x = 0)
      (M : ℝ) (hM : M < 1) (hwidth : WidthBound C u (exclusion C u q) M),
      ∃ t : ℝ, 0 < t ∧ ∃ lo hi : ℝ,
        (∀ x ∈ base C u, lo ≤ O.readout () P (a,e,t,x) ∧
          O.readout () P (a,e,t,x) ≤ hi) ∧
        (∃ x ∈ base C u, O.readout () P (a,e,t,x) = lo) ∧
        (∃ x ∈ base C u, O.readout () P (a,e,t,x) = hi) ∧
        0 < hi - lo ∧ hi - lo < 1 ∧
        let b := (hi - lo)⁻¹ • ((a + t • e) - lo • u)
        proper C u b ∧
        oscillation (exclusion C u p) a.toContinuousLinearMap <
          oscillation (exclusion C u p) b.toContinuousLinearMap ∧
        0 < oscillation (exclusion C u p) a.toContinuousLinearMap

abbrev sourceScope : Prop := type_of% (@adjacent_confirmation_perturbation.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P a e hc hu hg hB hinj p q hq ha ha0 he he0 M hM hwidth
    exact @h P.V P.add P.space P.finite P.cone P.unit a e hc hu hg hB hinj
      p q hq ha ha0 he he0 M hM hwidth
  · intro h V add space finite C u a e hc hu hg hB hinj p q hq ha ha0 he he0 M hM hwidth
    exact h (@Inputs.mk V add space finite C u) a e hc hu hg hB hinj
      p q hq ha ha0 he he0 M hM hwidth

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@adjacent_confirmation_perturbation.{v})

end Reg.D5.S3.Quantum.Foundation.AdjacentConfirmationPerturbation
