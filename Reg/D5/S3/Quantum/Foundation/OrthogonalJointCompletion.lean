import D5.S3.Quantum.Foundation.OrthogonalJointCompletion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Original all-P telescope with the entire joint-third relation as observation.
A complete four-slot registration additionally needs whole-family variation,
sensitivity, observational dependence and exact source-selection evidence. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.OrthogonalJointCompletion

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.WholePairBallConfirmation
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

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
  State P := pure P.cone P.unit × pure P.cone P.unit × pure P.cone P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P x => jointThird P.cone P.unit x.1 x.2.1 x.2.2)
    (fun e => nomatch e)

def erased : Realization signature.{v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u → weakPair C u →
    (∀ p q : pure C u, excludes C u p q →
      ∃! r : pure C u, O.readout () P (p, q, r)) ∧
    (∀ p : pure C u, ∃ q r : pure C u, O.readout () P (p, q, r)) ∧
    (∀ p q r s : pure C u,
      excludes C u p q → excludes C u p r → excludes C u p s →
      excludes C u q r → excludes C u q s → ¬ excludes C u r s) ∧
    measurement C u 3 ∧ (∀ n, measurement C u n → n ≤ 3)

abbrev sourceScope : Prop := type_of% (@whole_joint_completion.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
  · intro h V add space finite nontrivial C u hc hs hg hB hW
    exact h (@Inputs.mk V add space finite nontrivial C u) hc hs hg hB hW

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@whole_joint_completion.{v})

/-- Erasing the entire relation fails at every original admissible input.
This conditional witness is not a global enrolled four-slot registration. -/
theorem erased_negative (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hB : exclusionBalls P.cone P.unit) (hW : weakPair P.cone P.unit) :
    ¬ arena.{v}.Law erased.{v} := by
  intro h
  obtain ⟨p, f, hp, hd, _⟩ := (h P hc hs hg hB hW).2.2.2.1
  obtain ⟨q, r, hr⟩ := (h P hc hs hg hB hW).2.1 (p 0)
  exact hr

/-- The outstanding dependent evidence must be supplied before constructing
Contract.Registration; importing an enrollment is not registration completion. -/
abbrev pendingEvidence := Registration arena.{v} sourceScope.{v}

#print axioms source_bridge
#print axioms actual_positive
#print axioms erased_negative

end Reg.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
