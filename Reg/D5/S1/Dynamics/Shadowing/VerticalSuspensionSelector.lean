import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector
import Reg.Support.DependentFamily
import Mathlib.Topology.Metrizable.Uniformity

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector
open Set Topology

namespace Reg.D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector

noncomputable section
universe u

/-- Reify the final restriction equality on its actual suspension-valued operands. -/
abbrev restrictionSignature : Signature where
  Params := Σ X : Type u, X
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def restrictionActual : Realization restrictionSignature.{u} := by
  classical
  exact realize restrictionSignature (fun _ p x => decide (x = p.2)) (fun e => nomatch e)

def restrictionRejected : Realization restrictionSignature.{u} :=
  realize restrictionSignature (fun _ _ _ => false) (fun e => nomatch e)

/-- All original space, connector, metric, proof and tolerance binders remain universal. -/
abbrev restrictionArena : Arena where
  signature := restrictionSignature.{u}
  Law A := ∀ {K : Type u} [TopologicalSpace K] [Nonempty K] [CompactSpace K]
      [TopologicalSpace.MetrizableSpace K] (H : LocalEquiconnection K)
      (m : MetricSpace (Suspension K))
      (hm : (inferInstance : TopologicalSpace (Suspension K)) = m.toUniformSpace.toTopologicalSpace),
    letI := m.replaceTopology hm
    ∃ δstar : ℝ, ∃ hδstar : 0 < δstar,
      ∃ Rstar : IntegerSelector (vertical : Suspension K ≃ₜ Suspension K) δstar hδstar.le,
        ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hbound : δ ≤ δstar,
          ∃ R : IntegerSelector (vertical : Suspension K ≃ₜ Suspension K) δ hδ.le,
            ∀ x, A.readout () ⟨Suspension K,
              Rstar.map ⟨x.1, fun j => (x.2 j).trans hbound⟩⟩ (R.map x) = true

private abbrev One := ULift.{u} Unit

private def oneConnection : LocalEquiconnection One.{u} where
  domain := univ
  isOpen_domain := isOpen_univ
  diagonal _ := mem_univ _
  connect _ := ⟨()⟩
  continuous_connect := continuous_const
  left _ := Subsingleton.elim _ _
  right _ := Subsingleton.elim _ _
  refl _ _ := Subsingleton.elim _ _

private def oneSuspensionHomeo : Suspension One.{u} ≃ₜ Height where
  toFun := height
  invFun := point ⟨()⟩
  left_inv z := by
    induction z using Quotient.inductionOn with | _ p =>
      exact Quotient.sound ⟨rfl, Or.inr (Or.inr (Subsingleton.elim _ _))⟩
  right_inv _ := rfl
  continuous_toFun := continuous_snd.quotient_lift _
  continuous_invFun := continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)

private theorem restrictionActual_law : restrictionArena.{u}.Law restrictionActual := by
  classical
  simpa only [restrictionArena, restrictionActual, realize, decide_eq_true_eq] using
    (@compact_lec_crossing_selector.{u})

private theorem restrictionRejected_law : ¬restrictionArena.{u}.Law restrictionRejected := by
  intro h
  letI : TopologicalSpace.MetrizableSpace (Suspension One.{u}) :=
    oneSuspensionHomeo.isEmbedding.metrizableSpace
  let m : MetricSpace (Suspension One.{u}) :=
    TopologicalSpace.metrizableSpaceMetric (Suspension One.{u})
  have hm : (inferInstance : TopologicalSpace (Suspension One.{u})) =
      m.toUniformSpace.toTopologicalSpace := by rfl
  obtain ⟨δstar, hδstar, Rstar, hsmall⟩ := h oneConnection m hm
  obtain ⟨R, hR⟩ := hsmall δstar hδstar le_rfl
  have hb := hR (orbit (vertical : Suspension One.{u} ≃ₜ Suspension One.{u})
    δstar hδstar.le (point (⟨()⟩ : One.{u}) ⟨0, by constructor <;> norm_num⟩))
  exact Bool.false_ne_true hb

def restrictionRegistration : Registration restrictionArena.{u}
    (type_of% (@compact_lec_crossing_selector.{u})) where
  actual := restrictionActual
  bridge := by
    classical
    simp only [restrictionArena, restrictionActual, realize, decide_eq_true_eq]
  variation := ⟨restrictionActual_law, restrictionRejected, restrictionRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨restrictionRejected, ?_, rfl, restrictionRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ⟨false⟩⟩, ⟨false⟩, ⟨true⟩, ?_⟩
    simp [restrictionActual, realize]

def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compact_lec_crossing_selector.{u}) (Realization restrictionSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector.fullSelector
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector.restrictionRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨restrictionArena.{u}⟩
  objectArena := .source ⟨restrictionArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source restrictionArena.{u} ⟨restrictionRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize restrictionSignature.{u}
    (fun _ p x => @decide (x = p.2) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body",
        "arg","body","arg","body","arg","body","body","body","body","arg","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector
