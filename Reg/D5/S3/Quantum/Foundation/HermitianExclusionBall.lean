import D5.S3.Quantum.Foundation.HermitianExclusionBall
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Exact full-frame and all-original-pure chart telescopes.
Variation, sensitivity, dependence and source-selection evidence are unsupplied. -/

noncomputable section
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace

namespace Reg.D5.S3.Quantum.Foundation.HermitianExclusionBall

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.SectionROGFrame
open _root_.D5.S3.Quantum.Foundation.HermitianExclusionKernel
open _root_.D5.S3.Quantum.Foundation.HermitianExclusionBall
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Type
  State A := A → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ A P => ∃ a : A, P a) (fun e => nomatch e)

namespace Frame

def arena : Arena where
  signature := signature
  Law O := ∀ (v : EuclideanSpace ℂ (Fin 3)) (hv : ‖v‖ = 1)
    (W : Matrix (Fin 3) (Fin 2) ℂ)
    (hW : W.conjTranspose * W = 1)
    (hQ : W * W.conjTranspose = 1 - (rankOne v).mat),
    O.readout () (ExclusionChart cone unit (rankOne v)) (fun a => a.dim = 3)

abbrev sourceScope : Prop := type_of% (@chart_of_full_frame)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl
theorem actual_positive : arena.Law actual := source_bridge.mp chart_of_full_frame

end Frame

namespace AllPure

def arena : Arena where
  signature := signature
  Law O := ∀ p : pure (cone : PointedCone ℝ (HermitianMat (Fin 3) ℂ)) unit,
    O.readout () (ExclusionChart cone unit (p : HermitianMat (Fin 3) ℂ))
      (fun a => a.dim = 3)

abbrev sourceScope : Prop := type_of% (@all_pure_charts)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl
theorem actual_positive : arena.Law actual := source_bridge.mp all_pure_charts

end AllPure

end Reg.D5.S3.Quantum.Foundation.HermitianExclusionBall
