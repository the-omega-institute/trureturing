import D5.S3.Quantum.Foundation.OriginalHeptagonObstruction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The exact original all-effect mixed-gluing telescope is reconstructed over
arbitrary real linear maps and mixed states. This source bridge supplies neither
whole-family variation nor the complete four-slot source-selection certificate. -/

noncomputable section

namespace Reg.D5.S3.Quantum.Foundation.OriginalHeptagonObstruction

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.OriginalHeptagonObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := (V →ₗ[ℝ] ℝ) × V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z.1 z.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (q : pure C u) (x y : V), x ∈ K → y ∈ K →
    (∃ f, confirms C u q f ∧ O.readout () () (f,x) = 0) →
    (∃ f, confirms C u q f ∧ O.readout () () (f,y) = 0) →
    ∃ f, confirms C u q f ∧ O.readout () () (f,(1/2 : ℝ) • (x+y)) = 0

abbrev sourceScope : Prop := type_of% whole_mixed_zero_gluing

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp whole_mixed_zero_gluing

end Reg.D5.S3.Quantum.Foundation.OriginalHeptagonObstruction
