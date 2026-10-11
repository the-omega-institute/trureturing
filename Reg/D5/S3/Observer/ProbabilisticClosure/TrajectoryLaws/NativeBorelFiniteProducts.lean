import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelKilledPaths NativeBorelFiniteProducts
open Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

def finiteProductArena : Arena where
  signature := doobSignature
  Law R := ∀ F, ∃ (G : Set PDescriptor) (hsub : ∀ Q, R.readout 0 F G Q Set.univ ≤ 1),
    MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    ∀ n : ℕ,
      ((killedTrajectory F (R.readout 0 F G) hsub).map
        (fun x (i : Fin (n + 1)) => x i.1)).restrict (allLive n) =
        (finiteProduct F.nuP (R.readout 0 F G) n).map (fun w i => Sum.inl (w i)) ∧
      finiteProduct F.nuP (R.readout 0 F G) n =
        ((originalTrajectory F).map (fun x (i : Fin (n + 1)) => x i.1)).withDensity
          (finiteDensity F (R.readout 0 F G) n) ∧
      finiteProduct F.nuP (R.readout 0 F G) n ≪
        (originalTrajectory F).map (fun x (i : Fin (n + 1)) => x i.1)

theorem finite_product_bridge : (type_of% (@common_flow_finite_product)) ↔
    finiteProductArena.Law doobActual := Iff.rfl

theorem finite_product_actual_law : finiteProductArena.Law doobActual :=
  finite_product_bridge.mp common_flow_finite_product

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
