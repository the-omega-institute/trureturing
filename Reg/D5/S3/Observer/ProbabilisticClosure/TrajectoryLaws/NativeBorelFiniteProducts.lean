import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelKilledPaths NativeBorelFiniteProducts
open Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

def finiteProductArena : Arena where
  signature := doobSignature
  Law R := ∀ F, ∃ (G : Set PDescriptor) (hsub : ∀ Q, R.readout 0 F G Q Set.univ ≤ 1),
    MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    (∀ᵐ Q ∂F.nuP, ∀ᵐ R' ∂F.C Q,
      (R.readout 0 F G).rnDeriv F.C Q R' ≤
        (threeStepAverage F Q)⁻¹ * threeStepAverage F R' *
          ENNReal.ofReal (1 + 25 * excess Q / 9)) ∧
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

def finiteHistoryRNArena : Arena where
  signature := doobSignature
  Law R := ∀ F, ∃ (G : Set PDescriptor) (hsub : ∀ Q, R.readout 0 F G Q Set.univ ≤ 1),
    MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    (∀ᵐ Q ∂F.nuP, ∀ᵐ R' ∂F.C Q,
      (R.readout 0 F G).rnDeriv F.C Q R' ≤
        (threeStepAverage F Q)⁻¹ * threeStepAverage F R' *
          ENNReal.ofReal (1 + 25 * excess Q / 9)) ∧
    ∀ n : ℕ, (finiteProduct F.nuP (R.readout 0 F G) n).rnDeriv
        (finiteProduct F.nuP F.C n) ≤ᵐ[finiteProduct F.nuP F.C n]
      (fun w =>
        (threeStepAverage F (w 0))⁻¹ *
          threeStepAverage F (w (Fin.last n)) *
            ∏ i : Fin n, ENNReal.ofReal
              (1 + 25 * excess (w i.castSucc) / 9))

theorem finite_history_rn_bound_bridge :
    (type_of% (@common_flow_finite_history_rn_bound)) ↔
      finiteHistoryRNArena.Law doobActual := Iff.rfl

theorem finite_history_rn_bound_actual_law : finiteHistoryRNArena.Law doobActual :=
  finite_history_rn_bound_bridge.mp common_flow_finite_history_rn_bound


abbrev snocSignature : Signature where
  Params := Σ S : Type u, MeasurableSpace S
  State _ := Unit
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (n : ℕ) → ((Fin (n + 1) → p.1) × p.1) → (Fin (n + 2) → p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def snocActual : Realization snocSignature.{u} :=
  realize _ (fun _ _ _ _ p => Fin.snoc p.1 p.2) (fun e => nomatch e)

def snocArena : Arena where
  signature := snocSignature.{u}
  Law R := ∀ (S : Type u) (m : MeasurableSpace S), letI := m
    ∀ n, Measurable (R.readout 0 ⟨S,m⟩ () n)

theorem snoc_bridge : (type_of% (@snoc_measurable.{u})) ↔
    snocArena.{u}.Law snocActual.{u} := Iff.rfl

theorem snoc_actual_law : snocArena.{u}.Law snocActual.{u} :=
  snoc_bridge.{u}.mp (@snoc_measurable.{u})

def prefixProductArena : Arena where
  signature := homogeneousInitialSignature.{u}
  Law R := ∀ (S : Type u) (m : MeasurableSpace S), letI := m
    ∀ (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S S) [IsMarkovKernel K] (n : ℕ),
      (R.readout 0 ⟨S,m⟩ () μ K).map (fun x (i : Fin (n + 1)) => x i.1) =
        finiteProduct μ K n

theorem prefix_product_bridge : (type_of% (@homogeneous_prefix_product.{u})) ↔
    prefixProductArena.{u}.Law homogeneousInitialActual.{u} := Iff.rfl

theorem prefix_product_actual_law :
    prefixProductArena.{u}.Law homogeneousInitialActual.{u} :=
  prefix_product_bridge.{u}.mp (@homogeneous_prefix_product.{u})

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteProducts
