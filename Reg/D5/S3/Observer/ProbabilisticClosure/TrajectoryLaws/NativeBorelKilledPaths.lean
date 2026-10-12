import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelEndpointIdentification NativeBorelKilledPaths
open NativeBorelTVTopology NativeBorelEndpointIdentification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
attribute [local instance] Classical.propDecidable

abbrev doobSignature : Signature where
  Params := CommonFlow
  State _ := Set PDescriptor
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Kernel PDescriptor PDescriptor
  Anchor := Empty
  finiteAnchor := inferInstance

def doobActual : Realization doobSignature := realize _ (fun _ F G => doob F G) (fun e => nomatch e)

def doobArena : Arena where
  signature := doobSignature
  Law R := ∀ F, ∃ (G : Set PDescriptor) (hsub : ∀ Q, R.readout 0 F G Q Set.univ ≤ 1),
    MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    IsMarkovKernel (cemetery (R.readout 0 F G)) ∧
    IsProbabilityMeasure (killedTrajectory F (R.readout 0 F G) hsub) ∧
    (∀ Q, R.readout 0 F G Q ≪ F.C Q) ∧
    (∀ Q ∈ G, CoreAt F Q ∧ (∀ᵐ Q' ∂F.C Q, Q' ∈ G)) ∧
    (∀ (f : PDescriptor → ℝ≥0∞), Measurable f → ∀ n Q, Q ∈ G →
      normalizedIterate F (fun Q' => threeStepAverage F Q' * f Q') n Q =
        threeStepAverage F Q * iterate (R.readout 0 F G) f n Q) ∧
    (∀ᵐ Q ∂F.nuP, Antitone (fun n => iterate (R.readout 0 F G) (fun _ => 1) n Q) ∧
      Tendsto (fun n => iterate (R.readout 0 F G) (fun _ => 1) n Q) atTop
        (𝓝 (q F Q / threeStepAverage F Q))) ∧
    (∀ Q ∈ G, 0 < R.readout 0 F G Q Set.univ) ∧
    (∀ᵐ Q ∂F.nuP,
      (1 - R.readout 0 F G Q Set.univ).toReal = delta F Q / h F Q ∧
      (2 / 3 : ℝ) * excess Q ≤ (1 - R.readout 0 F G Q Set.univ).toReal) ∧
    (∀ᵐ Q ∂F.nuP, endpointRate⁻¹ • F.L Q ≤
      ENNReal.ofReal (1 + 25 * excess Q / 9) • F.C Q)

theorem doob_bridge : (type_of% (@common_flow_doob_survival)) ↔ doobArena.Law doobActual := Iff.rfl

theorem doob_actual_law : doobArena.Law doobActual := doob_bridge.mp common_flow_doob_survival

def immortalArena : Arena where
  signature := doobSignature
  Law R := ∀ F, ∃ (G : Set PDescriptor) (hsub : ∀ Q, R.readout 0 F G Q Set.univ ≤ 1),
    MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    (∀ Q ∈ G, ∀ n, 0 < iterate (R.readout 0 F G) (fun _ => 1) n Q) ∧
    (∀ᵐ Q ∂F.nuP,
      startedTrajectory (R.readout 0 F G) hsub Q immortal = q F Q / threeStepAverage F Q ∧
      startedTrajectory (R.readout 0 F G) hsub Q immortal =
        (if Q = nativeEndpoint .p true then 1 else 0)) ∧
    killedTrajectory F (R.readout 0 F G) hsub immortal = F.nuP {nativeEndpoint .p true}

theorem immortal_bridge : (type_of% (@common_flow_immortal_survival)) ↔
    immortalArena.Law doobActual := Iff.rfl

theorem immortal_actual_law : immortalArena.Law doobActual :=
  immortal_bridge.mp common_flow_immortal_survival

def immortalIdentityArena : Arena where
  signature := doobSignature
  Law R := ∀ F, ∃ (G : Set PDescriptor) (hsub : ∀ Q, R.readout 0 F G Q Set.univ ≤ 1),
    MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    (∀ Q ∈ G, ∀ n, 0 < iterate (R.readout 0 F G) (fun _ => 1) n Q) ∧
    (killedTrajectory F (R.readout 0 F G) hsub).restrict immortal =
      F.nuP {nativeEndpoint .p true} • Measure.dirac (fun _ => Sum.inl (nativeEndpoint .p true)) ∧
    (killedTrajectory F (R.readout 0 F G) hsub).restrict immortal =
      ((originalTrajectory F).restrict {x | x 0 = nativeEndpoint .p true}).map includePath ∧
    (killedTrajectory F (R.readout 0 F G) hsub).restrict immortal ≤
      (originalTrajectory F).map includePath ∧
    (killedTrajectory F (R.readout 0 F G) hsub).restrict immortal ≪
      (originalTrajectory F).map includePath ∧
    (∀ᵐ x ∂(killedTrajectory F (R.readout 0 F G) hsub).restrict immortal, pathDefect x = 0) ∧
    (∀ t : ℝ, 0 ≤ t →
      ((killedTrajectory F (R.readout 0 F G) hsub).restrict immortal).restrict
        {x | pathDefect x ≤ ENNReal.ofReal t} ≤
        ((25 / 6 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (25 * t / 9))) •
        (originalTrajectory F).map includePath) ∧
    (∀ n : ℕ,
      (killedTrajectory F (R.readout 0 F G) hsub).withDensity
        (fun x => Sum.elim (fun Q => q F Q / threeStepAverage F Q) (fun _ => 0) (x n)) =
        (killedTrajectory F (R.readout 0 F G) hsub).restrict immortal ∧
      ((killedTrajectory F (R.readout 0 F G) hsub).map (Preorder.frestrictLe n)).withDensity
        (fun x => Sum.elim (fun Q => q F Q / threeStepAverage F Q) (fun _ => 0)
          (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) =
        ((killedTrajectory F (R.readout 0 F G) hsub).restrict immortal).map
          (Preorder.frestrictLe n))

theorem immortal_identity_bridge : (type_of% (@common_flow_immortal_identity)) ↔
    immortalIdentityArena.Law doobActual := Iff.rfl

theorem immortal_identity_actual_law : immortalIdentityArena.Law doobActual :=
  immortal_identity_bridge.mp common_flow_immortal_identity


universe u v

abbrev cemeteryMarkovSignature : Signature where
  Params := Kernel PDescriptor PDescriptor
  State _ := Unit
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Kernel Cemetery Cemetery
  Anchor := Empty
  finiteAnchor := inferInstance

def cemeteryMarkovActual : Realization cemeteryMarkovSignature :=
  realize _ (fun _ M _ => cemetery M) (fun e => nomatch e)

def cemeteryMarkovArena : Arena where
  signature := cemeteryMarkovSignature
  Law R := ∀ (M : Kernel PDescriptor PDescriptor),
    (∀ Q, M Q Set.univ ≤ 1) → IsMarkovKernel (R.readout 0 M ())

theorem cemetery_markov_bridge : (type_of% (@cemetery_markov)) ↔
    cemeteryMarkovArena.Law cemeteryMarkovActual := Iff.rfl

theorem cemetery_markov_actual_law : cemeteryMarkovArena.Law cemeteryMarkovActual :=
  cemetery_markov_bridge.mp cemetery_markov

abbrev homogeneousInitialSignature : Signature where
  Params := Σ S : Type u, MeasurableSpace S
  State _ := Unit
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2
    Measure p.1 → (K : Kernel p.1 p.1) → [IsMarkovKernel K] → Measure (ℕ → p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def homogeneousInitialActual : Realization homogeneousInitialSignature.{u} :=
  realize _ (fun _ p _ => @homogeneousLaw p.1 p.2) (fun e => nomatch e)

def homogeneousInitialArena : Arena where
  signature := homogeneousInitialSignature.{u}
  Law R := ∀ (S : Type u) (m : MeasurableSpace S), letI := m
    ∀ (μ : Measure S) (K : Kernel S S) [IsMarkovKernel K],
      (R.readout 0 ⟨S,m⟩ () μ K).map (fun x => x 0) = μ

theorem homogeneous_initial_bridge : (type_of% (@homogeneous_initial.{u})) ↔
    homogeneousInitialArena.{u}.Law homogeneousInitialActual.{u} := Iff.rfl

theorem homogeneous_initial_actual_law :
    homogeneousInitialArena.{u}.Law homogeneousInitialActual.{u} :=
  homogeneous_initial_bridge.{u}.mp (@homogeneous_initial.{u})

abbrev mapTerminalDensitySignature : Signature where
  Params := (Σ S : Type u, MeasurableSpace S) × (Σ U : Type v, MeasurableSpace U)
  State _ := Unit
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.1.2
    letI := p.2.2
    Measure p.1.1 → (p.1.1 → p.2.1) → Measure p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def mapTerminalDensityActual : Realization mapTerminalDensitySignature.{u,v} :=
  realize _ (fun _ p _ => by
    letI := p.1.2
    letI := p.2.2
    exact fun μ f => μ.map f) (fun e => nomatch e)

def mapTerminalDensityArena : Arena where
  signature := mapTerminalDensitySignature.{u,v}
  Law R := ∀ (S : Type u) (U : Type v) (mS : MeasurableSpace S) (mU : MeasurableSpace U),
    letI := mS
    letI := mU
    ∀ (μ : Measure S) (f : S → U), Measurable f →
      ∀ (w : U → ℝ≥0∞), Measurable w →
        R.readout 0 (⟨S,mS⟩,⟨U,mU⟩) () (μ.withDensity (fun x => w (f x))) f =
          (R.readout 0 (⟨S,mS⟩,⟨U,mU⟩) () μ f).withDensity w

theorem map_terminal_density_bridge : (type_of% (@map_terminal_density.{u,v})) ↔
    mapTerminalDensityArena.{u,v}.Law mapTerminalDensityActual.{u,v} := Iff.rfl

theorem map_terminal_density_actual_law :
    mapTerminalDensityArena.{u,v}.Law mapTerminalDensityActual.{u,v} :=
  map_terminal_density_bridge.{u,v}.mp (@map_terminal_density.{u,v})


end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelKilledPaths
