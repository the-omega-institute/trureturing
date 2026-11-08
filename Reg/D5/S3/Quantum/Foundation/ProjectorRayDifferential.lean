import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Foundation.ProjectorRayDifferential
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Full-telescope source reconstruction for the local ray-distance speed theorem.
The parameter family retains the original amplitude carrier and both instances;
the state retains the original base amplitude and velocity. The law retains
the actual curve, derivative and neighbourhood unit-norm hypotheses.

The dependent-family evidence includes an explicit rejected whole family and
two distinct observations in the same two-dimensional amplitude space.
It is not a validated Contract.Registration: compiler occurrence/coordinate
evidence and the outer typed contract remain required. A signature that
discards the amplitude carrier cannot replace these operands.
The unfinished binding is tracked at
https://github.com/the-omega-institute/trureturing/issues/28177.
-/

noncomputable section
open Filter
open scoped Topology
universe u

namespace Reg.D5.S3.Quantum.Foundation.ProjectorRayDifferential

open _root_.D5.S3.Quantum.Foundation.ProjectorRayDifferential
open _root_.D5.S3.QuantumBounds.FubiniStudyRecordTime (fsAngle)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  E : Type u
  group : NormedAddCommGroup E
  space : letI := group; InnerProductSpace ℂ E

attribute [instance] Parameters.group Parameters.space

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.E × p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s =>
    Real.sqrt (‖s.2‖ ^ 2 - ‖inner ℂ s.1 s.2‖ ^ 2))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : Parameters.{u}) (f : ℝ → p.E) (ψ v : p.E),
    ‖ψ‖ = 1 → f 0 = ψ → HasDerivAt f v 0 →
    (∀ᶠ t in 𝓝 (0 : ℝ), ‖f t‖ = 1) →
    Tendsto (fun t : ℝ => fsAngle ψ (f t) / |t|) (𝓝[≠] 0)
      (𝓝 (R.readout () p (ψ, v)))

theorem source_bridge : (type_of% (@fs_angle_speed.{u})) ↔
    arena.{u}.Law actual := by
  constructor
  · intro h p f ψ v hψ h₀ hf hunit
    exact h hψ h₀ hf hunit
  · intro h E group space f ψ v hψ h₀ hf hunit
    exact h ⟨E, group, space⟩ f ψ v hψ h₀ hf hunit

theorem actual_positive : arena.{u}.Law actual :=
  source_bridge.mp (@fs_angle_speed.{u})

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private def testParameters : Parameters.{u} :=
  ⟨EuclideanSpace ℂ (ULift.{u} (Fin 2)), inferInstance, inferInstance⟩

private def base : testParameters.{u}.E := EuclideanSpace.single ⟨0⟩ 1

private def transverse : testParameters.{u}.E := EuclideanSpace.single ⟨1⟩ 1

private theorem base_norm : ‖base.{u}‖ = 1 := by
  simp [base, EuclideanSpace.single, PiLp.norm_single]

private theorem transverse_norm : ‖transverse.{u}‖ = 1 := by
  simp [transverse, EuclideanSpace.single, PiLp.norm_single]

private theorem base_transverse_inner : inner ℂ base.{u} transverse = 0 := by
  simp [base, transverse, EuclideanSpace.inner_single_left,
    EuclideanSpace.single, PiLp.single_apply]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have ht := h testParameters (fun _ : ℝ => base) base 0 base_norm rfl
    (hasDerivAt_const (0 : ℝ) base)
    (Eventually.of_forall fun _ => base_norm)
  have hz : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 1) := by
    simpa [rejected, realize, fsAngle, inner_self_eq_norm_sq_to_K, base_norm] using ht
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hz)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨testParameters, (base, 0), (base, transverse), ?_⟩
  change Real.sqrt (‖(0 : testParameters.E)‖ ^ 2 - ‖inner ℂ base 0‖ ^ 2) ≠
    Real.sqrt (‖transverse‖ ^ 2 - ‖inner ℂ base transverse‖ ^ 2)
  simp [transverse_norm, base_transverse_inner]

def family : Registration arena.{u} (type_of% (@fs_angle_speed.{u})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Reg.D5.S3.Quantum.Foundation.ProjectorRayDifferential
