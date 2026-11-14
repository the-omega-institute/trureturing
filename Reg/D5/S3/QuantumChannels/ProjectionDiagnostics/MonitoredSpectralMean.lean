import D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredSpectralMean
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open _root_.D5.S3.QuantumChannels.ProjectionDiagnostics
open MonitoredReturnConservation CyclicMonitoredContraction MonitoredSpectralMean
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
open scoped InnerProductSpace
universe u
namespace Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredSpectralMean

structure Scope where
  E : Type u
  [addE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℂ E]
  [finiteE : FiniteDimensional ℂ E]
  U : E ≃ₗᵢ[ℂ] E
  v : E

attribute [instance] Scope.addE Scope.innerE Scope.finiteE

abbrev signature : Signature where
  Params := Scope.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p n => (n + 1 : ℝ) * returnProbability p.U p.v (n + 1))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : E ≃ₗᵢ[ℂ] E) (v : E) (_hv : ‖v‖ = 1),
    (occupiedSpectrum U v).Finite ∧
      (occupiedSpectrum U v).ncard = Module.finrank ℂ (cyclicSpace U v) ∧
      HasSum (fun n : ℕ => R.readout () ⟨E, U, v⟩ n)
        ((occupiedSpectrum U v).ncard : ℝ) ∧
      HasSum (fun n : ℕ => returnProbability U v (n + 1)) 1

private abbrev WitnessSpace := EuclideanSpace ℂ (ULift.{u} Unit)
private def witnessUnitary : WitnessSpace.{u} ≃ₗᵢ[ℂ] WitnessSpace.{u} :=
  LinearIsometryEquiv.refl ℂ _
private def witnessVector : WitnessSpace.{u} := WithLp.toLp 2 (fun _ => (1 : ℂ))

private theorem witness_norm : ‖witnessVector.{u}‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [witnessVector]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨_, hcard, hsum, _⟩ := h witnessUnitary witnessVector witness_norm
  have hz : ((occupiedSpectrum witnessUnitary witnessVector).ncard : ℝ) = 0 :=
    hsum.unique (by simpa [rejected, realize] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0))
  rw [hcard] at hz
  have hd : Module.finrank ℂ (cyclicSpace witnessUnitary witnessVector) = 0 :=
    Nat.cast_eq_zero.mp hz
  haveI : Subsingleton (cyclicSpace witnessUnitary witnessVector) := Module.finrank_zero_iff.mp hd
  have hvzero : witnessVector.{u} = 0 :=
    congrArg Subtype.val (Subsingleton.elim
      (⟨witnessVector, initial_mem witnessUnitary witnessVector⟩ :
        cyclicSpace witnessUnitary witnessVector) 0)
  have hn := witness_norm.{u}
  rw [hvzero, norm_zero] at hn
  exact zero_ne_one hn

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let p : Scope.{u} := ⟨WitnessSpace, witnessUnitary, witnessVector⟩
  refine ⟨p, 0, 1, ?_⟩
  have hvinner : inner ℂ witnessVector.{u} witnessVector = 1 := by
    rw [inner_self_eq_norm_sq_to_K, witness_norm]
    norm_num
  have ht : monitoredStep witnessUnitary.{u} witnessVector.{u} witnessVector.{u} = 0 := by
    change witnessVector.{u} - (ℂ ∙ witnessVector.{u}).starProjection witnessVector.{u} = 0
    rw [Submodule.starProjection_singleton, witness_norm, hvinner]
    simp
  intro he
  have h1 : returnProbability witnessUnitary.{u} witnessVector.{u} 1 = 1 := by
    change ‖inner ℂ witnessVector.{u} witnessVector.{u}‖ ^ 2 = 1
    rw [hvinner]
    norm_num
  have h2 : returnProbability witnessUnitary.{u} witnessVector.{u} 2 = 0 := by
    change ‖inner ℂ witnessVector.{u}
      (witnessUnitary.{u} (monitoredStep witnessUnitary.{u} witnessVector.{u} witnessVector.{u}))‖ ^ 2 = 0
    rw [ht, map_zero, inner_zero_right, norm_zero, zero_pow (by decide)]
  have hh : (1 : ℝ) = 0 := by simpa [actual, realize, p, h1, h2] using he
  exact one_ne_zero hh

def family : Registration arena.{u} (type_of% (@monitored_spectral_mean.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@monitored_spectral_mean.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@monitored_spectral_mean.{u}) (Realization signature.{u}) (Type) Unit where
  unitName := `Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredSpectralMean.unit
  realizationName := `Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredSpectralMean.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => (n + 1 : ℝ) * returnProbability p.U p.v (n + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredSpectralMean
