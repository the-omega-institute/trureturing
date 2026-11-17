import D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction
import Mathlib.Analysis.InnerProductSpace.PiL2
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction

structure Scope where
  E : Type u
  [addE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℂ E]
  [finiteE : FiniteDimensional ℂ E]

attribute [instance] Scope.addE Scope.innerE Scope.finiteE

abbrev signature : Signature where
  Params := Scope.{u}
  State p := (p.E →L[ℂ] p.E) × (p.E →L[ℂ] p.E) × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Submodule ℂ p.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s =>
    LinearMap.ker (s.2.1.toLinearMap.comp (s.1.toLinearMap ^ s.2.2)))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : E ≃ₗᵢ[ℂ] E) (v : E),
    (⨅ n : ℕ, R.readout () ⟨cyclicSpace U v⟩
      (cyclicStep U v, cyclicClick U v, n)) = ⊥

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  let v : E := WithLp.toLp 2 (fun _ => (1 : ℂ))
  let U : E ≃ₗᵢ[ℂ] E := LinearIsometryEquiv.refl ℂ E
  have hv : v ∈ cyclicSpace U v := by
    exact Submodule.subset_span ⟨0, rfl⟩
  have heq := h U v
  have hx : (⟨v, hv⟩ : cyclicSpace U v) ∈ (⊥ : Submodule ℂ (cyclicSpace U v)) := by
    rw [← heq]
    simp [rejected, realize]
  have hz : (⟨v, hv⟩ : cyclicSpace U v) = 0 := hx
  have hc := congrArg (fun z : cyclicSpace U v => (z : E) (ULift.up ())) hz
  simp [v] at hc

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  let p : Scope.{u} := ⟨E⟩
  refine ⟨p, (0, 0, 0), (0, ContinuousLinearMap.id ℂ E, 0), ?_⟩
  intro heq
  let v : E := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hv : v ∈ actual.readout i p (0, 0, 0) := by
    simp [actual, realize]
  rw [heq] at hv
  have hz : v = 0 := by simpa [actual, realize] using hv
  have hc := congrArg (fun z : E => z (ULift.up ())) hz
  simp [v] at hc

def family : Registration arena.{u} (type_of% (@cyclic_future_kernel_eq_bot.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_future_kernel_eq_bot.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cyclic_future_kernel_eq_bot.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction.unit
  realizationName := `Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s =>
    LinearMap.ker (s.2.1.toLinearMap.comp (s.1.toLinearMap ^ s.2.2)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction
