import D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound
import Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction

/-! A dependent-family audit attempt for the complete strict-power statement. -/

open _root_.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction
open _root_.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound

open CyclicMonitoredContraction (Scope)

abbrev signature : Signature where
  Params := Scope.{u}
  State p := (p.E →L[ℂ] p.E) × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.E →L[ℂ] p.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => s.1 ^ s.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1),
    ∃ N : ℕ, 1 ≤ N ∧ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ‖R.readout () ⟨cyclicSpace U v⟩ (cyclicStep U v, N)‖ ≤ q

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  let U : E ≃ₗᵢ[ℂ] E := LinearIsometryEquiv.refl ℂ E
  let v : E := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hv : ‖v‖ = 1 := by
    change ‖(WithLp.toLp 2 (fun _ : ULift.{u} Unit => (1 : ℂ)) :
      EuclideanSpace ℂ (ULift.{u} Unit))‖ = 1
    rw [EuclideanSpace.norm_eq]
    simp
  have hvmem : v ∈ cyclicSpace U v := Submodule.subset_span ⟨0, rfl⟩
  have hvne : (⟨v, hvmem⟩ : cyclicSpace U v) ≠ 0 := by
    intro hz
    have hc := congrArg (fun z : cyclicSpace U v => (z : E) (ULift.up ())) hz
    simpa [v] using hc
  letI : Nontrivial (cyclicSpace U v) := ⟨⟨_, _, hvne⟩⟩
  obtain ⟨N, _, q, _, hq, hb⟩ := h U v hv
  have hone : (1 : ℝ) ≤ q := by simpa [rejected, realize] using hb
  exact (not_le_of_gt hq) hone

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  let p : Scope.{u} := ⟨E⟩
  refine ⟨p, (0, 1), (1, 1), ?_⟩
  intro he
  have hc := congrArg (fun T : E →L[ℂ] E =>
    (T (WithLp.toLp 2 (fun _ => (1 : ℂ)))) (ULift.up ())) he
  simpa [actual, realize] using hc

def family : Registration arena.{u} (type_of% (@cyclic_power_contraction.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_power_contraction.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cyclic_power_contraction.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound.unit
  realizationName := `Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 ^ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound
