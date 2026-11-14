import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the all-length canonical unit-phase inverse. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality

open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection (Word)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Parameter)
    (fun m => Word (3 + m) → ℂ)

def actual : Realization signature :=
  realize signature (fun _ m θ => state (3 + m) θ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) {θ η : Parameter},
    θ ∈ canonicalChart m → η ∈ canonicalChart m →
    ∀ ζ : ℂ, ‖ζ‖ = 1 → R.readout () m η = ζ • state (3 + m) θ → θ = η

def originalStatement : Prop :=
  ∀ (m : ℕ) {θ η : Parameter},
    θ ∈ canonicalChart m → η ∈ canonicalChart m →
    ∀ ζ : ℂ, ‖ζ‖ = 1 → state (3 + m) η = ζ • state (3 + m) θ → θ = η

private lemma distinct_chart_parameters :
    ∃ θ ∈ canonicalChart 0, ∃ η ∈ canonicalChart 0, θ ≠ η := by
  obtain ⟨θ, hθ, η, hη, hne, _⟩ := record_collision 1
    (isOpen_canonicalChart 0) (canonicalChart_nonempty 0)
  exact ⟨θ, hθ, η, hη, hne⟩

private def θ₀ : Parameter := Classical.choose distinct_chart_parameters

def rejected : Realization signature :=
  realize signature (fun _ m _ => state (3 + m) θ₀) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hθ := (Classical.choose_spec distinct_chart_parameters).1
  have hη := (Classical.choose_spec (Classical.choose_spec distinct_chart_parameters).2).1
  have hne := (Classical.choose_spec (Classical.choose_spec distinct_chart_parameters).2).2
  exact hne (h 0 hθ hη 1 (by simp) (by simp [rejected, realize, θ₀]))

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (![0, 1, 0, 0, 1], 1, 0), (![0, 1, 0, 0, 1], 2, 0), ?_⟩
  intro h
  have hh := congrFun h ![0, 0, 0]
  norm_num [actual, realize, state, left, core, right,
    _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.mpsState,
    List.ofFn_succ, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh

theorem source_equivalence : originalStatement ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := by
  intro m θ η hθ hη ζ hζ heq
  exact phase_rigidity m hθ hη ζ hζ heq

set_option maxHeartbeats 1600000 in
-- The complete dependent source telescope is checked against the typed family law.
def source_registration : Registration arena originalStatement where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@phase_rigidity) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m θ => state (3 + m) θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace NonemptyChart

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Set Parameter) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ U => U.Nonempty) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, R.readout () m (canonicalChart m)

def originalStatement : Prop := ∀ m : ℕ, (canonicalChart m).Nonempty

theorem rejected_law : ¬ arena.Law rejected := fun h => h 0

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, ∅, Set.univ, ?_⟩
  change (∅ : Set Parameter).Nonempty ≠ (Set.univ : Set Parameter).Nonempty
  simp

def source_registration : Registration arena originalStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨canonicalChart_nonempty, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@canonicalChart_nonempty) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.NonemptyChart.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.NonemptyChart.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ U => U.Nonempty) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end NonemptyChart

namespace OpenCollision

abbrev signature := NonemptyChart.signature

def actual : Realization signature :=
  realize signature (fun _ _ U => U.Nonempty) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) {U : Set Parameter}, IsOpen U → R.readout () m U →
    U ⊆ canonicalChart m →
    ∃ ψ ∈ state (2 + (1 + m)) '' U, ∃ φ ∈ state (2 + (1 + m)) '' U,
      ψ ∈ _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (2 + (1 + m)) ∧
      φ ∈ _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (2 + (1 + m)) ∧
      _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m) ψ =
        _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m) φ ∧
      ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ φ = ζ • ψ

def originalStatement : Prop := ∀ (m : ℕ) {U : Set Parameter}, IsOpen U → U.Nonempty →
    U ⊆ canonicalChart m →
    ∃ ψ ∈ state (2 + (1 + m)) '' U, ∃ φ ∈ state (2 + (1 + m)) '' U,
      ψ ∈ _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (2 + (1 + m)) ∧
      φ ∈ _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (2 + (1 + m)) ∧
      _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m) ψ =
        _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m) φ ∧
      ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ φ = ζ • ψ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ψ, hψ, _⟩ := h 0 (U := ∅) isOpen_empty trivial (Set.empty_subset _)
  simpa using hψ

theorem dependence : ObservationalDependence signature actual := NonemptyChart.dependence

def source_registration : Registration arena originalStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨open_subchart_collision, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@open_subchart_collision) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.OpenCollision.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality.OpenCollision.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ U => U.Nonempty) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end OpenCollision

#print axioms registration

end
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
