import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum
import Reg.Support.DependentFamily

/-! Source-bound audit of spectral zero for lattice Lindbladians. -/

namespace Reg.D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum

open _root_.D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum
open _root_.D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev Operator := ObserverHilbertSpace (ℤ × ℤ) →L[ℂ] ObserverHilbertSpace (ℤ × ℤ)

/-- Observe the spectrum of the operator supplied by the existential conclusion. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Operator
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => spectrum ℂ t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

/-- Retain every parameter, hypothesis, prescribed entry, and spectral membership. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (_hf : IsFiniteRange r h ℓ) (_ht : IsTranslationInvariant h ℓ),
    ∃ t : Operator,
      (∀ ρ : ObserverHilbertSpace (ℤ × ℤ), ∀ x y,
        t ρ (x, y) = lindbladEntry g h ℓ ρ x y) ∧
      (0 : ℂ) ∈ R.readout () () t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨t, _, hzero⟩ := law 0 0 (fun _ _ => 0) (fun _ _ _ => 0)
    ⟨by intros; rfl, by intros; rfl⟩ ⟨by intros; rfl, by intros; rfl⟩
  exact hzero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let v : ObserverHilbertSpace (ℤ × ℤ) := lp.single 2 (0, 0) 1
  have hv : v ≠ 0 := by
    intro hz
    have he := congrArg (fun ρ : ObserverHilbertSpace (ℤ × ℤ) => ρ (0, 0)) hz
    simpa [v] using he
  letI : Nontrivial (ObserverHilbertSpace (ℤ × ℤ)) := ⟨⟨v, 0, hv⟩⟩
  refine ⟨(), (0 : Operator), (1 : Operator), ?_⟩
  change spectrum ℂ (0 : Operator) ≠ spectrum ℂ (1 : Operator)
  intro heq
  have hz : (0 : ℂ) ∈ spectrum ℂ (0 : Operator) :=
    (spectrum.zero_mem_iff ℂ).mpr not_isUnit_zero
  rw [heq] at hz
  exact (spectrum.zero_notMem ℂ isUnit_one) hz

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum.unit
  realizationName :=
    `Reg.D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => spectrum ℂ t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum
