import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.WeightedPhaseRecurrence
import Reg.Support.DependentFamily

/-! The observation is the weighted loss at the time chosen in the source conclusion. -/

set_option autoImplicit false

namespace Reg.D5.S3.Fourier.WeightedPhaseRecurrence

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.WeightedPhaseRecurrence
open LeanInformationAudit Set
open scoped BigOperators

noncomputable section

universe u

abbrev signature : Signature where
  Params := Σ J : Type u, Σ _ : Fintype J, Σ _ : J → ℝ, Σ _ : J → ℝ, J → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ q t => @phaseLoss q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 t)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law readout := ∀ {J : Type u} [inst : Fintype J]
    (g θ p : J → ℝ) (N : ℕ) (ε δ a R : ℝ)
    (_hN : 0 < N) (_hp : ∀ j, 0 ≤ p j) (_hpsum : ∑ j, p j = 1)
    (_hε : 1 / (N : ℝ) < ε) (_hδ : 0 < δ) (_hR : 0 < R)
    (_hzero : ∀ k : J → ℤ, (∀ j, |k j| ≤ (N : ℤ)) →
      (∑ j, (k j : ℝ) * g j) = 0 → Real.cos (∑ j, (k j : ℝ) * θ j) = 1)
    (_hgap : ∀ k : J → ℤ, (∀ j, |k j| ≤ (N : ℤ)) →
      (∑ j, (k j : ℝ) * g j) ≠ 0 → δ ≤ |∑ j, (k j : ℝ) * g j|)
    (_hbudget : R * δ * (ε - 1 / (N : ℝ)) >
      2 * (ε * (N : ℝ) ^ Fintype.card J - (ε - 1 / (N : ℝ)))),
    ∃ t ∈ Icc a (a + R), readout.readout () ⟨J, inst, g, θ, p⟩ t < ε

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  let J := ULift.{u} Unit
  let j : J := ⟨()⟩
  have hsum (k : J → ℤ) : (∑ i, (k i : ℝ) * 1) = (k j : ℝ) := by
    rw [Fintype.sum_subsingleton _ j, mul_one]
  have hgap (k : J → ℤ) (hk : (∑ i, (k i : ℝ) * 1) ≠ 0) :
      (1 : ℝ) ≤ |∑ i, (k i : ℝ) * 1| := by
    rw [hsum] at hk ⊢
    have hi : k j ≠ 0 := fun hz => hk (by simp [hz])
    have hpos : 0 < |k j| := abs_pos.mpr hi
    exact_mod_cast (show (1 : ℤ) ≤ |k j| by omega)
  intro law
  obtain ⟨t, _, ht⟩ := law (fun _ : J => 1) (fun _ => 0) (fun _ => 1)
    2 1 1 0 8 (by norm_num) (fun _ => zero_le_one) (by simp [J])
    (by norm_num) zero_lt_one (by norm_num) (by simp)
    (fun k _ hk => hgap k hk) (by norm_num [J])
  simp [rejected, realize] at ht

private theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  let J := ULift.{u} Unit
  refine ⟨⟨J, inferInstance, fun _ => 1, fun _ => 0, fun _ => 1⟩, 0, Real.pi, ?_⟩
  change phaseLoss (fun _ : J => 1) (fun _ => 0) (fun _ => 1) 0 ≠
    phaseLoss (fun _ : J => 1) (fun _ => 0) (fun _ => 1) Real.pi
  norm_num [phaseLoss, J, Real.cos_pi]

def evidence : Registration arena.{u} (type_of% @weighted_phase_recurrence.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_phase_recurrence.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_phase_recurrence.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.WeightedPhaseRecurrence.unit
  realizationName := `Reg.D5.S3.Fourier.WeightedPhaseRecurrence.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q t => @phaseLoss q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedPhaseRecurrence
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      -- The source telescope, the witness binder, then the left operand of loss < ε.
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.WeightedPhaseRecurrence
