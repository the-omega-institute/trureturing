import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.LocalStatisticCutoffs

/-! The cutoff bound depends on the magnitude factor in front of the local tuple count. -/

namespace Reg.D5.S3.Fourier.Concentration.LocalStatisticCutoffs

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.LocalStatisticCutoffs
open _root_.Reg.Support
open Finset

noncomputable section

universe u

abbrev magnitudeSignature :=
  SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization magnitudeSignature :=
  realize magnitudeSignature (fun _ q m => m * ((q.2 - 1).descFactorial q.1 : ℝ))
    (fun e => nomatch e)

def rejected : Realization magnitudeSignature :=
  realize magnitudeSignature (fun _ q m => (m - 1) * ((q.2 - 1).descFactorial q.1 : ℝ))
    (fun e => nomatch e)

abbrev magnitudeArena : Arena where
  signature := magnitudeSignature
  Law v := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    {k D : ℕ} (s t : Finset J) (hs : s.Nonempty) (ht : t.Nonempty)
    (g : J → ℝ) (F : (Fin (k + 1) ↪ J) → ℝ) {R M : ℝ} (hM : 0 ≤ M)
    (hbounded : ∀ e, |F e| ≤ M)
    (hsupport : ∀ e, F e ≠ 0 → ∀ i, |g (e i) - g (e 0)| ≤ R)
    (hlocal : ∀ j ∈ s ∪ t, ((s ∪ t).filter fun x => |g x - g j| ≤ 2 * R).card ≤ D),
    let A (u : Finset J) := ∑ e : Fin (k + 1) ↪ J, if ∀ i, e i ∈ u then F e else 0
    let b := ((s \ t) ∪ (t \ s)).card
    let L := v.readout () ⟨k, D⟩ M
    |A s / s.card - A t / t.card| ≤
      min (L * (((k + 1 : ℕ) : ℝ) * b + |(s.card : ℝ) - t.card|) / max (s.card : ℝ) t.card)
        (2 * L)

private theorem rejected_law : ¬ magnitudeArena.{u}.Law rejected := by
  classical
  intro law
  let i : ULift.{u} Bool := ULift.up false
  let j : ULift.{u} Bool := ULift.up true
  have hne : i ≠ j := by decide
  have hlocal : ∀ x ∈ ({i} ∪ {j} : Finset (ULift.{u} Bool)),
      (({i} ∪ {j} : Finset (ULift.{u} Bool)).filter
        fun _ => |(0 : ℝ) - 0| ≤ 2 * 0).card ≤ 2 := by
    intro x hx
    simpa [hne] using card_filter_le ({i} ∪ {j} : Finset (ULift.{u} Bool))
      (fun _ => |(0 : ℝ) - 0| ≤ 2 * 0)
  have h := law (k := 0) (D := 2) {i} {j} (singleton_nonempty _) (singleton_nonempty _)
    (fun _ => 0) (fun _ => 0) (R := 0) (M := 0) le_rfl (by simp) (by simp) hlocal
  have hval : (rejected.readout () ⟨0, 2⟩ 0 : ℝ) = -1 := by
    change ((0 : ℝ) - 1) * (Nat.descFactorial (2 - 1) 0 : ℝ) = -1
    norm_num
  norm_num [hval, hne, Ne.symm hne] at h

private theorem magnitude_dependence : ObservationalDependence magnitudeSignature actual := by
  intro i
  cases i
  refine ⟨⟨0, 1⟩, 0, 1, ?_⟩
  change (0 : ℝ) * (Nat.descFactorial (1 - 1) 0 : ℝ) ≠
    1 * (Nat.descFactorial (1 - 1) 0 : ℝ)
  norm_num

def magnitudeEvidence :
    Registration magnitudeArena.{u} (type_of% @local_statistic_cutoff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_statistic_cutoff.{u}, rejected, rejected_law⟩
  sensitivity :=
    SingleDependentReadout.sensitivity magnitudeArena.Law actual rejected rejected_law
  dependence := magnitude_dependence

def magnitudeRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@local_statistic_cutoff.{u}) (Realization magnitudeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.LocalStatisticCutoffs.magnitudeUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.LocalStatisticCutoffs.magnitudeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨magnitudeArena.{u}⟩
  objectArena := .source ⟨magnitudeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source magnitudeArena.{u} ⟨magnitudeEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize magnitudeSignature (fun _ q m => m * ((q.2 - 1).descFactorial q.1 : ℝ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.LocalStatisticCutoffs
    definition := none
    coordinates := #[3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms magnitudeRegistration

end

end Reg.D5.S3.Fourier.Concentration.LocalStatisticCutoffs
