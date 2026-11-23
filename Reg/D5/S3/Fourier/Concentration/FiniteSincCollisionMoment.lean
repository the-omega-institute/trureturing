import Reg.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

/-! The bounded-start window uses the finite sine score on the original time orbit. -/

namespace Reg.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open FiniteSineMissingWindow (sensitivity)
open FiniteTailMomentMissingWindow (tailSignature tailActual)
open LeanInformationAudit Finset Set

noncomputable section

universe u

private def rejected : Realization tailSignature.{u} :=
  realize tailSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev boundedArena : Arena where
  signature := tailSignature.{u}
  Law V := ∀ {J : Type u} [i : Fintype J] [DecidableEq J] (g w : J → ℝ)
    (_ : ∀ j, 0 ≤ w j) (p : ℕ) {L H h δ : ℝ}
    (_ : 0 < L) (_ : 0 < h) (_ : 0 ≤ δ)
    (_ : 7 * ((⌊H / h⌋₊ : ℝ) + 1) * tailCollisionMass g w p (2 / L) < δ ^ (2 * p))
    (A : ℝ), ∃ b ∈ Ioo A (A + 2 * L), ∀ t ∈ Icc b (b + H),
      V.readout () ⟨J, i, g, w⟩ t < δ + h * ∑ j, w j * |g j|

private theorem rejected_law : ¬ boundedArena.{u}.Law rejected := by
  intro law
  have hbudget : (7 : ℝ) * ((⌊(1 : ℝ) / 1⌋₊ : ℝ) + 1) *
      tailCollisionMass (J := PEmpty.{u + 1}) 0 0 1 (2 / 1) < 1 ^ (2 * (1 : ℕ)) := by
    have hempty : Finset.piAntidiag (Finset.univ : Finset PEmpty.{u + 1}) 1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      simpa using (Finset.mem_piAntidiag.mp hm).1
    unfold tailCollisionMass
    rw [hempty]
    change (7 : ℝ) * ((⌊(1 : ℝ) / 1⌋₊ : ℝ) + 1) * 0 < 1 ^ (2 * (1 : ℕ))
    norm_num
  obtain ⟨b, _, hb⟩ := law (J := PEmpty.{u + 1}) 0 0 (by simp) 1
    (L := 1) (H := 1) (h := 1) (δ := 1) zero_lt_one zero_lt_one zero_le_one hbudget 0
  have h := hb b ⟨le_rfl, by linarith⟩
  simp [rejected, realize] at h

private theorem dependence : ObservationalDependence tailSignature.{u} tailActual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, 1, 1⟩, 0, Real.pi / 2, ?_⟩
  simp [tailActual, realize, Real.sin_pi_div_two]

def boundedEvidence :
    Registration boundedArena.{u} (type_of% @exists_bounded_tail_window.{u}) where
  actual := tailActual
  bridge := Iff.rfl
  variation := ⟨@exists_bounded_tail_window.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity boundedArena.Law tailActual rejected rejected_law
  dependence := dependence

def boundedRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_bounded_tail_window.{u}) (Realization tailSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment.boundedUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment.boundedEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨boundedArena.{u}⟩
  objectArena := .source ⟨boundedArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundedArena.{u} ⟨boundedEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tailSignature
    (fun _ q t => @Finset.sum q.1 ℝ _ (@Finset.univ q.1 q.2.1)
      (fun j => q.2.2.2 j * Real.sin (q.2.2.1 j * t)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
    definition := none
    coordinates := #[0, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 17
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms boundedRegistration

end
end Reg.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
