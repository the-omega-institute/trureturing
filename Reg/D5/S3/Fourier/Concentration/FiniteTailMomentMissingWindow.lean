import Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow
import D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow

/-! The finite sine score on the original time orbit is the observation. -/

namespace Reg.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open FiniteSineMissingWindow (oneRole sensitivity)
open LeanInformationAudit Finset Set

noncomputable section

universe u

abbrev tailSignature : Signature :=
  oneRole (Σ J : Type u, Σ _ : Fintype J, (J → ℝ) × (J → ℝ)) (fun _ => ℝ)

def tailActual : Realization tailSignature.{u} :=
  realize tailSignature
    (fun _ q t => @Finset.sum q.1 ℝ _ (@Finset.univ q.1 q.2.1)
      (fun j => q.2.2.2 j * Real.sin (q.2.2.1 j * t)))
    (fun e => nomatch e)

private def tailRejected : Realization tailSignature.{u} :=
  realize tailSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev tailArena : Arena where
  signature := tailSignature.{u}
  Law V := ∀ {J : Type u} [i : Fintype J] (g w : J → ℝ) (_ : ∀ j, 0 ≤ w j)
    (p : ℕ) (_ : 0 < p)
    (_ : ∀ k : J → ℤ, (∑ j, |k j|) ≤ (2 * p : ℤ) →
      (∑ j, (k j : ℝ) * g j) = 0 → k = 0)
    {H h δ : ℝ} (_ : 0 < h) (_ : 0 < δ),
    let squareMass := ∑ j, w j ^ 2
    squareMass = 0 ∨ ((⌊H / h⌋₊ : ℝ) + 1) * (2 * (p : ℝ) * squareMass / δ ^ 2) ^ p < 1 →
    ∀ A : ℝ, ∃ a > A, ∀ t ∈ Icc a (a + H),
      V.readout () ⟨J, i, g, w⟩ t < δ + h * ∑ j, w j * |g j|

private theorem tail_rejected : ¬ tailArena.{u}.Law tailRejected := by
  intro law
  have hshort (k : PEmpty.{u+1} → ℤ) :
      (∑ j, |k j|) ≤ (2 * (1 : ℕ) : ℤ) →
      (∑ j, (k j : ℝ) * 0) = 0 → k = 0 := fun _ _ => Subsingleton.elim _ _
  obtain ⟨a, _, ha⟩ := law (J := PEmpty.{u+1}) 0 0 (by simp) 1 Nat.one_pos hshort
    (H := 1) (h := 1) (δ := 1) zero_lt_one zero_lt_one (Or.inl (by simp)) 0
  have h := ha a ⟨le_rfl, by linarith⟩
  simp [tailRejected, realize] at h

private theorem tail_dependence : ObservationalDependence tailSignature.{u} tailActual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, 1, 1⟩, 0, Real.pi / 2, ?_⟩
  simp [tailActual, realize, Real.sin_pi_div_two]

def tailEvidence :
    Registration tailArena.{u} (type_of% @exists_arbitrarily_late_tail_window.{u}) where
  actual := tailActual
  bridge := Iff.rfl
  variation := ⟨@exists_arbitrarily_late_tail_window.{u}, tailRejected, tail_rejected⟩
  sensitivity := sensitivity tailArena.Law tailActual tailRejected tail_rejected
  dependence := tail_dependence

def tailRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_arbitrarily_late_tail_window.{u}) (Realization tailSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow.tailUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow.tailEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena.{u}⟩
  objectArena := .source ⟨tailArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena.{u} ⟨tailEvidence⟩
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
    owner := `D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
    definition := none
    coordinates := #[0, 2, 3]
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

#print axioms tailRegistration

end

end Reg.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
