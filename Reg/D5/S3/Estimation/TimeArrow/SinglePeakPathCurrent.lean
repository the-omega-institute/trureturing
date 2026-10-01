import D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
import Reg.Support.PathCurrentRegistrationTemplates
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.PathCurrentRegistrationTemplates
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
open LeanInformationAudit
open Lean Elab Command

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent

universe u

def actual : Realization signedPeakPathSignature.{u} :=
  realize signedPeakPathSignature.{u}
    (fun _ p x => Real.log
      (forwardLaw (kernel p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2 /
        reverseLaw (kernel p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2))
    (fun e => nomatch e)

def rejected : Realization signedPeakPathSignature.{u} :=
  realize signedPeakPathSignature.{u} (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signedPeakPathSignature.{u}
  Law R := ∀ {X : Type u} (χ : X → ℝ) (_hχ : ∀ x, χ x = 1 ∨ χ x = -1) (z : X) (_hz : χ z = 1)
    (r q N : ℝ) (_hr : |r| < 1) (_hq : |q| < 1) (_hN : 0 < N) (T : ℕ) (x : ℕ → X),
    R.readout () ⟨X, χ, z, r, q, N, T⟩ x =
      (Real.log ((1 + r) / (1 - q)) + Real.log (1 + q) - Real.log (1 - r)) *
          ((transitions (region χ z) x T Region.opposite Region.peak : ℝ) -
            (transitions (region χ z) x T Region.peak Region.opposite : ℝ)) +
        Real.log ((1 + r) / (1 - q)) * endpointDefect (region χ z) x T Region.peak -
          Real.log (1 + q) * endpointDefect (region χ z) x T Region.opposite

run_cmd do
  let root := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
  let sourceName := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent ++
    `log_forward_div_reverse_eq_current
  let identity := "sha256:9fe0bf0ee41c6c4aa060ac168ffce94a11bf8a412657c49411610c9ce698f7de"
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := identity
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

/-- The two-state sign space used for the rejected intervention and the dependence witness. -/
def sign (b : ULift.{u} Bool) : ℝ := if b.down then 1 else -1

def peakPath : ℕ → ULift.{u} Bool := fun t => if t = 0 then ⟨false⟩ else ⟨true⟩

def restPath : ℕ → ULift.{u} Bool := fun _ => ⟨true⟩

theorem sign_cases (b : ULift.{u} Bool) : sign b = 1 ∨ sign b = -1 := by
  cases b with | up b => cases b <;> simp [sign]

theorem sign_peak : sign (⟨true⟩ : ULift.{u} Bool) = 1 := by simp [sign]

theorem region_false :
    region sign (⟨true⟩ : ULift.{u} Bool) ⟨false⟩ = Region.opposite := by
  simp [region, sign]
  norm_num

theorem region_true : region sign (⟨true⟩ : ULift.{u} Bool) ⟨true⟩ = Region.peak := by
  simp [region]

/-- A single opposite-to-peak step carries log-likelihood `-log (1 - r) = log 2` at `r = 1/2`. -/
theorem peakPath_value :
    actual.{u}.readout () ⟨ULift.{u} Bool, sign, ⟨true⟩, 1 / 2, 0, 1, 1⟩ peakPath =
      Real.log 2 := by
  have h := log_forward_div_reverse_eq_current (sign : ULift.{u} Bool → ℝ) sign_cases ⟨true⟩
    sign_peak (1 / 2) 0 1 (by norm_num [abs_of_pos]) (by norm_num) one_pos 1 peakPath
  have h0 : peakPath.{u} 0 = ⟨false⟩ := rfl
  have h1 : peakPath.{u} 1 = ⟨true⟩ := rfl
  have ht1 : transitions (region sign (⟨true⟩ : ULift.{u} Bool)) peakPath 1 Region.opposite
      Region.peak = 1 := by
    simp [transitions, Finset.filter_singleton, h0, h1, region_false, region_true]
  have ht2 : transitions (region sign (⟨true⟩ : ULift.{u} Bool)) peakPath 1 Region.peak
      Region.opposite = 0 := by
    simp [transitions, Finset.filter_singleton, h0, h1, region_false, region_true]
  have he1 : endpointDefect (region sign (⟨true⟩ : ULift.{u} Bool)) peakPath 1 Region.peak =
      -1 := by
    simp [endpointDefect, h0, h1, region_false, region_true]
  have he2 : endpointDefect (region sign (⟨true⟩ : ULift.{u} Bool)) peakPath 1
      Region.opposite = 1 := by
    simp [endpointDefect, h0, h1, region_false, region_true]
  change Real.log _ = _
  rw [h, ht1, ht2, he1, he2]
  have hhalf : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
  rw [hhalf, Real.log_inv]
  simp

theorem restPath_value :
    actual.{u}.readout () ⟨ULift.{u} Bool, sign, ⟨true⟩, 1 / 2, 0, 1, 1⟩ restPath =
      (0 : ℝ) := by
  have h := log_forward_div_reverse_eq_current (sign : ULift.{u} Bool → ℝ) sign_cases ⟨true⟩
    sign_peak (1 / 2) 0 1 (by norm_num [abs_of_pos]) (by norm_num) one_pos 1 restPath
  have h0 : restPath.{u} 0 = ⟨true⟩ := rfl
  have h1 : restPath.{u} 1 = ⟨true⟩ := rfl
  change Real.log _ = _
  rw [h]
  simp [transitions, endpointDefect, Finset.filter_singleton, h0, h1, region_true]

theorem log_two_ne_zero' : Real.log 2 ≠ 0 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  exact this.ne'

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hlaw := h (X := ULift.{u} Bool) sign sign_cases ⟨true⟩ sign_peak (1 / 2) 0 1
    (by norm_num [abs_of_pos]) (by norm_num) one_pos 1 peakPath
  have hact := log_forward_div_reverse_eq_current (sign : ULift.{u} Bool → ℝ) sign_cases ⟨true⟩
    sign_peak
    (1 / 2) 0 1 (by norm_num [abs_of_pos]) (by norm_num) one_pos 1 peakPath
  have hv := peakPath_value.{u}
  change Real.log _ = _ at hv
  change (0 : ℝ) = _ at hlaw
  rw [← hact, hv] at hlaw
  exact log_two_ne_zero' hlaw.symm

theorem sensitivity_proof : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem dependence_proof :
    ObservationalDependence signedPeakPathSignature.{u} actual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} Bool, sign, ⟨true⟩, 1 / 2, 0, 1, 1⟩, peakPath, restPath, ?_⟩
  cases i
  rw [peakPath_value, restPath_value]
  exact log_two_ne_zero'

def registration : Registration arena.{u} (arena.{u}.Law actual.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun χ hχ z hz r q N hr hq hN T x =>
      log_forward_div_reverse_eq_current χ hχ z hz r q N hr hq hN T x,
    rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem log_forward_div_reverse_eq_current in arena
  readout via (realize signedPeakPathSignature.{u}
    (fun _ p x => Real.log
      (forwardLaw (kernel p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2 /
        reverseLaw (kernel p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1) p.2.2.2.2.2.1 x
          p.2.2.2.2.2.2))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
    coordinates := #[0, 1, 3, 5, 6, 7, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 12 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
