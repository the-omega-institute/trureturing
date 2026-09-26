import D5.S3.Estimation.TimeArrow.ParityKernelCharpoly
import Reg.Support.ParityKernelRegistrationTemplates
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates
open _root_.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
open _root_.D5.S3.Estimation.TimeArrow.ParityKernelCharpoly
open LeanInformationAudit Polynomial
open Lean Elab Command

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.ParityKernelCharpoly

run_cmd do
  let root := `Reg.D5.S3.Estimation.TimeArrow.ParityKernelCharpoly
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := `D5.S3.Estimation.TimeArrow.ParityKernelCharpoly ++ `charpoly_parityKernel
    statementIdentity := "sha256:a7349ba2cc96237f3540bb0b9201af38c32aa6f8374255558b6d0ae77b9b43f7"
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

def actual : Realization profileCharpolySignature :=
  realize profileCharpolySignature
    (fun _ d a => ((Matrix.of fun x y => parityKernel (d := d) a x y).charpoly : Polynomial ℝ))
    (fun e => nomatch e)

def rejected : Realization profileCharpolySignature :=
  realize profileCharpolySignature (fun _ _ _ => (0 : Polynomial ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := profileCharpolySignature
  Law R := ∀ {d : ℕ} (_hd : 1 ≤ d) (a : (Fin d → ℤˣ) → ℝ) (_ha : ∑ y, a y = 0)
    (_hχa : ∑ y, parity y * a y = 0),
    R.readout () d a = ((X - 1) * X ^ (2 ^ d - 1) : Polynomial ℝ)

/-- On the zero-dimensional cube the kernel is the scalar `1 + a(pt)`. -/
theorem actual_zero (a : (Fin 0 → ℤˣ) → ℝ) :
    actual.readout () 0 a = (X - C (1 + a default) : Polynomial ℝ) := by
  change (Matrix.of fun x y => parityKernel (d := 0) a x y).charpoly = _
  rw [Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq]
  simp [parityKernel, parity]
  exact congrArg a (Subsingleton.elim _ _)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have := h (d := 1) le_rfl (fun _ => 0) (by simp) (by simp)
  change (0 : Polynomial ℝ) = _ at this
  have hev := congrArg (Polynomial.eval 2) this
  norm_num at hev

theorem sensitivity_proof : Sensitivity arena actual := by
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

theorem dependence_proof : ObservationalDependence profileCharpolySignature actual := by
  intro i
  refine ⟨(0 : ℕ), (fun _ => 0 : (Fin 0 → ℤˣ) → ℝ), (fun _ => 1 : (Fin 0 → ℤˣ) → ℝ), ?_⟩
  cases i
  rw [actual_zero, actual_zero]
  intro h
  have h' : (X - C (1 + 0) : Polynomial ℝ) = X - C (1 + 1) := h
  have hev := congrArg (Polynomial.eval 0) h'
  norm_num at hev

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun hd a ha hχa => charpoly_parityKernel hd a ha hχa, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem charpoly_parityKernel in arena
  readout via (realize profileCharpolySignature
    (fun _ d a => ((Matrix.of fun x y => parityKernel (d := d) a x y).charpoly : Polynomial ℝ))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.ParityKernelCharpoly
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

run_cmd LeanInformationAudit.validateRegistrySnapshot (← getEnv)

end Reg.D5.S3.Estimation.TimeArrow.ParityKernelCharpoly
