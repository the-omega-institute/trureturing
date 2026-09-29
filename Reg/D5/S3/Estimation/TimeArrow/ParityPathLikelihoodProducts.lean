import D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
import Reg.Support.ParityKernelRegistrationTemplates
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates
open _root_.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
open _root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
open LeanInformationAudit
open Lean Elab Command

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts

run_cmd do
  let root := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
  let owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
  let fwdRow : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `forwardArena
    theoremName := owner ++ `forward_inner_product
    statementIdentity := "sha256:a891173e65cbf5af11a95ddf1a099bdec3a5eda44491c72a02b867ff47de6a7b"
    registrationModuleName := root }
  let bwdRow : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `backwardArena
    theoremName := owner ++ `backward_inner_product
    statementIdentity := "sha256:d49f17e68a06f102643e57b4c4f20e141fd73603830a548a891b99afc9e25075"
    registrationModuleName := root }
  let mixRow : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `mixedArena
    theoremName := owner ++ `forward_backward_inner_product
    statementIdentity := "sha256:b7882b0ca03e87b9976e128c5c7b46e0e307aa5758dd075b0f6ba9695fc5bd01"
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[fwdRow, bwdRow, mixRow], source := #[fwdRow, bwdRow, mixRow],
    companionPrefix := some root }

/-- On the zero-dimensional cube every path functional is its value on the unique path. -/
theorem uniformPathMean_zero (s : ℕ) (F : (Fin (s + 1) → Fin 0 → ℤˣ) → ℝ) :
    uniformPathMean s F = F default := by
  simp [uniformPathMean]
  congr 1
  exact Subsingleton.elim _ _

theorem parity_zero (y : Fin 0 → ℤˣ) : parity y = 1 := by simp [parity]

def rejected : Realization profilePairStepSignature :=
  realize profilePairStepSignature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

/-! ### Forward-forward -/

def forwardActual : Realization profilePairStepSignature :=
  realize profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * forwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e)

def forwardArena : Arena where
  signature := profilePairStepSignature
  Law R := ∀ {d : ℕ} (a b : (Fin d → ℤˣ) → ℝ) (_ha : ∑ y, a y = 0) (_hb : ∑ y, b y = 0)
    (s : ℕ), R.readout () ⟨d, a, b⟩ s = ((1 + (1 / 2 ^ d) * ∑ y, a y * b y) ^ s : ℝ)

theorem forwardActual_value (s : ℕ) :
    forwardActual.readout () ⟨0, fun _ => 1, fun _ => 1⟩ s = (4 : ℝ) ^ s := by
  change uniformPathMean s (fun x => forwardLikelihood (d := 0) (fun _ => 1) s x *
    forwardLikelihood (fun _ => 1) s x) = (4 : ℝ) ^ s
  rw [uniformPathMean_zero]
  simp only [forwardLikelihood, parityKernel, parity_zero, ← Finset.prod_mul_distrib]
  norm_num

theorem forward_rejected : ¬ forwardArena.Law rejected := by
  intro h
  have := h (d := 0) (fun _ => 0) (fun _ => 0) (by simp) (by simp) 0
  change (0 : ℝ) = _ at this
  norm_num at this

theorem forward_sensitivity : Sensitivity forwardArena forwardActual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, forward_rejected⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem forward_dependence : ObservationalDependence profilePairStepSignature forwardActual := by
  intro i
  refine ⟨⟨0, fun _ => 1, fun _ => 1⟩, (0 : ℕ), (1 : ℕ), ?_⟩
  cases i
  rw [forwardActual_value, forwardActual_value]
  intro h
  have h' : ((4 : ℝ) ^ 0) = 4 ^ 1 := h
  norm_num at h'

def forwardRegistration : Registration forwardArena (forwardArena.Law forwardActual) where
  actual := forwardActual
  bridge := Iff.rfl
  variation := ⟨fun a b ha hb s => forward_inner_product a b ha hb s, rejected,
    forward_rejected⟩
  sensitivity := forward_sensitivity
  dependence := forward_dependence

register_information_theorem forward_inner_product in forwardArena
  readout via (realize profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * forwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e))
  realizes forwardRegistration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

/-! ### Backward-backward -/

def backwardActual : Realization profilePairStepSignature :=
  realize profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => backwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e)

def backwardArena : Arena where
  signature := profilePairStepSignature
  Law R := ∀ {d : ℕ} (a b : (Fin d → ℤˣ) → ℝ) (_ha : ∑ y, a y = 0) (_hb : ∑ y, b y = 0)
    (s : ℕ), R.readout () ⟨d, a, b⟩ s = ((1 + (1 / 2 ^ d) * ∑ y, a y * b y) ^ s : ℝ)

theorem backwardActual_value (s : ℕ) :
    backwardActual.readout () ⟨0, fun _ => 1, fun _ => 1⟩ s = (4 : ℝ) ^ s := by
  change uniformPathMean s (fun x => backwardLikelihood (d := 0) (fun _ => 1) s x *
    backwardLikelihood (fun _ => 1) s x) = (4 : ℝ) ^ s
  rw [uniformPathMean_zero]
  simp only [backwardLikelihood, parityKernel, parity_zero, ← Finset.prod_mul_distrib]
  norm_num

theorem backward_rejected : ¬ backwardArena.Law rejected := by
  intro h
  have := h (d := 0) (fun _ => 0) (fun _ => 0) (by simp) (by simp) 0
  change (0 : ℝ) = _ at this
  norm_num at this

theorem backward_sensitivity : Sensitivity backwardArena backwardActual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, backward_rejected⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem backward_dependence : ObservationalDependence profilePairStepSignature backwardActual := by
  intro i
  refine ⟨⟨0, fun _ => 1, fun _ => 1⟩, (0 : ℕ), (1 : ℕ), ?_⟩
  cases i
  rw [backwardActual_value, backwardActual_value]
  intro h
  have h' : ((4 : ℝ) ^ 0) = 4 ^ 1 := h
  norm_num at h'

def backwardRegistration : Registration backwardArena (backwardArena.Law backwardActual) where
  actual := backwardActual
  bridge := Iff.rfl
  variation := ⟨fun a b ha hb s => backward_inner_product a b ha hb s, rejected,
    backward_rejected⟩
  sensitivity := backward_sensitivity
  dependence := backward_dependence

register_information_theorem backward_inner_product in backwardArena
  readout via (realize profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => backwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e))
  realizes backwardRegistration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

/-! ### Forward-backward -/

def mixedActual : Realization profilePairStepSignature :=
  realize profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e)

def mixedArena : Arena where
  signature := profilePairStepSignature
  Law R := ∀ {d : ℕ} (_hd : 1 ≤ d) (a b : (Fin d → ℤˣ) → ℝ) (_hb : ∑ y, b y = 0)
    (_hχb : ∑ y, parity y * b y = 0) (s : ℕ), R.readout () ⟨d, a, b⟩ s = (1 : ℝ)

theorem mixedActual_value (s : ℕ) :
    mixedActual.readout () ⟨0, fun _ => 1, fun _ => 1⟩ s = (4 : ℝ) ^ s := by
  change uniformPathMean s (fun x => forwardLikelihood (d := 0) (fun _ => 1) s x *
    backwardLikelihood (fun _ => 1) s x) = (4 : ℝ) ^ s
  rw [uniformPathMean_zero]
  simp only [forwardLikelihood, backwardLikelihood, parityKernel, parity_zero,
    ← Finset.prod_mul_distrib]
  norm_num

theorem mixed_rejected : ¬ mixedArena.Law rejected := by
  intro h
  have := h (d := 1) le_rfl (fun _ => 0) (fun _ => 0) (by simp) (by simp) 0
  change (0 : ℝ) = _ at this
  norm_num at this

theorem mixed_sensitivity : Sensitivity mixedArena mixedActual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, mixed_rejected⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem mixed_dependence : ObservationalDependence profilePairStepSignature mixedActual := by
  intro i
  refine ⟨⟨0, fun _ => 1, fun _ => 1⟩, (0 : ℕ), (1 : ℕ), ?_⟩
  cases i
  rw [mixedActual_value, mixedActual_value]
  intro h
  have h' : ((4 : ℝ) ^ 0) = 4 ^ 1 := h
  norm_num at h'

def mixedRegistration : Registration mixedArena (mixedArena.Law mixedActual) where
  actual := mixedActual
  bridge := Iff.rfl
  variation := ⟨fun hd a b hb hχb s => forward_backward_inner_product hd a b hb hχb s,
    rejected, mixed_rejected⟩
  sensitivity := mixed_sensitivity
  dependence := mixed_dependence

register_information_theorem forward_backward_inner_product in mixedArena
  readout via (realize profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e))
  realizes mixedRegistration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms forward_rejected
#print axioms forward_sensitivity
#print axioms forward_dependence
#print axioms backward_rejected
#print axioms backward_sensitivity
#print axioms backward_dependence
#print axioms mixed_rejected
#print axioms mixed_sensitivity
#print axioms mixed_dependence


end Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
