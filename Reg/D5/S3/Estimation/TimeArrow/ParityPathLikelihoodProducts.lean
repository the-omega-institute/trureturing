import LeanInformationAuditInterface.Contract.Registration
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product) (type_of% (forwardArena)) (type_of% (forwardArena)) (type_of% (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * forwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "ParityPathLikelihoodProducts") "forward_inner_product") "Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts/Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardRegistration,
  realizationSource := none,
  generated := false,
  arena := ⟨(forwardArena)⟩,
  objectArena := ⟨(forwardArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (forwardArena) ⟨(forwardRegistration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * forwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


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

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product) (type_of% (backwardArena)) (type_of% (backwardArena)) (type_of% (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => backwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "ParityPathLikelihoodProducts") "backward_inner_product") "Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts/Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardRegistration,
  realizationSource := none,
  generated := false,
  arena := ⟨(backwardArena)⟩,
  objectArena := ⟨(backwardArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (backwardArena) ⟨(backwardRegistration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => backwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


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

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product) (type_of% (mixedArena)) (type_of% (mixedArena)) (type_of% (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "ParityPathLikelihoodProducts") "forward_backward_inner_product") "Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts/Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedRegistration,
  realizationSource := none,
  generated := false,
  arena := ⟨(mixedArena)⟩,
  objectArena := ⟨(mixedArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (mixedArena) ⟨(mixedRegistration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, definition := none, coordinates := #[0, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


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
