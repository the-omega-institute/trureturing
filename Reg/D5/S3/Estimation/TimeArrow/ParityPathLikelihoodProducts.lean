import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
import Reg.Support.ParityKernelRegistrationTemplates
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product) (type_of% (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * forwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "ParityPathLikelihoodProducts") "forward_inner_product") "Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts/Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(forwardArena)⟩,
  objectArena := .source ⟨(forwardArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (forwardArena) ⟨(forwardRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * forwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.observationFact0, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.anchorEnumeration }


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

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product) (type_of% (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => backwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "ParityPathLikelihoodProducts") "backward_inner_product") "Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts/Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(backwardArena)⟩,
  objectArena := .source ⟨(backwardArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (backwardArena) ⟨(backwardRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => backwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.canonicalArenaFact, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.sourceBridgeFact, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.observationFact0, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.anchorEnumeration }


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

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product) (type_of% (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "TimeArrow") "ParityPathLikelihoodProducts") "forward_backward_inner_product") "Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts/Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(mixedArena)⟩,
  objectArena := .source ⟨(mixedArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (mixedArena) ⟨(mixedRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} profilePairStepSignature
    (fun _ p s => (uniformPathMean s
      (fun x => forwardLikelihood p.2.1 s x * backwardLikelihood p.2.2 s x) : ℝ))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, definition := none, coordinates := #[0, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.canonicalArenaFact, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.sourceBridgeFact, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.observationFact0, `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.anchorEnumeration }


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


noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardArena
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardArena
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardArena
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardArena
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedArena
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedArena
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardArena) (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardRegistration).actual

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"backward_inner_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardRegistration).bridge

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.observation0 : {d : Nat} →
  (a b : (Fin d → @Units.{0} Int Int.instMonoid) → Real) →
    (ha :
        @Eq.{1} Real
          (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
            (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
              (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid) (instDecidableEqFin d)
                (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
            fun (y : Fin d → @Units.{0} Int Int.instMonoid) => a y)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
      (hb :
          @Eq.{1} Real
            (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
              (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
                (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid)
                  (instDecidableEqFin d) (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
              fun (y : Fin d → @Units.{0} Int Int.instMonoid) => b y)
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
        (s : Nat) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates.profilePairStepSignature
            PUnit.unit.{1}
            (@Sigma.mk.{0, 0} Nat
              (fun (d : Nat) =>
                @Sigma.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
                  fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
                  (Fin d → @Units.{0} Int Int.instMonoid) → Real)
              d
              (@Sigma.mk.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
                (fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
                  (Fin d → @Units.{0} Int Int.instMonoid) → Real)
                a b)) :=
  fun {d : Nat} (a b : (Fin d → @Units.{0} Int Int.instMonoid) → Real)
    (ha :
      @Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
          (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
            (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid) (instDecidableEqFin d)
              (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
          fun (y : Fin d → @Units.{0} Int Int.instMonoid) => a y)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (hb :
      @Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
          (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
            (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid) (instDecidableEqFin d)
              (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
          fun (y : Fin d → @Units.{0} Int Int.instMonoid) => b y)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (s : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates.profilePairStepSignature
    Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (d : Nat) =>
        @Sigma.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
          fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) => (Fin d → @Units.{0} Int Int.instMonoid) → Real)
      d
      (@Sigma.mk.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
        (fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) => (Fin d → @Units.{0} Int Int.instMonoid) → Real) a
        b))
    s

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"backward_inner_product\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"backward_inner_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardRegistration).actual (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardRegistration).variation.2.choose (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardRegistration).variation.1 (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"backwardRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardArena) (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardRegistration).actual

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"forward_inner_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardRegistration).bridge

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.observation0 : {d : Nat} →
  (a b : (Fin d → @Units.{0} Int Int.instMonoid) → Real) →
    (ha :
        @Eq.{1} Real
          (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
            (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
              (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid) (instDecidableEqFin d)
                (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
            fun (y : Fin d → @Units.{0} Int Int.instMonoid) => a y)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
      (hb :
          @Eq.{1} Real
            (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
              (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
                (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid)
                  (instDecidableEqFin d) (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
              fun (y : Fin d → @Units.{0} Int Int.instMonoid) => b y)
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
        (s : Nat) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates.profilePairStepSignature
            PUnit.unit.{1}
            (@Sigma.mk.{0, 0} Nat
              (fun (d : Nat) =>
                @Sigma.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
                  fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
                  (Fin d → @Units.{0} Int Int.instMonoid) → Real)
              d
              (@Sigma.mk.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
                (fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
                  (Fin d → @Units.{0} Int Int.instMonoid) → Real)
                a b)) :=
  fun {d : Nat} (a b : (Fin d → @Units.{0} Int Int.instMonoid) → Real)
    (ha :
      @Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
          (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
            (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid) (instDecidableEqFin d)
              (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
          fun (y : Fin d → @Units.{0} Int Int.instMonoid) => a y)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (hb :
      @Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
          (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
            (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid) (instDecidableEqFin d)
              (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
          fun (y : Fin d → @Units.{0} Int Int.instMonoid) => b y)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (s : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates.profilePairStepSignature
    Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (d : Nat) =>
        @Sigma.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
          fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) => (Fin d → @Units.{0} Int Int.instMonoid) → Real)
      d
      (@Sigma.mk.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
        (fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) => (Fin d → @Units.{0} Int Int.instMonoid) → Real) a
        b))
    s

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"forward_inner_product\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"forward_inner_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardRegistration).actual (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardRegistration).variation.2.choose (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardRegistration).variation.1 (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"forwardRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedArena) (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedRegistration).actual

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"forward_backward_inner_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedRegistration).bridge

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.observation0 : {d : Nat} →
  (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d) →
    (a b : (Fin d → @Units.{0} Int Int.instMonoid) → Real) →
      (hb :
          @Eq.{1} Real
            (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
              (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
                (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid)
                  (instDecidableEqFin d) (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
              fun (y : Fin d → @Units.{0} Int Int.instMonoid) => b y)
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
        (hχb :
            @Eq.{1} Real
              (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
                (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
                  (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid)
                    (instDecidableEqFin d) (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
                fun (y : Fin d → @Units.{0} Int Int.instMonoid) =>
                @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parity d y) (b y))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
          (s : Nat) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates.profilePairStepSignature
              PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Nat
                (fun (d : Nat) =>
                  @Sigma.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
                    fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
                    (Fin d → @Units.{0} Int Int.instMonoid) → Real)
                d
                (@Sigma.mk.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
                  (fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) =>
                    (Fin d → @Units.{0} Int Int.instMonoid) → Real)
                  a b)) :=
  fun {d : Nat} (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
    (a b : (Fin d → @Units.{0} Int Int.instMonoid) → Real)
    (hb :
      @Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
          (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
            (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid) (instDecidableEqFin d)
              (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
          fun (y : Fin d → @Units.{0} Int Int.instMonoid) => b y)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (hχb :
      @Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin d → @Units.{0} Int Int.instMonoid) Real Real.instAddCommMonoid
          (@Finset.univ.{0} (Fin d → @Units.{0} Int Int.instMonoid)
            (@Pi.instFintype.{0, 0} (Fin d) (fun (a : Fin d) => @Units.{0} Int Int.instMonoid) (instDecidableEqFin d)
              (Fin.fintype d) fun (a : Fin d) => UnitsInt.fintype))
          fun (y : Fin d → @Units.{0} Int Int.instMonoid) =>
          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates.parity d y) (b y))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (s : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates.profilePairStepSignature
    Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (d : Nat) =>
        @Sigma.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
          fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) => (Fin d → @Units.{0} Int Int.instMonoid) → Real)
      d
      (@Sigma.mk.{0, 0} ((Fin d → @Units.{0} Int Int.instMonoid) → Real)
        (fun (x : (Fin d → @Units.{0} Int Int.instMonoid) → Real) => (Fin d → @Units.{0} Int Int.instMonoid) → Real) a
        b))
    s

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"forward_backward_inner_product\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"forward_backward_inner_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedRegistration).actual (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedRegistration).variation.2.choose (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedRegistration).variation.1 (Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"TimeArrow\",\"ParityPathLikelihoodProducts\",\"mixedRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts, declaration := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
