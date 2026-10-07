import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Reg.Support.DependentFamily
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.BigOperators.Fin

open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

universe u v

abbrev chainZeroSignature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def chainZeroActual : Realization chainZeroSignature :=
  realize chainZeroSignature (fun _ L j => j + L) (fun e => nomatch e)

def chainZeroRejected : Realization chainZeroSignature :=
  realize chainZeroSignature (fun _ _ _ => 0) (fun e => nomatch e)

def chainZeroArena : Arena where
  signature := chainZeroSignature
  Law r := ∀ {R : Type u} [Semiring R] {n m : ℕ} {A : Mat R n n} {B : Mat R m m} {L : ℕ}
    (c : ExchangeChain R A B L), ∀ j : ℕ, B ^ j = 0 →
      A ^ (r.readout () L j) = 0

theorem chainZeroRejectedLaw : ¬ chainZeroArena.{u}.Law chainZeroRejected := by
  intro h
  let Z : Mat (ULift.{u} Nat) 1 1 := 0
  let c : ExchangeChain (ULift.{u} Nat) Z Z 0 := ExchangeChain.nil Z
  have hz := h c 1 (by simp [Z])
  have hentry := congrArg (fun M : Mat (ULift.{u} Nat) 1 1 => M 0 0) hz
  simp [Z, chainZeroRejected, realize] at hentry

def chainZeroRegistration : Registration chainZeroArena (chainZeroArena.Law chainZeroActual) where
  actual := chainZeroActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R _ n m A B L c j hj
    simpa [chainZeroActual, realize] using chain_zero_power c j hj,
    chainZeroRejected, chainZeroRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨chainZeroRejected, ?_, rfl, chainZeroRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(0 : Nat), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ≠ 1
    exact Nat.zero_ne_one

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power.{u}) (type_of% (realize.{0, 0, 0, 0, 0} chainZeroSignature (fun _ L j => j + L) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "RectangularNilpotenceBarrier") "chain_zero_power") "Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier/Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(chainZeroArena.{u})⟩,
  objectArena := .source ⟨(chainZeroArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (chainZeroArena.{u}) ⟨(chainZeroRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} chainZeroSignature (fun _ L j => j + L) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, definition := none, coordinates := #[6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.anchorEnumeration }


#print axioms chainZeroRegistration

abbrev chainDepthSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def chainDepthActual : Realization chainDepthSignature :=
  realize chainDepthSignature (fun _ _ a => a) (fun e => nomatch e)

def chainDepthRejected : Realization chainDepthSignature :=
  realize chainDepthSignature (fun _ _ a => a + 1) (fun e => nomatch e)

def chainDepthArena : Arena where
  signature := chainDepthSignature
  Law r := ∀ {R : Type u} [Semiring R] {n m : ℕ}
    {A : Mat R n n} {B : Mat R m m} {a b L : ℕ}
    (c : ExchangeChain R A B L) (ha : ExactDepth A a) (hb : ExactDepth B b),
    r.readout () () a ≤ b + L ∧ b ≤ a + L

theorem chainDepthRejectedLaw : ¬ chainDepthArena.{u}.Law chainDepthRejected := by
  intro h
  let Z : Mat (ULift.{u} Nat) 1 1 := 0
  let c : ExchangeChain (ULift.{u} Nat) Z Z 0 := ExchangeChain.nil Z
  have hz : ExactDepth Z 1 := by
    refine ⟨by decide, ?_, ?_⟩
    · simp [Z]
    · intro j hj hlt
      omega
  have hb := h c hz hz
  have hbad := hb.1
  norm_num [chainDepthRejected, realize] at hbad

def chainDepthRegistration : Registration chainDepthArena (chainDepthArena.Law chainDepthActual) where
  actual := chainDepthActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R _ n m A B a b L c ha hb
    simpa [chainDepthActual, realize] using chain_depth_barrier c ha hb,
    chainDepthRejected, chainDepthRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨chainDepthRejected, ?_, rfl, chainDepthRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ≠ 1
    exact Nat.zero_ne_one

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_depth_barrier.{u}) (type_of% (realize.{0, 0, 0, 0, 0} chainDepthSignature (fun _ _ a => a) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "RectangularNilpotenceBarrier") "chain_depth_barrier") "Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier/Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(chainDepthArena.{u})⟩,
  objectArena := .source ⟨(chainDepthArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (chainDepthArena.{u}) ⟨(chainDepthRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} chainDepthSignature (fun _ _ a => a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_depth_barrier, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.anchorEnumeration }


abbrev chainReverseSignature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def chainReverseActual : Realization chainReverseSignature :=
  realize chainReverseSignature (fun _ L j => j + L) (fun e => nomatch e)

def chainReverseRejected : Realization chainReverseSignature :=
  realize chainReverseSignature (fun _ _ _ => 0) (fun e => nomatch e)

def chainReverseArena : Arena where
  signature := chainReverseSignature
  Law r := ∀ {R : Type u} [Semiring R] {n m : ℕ} {A : Mat R n n} {B : Mat R m m} {L : ℕ}
    (c : ExchangeChain R A B L), ∀ j : ℕ, A ^ j = 0 →
      B ^ (r.readout () L j) = 0

theorem chainReverseRejectedLaw : ¬ chainReverseArena.{u}.Law chainReverseRejected := by
  intro h
  let Z : Mat (ULift.{u} Nat) 1 1 := 0
  let c : ExchangeChain (ULift.{u} Nat) Z Z 0 := ExchangeChain.nil Z
  have hz := h c 1 (by simp [Z])
  have hentry := congrArg (fun M : Mat (ULift.{u} Nat) 1 1 => M 0 0) hz
  simp [Z, chainReverseRejected, realize] at hentry

def chainReverseRegistration : Registration chainReverseArena (chainReverseArena.Law chainReverseActual) where
  actual := chainReverseActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R _ n m A B L c j hj
    simpa [chainReverseActual, realize] using chain_zero_power_reverse c j hj,
    chainReverseRejected, chainReverseRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨chainReverseRejected, ?_, rfl, chainReverseRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(0 : Nat), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ≠ 1
    exact Nat.zero_ne_one

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power_reverse.{u}) (type_of% (realize.{0, 0, 0, 0, 0} chainReverseSignature (fun _ L j => j + L) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "RectangularNilpotenceBarrier") "chain_zero_power_reverse") "Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier/Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(chainReverseArena.{u})⟩,
  objectArena := .source ⟨(chainReverseArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (chainReverseArena.{u}) ⟨(chainReverseRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} chainReverseSignature (fun _ L j => j + L) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, definition := none, coordinates := #[6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power_reverse, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.anchorEnumeration }


abbrev rectangularSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def rectangularActual : Realization rectangularSignature :=
  realize rectangularSignature (fun _ _ j => j + 1) (fun e => nomatch e)

def rectangularRejected : Realization rectangularSignature :=
  realize rectangularSignature (fun _ _ _ => 0) (fun e => nomatch e)

def rectangularArena : Arena where
  signature := rectangularSignature
  Law r := ∀ {R : Type u} [Semiring R] {n m : ℕ}
    (U : Mat R n m) (V : Mat R m n) (j : ℕ),
    (U * V) ^ (r.readout () () j) = U * (V * U) ^ j * V

theorem rectangularRejectedLaw : ¬ rectangularArena.{u}.Law rectangularRejected := by
  intro h
  let Z : Mat (ULift.{u} Nat) 1 1 := 0
  have hz := h Z Z 0
  have hentry := congrArg (fun M : Mat (ULift.{u} Nat) 1 1 => M 0 0) hz
  simp [Z, rectangularRejected, realize] at hentry

def rectangularRegistration : Registration rectangularArena (rectangularArena.Law rectangularActual) where
  actual := rectangularActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R _ n m U V j
    simpa [rectangularActual, realize] using rectangular_exchange_power U V j,
    rectangularRejected, rectangularRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rectangularRejected, ?_, rfl, rectangularRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (1 : Nat) ≠ 2
    decide

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangular_exchange_power.{u}) (type_of% (realize.{0, 0, 0, 0, 0} rectangularSignature (fun _ _ j => j + 1) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "RectangularNilpotenceBarrier") "rectangular_exchange_power") "Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier/Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(rectangularArena.{u})⟩,
  objectArena := .source ⟨(rectangularArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (rectangularArena.{u}) ⟨(rectangularRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} rectangularSignature (fun _ _ j => j + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangular_exchange_power, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.anchorEnumeration }


abbrev mapSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def mapActual : Realization mapSignature :=
  realize mapSignature (fun _ _ L => L) (fun e => nomatch e)

def mapRejected : Realization mapSignature :=
  realize mapSignature (fun _ _ _ => 0) (fun e => nomatch e)

def mapArena : Arena where
  signature := mapSignature
  Law r := ∀ {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →ₙ+* S) {n m L : ℕ} {A : Mat R n n} {B : Mat R m m}
    (c : ExchangeChain R A B L),
    ExchangeChain S (A.map f) (B.map f) (r.readout () () L)

theorem mapRejectedLaw : ¬ mapArena.{u,v}.Law mapRejected := by
  intro h
  let R := ULift.{u} Nat
  let S := ULift.{v} Nat
  let f : R →ₙ+* S := {
    toFun := fun x => ⟨x.down⟩
    map_zero' := by rfl
    map_add' := by intro x y; rfl
    map_mul' := by intro x y; rfl }
  let U : Mat R 2 2 := Matrix.diagonal (fun i => if i = 0 then 1 else 0)
  let V : Mat R 2 2 := fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let A : Mat R 2 2 := U * V
  let B : Mat R 2 2 := V * U
  let c : ExchangeChain R A B 1 := ExchangeChain.cons U V (ExchangeChain.nil B)
  have hc := h f c
  have chain_zero_eq {X Y : Mat S 2 2} (hxy : ExchangeChain S X Y 0) : X = Y := by
    cases hxy
    rfl
  have heq : A.map f = B.map f := chain_zero_eq hc
  have hentry := congrFun (congrFun heq (0 : Fin 2)) (1 : Fin 2)
  have hA : A 0 1 = (1 : R) := by
    change (Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ULift.{u} Nat) else 0) * V) 0 1 = 1
    rw [Matrix.diagonal_mul]
    simp [V]
  have hB : B 0 1 = (0 : R) := by
    change (V * Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ULift.{u} Nat) else 0)) 0 1 = 0
    rw [Matrix.mul_diagonal]
    simp [V]
  change f (A 0 1) = f (B 0 1) at hentry
  rw [hA, hB] at hentry
  have hdown := congrArg ULift.down hentry
  exact Nat.noConfusion hdown

def mapRegistration : Registration mapArena (mapArena.Law mapActual) where
  actual := mapActual
  bridge := Iff.rfl
  variation := ⟨by
    intro R S _ _ f n m L A B c
    simpa [mapActual, realize] using map_exchange_chain f c,
    mapRejected, mapRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨mapRejected, ?_, rfl, mapRejectedLaw⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (0 : Nat) ≠ 1
    exact Nat.zero_ne_one

noncomputable def registration_5 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.map_exchange_chain.{u, v}) (type_of% (realize.{0, 0, 0, 0, 0} mapSignature (fun _ _ L => L) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "RectangularNilpotenceBarrier") "map_exchange_chain") "Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier/Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(mapArena.{u, v})⟩,
  objectArena := .source ⟨(mapArena.{u, v})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (mapArena.{u, v}) ⟨(mapRegistration.{u, v})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} mapSignature (fun _ _ L => L) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.map_exchange_chain, part := .type, path := [], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.anchorEnumeration }


end Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.canonicalArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapArena.{u, v}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.canonicalArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_5\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.canonicalObjectArenaOperand.{u, v} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapArena.{u, v}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.canonicalObjectArenaFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_5\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularArena.) (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularRegistration.{u}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"rectangular_exchange_power\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangular_exchange_power, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularRegistration.{u}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.observation0.{u} : {R : Type u} →
  [Semiring.{u} R] →
    {n m : Nat} →
      (U : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n m) →
        (V : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m n) →
          (j : Nat) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularSignature PUnit.unit.{1}
              PUnit.unit.{1} :=
  fun {R : Type u} [Semiring.{u} R] {n m : Nat}
    (U : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n m)
    (V : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m n) (j : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularSignature
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularActual PUnit.unit.{1} PUnit.unit.{1} j

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"rectangular_exchange_power\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangular_exchange_power, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"rectangular_exchange_power\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangular_exchange_power, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularRegistration.{u}).actual (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularRegistration.{u}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularRegistration.{u}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularRegistration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"rectangularRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.rectangularRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthArena.) (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthRegistration.{u}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chain_depth_barrier\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_depth_barrier, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthRegistration.{u}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.observation0.{u} : {R : Type u} →
  [inst : Semiring.{u} R] →
    {n m : Nat} →
      {A : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n} →
        {B : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m} →
          {a b L : Nat} →
            (c : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{u} R inst n m A B L) →
              (ha : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExactDepth.{u} R inst n A a) →
                (hb : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExactDepth.{u} R inst m B b) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthSignature PUnit.unit.{1}
                    PUnit.unit.{1} :=
  fun {R : Type u} [Semiring.{u} R] {n m : Nat}
    {A : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n}
    {B : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m} {a b L : Nat}
    (c : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{u} R inst n m A B L)
    (ha : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExactDepth.{u} R inst n A a)
    (hb : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExactDepth.{u} R inst m B b) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthSignature
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthActual PUnit.unit.{1} PUnit.unit.{1} a

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chain_depth_barrier\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_depth_barrier, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chain_depth_barrier\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_depth_barrier, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthRegistration.{u}).actual (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthRegistration.{u}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthRegistration.{u}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthRegistration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chainDepthRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainDepthRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroArena.) (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroRegistration.{u}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chain_zero_power\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroRegistration.{u}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.observation0.{u} : {R : Type u} →
  [inst : Semiring.{u} R] →
    {n m : Nat} →
      {A : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n} →
        {B : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m} →
          {L : Nat} →
            (c : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{u} R inst n m A B L) →
              (j : Nat) →
                @Eq.{u + 1} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
                    (@HPow.hPow.{u, 0, u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m) Nat
                      (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
                      (@instHPow.{u, 0} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m) Nat
                        (@NPow.toPow.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
                          (@Monoid.toNPow.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
                            (@Semiring.toMonoid.{u}
                              (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
                              (@Matrix.semiring.{u, 0} (Fin m) R inst (Fin.fintype m) (instDecidableEqFin m))))))
                      B j)
                    (@OfNat.ofNat.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
                      (nat_lit 0)
                      (@Zero.toOfNat0.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
                        (@Matrix.zero.{u, 0, 0} (Fin m) (Fin m) R
                          (@MulZeroClass.toZero.{u} R (@instMulZeroClassOfSemiring.{u} R inst))))) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroSignature PUnit.unit.{1} L :=
  fun {R : Type u} [Semiring.{u} R] {n m : Nat}
    {A : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n}
    {B : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m} {L : Nat}
    (c : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{u} R inst n m A B L) (j : Nat)
    (a :
      @Eq.{u + 1} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
        (@HPow.hPow.{u, 0, u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m) Nat
          (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
          (@instHPow.{u, 0} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m) Nat
            (@NPow.toPow.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
              (@Monoid.toNPow.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
                (@Semiring.toMonoid.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
                  (@Matrix.semiring.{u, 0} (Fin m) R inst (Fin.fintype m) (instDecidableEqFin m))))))
          B j)
        (@OfNat.ofNat.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m) (nat_lit 0)
          (@Zero.toOfNat0.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m)
            (@Matrix.zero.{u, 0, 0} (Fin m) (Fin m) R
              (@MulZeroClass.toZero.{u} R (@instMulZeroClassOfSemiring.{u} R inst)))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroSignature
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroActual PUnit.unit.{1} L j

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chain_zero_power\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chain_zero_power\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroRegistration.{u}).actual (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroRegistration.{u}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroRegistration.{u}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroRegistration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chainZeroRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainZeroRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.sourceLaw.{u, v} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapArena.) (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapRegistration.{u, v}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.sourceBridgeFact.{u, v} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"map_exchange_chain\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_5\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.map_exchange_chain, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.sourceLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapRegistration.{u, v}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.observation0.{u, v} : {R : Type u} →
  {S : Type v} →
    [inst : Semiring.{u} R] →
      [inst_1 : Semiring.{v} S] →
        (f :
            @NonUnitalRingHom.{u, v} R S
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (@Semiring.toNonAssocSemiring.{u} R inst))
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{v} S (@Semiring.toNonAssocSemiring.{v} S inst_1))) →
          {n m L : Nat} →
            {A : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n} →
              {B : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m} →
                (c : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{u} R inst n m A B L) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapSignature PUnit.unit.{1}
                    PUnit.unit.{1} :=
  fun {R : Type u} {S : Type v} [Semiring.{u} R] [Semiring.{v} S]
    (f :
      @NonUnitalRingHom.{u, v} R S
        (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (@Semiring.toNonAssocSemiring.{u} R inst))
        (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{v} S (@Semiring.toNonAssocSemiring.{v} S inst_1)))
    {n m L : Nat} {A : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n}
    {B : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m}
    (c : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{u} R inst n m A B L) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapSignature
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapActual PUnit.unit.{1} PUnit.unit.{1} L

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.observationFact0.{u, v} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"map_exchange_chain\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_5\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.map_exchange_chain, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.observation0, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.varyingLawInput.{u, v} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.canonicalArenaOperand.{u, v})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.varyingLaw.{u, v}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_5\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.statementExclusion.{u, v} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_5\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"map_exchange_chain\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.varyingLaw, part := .value, path := [], levels := [(.param `u), (.param `v)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.map_exchange_chain, part := .type, path := [], levels := [(.param `u), (.param `v)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapRegistration.{u, v}).actual (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapRegistration.{u, v}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapRegistration.{u, v}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapRegistration.{u, v}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"mapRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]],[\"param\",[\"v\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u), (.param `v)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.mapRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u), (.param `v)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseArena.) (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseRegistration.{u}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chain_zero_power_reverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power_reverse, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseRegistration.{u}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.observation0.{u} : {R : Type u} →
  [inst : Semiring.{u} R] →
    {n m : Nat} →
      {A : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n} →
        {B : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m} →
          {L : Nat} →
            (c : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{u} R inst n m A B L) →
              (j : Nat) →
                @Eq.{u + 1} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
                    (@HPow.hPow.{u, 0, u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n) Nat
                      (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
                      (@instHPow.{u, 0} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n) Nat
                        (@NPow.toPow.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
                          (@Monoid.toNPow.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
                            (@Semiring.toMonoid.{u}
                              (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
                              (@Matrix.semiring.{u, 0} (Fin n) R inst (Fin.fintype n) (instDecidableEqFin n))))))
                      A j)
                    (@OfNat.ofNat.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
                      (nat_lit 0)
                      (@Zero.toOfNat0.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
                        (@Matrix.zero.{u, 0, 0} (Fin n) (Fin n) R
                          (@MulZeroClass.toZero.{u} R (@instMulZeroClassOfSemiring.{u} R inst))))) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseSignature PUnit.unit.{1} L :=
  fun {R : Type u} [Semiring.{u} R] {n m : Nat}
    {A : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n}
    {B : D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R m m} {L : Nat}
    (c : @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{u} R inst n m A B L) (j : Nat)
    (a :
      @Eq.{u + 1} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
        (@HPow.hPow.{u, 0, u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n) Nat
          (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
          (@instHPow.{u, 0} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n) Nat
            (@NPow.toPow.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
              (@Monoid.toNPow.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
                (@Semiring.toMonoid.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
                  (@Matrix.semiring.{u, 0} (Fin n) R inst (Fin.fintype n) (instDecidableEqFin n))))))
          A j)
        (@OfNat.ofNat.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n) (nat_lit 0)
          (@Zero.toOfNat0.{u} (D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.Mat.{u} R n n)
            (@Matrix.zero.{u, 0, 0} (Fin n) (Fin n) R
              (@MulZeroClass.toZero.{u} R (@instMulZeroClassOfSemiring.{u} R inst)))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseSignature
    Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseActual PUnit.unit.{1} L j

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chain_zero_power_reverse\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power_reverse, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chain_zero_power_reverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chain_zero_power_reverse, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseRegistration.{u}).actual (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseRegistration.{u}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseRegistration.{u}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseRegistration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"RectangularNilpotenceBarrier\",\"chainReverseRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier, declaration := `Reg.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.chainReverseRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
