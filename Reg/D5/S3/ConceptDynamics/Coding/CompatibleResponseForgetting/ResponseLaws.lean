import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
import Reg.Support.DependentFamily
import Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ScalarCountMatrices

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open _root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open _root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

/-- Zero exchanges preserve the dimension, including empty matrix fibers. -/
theorem zeroChain_dimension {a b : ℕ} {X : CountMat a a} {Y : CountMat b b}
    (chain : ExchangeChain ℕ X Y 0) : a = b := by
  cases chain
  rfl

def emptyExchangeU : CountMat 0 1 := 0
def emptyExchangeV : CountMat 1 0 := 0

theorem emptyExchange : ExchangeChain ℕ
    (emptyExchangeU * emptyExchangeV) (emptyExchangeV * emptyExchangeU) 1 :=
  .cons emptyExchangeU emptyExchangeV (.nil _)

namespace ChainTrans

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ l₁ l₂ => l₁ + l₂) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {a b c : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {Z : CountMat c c}
    {l₁ l₂ : ℕ} (left : ExchangeChain ℕ X Y l₁)
    (right : ExchangeChain ℕ Y Z l₂),
    ExchangeChain ℕ X Z (rho.readout () l₁ l₂)

theorem actual_law : arena.Law actual := by
  intro a b c X Y Z l₁ l₂ left right
  exact exchange_chain_trans left right

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  exact Nat.zero_ne_one (zeroChain_dimension (h emptyExchange (.nil _)))

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_trans) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ l₁ l₂ => l₁ + l₂) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "exchange_chain_trans") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ l₁ l₂ => l₁ + l₂) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_trans, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.anchorEnumeration }


#print axioms registration

end ChainTrans

abbrev numberSignature : Signature where
  Params := Σ n, Σ k, Σ R : CountMat n k, Σ _ : Fin n, Fin k
  State p := Fin (p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  Anchor := Empty
  finiteAnchor := inferInstance

def numberActual : Realization numberSignature :=
  realize numberSignature (fun _ _ r => r) (fun e => nomatch e)
def numberBad : Realization numberSignature :=
  realize numberSignature (fun _ _ r => Fin.rev r) (fun e => nomatch e)

def swapNumbers (i z : Fin 1) : EdgePair U P2 i z ≃ EdgePair P2 U i z :=
  Equiv.sigmaCongrRight (fun _ => Equiv.prodComm _ _)

namespace UnsweepSweep

def arena : Arena where
  signature := numberSignature
  Law rho := ∀ {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k}
    (phi : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z),
    ∀ {d : ℕ} {i j : Fin n} {z : Fin k}
      (alpha : FinitePath A d i j) (r : Fin (R j z)),
      (let swept := sweep phi alpha r
       unsweep phi swept.2.1 swept.2.2) =
        ⟨j, alpha, rho.readout () ⟨n, k, R, j, z⟩ r⟩

theorem actual_law : arena.Law numberActual := by
  intro n k A B R phi
  exact unsweep_sweep phi

theorem rejected_law : ¬ arena.Law numberBad := by
  intro h
  have he := h swapNumbers (i := 0) (j := 0) (z := 0) (.nil 0) 0
  exact Nat.zero_ne_one (congrArg (fun p :
    Σ j : Fin 1, FinitePath U 0 0 j × Fin (P2 j 0) => p.2.2.val) he)

def registration : Registration arena (arena.Law numberActual) where
  actual := numberActual
  bridge := Iff.rfl
  variation := ⟨actual_law, numberBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨numberBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 1, P2, 0, 0⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_sweep) (type_of% (realize.{0, 0, 0, 0, 0} numberSignature (fun _ _ r => r) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "unsweep_sweep") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} numberSignature (fun _ _ r => r) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[0, 1, 4, 8, 9], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_sweep, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.anchorEnumeration }


#print axioms registration

end UnsweepSweep

namespace UnsweepAppend

def arena : Arena where
  signature := numberSignature
  Law rho := ∀ {n k : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} (phi : ∀ i z, EdgePair A R i z ≃ EdgePair R B i z),
    ∀ {d : ℕ} {i : Fin n} {t u z : Fin k} (r : Fin (R i t))
      (beta : FinitePath B d t u) (b : Fin (B u z)),
      unsweep phi (rho.readout () ⟨n, k, R, i, t⟩ r) (appendPath beta b) =
        (let prior := unsweep phi r beta
         let sq := (phi prior.1 z).symm ⟨u, prior.2.2, b⟩
         ⟨sq.1, appendPath prior.2.1 sq.2.1, sq.2.2⟩)

theorem actual_law : arena.Law numberActual := by
  intro n k A B R phi
  exact unsweep_append phi

theorem rejected_law : ¬ arena.Law numberBad := by
  intro h
  have he := h swapNumbers (i := 0) (t := 0) (u := 0) (z := 0) 0 (.nil 0) 0
  exact Nat.zero_ne_one (congrArg (fun p :
    Σ j : Fin 1, FinitePath U 1 0 j × Fin (P2 j 0) => p.2.2.val) he).symm

def registration : Registration arena (arena.Law numberActual) where
  actual := numberActual
  bridge := Iff.rfl
  variation := ⟨actual_law, numberBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨numberBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 1, P2, 0, 0⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_append) (type_of% (realize.{0, 0, 0, 0, 0} numberSignature (fun _ _ r => r) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "unsweep_append") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} numberSignature (fun _ _ r => r) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[0, 1, 4, 7, 8], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_append, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.anchorEnumeration }


#print axioms registration

end UnsweepAppend

abbrev depthSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def depthActual : Realization depthSignature :=
  realize depthSignature (fun _ _ d => d) (fun e => nomatch e)
def depthBad : Realization depthSignature :=
  realize depthSignature (fun _ _ _ => 0) (fun e => nomatch e)

namespace ChainReverse

def arena : Arena where
  signature := depthSignature
  Law rho := ∀ {a b : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {length : ℕ}
    (chain : ExchangeChain ℕ X Y length),
    ExchangeChain ℕ Y X (rho.readout () () length)

theorem actual_law : arena.Law depthActual := by
  intro a b X Y length chain
  exact exchange_chain_reverse chain

theorem rejected_law : ¬ arena.Law depthBad := by
  intro h
  exact Nat.zero_ne_one (zeroChain_dimension (h emptyExchange)).symm

def registration : Registration arena (arena.Law depthActual) where
  actual := depthActual
  bridge := Iff.rfl
  variation := ⟨actual_law, depthBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨depthBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_reverse) (type_of% (realize.{0, 0, 0, 0, 0} depthSignature (fun _ _ d => d) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "exchange_chain_reverse") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} depthSignature (fun _ _ d => d) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_reverse, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.anchorEnumeration }


#print axioms registration

end ChainReverse

namespace ChainTranspose

def arena : Arena where
  signature := depthSignature
  Law rho := ∀ {a b : ℕ}
    {X : CountMat a a} {Y : CountMat b b} {length : ℕ}
    (chain : ExchangeChain ℕ X Y length),
    ExchangeChain ℕ X.transpose Y.transpose (rho.readout () () length)

theorem actual_law : arena.Law depthActual := by
  intro a b X Y length chain
  exact exchange_chain_transpose chain

theorem rejected_law : ¬ arena.Law depthBad := by
  intro h
  exact Nat.zero_ne_one (zeroChain_dimension (h emptyExchange))

def registration : Registration arena (arena.Law depthActual) where
  actual := depthActual
  bridge := Iff.rfl
  variation := ⟨actual_law, depthBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨depthBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

noncomputable def registration_5 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_transpose) (type_of% (realize.{0, 0, 0, 0, 0} depthSignature (fun _ _ d => d) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "exchange_chain_transpose") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} depthSignature (fun _ _ d => d) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_transpose, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.anchorEnumeration }


#print axioms registration

end ChainTranspose

/-- One numbered loop with an arbitrary state transition. -/
def loopLift {Q : Type} (q₀ : Q) (f : Q → Q) : IncomingLift U Q where
  project := fun _ => 0
  onto := fun i => ⟨q₀, Subsingleton.elim _ _⟩
  lift := fun a q => ⟨f q.val, Subsingleton.elim _ _⟩

def uniqueLoopPath : (d : ℕ) → FinitePath U d 0 0
  | 0 => .nil 0
  | d + 1 => .cons 0 (uniqueLoopPath d)

theorem loopLift_path {Q : Type} (q₀ : Q) (f : Q → Q)
    {d : ℕ} {i j : Fin 1} (path : FinitePath U d i j)
    (q : {x : Q // (loopLift q₀ f).project x = j}) :
    ((loopLift q₀ f).liftPath path q).val = f^[d] q.val := by
  induction path with
  | nil i => rfl
  | cons a tail ih =>
    simpa only [IncomingLift.liftPath, loopLift, Function.iterate_succ_apply'] using
      congrArg f (ih q)

theorem loopLift_response {Q : Type} (q₀ : Q) (f : Q → Q)
    (d : ℕ) (x y : Q) :
    (loopLift q₀ f).response d x y ↔ f^[d] x = f^[d] y := by
  constructor
  · intro h
    have he := congrArg (fun o => o.2 0 0 (uniqueLoopPath d))
      (show (loopLift q₀ f).responseReadout d x =
        (loopLift q₀ f).responseReadout d y from h)
    have hx : (loopLift q₀ f).project x = 0 := rfl
    have hy : (loopLift q₀ f).project y = 0 := rfl
    simpa only [IncomingLift.responseReadout, dif_pos hx, dif_pos hy,
      loopLift_path, Option.some.injEq] using he
  · intro h
    change (loopLift q₀ f).responseReadout d x = (loopLift q₀ f).responseReadout d y
    apply Prod.ext
    · rfl
    funext i j path
    have hx : (loopLift q₀ f).project x = j := Subsingleton.elim _ _
    have hy : (loopLift q₀ f).project y = j := Subsingleton.elim _ _
    simp only [IncomingLift.responseReadout, dif_pos hx, dif_pos hy, loopLift_path, h]

def liftL0 : IncomingLift U Bool := loopLift false (fun _ => false)
def liftL2 : IncomingLift U (Fin 3) := loopLift 0 (fun x => if x = 2 then 1 else 0)
def liftIdBool : IncomingLift U Bool := loopLift false id
def liftUnit : IncomingLift U Unit := loopLift () id

def l0End : Quotient (liftL0.response 1) ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => Quotient.mk _ false
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      exact (loopLift_response false (fun _ => false) 1 false x).mpr rfl
  right_inv := fun _ => Subsingleton.elim _ _

instance uniqueUEdge : Subsingleton (Edge U) where
  allEq := by
    rintro ⟨i, j, a⟩ ⟨i', j', a'⟩
    have hi : i = i' := Subsingleton.elim _ _
    have hj : j = j' := Subsingleton.elim _ _
    subst i'; subst j'
    have ha : a = a' := Subsingleton.elim _ _
    subst a'; rfl

/-- The identity lift's incoming fiber is the singleton edge precisely on its class. -/
def identityFiberEquiv {Q : Type} (q₀ : Q) (d : ℕ) (x y : Q)
    (h : ∀ a b, (loopLift q₀ id).response d a b ↔ a = b) :
    incomingResponseFiber (loopLift q₀ id) d (Quotient.mk _ x) y ≃
      {a : Edge U // y = x} where
  toFun := fun a => ⟨a.val, by
    obtain ⟨hv, he⟩ := a.property
    exact (h _ _).mp (Quotient.exact he)⟩
  invFun := fun a => ⟨a.val, ⟨Subsingleton.elim _ _, by
    apply Quotient.sound
    exact (h _ _).mpr a.property⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

theorem identityFiber_card {Q : Type} [DecidableEq Q] (q₀ : Q) (d : ℕ) (x y : Q) :
    Nat.card (incomingResponseFiber (loopLift q₀ id) d (Quotient.mk _ x) y) =
      if y = x then 1 else 0 := by
  classical
  have hh : ∀ a b, (loopLift q₀ id).response d a b ↔ a = b := by
    intro a b
    simpa using loopLift_response q₀ id d a b
  rw [Nat.card_congr (identityFiberEquiv q₀ d x y hh)]
  by_cases h : y = x
  · let e : {a : Edge U // y = x} ≃ Fin 1 := {
      toFun := fun _ => 0
      invFun := fun _ => ⟨⟨0, 0, 0⟩, h⟩
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
    rw [Nat.card_congr e, Nat.card_fin, if_pos h]
  · let e : {a : Edge U // y = x} ≃ Empty := {
      toFun := fun a => (h a.property).elim
      invFun := fun e => nomatch e
      left_inv := fun a => (h a.property).elim
      right_inv := fun e => nomatch e }
    rw [Nat.card_congr e, if_neg h]
    simp

namespace IncomingStep

def arena : Arena where
  signature := depthSignature
  Law rho := ∀ {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q) (d : ℕ) {u v : Q}
    (h : L.response (d + 1) u v) (a : Edge A)
    (hu : L.project u = a.target) (hv : L.project v = a.target),
    L.response (rho.readout () () d)
      (L.lift a ⟨u, hu⟩).val (L.lift a ⟨v, hv⟩).val

theorem actual_law : arena.Law depthActual := by
  intro n A Q L d u v h a hu hv
  exact incoming_response_step L d h a hu hv

theorem rejected_law : ¬ arena.Law depthBad := by
  intro h
  have hr : liftL2.response 2 (0 : Fin 3) 2 := by
    exact (loopLift_response 0 (fun x : Fin 3 => if x = 2 then 1 else 0)
      2 0 2).mpr (by decide)
  have he := h liftL2 1 hr (⟨0, 0, 0⟩ : Edge U) rfl rfl
  change liftL2.response 0 (0 : Fin 3) 1 at he
  have hn := (loopLift_response 0 (fun x : Fin 3 => if x = 2 then 1 else 0)
    0 0 1).mp he
  exact Nat.zero_ne_one (congrArg Fin.val hn)

def registration : Registration arena (arena.Law depthActual) where
  actual := depthActual
  bridge := Iff.rfl
  variation := ⟨actual_law, depthBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨depthBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

noncomputable def registration_6 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.incoming_response_step) (type_of% (realize.{0, 0, 0, 0, 0} depthSignature (fun _ _ d => d) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "incoming_response_step") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} depthSignature (fun _ _ d => d) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.incoming_response_step, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.anchorEnumeration }


#print axioms registration

end IncomingStep

namespace FiniteChainTo

def actual : Realization depthSignature :=
  realize depthSignature (fun _ _ d => d + 1) (fun e => nomatch e)

def arena : Arena where
  signature := depthSignature
  Law rho := ∀ {p : ℕ} {M : CountMat p p}
    {Q : Type} [Fintype Q] (L : IncomingLift M Q)
    (start length : ℕ) {r : ℕ}
    (eEnd : Quotient (L.response (start + length + 1)) ≃ Fin r),
    ExchangeChain ℕ (finiteResponseMatrix L start)
      (Matrix.reindex eEnd eEnd
        (incomingResponseMatrix L (start + length + 1)))
      (rho.readout () () length)

theorem actual_law : arena.Law actual := by
  intro p M Q inst L start length r eEnd
  exact finite_response_chain_to L start length eEnd

theorem rejected_law : ¬ arena.Law depthBad := by
  intro h
  let e0 : Quotient (liftL0.response 0) ≃ Bool :=
    (Equiv.cast (congrArg (fun r : Setoid Bool => Quotient r)
      (response_zero_and_step liftL0).1)).trans Setoid.quotientBotEquiv
  have hc : @Fintype.card _ (responseFintype liftL0 0) = 2 := by
    calc
      _ = Fintype.card Bool :=
        @Fintype.card_congr _ _ (responseFintype liftL0 0) inferInstance e0
      _ = 2 := rfl
  have hh := zeroChain_dimension (h liftL0 0 0 l0End)
  change @Fintype.card _ (responseFintype liftL0 0) = 1 at hh
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, depthBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨depthBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), (by decide : (1 : ℕ) ≠ 2)⟩

noncomputable def registration_7 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.finite_response_chain_to) (type_of% (realize.{0, 0, 0, 0, 0} depthSignature (fun _ _ d => d + 1) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "finite_response_chain_to") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} depthSignature (fun _ _ d => d + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.finite_response_chain_to, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.anchorEnumeration }


#print axioms registration

end FiniteChainTo

namespace FiberCard

abbrev signature : Signature where
  Params := Σ p, Σ M : CountMat p p, Σ Q : Type, Σ L : IncomingLift M Q,
    Σ d : ℕ, Quotient (L.response d)
  State p := p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => Nat.card
    (incomingResponseFiber p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 w)) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ p w => Nat.card
    (incomingResponseFiber p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 w) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ) (F : Quotient (L.response d))
    {v w : Q} (h : L.response (d + 1) v w),
    Nat.card (incomingResponseFiber L d F v) = rho.readout () ⟨p, M, Q, L, d, F⟩ w

theorem actual_law : arena.Law actual := by
  intro p M Q L d F v w h
  exact incoming_response_fiber_card_step L d F h

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have he := h liftIdBool 0 (Quotient.mk _ false) (v := false) (w := false)
    ((liftIdBool.response 1).refl false)
  change Nat.card (incomingResponseFiber liftIdBool 0 (Quotient.mk _ false) false) =
    Nat.card (incomingResponseFiber liftIdBool 0 (Quotient.mk _ false) false) + 1 at he
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, U, Bool, liftIdBool, 0, Quotient.mk _ false⟩, false, true, ?_⟩
    intro h
    change Nat.card (incomingResponseFiber liftIdBool 0 (Quotient.mk _ false) false) =
      Nat.card (incomingResponseFiber liftIdBool 0 (Quotient.mk _ false) true) at h
    have hfalse : Nat.card (incomingResponseFiber liftIdBool 0
        (Quotient.mk _ false) false) = 1 := identityFiber_card false 0 false false
    have htrue : Nat.card (incomingResponseFiber liftIdBool 0
        (Quotient.mk _ false) true) = 0 := identityFiber_card false 0 false true
    exact Nat.zero_ne_one (htrue.symm.trans (h.symm.trans hfalse))

noncomputable def registration_8 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_fiber_card_step) (type_of% (realize.{1, 0, 0, 0, 0} signature (fun _ p w => Nat.card.{0}
    (incomingResponseFiber p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 w)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "incoming_response_fiber_card_step") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{1, 0, 0, 0, 0} signature (fun _ p w => Nat.card.{0}
    (incomingResponseFiber p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 w)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[0, 1, 2, 3, 4, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_fiber_card_step, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.anchorEnumeration }


#print axioms registration

end FiberCard

namespace ForgettingReindexed

abbrev signature : Signature where
  Params := ℕ
  State p := CountMat p p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := CountMat p p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {p : ℕ} {M : CountMat p p} {Q : Type} [Fintype Q]
    (L : IncomingLift M Q) (d : ℕ)
    (hd : L.response d = Setoid.ker L.project),
    ∃ e : Quotient (L.response d) ≃ Fin p,
      Matrix.reindex e e (incomingResponseMatrix L d) = rho.readout () p M

theorem actual_law : arena.Law actual := by
  intro p M Q inst L d hd
  exact response_matrix_forgetting_reindexed L d hd

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have hd : liftUnit.response 0 = Setoid.ker liftUnit.project := by
    apply Setoid.ext
    intro x y
    constructor
    · intro _; rfl
    · intro _
      exact (loopLift_response () id 0 x y).mpr (Subsingleton.elim _ _)
  obtain ⟨e, he⟩ := h liftUnit 0 hd
  have hv := congrArg (fun M : CountMat 1 1 => M 0 0) he
  change incomingResponseMatrix liftUnit 0 (e.symm 0) (e.symm 0) = 0 at hv
  have hq : e.symm 0 = Quotient.mk (liftUnit.response 0) () := by
    induction e.symm 0 using Quotient.inductionOn with
    | _ q => cases q; rfl
  rw [hq] at hv
  have hout : Quotient.out (Quotient.mk (liftUnit.response 0) ()) = () :=
    (loopLift_response () id 0 _ ()).mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (liftUnit.response 0) ())))
  change Nat.card (incomingResponseFiber liftUnit 0 (Quotient.mk _ ())
    (Quotient.out (Quotient.mk (liftUnit.response 0) ()))) = 0 at hv
  rw [hout] at hv
  have hc : Nat.card (incomingResponseFiber liftUnit 0 (Quotient.mk _ ()) ()) = 1 :=
    identityFiber_card () 0 () ()
  exact Nat.zero_ne_one (hv.symm.trans hc)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), U, P2, ?_⟩
    intro h
    exact (by decide : (1 : ℕ) ≠ 2) (congrArg (fun M : CountMat 1 1 => M 0 0) h)

noncomputable def registration_9 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.response_matrix_forgetting_reindexed) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ M => M) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "response_matrix_forgetting_reindexed") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ M => M) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.response_matrix_forgetting_reindexed, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.anchorEnumeration }


#print axioms registration

end ForgettingReindexed

namespace MatrixFactorStep

/-- Dependence is evaluation of a whole depth-indexed matrix family. -/
abbrev signature : Signature where
  Params := Σ p, Σ M : CountMat p p, Σ Q : Type, Σ _ : IncomingLift M Q, ℕ
  State theta := (k : ℕ) → Matrix (Quotient (theta.2.2.2.1.response k))
    (Quotient (theta.2.2.2.1.response k)) ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ theta := Matrix (Quotient (theta.2.2.2.1.response (theta.2.2.2.2 + 1)))
    (Quotient (theta.2.2.2.1.response (theta.2.2.2.2 + 1))) ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ theta F => F (theta.2.2.2.2 + 1)) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ theta F i j => F (theta.2.2.2.2 + 1) i j + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (d : ℕ)
    [Fintype (Quotient (L.response d))]
    [Fintype (Quotient (L.response (d + 1)))],
    rho.readout () ⟨p, M, Q, L, d⟩ (incomingResponseMatrix L) =
      incomingResponseV L d * incomingResponseU L d

theorem actual_law : arena.Law actual := by
  intro p M Q L d inst0 inst1
  exact incoming_response_matrix_factor_step L d

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  let f0 := responseFintype liftUnit 0
  let f1 := responseFintype liftUnit 1
  have changed := @h 1 U Unit liftUnit 0 f0 f1
  have original := @incoming_response_matrix_factor_step 1 U Unit liftUnit 0 f0 f1
  let q : Quotient (liftUnit.response 1) := Quotient.mk _ ()
  have entry := congrArg (fun A => A q q) (changed.trans original.symm)
  change incomingResponseMatrix liftUnit 1 q q + 1 =
    incomingResponseMatrix liftUnit 1 q q at entry
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, U, Unit, liftUnit, 0⟩, (fun _ _ _ => 0), (fun _ _ _ => 1), ?_⟩
    intro h
    let q : Quotient (liftUnit.response 1) := Quotient.mk _ ()
    exact Nat.zero_ne_one (congrArg (fun A => A q q) h)

noncomputable def registration_10 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_matrix_factor_step) (type_of% (realize.{1, 0, 0, 0, 0} signature (fun _ theta F => F (theta.2.2.2.2 + 1))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "incoming_response_matrix_factor_step") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{1, 0, 0, 0, 0} signature (fun _ theta F => F (theta.2.2.2.2 + 1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[0, 1, 2, 3, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_matrix_factor_step, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms registration

end MatrixFactorStep

end Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration_5\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration_5\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration_9\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration_9\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration_9\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration_9\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration_8\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration_8\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration_10\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration_10\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{1, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration_10\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration_10\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration_6\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration_6\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration_7\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration_7\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"exchange_chain_reverse\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_reverse, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.observation0 : {a b : Nat} →
  {X : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat a a} →
    {Y : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat b b} →
      {length : Nat} →
        (chain :
            @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring a b X Y
              length) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthSignature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {a b : Nat} {X : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat a a}
    {Y : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat b b} {length : Nat}
    (chain :
      @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring a b X Y
        length) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthSignature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthActual PUnit.unit.{1} PUnit.unit.{1} length

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"exchange_chain_reverse\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_reverse, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"exchange_chain_reverse\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_reverse, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainReverse\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainReverse.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"exchange_chain_transpose\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration_5\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_transpose, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.observation0 : {a b : Nat} →
  {X : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat a a} →
    {Y : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat b b} →
      {length : Nat} →
        (chain :
            @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring a b X Y
              length) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthSignature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {a b : Nat} {X : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat a a}
    {Y : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat b b} {length : Nat}
    (chain :
      @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring a b X Y
        length) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthSignature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthActual PUnit.unit.{1} PUnit.unit.{1} length

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"exchange_chain_transpose\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration_5\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_transpose, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration_5\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration_5\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"exchange_chain_transpose\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_transpose, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTranspose\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTranspose.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"response_matrix_forgetting_reindexed\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration_9\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.response_matrix_forgetting_reindexed, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.observation0 : {p : Nat} →
  {M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p} →
    {Q : Type} →
      [Fintype.{0} Q] →
        (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) →
          (d : Nat) →
            (hd :
                @Eq.{1} (Setoid.{1} Q)
                  (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d)
                  (@Setoid.ker.{0, 0} Q (Fin p)
                    (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.project p M Q L))) →
              (e :
                  Equiv.{1, 1}
                    (@Quotient.{1} Q
                      (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
                    (Fin p)) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.signature
                  PUnit.unit.{1} p :=
  fun {p : Nat} {M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p} {Q : Type} [Fintype.{0} Q]
    (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) (d : Nat)
    (hd :
      @Eq.{1} (Setoid.{1} Q) (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d)
        (@Setoid.ker.{0, 0} Q (Fin p)
          (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.project p M Q L)))
    (e :
      Equiv.{1, 1}
        (@Quotient.{1} Q (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
        (Fin p)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.signature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.actual PUnit.unit.{1} p M

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"response_matrix_forgetting_reindexed\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration_9\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.response_matrix_forgetting_reindexed, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration_9\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration_9\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"response_matrix_forgetting_reindexed\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.response_matrix_forgetting_reindexed, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration_9\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ForgettingReindexed\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration_9, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ForgettingReindexed.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"incoming_response_fiber_card_step\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration_8\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_fiber_card_step, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.observation0 : {p : Nat} →
  {M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p} →
    {Q : Type} →
      (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) →
        (d : Nat) →
          (F : @Quotient.{1} Q (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d)) →
            {v w : Q} →
              (h :
                  @Setoid.r.{1} Q
                    (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    v w) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{1, 0, 0, 0, 0}
                  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.signature PUnit.unit.{1}
                  (@Sigma.mk.{0, 1} Nat
                    (fun (p : Nat) =>
                      @Sigma.{0, 1} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p)
                        fun (M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p) =>
                        @Sigma.{1, 0} Type fun (Q : Type) =>
                          @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
                            fun (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) =>
                            @Sigma.{0, 0} Nat fun (d : Nat) =>
                              @Quotient.{1} Q
                                (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
                    p
                    (@Sigma.mk.{0, 1} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p)
                      (fun (M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p) =>
                        @Sigma.{1, 0} Type fun (Q : Type) =>
                          @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
                            fun (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) =>
                            @Sigma.{0, 0} Nat fun (d : Nat) =>
                              @Quotient.{1} Q
                                (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
                      M
                      (@Sigma.mk.{1, 0} Type
                        (fun (Q : Type) =>
                          @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
                            fun (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) =>
                            @Sigma.{0, 0} Nat fun (d : Nat) =>
                              @Quotient.{1} Q
                                (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
                        Q
                        (@Sigma.mk.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
                          (fun (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) =>
                            @Sigma.{0, 0} Nat fun (d : Nat) =>
                              @Quotient.{1} Q
                                (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
                          L
                          (@Sigma.mk.{0, 0} Nat
                            (fun (d : Nat) =>
                              @Quotient.{1} Q
                                (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
                            d F))))) :=
  fun {p : Nat} {M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p} {Q : Type}
    (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) (d : Nat)
    (F : @Quotient.{1} Q (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
    {v w : Q}
    (h :
      @Setoid.r.{1} Q
        (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        v w) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{1, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.signature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 1} Nat
      (fun (p : Nat) =>
        @Sigma.{0, 1} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p)
          fun (M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p) =>
          @Sigma.{1, 0} Type fun (Q : Type) =>
            @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
              fun (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) =>
              @Sigma.{0, 0} Nat fun (d : Nat) =>
                @Quotient.{1} Q (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
      p
      (@Sigma.mk.{0, 1} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p)
        (fun (M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p) =>
          @Sigma.{1, 0} Type fun (Q : Type) =>
            @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
              fun (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) =>
              @Sigma.{0, 0} Nat fun (d : Nat) =>
                @Quotient.{1} Q (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
        M
        (@Sigma.mk.{1, 0} Type
          (fun (Q : Type) =>
            @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
              fun (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) =>
              @Sigma.{0, 0} Nat fun (d : Nat) =>
                @Quotient.{1} Q (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
          Q
          (@Sigma.mk.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
            (fun (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) =>
              @Sigma.{0, 0} Nat fun (d : Nat) =>
                @Quotient.{1} Q (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
            L
            (@Sigma.mk.{0, 0} Nat
              (fun (d : Nat) =>
                @Quotient.{1} Q (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))
              d F)))))
    w

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"incoming_response_fiber_card_step\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration_8\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_fiber_card_step, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration_8\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration_8\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"incoming_response_fiber_card_step\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_fiber_card_step, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiberCard\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiberCard.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{1, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"incoming_response_matrix_factor_step\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration_10\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_matrix_factor_step, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.observation0 : {p : Nat} →
  {M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p} →
    {Q : Type} →
      (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) →
        (d : Nat) →
          [Fintype.{0}
                (@Quotient.{1} Q
                  (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))] →
            [Fintype.{0}
                  (@Quotient.{1} Q
                    (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))] →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{1, 0, 0, 0, 0}
                Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.signature PUnit.unit.{1}
                (@Sigma.mk.{0, 1} Nat
                  (fun (p : Nat) =>
                    @Sigma.{0, 1} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p)
                      fun (M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p) =>
                      @Sigma.{1, 0} Type fun (Q : Type) =>
                        @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
                          fun (x : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) => Nat)
                  p
                  (@Sigma.mk.{0, 1} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p)
                    (fun (M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p) =>
                      @Sigma.{1, 0} Type fun (Q : Type) =>
                        @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
                          fun (x : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) => Nat)
                    M
                    (@Sigma.mk.{1, 0} Type
                      (fun (Q : Type) =>
                        @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
                          fun (x : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) => Nat)
                      Q
                      (@Sigma.mk.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
                        (fun (x : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) => Nat) L
                        d)))) :=
  fun {p : Nat} {M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p} {Q : Type}
    (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) (d : Nat)
    [Fintype.{0}
        (@Quotient.{1} Q (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L d))]
    [Fintype.{0}
        (@Quotient.{1} Q
          (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))] =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{1, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.signature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 1} Nat
      (fun (p : Nat) =>
        @Sigma.{0, 1} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p)
          fun (M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p) =>
          @Sigma.{1, 0} Type fun (Q : Type) =>
            @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
              fun (x : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) => Nat)
      p
      (@Sigma.mk.{0, 1} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p)
        (fun (M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p) =>
          @Sigma.{1, 0} Type fun (Q : Type) =>
            @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
              fun (x : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) => Nat)
        M
        (@Sigma.mk.{1, 0} Type
          (fun (Q : Type) =>
            @Sigma.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
              fun (x : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) => Nat)
          Q
          (@Sigma.mk.{0, 0} (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q)
            (fun (x : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) => Nat) L d))))
    (@D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incomingResponseMatrix p M Q L)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"incoming_response_matrix_factor_step\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration_10\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_matrix_factor_step, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration_10\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration_10\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"incoming_response_matrix_factor_step\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.incoming_response_matrix_factor_step, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration_10\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"MatrixFactorStep\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration_10, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.MatrixFactorStep.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"incoming_response_step\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration_6\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.incoming_response_step, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.observation0 : {n : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {Q : Type} →
      (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift n A Q) →
        (d : Nat) →
          {u v : Q} →
            (h :
                @Setoid.r.{1} Q
                  (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response n A Q L
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  u v) →
              (a : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n n A) →
                (hu :
                    @Eq.{1} (Fin n)
                      (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.project n A Q L u)
                      (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.target n n A a)) →
                  (hv :
                      @Eq.{1} (Fin n)
                        (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.project n A Q L v)
                        (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.target n n A a)) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthSignature PUnit.unit.{1}
                      PUnit.unit.{1} :=
  fun {n : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} {Q : Type}
    (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift n A Q) (d : Nat) {u v : Q}
    (h :
      @Setoid.r.{1} Q
        (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response n A Q L
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        u v)
    (a : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n n A)
    (hu :
      @Eq.{1} (Fin n) (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.project n A Q L u)
        (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.target n n A a))
    (hv :
      @Eq.{1} (Fin n) (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.project n A Q L v)
        (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.target n n A a)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthSignature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthActual PUnit.unit.{1} PUnit.unit.{1} d

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"incoming_response_step\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration_6\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.incoming_response_step, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration_6\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration_6\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"incoming_response_step\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.incoming_response_step, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"IncomingStep\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.IncomingStep.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"unsweep_sweep\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_sweep, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.observation0 : {n k : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k} →
      {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k} →
        (phi :
            (i : Fin n) →
              (z : Fin k) →
                Equiv.{1, 1} (@D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.EdgePair n n k A R i z)
                  (@D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.EdgePair n k k R B i z)) →
          {d : Nat} →
            {i j : Fin n} →
              {z : Fin k} →
                (alpha : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.FinitePath n A d i j) →
                  (r : Fin (R j z)) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.numberSignature PUnit.unit.{1}
                      (@Sigma.mk.{0, 0} Nat
                        (fun (n : Nat) =>
                          @Sigma.{0, 0} Nat fun (k : Nat) =>
                            @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                              fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
                              @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
                        n
                        (@Sigma.mk.{0, 0} Nat
                          (fun (k : Nat) =>
                            @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                              fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
                              @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
                          k
                          (@Sigma.mk.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                            (fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
                              @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
                            R (@Sigma.mk.{0, 0} (Fin n) (fun (x : Fin n) => Fin k) j z)))) :=
  fun {n k : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n}
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k}
    {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k}
    (phi :
      (i : Fin n) →
        (z : Fin k) →
          Equiv.{1, 1} (@D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.EdgePair n n k A R i z)
            (@D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.EdgePair n k k R B i z))
    {d : Nat} {i j : Fin n} {z : Fin k}
    (alpha : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.FinitePath n A d i j) (r : Fin (R j z)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.numberSignature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.numberActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} Nat fun (k : Nat) =>
          @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
            fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
            @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
      n
      (@Sigma.mk.{0, 0} Nat
        (fun (k : Nat) =>
          @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
            fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
            @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
        k
        (@Sigma.mk.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
          (fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
            @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
          R (@Sigma.mk.{0, 0} (Fin n) (fun (x : Fin n) => Fin k) j z))))
    r

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"unsweep_sweep\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_sweep, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"unsweep_sweep\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_sweep, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepSweep\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepSweep.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"unsweep_append\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_append, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.observation0 : {n k : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k} →
      {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k} →
        (phi :
            (i : Fin n) →
              (z : Fin k) →
                Equiv.{1, 1} (@D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.EdgePair n n k A R i z)
                  (@D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.EdgePair n k k R B i z)) →
          {d : Nat} →
            {i : Fin n} →
              {t u z : Fin k} →
                (r : Fin (R i t)) →
                  (beta : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.FinitePath k B d t u) →
                    (b : Fin (B u z)) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                        Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.numberSignature PUnit.unit.{1}
                        (@Sigma.mk.{0, 0} Nat
                          (fun (n : Nat) =>
                            @Sigma.{0, 0} Nat fun (k : Nat) =>
                              @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                                fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
                                @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
                          n
                          (@Sigma.mk.{0, 0} Nat
                            (fun (k : Nat) =>
                              @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                                fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
                                @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
                            k
                            (@Sigma.mk.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                              (fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
                                @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
                              R (@Sigma.mk.{0, 0} (Fin n) (fun (x : Fin n) => Fin k) i t)))) :=
  fun {n k : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n}
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k}
    {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k}
    (phi :
      (i : Fin n) →
        (z : Fin k) →
          Equiv.{1, 1} (@D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.EdgePair n n k A R i z)
            (@D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.EdgePair n k k R B i z))
    {d : Nat} {i : Fin n} {t u z : Fin k} (r : Fin (R i t))
    (beta : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.FinitePath k B d t u) (b : Fin (B u z)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.numberSignature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.numberActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} Nat fun (k : Nat) =>
          @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
            fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
            @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
      n
      (@Sigma.mk.{0, 0} Nat
        (fun (k : Nat) =>
          @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
            fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
            @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
        k
        (@Sigma.mk.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
          (fun (R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) =>
            @Sigma.{0, 0} (Fin n) fun (x : Fin n) => Fin k)
          R (@Sigma.mk.{0, 0} (Fin n) (fun (x : Fin n) => Fin k) i t))))
    r

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"unsweep_append\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_append, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"unsweep_append\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.unsweep_append, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"UnsweepAppend\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.UnsweepAppend.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"exchange_chain_trans\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_trans, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.observation0 : {a b c : Nat} →
  {X : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat a a} →
    {Y : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat b b} →
      {Z : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat c c} →
        {l₁ l₂ : Nat} →
          (left :
              @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring a b X Y
                l₁) →
            (right :
                @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring b c Y
                  Z l₂) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.signature PUnit.unit.{1} l₁ :=
  fun {a b c : Nat} {X : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat a a}
    {Y : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat b b}
    {Z : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat c c} {l₁ l₂ : Nat}
    (left :
      @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring a b X Y l₁)
    (right :
      @D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.{0} Nat Nat.instSemiring b c Y Z l₂) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.signature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.actual PUnit.unit.{1} l₁ l₂

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"exchange_chain_trans\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_trans, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"exchange_chain_trans\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.exchange_chain_trans, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"ChainTrans\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ChainTrans.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.arena) (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"finite_response_chain_to\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration_7\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.finite_response_chain_to, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.observation0 : {p : Nat} →
  {M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p} →
    {Q : Type} →
      [Fintype.{0} Q] →
        (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) →
          (start length : Nat) →
            {r : Nat} →
              (eEnd :
                  Equiv.{1, 1}
                    (@Quotient.{1} Q
                      (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start length)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (Fin r)) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthSignature PUnit.unit.{1}
                  PUnit.unit.{1} :=
  fun {p : Nat} {M : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat p p} {Q : Type} [Fintype.{0} Q]
    (L : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift p M Q) (start length : Nat) {r : Nat}
    (eEnd :
      Equiv.{1, 1}
        (@Quotient.{1} Q
          (@D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.IncomingLift.response p M Q L
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start length)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (Fin r)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.depthSignature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.actual PUnit.unit.{1} PUnit.unit.{1}
    length

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"finite_response_chain_to\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration_7\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.finite_response_chain_to, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration_7\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration_7\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"finite_response_chain_to\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.finite_response_chain_to, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"FiniteChainTo\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.FiniteChainTo.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
