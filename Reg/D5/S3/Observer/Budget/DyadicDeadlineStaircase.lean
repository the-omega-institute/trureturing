import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Budget.DyadicDeadlineStaircase
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase

open _root_.D5.S3.Observer.Budget.DyadicDeadlineStaircase
open _root_.D5.S3.Observer.Budget.DyadicPrefixDelayRange
open _root_.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev timingSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def timingActual : Realization timingSignature :=
  realize timingSignature (fun _ _ d => earliestTime d (2 ^ d - 1))
    (fun e => nomatch e)

def timingRejected : Realization timingSignature :=
  realize timingSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev timingArena : Arena where
  signature := timingSignature
  Law R := ∀ d : Nat,
    let P := 2 ^ (d + 1)
    let W := sharpWait (d + 1)
    R.readout () () d + P = W + P ∧
    (∀ k : Nat, k < d →
      earliestTime d (2 ^ d - 1 - 2 ^ k) + P = W + 2 ^ (k + 1)) ∧
    (∀ t : Nat, t < 2 ^ d → t.bitIndices.length + 2 ≤ d →
      earliestTime d t + P ≤ W) ∧
    (∀ t : Nat, t < 2 ^ d →
      t.bitIndices.length ≤ d ∧
      (t.bitIndices.length = d → t = 2 ^ d - 1) ∧
      (t.bitIndices.length + 1 = d →
        ∃ k : Nat, k < d ∧ t + 2 ^ k = 2 ^ d - 1))

theorem timingRejected_law : ¬ timingArena.Law timingRejected := by
  intro h
  have hh := (h 0).1
  norm_num [timingRejected, realize, sharpWait] at hh

def timingRegistration : Registration timingArena (timingArena.Law timingActual) where
  actual := timingActual
  bridge := Iff.rfl
  variation := ⟨exceptional_prefix_timing, timingRejected, timingRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨timingRejected, ?_, rfl, timingRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [timingActual, realize, earliestTime, Nat.bitIndices]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Budget.DyadicDeadlineStaircase.exceptional_prefix_timing) (type_of% (realize.{0, 0, 0, 0, 0} timingSignature
    (fun _ _ d => earliestTime d (2 ^ d - 1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Budget") "DyadicDeadlineStaircase") "exceptional_prefix_timing") "Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase/Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(timingArena)⟩,
  objectArena := .source ⟨(timingArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (timingArena) ⟨(timingRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} timingSignature
    (fun _ _ d => earliestTime d (2 ^ d - 1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Budget.DyadicDeadlineStaircase, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `D5.S3.Observer.Budget.DyadicDeadlineStaircase.exceptional_prefix_timing, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.observationFact0, `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.anchorEnumeration }


#print axioms timingRegistration

end Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase


noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingArena
noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingArena
noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingArena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingArena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingArena
      Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingActual)
    Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingRegistration)

noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"exceptional_prefix_timing\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `D5.S3.Observer.Budget.DyadicDeadlineStaircase.exceptional_prefix_timing, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingArena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingArena
    Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingActual)
  Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingRegistration)

noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.observation0 : (d : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingSignature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (d : Nat) =>
  have P : Nat :=
    @HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))));
  have W : Nat :=
    D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.sharpWait
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))));
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingSignature
    Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingActual PUnit.unit.{1} PUnit.unit.{1} d

noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"exceptional_prefix_timing\"],\"part\":\"type\",\"path\":[\"body\",\"letBody\",\"letBody\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `D5.S3.Observer.Budget.DyadicDeadlineStaircase.exceptional_prefix_timing, part := .type, path := [.body, .letBody, .letBody, .function, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"exceptional_prefix_timing\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `D5.S3.Observer.Budget.DyadicDeadlineStaircase.exceptional_prefix_timing, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingRegistration).actual (Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingRegistration).variation.2.choose (Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingRegistration).variation.1 (Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicDeadlineStaircase\",\"timingRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase, declaration := `Reg.D5.S3.Observer.Budget.DyadicDeadlineStaircase.timingRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
