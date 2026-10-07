import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
open _root_.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- A known high-bit coordinate selects the full physical clock/readout function. -/
abbrev signature : Signature where
  Params := Nat
  State _ := Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat → Nat → Fin 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j b => rawBit (2 ^ j) b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : Nat) (b : Fin 2),
    let P := 2 ^ j
    let read := R.readout () j b
    (∀ n r, r < P →
      (read n r).val = (b.val + n / P + (threshold P n r).val) % 2 ∧
      sensor P b n r = threshold P n r) ∧
    IsLeast (waitingBounds P j read) (sharpWait j) ∧
    CorrectOn read (rawMidpoint P b j) 0 0 P ∧
    ∀ r, r < P → (execute read (rawMidpoint P b j) 0 r).2 ≤ sharpWait j

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 0 1).1 0 0 (by decide)
  norm_num [rejected, realize, threshold] at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dyadic_forward_waiting_optimality, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    intro h
    have point := congrFun (congrFun h 0) 0
    norm_num [actual, realize, rawBit] at point

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.dyadic_forward_waiting_optimality) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ j b => rawBit (2 ^ j) b) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Budget") "DyadicForwardWaitingOptimality") "dyadic_forward_waiting_optimality") "Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality/Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ j b => rawBit (2 ^ j) b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "value"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.dyadic_forward_waiting_optimality, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.observationFact0, `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality


noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.arena
noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.arena
noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.arena) (Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration).actual

noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"dyadic_forward_waiting_optimality\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.dyadic_forward_waiting_optimality, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration).bridge

noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.observation0 : (j : Nat) →
  (b : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.signature PUnit.unit.{1} j :=
  fun (j : Nat) (b : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
  have P : Nat :=
    @HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j;
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.signature
    Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.actual PUnit.unit.{1} j b

noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"dyadic_forward_waiting_optimality\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"letBody\",\"letValue\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.dyadic_forward_waiting_optimality, part := .type, path := [.body, .body, .letBody, .letValue], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"dyadic_forward_waiting_optimality\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.dyadic_forward_waiting_optimality, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration).actual (Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration).variation.2.choose (Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration).variation.1 (Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Budget\",\"DyadicForwardWaitingOptimality\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality, declaration := `Reg.D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
