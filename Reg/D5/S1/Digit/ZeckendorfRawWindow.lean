import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.ZeckendorfRawWindow
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S1.Words

namespace Reg.D5.S1.Digit.ZeckendorfRawWindow
noncomputable section
open Classical

abbrev coordinateSignature : Signature where
  Params := Unit
  State := fun _ => List (Fin 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateActual : Realization coordinateSignature := realize coordinateSignature
  (fun _ _ w => support w) (fun e => nomatch e)

abbrev coordinateArena : Arena where
  signature := coordinateSignature
  Law R := ∀ w : List (Fin 2), NoAdjacentOnes w →
    (R.readout () () w).IsZeckendorfRep ∧
      (∀ k ∈ R.readout () () w, k < w.length + 2) ∧
      ((R.readout () () w).map Nat.fib).sum = (fibPair w).1 ∧
      ((R.readout () () w).map (fun k => Nat.fib (k + 1))).sum = (fibPair w).2

def coordinateRejected : Realization coordinateSignature := realize coordinateSignature
  (fun _ _ _ => [2]) (fun e => nomatch e)

theorem coordinateRejectedLaw : ¬ coordinateArena.Law coordinateRejected := by
  intro h
  have hh := (h [] (by simp [NoAdjacentOnes])).2.2.2
  norm_num [coordinateRejected, realize, fibPair] at hh

def coordinateRegistration : Registration coordinateArena (coordinateArena.Law coordinateActual) where
  actual := coordinateActual
  bridge := Iff.rfl
  variation := ⟨source_word_coordinates, coordinateRejected, coordinateRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coordinateRejected, ?_, rfl, coordinateRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), [], [1], ?_⟩
    simp [coordinateActual, coordinateRejected, realize, support]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Digit.ZeckendorfRawWindow.source_word_coordinates) (type_of% (realize.{0, 0, 0, 0, 0} coordinateSignature (fun _ _ w => support w) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Digit") "ZeckendorfRawWindow") "source_word_coordinates") "Reg.D5.S1.Digit.ZeckendorfRawWindow/Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(coordinateArena)⟩,
  objectArena := .source ⟨(coordinateArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (coordinateArena) ⟨(coordinateRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} coordinateSignature (fun _ _ w => support w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Digit.ZeckendorfRawWindow, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.source_word_coordinates, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.canonicalArenaFact, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.sourceBridgeFact, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.observationFact0, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.anchorEnumeration }


abbrev expansionSignature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List (Bool × Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def expansionActual : Realization expansionSignature := realize expansionSignature
  (fun _ n t => ((List.range t).map (fun i => q (n + i))).flatMap mu)
  (fun e => nomatch e)

abbrev expansionArena : Arena where
  signature := expansionSignature
  Law R := ∀ n t : ℕ,
    R.readout () n t =
      (List.range (goldenSubstStart (n + t) - goldenSubstStart n)).map
        (fun i => q (goldenSubstStart n + i))

def expansionRejected : Realization expansionSignature := realize expansionSignature
  (fun _ _ _ => [(false, false)]) (fun e => nomatch e)

theorem expansionRejectedLaw : ¬ expansionArena.Law expansionRejected := by
  intro h
  have hh := h 0 0
  simp [expansionRejected, realize, expansionActual, q, mu] at hh

def expansionRegistration : Registration expansionArena (expansionArena.Law expansionActual) where
  actual := expansionActual
  bridge := Iff.rfl
  variation := ⟨source_expansion, expansionRejected, expansionRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨expansionRejected, ?_, rfl, expansionRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    intro he
    norm_num [expansionActual, realize, q, parity, D5.S0.Conventions.wdigits,
      Nat.greatestFib] at he
    simp [mu] at he

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Digit.ZeckendorfRawWindow.source_expansion) (type_of% (realize.{0, 0, 0, 0, 0} expansionSignature
    (fun _ n t => ((List.range t).map (fun i => q (n + i))).flatMap mu)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Digit") "ZeckendorfRawWindow") "source_expansion") "Reg.D5.S1.Digit.ZeckendorfRawWindow/Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(expansionArena)⟩,
  objectArena := .source ⟨(expansionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (expansionArena) ⟨(expansionRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} expansionSignature
    (fun _ n t => ((List.range t).map (fun i => q (n + i))).flatMap mu)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Digit.ZeckendorfRawWindow, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.source_expansion, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.canonicalArenaFact, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.canonicalObjectArenaFact, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.sourceBridgeFact, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.observationFact0, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.anchorEnumeration }


abbrev congruenceSignature : Signature where
  Params := ℕ
  State := fun _ => List (Fin 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List (Fin 2) → Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def congruenceActual : Realization congruenceSignature := realize congruenceSignature
  (fun _ c w => residual c w) (fun e => nomatch e)

abbrev congruenceArena : Arena where
  signature := congruenceSignature
  Law R := ∀ (c : ℕ) (w v : List (Fin 2)), NoAdjacentOnes w → NoAdjacentOnes v →
    window c (value w) = window c (value v) →
    R.readout () c w = residual c v

def congruenceRejected : Realization congruenceSignature := realize congruenceSignature
  (fun _ _ _ => fun _ => some true) (fun e => nomatch e)

theorem congruenceRejectedLaw : ¬ congruenceArena.Law congruenceRejected := by
  intro h
  have hh := h 0 [] [] (by simp [NoAdjacentOnes]) (by simp [NoAdjacentOnes]) rfl
  have := congrFun hh []
  norm_num [congruenceRejected, realize, D5.S1.Digit.ZeckendorfRawWindow.residual,
    parity, value, fibPair, D5.S0.Conventions.wdigits,
    NoAdjacentOnes, List.isChain_cons_cons, Nat.greatestFib] at this

def congruenceRegistration : Registration congruenceArena (congruenceArena.Law congruenceActual) where
  actual := congruenceActual
  bridge := Iff.rfl
  variation := ⟨window_residual_congruence, congruenceRejected, congruenceRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨congruenceRejected, ?_, rfl, congruenceRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨0, [], [1], ?_⟩
    intro he
    have hh := congrFun he []
    have h0 : residual 0 [] [] = some false := by
      norm_num [D5.S1.Digit.ZeckendorfRawWindow.residual, value, fibPair, parity,
        D5.S0.Conventions.wdigits, NoAdjacentOnes, List.isChain_cons_cons,
        Nat.greatestFib]
    have h1 : residual 0 [1] [] = some true := by
      norm_num [D5.S1.Digit.ZeckendorfRawWindow.residual, value, fibPair, parity,
        D5.S0.Conventions.wdigits, NoAdjacentOnes, List.isChain_cons_cons,
        Nat.greatestFib]
    change residual 0 [] [] = residual 0 [1] [] at hh
    rw [h0, h1] at hh
    cases hh

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Digit.ZeckendorfRawWindow.window_residual_congruence) (type_of% (realize.{0, 0, 0, 0, 0} congruenceSignature (fun _ c w => residual c w) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Digit") "ZeckendorfRawWindow") "window_residual_congruence") "Reg.D5.S1.Digit.ZeckendorfRawWindow/Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(congruenceArena)⟩,
  objectArena := .source ⟨(congruenceArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (congruenceArena) ⟨(congruenceRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} congruenceSignature (fun _ c w => residual c w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Digit.ZeckendorfRawWindow, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.window_residual_congruence, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.canonicalArenaFact, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.canonicalObjectArenaFact, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.sourceBridgeFact, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.observationFact0, `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.anchorEnumeration }


#print axioms coordinateRegistration
#print axioms expansionRegistration
#print axioms congruenceRegistration
end
end Reg.D5.S1.Digit.ZeckendorfRawWindow


noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceArena
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceArena
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateArena
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateArena
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionArena
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionArena
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceArena) (Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceRegistration).actual

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"window_residual_congruence\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.window_residual_congruence, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceRegistration).bridge

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.observation0 : (c : Nat) →
  (w v : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    (hw : D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes w) →
      (hv : D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes v) →
        (he :
            @Eq.{1} (List.{0} (Prod.{0, 0} Bool Bool))
              (D5.S1.Digit.ZeckendorfRawWindow.window c (D5.S1.Digit.ZeckendorfRawWindow.value w))
              (D5.S1.Digit.ZeckendorfRawWindow.window c (D5.S1.Digit.ZeckendorfRawWindow.value v))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceSignature PUnit.unit.{1} c :=
  fun (c : Nat) (w v : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hw : D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes w)
    (hv : D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes v)
    (he :
      @Eq.{1} (List.{0} (Prod.{0, 0} Bool Bool))
        (D5.S1.Digit.ZeckendorfRawWindow.window c (D5.S1.Digit.ZeckendorfRawWindow.value w))
        (D5.S1.Digit.ZeckendorfRawWindow.window c (D5.S1.Digit.ZeckendorfRawWindow.value v))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceSignature Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceActual
    PUnit.unit.{1} c w

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"window_residual_congruence\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.window_residual_congruence, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"window_residual_congruence\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.window_residual_congruence, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceRegistration).actual (Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceRegistration).variation.2.choose (Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceRegistration).variation.1 (Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"congruenceRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.congruenceRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateArena) (Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateRegistration).actual

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"source_word_coordinates\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.source_word_coordinates, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateRegistration).bridge

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.observation0 : (w : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
  (hw : D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes w) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateSignature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (w : List.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hw : D5.S0.Automata.BinaryZeckendorfLanguage.NoAdjacentOnes w) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateSignature Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateActual
    PUnit.unit.{1} PUnit.unit.{1} w

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"source_word_coordinates\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.source_word_coordinates, part := .type, path := [.body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"source_word_coordinates\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.source_word_coordinates, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateRegistration).actual (Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateRegistration).variation.2.choose (Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateRegistration).variation.1 (Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"coordinateRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.coordinateRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionArena) (Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionRegistration).actual

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"source_expansion\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.source_expansion, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionRegistration).bridge

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.observation0 : (n t : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionSignature PUnit.unit.{1} n :=
  fun (n t : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionSignature Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionActual
    PUnit.unit.{1} n t

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"source_expansion\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.source_expansion, part := .type, path := [.body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"source_expansion\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Digit.ZeckendorfRawWindow, declaration := `D5.S1.Digit.ZeckendorfRawWindow.source_expansion, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionRegistration).actual (Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionRegistration).variation.2.choose (Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionRegistration).variation.1 (Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Digit\",\"ZeckendorfRawWindow\",\"expansionRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Digit.ZeckendorfRawWindow, declaration := `Reg.D5.S1.Digit.ZeckendorfRawWindow.expansionRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
