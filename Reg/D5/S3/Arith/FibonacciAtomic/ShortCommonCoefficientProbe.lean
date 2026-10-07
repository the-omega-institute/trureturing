import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open _root_.D5.S3.Arith.ZeckendorfFutureKernel (legal value)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Lean LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
noncomputable section

abbrev signature : Signature where
  Params := Nat
  State _ := List Window
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ H := ZMod H × ZMod H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ H w => windowCoefficients H w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (_hH : 2 ≤ H),
    5 ≤ firstIndex H ∧
    2 * H < Nat.fib (firstIndex H) ∧ Nat.fib (firstIndex H) < 4 * H ∧
    (∀ A B : ZMod H, ∃ w : List Window,
      w.length ≤ lengthBound H ∧ w ≠ [] ∧ firstTwoZero w ∧ Success w ∧
      R.readout () H w = (A, B) ∧
      (∀ u v : ZMod H, value u v (flatten w) = A * u + B * v) ∧
      (∀ (epsilon : Bool) (p : List Window), legal epsilon (flatten p) →
        ∃ N : Nat, 0 < N ∧ initialized epsilon (p ++ w) = some N)) ∧
    D H ≤ D00 H ∧ D00 H ≤ (lengthBound H : WithTop Nat) ∧
    lengthBound H ≤ 2 * Nat.log 2 H + 5 ∧
    (lengthBound H : Real) ≤ (7 / Real.log 2) * Real.log (H : Real)

theorem actual_law : arena.Law actual := by
  intro H hH
  simpa only [actual, realize] using result H hH

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, _, _, _, _, hc, _⟩ := (h 2 (by omega)).2.2.2.1 1 0
  have hh : (0 : ZMod 2) = 1 := congrArg Prod.fst hc
  exact (by decide : (0 : ZMod 2) ≠ 1) hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, [.high], [.zero, .middle], ?_⟩
    change windowCoefficients 2 [.high] ≠ windowCoefficients 2 [.zero, .middle]
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.result) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ H w => windowCoefficients H w) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "ShortCommonCoefficientProbe") "result") "Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe/Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ H w => windowCoefficients H w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "arg", "arg", "arg", "fn", "arg", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.anchorEnumeration }


end
end Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.arena
      Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.actual)
    Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.arena
    Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.actual)
  Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.observation0 : (H : Nat) →
  (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) →
    (A B : ZMod H) →
      (w : List.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.signature PUnit.unit.{1} H :=
  fun (H : Nat) (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
    (A B : ZMod H) (w : List.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.signature
    Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.actual PUnit.unit.{1} H w

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.result, part := .type, path := [.body, .body, .argument, .argument, .argument, .function, .argument, .body, .body, .argument, .body, .argument, .argument, .argument, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ShortCommonCoefficientProbe\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
