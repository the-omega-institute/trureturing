import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.FibonacciRankEulerTail
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail

open Finset
open _root_.D5.S3.Arith.Robin.FibonacciRankEulerTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The prime weight varies while both bounds and the complete rank bucket remain fixed. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ), 5 < d →
    (∑ p ∈ rankBucket d, R.readout () () p) ≤ 6 * (harmonic d : ℝ) / d ∧
      6 * (harmonic d : ℝ) / d ≤ 6 * (1 + Real.log d) / d

def actual : Realization signature :=
  realize signature (fun _ _ p => Real.log ((p : ℝ) / ((p : ℝ) - 1)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 100) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 7 (by decide)).1
  have hb : rankBucket 7 = {13} := by
    norm_num [rankBucket, Nat.fib_add_two]
    intro k h1 h7
    interval_cases k <;> norm_num [Nat.fib_add_two]
  change (∑ _p ∈ rankBucket 7, (100 : ℝ)) ≤ 6 * (harmonic 7 : ℝ) / 7 at hh
  rw [hb] at hh
  norm_num [harmonic, Finset.sum_range_succ] at hh

def registration : Registration arena (∀ (d : ℕ), 5 < d →
    (∑ p ∈ rankBucket d, Real.log ((p : ℝ) / ((p : ℝ) - 1))) ≤
        6 * (harmonic d : ℝ) / d ∧
      6 * (harmonic d : ℝ) / d ≤ 6 * (1 + Real.log d) / d) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Robin.FibonacciRankEulerTail.result) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ p => Real.log ((p : ℝ) / ((p : ℝ) - 1))) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Robin") "FibonacciRankEulerTail") "result") "Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail/Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration,
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
    (fun _ _ p => Real.log ((p : ℝ) / ((p : ℝ) - 1))) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Robin.FibonacciRankEulerTail, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `D5.S3.Arith.Robin.FibonacciRankEulerTail.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.observationFact0, `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail


noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.arena
noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.arena
noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.arena) (Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration).actual

noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `D5.S3.Arith.Robin.FibonacciRankEulerTail.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration).bridge

noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.observation0 : (d : Nat) →
  (hd : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) d) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.signature PUnit.unit.{1} →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (d : Nat) (hd : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) d) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.signature Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.actual
    PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `D5.S3.Arith.Robin.FibonacciRankEulerTail.result, part := .type, path := [.body, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `D5.S3.Arith.Robin.FibonacciRankEulerTail.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration).actual (Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration).variation.2.choose (Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration).variation.1 (Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Robin\",\"FibonacciRankEulerTail\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail, declaration := `Reg.D5.S3.Arith.Robin.FibonacciRankEulerTail.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
