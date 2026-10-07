import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Filter Asymptotics
open scoped BigOperators Topology

namespace Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
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

def actual : Realization signature :=
  realize signature (fun _ _ m => delta m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ m a b : ℕ, 2 ≤ m → 0 < a → 0 < b → Nat.ModEq m.factorial a b →
      delta m ≤ smallWeight m a / smallWeight m b ∧
        smallWeight m a / smallWeight m b ≤ (delta m)⁻¹) ∧
    (∀ m : ℕ, 4 ≤ m →
      (∑ p ∈ Ioc 0 m with p.Prime,
        ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1)) ≤
          (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹) ∧
    (fun m : ℕ => r.readout () () m - 1) =O[atTop]
      (fun m : ℕ => (Real.sqrt m)⁻¹)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ho := h.2.2
  change (fun _ : ℕ => (0 : ℝ) - 1) =O[atTop] (fun m : ℕ => (Real.sqrt m)⁻¹) at ho
  have hi : Tendsto (fun m : ℕ => (Real.sqrt m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hc : (0 : ℝ) - 1 = 0 := tendsto_nhds_unique tendsto_const_nhds (ho.trans_tendsto hi)
  norm_num at hc

def registration : Registration arena (
(∀ m a b : ℕ, 2 ≤ m → 0 < a → 0 < b → Nat.ModEq m.factorial a b →
      delta m ≤ smallWeight m a / smallWeight m b ∧
        smallWeight m a / smallWeight m b ≤ (delta m)⁻¹) ∧
    (∀ m : ℕ, 4 ≤ m →
      (∑ p ∈ Ioc 0 m with p.Prime,
        ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1)) ≤
          (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹) ∧
    (fun m : ℕ => delta m - 1) =O[atTop] (fun m : ℕ => (Real.sqrt m)⁻¹)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change delta 0 ≠ delta 2
    have hprimes : (Ioc 0 2).filter Nat.Prime = {2} := by decide
    norm_num [delta, hprimes]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ m => delta m) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "ModularDivisorWeightTransfer") "result") "Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer/Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ m => delta m) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "fn", "arg", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena) (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).actual

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).bridge

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.observation0 : (m : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.signature PUnit.unit.{1} →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (m : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.signature
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.actual PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"result\"],\"part\":\"type\",\"path\":[\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result, part := .type, path := [.argument, .argument, .function, .argument, .body, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
