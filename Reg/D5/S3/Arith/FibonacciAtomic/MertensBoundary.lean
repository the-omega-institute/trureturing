import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.MertensBoundary
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.MertensBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Asymptotics
open scoped BigOperators

namespace Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => boundary x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x ^ (2 : ℕ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ a : ℝ, 0 < a →
    ((r.readout () () =O[atTop] (fun X : ℝ => X ^ a)) ↔
      coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a)) ∧
    ((coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a)) ↔
      coprimeMertens 1 =O[atTop] (fun X : ℝ => X ^ a))

theorem restricted_linear : coprimeMertens 70 =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
  classical
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Real.rpow_one, Real.norm_eq_abs, one_mul, abs_of_nonneg hx]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        |if n.Coprime 70 then (ArithmeticFunction.moebius n : ℝ) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      split_ifs
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      · norm_num
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := ((h 1 (by norm_num)).1).mpr restricted_linear
  change (fun x : ℝ => x ^ (2 : ℕ)) =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) at hb
  obtain ⟨C, hC⟩ := isBigO_iff.mp hb
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC
  let x := max (max T (|C| + 1)) 1
  have hx1 : 1 ≤ x := le_max_right _ _
  have hxT : T ≤ x := (le_max_left _ _).trans (le_max_left _ _)
  have hxC : |C| + 1 ≤ x := (le_max_right _ _).trans (le_max_left _ _)
  have hx : 0 ≤ x := by linarith
  have he := hT x hxT
  simp only [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg (sq_nonneg x),
    abs_of_nonneg hx] at he
  have hc := le_abs_self C
  nlinarith

def registration : Registration arena
    (∀ a : ℝ, 0 < a →
      ((boundary =O[atTop] (fun X : ℝ => X ^ a)) ↔
        coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a)) ∧
      ((coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a)) ↔
        coprimeMertens 1 =O[atTop] (fun X : ℝ => X ^ a))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨power_bounds_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (7 : ℝ), ?_⟩
    change boundary 0 ≠ boundary 7
    norm_num [boundary, Finset.sum_Ioc_succ_top]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.MertensBoundary.power_bounds_iff) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => boundary x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "MertensBoundary") "power_bounds_iff") "Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary/Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => boundary x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.MertensBoundary, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `D5.S3.Arith.FibonacciAtomic.MertensBoundary.power_bounds_iff, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.arena) (Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration).actual

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"power_bounds_iff\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `D5.S3.Arith.FibonacciAtomic.MertensBoundary.power_bounds_iff, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration).bridge

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.observation0 : (a : Real) →
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.signature PUnit.unit.{1} →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (a : Real)
    (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.signature Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.actual
    PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"power_bounds_iff\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `D5.S3.Arith.FibonacciAtomic.MertensBoundary.power_bounds_iff, part := .type, path := [.body, .body, .function, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"power_bounds_iff\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `D5.S3.Arith.FibonacciAtomic.MertensBoundary.power_bounds_iff, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"MertensBoundary\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
