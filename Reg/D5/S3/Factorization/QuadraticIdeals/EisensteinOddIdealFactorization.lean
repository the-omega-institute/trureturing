import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization

open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Ideal EisensteinOrder
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => orientedIdeal b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (⊥ : Ideal EisensteinOrder)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (b : ℕ) (_hb : Odd b),
    R.readout () () b =
      ∏ p ∈ (blockNorm b).primeFactors,
        (orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}) ^
          (blockNorm b).factorization p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 1 (by decide)
  change (⊥ : Ideal EisensteinOrder) =
    ∏ p ∈ (blockNorm 1).primeFactors,
      (orientedIdeal 1 ⊔ Ideal.span {(p : EisensteinOrder)}) ^
        (blockNorm 1).factorization p at hzero
  rw [← eisenstein_odd_ideal_factorization 1 (by decide)] at hzero
  have heta : orientedFactor 1 ∈ orientedIdeal 1 := Ideal.mem_span_singleton_self _
  rw [← hzero] at heta
  have hz : orientedFactor 1 = 0 := by simpa only [Submodule.mem_bot] using heta
  have hr := congrArg QuadraticAlgebra.re hz
  norm_num [orientedFactor] at hr

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro b hb
    exact eisenstein_odd_ideal_factorization b hb
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (_ : Unit) (x y : ℕ), orientedIdeal x ≠ orientedIdeal y
    refine ⟨(), 1, 3, ?_⟩
    intro heq
    have hC7 : (QuadraticAlgebra.C (7 : ℤ) : EisensteinOrder) = 7 := by
      norm_num [QuadraticAlgebra.C_eq_algebraMap]
    have h7 : (7 : EisensteinOrder) ∈ orientedIdeal 1 := by
      apply Ideal.mem_span_singleton.mpr
      have hc := ((eisenstein_odd_scalar_quotient 1 (by decide)).1 (7 : ℤ)).mpr
        (by norm_num [blockNorm])
      simpa only [hC7] using hc
    rw [heq] at h7
    have hdiv := ((eisenstein_odd_scalar_quotient 3 (by decide)).1 (7 : ℤ)).mp
      (by
        apply Ideal.mem_span_singleton.mp
        simpa only [orientedIdeal, hC7] using h7)
    norm_num [blockNorm] at hdiv

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.eisenstein_odd_ideal_factorization) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => orientedIdeal b) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "QuadraticIdeals") "EisensteinOddIdealFactorization") "eisenstein_odd_ideal_factorization") "Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization/Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ b => orientedIdeal b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.eisenstein_odd_ideal_factorization, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.observationFact0, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.arena) (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration).actual

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"eisenstein_odd_ideal_factorization\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.eisenstein_odd_ideal_factorization, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration).bridge

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.observation0 : (b : Nat) →
  (hb : @Odd.{0} Nat Nat.instSemiring b) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (b : Nat) (hb : @Odd.{0} Nat Nat.instSemiring b) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.signature
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.actual PUnit.unit.{1} PUnit.unit.{1} b

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"eisenstein_odd_ideal_factorization\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.eisenstein_odd_ideal_factorization, part := .type, path := [.body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"eisenstein_odd_ideal_factorization\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.eisenstein_odd_ideal_factorization, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration).actual (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration).variation.2.choose (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration).variation.1 (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddIdealFactorization\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddIdealFactorization.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
