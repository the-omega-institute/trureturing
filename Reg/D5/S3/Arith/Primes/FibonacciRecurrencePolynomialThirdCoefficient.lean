import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient

open _root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
open _root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature
    (fun _ _ n => (fibonacciRecurrencePolynomial (n + 5)).coeff n)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law x := ∀ n : ℕ, x.readout () () n = (Nat.choose (n + 2) 2 : ℤ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0
  change (0 : ℤ) = (Nat.choose 2 2 : ℤ) at hbad
  norm_num at hbad

noncomputable def registration : Registration arena
    (∀ n : ℕ,
      (fibonacciRecurrencePolynomial (n + 5)).coeff n =
        (Nat.choose (n + 2) 2 : ℤ)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_recurrence_polynomial_third_coefficient,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change (fibonacciRecurrencePolynomial 5).coeff 0 ≠
      (fibonacciRecurrencePolynomial 6).coeff 1
    norm_num [fibonacciRecurrencePolynomial]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.fibonacci_recurrence_polynomial_third_coefficient) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ n => (fibonacciRecurrencePolynomial (n + 5)).coeff.{0} n)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciRecurrencePolynomialThirdCoefficient") "fibonacci_recurrence_polynomial_third_coefficient") "Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient/Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration,
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
    (fun _ _ n => (fibonacciRecurrencePolynomial (n + 5)).coeff.{0} n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "fn", "arg", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.fibonacci_recurrence_polynomial_third_coefficient, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.arena) (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration).actual

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"fibonacci_recurrence_polynomial_third_coefficient\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.fibonacci_recurrence_polynomial_third_coefficient, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration).bridge

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"fibonacci_recurrence_polynomial_third_coefficient\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.fibonacci_recurrence_polynomial_third_coefficient, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration).actual (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialThirdCoefficient\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialThirdCoefficient.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
