import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open LeanInformationAudit
open scoped Matrix ComplexStarModule BigOperators Kronecker ComplexOrder MatrixOrder
noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra

abbrev signature : Signature where
  Params := ℕ
  State d := Labels d
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d a => carry d a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (d e : ℕ) (hd : 2 ≤ d) (he : 2 ≤ e),
    letI : NeZero d := ⟨by omega⟩
    letI : NeZero e := ⟨by omega⟩
    (∀ a h, transport d e (a,h) =
      (fibonacci d a, (h.2, h.1 + h.2 + (R.readout () d a : ZMod e)))) ∧
    (∀ B : Matrix (Labels d) (Labels d) ℂ,
      B ∈ outputAlgebra d e ↔
        ∀ a b, carry d a ≠ carry d b → alpha d B a b = 0) ∧
    (∀ B ∈ outputAlgebra d e,
      (jointUnitary d e)ᴴ * lowTensor d e B * jointUnitary d e =
        lowTensor d e (alpha d B)) ∧
    (∀ B : Matrix (Labels d) (Labels d) ℂ,
      B ∈ outputAlgebra d e ↔ ∃ F : DensityState (Labels d) → ℂ,
        ∀ rho : DensityState (Labels d × Labels e),
          outputExpectation d e B rho = F (marginalRight rho)) ∧
    (∀ B : Matrix (Labels d) (Labels d) ℂ,
      alpha d B = (lowUnitary d)ᴴ * B * lowUnitary d) ∧
    outputAlgebra d e = conjugatedBlocks d ∧
    Module.finrank ℂ (sector d 0) = d*(d+1)/2 ∧
    Module.finrank ℂ (sector d 1) = d*(d-1)/2 ∧
    Module.finrank ℂ (outputAlgebra d e) = d^2*(d^2+1)/2 ∧
    Module.finrank ℝ (selfAdjointOutput d e) = d^2*(d^2+1)/2

theorem actual_law : arena.Law actual := by
  intro d e hd he
  exact result d e hd he

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
  have hh := (h 2 2 (by norm_num) (by norm_num)).1
    ((1,1) : Labels 2) ((0,0) : Labels 2)
  have hs := (result 2 2 (by norm_num) (by norm_num)).1
    ((1,1) : Labels 2) ((0,0) : Labels 2)
  rw [hs] at hh
  have hk : carry 2 (1,1) = 1 := by decide
  have hz : (1 : ZMod 2) = 0 := by
    simpa [rejected, realize, hk] using congrArg (fun p => p.2.2) hh
  exact one_ne_zero hz

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(2 : ℕ),((0,0) : Labels 2),((1,1) : Labels 2),?_⟩
    intro h
    change carry 2 (0,0) = carry 2 (1,1) at h
    have hzero : carry 2 (0,0) = 0 := by decide
    have hone : carry 2 (1,1) = 1 := by decide
    rw [hzero,hone] at h
    exact Nat.zero_ne_one h

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ d a => carry d a) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Algebra") "CarryTransport") "FibonacciOutputAlgebra") "result") "Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra/Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ d a => carry d a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "arg", "arg", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.observationFact0, `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.anchorEnumeration }


#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms actual_law
#print axioms rejected_law
#print axioms registration
end Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra


noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.arena
noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.arena
noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.arena) (Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration).actual

noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.observation0 : (d e : Nat) →
  (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d) →
    (he : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      (a : D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.Labels d) →
        (h : D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.Labels e) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.signature PUnit.unit.{1} d :=
  fun (d e : Nat) (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d)
    (he : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e)
    (a : D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.Labels d)
    (h : D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.Labels e) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.signature
    Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.actual PUnit.unit.{1} d a

noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.result, part := .type, path := [.body, .body, .body, .body, .function, .argument, .body, .body, .argument, .argument, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration).actual (Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration).variation.2.choose (Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration).variation.1 (Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Algebra\",\"CarryTransport\",\"FibonacciOutputAlgebra\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra, declaration := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
