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
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms actual_law
#print axioms rejected_law
#print axioms registration
end Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra
