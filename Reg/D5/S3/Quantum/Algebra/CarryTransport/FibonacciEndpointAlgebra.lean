import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra
open _root_.D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra
open _root_.D5.S3.Quantum.Transport.FibonacciPrefix
open _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (matrixM)
open LeanInformationAudit
open scoped Matrix Kronecker
noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra

abbrev signature : Signature where
  Params := Σ _d : ℕ, Σ _e : ℕ, ℕ
  State p := Labels p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Labels p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => sourceCarry p.1 p.2.1 p.2.2 a) (fun x => nomatch x)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0,0)) (fun x => nomatch x)

/-- The full original telescope and every conclusion are retained. Only the carry
in the native affine action is exposed as the intervenable observation. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d e : ℕ) [NeZero d] [NeZero e] (hd : 2 ≤ d) (he : 2 ≤ e),
    (∀ m a, ![(integerEvolution d m a).1, (integerEvolution d m a).2] =
      (matrixM ^ m).mulVec ![(a.1.val : ℤ), (a.2.val : ℤ)]) ∧
    (∀ m a, (d : ℤ) ∣ (integerEvolution d m a).1 - (lowTrajectory d m a).1.val ∧
      (d : ℤ) ∣ (integerEvolution d m a).2 - (lowTrajectory d m a).2.val) ∧
    (∀ m a h, fibreTrajectory d e a m h =
      lowTrajectory e m h + R.readout () ⟨d,⟨e,m⟩⟩ a) ∧
    (∀ m a b, fibreTrajectory d e a m = fibreTrajectory d e b m ↔
      sourceCarry d e m a = sourceCarry d e m b) ∧
    (∀ m B, endpointPullback d e m B =
      (jointUnitary d e ^ m)ᴴ * lowTensor d e B * jointUnitary d e ^ m) ∧
    (∀ m B, endpointAlpha d m B = (lowUnitary d ^ m)ᴴ * B * lowUnitary d ^ m) ∧
    (∀ m B, (endpointAlpha d m).symm B =
      lowUnitary d ^ m * B * (lowUnitary d ^ m)ᴴ) ∧
    (∀ m B, B ∈ endpointAlgebra d e m ↔
      ∀ a b, sourceCarry d e m a ≠ sourceCarry d e m b → endpointAlpha d m B a b = 0) ∧
    (∀ m, endpointAlgebra d e m =
      (carryBlockEmbedding d e m).range.map (endpointAlpha d m).symm.toAlgHom) ∧
    (∀ m, sourceMatrix (d * e) ^ m = 1 →
      jointUnitary d e ^ m = 1 ∧ endpointAlgebra d e m = ⊤) ∧
    (∃ m : ℕ, 1 ≤ m ∧ sourceMatrix (d * e) ^ m = 1) ∧
    ¬ (∀ m n : ℕ, 1 ≤ m → m ≤ n → endpointAlgebra d e n ≤ endpointAlgebra d e m)

theorem actual_law : arena.Law actual := by
  intro d e _ _ hd he
  exact _root_.D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra.result d e hd he

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 2 2 (by omega) (by omega)).2.2.1
    1 ((1,1) : Labels 2) ((0,0) : Labels 2)
  have hbad : fibreTrajectory 2 2 (1,1) 1 (0,0) ≠
      lowTrajectory 2 1 (0,0) + rejected.readout () ⟨2,⟨2,1⟩⟩ (1,1) := by decide
  exact hbad hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2,⟨2,1⟩⟩, ((0,0) : Labels 2), ((1,1) : Labels 2), ?_⟩
  change sourceCarry 2 2 1 (0,0) ≠ sourceCarry 2 2 1 (1,1)
  decide

def registration : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra.result)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ p a => sourceCarry p.1 p.2.1 p.2.2 a) (fun x => nomatch x)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra.result.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ p a => sourceCarry p.1 p.2.1 p.2.2 a) (fun x => nomatch x)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra,
    definition := none,
    coordinates := #[0,1,6],
    readouts := #[{
      path := #["body","body","body","body","body","body",
        "arg","arg","fn","arg","body","body","body","arg","arg"],
      stateBinder := 7,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end Reg.D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra
