import D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := List Window
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ × ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => parityTask w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

/-- Vary the complete word response while preserving the linear minimum contract. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R :=
    (∀ w : List Window, wordBehavior fourDimensional w = R.readout () () w) ∧
    Module.finrank ℚ BlockState = 4 ∧
    (∀ (V : Type u) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (R : WordRepresentation ℚ Window V (ℚ × ℚ)),
      (∀ w : List Window, wordBehavior R w = parityTask w) → 4 ≤ Module.finrank ℚ V) ∧
    parityTask [.middle] = (1, 1) ∧ integerRationalTask [.middle] = (1, 3) ∧
    responseMinor = !![1, 1, 0, 0; 1, 0, 0, 0; 1, 1, 1, 1; 1, 0, 1, 0] ∧
    responseMinor.det = 1

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h.1 []
  have hne : wordBehavior fourDimensional [] ≠ (0, 0) := by decide +kernel
  exact hne hz

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result.{u}, rejected, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law.{u}⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), ([] : List Window), ([.middle] : List Window), ?_⟩
    change parityTask [] ≠ parityTask [.middle]
    decide +kernel

register_information_theorem result in arena
  readout via (realize signature (fun _ _ w => parityTask w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
    coordinates := #[]
    readouts := #[{ path := #["fn", "arg", "body", "arg"], stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.FibonacciAtomic.ParityLiftRationalMinimum
