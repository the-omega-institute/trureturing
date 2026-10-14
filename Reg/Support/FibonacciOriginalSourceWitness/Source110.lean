import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
import Reg.Support.FibonacciFactorWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open Filter
open scoped Topology

namespace Reg.Support.FibonacciOriginalSourceWitness.Source110
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℤ → CuLetter) (fun _ => CuLetter)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ ν => ν 0) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => CuLetter.c) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ)
    (v t : MemoryVertex n) (a : CuLetter)
    (left : LiveVertex side K d v)
    (p : ℤ → MemoryVertex n) (ω : ℤ → CuLetter)
    (right : BilateralGraphPath side K d p ω) (start : p 0 = t)
    (edge : MemoryEdge side K d v a t),
    ∃ q ν, BilateralGraphPath side K d q ν ∧ q 0 = v ∧ r.readout () () ν = a ∧
      ∀ i : ℤ, 0 ≤ i → ν (i+1) = ω i

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨q, ν, path, zero, bad, rest⟩ := h .lower 0 0
    (fun _ : Fin 1 => .u) (fun _ : Fin 1 => .u) .u
    (Reg.Support.FibonacciFactorWitnesses.all_u_live 1 .lower 0 0)
    (fun _ _ => .u) (fun _ => .u)
    (Reg.Support.FibonacciFactorWitnesses.all_u_path 1 .lower 0 0) rfl
    ((Reg.Support.FibonacciFactorWitnesses.all_u_path 1 .lower 0 0) 0)
  cases bad

theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), (fun _ => .u), (fun _ => .c), ?_⟩
  simp [actual, realize]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.prepend_bilateral_path) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph.prepend_bilateral_path, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

end
end Reg.Support.FibonacciOriginalSourceWitness.Source110
