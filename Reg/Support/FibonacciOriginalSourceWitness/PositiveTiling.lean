import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
import Reg.Support.SingleDependentReadout
import Reg.Support.FibonacciFactorWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetCodebook ResetFactors MemoryGraph
open Filter Topology

namespace Reg.Support.FibonacciOriginalSourceWitness.PositiveTiling
noncomputable section
abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℤ → CuLetter)
    (fun _ => ℤ → CuLetter)
def actual : Realization observationSignature := realize observationSignature
  (fun _ _ ω => ω) (fun e => nomatch e)
def rejected : Realization observationSignature := realize observationSignature
  (fun _ _ _ _ => CuLetter.c) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (W : ℤ → List CuLetter) (positive : ∀ j, 0 < (W j).length),
    blockCut W 0 = 0 ∧
    (∀ j, blockCut W (j + 1) = blockCut W j + (W j).length) ∧
    StrictMono (blockCut W) ∧
    ∃ ω : ℤ → CuLetter, ∀ j (k : Fin (W j).length),
      r.readout () () ω (blockCut W j + (k : ℕ)) = (W j)[k]
theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨ω, all⟩ := (h (fun _ => [CuLetter.u]) (by intro j; simp)).2.2.2
  have bad := all 0 ⟨0, by simp⟩
  cases bad
def evidence : Registration sourceArena (type_of% @positive_block_tiling) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_block_tiling, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ => .u), (fun _ => .c), ?_⟩
    intro same
    have bad := congrFun same 0
    cases bad
end
end Reg.Support.FibonacciOriginalSourceWitness.PositiveTiling
