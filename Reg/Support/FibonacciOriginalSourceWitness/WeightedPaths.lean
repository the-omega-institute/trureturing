import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
import Reg.Support.SingleDependentReadout
import Reg.Support.FibonacciFactorWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetCodebook ResetFactors MemoryGraph
open Filter Topology

namespace Reg.Support.FibonacciOriginalSourceWitness.WeightedPaths
noncomputable section
abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature
    (Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, Σ d : ℝ, Σ _ : ℝ,
      Σ _ : ℕ, CoreVertex side n K d)
    (fun p => Fin p.2.2.2.2.2.1 → CuLetter × CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2.1)
    (fun _ => ℝ)
def actual : Realization observationSignature := realize observationSignature
  (fun _ p choices => coreMonomial p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
    p.2.2.2.2.2.1 p.2.2.2.2.2.2 choices) (fun e => nomatch e)
def rejected : Realization observationSignature := realize observationSignature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d z : ℝ),
    (∀ (k : ℕ) (v : CoreVertex side n K d)
      (choices : Fin k → CuLetter × CoreVertex side n K d),
      CorePath side K d k v choices → RetainedWalk side K d v.val
        (List.ofFn (fun i => (choices i).1))) ∧
    (∀ (k : ℕ) (v : CoreVertex side n K d),
      (∑ t : CoreVertex side n K d, (weightedAdjacency side n K d z ^ k) v t) =
      ∑ choices : Fin k → CuLetter × CoreVertex side n K d,
        r.readout () ⟨side,n,K,d,z,k,v⟩ choices)
def allU : CoreVertex .lower 1 1 0 :=
  ⟨(fun _ => CuLetter.u), Reg.Support.FibonacciFactorWitnesses.all_u_live 1 .lower 1 0⟩
theorem rejected_law : ¬ sourceArena.Law rejected := by
  classical
  intro h
  have bad := (h .lower 1 1 0 2).2 0 allU
  simpa [rejected, realize, Matrix.one_apply] using bad
def evidence : Registration sourceArena (type_of% @original_weighted_adjacency_paths) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_weighted_adjacency_paths, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    classical
    intro i
    refine ⟨⟨MemorySide.lower,1,1,(0 : ℝ),(2 : ℝ),1,allU⟩,
      (fun _ => (CuLetter.u,allU)), (fun _ => (CuLetter.c,allU)), ?_⟩
    have good : CorePath .lower 1 0 1 allU (fun _ => (CuLetter.u,allU)) := by
      exact ⟨(Reg.Support.FibonacciFactorWitnesses.all_u_path 1 .lower 1 0 0), trivial⟩
    have bad : ¬ CorePath .lower 1 0 1 allU (fun _ => (CuLetter.c,allU)) := by
      intro h
      have eq := congrFun h.1.1 0
      cases eq
    change coreMonomial .lower 1 0 2 1 allU (fun _ => (CuLetter.u,allU)) ≠
      coreMonomial .lower 1 0 2 1 allU (fun _ => (CuLetter.c,allU))
    norm_num [coreMonomial, good, bad, List.ofFn_succ, wordWeight, letterWeight]
end
end Reg.Support.FibonacciOriginalSourceWitness.WeightedPaths
