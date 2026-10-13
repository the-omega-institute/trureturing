import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
import Reg.Support.FibonacciFactorWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
open Filter
open scoped Topology

namespace Reg.Support.FibonacciOriginalSourceWitness.Source135
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℤ → CuLetter) (fun _ => ℤ → CuLetter)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ ω => ω) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ _ => CuLetter.c) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (hK : 1 ≤ K)
    (W : ℤ → List CuLetter) (positive : ∀ j, 0 < (W j).length)
    (windows : ∀ a n, uPadding (blockWindow W a n) ∈ AuxiliaryLanguage K d),
    ∃ ω ∈ AuxiliaryLanguage K d, ∀ j (k : Fin (W j).length),
      r.readout () () ω (blockCut W j+(k : ℕ))=(W j)[k]

theorem windows_all_u (a : ℤ) (n : ℕ) :
    uPadding (blockWindow (fun _ => [CuLetter.u]) a n) ∈ AuxiliaryLanguage 1 0 := by
  have same : uPadding (blockWindow (fun _ => [CuLetter.u]) a n) = fun _ => CuLetter.u := by
    have window : blockWindow (fun _ => [CuLetter.u]) a n = List.replicate n CuLetter.u := by
      induction n generalizing a with
      | zero => rfl
      | succ n ih => simp [blockWindow, ih, List.replicate_succ]
    rw [window]
    funext i
    simp [uPadding, List.getElem?_replicate]
    split <;> simp_all
  rw [same]
  exact Reg.Support.FibonacciFactorWitnesses.all_u_auxiliary

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨ω, member, all⟩ := h 1 0 le_rfl (fun _ => [CuLetter.u]) (by intro j; simp) windows_all_u
  have bad := all 0 ⟨0, by simp⟩
  cases bad

theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), (fun _ => .u), (fun _ => .c), ?_⟩
  intro same
  have bad := congrFun same 0
  cases bad

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.compact_block_tiling) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.compact_block_tiling, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

end
end Reg.Support.FibonacciOriginalSourceWitness.Source135
