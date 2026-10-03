import D5.S3.TotalVariation.IndependentConvolutionL1Minimum
import Reg.Support.DependentFamily

open _root_.D5.S3.TotalVariation.IndependentConvolutionL1Minimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum

abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin n → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

/-- Preserve every source hypothesis and vary the first factor only at the objective readout. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 3 ≤ n),
    IsLeast {v : ℝ | ∃ p q : Fin n → ℝ,
      p ∈ stdSimplex ℝ (Fin n) ∧ q ∈ stdSimplex ℝ (Fin n) ∧
      fullL1 n (r.readout () n p) q = v} (1 / (2 * n - 1 : ℕ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, q, hp, hq, hv⟩ := (h 3 (by norm_num)).1
  norm_num [rejected, realize, fullL1, ordinaryConvolution,
    Finset.sum_range_succ] at hv

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, (Pi.single (0 : Fin 3) 1 : Fin 3 → ℝ),
    (Pi.single (1 : Fin 3) 1 : Fin 3 → ℝ), ?_⟩
  intro h
  have he := congrFun h (0 : Fin 3)
  norm_num [actual, realize, Pi.single_apply] at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

register_information_theorem
  _root_.D5.S3.TotalVariation.IndependentConvolutionL1Minimum.result in arena
  readout via (realize signature (fun _ _ p => p) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.TotalVariation.IndependentConvolutionL1Minimum
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "arg", "body",
        "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.TotalVariation.IndependentConvolutionL1Minimum
