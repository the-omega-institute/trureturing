import D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare
open _root_.D5.S3.TotalVariation.Bhattacharyya
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare

def signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (B : ℕ) (z : ℝ), |z| ≤ 1 →
    (∀ k ∈ Finset.range (B + 1), 0 ≤ p_z B (R.readout () B z) k) ∧
    (∑ k ∈ Finset.range (B + 1), p_z B z k) = 1 ∧
    (∀ k ≤ B, p_z B z k / p_0 B k =
      ((1 + z) ^ k * (1 - z) ^ (B - k) +
        (1 - z) ^ k * (1 + z) ^ (B - k)) / 2) ∧
    chiSquare B z = ((1 + z ^ 2) ^ B + (1 - z ^ 2) ^ B) / 2 - 1 ∧
      chiSquare B z =
        ∑ j ∈ Finset.Icc 1 (B / 2), (B.choose (2 * j) : ℝ) * z ^ (4 * j) ∧
    chiSquare B z ≤ Real.cosh (B * z ^ 2) - 1 ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → (B : ℝ) * δ ≤ 1 →
      z ^ 2 = 2 * δ - δ ^ 2 → chiSquare B z ≤ 3 * ((B : ℝ) * δ) ^ 2) ∧
    (|z| < 1 →
      (∀ k ∈ Finset.range (B + 1), 0 < p_z B z k) ∧
      0 < bhattacharyya
        (fun k : Fin (B + 1) => p_0 B k)
        (fun k : Fin (B + 1) => p_z B z k)) ∧
    1 - bhattacharyya
      (fun k : Fin (B + 1) => p_0 B k)
      (fun k : Fin (B + 1) => p_z B z k) ^ 2 ≤ chiSquare B z

theorem actual_law : arena.Law actual := by
  intro B z hz
  simpa [actual, realize, signature] using symmetric_binomial_chi_square B z hz

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcase := h 2 0 (by norm_num)
  have hnegative := hcase.1 1 (by norm_num)
  norm_num [rejected, realize, signature, p_z] at hnegative

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), ?_⟩
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem symmetric_binomial_chi_square in arena
  readout via (realize signature (fun _ _ z => z) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare
