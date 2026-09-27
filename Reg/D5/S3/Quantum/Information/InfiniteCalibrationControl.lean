import D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl
open _root_.D5.S3.Quantum.Information.InfiniteCalibrationControl
open _root_.D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨k, hk⟩ := h (1/2) (1/100) (1/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hk.1

def registration : Registration arena (∀ (a δ b : ℝ) (_ha : 0 < a) (_ha1 : a < 1)
    (_hδ : 0 < δ) (_hδL : δ < (1-a)/4) (_hδa : δ < (1-a^2)/16)
    (_hb : 0 < b) (_hbδ : b < 1 - a/(1-δ)), ∃ k : ℝ, InfiniteScalarControl a δ b k) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨(0 : ℝ), (0 : ℝ), (0 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ) ≠ 1
    exact zero_ne_one

register_information_theorem result in arena
  readout via (realize signature (fun _ _ k => k) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Information.InfiniteCalibrationControl
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg"]
      stateBinder := 10 }] })
  escape continues (open)

end Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl
