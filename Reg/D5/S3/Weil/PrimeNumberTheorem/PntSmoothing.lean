import D5.S3.Weil.PrimeNumberTheorem.PntSmoothing
import Reg.Support.DependentFamily
import Reg.Support.PntAuditFacts

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing

open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open scoped ContDiff Chebyshev
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PntAuditFacts
open LeanInformationAudit

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ
local notation "𝓜" => mellin

noncomputable section

namespace SmoothedChebyshevClose

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p C => C * p.2 * p.1 * Real.log p.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1),
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ r.readout () ⟨X, ε⟩ C

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ν, hd, hn, hs, hm⟩ := normalized_smooth_kernel
  obtain ⟨C, _hC, hh⟩ := h hd hs hn hm
  have hb := hh 4 (by norm_num) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
  change ‖SmoothedChebyshev ν (3 / 4) 4 - ψ 4‖ ≤ (-1 : ℝ) at hb
  exact (not_le_of_gt (by linarith [norm_nonneg (SmoothedChebyshev ν (3 / 4) 4 - ψ 4)])) hb

def registration : Registration arena
    (∀ {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1),
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.SmoothedChebyshevClose, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨Real.exp 1, (1 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ) * 1 * Real.exp 1 * Real.log (Real.exp 1) ≠
      1 * 1 * Real.exp 1 * Real.log (Real.exp 1)
    simp only [Real.log_exp, zero_mul, one_mul, mul_one]
    exact ne_of_lt (Real.exp_pos 1)

register_information_theorem _root_.SmoothedChebyshevClose in arena
  readout via (realize signature (fun _ p C => C * p.2 * p.1 * Real.log p.1) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.PntSmoothing
    coordinates := #[6, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      stateOperand := some #["fn", "arg", "fn", "arg", "fn", "arg"] }] })
  escape continues (open)

end SmoothedChebyshevClose

end
end Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing
