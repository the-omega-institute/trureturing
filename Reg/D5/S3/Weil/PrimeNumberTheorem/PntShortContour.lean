import D5.S3.Weil.PrimeNumberTheorem.PntShortContour
import Reg.Support.DependentFamily
import Reg.Support.PntAuditFacts

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour

open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open scoped ContDiff Chebyshev
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PntAuditFacts
open LeanInformationAudit

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ
local notation "𝓜" => mellin

noncomputable section

theorem small_holomorphic_strip : ∃ σ₂ : ℝ,
    σ₂ ∈ Ioo 0 1 ∧ LogDerivZetaIsHoloSmall σ₂ := by
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  refine ⟨σ₂, ⟨σ₂_pos, σ₂_lt_one⟩, ?_⟩
  apply holo2'.mono
  intro s hs
  simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff,
    mem_reProdIm, mem_Icc, mem_singleton_iff] at hs ⊢
  refine ⟨?_, hs.2⟩
  refine ⟨?_, hs.1.2⟩
  rcases hs.1.1 with ⟨left, right⟩
  constructor
  · apply le_trans _ left
    apply min_le_min_right
    apply le_max_left
  · rw [max_eq_right (by linarith)] at right ⊢
    exact right

namespace I4Bound

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p C => C * p.2.1 * p.2.1 ^ (-p.1 / (Real.log p.2.2.2 ^ 9)) / p.2.2.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)),
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ r.readout () ⟨A, X, ε, T⟩ C

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨σ₂, hσ₂, hholo⟩ := small_holomorphic_strip
  obtain ⟨C, _hC, Tlb, _hTlb, hh⟩ := h (SmoothingF := fun _ => 0) (by simp) contDiff_const
    hholo hσ₂ (A := 1 / 2) (by constructor <;> norm_num)
  have hb := hh 4 (by norm_num) (ε := 1 / 2) (by norm_num) (by norm_num)
    (T := Tlb + 1) (by linarith)
  change ‖I₄ (fun _ => 0) (1 / 2) 4 (1 - (1 / 2) / Real.log (Tlb + 1) ^ 9) σ₂‖ ≤ (-1 : ℝ) at hb
  exact (not_le_of_gt (by linarith [norm_nonneg (I₄ (fun _ => 0) (1 / 2) 4 (1 - (1 / 2) / Real.log (Tlb + 1) ^ 9) σ₂)])) hb

def registration : Registration arena
    (∀ {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)),
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.I4Bound, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (4 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ) * 1 * 1 ^ (-(0 : ℝ) / (Real.log 4 ^ 9)) / 1 ≠
      1 * 1 * 1 ^ (-(0 : ℝ) / (Real.log 4 ^ 9)) / 1
    norm_num

register_information_theorem _root_.I4Bound in arena
  readout via (realize signature (fun _ p C => C * p.2.1 * p.2.1 ^ (-p.1 / (Real.log p.2.2.2 ^ 9)) / p.2.2.1) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.PntShortContour
    coordinates := #[6, 12, 14, 17]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      stateOperand := some #["fn", "arg", "fn", "arg", "fn", "arg"] }] })
  escape continues (open)

end I4Bound

end
end Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour
