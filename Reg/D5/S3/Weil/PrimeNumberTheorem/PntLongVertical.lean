import D5.S3.Weil.PrimeNumberTheorem.PntLongVertical
import Reg.Support.DependentFamily
import Reg.Support.PntAuditFacts

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.PntLongVertical

open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open scoped ContDiff Chebyshev
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PntAuditFacts
open LeanInformationAudit

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ
local notation "𝓜" => mellin

noncomputable section

namespace I3Bound

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
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)),
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),
        let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ r.readout () ⟨A, X, ε, T⟩ C

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA, Cζ, hCζ, hbound⟩ := LogDerivZetaBndUnif
  obtain ⟨C, _hC, hh⟩ := h (SmoothingF := fun _ => 0) (by simp) contDiff_const
    (show LogDerivZetaHasBound A Cζ from hbound) hCζ hA
  have hb := hh 4 (by norm_num) (ε := 1 / 2) (by norm_num) (by norm_num) (T := 4) (by norm_num)
  change ‖I₃ (fun _ => 0) (1 / 2) 4 4 (1 - A / Real.log 4 ^ 9)‖ ≤ (-1 : ℝ) at hb
  exact (not_le_of_gt (by linarith [norm_nonneg (I₃ (fun _ => 0) (1 / 2) 4 4 (1 - A / Real.log 4 ^ 9))])) hb

def registration : Registration arena
    (∀ {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)),
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),
        let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.I3Bound, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (4 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ) * 1 * 1 ^ (-(0 : ℝ) / (Real.log 4 ^ 9)) / 1 ≠
      1 * 1 * 1 ^ (-(0 : ℝ) / (Real.log 4 ^ 9)) / 1
    norm_num

register_information_theorem _root_.I3Bound in arena
  readout via (realize signature (fun _ p C => C * p.2.1 * p.2.1 ^ (-p.1 / (Real.log p.2.2.2 ^ 9)) / p.2.2.1) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.PntLongVertical
    coordinates := #[3, 10, 12, 15]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      stateOperand := some #["fn", "arg", "fn", "arg", "fn", "arg"] }] })
  escape continues (open)

end I3Bound

end
end Reg.D5.S3.Weil.PrimeNumberTheorem.PntLongVertical
