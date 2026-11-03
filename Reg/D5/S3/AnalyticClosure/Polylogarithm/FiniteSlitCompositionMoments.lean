import LeanInformationAuditInterface.Contract.Registration
import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCompositionMoments
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter MeasureTheory Set Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCompositionMoments
open _root_.D5.S3.AnalyticClosure.Polylogarithm
open _root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCompositionMoments

abbrev signature : Signature where
  Params := ℕ+ × List ℕ+ × ℕ+
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z ↦ reciprocal p.1 p.2.1 p.2.2 z) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (head : ℕ+) (tail : List ℕ+) (ell : ℕ+),
    ∃ R0 ρ R : ℝ, ∃ upper : ℂ → ℂ,
      1 < R0 ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < R ∧ R < R0 ∧ R < 1 + ρ ∧
      AnalyticOnNhd ℂ (reciprocal head tail ell)
        {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0} ∧
      (∀ z : ℂ, ‖z‖ < 1 → r.readout () ⟨head, tail, ell⟩ z =
        ((CompositionDisk.normalized head tail z)⁻¹) ^ (ell : ℕ)) ∧
      r.readout () ⟨head, tail, ell⟩ 0 =
        ((CompositionDisk.normalized head tail 0)⁻¹) ^ (ell : ℕ) ∧
      ContinuousOn upper {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im} ∧
      (∀ z : ℂ, ‖z - 1‖ ≤ ρ → 0 ≤ z.im → z ∈ CompositionContinuation.omega →
        upper z = r.readout () ⟨head, tail, ell⟩ z) ∧
      upper 1 = (if 1 < (head : ℕ) then
        ((CompositionBoundary.zeta head tail : ℂ)⁻¹) ^ (ell : ℕ) else 0) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ CompositionContinuation.omega,
        ‖z‖ = R → ‖r.readout () ⟨head, tail, ell⟩ z‖ ≤ B) ∧
      ∀ B : ℝ, ∀ᶠ n : ℕ in atTop,
        B / R ^ n + (1 / Real.pi) *
          (∫ x in (1 : ℝ)..R, (upper (x : ℂ)).im / x ^ (n + 1)) < 0

 theorem source_equivalence : (type_of% @result) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨R0, ρ, R, upper, _hR0, _hρ, _hρ1, _hR, _hRR0, _hRρ,
      _ha, _hdisk, hzero, _rest⟩ := h 1 [] 1
  simp only [rejected, realize] at hzero
  rw [(_root_.D5.S3.AnalyticClosure.Polylogarithm.CompositionDisk.source_series 1 []).2.1] at hzero
  norm_num [_root_.D5.S3.AnalyticClosure.Polylogarithm.CompositionDisk.leading] at hzero

def variation : Variation arena actual := ⟨result, rejected, rejected_law⟩

def sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

end Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCompositionMoments
