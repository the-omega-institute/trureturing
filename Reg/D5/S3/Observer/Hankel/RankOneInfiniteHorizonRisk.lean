import D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk

open _root_.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped ENNReal Topology

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ T η => minimaxRisk T η) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ℕ) (_hT : 1 ≤ T) (η : ℝ) (_hη : 0 < η),
    R.readout () T η = ENNReal.ofReal (1 / 2 : ℝ) ∧
    (∀ a ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) ∧
      ∀ N, (hankel a N).PosSemidef ∧ (hankel a N).rank = 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 1 le_rfl 1 zero_lt_one).1
  have hp : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2 : ℝ) :=
    ENNReal.ofReal_pos.mpr (by norm_num)
  exact (ne_of_gt hp) he.symm

/-- Exact observation of the first response determines the parameter. -/
theorem noiseless_risk : minimaxRisk 1 0 = 0 := by
  apply bot_unique
  refine (iInf_le (fun Ψ => risk 1 0 Ψ)
    (fun y n => y (1 : Fin 2) ^ n.val)).trans ?_
  refine iSup_le fun a => iSup_le fun y => iSup_le fun hy => iSup_le fun n => ?_
  have he : y (1 : Fin 2) = a.val := by
    have hh := hy (1 : Fin 2)
    have hz : |y (1 : Fin 2) - a.val| = 0 := by
      apply le_antisymm
      · simpa using hh
      · exact abs_nonneg _
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  simp [he]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rank_one_infinite_horizon_risk, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), ?_⟩
    change minimaxRisk 1 0 ≠ minimaxRisk 1 1
    rw [noiseless_risk, (rank_one_infinite_horizon_risk 1 le_rfl 1 zero_lt_one).1]
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))).symm

register_information_theorem rank_one_infinite_horizon_risk in arena
  readout via (realize signature (fun _ T η => minimaxRisk T η) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk
