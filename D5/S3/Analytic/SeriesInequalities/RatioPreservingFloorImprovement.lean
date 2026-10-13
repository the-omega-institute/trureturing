/- GID: D5/S3/Analytic/SeriesInequalities/RatioPreservingFloorImprovement
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/RatioPreservingFloorImprovement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summable floors admit unbounded amplification with the same adjacent ratio. -/

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Filter Finset
open scoped BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement

/-- Flatten a floor above the height of its `N`th entry. -/
def cappedFloor (η : ℕ → ℝ) (N k : ℕ) : ℝ := min (η k) (η N)

private lemma cappedFloor_summable {η : ℕ → ℝ}
    (hpos : ∀ k, 0 < η k) (hs : Summable η) (N : ℕ) :
    Summable (cappedFloor η N) :=
  Summable.of_nonneg_of_le (fun k => le_min (hpos k).le (hpos N).le)
    (fun _ => min_le_left _ _) hs

private lemma cappedFloor_mass_tendsto_zero {η : ℕ → ℝ}
    (hpos : ∀ k, 0 < η k) (hs : Summable η) :
    Tendsto (fun N => ∑' k, cappedFloor η N k) atTop (𝓝 0) := by
  have hterm (k : ℕ) :
      Tendsto (fun N => cappedFloor η N k) atTop (𝓝 0) := by
    simpa only [cappedFloor, min_eq_right (hpos k).le] using
      (tendsto_const_nhds.min hs.tendsto_atTop_zero :
        Tendsto (fun N => min (η k) (η N)) atTop (𝓝 (min (η k) 0)))
  have hbound : ∀ᶠ N in atTop, ∀ k, ‖cappedFloor η N k‖ ≤ η k :=
    Eventually.of_forall fun N k => by
      rw [cappedFloor, Real.norm_eq_abs, abs_of_nonneg (le_min (hpos k).le (hpos N).le)]
      exact min_le_left _ _
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hs hterm hbound

private lemma cappedFloor_adjacent {η : ℕ → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hpos : ∀ k, 0 < η k)
    (hratio : ∀ k, η k ≤ R * η (k + 1)) (N k : ℕ) :
    cappedFloor η N k ≤ R * cappedFloor η N (k + 1) := by
  unfold cappedFloor
  by_cases h : η (k + 1) ≤ η N
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (hratio k)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans (by nlinarith [hpos N])

/-- A single new floor has arbitrarily small total mass, keeps the original
adjacent-ratio bound, dominates a positive fixed multiple of the old floor
at every index, and dominates every fixed multiple on a sufficiently late tail.
The same floor works for all the tail multiples. -/
theorem exists_ratio_preserving_improvement {η : ℕ → ℝ} {R ε : ℝ}
    (hR : 1 ≤ R) (hpos : ∀ k, 0 < η k) (hanti : Antitone η)
    (hs : Summable η) (hratio : ∀ k, η k ≤ R * η (k + 1)) (hε : 0 < ε) :
    ∃ θ : ℕ → ℝ,
      (∀ k, 0 < θ k) ∧ Antitone θ ∧ Summable θ ∧
      (∑' k, θ k) ≤ ε ∧ (∀ k, θ k ≤ ε) ∧
      (∀ k, θ k ≤ R * θ (k + 1)) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ * η k ≤ θ k) ∧
      (∀ B : ℝ, 0 < B → ∃ L : ℕ, ∀ k, L ≤ k → B * η k ≤ θ k) := by
  classical
  let budget : ℕ → ℝ := fun j => (ε / 2) * (1 / 2 : ℝ) ^ j
  have hbudget : Summable budget :=
    (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left _
  have hbudget_sum : (∑' j, budget j) = ε := by
    change (∑' j, (ε / 2) * (1 / 2 : ℝ) ^ j) = ε
    rw [tsum_mul_left]
    rw [tsum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)]
    ring
  have hsmall : ∀ j, ∃ N, (∑' k, cappedFloor η N k) ≤ budget j := by
    intro j
    have hb : 0 < budget j := by dsimp [budget]; positivity
    obtain ⟨N, hN⟩ := ((tendsto_order.1
      (cappedFloor_mass_tendsto_zero hpos hs)).2 _ hb).exists
    exact ⟨N, hN.le⟩
  choose N hN using hsmall
  let f : ℕ → ℕ → ℝ := fun j k => cappedFloor η (N j) k
  have hfpos : ∀ j k, 0 < f j k := fun j k => lt_min (hpos k) (hpos (N j))
  have hfrow : ∀ j, Summable (f j) := fun j => cappedFloor_summable hpos hs _
  have hrows : Summable (fun j => ∑' k, f j k) :=
    Summable.of_nonneg_of_le (fun j => tsum_nonneg (fun k => (hfpos j k).le))
      hN hbudget
  have hprod : Summable (fun p : ℕ × ℕ => f p.1 p.2) :=
    (summable_prod_of_nonneg (fun p => (hfpos p.1 p.2).le)).2 ⟨hfrow, hrows⟩
  have hswap : Summable (fun p : ℕ × ℕ => f p.2 p.1) :=
    hprod.comp_injective (Equiv.prodComm ℕ ℕ).injective
  have hcols : (∀ k, Summable (fun j => f j k)) ∧
      Summable (fun k => ∑' j, f j k) :=
    (summable_prod_of_nonneg (fun p => (hfpos p.2 p.1).le)).1 hswap
  let θ : ℕ → ℝ := fun k => ∑' j, f j k
  have hθsum : Summable θ := hcols.2
  have hmass : (∑' k, θ k) ≤ ε := by
    calc
      (∑' k, θ k) = ∑' j, ∑' k, f j k := hprod.tsum_comm
      _ ≤ ∑' j, budget j := hrows.tsum_le_tsum hN hbudget
      _ = ε := hbudget_sum
  have hθpos : ∀ k, 0 < θ k := fun k =>
    (hfpos 0 k).trans_le ((hcols.1 k).le_tsum 0 (fun j _ => (hfpos j k).le))
  refine ⟨θ, hθpos, ?_, hθsum, hmass, ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    exact (hcols.1 l).tsum_le_tsum
      (fun j => min_le_min_right _ (hanti hkl)) (hcols.1 k)
  · intro k
    exact (hθsum.le_tsum k (fun i _ => (hθpos i).le)).trans hmass
  · intro k
    calc
      θ k ≤ ∑' j, R * f j (k + 1) :=
        (hcols.1 k).tsum_le_tsum (fun j => cappedFloor_adjacent hR hpos hratio _ _)
          ((hcols.1 (k + 1)).mul_left R)
      _ = R * θ (k + 1) := (hcols.1 (k + 1)).tsum_mul_left R
  · let c₀ : ℝ := η (N 0) / η 0
    have hc₀pos : 0 < c₀ := div_pos (hpos _) (hpos _)
    have hc₀le : c₀ ≤ 1 := (div_le_one (hpos 0)).2 (hanti (Nat.zero_le _))
    refine ⟨c₀, hc₀pos, fun k => ?_⟩
    have hcap : c₀ * η k ≤ f 0 k := by
      change c₀ * η k ≤ min (η k) (η (N 0))
      refine le_min ?_ ?_
      · nlinarith [hpos k]
      · calc
          c₀ * η k ≤ c₀ * η 0 := mul_le_mul_of_nonneg_left
            (hanti (Nat.zero_le k)) hc₀pos.le
          _ = η (N 0) := div_mul_cancel₀ _ (ne_of_gt (hpos 0))
    exact hcap.trans ((hcols.1 k).le_tsum 0 (fun j _ => (hfpos j k).le))
  · intro B hB
    obtain ⟨J, hJ⟩ := exists_nat_gt B
    let L : ℕ := (range J).sup N
    refine ⟨L, fun k hk => ?_⟩
    have heq : ∀ j ∈ range J, f j k = η k := by
      intro j hj
      exact min_eq_left (hanti ((le_sup hj).trans hk))
    calc
      B * η k ≤ (J : ℝ) * η k := mul_le_mul_of_nonneg_right hJ.le (hpos k).le
      _ = ∑ j ∈ range J, f j k := by
        rw [sum_congr rfl heq]
        simp only [sum_const, card_range, nsmul_eq_mul]
      _ ≤ θ k := (hcols.1 k).sum_le_tsum (range J) (fun j _ => (hfpos j k).le)

end D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement
