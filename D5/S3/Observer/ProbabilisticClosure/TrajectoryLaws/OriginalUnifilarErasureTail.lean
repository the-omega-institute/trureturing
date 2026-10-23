/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarErasureTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The selected original visible law has a finite geometric erasure allowance tending to zero. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalUnifilarQuotient
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient PositiveSupportPresentation OriginalLawTrimming
open OriginalErasureComparison OriginalUnifilarQuotient

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalUnifilarErasureTail
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

/-- Original-clock allowance, including the first partial block. -/
def allowance (D rho : ℝ) (ell R : ℕ) : ℝ :=
  2*D*ell/(1-rho)*rho^(R/ell)

private theorem block_series (rho : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho < 1)
    (ell : ℕ) (he : 0 < ell) :
    Summable (fun n : ℕ => rho^(n/ell)) ∧
      (∑' n : ℕ, rho^(n/ell)) = (ell : ℝ)/(1-rho) := by
  letI : NeZero ell := ⟨he.ne'⟩
  have hg := summable_geometric_of_lt_one hr0 hr1
  have hprod : Summable (fun p : ℕ × Fin ell => rho^p.1) := by
    rw [summable_prod_of_nonneg (fun p => pow_nonneg hr0 p.1)]
    exact ⟨fun _ => (hasSum_fintype _).summable,by
      simpa only [tsum_fintype,Finset.sum_const,Finset.card_fin,nsmul_eq_mul] using hg.mul_left (ell : ℝ)⟩
  have hmajor : Summable (fun n : ℕ => rho^(n/ell)) :=
    hprod.comp_injective (Nat.divModEquiv ell).injective
  refine ⟨hmajor,?_⟩
  calc
    ∑' n : ℕ, rho^(n/ell) = ∑' p : ℕ × Fin ell, rho^p.1 :=
      by simpa only [Nat.divModEquiv_apply] using
        (Nat.divModEquiv ell).tsum_eq (fun p : ℕ × Fin ell => rho^p.1)
    _ = ∑' n : ℕ, ∑' _i : Fin ell, rho^n := hprod.tsum_prod
    _ = (ell : ℝ) * ∑' n : ℕ, rho^n := by simp [tsum_mul_left]
    _ = (ell : ℝ)/(1-rho) := by rw [tsum_geometric_of_lt_one hr0 hr1]; rfl

theorem tail_series (D rho : ℝ) (hD : 0 ≤ D) (hr0 : 0 ≤ rho) (hr1 : rho < 1)
    (ell : ℕ) (he : 0 < ell) (R : ℕ) :
    Summable (fun n : ℕ => D*rho^((R+n)/ell)) ∧
      (∑' n : ℕ, D*rho^((R+n)/ell)) ≤ D*(ell : ℝ)/(1-rho)*rho^(R/ell) := by
  have hb := block_series rho hr0 hr1 ell he
  have hm : Summable (fun n : ℕ => D*rho^(R/ell)*rho^(n/ell)) := hb.1.mul_left _
  have hpoint (n : ℕ) : D*rho^((R+n)/ell) ≤ D*rho^(R/ell)*rho^(n/ell) := by
    rw [mul_assoc,← pow_add]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hr0 hr1.le (Nat.div_add_div_le_add_div)) hD
  have hsum := Summable.of_nonneg_of_le (fun n => mul_nonneg hD (pow_nonneg hr0 _)) hpoint hm
  refine ⟨hsum,(hsum.tsum_le_tsum hpoint hm).trans_eq ?_⟩
  rw [tsum_mul_left,hb.2]
  ring

/-- Both original full-half-line defects and the possibly infinite tail become summable
on the same selected law under retained-row unifilarity. -/
theorem all_stationary_geometric_allowance (θ : Presentation H) (hu : RowUnifilar (trim θ).matrix) :
    letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
    let D := pairWeight (classWeight (trim θ))
    ∃ (ell : ℕ) (rho : ℝ), 0 < ell ∧ 0 ≤ rho ∧ rho < 1 ∧
      (∀ r : ℕ, classError θ r ≤ ENNReal.ofReal (D*rho^(r/ell)) ∧
        leftRisk θ r ≤ D*rho^(r/ell) ∧ rightRisk θ r ≤ D*rho^(r/ell)) ∧
      (∀ R : ℕ, erasureTail θ R ≤ ENNReal.ofReal (allowance D rho ell R) ∧
        erasureTail θ R ≠ ⊤) ∧
      Summable (fun r : ℕ => leftRisk θ r+rightRisk θ r) ∧
      Tendsto (allowance D rho ell) atTop (𝓝 0) ∧
      Tendsto (erasureTail θ) atTop (𝓝 0) ∧
      (rho = 0 → ∀ r : ℕ, ell ≤ r → classError θ r = 0 ∧
        leftRisk θ r = 0 ∧ rightRisk θ r = 0) ∧
      (Fintype.card (FutureClass (trim θ).matrix) = 1 →
        ∀ R : ℕ, classError θ R = 0 ∧ leftRisk θ R = 0 ∧ rightRisk θ R = 0 ∧
          erasureTail θ R = 0 ∧ allowance D rho ell R = 0) := by
  classical
  letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
  let D := pairWeight (classWeight (trim θ))
  obtain ⟨hD,hDK,ell,rho,he,hr0,hr1,_hd,_haff,_hc,hclass⟩ := actual_geometric_classification θ hu
  change ∀ r, classError θ r ≤ ENNReal.ofReal (D*rho^(r/ell)) at hclass
  change 0 ≤ D at hD
  have hcomp := full_half_line_erasure_comparison θ
  have hpoint (r : ℕ) : leftRisk θ r ≤ D*rho^(r/ell) ∧ rightRisk θ r ≤ D*rho^(r/ell) := by
    have hm := hclass r
    have hf : classError θ r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
    have hb : (classError θ r).toReal ≤ D*rho^(r/ell) :=
      (ENNReal.le_ofReal_iff_toReal_le hf (mul_nonneg hD (pow_nonneg hr0 _))).mp hm
    exact ⟨((hcomp.1 r).2.2.2.2.1).trans hb,((hcomp.1 r).2.2.2.2.2).trans hb⟩
  have htail (R : ℕ) : erasureTail θ R ≤ ENNReal.ofReal (allowance D rho ell R) := by
    have hs := tail_series D rho hD hr0 hr1 ell he R
    calc
      erasureTail θ R ≤ 2*∑' n : ℕ, classError θ (R+n) := hcomp.2.1 R
      _ ≤ 2*∑' n : ℕ, ENNReal.ofReal (D*rho^((R+n)/ell)) := by
        exact mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum (fun n => hclass (R+n))) (by positivity)
      _ = ENNReal.ofReal (2*∑' n : ℕ, D*rho^((R+n)/ell)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hD (pow_nonneg hr0 _)) hs.1,
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      _ ≤ ENNReal.ofReal (allowance D rho ell R) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          2*∑' n : ℕ, D*rho^((R+n)/ell) ≤
              2*(D*(ell : ℝ)/(1-rho)*rho^(R/ell)) :=
            mul_le_mul_of_nonneg_left hs.2 (by norm_num)
          _ = allowance D rho ell R := by unfold allowance; ring
  have hnonneg (r : ℕ) : 0 ≤ leftRisk θ r ∧ 0 ≤ rightRisk θ r := by
    exact ⟨integral_nonneg (fun z => sq_nonneg _),integral_nonneg (fun z => sq_nonneg _)⟩
  have hsummable : Summable (fun r : ℕ => leftRisk θ r+rightRisk θ r) := by
    apply Summable.of_nonneg_of_le (fun r => add_nonneg (hnonneg r).1 (hnonneg r).2)
      (fun r => add_le_add (hpoint r).1 (hpoint r).2)
    simpa only [Nat.zero_add] using (tail_series D rho hD hr0 hr1 ell he 0).1.add
      (tail_series D rho hD hr0 hr1 ell he 0).1
  have hlim : Tendsto (allowance D rho ell) atTop (𝓝 0) := by
    change Tendsto (fun R : ℕ => 2*D*ell/(1-rho)*rho^(R/ell)) atTop (𝓝 0)
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      (Nat.tendsto_div_const_atTop he.ne')
    simpa only [allowance,Function.comp_def,mul_zero] using ht.const_mul (2*D*ell/(1-rho))
  refine ⟨ell,rho,he,hr0,hr1,fun r => ⟨hclass r,(hpoint r).1,(hpoint r).2⟩,
    fun R => ⟨htail R,ne_top_of_le_ne_top ENNReal.ofReal_ne_top (htail R)⟩,
    hsummable,hlim,?_,?_,?_⟩
  · have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
    simpa only [ENNReal.ofReal_zero] using
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun R => by simp only [ENNReal.ofReal_zero]; exact bot_le) htail
  · intro hr r hrl
    have hn : r/ell ≠ 0 := Nat.ne_of_gt (Nat.div_pos hrl he)
    have hz : D*rho^(r/ell) = 0 := by simp [hr,zero_pow hn]
    have hcz : classError θ r = 0 := le_antisymm (by simpa only [hz,ENNReal.ofReal_zero] using hclass r) bot_le
    exact ⟨hcz,le_antisymm ((hpoint r).1.trans_eq hz) (hnonneg r).1,
      le_antisymm ((hpoint r).2.trans_eq hz) (hnonneg r).2⟩
  · intro hK
    have hDz : D = 0 := le_antisymm (by simpa [hK] using hDK) hD
    intro R
    have hc : classError θ R = 0 := le_antisymm (by simpa only [hDz,zero_mul,ENNReal.ofReal_zero] using hclass R) bot_le
    refine ⟨hc,le_antisymm (by simpa [hDz] using (hpoint R).1) (hnonneg R).1,
      le_antisymm (by simpa [hDz] using (hpoint R).2) (hnonneg R).2,
      le_antisymm (by simpa [allowance,hDz] using htail R) bot_le,?_⟩
    change 2*D*ell/(1-rho)*rho^(R/ell) = 0
    simp only [hDz,mul_zero,zero_mul,zero_div]

#print axioms all_stationary_geometric_allowance
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalUnifilarErasureTail
