/- GID: D5/S3/Quantum/Decoherence/GibbsLadderForwardVariance
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/GibbsLadderForwardVariance
   mirror-E: none(waiver:analytic-gibbs-ladder-proof)
   anchors: []
   utility: none
   digest: Finite cyclic Gibbs dynamics can have arbitrarily small forward variance at a fixed positive mean. -/

import D5.S3.Quantum.Decoherence.GibbsBathBandwidth
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Topology.Order.IntermediateValue

/-!
Finite Gibbs ladder for the forward-variance question in arXiv:2611.33384v1,
Section VI. The finite Gibbs ladder gives actual cyclic permutation dynamics.
-/

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace GibbsLadderForwardVariance

open GibbsBathBandwidth (gibbsWeight gibbsWeight_pos sum_gibbsWeight)

noncomputable section

/-- Equally spaced energies on a ladder of `n + 2` levels. -/
def ladderEnergy {n : ℕ} (ν : ℝ) (i : Fin (n + 2)) : ℝ :=
  ν * (i.val : ℝ)

/-- Energy after the cyclic shift minus energy before it. -/
def forwardChange {n : ℕ} (ν : ℝ) (i : Fin (n + 2)) : ℝ :=
  ladderEnergy ν (finRotate (n + 2) i) - ladderEnergy ν i

private theorem forwardChange_castSucc (n : ℕ) (ν : ℝ) (i : Fin (n + 1)) :
    forwardChange ν i.castSucc = ν := by
  have hrotate : finRotate (n + 2) i.castSucc = i.succ := by
    apply Fin.ext
    exact coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)
  rw [forwardChange, hrotate]
  simp only [ladderEnergy, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

private theorem forwardChange_last (n : ℕ) (ν : ℝ) :
    forwardChange ν (Fin.last (n + 1)) = -((n : ℝ) + 1) * ν := by
  rw [forwardChange, finRotate_last]
  simp only [ladderEnergy, Fin.val_zero, Nat.cast_zero, mul_zero, Fin.val_last,
    Nat.cast_add, Nat.cast_one]
  ring

private def partition (β : ℝ) (n : ℕ) (ν : ℝ) : ℝ :=
  ∑ i : Fin (n + 2), Real.exp (-β * ladderEnergy ν i)

private theorem one_le_partition (β : ℝ) (n : ℕ) (ν : ℝ) : 1 ≤ partition β n ν := by
  calc
    1 = Real.exp (-β * ladderEnergy (n := n) ν 0) := by simp [ladderEnergy]
    _ ≤ partition β n ν :=
      Finset.single_le_sum (fun i _ => (Real.exp_pos (-β * ladderEnergy ν i)).le)
        (Finset.mem_univ (0 : Fin (n + 2)))

private def lastWeight (β : ℝ) (n : ℕ) (ν : ℝ) : ℝ :=
  gibbsWeight β (ladderEnergy ν) (Fin.last (n + 1))

private theorem lastWeight_pos (β : ℝ) (n : ℕ) (ν : ℝ) : 0 < lastWeight β n ν :=
  gibbsWeight_pos β (ladderEnergy ν) (Fin.last (n + 1))

private theorem lastWeight_eq (β : ℝ) (n : ℕ) (ν : ℝ) :
    lastWeight β n ν = Real.exp (-β * ν) ^ (n + 1) / partition β n ν := by
  rw [← Real.exp_nat_mul]
  change Real.exp (-β * ladderEnergy ν (Fin.last (n + 1))) / partition β n ν = _
  have hexponent : -β * ladderEnergy ν (Fin.last (n + 1)) =
      ((n + 1 : ℕ) : ℝ) * (-β * ν) := by
    simp only [ladderEnergy, Fin.val_last]
    ring
  rw [hexponent]

private theorem lastWeight_le (β : ℝ) (n : ℕ) (ν : ℝ) :
    lastWeight β n ν ≤ Real.exp (-β * ν) ^ (n + 1) := by
  rw [lastWeight_eq]
  exact div_le_self (pow_nonneg (Real.exp_pos _).le _) (one_le_partition β n ν)

private theorem continuous_lastWeight (β : ℝ) (n : ℕ) : Continuous (lastWeight β n) := by
  have hpartition : Continuous (partition β n) := by
    change Continuous (fun ν : ℝ => ∑ i : Fin (n + 2), Real.exp (-β * (ν * (i.val : ℝ))))
    exact continuous_finsetSum _ fun i _ => by fun_prop
  have hnum : Continuous (fun ν : ℝ => Real.exp (-β * ν) ^ (n + 1)) := by fun_prop
  have hformula : lastWeight β n =
      (fun ν => Real.exp (-β * ν) ^ (n + 1) / partition β n ν) :=
    funext (lastWeight_eq β n)
  rw [hformula]
  exact hnum.div hpartition (fun ν => ne_of_gt (zero_lt_one.trans_le (one_le_partition β n ν)))

private theorem forwardMean_eq (β : ℝ) (n : ℕ) (ν : ℝ) :
    (∑ i : Fin (n + 2), gibbsWeight β (ladderEnergy ν) i * forwardChange ν i) =
      ν - ν * (((n : ℝ) + 2) * lastWeight β n ν) := by
  have hmass : (∑ i : Fin (n + 1), gibbsWeight β (ladderEnergy ν) i.castSucc) =
      1 - lastWeight β n ν := by
    have htotal := sum_gibbsWeight β (ladderEnergy (n := n) ν)
    rw [Fin.sum_univ_castSucc] at htotal
    exact eq_sub_of_add_eq htotal
  rw [Fin.sum_univ_castSucc]
  simp only [forwardChange_castSucc, forwardChange_last, ← Finset.sum_mul]
  change (∑ i : Fin (n + 1), gibbsWeight β (ladderEnergy ν) i.castSucc) * ν +
    lastWeight β n ν * (-((n : ℝ) + 1) * ν) = _
  rw [hmass]
  ring

private theorem secondMoment_eq (β : ℝ) (n : ℕ) (ν : ℝ) :
    (∑ i : Fin (n + 2), gibbsWeight β (ladderEnergy ν) i * (forwardChange ν i - ν) ^ 2) =
      ν ^ 2 * ((n : ℝ) + 2) ^ 2 * lastWeight β n ν := by
  rw [Fin.sum_univ_castSucc]
  simp only [forwardChange_castSucc, forwardChange_last, sub_self,
    zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero, zero_add]
  change lastWeight β n ν * (-((n : ℝ) + 1) * ν - ν) ^ 2 = _
  ring

private theorem centeredMoment_le {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    {μ ν : ℝ} (hmass : ∑ i, p i = 1) (hmean : ∑ i, p i * q i = μ) :
    (∑ i, p i * (q i - μ) ^ 2) ≤ ∑ i, p i * (q i - ν) ^ 2 := by
  calc
    _ ≤ (∑ i, p i * (q i - μ) ^ 2) + (ν - μ) ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg _)
    _ = (∑ i, p i * (q i - μ) ^ 2) + (2 * (μ - ν)) * (∑ i, p i * q i) +
        (ν ^ 2 - μ ^ 2) * (∑ i, p i) := by
      rw [hmean, hmass]
      ring
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring

private theorem exists_small_tail {r ε : ℝ} (hr : 0 < r) (hr₁ : r < 1) (hε : 0 < ε) :
    ∃ n : ℕ, ((n : ℝ) + 2) ^ 2 * r ^ (n + 1) < ε := by
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by
      simpa only [Real.norm_eq_abs, abs_of_pos hr] using hr₁)
  have ht : Tendsto (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) atTop (𝓝 0) := by
    simpa only [Nat.cofinite_eq_atTop] using hs.tendsto_cofinite_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_lt_const (mul_pos hε hr))
  refine ⟨N, lt_of_mul_lt_mul_right ?_ hr.le⟩
  calc
    ((N : ℝ) + 2) ^ 2 * r ^ (N + 1) * r = ((N + 2 : ℕ) : ℝ) ^ 2 * r ^ (N + 2) := by
      rw [show ((N + 2 : ℕ) : ℝ) = (N : ℝ) + 2 by push_cast <;> rfl,
        show r ^ (N + 2) = r ^ (N + 1) * r from pow_succ r (N + 1), mul_assoc]
    _ < ε * r := hN (N + 2) (by omega)

/-- At any positive inverse temperature, a finite Gibbs ladder and its cyclic shift
can realize any prescribed positive mean forward energy change with arbitrarily
small forward variance. -/
theorem exists_gibbs_ladder_forward_variance_lt {β μ η : ℝ}
    (hβ : 0 < β) (hμ : 0 < μ) (hη : 0 < η) :
    ∃ (n : ℕ) (ν : ℝ), 0 < ν ∧
      (∑ i : Fin (n + 2), gibbsWeight β (ladderEnergy ν) i * forwardChange ν i) = μ ∧
      (∑ i : Fin (n + 2), gibbsWeight β (ladderEnergy ν) i * (forwardChange ν i - μ) ^ 2) < η := by
  let lo := μ / 2
  let hi := 3 * μ / 2
  have hlo : 0 < lo := by dsimp [lo]; linarith
  have hhi : 0 < hi := by dsimp [hi]; linarith
  have hinterval : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hhi_sq : 0 < hi ^ 2 := pow_pos hhi 2
  let ε := min (1 / 3 : ℝ) (η / hi ^ 2)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hη hhi_sq)
  let r := Real.exp (-β * lo)
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) hlo)
  obtain ⟨n, hn⟩ := exists_small_tail hr hr₁ hε
  have htail (ν : ℝ) (hν : lo ≤ ν) : ((n : ℝ) + 2) ^ 2 * lastWeight β n ν < ε := by
    have hexp : Real.exp (-β * ν) ≤ r :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hν (neg_nonpos.mpr hβ.le))
    calc
      _ ≤ ((n : ℝ) + 2) ^ 2 * r ^ (n + 1) :=
        mul_le_mul_of_nonneg_left
          ((lastWeight_le β n ν).trans (pow_le_pow_left₀ (Real.exp_pos _).le hexp _))
          (sq_nonneg _)
      _ < ε := hn
  have hsize : 1 ≤ (n : ℝ) + 2 := by
    have hn₀ : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsize₀ := zero_le_one.trans hsize
  let mean : ℝ → ℝ := fun ν => ν - ν * (((n : ℝ) + 2) * lastWeight β n ν)
  have hcont : Continuous mean :=
    continuous_id.sub (continuous_id.mul (continuous_const.mul (continuous_lastWeight β n)))
  have hlow_mean : mean lo ≤ μ := by
    have hdrop : 0 ≤ lo * (((n : ℝ) + 2) * lastWeight β n lo) :=
      mul_nonneg hlo.le (mul_nonneg hsize₀ (lastWeight_pos β n lo).le)
    have hlo_le : lo ≤ μ := by dsimp [lo]; linarith
    exact (sub_le_self _ hdrop).trans hlo_le
  have hlinear : ((n : ℝ) + 2) * lastWeight β n hi < 1 / 3 := by
    have hsize_sq : (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 2 := by
      simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right hsize hsize₀
    calc
      _ ≤ ((n : ℝ) + 2) ^ 2 * lastWeight β n hi :=
        mul_le_mul_of_nonneg_right hsize_sq (lastWeight_pos β n hi).le
      _ < ε := htail hi hinterval
      _ ≤ 1 / 3 := min_le_left _ _
  have hhigh_mean : μ ≤ mean hi := by
    calc
      μ = hi - hi * (1 / 3) := by dsimp [hi]; ring
      _ ≤ mean hi := sub_le_sub_left (mul_lt_mul_of_pos_left hlinear hhi).le hi
  obtain ⟨ν, hν, hcalibrated⟩ := intermediate_value_Icc hinterval hcont.continuousOn
    (show μ ∈ Set.Icc (mean lo) (mean hi) from ⟨hlow_mean, hhigh_mean⟩)
  have hν₀ : 0 < ν := hlo.trans_le hν.1
  have hmean := (forwardMean_eq β n ν).trans hcalibrated
  refine ⟨n, ν, hν₀, hmean, ?_⟩
  calc
    _ ≤ ∑ i : Fin (n + 2), gibbsWeight β (ladderEnergy ν) i * (forwardChange ν i - ν) ^ 2 :=
      centeredMoment_le (gibbsWeight β (ladderEnergy ν)) (forwardChange ν)
        (sum_gibbsWeight β (ladderEnergy ν)) hmean
    _ = ν ^ 2 * (((n : ℝ) + 2) ^ 2 * lastWeight β n ν) := by rw [secondMoment_eq, mul_assoc]
    _ ≤ hi ^ 2 * (((n : ℝ) + 2) ^ 2 * lastWeight β n ν) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hν₀.le hν.2 2)
        (mul_nonneg (sq_nonneg _) (lastWeight_pos β n ν).le)
    _ < hi ^ 2 * (η / hi ^ 2) :=
      mul_lt_mul_of_pos_left ((htail ν hν.1).trans_le (min_le_right _ _)) hhi_sq
    _ = η := mul_div_cancel₀ η (ne_of_gt hhi_sq)

end

#print axioms exists_gibbs_ladder_forward_variance_lt

end GibbsLadderForwardVariance
