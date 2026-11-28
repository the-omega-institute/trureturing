/- GID: D5/S3/Quantum/Decoherence/GibbsLadderReverseBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/GibbsLadderReverseBudget
   mirror-E: none(waiver:analytic-reflected-tilt-and-gibbs-calibration)
   anchors: []
   utility: none
   digest: A reverse mean budget fixes the sharp logarithmic rate of forward variance. -/

import D5.S3.Quantum.Decoherence.GibbsLadderForwardVariance
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Forward variance under a reverse mean budget

The finite-law input is the reflected exponential tilt from Marcos L. W. Basso,
“Modular fluctuation relations on local causal horizons”, Eq. (29)
<https://arxiv.org/html/2611.33384v1#S3.E29>.
The recovery protocols use the Gibbs energies and cyclic permutations of
`GibbsLadderForwardVariance`.
-/

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace GibbsLadderReverseBudget

noncomputable section

/-- Reverse probability on the same index, carrying the value `-X i`. -/
def reverseWeight {ι : Type*} (β : ℝ) (p X : ι → ℝ) (i : ι) : ℝ :=
  p i * Real.exp (-β * X i)

def forwardVariance {ι : Type*} [Fintype ι] (p X : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ i, p i * (X i - a) ^ 2

def reverseMean {ι : Type*} [Fintype ι] (β : ℝ) (p X : ι → ℝ) : ℝ :=
  ∑ i, reverseWeight β p X i * (-X i)

/-- A finite-law bound on the second moment about an observation point. -/
theorem variance_lower_bound {ι : Type*} [Fintype ι] (p X : ι → ℝ)
    {β a B δ R : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hR : 0 < R)
    (hp : ∀ i, 0 ≤ p i) (hp_mass : ∑ i, p i = 1)
    (hq_mass : ∑ i, reverseWeight β p X i = 1)
    (hbudget : reverseMean β p X ≤ B) :
    δ ^ 2 * Real.exp (-β * R) *
      ((1 - Real.exp (-β * (a - δ))) - (B + 1 / (Real.exp 1 * β)) / R) ≤
      forwardVariance p X a := by
  classical
  let q := reverseWeight β p X
  let C := 1 / (Real.exp 1 * β)
  let tail : ι → ℝ := fun i => if X i < -R then q i else 0
  have hq (i : ι) : 0 ≤ q i := mul_nonneg (hp i) (Real.exp_pos _).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcost (i : ι) : R * tail i ≤ q i * (-X i) + p i * C := by
    by_cases hi : X i < -R
    · simp only [tail, ite_eq_left hi]
      calc
        R * q i ≤ (-X i) * q i := mul_le_mul_of_nonneg_right (by linarith) (hq i)
        _ ≤ q i * (-X i) + p i * C := by
          rw [mul_comm (-X i)]
          exact le_add_of_nonneg_right (mul_nonneg (hp i) hC)
    · simp only [tail, ite_eq_right hi, mul_zero]
      have hexp := Real.mul_exp_neg_le_exp_neg_one (β * X i)
      rw [show -(β * X i) = -β * X i by ring, Real.exp_neg] at hexp
      have hXi : X i * Real.exp (-β * X i) ≤ C := by
        apply (le_div_iff₀ (mul_pos (Real.exp_pos _) hβ)).mpr
        calc
          X i * Real.exp (-β * X i) * (Real.exp 1 * β) =
              (β * X i * Real.exp (-β * X i)) * Real.exp 1 := by ring
          _ ≤ (Real.exp 1)⁻¹ * Real.exp 1 :=
            mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
          _ = 1 := inv_mul_cancel₀ (Real.exp_ne_zero _)
      have hmul := mul_le_mul_of_nonneg_left hXi (hp i)
      dsimp [q, reverseWeight]
      linarith only [hmul]
  have htail : (∑ i, tail i) ≤ (B + C) / R := by
    apply (le_div_iff₀ hR).mpr
    rw [mul_comm _ R, Finset.mul_sum]
    calc
      _ ≤ ∑ i, (q i * (-X i) + p i * C) := Finset.sum_le_sum fun i _ => hcost i
      _ ≤ B + C := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp_mass, one_mul]
        exact add_le_add_left hbudget C
  let K := Real.exp (β * R) / δ ^ 2
  have hδ₂ : 0 < δ ^ 2 := pow_pos hδ 2
  have hK : 0 ≤ K := div_nonneg (Real.exp_pos _).le hδ₂.le
  have htilt (i : ι) : q i ≤ tail i + p i * Real.exp (-β * (a - δ)) +
      K * (p i * (X i - a) ^ 2) := by
    have herr : 0 ≤ K * (p i * (X i - a) ^ 2) :=
      mul_nonneg hK (mul_nonneg (hp i) (sq_nonneg _))
    by_cases hi : X i < -R
    · simp only [tail, ite_eq_left hi]
      linarith only [herr, mul_nonneg (hp i) (Real.exp_pos (-β * (a - δ))).le]
    simp only [tail, ite_eq_right hi, zero_add]
    by_cases hnear : a - δ ≤ X i
    · have hmono := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hnear (neg_nonpos.mpr hβ.le))
      exact (mul_le_mul_of_nonneg_left hmono (hp i)).trans (le_add_of_nonneg_right herr)
    · have hmono : Real.exp (-β * X i) ≤ Real.exp (β * R) := by
        apply Real.exp_le_exp.mpr
        calc
          -β * X i ≤ -β * (-R) := mul_le_mul_of_nonpos_left (le_of_not_gt hi) (neg_nonpos.mpr hβ.le)
          _ = β * R := by ring
      have hsquare : δ ^ 2 ≤ (X i - a) ^ 2 := by
        rw [← neg_sub, neg_sq]
        exact pow_le_pow_left₀ hδ.le (by linarith [lt_of_not_ge hnear]) 2
      calc
        q i ≤ p i * Real.exp (β * R) := mul_le_mul_of_nonneg_left hmono (hp i)
        _ = K * (p i * δ ^ 2) := by dsimp [K]; field_simp [hδ.ne']
        _ ≤ K * (p i * (X i - a) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsquare (hp i)) hK
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (hp i) (Real.exp_pos _).le)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => htilt i)
  change (∑ i, reverseWeight β p X i) ≤ _ at hsum
  rw [hq_mass, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hp_mass, one_mul] at hsum
  have hineq : (1 - Real.exp (-β * (a - δ))) - (B + C) / R ≤
      K * forwardVariance p X a := by
    unfold forwardVariance
    linarith only [hsum, htail]
  have hscale : δ ^ 2 * Real.exp (-β * R) * K = 1 := by
    dsimp [K]
    rw [show -β * R = -(β * R) by ring, Real.exp_neg]
    field_simp [hδ.ne', Real.exp_ne_zero]
  calc
    _ ≤ δ ^ 2 * Real.exp (-β * R) * (K * forwardVariance p X a) :=
      mul_le_mul_of_nonneg_left hineq (mul_nonneg hδ₂.le (Real.exp_pos _).le)
    _ = _ := by rw [← mul_assoc, hscale, one_mul]

/-- The explicit floor is strictly positive at every nonnegative budget. -/
theorem variance_exponential_floor {ι : Type*} [Fintype ι] (p X : ι → ℝ)
    {β a B δ γ : ℝ} (hβ : 0 < β) (hB : 0 ≤ B) (hδ : 0 < δ) (hδa : δ < a)
    (hγ : 0 < γ) (hp : ∀ i, 0 ≤ p i) (hp_mass : ∑ i, p i = 1)
    (hq_mass : ∑ i, reverseWeight β p X i = 1)
    (hbudget : reverseMean β p X ≤ B) :
    let c := 1 - Real.exp (-β * (a - δ))
    let R := (1 + γ) * (B + 1 / (Real.exp 1 * β)) / c
    0 < δ ^ 2 * Real.exp (-β * R) * (c * γ / (1 + γ)) ∧
    δ ^ 2 * Real.exp (-β * R) * (c * γ / (1 + γ)) ≤ forwardVariance p X a := by
  dsimp only
  let c := 1 - Real.exp (-β * (a - δ))
  let C := 1 / (Real.exp 1 * β)
  let R := (1 + γ) * (B + C) / c
  have hc : 0 < c := sub_pos.mpr (Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) (sub_pos.mpr hδa)))
  have hBC : 0 < B + C := add_pos_of_nonneg_of_pos hB (by dsimp [C]; positivity)
  have hγ₁ : 0 < 1 + γ := by positivity
  have hR : 0 < R := div_pos (mul_pos hγ₁ hBC) hc
  have hbracket : c - (B + C) / R = c * γ / (1 + γ) := by
    dsimp only [R]
    field_simp [hc.ne', hBC.ne', hγ₁.ne']
    ring
  refine ⟨mul_pos (mul_pos (pow_pos hδ 2) (Real.exp_pos _))
    (div_pos (mul_pos hc hγ) hγ₁), ?_⟩
  rw [← hbracket]
  exact variance_lower_bound p X hβ hδ hR hp hp_mass hq_mass hbudget

open GibbsLadderForwardVariance (ladderEnergy forwardChange)
open GibbsBathBandwidth (gibbsWeight gibbsWeight_pos sum_gibbsWeight)

abbrev ladderWeight (β : ℝ) (n : ℕ) (ν : ℝ) :=
  gibbsWeight β (ladderEnergy (n := n) ν)

abbrev lastLevel (n : ℕ) : Fin (n + 2) := Fin.last (n + 1)

/-- Transport of the Gibbs weights by any permutation of a finite energy spectrum. -/
private theorem gibbs_weight_tilt {ι : Type*} [Fintype ι] [Nonempty ι] (β : ℝ) (E : ι → ℝ)
    (σ : Equiv.Perm ι) (i : ι) :
    reverseWeight β (gibbsWeight β E) (fun j => E (σ j) - E j) i =
      gibbsWeight β E (σ i) := by
  simp only [reverseWeight, gibbsWeight, div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

private theorem ladder_reverseWeight (β : ℝ) (n : ℕ) (ν : ℝ) (i : Fin (n + 2)) :
    reverseWeight β (ladderWeight β n ν) (forwardChange ν) i =
      ladderWeight β n ν (finRotate (n + 2) i) :=
  gibbs_weight_tilt β (ladderEnergy ν) (finRotate (n + 2)) i

private theorem ladder_reverse_mass (β : ℝ) (n : ℕ) (ν : ℝ) :
    ∑ i, reverseWeight β (ladderWeight β n ν) (forwardChange ν) i = 1 := by
  simp only [ladder_reverseWeight]
  calc
    _ = ∑ i, ladderWeight β n ν i := Equiv.sum_comp (finRotate (n + 2)) (ladderWeight β n ν)
    _ = 1 := sum_gibbsWeight β (ladderEnergy ν)

/-- The reverse mean indexed by the arrival level is the work of the inverse cycle. -/
private theorem ladder_reverseMean_inverse (β : ℝ) (n : ℕ) (ν : ℝ) :
    reverseMean β (ladderWeight β n ν) (forwardChange ν) =
      ∑ j, ladderWeight β n ν j *
        (ladderEnergy ν ((finRotate (n + 2)).symm j) - ladderEnergy ν j) := by
  unfold reverseMean
  simp only [ladder_reverseWeight, forwardChange, neg_sub]
  symm
  calc
    _ = ∑ i, ladderWeight β n ν (finRotate (n + 2) i) *
        (ladderEnergy ν ((finRotate (n + 2)).symm (finRotate (n + 2) i)) -
          ladderEnergy ν (finRotate (n + 2) i)) :=
      (Equiv.sum_comp (finRotate (n + 2)) _).symm
    _ = _ := by simp only [Equiv.symm_apply_apply]

private theorem ladder_succ_change (n : ℕ) (ν : ℝ) (i : Fin (n + 1)) :
    forwardChange ν i.castSucc = ν := by
  have hrotate : finRotate (n + 2) i.castSucc = i.succ :=
    Fin.ext (coe_finRotate_of_ne_last (Fin.castSucc_ne_last i))
  rw [forwardChange, hrotate]
  simp only [ladderEnergy, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

private theorem ladder_last_change (n : ℕ) (ν : ℝ) :
    forwardChange ν (lastLevel n) = -((n : ℝ) + 1) * ν := by
  rw [forwardChange, finRotate_last]
  simp only [ladderEnergy, Fin.val_zero, Nat.cast_zero, mul_zero, Fin.val_last,
    Nat.cast_add, Nat.cast_one]
  ring

private theorem ladder_sum (n : ℕ) (ν : ℝ) (w : Fin (n + 2) → ℝ) (f : ℝ → ℝ)
    (hmass : ∑ i, w i = 1) :
    ∑ i, w i * f (forwardChange ν i) =
      (1 - w (lastLevel n)) * f ν + w (lastLevel n) * f (-((n : ℝ) + 1) * ν) := by
  rw [Fin.sum_univ_castSucc] at hmass ⊢
  simp only [ladder_succ_change, ladder_last_change, ← Finset.sum_mul]
  rw [eq_sub_of_add_eq hmass]

private theorem ladder_forwardMean (β : ℝ) (n : ℕ) (ν : ℝ) :
    ∑ i, ladderWeight β n ν i * forwardChange ν i =
      ν * (1 - ((n : ℝ) + 2) * ladderWeight β n ν (lastLevel n)) := by
  change (∑ i, ladderWeight β n ν i * id (forwardChange ν i)) = _
  rw [ladder_sum n ν _ id (sum_gibbsWeight β (ladderEnergy ν))]
  dsimp only [id]
  ring

private theorem ladder_reverseMean (β : ℝ) (n : ℕ) (ν : ℝ) :
    reverseMean β (ladderWeight β n ν) (forwardChange ν) =
      ν * (((n : ℝ) + 2) * ladderWeight β n ν 0 - 1) := by
  unfold reverseMean
  rw [ladder_sum n ν _ Neg.neg (ladder_reverse_mass β n ν),
    ladder_reverseWeight, finRotate_last]
  ring

private theorem ladder_variance (β : ℝ) (n : ℕ) (ν a : ℝ)
    (hmean : ∑ i, ladderWeight β n ν i * forwardChange ν i = a) :
    forwardVariance (ladderWeight β n ν) (forwardChange ν) a =
      (((n : ℝ) + 2) * ν) ^ 2 * ladderWeight β n ν (lastLevel n) *
        (1 - ladderWeight β n ν (lastLevel n)) := by
  rw [← hmean, ladder_forwardMean]
  unfold forwardVariance
  rw [ladder_sum n ν _ (fun x => (x - ν *
    (1 - ((n : ℝ) + 2) * ladderWeight β n ν (lastLevel n))) ^ 2)
    (sum_gibbsWeight β (ladderEnergy ν))]
  ring

private theorem ladder_weight_geom (β : ℝ) (n : ℕ) (ν : ℝ) (i : Fin (n + 2)) :
    ladderWeight β n ν i =
      Real.exp (-β * ν) ^ i.val / ∑ k ∈ Finset.range (n + 2), Real.exp (-β * ν) ^ k := by
  have h (j : Fin (n + 2)) : Real.exp (-β * ladderEnergy ν j) =
      Real.exp (-β * ν) ^ j.val := by
    rw [← Real.exp_nat_mul, ladderEnergy]
    congr 1
    ring
  simp only [ladderWeight, gibbsWeight, h, Fin.sum_univ_eq_sum_range]

private theorem ladder_weight_closed {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν)
    (n : ℕ) (i : Fin (n + 2)) :
    let r := Real.exp (-β * ν)
    ladderWeight β n ν i = r ^ i.val * ((1 - r) / (1 - r ^ (n + 2))) := by
  dsimp only
  let r := Real.exp (-β * ν)
  have hr₁ : r < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) hν)
  have hpow : r ^ (n + 2) < 1 :=
    pow_lt_one₀ (Real.exp_pos _).le hr₁ (by omega)
  rw [ladder_weight_geom]
  change r ^ i.val / (∑ k ∈ Finset.range (n + 2), r ^ k) =
    r ^ i.val * ((1 - r) / (1 - r ^ (n + 2)))
  rw [geom_sum_eq hr₁.ne]
  field_simp [hr₁.ne, sub_ne_zero.mpr hr₁.ne, (sub_pos.mpr hpow).ne',
    (sub_neg.mpr hpow).ne]
  ring

private theorem lastWeight_le (β : ℝ) (n : ℕ) (ν : ℝ) :
    ladderWeight β n ν (lastLevel n) ≤ Real.exp (-β * ν) ^ (n + 1) := by
  rw [ladder_weight_geom]
  have hsum : 1 ≤ ∑ k ∈ Finset.range (n + 2), Real.exp (-β * ν) ^ k := by
    simpa only [pow_zero] using
      (Finset.single_le_sum (f := fun k => Real.exp (-β * ν) ^ k)
        (fun k _ => pow_nonneg (Real.exp_pos _).le k)
        (Finset.mem_range.mpr (by omega : 0 < n + 2)))
  exact div_le_self (pow_nonneg (Real.exp_pos _).le _) hsum

private theorem continuous_ladder_weight (β : ℝ) (n : ℕ) (i : Fin (n + 2)) :
    Continuous (fun ν => ladderWeight β n ν i) := by
  simp only [ladderWeight, gibbsWeight, ladderEnergy]
  have hcont : Continuous (fun ν : ℝ => ∑ j : Fin (n + 2),
      Real.exp (-β * (ν * (j.val : ℝ)))) :=
    continuous_finsetSum _ fun j _ => by fun_prop
  exact (by fun_prop : Continuous (fun ν : ℝ => Real.exp (-β * (ν * (i.val : ℝ))))).div
    hcont (fun ν => (Finset.sum_pos (fun j _ => Real.exp_pos (-β * (ν * (j.val : ℝ))))
      Finset.univ_nonempty).ne')

private theorem tendsto_size : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

private theorem tendsto_size_mul_geom {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) * r ^ (n + 1)) atTop (𝓝 0) := by
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ 1 * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa [abs_of_pos hr] using hr₁)
  have ht : Tendsto (fun k : ℕ => (k : ℝ) ^ 1 * r ^ k) atTop (𝓝 0) := by
    simpa only [Nat.cofinite_eq_atTop] using hs.tendsto_cofinite_zero
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr₁).comp (tendsto_add_atTop_nat 1)
  simpa only [zero_add] using
    (((ht.comp (tendsto_add_atTop_nat 1)).add hp).congr
      (fun n => by simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_one]; ring))

private theorem tendsto_lastWeight_mul_size {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (ν : ℕ → ℝ) (hν : ∀ n, a / 2 ≤ ν n) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) * ladderWeight β n (ν n) (lastLevel n)) atTop (𝓝 0) := by
  let r := Real.exp (-β * (a / 2))
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) (half_pos ha))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_size_mul_geom hr hr₁) (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (by positivity) (gibbsWeight_pos β _ _).le
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (lastWeight_le β n (ν n)).trans
      (pow_le_pow_left₀ (Real.exp_pos _).le
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hν n) (neg_nonpos.mpr hβ.le))) _)

private theorem exists_calibrated_spacing {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    ∃ ν : ℕ → ℝ, (∀ n, ν n ∈ Set.Icc (a / 2) (3 * a / 2)) ∧
      (∀ᶠ n in atTop, ∑ i, ladderWeight β n (ν n) i * forwardChange (ν n) i = a) ∧
      Tendsto ν atTop (𝓝 a) := by
  let hi := 3 * a / 2
  have hlo : 0 < a / 2 := half_pos ha
  have hhi : 0 < hi := by dsimp [hi]; positivity
  have hI : a / 2 ≤ hi := by dsimp [hi]; linarith
  have htail := tendsto_lastWeight_mul_size hβ ha (fun _ => hi) (fun _ => hI)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (htail.eventually_lt_const (by norm_num : (0 : ℝ) < 1/3))
  have hexists (n : ℕ) (hn : n₀ ≤ n) : ∃ ν ∈ Set.Icc (a / 2) hi,
      ∑ i, ladderWeight β n ν i * forwardChange ν i = a := by
    let m := fun ν => ν * (1 - ((n : ℝ) + 2) * ladderWeight β n ν (lastLevel n))
    have hm : Continuous m := continuous_id.mul
      (continuous_const.sub (continuous_const.mul (continuous_ladder_weight β n (lastLevel n))))
    have hmlo : m (a / 2) ≤ a := by
      dsimp [m]
      have hd : 0 ≤ ((n : ℝ) + 2) * ladderWeight β n (a / 2) (lastLevel n) :=
        mul_nonneg (by positivity) (gibbsWeight_pos β _ _).le
      nlinarith only [mul_nonneg hlo.le hd, ha]
    have hmhi : a ≤ m hi := by
      dsimp only [m]
      have hh := mul_lt_mul_of_pos_left (hn₀ n hn) hhi
      dsimp [hi] at hh ⊢
      linarith only [hh]
    obtain ⟨ν, hνI, hνmean⟩ :=
      intermediate_value_Icc hI hm.continuousOn (show a ∈ Set.Icc (m (a / 2)) (m hi) from
        ⟨hmlo, hmhi⟩)
    exact ⟨ν, hνI, (ladder_forwardMean β n ν).trans hνmean⟩
  have hall (n : ℕ) : ∃ ν ∈ Set.Icc (a / 2) hi, n₀ ≤ n →
      ∑ i, ladderWeight β n ν i * forwardChange ν i = a := by
    by_cases hn : n₀ ≤ n
    · obtain ⟨ν, hνI, hν⟩ := hexists n hn
      exact ⟨ν, hνI, fun _ => hν⟩
    · exact ⟨a / 2, ⟨le_rfl, hI⟩, fun h => (hn h).elim⟩
  choose ν hνI hνmean using hall
  have hmean : ∀ᶠ n in atTop, ∑ i, ladderWeight β n (ν n) i * forwardChange (ν n) i = a :=
    (eventually_ge_atTop n₀).mono (fun n hn => hνmean n hn)
  have hsmall := tendsto_lastWeight_mul_size hβ ha ν (fun n => (hνI n).1)
  refine ⟨ν, hνI, hmean, ?_⟩
  have ha_lim : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
  have hupper : Tendsto (fun n : ℕ => a + hi *
      (((n : ℝ) + 2) * ladderWeight β n (ν n) (lastLevel n))) atTop (𝓝 a) := by
    simpa only [mul_zero, add_zero] using ha_lim.add (hsmall.const_mul hi)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [hmean] with n hn
    rw [ladder_forwardMean] at hn
    have hnonneg : 0 ≤ ν n * (((n : ℝ) + 2) * ladderWeight β n (ν n) (lastLevel n)) :=
      mul_nonneg (hlo.le.trans (hνI n).1)
        (mul_nonneg (by positivity) (gibbsWeight_pos β _ _).le)
    linarith only [hn, hnonneg]
  · filter_upwards [hmean] with n hn
    rw [ladder_forwardMean] at hn
    have hle := mul_le_mul_of_nonneg_right (hνI n).2
      (mul_nonneg (by positivity : 0 ≤ (n : ℝ) + 2) (gibbsWeight_pos β _ _).le :
        0 ≤ ((n : ℝ) + 2) * ladderWeight β n (ν n) (lastLevel n))
    linarith only [hn, hle]

/-- The positive denominator in the sharp reverse-budget rate. -/
def tiltDeficit (β a : ℝ) : ℝ := 1 - Real.exp (-β * a)

private theorem tiltDeficit_pos {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) : 0 < tiltDeficit β a :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) ha))

/-- The Gibbs cycle achieves the matching exponent at its actual reverse mean.
Each sufficiently large ladder is calibrated to have forward mean exactly `a`. -/
theorem exists_calibrated_gibbs_rate {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    ∃ ν : ℕ → ℝ, (∀ n, ν n ∈ Set.Icc (a / 2) (3 * a / 2)) ∧ Tendsto ν atTop (𝓝 a) ∧
      (∀ᶠ n in atTop, ∑ i, ladderWeight β n (ν n) i * forwardChange (ν n) i = a) ∧
      (let b := fun n => reverseMean β (ladderWeight β n (ν n)) (forwardChange (ν n))
       let v := fun n => forwardVariance (ladderWeight β n (ν n)) (forwardChange (ν n)) a
       (∀ᶠ n in atTop, 0 < v n) ∧
       Tendsto (fun n => b n / ((n : ℝ) + 2)) atTop (𝓝 (a * tiltDeficit β a)) ∧
       Tendsto (fun n => Real.log (v n) / ((n : ℝ) + 2)) atTop (𝓝 (-β * a)) ∧
       Tendsto b atTop atTop ∧
       Tendsto (fun n => Real.log (v n) / b n) atTop (𝓝 (-β / tiltDeficit β a))) := by
  obtain ⟨ν, hνI, hmean, hν⟩ := exists_calibrated_spacing hβ ha
  refine ⟨ν, hνI, hν, hmean, ?_⟩
  dsimp only
  let N := fun n : ℕ => (n : ℝ) + 2
  let r := fun n => Real.exp (-β * ν n)
  let p₀ := fun n => ladderWeight β n (ν n) 0
  let pLast := fun n => ladderWeight β n (ν n) (lastLevel n)
  let b := fun n => reverseMean β (ladderWeight β n (ν n)) (forwardChange (ν n))
  let v := fun n => forwardVariance (ladderWeight β n (ν n)) (forwardChange (ν n)) a
  have hνpos (n : ℕ) : 0 < ν n := (half_pos ha).trans_le (hνI n).1
  have hNpos (n : ℕ) : 0 < N n := by dsimp [N]; positivity
  have hNinv : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_size
  have hr : Tendsto r atTop (𝓝 (Real.exp (-β * a))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (hν.const_mul (-β))
  let ρ := Real.exp (-β * (a / 2))
  have hρ : 0 < ρ := Real.exp_pos _
  have hρ₁ : ρ < 1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) (half_pos ha))
  have hrle (n : ℕ) : r n ≤ ρ :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hνI n).1 (neg_nonpos.mpr hβ.le))
  have hpower (k : ℕ) : Tendsto (fun n => r n ^ (n + k)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ₁).comp (tendsto_add_atTop_nat k))
      (fun n => pow_nonneg (Real.exp_pos _).le _) (fun n => ?_)
    exact pow_le_pow_left₀ (Real.exp_pos _).le (hrle n) _
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hp₀ : Tendsto p₀ atTop (𝓝 (tiltDeficit β a)) := by
    have h : Tendsto (fun n => (1 - r n) / (1 - r n ^ (n + 2))) atTop
        (𝓝 (tiltDeficit β a)) := by
      have hlim := (hone.sub hr).div (hone.sub (hpower 2)) (show (1 : ℝ) - 0 ≠ 0 by norm_num)
      rw [sub_zero, div_one] at hlim
      exact hlim.congr (fun _ => rfl)
    refine h.congr ?_
    intro n
    simpa only [Fin.val_zero, pow_zero, one_mul] using (ladder_weight_closed hβ (hνpos n) n 0).symm
  have hpLast_formula (n : ℕ) : pLast n = r n ^ (n + 1) * p₀ n := by
    rw [show pLast n = ladderWeight β n (ν n) (lastLevel n) from rfl, ladder_weight_closed hβ (hνpos n),
      show p₀ n = ladderWeight β n (ν n) 0 from rfl, ladder_weight_closed hβ (hνpos n)]
    simp [r]
  have hpLast : Tendsto pLast atTop (𝓝 0) := by
    simpa only [zero_mul] using ((hpower 1).mul hp₀).congr (fun n => (hpLast_formula n).symm)
  have hb : Tendsto (fun n => b n / N n) atTop (𝓝 (a * tiltDeficit β a)) := by
    simpa only [sub_zero] using (hν.mul (hp₀.sub hNinv)).congr (fun n => by
      dsimp only [b]
      rw [ladder_reverseMean]
      change ν n * (p₀ n - (N n)⁻¹) = ν n * (N n * p₀ n - 1) / N n
      field_simp [(hNpos n).ne'])
  let D := fun n => (ν n) ^ 2 * p₀ n * (1 - pLast n)
  let d := a ^ 2 * tiltDeficit β a
  have hc : 0 < tiltDeficit β a := tiltDeficit_pos hβ ha
  have hd : 0 < d := mul_pos (pow_pos ha 2) hc
  have hD : Tendsto D atTop (𝓝 d) := by
    simpa only [sub_zero, mul_one, d, D] using
      ((hν.pow 2).mul hp₀).mul (hone.sub hpLast)
  have hDv : ∀ᶠ n in atTop, v n = (N n) ^ 2 * r n ^ (n + 1) * D n := by
    filter_upwards [hmean] with n hn
    dsimp only [v]
    rw [ladder_variance β n (ν n) a hn]
    change (N n * ν n) ^ 2 * pLast n * (1 - pLast n) = _
    dsimp only [D]
    rw [hpLast_formula n]
    ring
  have hvpos : ∀ᶠ n in atTop, 0 < v n := by
    filter_upwards [hDv, hD.eventually_const_lt hd] with n hn hdₙ
    rw [hn]
    exact mul_pos (mul_pos (pow_pos (hNpos n) 2) (pow_pos (Real.exp_pos _) _)) hdₙ
  have hlogN : Tendsto (fun n => Real.log (N n) / N n) atTop (𝓝 0) := by
    have hlim := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_size
    exact hlim.congr (fun n => by simp [N])
  have hlogD : Tendsto (fun n => Real.log (D n) / N n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      ((Real.continuousAt_log hd.ne').tendsto.comp hD).mul hNinv
  have hlinear : Tendsto (fun n => (1 - (N n)⁻¹) * (-β * ν n)) atTop (𝓝 (-β * a)) := by
    simpa only [sub_zero, one_mul] using
      (hone.sub hNinv).mul (hν.const_mul (-β))
  have hv : Tendsto (fun n => Real.log (v n) / N n) atTop (𝓝 (-β * a)) := by
    refine (show Tendsto (fun n => 2 * (Real.log (N n) / N n) +
        (1 - (N n)⁻¹) * (-β * ν n) + Real.log (D n) / N n) atTop (𝓝 (-β * a)) by
      simpa only [mul_zero, zero_add, add_zero] using ((hlogN.const_mul 2).add hlinear).add hlogD).congr' ?_
    filter_upwards [hDv, hD.eventually_const_lt hd] with n hnv hnD
    rw [hnv, Real.log_mul (mul_ne_zero (pow_ne_zero _ (hNpos n).ne')
      (pow_ne_zero _ (Real.exp_ne_zero _))) hnD.ne',
      Real.log_mul (pow_ne_zero _ (hNpos n).ne') (pow_ne_zero _ (Real.exp_ne_zero _)),
      Real.log_pow, Real.log_pow]
    rw [show Real.log (r n) = -β * ν n from Real.log_exp _]
    push_cast
    field_simp [(hNpos n).ne']
    dsimp only [N]
    ring
  refine ⟨hvpos, hb, hv, ?_, ?_⟩
  · have hlim := hb.pos_mul_atTop (mul_pos ha hc) tendsto_size
    exact hlim.congr (fun n => div_mul_cancel₀ (b n) (hNpos n).ne')
  · have hlim := hv.div hb (mul_pos ha hc).ne'
    have hval : (-β * a) / (a * tiltDeficit β a) = -β / tiltDeficit β a := by
      field_simp [ha.ne', hc.ne']
    rw [hval] at hlim
    exact hlim.congr (fun n => div_div_div_cancel_right₀ (hNpos n).ne' _ _)


private theorem tendsto_floor_log (A s C : ℝ) (hA : 0 < A) :
    Tendsto (fun B : ℝ => Real.log (A * Real.exp (s * (B + C))) / B) atTop (𝓝 s) := by
  have h₀ : Tendsto (fun B : ℝ => B⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hs : Tendsto (fun _ : ℝ => s) atTop (𝓝 s) := tendsto_const_nhds
  have hlim : Tendsto (fun B : ℝ => s + (Real.log A + s * C) * B⁻¹) atTop (𝓝 s) := by
    simpa only [mul_zero, add_zero] using hs.add
      (h₀.const_mul (Real.log A + s * C))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  rw [Real.log_mul hA.ne' (Real.exp_ne_zero _), Real.log_exp]
  field_simp [hB.ne']
  ring

/-- Every slope strictly below the Gibbs exponent eventually bounds all finite laws. -/
private theorem eventually_log_variance_lower {β a L : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hL : L < -β / tiltDeficit β a) :
    ∃ B₀ : ℝ, ∀ B ≥ B₀, ∀ {ι : Type*} [Fintype ι] (p X : ι → ℝ),
      (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 → (∑ i, reverseWeight β p X i) = 1 →
      reverseMean β p X ≤ B →
      0 < forwardVariance p X a ∧ L < Real.log (forwardVariance p X a) / B := by
  let t := fun n : ℕ => ((n : ℝ) + 2)⁻¹
  have ht : Tendsto t atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_size
  have hc := tiltDeficit_pos hβ ha
  have hdef : Continuous (tiltDeficit β) := by unfold tiltDeficit; fun_prop
  have ha_lim : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
  have htdef : Tendsto (fun n => tiltDeficit β (a - a * t n)) atTop (𝓝 (tiltDeficit β a)) :=
    hdef.continuousAt.tendsto.comp (by
      simpa only [mul_zero, sub_zero] using ha_lim.sub (ht.const_mul a))
  have hrate : Tendsto (fun n => -β * (1 + t n) / tiltDeficit β (a - a * t n))
      atTop (𝓝 (-β / tiltDeficit β a)) := by
    have hlim := ((ht.const_add 1).const_mul (-β)).div htdef hc.ne'
    rw [add_zero, mul_one] at hlim
    exact hlim.congr (fun _ => rfl)
  obtain ⟨n, hn⟩ := (hrate.eventually_const_lt hL).exists
  let δ := a * t n
  let γ := t n
  have hγ : 0 < γ := by dsimp [γ, t]; positivity
  have hδ : 0 < δ := mul_pos ha hγ
  have ht₁ : t n < 1 := by
    dsimp [t]
    rw [inv_lt_one₀ (by positivity)]
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hδa : δ < a := by simpa only [mul_one] using mul_lt_mul_of_pos_left ht₁ ha
  let c := tiltDeficit β (a - δ)
  let A := δ ^ 2 * (c * γ / (1 + γ))
  let s := -β * (1 + γ) / c
  let C := 1 / (Real.exp 1 * β)
  have hca : 0 < c := tiltDeficit_pos hβ (sub_pos.mpr hδa)
  have hA : 0 < A := mul_pos (pow_pos hδ 2) (div_pos (mul_pos hca hγ) (by positivity))
  have hLs : L < s := hn
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp
    (((tendsto_floor_log A s C hA).eventually_const_lt hLs).and
      (eventually_gt_atTop (0 : ℝ)))
  refine ⟨B₀, fun B hB ι _ p X hp hp_mass hq_mass hbudget => ?_⟩
  obtain ⟨hlog, hBpos⟩ := hB₀ B hB
  have hform : A * Real.exp (s * (B + C)) =
      δ ^ 2 * Real.exp (-β * ((1 + γ) * (B + C) / c)) * (c * γ / (1 + γ)) := by
    have he : s * (B + C) = -β * ((1 + γ) * (B + C) / c) := by
      dsimp only [s]
      ring
    rw [he]
    dsimp only [A]
    ring
  have hfloor := (variance_exponential_floor p X hβ hBpos.le hδ hδa hγ hp hp_mass
    hq_mass hbudget).2
  rw [hform] at hlog
  have hpositive : 0 <
      δ ^ 2 * Real.exp (-β * ((1 + γ) * (B + C) / c)) * (c * γ / (1 + γ)) :=
    mul_pos (mul_pos (pow_pos hδ 2) (Real.exp_pos _))
      (div_pos (mul_pos hca hγ) (by positivity))
  exact ⟨hpositive.trans_le hfloor, hlog.trans_le
    (div_le_div_of_nonneg_right (Real.log_le_log hpositive hfloor) hBpos.le)⟩

/-- Every slope strictly above the sharp exponent is achieved by a calibrated
Gibbs ladder at every sufficiently large real budget. -/
private theorem eventually_gibbs_log_variance_upper {β a U : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hU : -β / tiltDeficit β a < U) :
    ∃ B₀ : ℝ, ∀ B ≥ B₀, ∃ (n : ℕ) (ν : ℝ), 0 < ν ∧
      (∑ i, ladderWeight β n ν i * forwardChange ν i) = a ∧
      reverseMean β (ladderWeight β n ν) (forwardChange ν) ≤ B ∧
      0 < forwardVariance (ladderWeight β n ν) (forwardChange ν) a ∧
      Real.log (forwardVariance (ladderWeight β n ν) (forwardChange ν) a) / B < U := by
  obtain ⟨ν, hνI, _, hmean, hvpos, hb, hv, _, _⟩ := exists_calibrated_gibbs_rate hβ ha
  let c := a * tiltDeficit β a
  have hc : 0 < c := mul_pos ha (tiltDeficit_pos hβ ha)
  have he : (-β * a) / c = -β / tiltDeficit β a := by
    dsimp only [c]
    field_simp [ha.ne', (tiltDeficit_pos hβ ha).ne']
  let t := fun k : ℕ => ((k : ℝ) + 2)⁻¹
  have ht : Tendsto t atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_size
  have hslope : Tendsto (fun k => (-β * a) / (c + t k)) atTop (𝓝 ((-β * a) / c)) := by
    have hnum : Tendsto (fun _ : ℕ => -β * a) atTop (𝓝 (-β * a)) := tendsto_const_nhds
    have hlim := hnum.div (ht.const_add c) (show c + 0 ≠ 0 by simpa using hc.ne')
    rw [add_zero] at hlim
    exact hlim.congr (fun _ => rfl)
  obtain ⟨k, hk⟩ := (hslope.eventually_lt_const (he ▸ hU)).exists
  let d := c + t k
  have hgap : c < d := lt_add_of_pos_right _ (by dsimp [t]; positivity)
  have hd : 0 < d := hc.trans hgap
  let m := fun B : ℝ => ⌊B / d⌋₊
  have hdiv : Tendsto (fun B : ℝ => B / d) atTop atTop := tendsto_id.atTop_div_const hd
  have hm : Tendsto m atTop atTop := tendsto_nat_floor_atTop.comp hdiv
  have hmdiv :
      Tendsto (fun B : ℝ => ((m B : ℝ) + 2) / B) atTop (𝓝 (1 / d)) := by
    have hf := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hdiv
    have h₂ : Tendsto (fun B : ℝ => 2 * B⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_inv_atTop_zero : Tendsto (fun B : ℝ => B⁻¹) atTop
        (𝓝 0)).const_mul 2
    have hsum := (hf.div_const d).add h₂
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    change (m B : ℝ) / (B / d) / d + 2 * B⁻¹ = ((m B : ℝ) + 2) / B
    field_simp [hB.ne', hd.ne']
  have hsizeB (B : ℝ) : ((m B : ℝ) + 2) ≠ 0 := by positivity
  let b := fun n => reverseMean β (ladderWeight β n (ν n)) (forwardChange (ν n))
  let v := fun n => forwardVariance (ladderWeight β n (ν n)) (forwardChange (ν n)) a
  have hbB : Tendsto (fun B => b (m B) / B) atTop (𝓝 (c / d)) := by
    have h := (hb.comp hm).mul hmdiv
    rw [mul_one_div] at h
    refine h.congr (fun B => ?_)
    change b (m B) / ((m B : ℝ) + 2) * (((m B : ℝ) + 2) / B) = _
    rw [← mul_div_assoc, div_mul_cancel₀ _ (hsizeB B)]
  have hvB : Tendsto (fun B => Real.log (v (m B)) / B) atTop (𝓝 ((-β * a) / d)) := by
    have h := (hv.comp hm).mul hmdiv
    rw [mul_one_div] at h
    refine h.congr (fun B => ?_)
    change Real.log (v (m B)) / ((m B : ℝ) + 2) * (((m B : ℝ) + 2) / B) = _
    rw [← mul_div_assoc, div_mul_cancel₀ _ (hsizeB B)]
  have hbudget := hbB.eventually_lt_const ((div_lt_one hd).mpr hgap)
  have hupper := hvB.eventually_lt_const (show (-β * a) / d < U from hk)
  have hgood := (hm.eventually hmean).and
    ((hm.eventually hvpos).and (hbudget.and (hupper.and (eventually_gt_atTop (0 : ℝ)))))
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hgood
  refine ⟨B₀, fun B hB => ?_⟩
  obtain ⟨hμ, hv₀, hbB₀, hvU, hBpos⟩ := hB₀ B hB
  exact ⟨m B, ν (m B), (half_pos ha).trans_le (hνI (m B)).1, hμ,
    ((div_lt_one hBpos).mp hbB₀).le, hv₀, hvU⟩

/-- Variances of finite reflected-tilt laws of forward mean `a` and reverse mean at most `B`. -/
def finiteVariances (β a B : ℝ) : Set ℝ :=
  {v | ∃ (n : ℕ) (p X : Fin n → ℝ),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∑ i, reverseWeight β p X i) = 1 ∧
    (∑ i, p i * X i) = a ∧ reverseMean β p X ≤ B ∧ v = forwardVariance p X a}

/-- Variances of the cyclic Gibbs ladders satisfying the same mean and budget constraints. -/
def gibbsVariances (β a B : ℝ) : Set ℝ :=
  {v | ∃ (n : ℕ) (ν : ℝ), 0 < ν ∧
    (∑ i, ladderWeight β n ν i * forwardChange ν i) = a ∧
    (∑ j, ladderWeight β n ν j *
      (ladderEnergy ν ((finRotate (n + 2)).symm j) - ladderEnergy ν j)) ≤ B ∧
    v = forwardVariance (ladderWeight β n ν) (forwardChange ν) a}

private theorem gibbsVariances_subset_finite (β a B : ℝ) :
    gibbsVariances β a B ⊆ finiteVariances β a B := by
  rintro v ⟨n, ν, _, hmean, hb, rfl⟩
  exact ⟨n + 2, ladderWeight β n ν, forwardChange ν, fun i => (gibbsWeight_pos β _ i).le,
    sum_gibbsWeight β _, ladder_reverse_mass β n ν, hmean, by
      rw [ladder_reverseMean_inverse]
      exact hb, rfl⟩

/-- The optimal finite-law logarithmic rate holds for every class containing the
cyclic Gibbs ladders and contained in the finite reflected-tilt laws. -/
theorem tendsto_log_inf_variance {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (V : ℝ → Set ℝ) (hg : ∀ B, gibbsVariances β a B ⊆ V B)
    (hf : ∀ B, V B ⊆ finiteVariances β a B) :
    Tendsto (fun B => Real.log (sInf (V B)) / B) atTop (𝓝 (-β / tiltDeficit β a)) := by
  let rate := -β / tiltDeficit β a
  have hlower (L : ℝ) (hL : L < rate) :
      ∀ᶠ B in atTop, 0 < B ∧ ∀ v ∈ V B, Real.exp (L * B) ≤ v := by
    obtain ⟨B₀, hB₀⟩ := eventually_log_variance_lower hβ ha hL
    filter_upwards [eventually_ge_atTop B₀, eventually_gt_atTop (0 : ℝ)] with B hB hBp
    refine ⟨hBp, fun v hv => ?_⟩
    obtain ⟨n, p, X, hp, hp_mass, hq_mass, _, hb, rfl⟩ := hf B hv
    obtain ⟨hvpos, hlog⟩ := hB₀ B hB p X hp hp_mass hq_mass hb
    have hexp := Real.exp_lt_exp.mpr ((lt_div_iff₀ hBp).mp hlog)
    rw [Real.exp_log hvpos] at hexp
    exact hexp.le
  have hupper (U : ℝ) (hU : rate < U) :
      ∀ᶠ B in atTop, ∃ v ∈ V B, 0 < v ∧ Real.log v / B < U := by
    obtain ⟨B₀, hB₀⟩ := eventually_gibbs_log_variance_upper hβ ha hU
    filter_upwards [eventually_ge_atTop B₀] with B hB
    obtain ⟨n, ν, hν, hmean, hb, hv, hlog⟩ := hB₀ B hB
    exact ⟨_, hg B ⟨n, ν, hν, hmean, (ladder_reverseMean_inverse β n ν ▸ hb), rfl⟩, hv, hlog⟩
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro L hL
    obtain ⟨s, hLs, hs⟩ := exists_between hL
    filter_upwards [hlower s hs, hupper (rate + 1) (lt_add_one rate)] with B hl hu
    obtain ⟨hB, hl⟩ := hl
    obtain ⟨v, hv, _, _⟩ := hu
    have hfloor := le_csInf ⟨v, hv⟩ hl
    have hlog := Real.log_le_log (Real.exp_pos _) hfloor
    rw [Real.log_exp] at hlog
    exact hLs.trans_le ((le_div_iff₀ hB).mpr hlog)
  · intro U hU
    filter_upwards [hlower (rate - 1) (sub_one_lt rate), hupper U hU] with B hl hu
    obtain ⟨hB, hl⟩ := hl
    obtain ⟨v, hv, _, hlog⟩ := hu
    have hBdd : BddBelow (V B) := ⟨_, hl⟩
    have hpos := (Real.exp_pos _).trans_le (le_csInf ⟨v, hv⟩ hl)
    exact (div_le_div_of_nonneg_right (Real.log_le_log hpos (csInf_le hBdd hv)) hB.le).trans_lt hlog

end

#print axioms variance_lower_bound
#print axioms exists_calibrated_gibbs_rate
#print axioms tendsto_log_inf_variance

end GibbsLadderReverseBudget
