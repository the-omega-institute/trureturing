/- GID: D5/S3/Fourier/Concentration/ReducedDegreeCollisionBudgets
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/ReducedDegreeCollisionBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separation of low-degree residual pairs controls weighted collisions. -/

import D5.S3.Fourier.Concentration.LocalizedCollisionBudgets
import D5.S3.Fourier.Concentration.FiniteMultinomialOverlap

/-! Budgets obtained by cancelling the common counts of each pair. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations (pairRadius weightedPairBudget)
open D5.S3.Fourier.Concentration.LocalizedCollisionBudgets
open D5.S3.Fourier.Concentration.FiniteMultinomialOverlap (weighted_count_difference_sq_ge)
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
  (monomialFrequency monomialWeight diagonal)
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (monomialWeight_nonneg)
open scoped ENNReal

namespace D5.S3.Fourier.Concentration.ReducedDegreeCollisionBudgets

private theorem reducedDegree_ge_of_reachable {J : Type*} [Fintype J]
    (g radius : J → ℝ) (η : ℝ) (p k : ℕ)
    (hsep : ∀ (d : ℕ) (u v : J → ℕ), 0 < d → d < k → d ≤ p →
      (∑ j, u j) = d → (∑ j, v j) = d → (∀ j, min (u j) (v j) = 0) →
      η + ∑ j, ((u j : ℝ) + v j) * radius j <
        |monomialFrequency g u - monomialFrequency g v|)
    (m n : J → ℕ) (hm : (∑ j, m j) = p) (hn : (∑ j, n j) = p) (hne : m ≠ n)
    (hreach : |monomialFrequency g m - monomialFrequency g n| ≤
      η + ∑ j, |(m j : ℝ) - n j| * radius j) :
    k ≤ p - ∑ j, min (m j) (n j) := by
  let l (j : J) := min (m j) (n j)
  let u := m - l
  let v := n - l
  let d := p - ∑ j, l j
  have huadd (j : J) : u j + l j = m j := Nat.sub_add_cancel (min_le_left _ _)
  have hvadd (j : J) : v j + l j = n j := Nat.sub_add_cancel (min_le_right _ _)
  have hu : (∑ j, u j) = d :=
    (sum_tsub_distrib univ (fun j _ => min_le_left (m j) (n j))).trans (by rw [hm])
  have hv : (∑ j, v j) = d :=
    (sum_tsub_distrib univ (fun j _ => min_le_right (m j) (n j))).trans (by rw [hn])
  have hd : 0 < d := by
    by_contra! h
    have hzero := Nat.eq_zero_of_le_zero h
    have hu0 := (sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le (u j))).mp (hu.trans hzero)
    have hv0 := (sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le (v j))).mp (hv.trans hzero)
    apply hne
    ext j
    rw [← huadd j, ← hvadd j, hu0 j (mem_univ j), hv0 j (mem_univ j)]
  have hdiff (j : J) : (m j : ℝ) - n j = (u j : ℝ) - v j := by
    have huReal : (u j : ℝ) + l j = m j := by exact_mod_cast huadd j
    have hvReal : (v j : ℝ) + l j = n j := by exact_mod_cast hvadd j
    linarith
  have hdisjoint (j : J) : u j = 0 ∨ v j = 0 := by
    rcases le_total (m j) (n j) with h | h
    · exact Or.inl (by simp [u, l, min_eq_left h])
    · exact Or.inr (by simp [v, l, min_eq_right h])
  have habs (j : J) : |(m j : ℝ) - n j| = (u j : ℝ) + v j := by
    rw [hdiff]
    rcases hdisjoint j with h | h
    · simp [h, abs_of_nonneg (show (0 : ℝ) ≤ (v j : ℝ) from Nat.cast_nonneg _)]
    · simp [h, abs_of_nonneg (show (0 : ℝ) ≤ (u j : ℝ) from Nat.cast_nonneg _)]
  have hgap : monomialFrequency g m - monomialFrequency g n =
      monomialFrequency g u - monomialFrequency g v := by
    simp only [monomialFrequency, ← sum_sub_distrib, ← sub_mul, hdiff]
  by_contra! hdk
  have hmin (j : J) : min (u j) (v j) = 0 := by
    rcases hdisjoint j with h | h <;> simp [h]
  exact (not_lt_of_ge (by simpa only [hgap, habs] using hreach))
    (hsep d u v hd hdk (Nat.sub_le _ _) hu hv hmin)

/-- Reject pairs below the separation threshold and bound the remaining weighted budget. -/
theorem localized_excess_le_of_reduced_separation {J : Type*} [Fintype J] [DecidableEq J]
    (g w radius : J → ℝ) (hw : ∀ j, 0 ≤ w j) {ρ η : ℝ} (hρ : 0 < ρ)
    (hr : ∀ j, ρ ≤ radius j) (p k : ℕ) (hk : 0 < k)
    (hsep : 0 < η → ∀ (d : ℕ) (u v : J → ℕ), 0 < d → d < k → d ≤ p →
      (∑ j, u j) = d → (∑ j, v j) = d → (∀ j, min (u j) (v j) = 0) →
      η + ∑ j, ((u j : ℝ) + v j) * radius j <
        |monomialFrequency g u - monomialFrequency g v|) :
    (η ≤ 0 ∨ p < k → localizedExcessBound g w radius p η = 0) ∧
      localizedExcessBound g w radius p η ≤
        ENNReal.ofReal (((∑ j, w j) ^ (2 * p) - diagonal w p) *
          min (min 1 (η / ρ)) (Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * η /
            (ρ * Real.sqrt (2 * (k : ℝ))))) := by
  by_cases hηpos : 0 < η
  swap
  · have hη := le_of_not_gt hηpos
    have hzero : localizedExcessBound g w radius p η = 0 := by
      unfold localizedExcessBound weightedPairBudget
      refine sum_eq_zero fun m _ => sum_eq_zero fun n _ => ?_
      suffices hp : localizedPairBound g radius η m n = 0 by rw [hp, mul_zero]
      unfold localizedPairBound
      split_ifs
      · have hr' : 0 ≤ pairRadius radius m n := NNReal.coe_nonneg _
        rw [ENNReal.ofReal_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hη hr')]
        simp
      · rfl
    exact ⟨fun _ => hzero, hzero ▸ zero_le⟩
  have hη := hηpos.le
  let s := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  let C := Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * η
  let L := ρ * Real.sqrt (2 * (k : ℝ))
  let b := min (min 1 (η / ρ)) (C / L)
  have hL : 0 < L := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    dsimp [L]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : 0 ≤ b := le_min (le_min zero_le_one (div_nonneg hη hρ.le)) (div_nonneg hC hL.le)
  have hweight (m n : J → ℕ) : 0 ≤ c m * c n :=
    mul_nonneg (monomialWeight_nonneg w hw m) (monomialWeight_nonneg w hw n)
  have hpair (m n : J → ℕ) (hm : m ∈ s) (hn : n ∈ s.erase m) :
      (p < k → localizedPairBound g radius η m n = 0) ∧
        localizedPairBound g radius η m n ≤ ENNReal.ofReal b := by
    have hmp := (mem_piAntidiag.mp hm).1
    have hnp := (mem_piAntidiag.mp (mem_of_mem_erase hn)).1
    have hne := (ne_of_mem_erase hn).symm
    unfold localizedPairBound
    split_ifs with hreach
    · have hdegree :=
        reducedDegree_ge_of_reachable g radius η p k (hsep hηpos) m n hmp hnp
          hne hreach
      refine ⟨fun h => False.elim ((not_lt_of_ge (hdegree.trans (Nat.sub_le _ _))) h), ?_⟩
      have hl : (∑ j, min (m j) (n j)) ≤ p := by
        rw [← hmp]
        exact sum_le_sum fun j _ => min_le_left _ _
      have hkSum : k + (∑ j, min (m j) (n j)) ≤ p := by omega
      have hkReal : (k : ℝ) + ∑ j, (min (m j) (n j) : ℝ) ≤ p := by exact_mod_cast hkSum
      have hscale : L ≤ Real.sqrt (∑ j, (((m j : ℝ) - n j) * radius j) ^ 2) := by
        dsimp [L]
        rw [← Real.sqrt_sq hρ.le, ← Real.sqrt_mul (sq_nonneg ρ)]
        apply Real.sqrt_le_sqrt
        refine le_trans ?_ (weighted_count_difference_sq_ge radius hρ.le hr m n p hmp hnp)
        calc
          _ = (2 * ρ ^ 2) * k := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hradius : ρ ≤ pairRadius radius m n := by
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
        have hdiff : 1 ≤ |(m j : ℝ) - n j| := by
          rcases lt_or_gt_of_ne hj with h | h
          · have hReal : (m j : ℝ) + 1 ≤ n j := by exact_mod_cast Nat.succ_le_of_lt h
            rw [abs_of_nonpos (by linarith)]
            linarith
          · have hReal : (n j : ℝ) + 1 ≤ m j := by exact_mod_cast Nat.succ_le_of_lt h
            rw [abs_of_nonneg (by linarith)]
            linarith
        have hrj := hρ.le.trans (hr j)
        calc
          ρ ≤ |(m j : ℝ) - n j| * radius j :=
            (hr j).trans (le_mul_of_one_le_left hrj hdiff)
          _ ≤ pairRadius radius m n := by
            unfold pairRadius
            rw [← Real.coe_toNNReal _ (mul_nonneg (abs_nonneg _) hrj)]
            exact NNReal.coe_le_coe.mpr (Finset.le_sup
              (f := fun i => (|(m i : ℝ) - n i| * radius i).toNNReal) (mem_univ j))
      change min (min 1 (ENNReal.ofReal (η / pairRadius radius m n))) (ENNReal.ofReal
        (C / Real.sqrt (∑ j, (((m j : ℝ) - n j) * radius j) ^ 2))) ≤ ENNReal.ofReal b
      rw [show ENNReal.ofReal b = min (min 1 (ENNReal.ofReal (η / ρ))) (ENNReal.ofReal (C / L)) by
        simp [b, ENNReal.ofReal_min]]
      refine le_min (le_min ((min_le_left _ _).trans (min_le_left _ _)) ?_) ?_
      · exact ((min_le_left _ _).trans (min_le_right _ _)).trans
          (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hη hρ hradius))
      · exact (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_left hC hL hscale))
    · exact ⟨fun _ => rfl, zero_le⟩
  constructor
  · intro hwindow
    have hpk := hwindow.resolve_left hηpos.not_ge
    unfold localizedExcessBound weightedPairBudget
    exact sum_eq_zero fun m hm => sum_eq_zero fun n hn => by
      rw [(hpair m n hm hn).1 hpk, mul_zero]
  · have hmass :
        (∑ m ∈ s, ∑ n ∈ s.erase m, c m * c n) = (∑ j, w j) ^ (2 * p) - diagonal w p := by
      have htotal : (∑ m ∈ s, ∑ n ∈ s, c m * c n) = (∑ j, w j) ^ (2 * p) := by
        simp_rw [← mul_sum, ← sum_mul]
        have hsum : (∑ m ∈ s, c m) = (∑ j, w j) ^ p :=
          (sum_pow_eq_sum_piAntidiag univ w p).symm
        rw [hsum, pow_mul, pow_two]
        ring
      change _ = (∑ j, w j) ^ (2 * p) - ∑ m ∈ s, c m ^ 2
      rw [← htotal, ← sum_sub_distrib]
      refine sum_congr rfl fun m hm => ?_
      rw [sum_erase_eq_sub hm, pow_two]
    calc
      _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m, ENNReal.ofReal (c m * c n * b) := by
        unfold localizedExcessBound weightedPairBudget
        refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
        rw [ENNReal.ofReal_mul (hweight m n)]
        exact mul_le_mul_right (hpair m n hm hn).2 _
      _ = ENNReal.ofReal ((∑ m ∈ s, ∑ n ∈ s.erase m, c m * c n) * b) := by
        simp_rw [sum_mul]
        rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => sum_nonneg (fun n _ =>
          mul_nonneg (hweight m n) hb))]
        exact sum_congr rfl fun m _ => (ENNReal.ofReal_sum_of_nonneg
          (fun n _ => mul_nonneg (hweight m n) hb)).symm
      _ = _ := by rw [hmass]

#print axioms localized_excess_le_of_reduced_separation

end D5.S3.Fourier.Concentration.ReducedDegreeCollisionBudgets
