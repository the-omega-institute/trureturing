/- GID: D5/S3/Weil/RightStripInverseHeight
   generality: I
   mirror-B: D5/B/S3/Weil/RightStripInverseHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A dyadic power saving sums reciprocal heights of actual right-strip zeros. -/

import D5.S3.Weil.MollifiedZeroCount
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Partition the actual right-strip zeros into a finite low band and dyadic height bands. -/

open Set

noncomputable section

namespace Zeta23

private def rightZeros (σ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ σ < ρ.re}

private def heightShell (σ : ℝ) : ℕ → Set (rightZeros σ)
  | 0 => {ρ | |(ρ : ℂ).im| ≤ 2}
  | n + 1 => {ρ | (2 : ℝ) ^ (n + 1) < |(ρ : ℂ).im| ∧
      |(ρ : ℂ).im| ≤ (2 : ℝ) ^ (n + 2)}

private theorem heightShell_partition (σ : ℝ) (ρ : rightZeros σ) :
    ∃! k, ρ ∈ heightShell σ k := by
  classical
  have hex : ∃ k : ℕ, |(ρ : ℂ).im| ≤ (2 : ℝ) ^ (k + 1) := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt |(ρ : ℂ).im| (show (1 : ℝ) < 2 by norm_num)
    exact ⟨k, hk.le.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k))⟩
  have hupper {k : ℕ} (hk : ρ ∈ heightShell σ k) :
      |(ρ : ℂ).im| ≤ (2 : ℝ) ^ (k + 1) := by
    cases k with
    | zero => simpa [heightShell] using hk
    | succ k => exact hk.2
  refine ⟨Nat.find hex, ?_, fun k hk => ?_⟩
  · have hb := Nat.find_spec hex
    cases hk : Nat.find hex with
    | zero => simpa [heightShell, hk] using hb
    | succ k =>
      rw [hk] at hb
      have hmin := Nat.find_min hex (show k < Nat.find hex by rw [hk]; exact Nat.lt_succ_self k)
      exact ⟨lt_of_not_ge hmin, hb⟩
  · have hmin := Nat.find_min' hex (hupper hk)
    apply le_antisymm _ hmin
    by_contra! hlt
    cases k with
    | zero => omega
    | succ k =>
      have hs : Nat.find hex + 1 ≤ k + 1 := hlt
      exact hk.1.not_ge ((Nat.find_spec hex).trans (pow_le_pow_right₀ (by norm_num) hs))

private theorem heightShell_finite (σ : ℝ) (k : ℕ) : (heightShell σ k).Finite := by
  let B : ℝ := (2 : ℝ) ^ (k + 1)
  apply ((zerosIn_finite (-(B + 1)) B).preimage Subtype.val_injective.injOn).subset
  intro ρ hρ
  have hb : |(ρ : ℂ).im| ≤ B := by
    cases k with
    | zero => simpa [heightShell, B] using hρ
    | succ _ => exact hρ.2
  exact ⟨ρ.property.1, by linarith [neg_abs_le (ρ : ℂ).im],
    (le_abs_self (ρ : ℂ).im).trans hb⟩

/-- A dyadic power saving for the multiplicity-weighted right-strip counts implies
summability of the reciprocal heights of those zeros, with multiplicity. -/
theorem summable_rightStrip_inverse_height_of_dyadic_count {σ C η : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η)
    (hcount : ∀ T : ℝ, 2 ≤ T →
      (rightStripDyadicCount σ T : ℝ) ≤ C * T ^ (1 - η)) :
    Summable (fun ρ : {ρ : ℂ // IsNontrivialZero ρ ∧ σ < ρ.re} =>
      (zeroMult ρ : ℝ) / |(ρ : ℂ).im|) := by
  classical
  let f : rightZeros σ → ℝ := fun ρ => (zeroMult ρ : ℝ) / |(ρ : ℂ).im|
  have hf : 0 ≤ f := fun ρ => div_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  change Summable f
  rw [summable_partition hf (heightShell_partition σ)]
  constructor
  · intro k
    letI : Fintype (heightShell σ k) := (heightShell_finite σ k).fintype
    exact Summable.of_finite
  · apply (summable_nat_add_iff 1).mp
    let q : ℝ := (2 : ℝ) ^ (-η)
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hη)
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun ρ => hf ρ)
      (fun k => ?_) ((summable_geometric_of_lt_one hq0 hq1).mul_left (C * q))
    let T : ℝ := (2 : ℝ) ^ (k + 1)
    have hT : 2 ≤ T := by
      simpa [T] using (pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num)
        (show (1 : ℕ) ≤ k + 1 by omega))
    have hT0 : 0 < T := by linarith
    let s := heightShell_finite σ (k + 1)
    let S := rightStripDyadicZeros_finite σ T
    letI := s.fintype
    let ι : heightShell σ (k + 1) ↪ ℂ :=
      ⟨fun ρ => ρ.val.val, Subtype.val_injective.comp Subtype.val_injective⟩
    have hmem (ρ : heightShell σ (k + 1)) : ι ρ ∈ rightStripDyadicZeros σ T := by
      have hρ := ρ.property
      change T < |(ρ.val : ℂ).im| ∧ |(ρ.val : ℂ).im| ≤ (2 : ℝ) ^ (k + 2) at hρ
      refine ⟨ρ.val.property.1, ρ.val.property.2, hρ.1, ?_⟩
      change |(ρ.val : ℂ).im| ≤ 2 * T
      simpa [T, pow_succ, mul_comm] using hρ.2
    have hsum : (∑ ρ : heightShell σ (k + 1), (zeroMult (ι ρ) : ℝ)) ≤
        (rightStripDyadicCount σ T : ℝ) := by
      rw [← Finset.sum_map Finset.univ ι (fun ρ : ℂ => (zeroMult ρ : ℝ))]
      rw [rightStripDyadicCount, finsum_mem_eq_finite_toFinset_sum _ S, Nat.cast_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ρ hρ
        obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hρ
        exact S.mem_toFinset.mpr (hmem p)
      · exact fun _ _ _ => Nat.cast_nonneg _
    calc
      (∑' ρ : heightShell σ (k + 1), f ρ) =
          ∑ ρ : heightShell σ (k + 1), f ρ := tsum_fintype _
      _ ≤ ∑ ρ : heightShell σ (k + 1), (zeroMult (ι ρ) : ℝ) / T := by
        exact Finset.sum_le_sum fun ρ _ =>
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hT0 (hmem ρ).2.2.1.le
      _ = (∑ ρ : heightShell σ (k + 1), (zeroMult (ι ρ) : ℝ)) / T := by
        rw [Finset.sum_div]
      _ ≤ (C * T ^ (1 - η)) / T :=
        div_le_div_of_nonneg_right (hsum.trans (hcount T hT)) hT0.le
      _ = (C * q) * q ^ k := by
        rw [mul_div_assoc, ← Real.rpow_sub_one hT0.ne', show 1 - η - 1 = -η by ring]
        rw [show T ^ (-η) = q ^ (k + 1) by
          simp only [T, q, ← Real.rpow_natCast_mul (show (0 : ℝ) ≤ 2 by norm_num),
            ← Real.rpow_mul_natCast (show (0 : ℝ) ≤ 2 by norm_num), mul_comm]]
        rw [pow_succ]
        ring

end Zeta23
