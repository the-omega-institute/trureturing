/- GID: D5/S3/TotalVariation/ParryResetLaw
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryResetLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual geometric root and stationary signed Parry reset chain. -/

import D5.S3.TotalVariation.TwistedResetPaths
import D5.S0.Tower.DBonacci.PerronRoot

open scoped BigOperators
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S0.Tower.DBonacci.PerronRoot
namespace D5.S3.TotalVariation.ParryResetLaw

/-- The geometric polynomial whose level one selects the reciprocal spectral root. -/
noncomputable def rootSum (k : ℕ) (p : ℝ) : ℝ :=
  ∑ a ∈ Finset.range k, p ^ (a + 1)

/-- The actual reciprocal Parry root; the unused small carriers have a fixed default. -/
noncomputable def parryParameter (k : ℕ) : ℝ :=
  if 2 ≤ k then (dbonacciPerronRoot k)⁻¹ else 1 / 2

/-- Normalizing sum of the left and right eigenvector products. -/
noncomputable def normalizer (k : ℕ) : ℝ :=
  ∑ j : Fin k, parryParameter k ^ j.val * suffixWeight k (parryParameter k) j

/-- The actual stationary signed mass, with a fair absolute sign. -/
noncomputable def parryLaw (k : ℕ) (s : State k) : ℝ :=
  parryParameter k ^ s.2.val * suffixWeight k (parryParameter k) s.2 / (2 * normalizer k)


/-- The selected source parameter makes the actual reset kernel stochastic and the
explicit eigenvector-product law stationary. All suffix weights have uniform bounds. -/
theorem parry_stationary_law (k : ℕ) (hk : 2 ≤ k) :
    let p := parryParameter k
    (1 / 2 < p ∧ p ≤ Real.goldenRatio⁻¹ ∧ rootSum k p = 1) ∧
    (∀ j, p ≤ suffixWeight k p j ∧ suffixWeight k p j ≤ 1) ∧
    1 ≤ normalizer k ∧
    (∀ s t, 0 ≤ kernel k p s t) ∧
    (∀ s, ∑ t, kernel k p s t = 1) ∧
    (∀ s, 0 ≤ parryLaw k s) ∧
    (∑ s, parryLaw k s) = 1 ∧
    (∀ t, ∑ s, parryLaw k s * kernel k p s t = parryLaw k t) ∧
    (∀ s, parryLaw k (flip s) = parryLaw k s) := by
  classical
  let p := parryParameter k
  let z : Fin k := ⟨0, by omega⟩
  have hsel : p = (dbonacciPerronRoot k)⁻¹ := by
    simp [p, parryParameter, hk]
  have hspec := dbonacciPerronRoot_spec k hk
  have hβpos : 0 < dbonacciPerronRoot k := lt_trans zero_lt_one hspec.1
  have hlo : 1 / 2 < p := by
    rw [hsel]
    simpa only [one_div] using (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) hβpos).2
      hspec.2.1
  have hgolden : Real.goldenRatio ≤ dbonacciPerronRoot k := by
    rw [← dbonacciPerronRoot_two_eq_goldenRatio]
    exact dbonacciPerronRoot_strictMonoOn.monotoneOn (by simp) hk hk
  have hhi : p ≤ Real.goldenRatio⁻¹ := by
    rw [hsel]
    exact (inv_le_inv₀ hβpos Real.goldenRatio_pos).2 hgolden
  have hp : 0 < p := by linarith [hlo]
  have hroot : rootSum k p = 1 := by
    simpa only [rootSum, hsel, dbonacciReciprocalSum] using
      dbonacciPerronRoot_reciprocalSum k hk
  have hzero : suffixWeight k p z = 1 := by simpa [suffixWeight, z, rootSum] using hroot
  have hb (j : Fin k) : p ≤ suffixWeight k p j ∧ suffixWeight k p j ≤ 1 := by
    constructor
    · unfold suffixWeight
      simpa using Finset.single_le_sum (fun a _ => pow_nonneg hp.le (a + 1))
        (Finset.mem_range.mpr (by have := j.isLt; omega) : 0 ∈ Finset.range (k-j.val))
    · rw [← hroot]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le _ _))
        (fun a _ _ => pow_nonneg hp.le _)
  have hh (j : Fin k) : 0 < suffixWeight k p j := lt_of_lt_of_le hp (hb j).1
  have hrec (j : Fin k) (hj : j.val + 1 < k) :
      suffixWeight k p j = p + p * suffixWeight k p ⟨j.val+1,hj⟩ := by
    unfold suffixWeight
    rw [show k-j.val = (k-(j.val+1))+1 by omega, Finset.sum_range_succ']
    simp only [pow_one]
    simp_rw [pow_succ, ← Finset.sum_mul]
    ring
  have hlast (j : Fin k) (hj : ¬j.val+1<k) : suffixWeight k p j = p := by
    have hjk : k-j.val = 1 := by have := j.isLt; omega
    simp [suffixWeight, hjk]
  have hrow (s : State k) : ∑ t, kernel k p s t = 1 := by
    have hreset : (!s.1) ≠ s.1 := by cases s.1 <;> decide
    by_cases hs : s.2.val + 1 < k
    · let u : Fin k := ⟨s.2.val+1,hs⟩
      have hf (t : State k) : kernel k p s t =
          (if t = (!s.1,z) then p / suffixWeight k p s.2 else 0) +
          (if t = (s.1,u) then p * suffixWeight k p u / suffixWeight k p s.2 else 0) := by
        by_cases ht0 : t = (!s.1,z)
        · subst t
          simp [kernel, z, u, hreset]
        · by_cases ht1 : t = (s.1,u)
          · subst t
            simp [kernel, z, u, hreset, Ne.symm hreset]
          · have h0 : ¬(t.1 = !s.1 ∧ t.2.val = 0) := by
              simpa [Prod.ext_iff, Fin.ext_iff, z] using ht0
            have h1 : ¬(t.1 = s.1 ∧ t.2.val = s.2.val+1) := by
              simpa [Prod.ext_iff, Fin.ext_iff, u] using ht1
            simp [kernel, h0, h1, ht0, ht1]
      simp_rw [hf]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← add_div]
      exact (div_eq_one_iff_eq (hh s.2).ne').mpr (hrec s.2 hs).symm
    · have hf (t : State k) : kernel k p s t =
          if t = (!s.1,z) then p / suffixWeight k p s.2 else 0 := by
        have hn : t.2.val ≠ s.2.val+1 := by have := t.2.isLt; omega
        simp [kernel, Prod.ext_iff, Fin.ext_iff, z, hn]
      simp_rw [hf]
      simp [hlast s.2 hs, hp.ne']
  have hS : 1 ≤ normalizer k := by
    calc
      1 = p ^ z.val * suffixWeight k p z := by simp [z, hzero]
      _ ≤ normalizer k := Finset.single_le_sum
        (fun j _ => mul_nonneg (pow_nonneg hp.le _) (hh j).le) (Finset.mem_univ z)
  have hSpos : 0 < normalizer k := by linarith
  have hQ (s t : State k) : 0 ≤ kernel k p s t := by
    unfold kernel
    split_ifs
    · exact (div_pos hp (hh _)).le
    · exact (div_pos (mul_pos hp (hh _)) (hh _)).le
    · exact le_rfl
  have hπ (s : State k) : 0 ≤ parryLaw k s :=
    div_nonneg (mul_nonneg (pow_nonneg hp.le _) (hh _).le) (by positivity)
  have hπsum : (∑ s, parryLaw k s) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [parryLaw, ← Finset.sum_div]
    change (∑ _ : Bool, normalizer k) / (2 * normalizer k) = 1
    simp [hSpos.ne']
  have hstat (t : State k) : ∑ s, parryLaw k s * kernel k p s t = parryLaw k t := by
    by_cases ht : t.2.val = 0
    · have htz : t.2 = z := Fin.ext ht
      have hf (s : State k) : parryLaw k s * kernel k p s t =
          if s.1 = !t.1 then p ^ (s.2.val+1) / (2 * normalizer k) else 0 := by
        have hi : ¬ t.2.val = s.2.val+1 := by omega
        have he : t.1 = !s.1 ↔ s.1 = !t.1 := by cases t.1 <;> cases s.1 <;> decide
        simp only [kernel, ht, he, Nat.zero_ne_add_one, and_true, and_false, if_false]
        split_ifs
        · dsimp [parryLaw]
          change p ^ s.2.val * suffixWeight k p s.2 / (2 * normalizer k) *
            (p / suffixWeight k p s.2) = _
          rw [pow_succ]
          field_simp [(hh s.2).ne']
        · simp
      simp_rw [hf]
      rw [Fintype.sum_prod_type]
      simp only [← Finset.sum_div]
      have hsump : (∑ j : Fin k, p^(j.val+1)) = 1 := by
        rw [Fin.sum_univ_eq_sum_range (fun j => p^(j+1))]
        exact hroot
      change (∑ a : Bool, ∑ j : Fin k,
        if a = !t.1 then p^(j.val+1)/(2*normalizer k) else 0) =
        p^t.2.val * suffixWeight k p t.2 / (2*normalizer k)
      rw [htz, hzero]
      cases htbool : t.1 <;> simp [z, ← Finset.sum_div, hsump]
    · let u : State k := (t.1, ⟨t.2.val-1, by have := t.2.isLt; omega⟩)
      have hu : u.2.val+1 = t.2.val := by dsimp [u]; omega
      have hf (s : State k) (hs : s ≠ u) : parryLaw k s * kernel k p s t = 0 := by
        have hn : ¬ (t.1 = s.1 ∧ t.2.val = s.2.val+1) := by
          rintro ⟨ha,hj⟩
          apply hs
          apply Prod.ext
          · exact ha.symm
          apply Fin.ext
          dsimp [u]
          omega
        simp [kernel, ht, hn]
      rw [Finset.sum_eq_single u]
      · have he : t.1 ≠ !u.1 := by dsimp [u]; cases t.1 <;> decide
        simp only [kernel, he, false_and, ht, and_false, if_false]
        have he2 : t.1 = u.1 ∧ t.2.val = u.2.val+1 := ⟨rfl,hu.symm⟩
        rw [if_pos he2]
        dsimp [parryLaw]
        change p^u.2.val * suffixWeight k p u.2 / (2 * normalizer k) *
          (p * suffixWeight k p t.2 / suffixWeight k p u.2) =
          p^t.2.val * suffixWeight k p t.2 / (2 * normalizer k)
        rw [← hu, pow_succ]
        field_simp [(hh u.2).ne']
      · intro s _ hs
        exact hf s hs
      · simp
  exact ⟨⟨hlo, hhi, hroot⟩, hb, hS, hQ, hrow, hπ, hπsum, hstat, fun _ => rfl⟩

#print axioms parry_stationary_law
end D5.S3.TotalVariation.ParryResetLaw
