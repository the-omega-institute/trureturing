/- GID: D5/S3/Fourier/Concentration/FiniteMultinomialOverlap
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FiniteMultinomialOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common coordinates of two degree vectors are controlled by a lower-degree diagonal. -/

import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

/-! Weighted multinomial overlap is bounded by a lower-degree diagonal. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight diagonal)
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (monomialWeight_nonneg)

namespace D5.S3.Fourier.Concentration.FiniteMultinomialOverlap

def subvectorMultiplicity {J : Type*} [Fintype J] (m l : J → ℕ) : ℝ :=
  ∏ j, (Nat.choose (m j) (l j) : ℝ)

theorem subvectorMultiplicity_mul_monomialWeight {J : Type*} [Fintype J]
    (w : J → ℝ) (l u : J → ℕ) :
    subvectorMultiplicity (l + u) l * monomialWeight w (l + u) =
      (Nat.choose ((∑ j, l j) + ∑ j, u j) (∑ j, l j) : ℝ) *
        monomialWeight w l * monomialWeight w u := by
  let B := ∏ j, (l j).factorial
  let C := ∏ j, (u j).factorial
  let D := ∏ j, ((l + u) j).factorial
  let M := ∏ j, Nat.choose ((l + u) j) (l j)
  let N := Nat.choose ((∑ j, l j) + ∑ j, u j) (∑ j, l j)
  have hfact : M * B * C = D := by
    dsimp [M, B, C, D]
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    simpa only [Nat.add_comm (u j) (l j), Nat.mul_assoc,
      Nat.mul_comm (u j).factorial (l j).factorial] using
      Nat.add_choose_mul_factorial_mul_factorial (u j) (l j)
  have hmul : M * Nat.multinomial univ (l + u) =
      N * Nat.multinomial univ l * Nat.multinomial univ u := by
    have hB : 0 < B := prod_pos (fun j _ => Nat.factorial_pos (l j))
    have hC : 0 < C := prod_pos (fun j _ => Nat.factorial_pos (u j))
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hB hC)
    have htotal : (∑ j, (l + u) j) = (∑ j, l j) + ∑ j, u j :=
      sum_add_distrib
    calc
      (B * C) * (M * Nat.multinomial univ (l + u)) =
          D * Nat.multinomial univ (l + u) := by rw [← hfact]; ac_rfl
      _ = ((∑ j, l j) + ∑ j, u j).factorial := by
        rw [show D * Nat.multinomial univ (l + u) = (∑ j, (l + u) j).factorial from
          Nat.multinomial_spec _ _, htotal]
      _ = N * (B * Nat.multinomial univ l) * (C * Nat.multinomial univ u) := by
        rw [show B * Nat.multinomial univ l = (∑ j, l j).factorial from
          Nat.multinomial_spec _ _,
          show C * Nat.multinomial univ u = (∑ j, u j).factorial from
          Nat.multinomial_spec _ _]
        dsimp [N]
        simpa only [Nat.add_comm (∑ j, u j) (∑ j, l j), Nat.mul_assoc,
          Nat.mul_comm (∑ j, u j).factorial (∑ j, l j).factorial] using
          (Nat.add_choose_mul_factorial_mul_factorial (∑ j, u j) (∑ j, l j)).symm
      _ = (B * C) * (N * Nat.multinomial univ l * Nat.multinomial univ u) := by ac_rfl
  have hcast : (M : ℝ) * (Nat.multinomial univ (l + u) : ℝ) =
      (N : ℝ) * (Nat.multinomial univ l : ℝ) * (Nat.multinomial univ u : ℝ) := by
    exact_mod_cast hmul
  have hprod : (∏ j, w j ^ (l + u) j) = (∏ j, w j ^ l j) * ∏ j, w j ^ u j := by
    simp only [Pi.add_apply, pow_add, prod_mul_distrib]
  unfold subvectorMultiplicity monomialWeight
  rw [hprod, ← Nat.cast_prod]
  change (M : ℝ) * ((Nat.multinomial univ (l + u) : ℝ) *
    ((∏ j, w j ^ l j) * ∏ j, w j ^ u j)) =
    (N : ℝ) * ((Nat.multinomial univ l : ℝ) * ∏ j, w j ^ l j) *
      ((Nat.multinomial univ u : ℝ) * ∏ j, w j ^ u j)
  rw [← mul_assoc, hcast]
  ring

private theorem sum_subvectorMultiplicity_mul_monomialWeight {J : Type*} [Fintype J]
    [DecidableEq J] (w : J → ℝ) (p k : ℕ) (hkp : k ≤ p) (l : J → ℕ)
    (hl : l ∈ piAntidiag univ k) :
    (∑ m ∈ piAntidiag univ p, subvectorMultiplicity m l * monomialWeight w m) =
      (Nat.choose p k : ℝ) * monomialWeight w l * (∑ j, w j) ^ (p - k) := by
  classical
  let s := piAntidiag (univ : Finset J) p
  let r := piAntidiag (univ : Finset J) (p - k)
  have hlsum := (mem_piAntidiag.mp hl).1
  have himage : s.filter (l ≤ ·) = r.image (l + ·) := by
    ext m
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hm, hle⟩
      have hmsum := (mem_piAntidiag.mp hm).1
      refine ⟨m - l, mem_piAntidiag.mpr ⟨?_, fun j _ => mem_univ j⟩, ?_⟩
      · exact (sum_tsub_distrib univ (fun j _ => hle j)).trans (by rw [hmsum, hlsum])
      · ext j
        exact Nat.add_sub_of_le (hle j)
    · rintro ⟨u, hu, rfl⟩
      have husum := (mem_piAntidiag.mp hu).1
      refine ⟨mem_piAntidiag.mpr ⟨?_, fun j _ => mem_univ j⟩, fun j => Nat.le_add_right _ _⟩
      rw [show (∑ j, (l + u) j) = (∑ j, l j) + ∑ j, u j from sum_add_distrib,
        hlsum, husum, Nat.add_sub_of_le hkp]
  have hsum :
      (∑ m ∈ s, subvectorMultiplicity m l * monomialWeight w m) =
        ∑ m ∈ s.filter (l ≤ ·), subvectorMultiplicity m l * monomialWeight w m := by
    rw [sum_filter]
    refine sum_congr rfl (fun m _ => ?_)
    split_ifs with hle
    · rfl
    · have hbad : ∃ j, m j < l j := by
        by_contra! hall
        exact hle hall
      obtain ⟨j, hj⟩ := hbad
      have hzero : subvectorMultiplicity m l = 0 := by
        unfold subvectorMultiplicity
        exact prod_eq_zero (mem_univ j) (by simp [Nat.choose_eq_zero_of_lt hj])
      rw [hzero, zero_mul]
  change (∑ m ∈ s, subvectorMultiplicity m l * monomialWeight w m) = _
  rw [hsum, himage, sum_image (fun _ _ _ _ h => add_left_cancel h)]
  calc
    _ = ∑ u ∈ r, (Nat.choose p k : ℝ) * monomialWeight w l * monomialWeight w u := by
      refine sum_congr rfl (fun u hu => ?_)
      rw [subvectorMultiplicity_mul_monomialWeight, hlsum, (mem_piAntidiag.mp hu).1,
        Nat.add_sub_of_le hkp]
    _ = _ := by
      rw [← mul_sum]
      congr 1
      exact (sum_pow_eq_sum_piAntidiag univ w (p - k)).symm

private theorem exists_degree_subvector {J : Type*} [Fintype J] [DecidableEq J]
    (capacity : J → ℕ) (k : ℕ) (hk : k ≤ ∑ j, capacity j) :
    ∃ l ∈ piAntidiag univ k, l ≤ capacity := by
  induction k with
  | zero => exact ⟨0, by simp, fun j => Nat.zero_le (capacity j)⟩
  | succ k ih =>
      obtain ⟨l, hl, hle⟩ := ih ((Nat.le_succ k).trans hk)
      have hsum := (mem_piAntidiag.mp hl).1
      have hex : ∃ j, l j < capacity j := by
        by_contra! h
        have heq := le_antisymm hle (show capacity ≤ l from h)
        rw [← heq, hsum] at hk
        exact (Nat.not_succ_le_self k) hk
      obtain ⟨j, hj⟩ := hex
      let increment (i : J) : ℕ := if i = j then 1 else 0
      refine ⟨l + increment, mem_piAntidiag.mpr ⟨?_, fun i _ => mem_univ i⟩, ?_⟩
      · change (∑ i : J, (l i + increment i)) = k + 1
        rw [sum_add_distrib, hsum]
        simp [increment]
      · intro i
        change l i + increment i ≤ capacity i
        by_cases hi : i = j
        · simpa [increment, hi] using hj
        · simpa [increment, hi] using hle i

theorem one_le_subvectorMultiplicity {J : Type*} [Fintype J]
    {m l : J → ℕ} (hl : l ≤ m) : 1 ≤ subvectorMultiplicity m l := by
  rw [subvectorMultiplicity, ← Nat.cast_prod]
  exact_mod_cast (show 1 ≤ ∏ j, Nat.choose (m j) (l j) from
    one_le_prod (fun j _ => Nat.choose_pos (hl j)))

/-- Bound the weighted number of pairs sharing at least k occurrences. -/
theorem weighted_overlap_le_diagonal {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p k : ℕ) (hkp : k ≤ p) :
    (∑ m ∈ piAntidiag univ p, ∑ n ∈ piAntidiag univ p,
      if k ≤ ∑ j, min (m j) (n j) then monomialWeight w m * monomialWeight w n else 0) ≤
      (Nat.choose p k : ℝ) ^ 2 * (∑ j, w j) ^ (2 * (p - k)) * diagonal w k := by
  classical
  let s := piAntidiag (univ : Finset J) p
  let t := piAntidiag (univ : Finset J) k
  let c := monomialWeight w
  let factor (l m : J → ℕ) := subvectorMultiplicity m l * c m
  have hfactor (l m : J → ℕ) : 0 ≤ factor l m :=
    mul_nonneg (prod_nonneg (fun _ _ => Nat.cast_nonneg _)) (monomialWeight_nonneg w hw m)
  have hterm (m n : J → ℕ) :
      (if k ≤ ∑ j, min (m j) (n j) then c m * c n else 0) ≤
        ∑ l ∈ t, factor l m * factor l n := by
    by_cases h : k ≤ ∑ j, min (m j) (n j)
    · obtain ⟨l, hl, hle⟩ := exists_degree_subvector (fun j => min (m j) (n j)) k h
      have hm : l ≤ m := fun j => (hle j).trans (min_le_left _ _)
      have hn : l ≤ n := fun j => (hle j).trans (min_le_right _ _)
      rw [ite_eq_left h]
      calc
        c m * c n ≤ factor l m * factor l n := by
          have hmono (v : J → ℕ) (hv : l ≤ v) : c v ≤ factor l v := by
            change c v ≤ subvectorMultiplicity v l * c v
            simpa using mul_le_mul_of_nonneg_right (one_le_subvectorMultiplicity hv)
              (monomialWeight_nonneg w hw v)
          exact mul_le_mul (hmono m hm) (hmono n hn) (monomialWeight_nonneg w hw n) (hfactor l m)
        _ ≤ _ := single_le_sum (fun i _ => mul_nonneg (hfactor i m) (hfactor i n)) hl
    · rw [ite_eq_right h]
      exact sum_nonneg (fun l _ => mul_nonneg (hfactor l m) (hfactor l n))
  calc
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, ∑ l ∈ t, factor l m * factor l n :=
      sum_le_sum (fun m _ => sum_le_sum (fun n _ => hterm m n))
    _ = ∑ l ∈ t, (∑ m ∈ s, factor l m) ^ 2 := by
      simp_rw [sum_comm (s := s) (t := t) (f := fun n l => factor l _ * factor l n)]
      rw [sum_comm]
      apply sum_congr rfl
      intro l _
      simp_rw [← mul_sum, ← sum_mul, pow_two]
    _ = _ := by
      unfold diagonal
      rw [mul_sum]
      refine sum_congr rfl (fun l hl => ?_)
      rw [show (∑ m ∈ s, factor l m) =
        (Nat.choose p k : ℝ) * c l * (∑ j, w j) ^ (p - k) from
          sum_subvectorMultiplicity_mul_monomialWeight w p k hkp l hl, pow_mul]
      ring

private theorem abs_count_sub_le_square (a b : ℕ) :
    |(a : ℝ) - b| ≤ ((a : ℝ) - b) ^ 2 := by
  rcases lt_trichotomy a b with h | rfl | h
  · have hpos : (1 : ℝ) ≤ (b : ℝ) - a := by
      have hab : a + 1 ≤ b := h
      have hreal : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
      linarith
    rw [abs_of_nonpos (by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ (b : ℝ) - a from by linarith)
      (show 0 ≤ (b : ℝ) - a - 1 from by linarith)]
  · simp
  · have hpos : (1 : ℝ) ≤ (a : ℝ) - b := by
      have hba : b + 1 ≤ a := h
      have hreal : (b : ℝ) + 1 ≤ a := by exact_mod_cast hba
      linarith
    rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ (a : ℝ) - b from by linarith)
      (show 0 ≤ (a : ℝ) - b - 1 from by linarith)]

/-- A lower bound on the Euclidean scale of a pair from its common count. -/
theorem weighted_count_difference_sq_ge {J : Type*} [Fintype J] (radius : J → ℝ)
    {lowerRadius : ℝ} (hlower : 0 ≤ lowerRadius) (hradius : ∀ j, lowerRadius ≤ radius j)
    (m n : J → ℕ) (p : ℕ) (hm : (∑ j, m j) = p) (hn : (∑ j, n j) = p) :
    2 * lowerRadius ^ 2 * ((p : ℝ) - ∑ j, (min (m j) (n j) : ℝ)) ≤
      ∑ j, (((m j : ℝ) - n j) * radius j) ^ 2 := by
  have hsum :
      (∑ j, |(m j : ℝ) - n j|) = 2 * ((p : ℝ) - ∑ j, (min (m j) (n j) : ℝ)) := by
    have hcastm : (∑ j, (m j : ℝ)) = (p : ℝ) := by exact_mod_cast hm
    have hcastn : (∑ j, (n j : ℝ)) = (p : ℝ) := by exact_mod_cast hn
    have hpoint (j : J) :
        |(m j : ℝ) - n j| = ((m j : ℝ) + n j) - 2 * (min (m j) (n j) : ℝ) := by
      rcases le_total (m j) (n j) with h | h
      · have hreal : (m j : ℝ) ≤ n j := by exact_mod_cast h
        rw [min_eq_left hreal, abs_of_nonpos (sub_nonpos.mpr hreal)]
        ring
      · have hreal : (n j : ℝ) ≤ m j := by exact_mod_cast h
        rw [min_eq_right hreal, abs_of_nonneg (sub_nonneg.mpr hreal)]
        ring
    simp_rw [hpoint, sum_sub_distrib, sum_add_distrib, ← mul_sum, hcastm, hcastn]
    ring
  calc
    _ = lowerRadius ^ 2 * ∑ j, |(m j : ℝ) - n j| := by rw [hsum]; ring
    _ ≤ ∑ j, (((m j : ℝ) - n j) * radius j) ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum (fun j _ => ?_)
      rw [mul_pow]
      calc
        lowerRadius ^ 2 * |(m j : ℝ) - n j| ≤
          ((m j : ℝ) - n j) ^ 2 * lowerRadius ^ 2 := by
            rw [mul_comm (lowerRadius ^ 2) |(m j : ℝ) - n j|]
            exact mul_le_mul_of_nonneg_right (abs_count_sub_le_square (m j) (n j))
              (sq_nonneg _)
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact pow_le_pow_left₀ hlower (hradius j) 2

#print axioms weighted_overlap_le_diagonal
#print axioms weighted_count_difference_sq_ge

end D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
