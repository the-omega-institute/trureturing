/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/Moments
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.TotalVariation.ParityKernelMasses

/-! First and second coordinate moments of four-part compositions for refined BMV. -/

open scoped BigOperators

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarMoments

open D5.S3.TotalVariation.ParityKernelMasses (antidiagonal_tuple_card)

private def bump (i : Fin 4) (r : Fin 4 → ℕ) : Fin 4 → ℕ :=
  fun j => r j + if j = i then 1 else 0

private theorem bump_self (i : Fin 4) (r : Fin 4 → ℕ) :
    bump i r i = r i + 1 := by
  simp [bump]

private theorem bump_of_ne (i j : Fin 4) (h : j ≠ i) (r : Fin 4 → ℕ) :
    bump i r j = r j := by
  simp [bump, h]

private theorem sum_bump (i : Fin 4) (r : Fin 4 → ℕ) :
    (∑ j, bump i r j) = (∑ j, r j) + 1 := by
  classical
  unfold bump
  rw [Finset.sum_add_distrib]
  simp

/-- Removing one unit of the distinguished coordinate bijects its positive
fiber with all compositions of the preceding total. A weight vanishing on
the zero fiber can therefore be summed over the smaller total. -/
private theorem sum_bump_of_zero (p : ℕ) (i : Fin 4)
    (f : (Fin 4 → ℕ) → ℕ) (hf : ∀ r, r i = 0 → f r = 0) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple 4 (p + 1), f r) =
      ∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, f (bump i r) := by
  classical
  let C := Finset.Nat.antidiagonalTuple 4
  have hfilter :
      (∑ r ∈ (C (p + 1)).filter (fun r => 0 < r i), f r) =
        ∑ r ∈ C (p + 1), f r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : 0 < r i
    · simp [h]
    · simp [h, hf r (by omega)]
  rw [← hfilter]
  symm
  apply Finset.sum_bij (fun r _ => bump i r)
  · intro r hr
    apply Finset.mem_filter.mpr
    constructor
    · change bump i r ∈ Finset.Nat.antidiagonalTuple 4 (p + 1)
      rw [Finset.Nat.mem_antidiagonalTuple, sum_bump]
      exact congrArg (fun n : ℕ => n + 1) (Finset.Nat.mem_antidiagonalTuple.mp hr)
    · rw [bump_self]
      exact Nat.zero_lt_succ _
  · intro r _ s _ hrs
    funext j
    have h := congrFun hrs j
    change r j + (if j = i then 1 else 0) =
      s j + (if j = i then 1 else 0) at h
    exact Nat.add_right_cancel h
  · intro s hs
    have hs' := Finset.mem_filter.mp hs
    let r : Fin 4 → ℕ := fun j => s j - if j = i then 1 else 0
    have he : bump i r = s := by
      funext j
      by_cases hj : j = i
      · subst j
        have hpos : 0 < s i := hs'.2
        have hselected : r i = s i - 1 := by simp [r]
        rw [bump_self, hselected]
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
      · rw [bump_of_ne i j hj]
        simp [r, hj]
    have ht : (∑ j, s j) = p + 1 :=
      Finset.Nat.mem_antidiagonalTuple.mp hs'.1
    have hr : r ∈ C p := by
      change r ∈ Finset.Nat.antidiagonalTuple 4 p
      rw [Finset.Nat.mem_antidiagonalTuple]
      have h := sum_bump i r
      rw [he, ht] at h
      omega
    exact ⟨r, hr, he⟩
  · intro r _
    rfl

private theorem card_four (p : ℕ) :
    (Finset.Nat.antidiagonalTuple 4 p).card = (p + 3).choose 3 := by
  have h := antidiagonal_tuple_card (d := 4) (by decide) p
  simpa only [show p + 4 - 1 = p + 3 by omega] using h

/-- Unnormalized first moment of any of the four coordinates. -/
theorem sum_coordinate (p : ℕ) (i : Fin 4) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, r i) =
      (p + 3).choose 4 := by
  classical
  induction p with
  | zero =>
      norm_num [Finset.Nat.antidiagonalTuple_zero_right, Pi.zero_apply,
        Nat.choose_eq_zero_of_lt (show 3 < 4 by decide),
        Nat.choose_eq_zero_of_lt (show 3 < 5 by decide)]
  | succ p ih =>
      rw [sum_bump_of_zero p i (fun r => r i) (fun r hr => hr)]
      simp only [bump_self, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      rw [ih, card_four]
      simp only [Nat.cast_id]
      have h : (p + 3 + 1).choose 4 = (p + 3).choose 3 + (p + 3).choose 4 :=
        Nat.choose_succ_succ' (p + 3) 3
      rw [show p + 1 + 3 = p + 3 + 1 by omega]
      omega

/-- Unnormalized mixed second moment, for any two different slots. -/
theorem sum_coordinate_mul_coordinate (p : ℕ) (i j : Fin 4) (hij : i ≠ j) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, r i * r j) =
      (p + 3).choose 5 := by
  classical
  induction p with
  | zero =>
      norm_num [Finset.Nat.antidiagonalTuple_zero_right, Pi.zero_apply,
        Nat.choose_eq_zero_of_lt (show 3 < 4 by decide),
        Nat.choose_eq_zero_of_lt (show 3 < 5 by decide)]
  | succ p ih =>
      rw [sum_bump_of_zero p i (fun r => r i * r j) (by
        intro r hr
        simp [hr])]
      simp only [bump_self, bump_of_ne i j (Ne.symm hij), add_mul,
        one_mul, Finset.sum_add_distrib]
      rw [ih, sum_coordinate p j]
      have h : (p + 3 + 1).choose 5 = (p + 3).choose 4 + (p + 3).choose 5 :=
        Nat.choose_succ_succ' (p + 3) 4
      rw [show p + 1 + 3 = p + 3 + 1 by omega]
      omega

/-- Unnormalized diagonal second moment. -/
theorem sum_coordinate_sq (p : ℕ) (i : Fin 4) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, r i ^ 2) =
      (p + 3).choose 4 + 2 * (p + 3).choose 5 := by
  classical
  induction p with
  | zero =>
      norm_num [Finset.Nat.antidiagonalTuple_zero_right, Pi.zero_apply,
        Nat.choose_eq_zero_of_lt (show 3 < 4 by decide),
        Nat.choose_eq_zero_of_lt (show 3 < 5 by decide)]
  | succ p ih =>
      rw [sum_bump_of_zero p i (fun r => r i ^ 2) (by
        intro r hr
        simp [hr])]
      have hsplit :
          (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, bump i r i ^ 2) =
            (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, r i ^ 2) +
              2 * (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, r i) +
              (Finset.Nat.antidiagonalTuple 4 p).card := by
        calc
          _ = ∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, (r i ^ 2 + 2 * r i + 1) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [bump_self]
            ring
          _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
      rw [hsplit, ih, sum_coordinate p i, card_four]
      have h₄ : (p + 3 + 1).choose 4 = (p + 3).choose 3 + (p + 3).choose 4 :=
        Nat.choose_succ_succ' (p + 3) 3
      have h₅ : (p + 3 + 1).choose 5 = (p + 3).choose 4 + (p + 3).choose 5 :=
        Nat.choose_succ_succ' (p + 3) 4
      rw [show p + 1 + 3 = p + 3 + 1 by omega]
      omega

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarMoments
