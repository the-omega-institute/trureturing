/- GID: D5/S3/TotalVariation/BooleanDeletionParity
   generality: G
   mirror-B: D5/B/S3/TotalVariation/BooleanDeletionParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Agreement after each single-coordinate deletion determines the parity of the mass discrepancy. -/

import D5.S3.TotalVariation.Pinsker
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.BooleanDeletionParity

open D5.S3.TotalVariation.Pinsker (totalVariation)

/-- When every one-coordinate marginal agrees, the signed mass difference
is the full parity character scaled by its sign-moment difference. -/
theorem boolean_deletion_mass_difference {I : Type*} [Fintype I] [DecidableEq I]
    (μ ν : (I → Bool) → ℝ)
    (hdelete : ∀ (i : I) (x : I → Bool),
      μ (Function.update x i false) + μ (Function.update x i true) =
      ν (Function.update x i false) + ν (Function.update x i true)) :
    let sign (x : I → Bool) := ∏ i, if x i then (-1 : ℝ) else 1
    let d := ∑ x, (μ x - ν x) * sign x
    (∀ x, μ x - ν x = (d / (2 : ℝ) ^ Fintype.card I) * sign x) ∧
      totalVariation μ ν = |d| / 2 := by
  classical
  intro sign d
  let delta (x : I → Bool) := μ x - ν x
  let bitMask (s : Finset I) (i : I) : Bool := decide (i ∈ s)
  let origin : I → Bool := fun _ => false
  have hmask (s : Finset I) : delta (bitMask s) = (∏ _ ∈ s, (-1 : ℝ)) * delta origin := by
    induction s using Finset.induction_on with
    | empty => simp [bitMask, origin]
    | @insert i s hi ih =>
      have hfalse : Function.update (bitMask s) i false = bitMask s := by
        funext j
        by_cases h : j = i
        · subst j
          simp [bitMask, hi]
        · simp [Function.update_of_ne h]
      have htrue : Function.update (bitMask s) i true = bitMask (insert i s) := by
        funext j
        by_cases h : j = i
        · subst j
          simp [bitMask]
        · simp [Function.update_of_ne h, bitMask, h]
      have h := hdelete i (bitMask s)
      rw [hfalse, htrue] at h
      rw [Finset.prod_insert hi, mul_assoc, ← ih]
      simp only [delta]
      linarith
  have hmass (x : I → Bool) : delta x = sign x * delta origin := by
    let s := Finset.univ.filter (fun i => x i = true)
    have hx : bitMask s = x := by
      funext i
      cases h : x i <;> simp [bitMask, s, h]
    have hsign : sign x = ∏ _ ∈ s, (-1 : ℝ) := by
      change (∏ i, if x i then (-1 : ℝ) else 1) = _
      simp only [s, Finset.prod_filter]
    rw [hsign, ← hx]
    exact hmask s
  have hsignAbs (x : I → Bool) : |sign x| = 1 := by
    change |∏ i, if x i then (-1 : ℝ) else 1| = 1
    rw [Finset.abs_prod]
    apply Finset.prod_eq_one
    intro i _
    cases x i <;> norm_num
  have hsignSq (x : I → Bool) : sign x * sign x = 1 := by
    rw [← sq, ← sq_abs, hsignAbs]
    norm_num
  have hcard : (Fintype.card (I → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card I := by
    rw [Fintype.card_fun, Fintype.card_bool]
    norm_cast
  have hd : d = (2 : ℝ) ^ Fintype.card I * delta origin := by
    change (∑ x, delta x * sign x) = _
    have hterm (x : I → Bool) : delta x * sign x = delta origin := by
      rw [hmass]
      calc
        (sign x * delta origin) * sign x = (sign x * sign x) * delta origin := by ring
        _ = delta origin := by rw [hsignSq, one_mul]
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hden : (2 : ℝ) ^ Fintype.card I ≠ 0 := by positivity
  have hcoef : d / (2 : ℝ) ^ Fintype.card I = delta origin := by
    rw [div_eq_iff hden, hd, mul_comm]
  constructor
  · intro x
    change delta x = _
    rw [hmass, hcoef, mul_comm]
  · have hterm (x : I → Bool) : |μ x - ν x| = |delta origin| := by
      change |delta x| = _
      rw [hmass, abs_mul, hsignAbs, one_mul]
    have hpos : 0 ≤ (2 : ℝ) ^ Fintype.card I := by positivity
    unfold totalVariation
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, hd, abs_mul,
      abs_of_nonneg hpos]
    ring

end D5.S3.TotalVariation.BooleanDeletionParity
