/- GID: D5/S3/Entropy/BinaryCompression
   generality: G
   mirror-B: D5/B/S3/Entropy/BinaryCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp binary conditional entropy and Bayes error frontiers. -/

import D5.S3.Entropy.ConditionalEntropy
import D5.S3.Estimation.FanoSharp
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Finite stochastic views of a fair measured bit, with entropy in bits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset
open Set (SurjOn)

noncomputable section

namespace D5.S3.Entropy.BinaryCompression

structure Compression (Y : Type*) [Fintype Y] where
  kernel : Fin 2 → Y → ℝ
  nonneg : ∀ j y, 0 ≤ kernel j y
  sum_one : ∀ j, ∑ y, kernel j y = 1

variable {Y : Type*} [Fintype Y] (C : Compression Y)

def joint (y : Y) (j : Fin 2) : ℝ := C.kernel j y / 2

def mass (y : Y) : ℝ := joint C y 0 + joint C y 1

/-- Positive-mass posteriors use the joint law. Lean's division at zero
assigns zero here, and every score contribution at such a view has weight zero. -/
def posterior (y : Y) : ℝ := joint C y 0 / mass C y

theorem joint_nonneg (y : Y) (j : Fin 2) : 0 ≤ joint C y j :=
  div_nonneg (C.nonneg j y) (by norm_num)

theorem mass_nonneg (y : Y) : 0 ≤ mass C y :=
  add_nonneg (joint_nonneg C y 0) (joint_nonneg C y 1)

theorem sum_mass : ∑ y, mass C y = 1 := by
  simp only [mass, joint, sum_add_distrib, ← sum_div, C.sum_one]
  norm_num

theorem posterior_mem (y : Y) : posterior C y ∈ Set.Icc 0 1 := by
  refine ⟨div_nonneg (joint_nonneg C y 0) (mass_nonneg C y), ?_⟩
  by_cases h : mass C y = 0
  · simp [posterior, h]
  exact (div_le_one (lt_of_le_of_ne (mass_nonneg C y) (Ne.symm h))).2
    (le_add_of_nonneg_right (joint_nonneg C y 1))

theorem mass_mul_posterior (y : Y) : mass C y * posterior C y = joint C y 0 := by
  by_cases h : mass C y = 0
  · have h' := joint_nonneg C y 0
    have h'' := joint_nonneg C y 1
    unfold mass at h
    rw [show mass C y = 0 from h, zero_mul]
    linarith
  · rw [posterior, mul_div_cancel₀ _ h]

theorem mass_mul_one_sub_posterior (y : Y) :
    mass C y * (1 - posterior C y) = joint C y 1 := by
  rw [mul_sub, mul_one, mass_mul_posterior, mass]
  ring

def posteriorError (y : Y) : ℝ := min (posterior C y) (1 - posterior C y)

def bayesError : ℝ := ∑ y, mass C y * posteriorError C y

def errorOf (g : Y → Fin 2) : ℝ :=
  ∑ y, joint C y (1 - g y)

def mapGuess (y : Y) : Fin 2 := if 1 - posterior C y ≤ posterior C y then 0 else 1

/-- The posterior formula is the minimum probability of a wrong guess. -/
theorem bayesError_isLeast :
    IsLeast {e : ℝ | ∃ g : Y → Fin 2, errorOf C g = e} (bayesError C) := by
  have h0 (y : Y) : mass C y * posteriorError C y ≤ joint C y 0 := by
    rw [← mass_mul_posterior C y]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (mass_nonneg C y)
  have h1 (y : Y) : mass C y * posteriorError C y ≤ joint C y 1 := by
    rw [← mass_mul_one_sub_posterior C y]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (mass_nonneg C y)
  constructor
  · refine ⟨mapGuess C, sum_congr rfl fun y _ => ?_⟩
    by_cases h : 1 - posterior C y ≤ posterior C y
    · rw [mapGuess, ite_eq_left h, sub_zero, posteriorError, min_eq_right h,
        mass_mul_one_sub_posterior]
    · rw [mapGuess, ite_eq_right h, sub_self, posteriorError, min_eq_left (le_of_not_ge h),
        mass_mul_posterior]
  · rintro e ⟨g, rfl⟩
    exact sum_le_sum fun y _ => by
      have hg (j : Fin 2) : j = 0 ∨ j = 1 := by fin_cases j <;> decide
      rcases hg (g y) with h | h
      · simpa [h] using h1 y
      · simpa [h] using h0 y

theorem posteriorError_mem (y : Y) : posteriorError C y ∈ Set.Icc 0 (2 : ℝ)⁻¹ := by
  obtain ⟨h0, h1⟩ := posterior_mem C y
  refine ⟨le_min h0 (sub_nonneg.mpr h1), ?_⟩
  unfold posteriorError
  by_cases h : posterior C y ≤ 2⁻¹
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by norm_num at h ⊢; linarith)

theorem bayesError_mem : bayesError C ∈ Set.Icc 0 (2 : ℝ)⁻¹ := by
  refine ⟨sum_nonneg fun y _ => mul_nonneg (mass_nonneg C y) (posteriorError_mem C y).1, ?_⟩
  calc
    bayesError C ≤ ∑ y, mass C y * (2 : ℝ)⁻¹ :=
      sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (posteriorError_mem C y).2 (mass_nonneg C y)
    _ = (2 : ℝ)⁻¹ := by rw [← sum_mul, sum_mass, one_mul]

def h2 (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

def entropyBits : ℝ := ∑ y, mass C y * h2 (posterior C y)

private theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem h2_zero : h2 0 = 0 := by simp [h2]
@[simp] theorem h2_one : h2 1 = 0 := by simp [h2]
@[simp] theorem h2_half : h2 (2 : ℝ)⁻¹ = 1 := by
  simp [h2, log_two_pos.ne']

@[simp] theorem h2_one_sub (p : ℝ) : h2 (1 - p) = h2 p := by simp [h2]

theorem h2_concave : ConcaveOn ℝ (Set.Icc 0 1) h2 := by
  change ConcaveOn ℝ (Set.Icc 0 1) (fun x => Real.binEntropy x / Real.log 2)
  simpa only [div_eq_inv_mul, smul_eq_mul] using
    Real.strictConcave_binEntropy.concaveOn.smul (inv_nonneg.mpr log_two_pos.le)

theorem h2_strictMonoOn : StrictMonoOn h2 (Set.Icc 0 (2 : ℝ)⁻¹) := by
  intro x hx y hy hxy
  exact (div_lt_div_iff_of_pos_right log_two_pos).2 (Real.binEntropy_strictMonoOn hx hy hxy)

private theorem chord (x : ℝ) (hx : x ∈ Set.Icc 0 (2 : ℝ)⁻¹) : 2 * x ≤ h2 x := by
  have h := h2_concave.2 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show (2 : ℝ)⁻¹ ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show 0 ≤ 1 - 2 * x by have := hx.2; norm_num at this; linarith)
    (show 0 ≤ 2 * x from mul_nonneg (by norm_num) hx.1)
    (show 1 - 2 * x + 2 * x = 1 by ring)
  simpa [smul_eq_mul, show 2 * x * (2 : ℝ)⁻¹ = x by ring] using h

theorem h2_posteriorError (y : Y) : h2 (posteriorError C y) = h2 (posterior C y) := by
  unfold posteriorError
  rcases le_total (posterior C y) (1 - posterior C y) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, h2_one_sub]

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy (conditionalEntropy)
open D5.S3.Entropy.MaxEntropy (shannonEntropy)

/-- The posterior formula agrees with the repository's conditional entropy,
converted from nats to bits. -/
theorem entropyBits_eq_conditionalEntropy :
    entropyBits C = conditionalEntropy (fun x : Y × Fin 2 => joint C x.1 x.2) / Real.log 2 := by
  rw [entropyBits, conditionalEntropy, sum_div]
  apply sum_congr rfl
  intro y _
  have hm : marginal (fun x : Y × Fin 2 => joint C x.1 x.2) y = mass C y := by
    simp [marginal, Fin.sum_univ_two, mass]
  rw [hm]
  by_cases hz : mass C y = 0
  · simp [hz]
  have h0 : conditional (fun x : Y × Fin 2 => joint C x.1 x.2) y 0 = posterior C y := by
    simp [conditional, hm, posterior]
  have h1 : conditional (fun x : Y × Fin 2 => joint C x.1 x.2) y 1 = 1 - posterior C y := by
    rw [conditional, hm, ← mass_mul_one_sub_posterior C y]
    field_simp
  rw [shannonEntropy, Fin.sum_univ_two, h0, h1, h2,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- The lower chord and the binary specialization of sharp Fano in bits. -/
theorem entropy_budget : 2 * bayesError C ≤ entropyBits C ∧
    entropyBits C ≤ h2 (bayesError C) := by
  constructor
  · rw [bayesError, mul_sum, entropyBits]
    exact sum_le_sum fun y _ => by
      rw [mul_left_comm, ← h2_posteriorError C y]
      exact mul_le_mul_of_nonneg_left (chord _ (posteriorError_mem C y)) (mass_nonneg C y)
  · classical
    let P : Y × Fin 2 → ℝ := fun z => joint C z.1 z.2
    obtain ⟨g, hg⟩ := (bayesError_isLeast C).1
    have hP : (∀ z, 0 ≤ P z) ∧ ∑ z, P z = 1 := by
      refine ⟨fun z => joint_nonneg C z.1 z.2, ?_⟩
      simpa only [P, Fintype.sum_prod_type, Fin.sum_univ_two, mass] using sum_mass C
    have he : (∑ z, if g z.1 ≠ z.2 then P z else 0) = bayesError C := by
      rw [← hg, errorOf, Fintype.sum_prod_type]
      apply sum_congr rfl
      intro y _
      have hs (j : Fin 2) : j = 0 ∨ j = 1 := by fin_cases j <;> decide
      rcases hs (g y) with h | h <;> simp [Fin.sum_univ_two, h, P]
    have hf := D5.S3.Estimation.FanoSharp.fano_inequality_sharp P g hP (by decide)
    dsimp only at hf
    have hf' : conditionalEntropy P ≤
        shannonEntropy (fun b : Bool => if b then bayesError C else 1 - bayesError C) +
          bayesError C * Real.log ((Fintype.card (Fin 2) : ℝ) - 1) := by
      rw [← he]
      convert hf using 3 <;> congr! 6
    have hh : conditionalEntropy P ≤ Real.binEntropy (bayesError C) := by
      norm_num [shannonEntropy, Fintype.sum_bool,
        Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_comm] at hf' ⊢
      exact hf'
    rw [entropyBits_eq_conditionalEntropy, h2]
    exact div_le_div_of_nonneg_right hh log_two_pos.le

/-- Reveal the label with probability `1 - t` and report an erasure otherwise. -/
def erasure (t : ℝ) (ht : t ∈ Set.Icc 0 1) : Compression (Fin 3) where
  kernel j y := if y = 2 then t else if y = j.castSucc then 1 - t else 0
  nonneg j y := by
    split
    · exact ht.1
    · split
      · exact sub_nonneg.mpr ht.2
      · exact le_rfl
  sum_one j := by fin_cases j <;> simp [Fin.sum_univ_succ]

/-- Report the fair label after a symmetric flip with probability `t`. -/
def symmetric (t : ℝ) (ht : t ∈ Set.Icc 0 1) : Compression (Fin 2) where
  kernel j y := if y = j then 1 - t else t
  nonneg j y := by split; exact sub_nonneg.mpr ht.2; exact ht.1
  sum_one j := by fin_cases j <;> simp [Fin.sum_univ_two]

private theorem weighted_of_joint (y : Y) (p : ℝ) (f : ℝ → ℝ)
    (hp : joint C y 0 = mass C y * p) :
    mass C y * f (posterior C y) = mass C y * f p := by
  by_cases hz : mass C y = 0
  · simp [hz]
  have heq : posterior C y = p := by
    rw [posterior, hp]
    field_simp
  rw [heq]

theorem erasure_scores (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    entropyBits (erasure t ht) = t ∧ bayesError (erasure t ht) = t / 2 := by
  have hf (f : ℝ → ℝ) :
      (∑ y, mass (erasure t ht) y * f (posterior (erasure t ht) y)) =
        (1 - t) / 2 * f 1 + ((1 - t) / 2 * f 0 + t * f (2 : ℝ)⁻¹) := by
    have hm (y : Fin 3) : mass (erasure t ht) y = if y = 2 then t else (1 - t) / 2 := by
      fin_cases y <;> norm_num [mass, joint, erasure]
    rw [Fin.sum_univ_three,
      weighted_of_joint _ 0 1 f (by rw [hm]; norm_num [joint, erasure]),
      weighted_of_joint _ 1 0 f (by rw [hm]; norm_num [joint, erasure]),
      weighted_of_joint _ 2 (2 : ℝ)⁻¹ f (by rw [hm]; norm_num [joint, erasure]; ring)]
    norm_num [hm, add_assoc]
  constructor
  · rw [entropyBits, hf h2]
    simp
  · rw [bayesError, show posteriorError (erasure t ht) =
      fun y => (fun p : ℝ => min p (1 - p)) (posterior (erasure t ht) y) from rfl, hf]
    norm_num
    ring

theorem symmetric_scores (t : ℝ) (ht : t ∈ Set.Icc 0 (2 : ℝ)⁻¹) :
    entropyBits (symmetric t ⟨ht.1, ht.2.trans (by norm_num)⟩) = h2 t ∧
    bayesError (symmetric t ⟨ht.1, ht.2.trans (by norm_num)⟩) = t := by
  let C := symmetric t ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hm (y : Fin 2) : mass C y = 1 / 2 := by
    fin_cases y <;> norm_num [mass, joint, C, symmetric] <;> ring
  have h0 : posterior C 0 = 1 - t := by
    rw [posterior, hm]
    norm_num [joint, C, symmetric]
    ring
  have h1 : posterior C 1 = t := by
    rw [posterior, hm]
    norm_num [joint, C, symmetric]
    ring
  have hle : t ≤ 1 - t := by have := ht.2; norm_num at this; linarith
  change entropyBits C = h2 t ∧ bayesError C = t
  constructor
  · rw [entropyBits, Fin.sum_univ_two, hm, hm, h0, h1, h2_one_sub]
    ring
  · rw [bayesError, Fin.sum_univ_two]
    simp only [posteriorError, hm, h0, h1, sub_sub_cancel, min_eq_right hle, min_eq_left hle]
    ring

theorem h2_surj : SurjOn h2 (Set.Icc 0 (2 : ℝ)⁻¹) (Set.Icc 0 1) := by
  have hcont : Continuous h2 := Real.binEntropy_continuous.div_const _
  change Set.Icc 0 1 ⊆ h2 '' Set.Icc 0 2⁻¹
  simpa only [h2_zero, h2_half] using
    (intermediate_value_Icc (show (0 : ℝ) ≤ 2⁻¹ by norm_num) hcont.continuousOn)

theorem entropy_frontiers (H : ℝ) (hH : H ∈ Set.Icc 0 1) :
    (∃ C : Compression (Fin 3), entropyBits C = H ∧ bayesError C = H / 2) ∧
    (∃ C : Compression (Fin 2), entropyBits C = H ∧ h2 (bayesError C) = H) := by
  refine ⟨⟨erasure H hH, erasure_scores H hH⟩, ?_⟩
  obtain ⟨t, ht, hte⟩ := h2_surj hH
  obtain ⟨hent, herr⟩ := symmetric_scores t ht
  exact ⟨_, hent.trans hte, by rw [herr, hte]⟩

#print axioms bayesError_isLeast
#print axioms entropy_budget
#print axioms entropyBits_eq_conditionalEntropy
#print axioms erasure_scores
#print axioms symmetric_scores
#print axioms entropy_frontiers

end D5.S3.Entropy.BinaryCompression
