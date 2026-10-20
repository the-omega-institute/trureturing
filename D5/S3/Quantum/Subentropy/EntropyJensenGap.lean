/- GID: D5/S3/Quantum/Subentropy/EntropyJensenGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/EntropyJensenGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.NegMulLog]
   utility: none
   digest: Nonnegativity, homogeneity and joint convexity of finite entropy Jensen gaps. -/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Finite entropy gaps on the full nonnegative cone. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Quantum.Subentropy.EntropyJensenGap

/-- The uniform arithmetic mean of a finite real family. -/
def finiteAverage {S : Type*} [Fintype S] (a : S → ℝ) : ℝ :=
  (Fintype.card S : ℝ)⁻¹ * ∑ s, a s

/-- The entropy Jensen gap uses the continuous convention `η(0)=0`. -/
def entropyJensenGap {S : Type*} [Fintype S] (a : S → ℝ) : ℝ :=
  Real.negMulLog (finiteAverage a) - finiteAverage (fun s => Real.negMulLog (a s))

private theorem average_nonneg {S : Type*} [Fintype S] (a : S → ℝ)
    (ha : ∀ s, 0 ≤ a s) : 0 ≤ finiteAverage a := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun s _ => ha s))

private theorem average_add {S : Type*} [Fintype S] (a b : S → ℝ) :
    finiteAverage (fun s => a s + b s) = finiteAverage a + finiteAverage b := by
  simp [finiteAverage, Finset.sum_add_distrib, mul_add]

private theorem average_mul {S : Type*} [Fintype S] (c : ℝ) (a : S → ℝ) :
    finiteAverage (fun s => c * a s) = c * finiteAverage a := by
  simp [finiteAverage, ← Finset.mul_sum, mul_left_comm]

private theorem average_zero_iff {S : Type*} [Fintype S] [Nonempty S]
    (a : S → ℝ) (ha : ∀ s, 0 ≤ a s) : finiteAverage a = 0 ↔ a = 0 := by
  have hn : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro h
    have hsum : ∑ s, a s = 0 := (mul_eq_zero.mp h).resolve_left (inv_ne_zero hn)
    funext s
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => ha t)).mp hsum s (Finset.mem_univ s)
  · rintro rfl
    simp [finiteAverage]

private theorem gap_zero {S : Type*} [Fintype S] : entropyJensenGap (0 : S → ℝ) = 0 := by
  simp [entropyJensenGap, finiteAverage]

private theorem gap_nonneg {S : Type*} [Fintype S] [Nonempty S]
    (a : S → ℝ) (ha : ∀ s, 0 ≤ a s) : 0 ≤ entropyJensenGap a := by
  have hn : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _ : S => (Fintype.card S : ℝ)⁻¹)
    (p := a) (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp [hn]) (fun s _ => ha s)
  simpa [entropyJensenGap, finiteAverage, ← Finset.mul_sum, sub_nonneg] using h

private theorem gap_mul {S : Type*} [Fintype S] (c : ℝ) (a : S → ℝ) :
    entropyJensenGap (fun s => c * a s) = c * entropyJensenGap a := by
  simp only [entropyJensenGap, average_mul, Real.negMulLog_mul,
    average_add]
  rw [show finiteAverage (fun s => a s * Real.negMulLog c) =
    Real.negMulLog c * finiteAverage a by
      simpa only [mul_comm] using average_mul (Real.negMulLog c) a]
  ring

private theorem gap_normalized {S : Type*} [Fintype S]
    (a : S → ℝ) (hA : finiteAverage a ≠ 0) :
    entropyJensenGap a = -finiteAverage a *
      finiteAverage (fun s => Real.negMulLog (a s / finiteAverage a)) := by
  have hn : finiteAverage (fun s => a s / finiteAverage a) = 1 := by
    simp only [div_eq_mul_inv, mul_comm _ (finiteAverage a)⁻¹, average_mul]
    exact inv_mul_cancel₀ hA
  have heq : (fun s => finiteAverage a * (a s / finiteAverage a)) = a := by
    funext s
    field_simp
  have h := gap_mul (finiteAverage a) (fun s => a s / finiteAverage a)
  rw [heq] at h
  simp only [entropyJensenGap, hn, Real.negMulLog_one, zero_sub] at h
  simpa only [entropyJensenGap, mul_neg, neg_mul] using h

private theorem gap_subadditive {S : Type*} [Fintype S] [Nonempty S]
    (a b : S → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) :
    entropyJensenGap (fun s => a s + b s) ≤ entropyJensenGap a + entropyJensenGap b := by
  have hA := average_nonneg a ha
  have hB := average_nonneg b hb
  by_cases hAz : finiteAverage a = 0
  · have haz := (average_zero_iff a ha).mp hAz
    simp [haz, gap_zero]
  by_cases hBz : finiteAverage b = 0
  · have hbz := (average_zero_iff b hb).mp hBz
    simp [hbz, gap_zero]
  have hAp : 0 < finiteAverage a := lt_of_le_of_ne hA (Ne.symm hAz)
  have hBp : 0 < finiteAverage b := lt_of_le_of_ne hB (Ne.symm hBz)
  have hT : 0 < finiteAverage a + finiteAverage b := add_pos hAp hBp
  rw [gap_normalized _ (by rw [average_add]; exact hT.ne'),
    gap_normalized a hAz, gap_normalized b hBz, average_add]
  have hp : ∀ s,
      finiteAverage a / (finiteAverage a + finiteAverage b) *
          Real.negMulLog (a s / finiteAverage a) +
        finiteAverage b / (finiteAverage a + finiteAverage b) *
          Real.negMulLog (b s / finiteAverage b) ≤
      Real.negMulLog ((a s + b s) / (finiteAverage a + finiteAverage b)) := by
    intro s
    have h := Real.concaveOn_negMulLog.2
      (div_nonneg (ha s) hA) (div_nonneg (hb s) hB)
      (div_nonneg hA hT.le) (div_nonneg hB hT.le)
      (by field_simp <;> ring : finiteAverage a / (finiteAverage a + finiteAverage b) +
        finiteAverage b / (finiteAverage a + finiteAverage b) = 1)
    simp only [smul_eq_mul] at h
    convert h using 1
    congr 1
    field_simp
    <;> ring
  have hav := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun s _ => hp s))
    (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card S) : (0 : ℝ) ≤ Fintype.card S))
  change finiteAverage (fun s => _ + _) ≤ finiteAverage (fun s => _) at hav
  rw [average_add, average_mul, average_mul] at hav
  have hmul := mul_le_mul_of_nonneg_left hav hT.le
  have hcancel :
      (finiteAverage a + finiteAverage b) *
        (finiteAverage a / (finiteAverage a + finiteAverage b) *
            finiteAverage (fun s => Real.negMulLog (a s / finiteAverage a)) +
          finiteAverage b / (finiteAverage a + finiteAverage b) *
            finiteAverage (fun s => Real.negMulLog (b s / finiteAverage b))) =
      finiteAverage a * finiteAverage (fun s => Real.negMulLog (a s / finiteAverage a)) +
        finiteAverage b * finiteAverage (fun s => Real.negMulLog (b s / finiteAverage b)) := by
    field_simp
    <;> ring
  rw [hcancel] at hmul
  nlinarith

private theorem gap_convex {S : Type*} [Fintype S] [Nonempty S] :
    ConvexOn ℝ {a : S → ℝ | ∀ s, 0 ≤ a s} entropyJensenGap := by
  constructor
  · intro a ha b hb c d hc hd hcd s
    exact add_nonneg (mul_nonneg hc (ha s)) (mul_nonneg hd (hb s))
  · intro a ha b hb c d hc hd hcd
    have h := gap_subadditive (fun s => c * a s) (fun s => d * b s)
      (fun s => mul_nonneg hc (ha s)) (fun s => mul_nonneg hd (hb s))
    change entropyJensenGap (fun s => c * a s + d * b s) ≤
      c * entropyJensenGap a + d * entropyJensenGap b
    simpa only [gap_mul] using h

/-- The finite entropy Jensen gap is nonnegative, homogeneous, and jointly convex
on the full nonnegative cone, including all zero-coordinate boundary faces. -/
theorem entropyJensenGap_laws {S : Type*} [Fintype S] [Nonempty S] :
    (∀ (a : S → ℝ), (∀ s, 0 ≤ a s) → 0 ≤ entropyJensenGap a) ∧
    (∀ (c : ℝ) (a : S → ℝ), 0 ≤ c →
      entropyJensenGap (fun s => c * a s) = c * entropyJensenGap a) ∧
    ConvexOn ℝ {a : S → ℝ | ∀ s, 0 ≤ a s} entropyJensenGap :=
  ⟨gap_nonneg, ⟨fun c a _ => gap_mul c a, gap_convex⟩⟩


end D5.S3.Quantum.Subentropy.EntropyJensenGap
