/- GID: D5/S3/StatisticalMechanics/RandomWalks/HarmonicSquareDifferences
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/RandomWalks/HarmonicSquareDifferences
   mirror-E: none(waiver:abstract-lattice-family)
   anchors: []
   utility: none
   digest: All-order mixed-square differences of real harmonic lattice functions. -/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Harmonic squares on the integer lattice

The signed coordinate directions are labelled, so a word can repeat a direction.
The empty word acts as the identity. The normalization is the reciprocal of the
number of labels, not the reciprocal of the number of distinct word endpoints.

The all-order identity is the mixed-square identity of Lippner--Mangoubi,
arXiv:1312.4550v3, Theorem 2.1, Claim 2.2 and Remark 2.3.
-/

noncomputable section

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.RandomWalks.HarmonicSquareDifferences

/-- The integer lattice of arbitrary finite dimension. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- A coordinate and its sign; `true` denotes the positive direction. -/
abbrev Direction (d : ℕ) := Fin d × Bool

/-- The signed standard coordinate vector labelled by `v`. -/
def step {d : ℕ} (v : Direction d) : Lattice d :=
  fun i => if i = v.1 then (if v.2 then 1 else -1) else 0

/-- An ordered word, with no distinctness restriction on its letters. -/
abbrev Word (d k : ℕ) := Fin k → Direction d

/-- The uniform mean over all `2*d` labelled nearest neighbours. -/
def translationMean (d : ℕ) : Module.End ℝ (Lattice d → ℝ) where
  toFun f := fun x => (2 * (d : ℝ))⁻¹ * ∑ v : Direction d, f (x + step v)
  map_add' f g := by
    ext x
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

/-- The normalized discrete Laplacian `P-I`. -/
def laplacian (d : ℕ) : Module.End ℝ (Lattice d → ℝ) :=
  translationMean d - 1

/-- Harmonicity is exactly the fixed-point equation for the finite mean. -/
def Harmonic {d : ℕ} (f : Lattice d → ℝ) : Prop :=
  translationMean d f = f

/-- Pointwise square, with no sign restriction on the original function. -/
def square {d : ℕ} (f : Lattice d → ℝ) : Lattice d → ℝ :=
  fun x => (f x) ^ 2

/-- Compose the forward differences in the order of the word. -/
def mixedDifference {d : ℕ} : (k : ℕ) → Word d k →
    (Lattice d → ℝ) → Lattice d → ℝ
  | 0, _, f => f
  | k + 1, w, f => fwdDiff (step (w 0)) (mixedDifference k (Fin.tail w) f)

private theorem normalization {d : ℕ} (hd : 0 < d) :
    (2 * (d : ℝ))⁻¹ * (2 * (d : ℝ)) = 1 := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) hd')

private theorem mean_as_sum {d : ℕ} (f : Lattice d → ℝ) :
    translationMean d f = (2 * (d : ℝ))⁻¹ •
      ∑ v : Direction d, (fun x => f (x + step v)) := by
  ext x
  simp [translationMean, Finset.sum_apply, smul_eq_mul]

private theorem mean_forward_difference {d : ℕ} (v : Direction d)
    (f : Lattice d → ℝ) :
    translationMean d (fwdDiff (step v) f) =
      fwdDiff (step v) (translationMean d f) := by
  rw [mean_as_sum, mean_as_sum, fwdDiff_const_smul, fwdDiff_finsetSum]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  ext x
  exact (fwdDiff_comp_add (step v) f (step u) x).symm

private theorem harmonic_forward_difference {d : ℕ} {f : Lattice d → ℝ}
    (hf : Harmonic f) (v : Direction d) : Harmonic (fwdDiff (step v) f) := by
  change translationMean d (fwdDiff (step v) f) = fwdDiff (step v) f
  rw [mean_forward_difference, hf]

private theorem harmonic_mixed_difference {d : ℕ} {f : Lattice d → ℝ}
    (hf : Harmonic f) (k : ℕ) (w : Word d k) :
    Harmonic (mixedDifference k w f) := by
  induction k generalizing w with
  | zero => exact hf
  | succ k ih =>
    exact harmonic_forward_difference (ih (Fin.tail w)) (w 0)

private theorem square_laplacian {d : ℕ} (hd : 0 < d)
    {f : Lattice d → ℝ} (hf : Harmonic f) :
    laplacian d (square f) = (2 * (d : ℝ))⁻¹ •
      ∑ v : Direction d, square (fwdDiff (step v) f) := by
  ext x
  have hmean : (2 * (d : ℝ))⁻¹ * ∑ v : Direction d, f (x + step v) = f x :=
    congrFun hf x
  have hnorm := normalization hd
  have hsum : (∑ v : Direction d, (f (x + step v) - f x) ^ 2) =
      (∑ v : Direction d, (f (x + step v)) ^ 2) -
        (2 * f x) * (∑ v : Direction d, f (x + step v)) +
        (2 * (d : ℝ)) * (f x) ^ 2 := by
    calc
      _ = ∑ v : Direction d,
          ((f (x + step v)) ^ 2 - (2 * f x) * f (x + step v) + (f x) ^ 2) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
        <;> ring
  change (2 * (d : ℝ))⁻¹ * (∑ v : Direction d, (f (x + step v)) ^ 2) -
      (f x) ^ 2 = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, square, fwdDiff]
  rw [hsum]
  have hcross := congrArg (fun t : ℝ => (2 * f x) * t) hmean
  have hconstant := congrArg (fun t : ℝ => t * (f x) ^ 2) hnorm
  nlinarith [hcross, hconstant]

private theorem sum_words_succ {d k : ℕ} (F : Word d (k + 1) → ℝ) :
    (∑ w : Word d (k + 1), F w) =
      ∑ v : Direction d, ∑ w : Word d k, F (Fin.cons v w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Direction d)).sum_comp,
    Fintype.sum_prod_type]

/-- Every iterate of `P-I` on a harmonic square is the normalized sum of all
ordered mixed-difference squares, including order zero and repeated letters. -/
theorem harmonic_square_iterate {d : ℕ} (hd : 0 < d) (H : Lattice d → ℝ)
    (hH : Harmonic H) (k : ℕ) (x : Lattice d) :
    ((laplacian d)^[k]) (square H) x =
      ((2 * (d : ℝ))⁻¹) ^ k *
        ∑ w : Word d k, (mixedDifference k w H x) ^ 2 := by
  have hall : ∀ k : ℕ,
      ((laplacian d)^[k]) (square H) =
        ((2 * (d : ℝ))⁻¹) ^ k •
          ∑ w : Word d k, square (mixedDifference k w H) := by
    intro k
    induction k with
    | zero =>
      ext y
      simp [mixedDifference, square, Finset.sum_apply]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_smul, map_sum]
      simp_rw [square_laplacian hd (harmonic_mixed_difference hH k _)]
      rw [← Finset.smul_sum, smul_smul]
      ext y
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, square]
      rw [sum_words_succ]
      simp only [mixedDifference, Fin.cons_zero, Fin.tail_cons]
      rw [Finset.sum_comm, pow_succ]
  have hx := congrFun (hall k) x
  simpa only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, square] using hx

end D5.S3.StatisticalMechanics.RandomWalks.HarmonicSquareDifferences
