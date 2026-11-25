/- GID: D5/S3/Geometry/Diversity/SimplexQuadraticOptimality
   generality: G
   mirror-B: D5/B/S3/Geometry/Diversity/SimplexQuadraticOptimality
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Minimizers of a symmetric quadratic form on the probability simplex are characterized by the support and lower conditions. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#32)
escape_witness: nonneg_of_small (a quantity a with a t + b t^2 >= 0 for all small t > 0 is
  nonnegative) and the two feasible directions e_j - p and p - e_i in result, which turn
  minimality into the lower and support conditions; energy_add gives the exact expansion used
  for sufficiency under conditional nonnegativity.
proof_shape:
  Prob, energy: definitions; consumers: result.
  energy_add: content; consumer: result.
  nonneg_of_small: content; consumer: result.
  result: content.
Direct frozen dependencies: none.
Search record (§3.1): Mathlib has the standard simplex (stdSimplex, deprecated in favour of the
  Finsupp-based Convexity.StdSimplex) but no first-order characterization of quadratic
  minimizers on it; no D5 module states the criterion. The frozen
  BouafiaNegativeTypeDiversityDeletionRefutation is a fixed five-point refutation only.
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # Optimality of a quadratic form on the probability simplex

For a symmetric matrix `Z` and a probability vector `p`, write `E(p) = p ⬝ (Z p)`. If `p`
minimizes `E` on the probability simplex then `(Z p)_i = E(p)` on the support of `p` and
`(Z p)_j ≥ E(p)` for every `j`. When `E` is nonnegative on vectors with coordinate sum zero
(in particular when `Z` is positive definite), these conditions are also sufficient.
-/

set_option autoImplicit false

namespace D5.S3.Geometry.Diversity.SimplexQuadraticOptimality

open Matrix

variable {ι : Type*} [Fintype ι]

/-- A probability vector: nonnegative coordinates summing to one. -/
def Prob (p : ι → ℝ) : Prop := (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1

/-- The quadratic energy `E(p) = p ⬝ (Z p)`. -/
def energy (Z : Matrix ι ι ℝ) (p : ι → ℝ) : ℝ := p ⬝ᵥ (Z *ᵥ p)

/-- For symmetric `Z`, `E(p + t d) = E(p) + 2t d ⬝ (Z p) + t² E(d)`. -/
private lemma energy_add {Z : Matrix ι ι ℝ} (hZ : Z.IsSymm) (p d : ι → ℝ) (t : ℝ) :
    energy Z (p + t • d) = energy Z p + 2 * t * (d ⬝ᵥ (Z *ᵥ p)) + t ^ 2 * energy Z d := by
  have hs : p ⬝ᵥ (Z *ᵥ d) = d ⬝ᵥ (Z *ᵥ p) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hZ.eq, dotProduct_comm]
  simp only [energy, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hs]
  ring

/-- A real `a` with `a t + b t² ≥ 0` for all small `t > 0` is nonnegative. -/
private lemma nonneg_of_small {a b ε : ℝ} (hε : 0 < ε)
    (h : ∀ t, 0 < t → t ≤ ε → 0 ≤ a * t + b * t ^ 2) : 0 ≤ a := by
  by_contra ha
  push Not at ha
  set t := min ε (-a / (|b| + 1)) with htdef
  have hb1 : 0 < |b| + 1 := by positivity
  have ht : 0 < t := lt_min hε (div_pos (by linarith) hb1)
  have ht2 : t * (|b| + 1) ≤ -a := (le_div_iff₀ hb1).mp (min_le_right _ _)
  have hval := h t ht (min_le_left _ _)
  have hb : b * t ^ 2 ≤ |b| * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self b) (by positivity)
  nlinarith [abs_nonneg b]

/-- For symmetric `Z` and a probability vector `p`: a minimizer of `E` on the simplex satisfies
the support and lower conditions; when `E` is nonnegative on vectors of coordinate sum zero,
the two conditions characterize the minimizers. -/
theorem result (Z : Matrix ι ι ℝ) (hZ : Z.IsSymm) {p : ι → ℝ} (hp : Prob p) :
    ((∀ q, Prob q → energy Z p ≤ energy Z q) →
      (∀ i, 0 < p i → (Z *ᵥ p) i = energy Z p) ∧ ∀ j, energy Z p ≤ (Z *ᵥ p) j) ∧
    ((∀ v : ι → ℝ, ∑ i, v i = 0 → 0 ≤ energy Z v) →
      ((∀ q, Prob q → energy Z p ≤ energy Z q) ↔
        (∀ i, 0 < p i → (Z *ᵥ p) i = energy Z p) ∧ ∀ j, energy Z p ≤ (Z *ᵥ p) j)) := by
  classical
  have hp0 : ∀ k, 0 ≤ p k := hp.1
  have hp1 : ∑ k, p k = 1 := hp.2
  have necessary : (∀ q, Prob q → energy Z p ≤ energy Z q) →
      (∀ i, 0 < p i → (Z *ᵥ p) i = energy Z p) ∧ ∀ j, energy Z p ≤ (Z *ᵥ p) j := by
    intro hmin
    have hdir : ∀ d : ι → ℝ, ∀ ε : ℝ, 0 < ε →
        (∀ t, 0 < t → t ≤ ε → Prob (p + t • d)) → 0 ≤ d ⬝ᵥ (Z *ᵥ p) := by
      intro d ε hε hin
      have := nonneg_of_small (a := 2 * (d ⬝ᵥ (Z *ᵥ p))) (b := energy Z d) hε
        (fun t ht htε => by
          have h := hmin _ (hin t ht htε)
          rw [energy_add hZ] at h
          nlinarith)
      linarith
    have hlow : ∀ j, energy Z p ≤ (Z *ᵥ p) j := by
      intro j
      have h := hdir (Pi.single j 1 - p) 1 one_pos (fun t ht ht1 => by
        refine ⟨fun k => ?_, ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          have hs : 0 ≤ (Pi.single j (1 : ℝ) : ι → ℝ) k := by
            rcases eq_or_ne k j with rfl | hkj
            · simp
            · simp [hkj]
          nlinarith [hp0 k]
        · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
            Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
            Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte, hp1]
          ring)
      rw [sub_dotProduct, single_dotProduct, one_mul] at h
      exact sub_nonneg.mp h
    refine ⟨fun i hi => ?_, hlow⟩
    have h := hdir (p - Pi.single i 1) (p i) hi (fun t ht hti => by
      refine ⟨fun k => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rcases eq_or_ne k i with rfl | hki
        · simp only [Pi.single_eq_same]
          nlinarith
        · simp only [Pi.single_eq_of_ne hki, sub_zero]
          nlinarith [hp0 k]
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
          Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
          Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte, hp1]
        ring)
    rw [sub_dotProduct, single_dotProduct, one_mul] at h
    exact le_antisymm (sub_nonneg.mp h) (hlow i)
  refine ⟨necessary, fun hpsd => ⟨necessary, fun ⟨_, hlow⟩ q hq => ?_⟩⟩
  have hq0 : ∀ k, 0 ≤ q k := hq.1
  have hq1 : ∑ k, q k = 1 := hq.2
  have hexp := energy_add hZ p (q - p) 1
  rw [one_smul, add_sub_cancel] at hexp
  have hsum : ∑ i, (q - p) i = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hq1, hp1, sub_self]
  have hd := hpsd (q - p) hsum
  have hlin : 0 ≤ (q - p) ⬝ᵥ (Z *ᵥ p) := by
    rw [sub_dotProduct]
    have hE : p ⬝ᵥ (Z *ᵥ p) = energy Z p := rfl
    have : ∑ k, q k * energy Z p ≤ q ⬝ᵥ (Z *ᵥ p) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hlow k) (hq0 k)
    rw [← Finset.sum_mul, hq1, one_mul] at this
    linarith
  rw [hexp]
  nlinarith

end D5.S3.Geometry.Diversity.SimplexQuadraticOptimality
