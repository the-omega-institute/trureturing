/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Biased native frontier distances and exact shift-copy product minima. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeBiasedFrontierInfima

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)

/-- Directional cylinder weight, with `false` as the left edge. -/
def weight (θ : ℝ) : Address → ℝ
  | [] => 1
  | false :: p => θ * weight θ p
  | true :: p => (1 - θ) * weight θ p

/-- Biased mass of the existing first-disagreement frontier. -/
def distance (θ : ℝ) (s t : Source) : ℝ :=
  ∑ p ∈ D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier s t, weight θ p

private theorem distance_self (θ : ℝ) (s : Source) : distance θ s s = 0 := by
  cases s <;> simp [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier]

private theorem distance_of_of (θ : ℝ) (b c : Bool) (h : b ≠ c) :
    distance θ (.of b) (.of c) = 1 := by
  have hn : (FreeMagma.of b : Source) ≠ .of c := by
    intro he
    injection he with he
    exact h he
  simp only [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, if_neg hn, Finset.sum_singleton, weight, List.length_nil,
    pow_zero]

private theorem distance_of_mul (θ : ℝ) (b : Bool) (u v : Source) :
    distance θ (.of b) (.mul u v) = 1 := by
  simp [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, weight]

private theorem distance_mul_of (θ : ℝ) (u v : Source) (b : Bool) :
    distance θ (.mul u v) (.of b) = 1 := by
  simp [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, weight]

private theorem distance_mul_mul (θ : ℝ) (s u t v : Source) :
    distance θ (.mul s u) (.mul t v) =
      θ * distance θ s t + (1 - θ) * distance θ u v := by
  by_cases he : (.mul s u : Source) = .mul t v
  · injection he with hs hu
    subst t
    subst v
    rw [distance_self, distance_self, distance_self]
    ring
  · have hd : Disjoint ((D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier s t).image (List.cons false))
        ((D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier u v).image (List.cons true)) := by
        simp only [Finset.disjoint_left, Finset.mem_image]
        rintro _ ⟨a, _, rfl⟩ ⟨b, _, hb⟩
        cases hb
    simp only [distance, D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation.frontier, if_neg he]
    rw [Finset.sum_union hd,
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
    simp only [weight]
    rw [← Finset.mul_sum, ← Finset.mul_sum]

private theorem distance_nonneg (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s t : Source) : 0 ≤ distance θ s t := by
  classical
  have hw : ∀ p : Address, 0 ≤ weight θ p := by
    intro p
    induction p with
    | nil => simp [weight]
    | cons b p ih =>
        cases b
        · simpa [weight] using mul_nonneg hθ ih
        · simpa [weight] using mul_nonneg (sub_nonneg.mpr hθ1) ih
  unfold distance
  exact Finset.sum_nonneg (fun p hp => hw p)

private theorem distance_le_one (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s t : Source) : distance θ s t ≤ 1 := by
  induction s generalizing t with
  | of b =>
    cases t with
    | of c =>
      by_cases h : b = c
      · subst c
        rw [distance_self]
        norm_num
      · rw [distance_of_of θ b c h]
    | mul u v => rw [distance_of_mul]
  | mul s u hs hu =>
    cases t with
    | of c => rw [distance_mul_of]
    | mul t v =>
      rw [distance_mul_mul]
      calc
        θ * distance θ s t + (1 - θ) * distance θ u v ≤
            θ * 1 + (1 - θ) * 1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hs t) hθ)
            (mul_le_mul_of_nonneg_left (hu v) (sub_nonneg.mpr hθ1))
        _ = 1 := by ring

/-- The weighted first-disagreement mass satisfies the triangle inequality. -/
theorem biased_frontier_triangle (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s z t : Source) : distance θ s t ≤ distance θ s z + distance θ z t := by
  induction s generalizing z t with
  | of b =>
    cases z with
    | of c =>
      cases t with
      | of d =>
          by_cases hbc : b = c <;> by_cases hcd : c = d <;>
            by_cases hbd : b = d <;>
            simp_all [distance_self, distance_of_of]
      | mul u v =>
          rw [distance_of_mul]
          rw [distance_of_mul]
          by_cases h : b = c
          · subst c
            rw [distance_self]
            norm_num
          · rw [distance_of_of θ b c h]
            norm_num
    | mul l r =>
      cases t with
      | of d =>
          rw [distance_of_mul, distance_mul_of]
          by_cases h : b = d
          · subst d
            rw [distance_self]
            norm_num
          · rw [distance_of_of θ b d h]
            norm_num
      | mul u v =>
          rw [distance_of_mul, distance_of_mul]
          exact le_add_of_nonneg_right (distance_nonneg θ hθ hθ1 _ _)
  | mul s u hs hu =>
    cases z with
    | of c =>
      cases t with
      | of d =>
          rw [distance_mul_of, distance_mul_of]
          by_cases h : c = d
          · subst d
            rw [distance_self]
            norm_num
          · rw [distance_of_of θ c d h]
            norm_num
      | mul t v =>
          have hle := distance_le_one θ hθ hθ1 (.mul s u) (.mul t v)
          rw [distance_mul_mul] at hle
          rw [distance_mul_mul, distance_mul_of, distance_of_mul]
          exact hle.trans (by norm_num)
    | mul z w =>
      cases t with
      | of d =>
          rw [distance_mul_of, distance_mul_mul, distance_mul_of]
          have hn : 0 ≤ θ * distance θ s z + (1 - θ) * distance θ u w :=
            add_nonneg
              (mul_nonneg hθ (distance_nonneg θ hθ hθ1 _ _))
              (mul_nonneg (sub_nonneg.mpr hθ1) (distance_nonneg θ hθ hθ1 _ _))
          linarith
      | mul t v =>
          rw [distance_mul_mul, distance_mul_mul, distance_mul_mul]
          calc
            θ * distance θ s t + (1 - θ) * distance θ u v ≤
                θ * (distance θ s z + distance θ z t) +
                  (1 - θ) * (distance θ u w + distance θ w v) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (hs z t) hθ)
                (mul_le_mul_of_nonneg_left (hu w v) (sub_nonneg.mpr hθ1))
            _ = θ * distance θ s z + (1 - θ) * distance θ u w +
                  (θ * distance θ z t + (1 - θ) * distance θ w v) := by ring

/-- The same finite induction gives the probability bounds. -/
theorem biased_frontier_bounds (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (s t : Source) : 0 ≤ distance θ s t ∧ distance θ s t ≤ 1 := by
  exact ⟨distance_nonneg θ hθ hθ1 s t, distance_le_one θ hθ hθ1 s t⟩

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeBiasedFrontierInfima
