/- GID: D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform bound along N = 6t refutes the proposed Fibonacci minimum limit. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Fib.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S1.Recurrence.PudelkoFibonacciMinimumLimitRefutation

/-- The bilateral Fibonacci sequence with values `x` and `y` at indices zero and one. -/
def bilateral_fibonacci (x y : ℤ) (k : ℤ) : ℤ :=
  x * Int.fib (k - 1) + y * Int.fib k

/-- Position zero is a global absolute-value minimizer; ties are allowed. -/
def min0 (x y : ℤ) : Prop :=
  ∀ k : ℤ, |bilateral_fibonacci x y 0| ≤ |bilateral_fibonacci x y k|

private noncomputable def downRegion (t : ℕ) : Finset (Σ _ : ℕ, ℤ) :=
  (Finset.range (3 * t)).sigma fun i =>
    Finset.Icc (-(6 * (t : ℤ))) (-2 * ((i : ℤ) + 1))

private noncomputable def upRegion (t : ℕ) : Finset (Σ _ : ℕ, ℤ) :=
  (Finset.range (2 * t)).sigma fun i =>
    Finset.Icc (3 * ((i : ℤ) + 1)) (6 * (t : ℤ))

private noncomputable def square (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)

private noncomputable def good (N : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact (square N).filter fun p => min0 p.1 p.2

private noncomputable def downImage (t : ℕ) : Finset (ℤ × ℤ) :=
  (downRegion t).image fun p => ((p.1 : ℤ) + 1, p.2)

private noncomputable def upImage (t : ℕ) : Finset (ℤ × ℤ) :=
  (upRegion t).image fun p => ((p.1 : ℤ) + 1, p.2)

private noncomputable def negImage (s : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  s.image fun p => (-p.1, -p.2)

private noncomputable def zeroImage (t : ℕ) : Finset (ℤ × ℤ) :=
  ({0} : Finset ℤ) ×ˢ Finset.Icc (-(6 * (t : ℤ))) (6 * (t : ℤ))

/-- Uniform probability that zero is a global absolute-value minimizer in the integer box. -/
noncomputable def bounded_min0_probability (N : ℕ) : ℚ :=
  by
    classical
    exact (((Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ
        Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
          fun p : ℤ × ℤ => min0 p.1 p.2).card : ℚ) /
      (((2 * N + 1 : ℕ) : ℚ) ^ 2)

/-- The proposed convergence of the bounded probability to one quarter. -/
def claim : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |bounded_min0_probability N - 1 / 4| < ε

/-- The bounded-initialization probability does not converge to one quarter. -/
theorem result : ¬ claim := by
  have bilateral_fibonacci_values (x y : ℤ) :
      bilateral_fibonacci x y 0 = x ∧
        bilateral_fibonacci x y 1 = y ∧
        bilateral_fibonacci x y 2 = x + y ∧
        bilateral_fibonacci x y (-1) = y - x ∧
        bilateral_fibonacci x y (-2) = 2 * x - y := by
    have hf : Int.fib (-3) = 2 := by decide
    simp [bilateral_fibonacci, hf]
    constructor <;> ring
  have cone (x y : ℤ) (hm : min0 x y) (hx : 0 < x) :
      3 * x ≤ y ∨ y ≤ -2 * x := by
    obtain ⟨h0, h1, h2, hn1, hn2⟩ := bilateral_fibonacci_values x y
    have h1' := hm 1
    have h2' := hm 2
    have hn1' := hm (-1)
    have hn2' := hm (-2)
    rw [h0, h1] at h1'
    rw [h0, h2] at h2'
    rw [h0, hn1] at hn1'
    rw [h0, hn2] at hn2'
    rw [abs_of_pos hx] at h1' h2' hn1' hn2'
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy] at h1'
      rcases le_total 0 (y - x) with hnx | hnx
      · rw [abs_of_nonneg hnx] at hn1'
        rcases le_total 0 (2 * x - y) with hnnx | hnnx
        · rw [abs_of_nonneg hnnx] at hn2'
          omega
        · rw [abs_of_nonpos hnnx] at hn2'
          omega
      · rw [abs_of_nonpos hnx] at hn1'
        omega
    · rw [abs_of_nonpos hy] at h1'
      rcases le_total 0 (x + y) with hxy | hxy
      · rw [abs_of_nonneg hxy] at h2'
        omega
      · rw [abs_of_nonpos hxy] at h2'
        omega
  have min0_neg (x y : ℤ) (h : min0 x y) : min0 (-x) (-y) := by
    intro k
    have hs (j : ℤ) : bilateral_fibonacci (-x) (-y) j =
        -bilateral_fibonacci x y j := by
      simp only [bilateral_fibonacci]
      ring
    simpa only [hs, abs_neg] using h k
  have sum_cast (n : ℕ) :
      2 * (∑ i ∈ Finset.range n, (i : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith [ih]
  have down_count (t : ℕ) :
      ((downRegion t).card : ℤ) = 9 * (t : ℤ) ^ 2 := by
    have hs : 2 * (∑ i ∈ Finset.range (3 * t), (i : ℤ)) =
        ((3 * t : ℕ) : ℤ) * (((3 * t : ℕ) : ℤ) - 1) := by
      exact sum_cast (3 * t)
    calc
      ((downRegion t).card : ℤ) =
          ∑ i ∈ Finset.range (3 * t), (6 * (t : ℤ) - 2 * (i : ℤ) - 1) := by
        simp only [downRegion, Finset.card_sigma, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hib : i < 3 * t := Finset.mem_range.mp hi
        calc
          ((Finset.Icc (-(6 * (t : ℤ))) (-2 * ((i : ℤ) + 1))).card : ℤ) =
              -2 * ((i : ℤ) + 1) + 1 - (-(6 * (t : ℤ))) :=
                Int.card_Icc_of_le (-(6 * (t : ℤ))) (-2 * ((i : ℤ) + 1)) (by omega)
          _ = _ := by ring
      _ = 9 * (t : ℤ) ^ 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
        push_cast
        norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hs
        ring_nf at hs ⊢
        omega
  have up_count (t : ℕ) :
      ((upRegion t).card : ℤ) = 6 * (t : ℤ) ^ 2 - (t : ℤ) := by
    have hs : 2 * (∑ i ∈ Finset.range (2 * t), (i : ℤ)) =
        ((2 * t : ℕ) : ℤ) * (((2 * t : ℕ) : ℤ) - 1) := by
      exact sum_cast (2 * t)
    calc
      ((upRegion t).card : ℤ) =
          ∑ i ∈ Finset.range (2 * t), (6 * (t : ℤ) - 3 * (i : ℤ) - 2) := by
        simp only [upRegion, Finset.card_sigma, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hib : i < 2 * t := Finset.mem_range.mp hi
        calc
          ((Finset.Icc (3 * ((i : ℤ) + 1)) (6 * (t : ℤ))).card : ℤ) =
              6 * (t : ℤ) + 1 - 3 * ((i : ℤ) + 1) :=
                Int.card_Icc_of_le (3 * ((i : ℤ) + 1)) (6 * (t : ℤ)) (by omega)
          _ = _ := by ring
      _ = 6 * (t : ℤ) ^ 2 - (t : ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
        push_cast
        norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hs
        ring_nf at hs ⊢
        omega
  have pos_down (t : ℕ) (x y : ℤ)
      (hx : 0 < x) (hxl : x ≤ 6 * (t : ℤ))
      (hyl : -(6 * (t : ℤ)) ≤ y) (hy : y ≤ -2 * x) :
      (x, y) ∈ downImage t := by
    let i := (x - 1).toNat
    have hi : i < 3 * t := by
      dsimp [i]
      omega
    have heq : (i : ℤ) + 1 = x := by
      dsimp [i]
      omega
    apply Finset.mem_image.mpr
    refine ⟨⟨i, y⟩, ?_, ?_⟩
    · simp only [downRegion, Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc]
      exact ⟨hi, hyl, by omega⟩
    · simp [heq]
  have pos_up (t : ℕ) (x y : ℤ)
      (hx : 0 < x) (hxl : x ≤ 6 * (t : ℤ))
      (hyu : y ≤ 6 * (t : ℤ)) (hy : 3 * x ≤ y) :
      (x, y) ∈ upImage t := by
    let i := (x - 1).toNat
    have hi : i < 2 * t := by
      dsimp [i]
      omega
    have heq : (i : ℤ) + 1 = x := by
      dsimp [i]
      omega
    apply Finset.mem_image.mpr
    refine ⟨⟨i, y⟩, ?_, ?_⟩
    · simp only [upRegion, Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc]
      exact ⟨hi, by omega, hyu⟩
    · simp [heq]
  have good_subset (t : ℕ) :
      good (6 * t) ⊆ zeroImage t ∪ downImage t ∪ upImage t ∪
        negImage (downImage t) ∪ negImage (upImage t) := by
    classical
    intro p hp
    have hgood : min0 p.1 p.2 := (Finset.mem_filter.mp hp).2
    have hbox : p.1 ∈ Finset.Icc (-(6 * (t : ℤ))) (6 * (t : ℤ)) ∧
        p.2 ∈ Finset.Icc (-(6 * (t : ℤ))) (6 * (t : ℤ)) := by
      simpa only [good, square, Finset.mem_product, Finset.mem_Icc,
        Nat.cast_mul, Nat.cast_ofNat] using
          (Finset.mem_product.mp (Finset.mem_filter.mp hp).1)
    simp only [Finset.mem_Icc] at hbox
    obtain ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩ := hbox
    rcases lt_trichotomy p.1 0 with hx | hx | hx
    · have hcone := cone (-p.1) (-p.2) (min0_neg _ _ hgood) (by omega)
      rcases hcone with hcone | hcone
      · have hmem := pos_up t (-p.1) (-p.2) (by omega) (by omega)
          (by omega) (by omega)
        simp only [Finset.mem_union]
        right
        exact Finset.mem_image.mpr ⟨(-p.1, -p.2), hmem, by simp⟩
      · have hmem := pos_down t (-p.1) (-p.2) (by omega) (by omega)
          (by omega) (by omega)
        simp only [Finset.mem_union]
        left
        right
        exact Finset.mem_image.mpr ⟨(-p.1, -p.2), hmem, by simp⟩
    · simp only [Finset.mem_union]
      left
      left
      left
      left
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hx,
        Finset.mem_Icc.mpr ⟨hyl, hyu⟩⟩
    · have hcone := cone p.1 p.2 hgood hx
      rcases hcone with hcone | hcone
      · simp only [Finset.mem_union]
        left
        left
        right
        exact pos_up t p.1 p.2 hx hxu hyu hcone
      · simp only [Finset.mem_union]
        left
        left
        left
        right
        exact pos_down t p.1 p.2 hx hxu hyl hcone
  have bounded_min0_count_six_mul (t : ℕ) :
      ((good (6 * t)).card : ℤ) ≤ 30 * (t : ℤ) ^ 2 + 10 * (t : ℤ) + 1 := by
    let z := zeroImage t
    let d := downImage t
    let u := upImage t
    let nd := negImage d
    let nu := negImage u
    have hsub : good (6 * t) ⊆ z ∪ d ∪ u ∪ nd ∪ nu := good_subset t
    have hcard : (good (6 * t)).card ≤ z.card + d.card + u.card + nd.card + nu.card := by
      have h₁ := Finset.card_le_card hsub
      have h₂ := Finset.card_union_le (z ∪ d ∪ u ∪ nd) nu
      have h₃ := Finset.card_union_le (z ∪ d ∪ u) nd
      have h₄ := Finset.card_union_le (z ∪ d) u
      have h₅ := Finset.card_union_le z d
      omega
    have hz : (z.card : ℤ) = 12 * (t : ℤ) + 1 := by
      dsimp [z, zeroImage]
      rw [Finset.card_product]
      simp only [Finset.card_singleton, one_mul]
      calc
        ((Finset.Icc (-(6 * (t : ℤ))) (6 * (t : ℤ))).card : ℤ) =
            6 * (t : ℤ) + 1 - (-(6 * (t : ℤ))) :=
              Int.card_Icc_of_le _ _ (by omega)
        _ = _ := by ring
    have hd : (d.card : ℤ) ≤ (downRegion t).card := by
      exact_mod_cast Finset.card_image_le
    have hu : (u.card : ℤ) ≤ (upRegion t).card := by
      exact_mod_cast Finset.card_image_le
    have hnd : (nd.card : ℤ) ≤ d.card := by
      exact_mod_cast Finset.card_image_le
    have hnu : (nu.card : ℤ) ≤ u.card := by
      exact_mod_cast Finset.card_image_le
    have hdc := down_count t
    have huc := up_count t
    have hci : ((good (6 * t)).card : ℤ) ≤
        (z.card : ℤ) + d.card + u.card + nd.card + nu.card := by
      exact_mod_cast hcard
    have hpoly : 30 * (t : ℤ) ^ 2 + 10 * (t : ℤ) + 1 =
        (12 * (t : ℤ) + 1) + 2 * (9 * (t : ℤ) ^ 2) +
          2 * (6 * (t : ℤ) ^ 2 - (t : ℤ)) := by
      ring
    rw [hpoly]
    omega
  have bound_probability (t : ℕ) (ht : 3 ≤ t) :
      bounded_min0_probability (6 * t) ≤ 2 / 9 := by
    have hcard : (((good (6 * t)).card : ℚ) ≤
        30 * (t : ℚ) ^ 2 + 10 * (t : ℚ) + 1) := by
      exact_mod_cast bounded_min0_count_six_mul t
    have hpos : (0 : ℚ) < (12 * (t : ℚ) + 1) ^ 2 := by positivity
    have htq : (3 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht
    have hsq : 3 * (t : ℚ) ≤ (t : ℚ) ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℚ) ≤ (t : ℚ) - 3 by linarith)
        (show (0 : ℚ) ≤ (t : ℚ) by positivity)]
    calc
      bounded_min0_probability (6 * t) =
          (((good (6 * t)).card : ℚ)) / (12 * (t : ℚ) + 1) ^ 2 := by
        simp only [bounded_min0_probability, good, square]
        congr 1
        push_cast
        ring
      _ ≤ (30 * (t : ℚ) ^ 2 + 10 * (t : ℚ) + 1) /
          (12 * (t : ℚ) + 1) ^ 2 :=
        (div_le_div_iff_of_pos_right hpos).mpr hcard
      _ ≤ 2 / 9 := by
        apply (div_le_iff₀ hpos).2
        nlinarith [hsq]
  intro hc
  obtain ⟨N₀, hlarge⟩ := hc (1 / 72) (by norm_num)
  let t := max 3 N₀
  have ht : 3 ≤ t := Nat.le_max_left _ _
  have hn : N₀ ≤ 6 * t := by
    dsimp [t]
    omega
  have hclose := hlarge (6 * t) hn
  have hfar := bound_probability t ht
  have hbelow := (abs_lt.mp hclose).1
  norm_num at hbelow
  linarith

example : Nonempty (ℤ × ℤ) := ⟨(0, 0)⟩

example : min0 0 0 := by
  intro k
  simp [bilateral_fibonacci]

example : (0 : ℚ) < 1 / 72 := by norm_num

#print axioms result

end D5.S1.Recurrence.PudelkoFibonacciMinimumLimitRefutation
