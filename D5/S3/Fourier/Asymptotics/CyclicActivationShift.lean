/- GID: D5/S3/Fourier/Asymptotics/CyclicActivationShift
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicActivationShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Displacement of a front support boundary under the two cyclic cosine constraints. -/

import D5.S3.Fourier.Asymptotics.CyclicEventualSupport

/-! The zero of the outermost weight locates the change of the front support. -/

open Finset Filter Matrix
open scoped Topology
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

namespace D5.S3.Fourier.Asymptotics.CyclicActivationShift

set_option autoImplicit false

private theorem boundary_moment_elimination {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (T a b g : ℝ)
    (hmass : ∑ i, (a + b * x i + g * x i ^ 2) = 0) :
    let n : ℝ := Fintype.card ι
    let s₁ := ∑ i, x i
    let s₂ := ∑ i, x i ^ 2
    let s₃ := ∑ i, x i ^ 3
    let K := ∑ i, x i * (a + b * x i + g * x i ^ 2)
    (n * s₂ - s₁ ^ 2) * (a + b * T + g * T ^ 2) =
      (n * T - s₁) * K +
        g * ((n * T - s₁) * (s₂ * T - s₃) - (s₁ * T - s₂) ^ 2) := by
  intro n s₁ s₂ s₃ K
  have hs₀ : n * a + s₁ * b + s₂ * g = 0 := by
    simpa [n, s₁, s₂, sum_add_distrib, ← mul_sum, mul_comm] using hmass
  have hs₁ : s₁ * a + s₂ * b + s₃ * g = K := by
    have term (i : ι) : x i * (a + b * x i + g * x i ^ 2) =
        x i * a + x i ^ 2 * b + x i ^ 3 * g := by ring
    simp [K, term, sum_add_distrib, ← sum_mul, s₁, s₂, s₃]
  rw [← hs₁]
  linear_combination (s₂ - s₁ * T) * hs₀

private theorem switch_coefficient {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (T a b a' b' m m₄ K : ℝ)
    (hZ : 0 < ∑ i, (T - x i))
    (hdet : 0 < (Fintype.card ι : ℝ) * (∑ i, x i ^ 2) - (∑ i, x i) ^ 2)
    (hM : ∑ i, x i * (T - x i) = (∑ i, (T - x i)) * m)
    (hM₄ : ∑ i, x i ^ 2 * (T - x i) = (∑ i, (T - x i)) * m₄)
    (hmass : ∑ i, (a + b * x i + (1 / (3 * ∑ j, (T - x j))) * x i ^ 2) = 0)
    (hmoment : ∑ i, x i * (a + b * x i + (1 / (3 * ∑ j, (T - x j))) * x i ^ 2) = K)
    (hmass' : ∑ i, (a' + b' * x i) = 0)
    (hmoment' : ∑ i, x i * (a' + b' * x i) = 1) :
    let Z := ∑ i, (T - x i)
    0 < a' + b' * T ∧
      (a + b * T + (1 / (3 * Z)) * T ^ 2) / (a' + b' * T) = K + (m₄ - m ^ 2) / 3 := by
  let n : ℝ := Fintype.card ι
  let s₁ := ∑ i, x i
  let s₂ := ∑ i, x i ^ 2
  let s₃ := ∑ i, x i ^ 3
  let Z := ∑ i, (T - x i)
  let g := 1 / (3 * Z)
  have h₀ : n * T - s₁ = Z := by simp [n, s₁, Z, sum_sub_distrib, mul_comm]
  have h₁ : s₁ * T - s₂ = Z * m := by
    rw [← hM]
    simp_rw [mul_sub, ← pow_two, sum_sub_distrib, ← sum_mul]
    rfl
  have h₂ : s₂ * T - s₃ = Z * m₄ := by
    rw [← hM₄]
    simp_rw [mul_sub, ← pow_succ, sum_sub_distrib, ← sum_mul]
    rfl
  have hf := boundary_moment_elimination x T a b g hmass
  dsimp only at hf
  change (n * s₂ - s₁ ^ 2) * _ = (n * T - s₁) * _ +
    g * ((n * T - s₁) * (s₂ * T - s₃) - (s₁ * T - s₂) ^ 2) at hf
  rw [h₀, h₁, h₂, hmoment] at hf
  have hmasslin : ∑ i, (a' + b' * x i + 0 * x i ^ 2) = 0 := by simpa using hmass'
  have hfl := boundary_moment_elimination x T a' b' 0 hmasslin
  dsimp only at hfl
  simp only [zero_mul, add_zero, hmoment', mul_one] at hfl
  change (n * s₂ - s₁ ^ 2) * (a' + b' * T) = n * T - s₁ at hfl
  rw [h₀] at hfl
  have hpositive : 0 < a' + b' * T := pos_of_mul_pos_right (hfl ▸ hZ) hdet.le
  refine ⟨hpositive, (div_eq_iff hpositive.ne').mpr ?_⟩
  apply (mul_right_inj' hdet.ne').mp
  change (n * s₂ - s₁ ^ 2) * (a + b * T + g * T ^ 2) =
    (n * s₂ - s₁ ^ 2) * ((K + (m₄ - m ^ 2) / 3) * (a' + b' * T))
  calc
    _ = Z * K + g * (Z * (Z * m₄) - (Z * m) ^ 2) := hf
    _ = Z * (K + (m₄ - m ^ 2) / 3) := by
      dsimp only [g]
      field_simp [hZ.ne']
    _ = _ := by rw [← hfl]; ring

private theorem sum_sixth_rat (n : ℕ) :
    (∑ j ∈ range (n + 1), (j : ℚ) ^ 6) =
      (n : ℚ) * (n + 1) * (2 * n + 1) *
        (3 * (n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 3 - 3 * n + 1) / 42 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_centered_sixth (n : ℕ) :
    (∑ k ∈ Icc (-(n : ℤ)) (n : ℤ), (k : ℝ) ^ 6) =
      (n : ℝ) * (n + 1) * (2 * n + 1) *
        (3 * (n : ℝ) ^ 4 + 6 * (n : ℝ) ^ 3 - 3 * n + 1) / 21 := by
  have heven : Function.Even (fun k : ℤ => (k : ℝ) ^ 6) := by
    intro k
    dsimp only
    push_cast
    ring
  rw [Finset.sum_Icc_of_even_eq_range heven]
  push_cast
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_sixth_rat n)
  push_cast at h
  rw [h]
  norm_num
  ring


private theorem threshold_lattice_fourth_moment (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ latticeInterval n, (k : ℝ) ^ 4 *
      (((n : ℝ) ^ 2 - (k : ℝ) ^ 2) / normalizer n ((n : ℝ) ^ 2))) =
      ((n : ℝ) ^ 2 - 1) * (3 * (n : ℝ) ^ 2 - 5) / 35 := by
  have hz := (normalizer_pos n hn le_rfl).ne'
  simp_rw [← mul_div_assoc, mul_sub, ← pow_add]
  norm_num
  rw [← sum_div, sum_sub_distrib, ← sum_mul, sum_lattice_fourth]
  change (_ - (∑ k ∈ Icc (-(n : ℤ)) (n : ℤ), (k : ℝ) ^ 6)) /
      normalizer n ((n : ℝ) ^ 2) = _
  rw [sum_centered_sixth, div_eq_iff hz, normalizer_formula]
  ring

private theorem shared_gram_at_zero {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ)
    (row a : ι → ℝ) (k : ℝ) (hzero : row ⬝ᵥ a = 0) :
    (G + k • vecMulVec row row) *ᵥ a = G *ᵥ a := by
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, hzero]
  simp

private theorem affine_switch {κ : Type*} {l : Filter κ}
    {s r b : κ → ℝ} {r₀ b₀ : ℝ}
    (hs : ∀ᶠ k in l, 0 < s k) (hr : Tendsto r l (𝓝 r₀))
    (hb : Tendsto b l (𝓝 b₀)) (hb₀ : 0 < b₀) (m₀ : ℝ) :
    ∃ m : κ → ℝ, Tendsto (fun k => (m k - m₀) / s k) l (𝓝 (-r₀ / b₀)) ∧
      ∀ᶠ k in l, ∀ z : ℝ,
        ((s k * r k + (z - m₀) * b k = 0) ↔ z = m k) ∧
        ((0 < s k * r k + (z - m₀) * b k) ↔ m k < z) := by
  let m := fun k => m₀ - s k * (r k / b k)
  have hbpos : ∀ᶠ k in l, 0 < b k := hb.eventually (lt_mem_nhds hb₀)
  refine ⟨m, ?_, ?_⟩
  · apply ((hr.neg).div hb hb₀.ne').congr'
    filter_upwards [hs] with k hk
    dsimp [m]
    field_simp [hk.ne']
    ring
  · filter_upwards [hbpos] with k hk z
    have factor : s k * r k + (z - m₀) * b k = (z - m k) * b k := by
      dsimp [m]
      field_simp [hk.ne']
      ring
    rw [factor, mul_eq_zero, or_iff_left hk.ne', sub_eq_zero,
      mul_pos_iff_of_pos_right hk, sub_pos]
    exact ⟨Iff.rfl, Iff.rfl⟩

end D5.S3.Fourier.Asymptotics.CyclicActivationShift
