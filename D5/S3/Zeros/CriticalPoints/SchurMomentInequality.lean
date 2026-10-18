/- GID: D5/S3/Zeros/CriticalPoints/SchurMomentInequality
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/SchurMomentInequality
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Hadamard]
   utility: none
   digest: Real Schur moments for a diagonal matrix between rank-one square roots. -/

import D5.S3.Zeros.CriticalPoints.SchurMomentNormalization
import D5.S3.Zeros.CriticalPoints.SchurStripBoundary
import D5.S3.Zeros.CriticalPoints.SchurStripCenter

/-! Three-lines interpolation controls the actual Schur diagonal, including equality. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.SchurMomentInequality

open Matrix Complex
open scoped ComplexConjugate
open RankOneComplexPowers SchurMomentNormalization SchurStripFunctions
open ThreeLinesSchurMoment SchurStripBoundary SchurStripCenter
open Complex.HadamardThreeLines

theorem spectral_bound_and_rigidity {n : ℕ} (hn : 0 < n) (b : Fin n → ℂ)
    (hb : ∀ j, b j ≠ 0) (p : ℝ) (hp : 1 ≤ p) :
    let S := ((TangZhangOrderMinusTwo.B b).charpoly.roots.map (fun μ => ‖μ‖ ^ p)).sum
    let M := ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, ‖b j‖ ^ p
    S ≤ M ∧ (1 < p → S = M → ∀ i j, b i = b j) := by
  dsimp only
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let t : Fin n → ℝ := fun j => ‖b j‖
  let u : Fin n → ℂ := fun j => b j / (t j : ℂ)
  have ht (j) : 0 < t j := norm_pos_iff.mpr (hb j)
  have hu (j) : ‖u j‖ = 1 := by
    simp [u, norm_div, Complex.norm_real, Real.norm_of_nonneg (ht j).le,
      div_self (ht j).ne', t]
  have hbu (j) : b j = u j * (t j : ℂ) := by
    exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ht j).ne')).symm
  obtain ⟨Q, hQ, hQ', htri⟩ := SchurFrobeniusInequality.triangularize n (A b)
  have hQu : Q ∈ Matrix.unitaryGroup (Fin n) ℂ := Unitary.mem_iff.mpr ⟨hQ, hQ'⟩
  let μ : Fin n → ℂ := fun k => (Qᴴ * A b * Q) k k
  have hμ : ∀ k, μ k ≠ 0 := schur_diagonal_ne_zero hn b hb Q hQu htri
  obtain ⟨N, ρ, v, hN, hρ, hv, hdecomp, hmass, hNp, hsum⟩ :=
    normalized_weights hn μ hμ p hp0
  let S : ℝ := ∑ k, ‖μ k‖ ^ p
  change N ^ p = S at hNp
  let M : ℝ := ((((n : ℝ) + 1) ^ p + n - 1) / n) * ∑ j, t j ^ p
  have hM : 0 < M := by
    have hbase : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
    have hpow := Real.one_lt_rpow hbase hp0
    have hcoeff : 0 < (((n : ℝ) + 1) ^ p + n - 1) / n :=
      div_pos (by have : (0 : ℝ) < n := Nat.cast_pos.mpr hn; linarith)
        (Nat.cast_pos.mpr hn)
    exact mul_pos hcoeff (Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (ht j) _)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩))
  let g : ℂ → ℂ := f n Q u v t ρ p
  have hgcenter : g ((1 / p : ℝ) : ℂ) = (N : ℂ) := by
    apply center_identity n Q u v b μ t ρ p N hp0 ht hρ hbu
    · intro k
      simp only [μ, A, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    · exact hsum
  have hnormcenter : ‖g ((1 / p : ℝ) : ℂ)‖ = N := by
    rw [hgcenter, Complex.norm_real, Real.norm_of_nonneg hN.le]
  have hright (y : ℝ) : ‖g (1 + (y : ℂ) * I)‖ ≤ M ∧
      (‖g (1 + (y : ℂ) * I)‖ = M →
        ∀ i j, u i * positivePower (t i) (((p * y : ℝ) : ℂ) * I) =
          u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I)) := by
    have h := right_boundary_bound_and_phases n hn u hu t ht p hp0 y
      (K n Q v ρ p (1 + (y : ℂ) * I)) (K_unitary_right n Q hQu v hv ρ p y)
    exact h
  have hstrip := f_strip n Q u v t ρ p
  have hinterp := strip_moment_bound_and_equality hM hstrip.differentiable.diffContOnCl
    hstrip.bddAbove (fun ζ hζ => by
      have he : ζ = (ζ.im : ℂ) * I := by apply Complex.ext <;> simp [hζ]
      rw [he]
      exact left_bound n hn Q hQu u v hu hv t ρ hρ p hmass ζ.im)
    (fun ζ hζ => by
      have he : ζ = 1 + (ζ.im : ℂ) * I := by apply Complex.ext <;> simp [hζ]
      rw [he]
      exact (hright ζ.im).1)
  have hθ0 : 0 < 1 / p := one_div_pos.mpr hp0
  have hθ1 : 1 / p ≤ 1 := (div_le_one hp0).mpr hp
  have hle : N ≤ M ^ (1 / p) := by
    have h := hinterp.1 ((1 / p : ℝ) : ℂ) ⟨hθ0.le, hθ1⟩
    change ‖g ((1 / p : ℝ) : ℂ)‖ ≤ M ^ (1 / p) at h
    rwa [hnormcenter] at h
  have hbound : S ≤ M := by
    have h := Real.rpow_le_rpow hN.le hle hp0.le
    rw [← Real.rpow_mul hM.le, one_div_mul_cancel hp0.ne', Real.rpow_one] at h
    exact hNp.symm.trans_le h
  have hspectral : ((TangZhangOrderMinusTwo.B b).charpoly.roots.map
      (fun μ => ‖μ‖ ^ p)).sum = S := by
    rw [← A_charpoly hn b]
    exact schur_roots_moment (A b) Q hQu htri p
  rw [hspectral]
  refine ⟨hbound, ?_⟩
  intro hp1 heq
  change S = M at heq
  have heqcenter : ‖g ((1 / p : ℝ) : ℂ)‖ = M ^ (1 / p) := by
    rw [hnormcenter, ← heq, ← hNp, ← Real.rpow_mul hN.le,
      mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hall : ∀ y : ℝ, ∀ i j,
      u i * positivePower (t i) (((p * y : ℝ) : ℂ) * I) =
        u j * positivePower (t j) (((p * y : ℝ) : ℂ) * I) := by
    intro y
    exact (hright y).2 (hinterp.2 (1 / p) hθ0 ((div_lt_one hp0).mpr hp1) heqcenter y)
  intro i j
  have hu0 : u i ≠ 0 := by
    intro h
    have hi := hu i
    simp only [h, norm_zero, zero_ne_one] at hi
  have hfreq : ∀ y : ℝ,
      u i * exp ((y : ℂ) * ((p * Real.log (t i) : ℝ) : ℂ) * I) =
        u j * exp ((y : ℂ) * ((p * Real.log (t j) : ℝ) : ℂ) * I) := by
    intro y
    convert hall y i j using 1 <;> unfold positivePower <;> congr 2 <;> push_cast <;> ring
  obtain ⟨huij, hlog⟩ := rotating_phase_injective hu0 hfreq
  have htij : t i = t j := Real.log_injOn_pos (ht i) (ht j) (mul_left_cancel₀ hp0.ne' hlog)
  rw [hbu i, hbu j, huij, htij]

end D5.S3.Zeros.CriticalPoints.SchurMomentInequality
