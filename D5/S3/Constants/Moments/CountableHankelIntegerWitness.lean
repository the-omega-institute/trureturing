/- GID: D5/S3/Constants/Moments/CountableHankelIntegerWitness
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/CountableHankelIntegerWitness
   mirror-E: none(waiver:countable-spectrum-classical-analysis)
   anchors: []
   utility: none
   digest: Rational density and exact homogeneous scaling integerize complete spectral negative witnesses. -/

import D5.S3.Constants.Moments.CountableHankelNegativeWitness

/-!
Finite-dimensional continuity is applied to the complete absolutely convergent
moment form. Clearing denominators multiplies that same form by a positive
square, without changing the spectral family.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Polynomial
open scoped BigOperators ComplexConjugate

namespace D5.S3.Constants.Moments.CountableHankelNegativeWitness

private theorem moment_summable {ι : Type*} (z w : ι → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hw : Summable (fun i => ‖w i‖)) (k : ℕ) :
    Summable (fun i => w i * z i ^ k) := by
  apply Summable.of_norm_bounded hw
  intro i
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz i))

theorem quadratic_identity {ι : Type*} (z w : ι → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hw : Summable (fun i => ‖w i‖))
    (N : ℕ) (u : Fin (N + 1) → ℝ) :
    (∑' i, w i * (∑ a : Fin (N + 1), (u a : ℂ) * z i ^ (a : ℕ)) ^ 2).re =
      ∑ a : Fin (N + 1), ∑ b : Fin (N + 1), u a * u b *
        (∑' i, w i * z i ^ ((a : ℕ) + (b : ℕ))).re := by
  classical
  have hs := hasSum_sum (s := (Finset.univ : Finset (Fin (N + 1)))) (fun a _ =>
    hasSum_sum (s := (Finset.univ : Finset (Fin (N + 1)))) (fun b _ =>
      (moment_summable z w hz hw ((a : ℕ) + (b : ℕ))).hasSum.mul_left
        ((u a : ℂ) * (u b : ℂ))))
  have hid (i : ι) : w i * (∑ a : Fin (N + 1), (u a : ℂ) * z i ^ (a : ℕ)) ^ 2 =
      ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
        ((u a : ℂ) * (u b : ℂ)) * (w i * z i ^ ((a : ℕ) + (b : ℕ))) := by
    rw [pow_two]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [pow_add]
    ring
  rw [(hs.congr_fun hid).tsum_eq]
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- A nonreal node with nonzero weight produces a finite integer coefficient
vector whose complete weighted ordinary-square sum has negative real part. -/
theorem exists_integer_negative {ι : Type*} (z w : ι → ℂ)
    (c : Equiv.Perm ι) (hz : ∀ i, ‖z i‖ ≤ 1)
    (hzi : Function.Injective z) (hzc : ∀ i, z (c i) = conj (z i))
    (hwc : ∀ i, w (c i) = conj (w i))
    (hw : Summable (fun i => ‖w i‖))
    (hfinite : ∀ r : ℝ, 0 < r → {i | r ≤ ‖z i‖}.Finite)
    (i₀ : ι) (hni : conj (z i₀) ≠ z i₀) (hw₀ : w i₀ ≠ 0) :
    ∃ N : ℕ, ∃ u : Fin (N + 1) → ℤ,
      (∑' i, w i * (∑ a : Fin (N + 1), (u a : ℂ) * z i ^ (a : ℕ)) ^ 2).re < 0 := by
  obtain ⟨p, hp⟩ := exists_real_negative z w c hz hzi hzc hwc hw hfinite i₀ hni hw₀
  let N := p.natDegree
  let u : Fin (N + 1) → ℝ := fun a => p.coeff a
  have heval (x : ℂ) : p.eval₂ Complex.ofRealHom x =
      ∑ a : Fin (N + 1), (u a : ℂ) * x ^ (a : ℕ) := by
    rw [Polynomial.eval₂_eq_sum_range]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  simp_rw [heval] at hp
  rw [quadratic_identity z w hz hw N u] at hp
  obtain ⟨v, hv⟩ := exists_integer_negative_quadratic
    (fun a b : Fin (N + 1) => (∑' i, w i * z i ^ ((a : ℕ) + (b : ℕ))).re) u hp
  refine ⟨N, v, ?_⟩
  have hid := quadratic_identity z w hz hw N (fun a => (v a : ℝ))
  simp only [Complex.ofReal_intCast] at hid
  rw [hid]
  exact hv

end D5.S3.Constants.Moments.CountableHankelNegativeWitness
