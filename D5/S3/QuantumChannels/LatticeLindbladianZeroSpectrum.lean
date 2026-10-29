/- GID: D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/LatticeLindbladianZeroSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Finite-range translation-invariant lattice Lindbladians have zero in their spectrum. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

noncomputable section

namespace D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum

/-- Hilbert--Schmidt kernels in the position basis on the integer lattice. -/
abbrev Kernel := lp (fun _ : ℤ × ℤ => ℂ) 2

/-- Matrix support of the Hamiltonian and the localized jump operators. -/
def IsFiniteRange (r : ℕ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ) : Prop :=
  (∀ x y, (r : ℤ) < |x - y| → h x y = 0) ∧
  (∀ k x y, (r : ℤ) < max |x - k| |y - k| → ℓ k x y = 0)

/-- Simultaneous translation of all matrix indices by one lattice site. -/
def IsTranslationInvariant (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ) : Prop :=
  (∀ x y, h (x + 1) (y + 1) = h x y) ∧
  (∀ k x y, ℓ (k + 1) (x + 1) (y + 1) = ℓ k x y)

/-- The Lindblad generator in matrix elements; all index sums are unconditional sums. -/
def lindbladEntry (g : ℝ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (ρ : ℤ × ℤ → ℂ) (x y : ℤ) : ℂ :=
  -Complex.I * ((∑' z, h x z * ρ (z, y)) - ∑' z, ρ (x, z) * h z y) +
    (g : ℂ) * ∑' k,
      ((∑' u, ∑' v, ℓ k x u * ρ (u, v) * star (ℓ k y v)) -
        (1 / 2 : ℂ) * ∑' z, (∑' w, star (ℓ k w x) * ℓ k w z) * ρ (z, y) -
        (1 / 2 : ℂ) * ∑' z, ρ (x, z) * (∑' w, star (ℓ k w z) * ℓ k w y))

private lemma h_difference (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (ht : IsTranslationInvariant h ℓ) (x y : ℤ) : h x y = h 0 (y - x) := by
  sorry

private lemma jump_difference (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (ht : IsTranslationInvariant h ℓ) (k x y : ℤ) :
    ℓ k x y = ℓ 0 (x - k) (y - k) := by
  sorry

private lemma matrix_bound (r : ℕ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (hf : IsFiniteRange r h ℓ) (ht : IsTranslationInvariant h ℓ) :
    ∃ m : ℝ, 0 ≤ m ∧ (∀ x y, ‖h x y‖ ≤ m) ∧ (∀ k x y, ‖ℓ k x y‖ ≤ m) := by
  sorry

private lemma weighted_shift_exists (w : ℤ × ℤ) (c : ℤ × ℤ → ℂ) (m : ℝ)
    (hm : 0 ≤ m) (hc : ∀ p, ‖c p‖ ≤ m) :
    ∃ t : Kernel →L[ℂ] Kernel,
      (∀ ρ p, t ρ p = c p * ρ (p + w)) ∧ ‖t‖ ≤ m := by
  sorry

private def coefficient (g : ℝ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (w p : ℤ × ℤ) : ℂ :=
  lindbladEntry g h ℓ (Pi.single (p + w) 1) p.1 p.2

private lemma finite_window (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ) (ρ : Kernel) (p : ℤ × ℤ) :
    lindbladEntry g h ℓ ρ p.1 p.2 =
      ∑ w ∈ (Finset.Icc (-(2 * r : ℤ)) (2 * r) ×ˢ
        Finset.Icc (-(2 * r : ℤ)) (2 * r)), coefficient g h ℓ w p * ρ (p + w) := by
  sorry

private lemma coefficient_bound (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ht : IsTranslationInvariant h ℓ) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ w p, ‖coefficient g h ℓ w p‖ ≤ m := by
  sorry

private lemma bounded_operator (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ht : IsTranslationInvariant h ℓ) :
    ∃ t : Kernel →L[ℂ] Kernel, ∀ ρ : Kernel, ∀ x y,
      t ρ (x, y) = lindbladEntry g h ℓ ρ x y := by
  sorry

private def projection (n : ℕ) : Kernel :=
  ∑ x ∈ Finset.Icc (-(n : ℤ)) n, lp.single 2 (x, x) 1

private lemma projection_norm_sq (n : ℕ) : ‖projection n‖ ^ 2 = 2 * (n : ℝ) + 1 := by
  sorry

private lemma projection_trace (n : ℕ) (ρ : Kernel) :
    inner ℂ (projection n) ρ = ∑ x ∈ Finset.Icc (-(n : ℤ)) n, ρ (x, x) := by
  sorry

private lemma boundary_estimate (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ)
    (ℓ : ℤ → ℤ → ℤ → ℂ) (hf : IsFiniteRange r h ℓ)
    (ht : IsTranslationInvariant h ℓ) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ (n : ℕ) (ρ : Kernel),
      ‖∑ x ∈ Finset.Icc (-(n : ℤ)) n, lindbladEntry g h ℓ ρ x x‖ ≤ k * ‖ρ‖ := by
  sorry

private lemma nonunit_from_boundary (t : Kernel →L[ℂ] Kernel)
    (hb : ∃ k : ℝ, 0 ≤ k ∧ ∀ (n : ℕ) (ρ : Kernel),
      ‖inner ℂ (projection n) (t ρ)‖ ≤ k * ‖ρ‖) : ¬IsUnit t := by
  sorry

/-- The finite-range translation-invariant matrix Lindbladian is bounded and has spectral zero. -/
theorem result (r : ℕ) (g : ℝ) (h : ℤ → ℤ → ℂ) (ℓ : ℤ → ℤ → ℤ → ℂ)
    (hf : IsFiniteRange r h ℓ) (ht : IsTranslationInvariant h ℓ) :
    ∃ t : Kernel →L[ℂ] Kernel,
      (∀ ρ : Kernel, ∀ x y, t ρ (x, y) = lindbladEntry g h ℓ ρ x y) ∧
      (0 : ℂ) ∈ spectrum ℂ t := by
  obtain ⟨t, he⟩ := bounded_operator r g h ℓ hf ht
  refine ⟨t, he, spectrum.zero_mem_iff.mpr (nonunit_from_boundary t ?_)⟩
  obtain ⟨k, hk, hb⟩ := boundary_estimate r g h ℓ hf ht
  refine ⟨k, hk, ?_⟩
  intro n ρ
  rw [projection_trace]
  simpa only [he] using hb n ρ

end D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum
