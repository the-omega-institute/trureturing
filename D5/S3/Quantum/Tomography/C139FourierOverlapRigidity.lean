/- GID: D5/S3/Quantum/Tomography/C139FourierOverlapRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/C139FourierOverlapRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three phase probes recover every complex cross term across a Fourier coordinate window. -/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.C139FourierOverlapRigidity

abbrev Qutrit := Fin 3 → ℂ
abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

private def probe (ζ : ℂ) : Fin 3 → Qutrit :=
  ![![1, -1, 0], ![0, 1, -1], ![1, -ζ, 0]]

private def sesq (v z : Qutrit) : ℂ := star v ⬝ᵥ z

private lemma phase_zero (ζ z : ℂ)
    (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hsζ : star ζ = ζ ^ 2)
    (huζ : star ζ * ζ = 1)
    (hread : ∀ r : Fin 3, 2 * Complex.re ((ζ ^ r.val) * z) = 0) :
    z = 0 := by
  have hzre : z.re = 0 := by
    have h0 := hread 0
    simpa using h0
  have hζim : ζ.im ≠ 0 := by
    intro him
    have hreal := congrArg Complex.re hζ
    simp [pow_two, Complex.mul_re, Complex.mul_im, him] at hreal
    nlinarith [sq_nonneg (2 * ζ.re + 1)]
  have hzprod : ζ.im * z.im = 0 := by
    have h1 := hread 1
    have h1' : 2 * (ζ.re * z.re - ζ.im * z.im) = 0 := by
      simpa only [Fin.val_one, pow_one, Complex.mul_re] using h1
    rw [hzre] at h1'
    nlinarith [h1']
  have hzim : z.im = 0 := (mul_eq_zero.mp hzprod).resolve_left hζim
  simpa using (Complex.ext hzre hzim)

/-- The nine common unit probes determine the complete complex cross-term vector.

This is the finite algebraic core of AURIC C139, Theorem 1.4: the three probe
directions separate the three coordinates, while the three phase readouts
separate a complex scalar into its two real components. -/
theorem nine_phase_probes_recover_cross_term
    (ζ : ℂ) (B : QutritMatrix) (x y : Qutrit)
    (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hsζ : star ζ = ζ ^ 2)
    (huζ : star ζ * ζ = 1)
    (hB : Bᴴ * B = 1)
    (hread : ∀ (i r : Fin 3),
      2 * Complex.re (ζ ^ r.val * sesq (probe ζ i) (x - B *ᵥ y)) = 0) :
    x = B *ᵥ y ∧ y = Bᴴ *ᵥ x := by
  let z : Qutrit := x - B *ᵥ y
  have hprobe (i : Fin 3) : sesq (probe ζ i) z = 0 := by
    apply phase_zero ζ (sesq (probe ζ i) z) hζ hsζ huζ
    intro r
    simpa [z] using hread i r
  have h01 : z 0 = z 1 := by
    have h := hprobe 0
    have h' : z 0 - z 1 = 0 := by
      simpa [sesq, probe, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg] using h
    exact sub_eq_zero.mp h'
  have h12 : z 1 = z 2 := by
    have h := hprobe 1
    have h' : z 1 - z 2 = 0 := by
      simpa [sesq, probe, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg] using h
    exact sub_eq_zero.mp h'
  have h02 : z 0 = star ζ * z 1 := by
    have h := hprobe 2
    have h' : z 0 - star ζ * z 1 = 0 := by
      simpa [sesq, probe, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg] using h
    exact sub_eq_zero.mp h'
  have hζne : star ζ - 1 ≠ 0 := by
    intro h
    have hstar : star ζ = 1 := sub_eq_zero.mp h
    have hzeta : ζ = 1 := by
      have hstar' := congrArg star hstar
      simpa using hstar'
    rw [hzeta] at hζ
    norm_num at hζ
  have hz1 : z 1 = 0 := by
    have hmul : (star ζ - 1) * z 1 = 0 := by
      calc
        (star ζ - 1) * z 1 = star ζ * z 1 - z 1 := by ring
        _ = z 0 - z 0 := by rw [← h02, ← h01]
        _ = 0 := sub_self _
    exact (mul_eq_zero.mp hmul).resolve_left hζne
  have hz0 : z 0 = 0 := by
    calc z 0 = z 1 := h01
      _ = 0 := hz1
  have hz2 : z 2 = 0 := by
    calc z 2 = z 1 := h12.symm
      _ = 0 := hz1
  have hz : z = 0 := by
    funext i
    fin_cases i <;> assumption
  have hxy : x = B *ᵥ y := by
    simpa [z] using sub_eq_zero.mp hz
  refine ⟨hxy, ?_⟩
  calc
    y = (1 : QutritMatrix) *ᵥ y := by simp
    _ = (Bᴴ * B) *ᵥ y := by rw [hB]
    _ = Bᴴ *ᵥ (B *ᵥ y) := by rw [Matrix.mulVec_mulVec]
    _ = Bᴴ *ᵥ x := by rw [hxy]

#print axioms nine_phase_probes_recover_cross_term

end D5.S3.Quantum.Tomography.C139FourierOverlapRigidity
