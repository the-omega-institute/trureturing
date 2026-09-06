/- GID: D5/S3/Quantum/Tomography/TwoCirculantXSeed
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/TwoCirculantXSeed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Opposite unit-phase cubic root sums construct an order-six Hadamard seed for the certified completion patch. -/

import D5.S3.Quantum.Tomography.MUBHadamardCompatibility
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.LinearCombination

/- Reuse audit (2026-09-05):
   * Uses the lane's Mat6 and IsComplexHadamard, with no new matrix predicate.
   * Uses Matrix.circulant, Matrix.Fin.circulant_mul_comm, its adjoint formula,
     and Matrix.fromBlocks_multiply. The finite entry calculation below proves
     only the seed-specific Gram relation; circulant algebra is not rebuilt.
   * This supplies the algebraic input to x_quarter_seed/root_boxes.json.
     It does not claim the interval, Segre-degree, or completeness theorems
     have been admitted by the Lean kernel.
-/

open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.TwoCirculantXSeed

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility

/-- The X-construction seed with top block rows `(a,b,1)` and `(c,d,1)`.
The order of the circulant generator follows the library's `v(i-j)` convention. -/
def twoCirculantSeed (a b c d : ℂ) : Mat6 :=
  let A : Matrix (Fin 3) (Fin 3) ℂ := Matrix.circulant ![a, 1, b]
  let B : Matrix (Fin 3) (Fin 3) ℂ := Matrix.circulant ![c, 1, d]
  Matrix.fromBlocks A B Bᴴ (-Aᴴ)

private theorem mul_star_of_unit (z : ℂ) (hz : Complex.normSq z = 1) :
    z * star z = 1 := by
  simpa [Complex.star_def, hz] using Complex.mul_conj z

private theorem top_gram
    (a b c d : ℂ)
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hd : Complex.normSq d = 1)
    (hcycle : a * star b + b + star a + c * star d + d + star c = 0) :
    (Matrix.circulant ![a, 1, b]) * (Matrix.circulant ![a, 1, b])ᴴ +
      (Matrix.circulant ![c, 1, d]) * (Matrix.circulant ![c, 1, d])ᴴ =
      (6 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have ha' := mul_star_of_unit a ha
  have hb' := mul_star_of_unit b hb
  have hc' := mul_star_of_unit c hc
  have hd' := mul_star_of_unit d hd
  have hconj := congrArg (star : ℂ → ℂ) hcycle
  simp only [star_add, star_mul, star_star, star_zero] at hconj
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.circulant_apply, Fin.sum_univ_three, Matrix.smul_apply,
      Matrix.one_apply] <;>
    first
    | linear_combination ha' + hb' + hc' + hd'
    | linear_combination hcycle
    | linear_combination hconj

private theorem hadamard_of_cycle
    (a b c d : ℂ)
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hd : Complex.normSq d = 1)
    (hcycle : a * star b + b + star a + c * star d + d + star c = 0) :
    IsComplexHadamard (twoCirculantSeed a b c d) := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := Matrix.circulant ![a, 1, b]
  let B : Matrix (Fin 3) (Fin 3) ℂ := Matrix.circulant ![c, 1, d]
  have hTop : A * Aᴴ + B * Bᴴ = (6 : ℂ) • 1 :=
    top_gram a b c d ha hb hc hd hcycle
  have hAN : Aᴴ * A = A * Aᴴ := by
    dsimp [A]
    simp only [Matrix.Fin.conjTranspose_circulant]
    exact Matrix.Fin.circulant_mul_comm _ _
  have hBN : Bᴴ * B = B * Bᴴ := by
    dsimp [B]
    simp only [Matrix.Fin.conjTranspose_circulant]
    exact Matrix.Fin.circulant_mul_comm _ _
  have hAB : A * B = B * A := Matrix.Fin.circulant_mul_comm _ _
  have hAdjAB : Bᴴ * Aᴴ = Aᴴ * Bᴴ := by
    simpa only [Matrix.conjTranspose_mul] using
      congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ ↦ Mᴴ) hAB
  have hBottom : Bᴴ * B + Aᴴ * A = (6 : ℂ) • 1 := by
    rw [hBN, hAN, add_comm]
    exact hTop
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [twoCirculantSeed, Matrix.circulant_apply,
        Matrix.conjTranspose_apply, Complex.star_def,
        Complex.normSq_conj, ha, hb, hc, hd]
  · change (Matrix.fromBlocks A B Bᴴ (-Aᴴ)) *
        (Matrix.fromBlocks A B Bᴴ (-Aᴴ))ᴴ =
        (Fintype.card (Fin 3 ⊕ Fin 3) : ℂ) • 1
    norm_num only [Fintype.card_sum, Fintype.card_fin, Nat.cast_ofNat]
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      hTop, hBottom, hAB, hAdjAB, add_neg_cancel]
    calc
      Matrix.fromBlocks ((6 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) 0 0
          ((6 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) =
        (6 : ℂ) • Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 1 := by
          rw [Matrix.fromBlocks_smul]
          simp only [smul_zero]
      _ = (6 : ℂ) • 1 := by rw [Matrix.fromBlocks_one]

/-- Two triples of unit phases, each of product one and with opposite sums,
construct an order-six complex Hadamard matrix. These are precisely the Vieta
inputs supplied by the two Cayley cubics in the exact parameter-patch certificate.
No classification, numerical root count, or additional axiom is assumed. -/
theorem twoCirculantSeed_hadamard_of_opposite_phase_triples
    (r s : Fin 3 → ℂ)
    (hr : ∀ i, Complex.normSq (r i) = 1)
    (hs : ∀ i, Complex.normSq (s i) = 1)
    (hrprod : r 0 * r 1 * r 2 = 1)
    (hsprod : s 0 * s 1 * s 2 = 1)
    (hsum : r 0 + r 1 + r 2 + s 0 + s 1 + s 2 = 0) :
    IsComplexHadamard
      (twoCirculantSeed (r 0 * r 1) (r 1) (s 0 * s 1) (s 1)) := by
  have hr01 : Complex.normSq (r 0 * r 1) = 1 := by
    rw [Complex.normSq_mul, hr 0, hr 1, one_mul]
  have hs01 : Complex.normSq (s 0 * s 1) = 1 := by
    rw [Complex.normSq_mul, hs 0, hs 1, one_mul]
  have hrnz : r 0 * r 1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrprod
    exact zero_ne_one hrprod
  have hsnz : s 0 * s 1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsprod
    exact zero_ne_one hsprod
  have hrstar : star (r 0 * r 1) = r 2 := by
    apply mul_left_cancel₀ hrnz
    exact (mul_star_of_unit _ hr01).trans hrprod.symm
  have hsstar : star (s 0 * s 1) = s 2 := by
    apply mul_left_cancel₀ hsnz
    exact (mul_star_of_unit _ hs01).trans hsprod.symm
  apply hadamard_of_cycle _ _ _ _ hr01 (hr 1) hs01 (hs 1)
  simpa only [mul_assoc, mul_star_of_unit (r 1) (hr 1),
    mul_star_of_unit (s 1) (hs 1), mul_one, hrstar, hsstar] using hsum

#print axioms twoCirculantSeed_hadamard_of_opposite_phase_triples

end D5.S3.Quantum.Tomography.TwoCirculantXSeed
