/- GID: D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicSharpLongCrossing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp singleton-pair crossing bound for the two physical signed CAR jumps. -/

import D5.S3.Quantum.Semigroups.WuCubicRankTwoCut
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-!
# Sharp long crossing for one physical singleton pair

For two columns of a complex unitary frame, the even and odd CAR minors obey
the determinant identity from `WuCubicRankTwoCut`.  Cauchy--Schwarz on the two
minors gives the exact lower bound

`(sqrt ((1 - t) * s) - sqrt (t * (1 - s))) ^ 2`.

The product form is stated without dividing by `t + s`, so it includes the
zero-mass endpoint.  The real extremizer uses the necessary relative CAR phase
between the two odd coordinates.  With both coefficients positive, as in the
literal pair `sqrt (1 - s) e₃ + sqrt s e₂`, the same frame gives `(P + Q)^2`.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing

open WuCubicDirectedOccupationCap (Mat frameVector frameWeight frameWeight_eq_jumpWeight
  evenProbability oddProbability emptyProbability fullProbability jumpWeight)

open private lowering_amplitudes odd_eq_one_sub_even from
  D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
open private evenMinor oddMinor jumpWeight_add_swap normSq_minor_add_inner from
  D5.S3.Quantum.Semigroups.WuCubicRankTwoCut

private theorem odd_mass_mem (U : unitary Mat) (i : Fin 4) :
    oddProbability (frameVector U i) ∈ Set.Icc (0 : ℝ) 1 := by
  have ho : 0 ≤ oddProbability (frameVector U i) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have he : 0 ≤ evenProbability (frameVector U i) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have h := odd_eq_one_sub_even U i
  exact ⟨ho, by linarith only [h, he]⟩

/-- The even determinant minor is bounded by the product of the even masses. -/
private theorem even_minor_mass_le (x y : Fin 4 → ℂ) :
    Complex.normSq (evenMinor x y) ≤ evenProbability x * evenProbability y := by
  have h := normSq_minor_add_inner (x 0) (x 3) (y 0) (y 3)
  change Complex.normSq (evenMinor x y) + _ =
    evenProbability x * evenProbability y at h
  exact (le_add_of_nonneg_right (Complex.normSq_nonneg _)).trans_eq h

/-- The odd determinant minor is bounded by the product of the odd masses. -/
private theorem odd_minor_mass_le (x y : Fin 4 → ℂ) :
    Complex.normSq (oddMinor x y) ≤ oddProbability x * oddProbability y := by
  have h := normSq_minor_add_inner (x 1) (x 2) (y 1) (y 2)
  change Complex.normSq (oddMinor x y) + _ =
    oddProbability x * oddProbability y at h
  exact (le_add_of_nonneg_right (Complex.normSq_nonneg _)).trans_eq h

private theorem singleton_pair_radical_of_masses (x y : Fin 4 → ℂ) :
    (Real.sqrt (evenProbability x * oddProbability y) -
        Real.sqrt (oddProbability x * evenProbability y)) ^ 2 ≤
      jumpWeight x y + jumpWeight y x := by
  let a := evenProbability x * oddProbability y
  let b := oddProbability x * evenProbability y
  let z := conj (evenMinor x y) * oddMinor x y
  have hEx : 0 ≤ evenProbability x :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hEy : 0 ≤ evenProbability y :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hOx : 0 ≤ oddProbability x :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hOy : 0 ≤ oddProbability y :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have ha : 0 ≤ a := mul_nonneg hEx hOy
  have hb : 0 ≤ b := mul_nonneg hOx hEy
  have hz : z.re ^ 2 ≤ a * b := by
    calc
      z.re ^ 2 ≤ Complex.normSq z := by
        simpa only [pow_two] using Complex.re_sq_le_normSq z
      _ = Complex.normSq (evenMinor x y) * Complex.normSq (oddMinor x y) := by
        simp only [z, Complex.normSq_mul, Complex.normSq_conj]
      _ ≤ (evenProbability x * evenProbability y) *
          (oddProbability x * oddProbability y) := by
        exact mul_le_mul (even_minor_mass_le x y) (odd_minor_mass_le x y)
          (Complex.normSq_nonneg _) (mul_nonneg hEx hEy)
      _ = a * b := by
        dsimp only [a, b]
        ring
  have hsq : (2 * z.re) ^ 2 ≤
      (2 * Real.sqrt a * Real.sqrt b) ^ 2 := by
    have ha' : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
    have hb' : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
    have hab' : (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
      rw [mul_pow, ha', hb']
    nlinarith only [hz, hab']
  have hcross : -(2 * Real.sqrt a * Real.sqrt b) ≤ 2 * z.re := by
    exact (abs_le_of_sq_le_sq' hsq
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))).1
  have hquad : (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a + b + 2 * z.re := by
    have ha' : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
    have hb' : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
    nlinarith only [hcross, ha', hb']
  have hsum : jumpWeight x y + jumpWeight y x = a + b + 2 * z.re := by
    simpa only [a, b, z] using jumpWeight_add_swap x y
  rw [← hsum] at hquad
  exact hquad

/- The two square roots in the physical statement are the even--odd mass
   products of the two columns. -/
theorem singletonPairWeight_ge_radical (U : unitary Mat) (i j : Fin 4) :
    let t := oddProbability (frameVector U i)
    let s := oddProbability (frameVector U j)
    let P := Real.sqrt ((1 - t) * s)
    let Q := Real.sqrt (t * (1 - s))
    (P - Q) ^ 2 ≤ frameWeight U i j + frameWeight U j i := by
  dsimp only
  let x := frameVector U i
  let y := frameVector U j
  have hxi := odd_eq_one_sub_even U i
  have hyj := odd_eq_one_sub_even U j
  change oddProbability x = 1 - evenProbability x at hxi
  change oddProbability y = 1 - evenProbability y at hyj
  have hx : evenProbability x = 1 - oddProbability x := by
    linarith only [hxi]
  have hy : evenProbability y = 1 - oddProbability y := by
    linarith only [hyj]
  have h := singleton_pair_radical_of_masses x y
  rw [hx, hy] at h
  simpa only [x, y, frameWeight_eq_jumpWeight] using h

private theorem radical_product_bound {t s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (t - s) ^ 2 ≤ 2 * (t + s) *
      (Real.sqrt ((1 - t) * s) - Real.sqrt (t * (1 - s))) ^ 2 := by
  by_cases hzero : t + s = 0
  · have ht0 : t = 0 := by linarith only [ht.1, hs.1, hzero]
    have hs0 : s = 0 := by linarith only [ht.1, hs.1, hzero]
    simp [ht0, hs0]
  · let P := Real.sqrt ((1 - t) * s)
    let Q := Real.sqrt (t * (1 - s))
    have hP0 : 0 ≤ P := Real.sqrt_nonneg _
    have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
    have hP2 : P ^ 2 = (1 - t) * s := by
      dsimp only [P]
      rw [Real.sq_sqrt]
      exact mul_nonneg (sub_nonneg.mpr ht.2) hs.1
    have hQ2 : Q ^ 2 = t * (1 - s) := by
      dsimp only [Q]
      rw [Real.sq_sqrt]
      exact mul_nonneg ht.1 (sub_nonneg.mpr hs.2)
    have hsum_sq : (P + Q) ^ 2 ≤ 2 * (t + s) := by
      have hts : 0 ≤ t * s := mul_nonneg ht.1 hs.1
      nlinarith only [sq_nonneg (P - Q), hP2, hQ2, hts]
    have hfactor : (t - s) ^ 2 = (P - Q) ^ 2 * (P + Q) ^ 2 := by
      have hdiff : t - s = Q ^ 2 - P ^ 2 := by
        nlinarith only [hP2, hQ2]
      calc
        (t - s) ^ 2 = (Q ^ 2 - P ^ 2) ^ 2 := by rw [hdiff]
        _ = (P - Q) ^ 2 * (P + Q) ^ 2 := by ring
    have hmul := mul_le_mul_of_nonneg_left hsum_sq (sq_nonneg (P - Q))
    dsimp only [P, Q] at hfactor hmul ⊢
    nlinarith only [hfactor, hmul]

theorem singletonPairWeight_ge_product (U : unitary Mat) (i j : Fin 4) :
    let t := oddProbability (frameVector U i)
    let s := oddProbability (frameVector U j)
    2 * (t + s) * (frameWeight U i j + frameWeight U j i) ≥ (t - s) ^ 2 := by
  dsimp only
  have ht := odd_mass_mem U i
  have hs := odd_mass_mem U j
  have hrad := radical_product_bound ht hs
  have hnonneg : 0 ≤ 2 *
      (oddProbability (frameVector U i) + oddProbability (frameVector U j)) := by
    nlinarith only [ht.1, hs.1]
  have hmul := mul_le_mul_of_nonneg_left
    (singletonPairWeight_ge_radical U i j) hnonneg
  nlinarith only [hrad, hmul]

/- The first two columns are
   `sqrt (1 - t) e₀ + sqrt t e₁` and
   `sqrt (1 - s) e₃ - sqrt s e₂`.  The last two columns are their
   real orthogonal complements in the two coordinate planes. -/
private def sharpPairMatrix (t s : ℝ) : Mat :=
  !![↑(Real.sqrt (1 - t)), 0, -↑(Real.sqrt t), 0;
    ↑(Real.sqrt t), 0, ↑(Real.sqrt (1 - t)), 0;
    0, -↑(Real.sqrt s), 0, ↑(Real.sqrt (1 - s));
    0, ↑(Real.sqrt (1 - s)), 0, ↑(Real.sqrt s)]

private def sharpPairFrame {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : unitary Mat := by
  refine ⟨sharpPairMatrix t s, Unitary.mem_iff.mpr ⟨?_, ?_⟩⟩
  all_goals
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [sharpPairMatrix, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
        Fin.sum_univ_four, Complex.star_def, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im] <;>
      nlinarith only [Real.sq_sqrt ht.1, Real.sq_sqrt (sub_nonneg.mpr ht.2),
        Real.sq_sqrt hs.1, Real.sq_sqrt (sub_nonneg.mpr hs.2)]

theorem singletonPairWeight_radical_attained {t s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∃ U : unitary Mat,
      oddProbability (frameVector U 0) = t ∧
      oddProbability (frameVector U 1) = s ∧
      frameWeight U 0 1 + frameWeight U 1 0 =
        (Real.sqrt ((1 - t) * s) - Real.sqrt (t * (1 - s))) ^ 2 := by
  let U := sharpPairFrame ht hs
  have h0 : oddProbability (frameVector U 0) = t := by
    norm_num [oddProbability, frameVector, U, sharpPairFrame, sharpPairMatrix,
      Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt ht.1]
  have h1 : oddProbability (frameVector U 1) = s := by
    norm_num [oddProbability, frameVector, U, sharpPairFrame, sharpPairMatrix,
      Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt hs.1]
  have hP : Real.sqrt ((1 - t) * s) =
      Real.sqrt (1 - t) * Real.sqrt s := by
    rw [Real.sqrt_mul (sub_nonneg.mpr ht.2)]
  have hQ : Real.sqrt (t * (1 - s)) =
      Real.sqrt t * Real.sqrt (1 - s) := by
    rw [Real.sqrt_mul ht.1]
  have hw : frameWeight U 0 1 + frameWeight U 1 0 =
      (Real.sqrt (1 - t) * Real.sqrt s -
        Real.sqrt t * Real.sqrt (1 - s)) ^ 2 := by
    rw [frameWeight_eq_jumpWeight, frameWeight_eq_jumpWeight]
    obtain ⟨hxy₀, hxy₁⟩ := lowering_amplitudes (frameVector U 0) (frameVector U 1)
    obtain ⟨hyx₀, hyx₁⟩ := lowering_amplitudes (frameVector U 1) (frameVector U 0)
    simp only [jumpWeight, Fin.sum_univ_two, hxy₀, hxy₁, hyx₀, hyx₁]
    norm_num [frameVector, U, sharpPairFrame, sharpPairMatrix,
      Complex.normSq_apply, Complex.star_def, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt ht.1,
      Real.sq_sqrt (sub_nonneg.mpr ht.2), Real.sq_sqrt hs.1,
      Real.sq_sqrt (sub_nonneg.mpr hs.2)] <;> ring
  refine ⟨U, h0, h1, ?_⟩
  rw [hP, hQ]
  exact hw

end D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
