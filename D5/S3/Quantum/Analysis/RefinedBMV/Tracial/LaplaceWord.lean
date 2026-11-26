/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/LaplaceWord
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Orthant Laplace moments of the normalized four-copy word mean. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.LaplaceFourth
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

namespace RefinedBMV.Tracial

open Matrix MeasureTheory Set FourCopyGap
open scoped BigOperators

open private contract eigenDiagonal gapTrace gapTrace_diagonal gaps_card_pos monomial
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def fourRates (a b c d : ℝ) : Fin 4 → ℝ := ![a, b, c, d]

private def raisedGap (g : Gap) : Gap :=
  (g.1 + 1, g.2.1 + 1, g.2.2.1 + 1, g.2.2.2 + 1)

private def orthantMoment (m : ℕ) (r : Fin 4 → ℝ) : ℝ :=
  ∫ x : Fin 4 → ℝ, (∑ i, x i) ^ m * Real.exp (-(∑ i, r i * x i))
    ∂(Measure.pi fun _ : Fin 4 ↦ volume.restrict (Ioi (0 : ℝ)))

private theorem orthantMoment_eq_gaps (m : ℕ) {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    orthantMoment m (fourRates a b c d) = (m.factorial : ℝ) *
      ∑ g ∈ gaps m, monomial a⁻¹ b⁻¹ c⁻¹ d⁻¹ (raisedGap g) := by
  have hr (i : Fin 4) : 0 < fourRates a b c d i := by
    fin_cases i <;> assumption
  unfold orthantMoment
  rw [integral_orthant_sum_pow_mul_exp _ _ hr]
  congr 1
  apply Finset.sum_nbij' (fun g : Fin 4 → ℕ ↦ (g 0, g 1, g 2, g 3))
    (fun g : Gap ↦ ![g.1, g.2.1, g.2.2.1, g.2.2.2])
  · intro g hg
    exact mem_gaps.mpr (by simpa only [Fin.sum_univ_four] using (Finset.mem_piAntidiag.mp hg).1)
  · intro g hg
    refine Finset.mem_piAntidiag.mpr ⟨?_, fun i _ ↦ Finset.mem_univ i⟩
    simpa [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three] using mem_gaps.mp hg
  · intro g _
    funext i
    fin_cases i <;> rfl
  · rintro ⟨u, v, w, z⟩ _
    rfl
  · intro g _
    simp [Fin.prod_univ_four, monomial, raisedGap, fourRates,
      Matrix.cons_val_two, Matrix.cons_val_three]
    ring

/-- The four-variable orthant moment contracted against the spectral trace
cycles of the second factor. -/
def fourthOrthantLaplaceMoment (m : ℕ) (a : ι → ℝ) (B : Matrix ι ι ℂ) : ℂ :=
  contract (spectralBlock id B) fun i j k l ↦ (orthantMoment m
    (fourRates (a i) (a j) (a k) (a l)) : ℂ)

/-- The four-variable orthant integral equals the normalized word mean
at the inverse rates, with the exact radial Gamma normalization. -/
theorem fourthOrthantLaplaceMoment_eq_wordMean (m : ℕ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (B : Matrix ι ι ℂ) :
    let R := diagonal fun i ↦ ((a i)⁻¹ : ℂ)
    6 * fourthOrthantLaplaceMoment m a B =
      ((m + 3).factorial : ℂ) * FourCopyGap.wordMean m R (R * B) := by
  let R := diagonal fun i ↦ ((a i)⁻¹ : ℂ)
  let K (g : Gap) (i j k l : ι) : ℂ :=
    (monomial (a i)⁻¹ (a j)⁻¹ (a k)⁻¹ (a l)⁻¹ (raisedGap g) : ℂ)
  have htrace (g : Gap) : gapTrace R (R * B) g = contract (spectralBlock id B) (K g) := by
    calc
      _ = gapTrace R B (raisedGap g) := by simp only [gapTrace, raisedGap, pow_succ, mul_assoc]
      _ = _ := by
        simpa only [R, K, eigenDiagonal, id_eq, Complex.ofReal_inv] using
          gapTrace_diagonal id (fun i ↦ (a i)⁻¹) B (raisedGap g)
  have hscalar : (fun i j k l : ι ↦ (orthantMoment m
      (fourRates (a i) (a j) (a k) (a l)) : ℂ)) =
      (m.factorial : ℂ) • ∑ g ∈ gaps m, K g := by
    funext i j k l
    rw [orthantMoment_eq_gaps m (ha i) (ha j) (ha k) (ha l)]
    simp only [K, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hmoment : fourthOrthantLaplaceMoment m a B =
      (m.factorial : ℂ) * ∑ g ∈ gaps m, gapTrace R (R * B) g := by
    unfold fourthOrthantLaplaceMoment
    rw [hscalar, map_smul, map_sum]
    simp only [← htrace, smul_eq_mul]
  have hcard : ((gaps m).card : ℂ) ≠ 0 := by exact_mod_cast (gaps_card_pos m).ne'
  have hnat := Nat.choose_mul_factorial_mul_factorial
    (n := m + 3) (k := 3) (by omega)
  rw [show m + 3 - 3 = m by omega] at hnat
  have hfactorial : ((m + 3).factorial : ℂ) = 6 * (m.factorial : ℂ) * (gaps m).card := by
    rw [gaps_card]
    have hh : ((m + 3).choose 3 : ℂ) * (3 : ℕ).factorial * (m.factorial : ℂ) =
        ((m + 3).factorial : ℂ) := by exact_mod_cast hnat
    rw [← hh]
    norm_num [Nat.factorial]
    ring
  change 6 * fourthOrthantLaplaceMoment m a B =
    ((m + 3).factorial : ℂ) * FourCopyGap.wordMean m R (R * B)
  rw [hmoment, wordMean_eq_gaps, hfactorial]
  field_simp [hcard]

set_option maxHeartbeats 600000 in
-- Normalizing the four products under the trace exceeds the default heartbeat limit.
private theorem wordMean_diagonal_congruence (m : ℕ) (R S B : Matrix ι ι ℂ)
    (hR : S * S = R) : FourCopyGap.wordMean m R (R * B) = FourCopyGap.wordMean m R (S * B * S) := by
  have hs : Commute S R := by rw [← hR]; exact (Commute.refl S).mul_right (Commute.refl S)
  have h (v : ℕ) : S * R ^ v * S = R ^ v * R := by
    rw [(hs.pow_right v).eq, mul_assoc, hR]
  simp only [wordMean_eq_gaps]
  apply congrArg (fun value : ℂ ↦ value / (gaps m).card)
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  let U := R ^ g.1 * S * B * (S * R ^ g.2.1 * S) * B *
    (S * R ^ g.2.2.1 * S) * B * (S * R ^ g.2.2.2 * S) * B
  calc
    gapTrace R (R * B) g = trace (S * U) := by
      calc
        _ = trace ((R ^ g.1 * R) * B * (R ^ g.2.1 * R) * B *
            (R ^ g.2.2.1 * R) * B * (R ^ g.2.2.2 * R) * B) := by
          simp only [gapTrace, mul_assoc]
        _ = trace ((S * R ^ g.1 * S) * B * (S * R ^ g.2.1 * S) * B *
            (S * R ^ g.2.2.1 * S) * B * (S * R ^ g.2.2.2 * S) * B) := by
          simp only [h]
        _ = _ := by simp only [U, mul_assoc]
    _ = trace (U * S) := trace_mul_comm _ _
    _ = gapTrace R (S * B * S) g := by simp only [gapTrace, U, mul_assoc]

/-- In a Hermitian presentation, the second factor of the orthant word
mean is the congruence by the square root of the inverse rate matrix. -/
theorem fourthOrthantLaplaceMoment_eq_congruence_wordMean (m : ℕ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (B : Matrix ι ι ℂ) :
    let R := diagonal fun i ↦ ((a i)⁻¹ : ℂ)
    let S := diagonal fun i ↦ (Real.sqrt ((a i)⁻¹) : ℂ)
    6 * fourthOrthantLaplaceMoment m a B =
      ((m + 3).factorial : ℂ) * FourCopyGap.wordMean m R (S * B * S) := by
  let R := diagonal fun i ↦ ((a i)⁻¹ : ℂ)
  let S := diagonal fun i ↦ (Real.sqrt ((a i)⁻¹) : ℂ)
  have hR : S * S = R := by
    simp only [S, R, diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (inv_nonneg.mpr (ha i).le), Complex.ofReal_inv]
  change _ = ((m + 3).factorial : ℂ) * FourCopyGap.wordMean m R (S * B * S)
  rw [← wordMean_diagonal_congruence m R S B hR]
  exact fourthOrthantLaplaceMoment_eq_wordMean m a ha B

/-- A four-copy word bound at integer degree `m` controls the corresponding
balanced one-dimensional Laplace moment against the orthant moment. -/
theorem fourth_laplace_moment_le_orthant_of_word_bound (m : ℕ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (hword :
      let R := diagonal fun i ↦ ((a i)⁻¹ : ℂ)
      let S := diagonal fun i ↦ (Real.sqrt ((a i)⁻¹) : ℂ)
      let T := diagonal fun i ↦ ((a i ^ (-((m : ℝ) / 4)) : ℝ) : ℂ)
      (trace ((T * (S * B * S)) ^ 4)).re ≤ (FourCopyGap.wordMean m R (S * B * S)).re) :
    (∫ s in Ioi (0 : ℝ), s ^ ((m : ℝ) + 3) *
      (trace ((fourthLaplaceWeight a (fun _ ↦ 1) s * B) ^ 4)).re) ≤
        6 * (fourthOrthantLaplaceMoment m a B).re := by
  let R := diagonal fun i ↦ ((a i)⁻¹ : ℂ)
  let S := diagonal fun i ↦ (Real.sqrt ((a i)⁻¹) : ℂ)
  let E := diagonal fun i ↦ ((a i ^ (-((m : ℝ) / 8)) : ℝ) : ℂ)
  let T := diagonal fun i ↦ ((a i ^ (-((m : ℝ) / 4)) : ℝ) : ℂ)
  let C := S * B * S
  have hS : Sᴴ = S := by
    unfold S
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    exact Complex.conj_ofReal _
  have hE : E * E = T := by
    simp only [E, T, diagonal_mul_diagonal, ← Complex.ofReal_mul]
    congr 1
    funext i
    rw [← Real.rpow_add (ha i),
      show -((m : ℝ) / 8) + -((m : ℝ) / 8) = -((m : ℝ) / 4) by ring]
  have hC : C.IsHermitian := by
    change Cᴴ = C
    simp only [C, conjTranspose_mul, hS, hB.eq, mul_assoc]
  have hcycle (X Y : Matrix ι ι ℂ) : trace ((X * Y) ^ 4) = trace ((Y * X) ^ 4) := by
    rw [show (X * Y) ^ 4 = X * ((Y * X) ^ 3 * Y) by noncomm_ring, trace_mul_comm]
    congr 1
    noncomm_ring
  have hweight (s : ℝ) :
      S * fourthLaplaceWeight a a s * S = fourthLaplaceWeight a (fun _ ↦ 1) s := by
    simp only [S, fourthLaplaceWeight, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [← Complex.ofReal_mul]
    congr 1
    calc
      _ = (Real.sqrt ((a i)⁻¹) * Real.sqrt ((a i)⁻¹)) * a i *
          Real.exp (-(s * a i / 4)) := by ring
      _ = _ := by
        rw [Real.mul_self_sqrt (inv_nonneg.mpr (ha i).le), inv_mul_cancel₀ (ha i).ne', one_mul]
  have htrace (s : ℝ) :
      trace ((fourthLaplaceWeight a a s * C) ^ 4) =
        trace ((fourthLaplaceWeight a (fun _ ↦ 1) s * B) ^ 4) := by
    let P := fourthLaplaceWeight a a s
    calc
      _ = trace (((P * S * B) * S) ^ 4) := by simp only [P, C, mul_assoc]
      _ = trace ((S * (P * S * B)) ^ 4) := hcycle _ _
      _ = trace (((S * P * S) * B) ^ 4) := by simp only [mul_assoc]
      _ = _ := by rw [show S * P * S = _ from hweight s]
  have hmoment := fourth_laplace_moment_congruence_le (m : ℝ)
    (by linarith [Nat.cast_nonneg (α := ℝ) m]) a ha C hC
  change (∫ s in Ioi (0 : ℝ), s ^ ((m : ℝ) + 3) *
    (trace ((fourthLaplaceWeight a a s * C) ^ 4)).re) ≤
      Real.Gamma ((m : ℝ) + 4) * (trace ((E * C * E) ^ 4)).re at hmoment
  have hgamma : Real.Gamma ((m : ℝ) + 4) = ((m + 3).factorial : ℝ) := by
    rw [show (m : ℝ) + 4 = ((m + 3 : ℕ) : ℝ) + 1 by
      push_cast
      ring,
      Real.Gamma_nat_eq_factorial]
  simp_rw [htrace, hgamma] at hmoment
  have hort := congrArg Complex.re (fourthOrthantLaplaceMoment_eq_congruence_wordMean m a ha B)
  change (6 * fourthOrthantLaplaceMoment m a B).re =
    (((m + 3).factorial : ℂ) * FourCopyGap.wordMean m R C).re at hort
  have hsix_re : (6 : ℂ).re = 6 := by norm_num
  have hsix_im : (6 : ℂ).im = 0 := by norm_num
  simp only [Complex.mul_re, hsix_re, hsix_im, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] at hort
  have hword' : (trace ((E * C * E) ^ 4)).re ≤ (FourCopyGap.wordMean m R C).re := by
    have heq : trace ((E * C * E) ^ 4) = trace ((T * C) ^ 4) := by
      rw [hcycle (E * C) E, ← mul_assoc, hE]
    rw [heq]
    exact hword
  rw [hort]
  exact hmoment.trans (mul_le_mul_of_nonneg_left hword' (Nat.cast_nonneg _))

end

end RefinedBMV.Tracial
