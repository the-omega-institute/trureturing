/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmMinimality
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmMinimality
   mirror-E: none(waiver:universal-minimality-proof)
   anchors: []
   utility: none
   digest: Actual PGM minimality in dimension and label count, and limited pure control. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity
import D5.S3.Quantum.Measurement.EquiprobablePgmScores

/-!
The minimality and limited pure-pair geometry are from section 7 of the anonymous
mechanism manuscript (no license grant supplied). They do not settle the general
all-pure comparison. The Ma–Zhang unbounded family does not settle a comparison
with a quantitative positive spectral floor either. Those limits remain open.
Admission commitment: actual singleton and dimension-one scores, the actual
comparison for every nonempty label subset when N≤2, and the precise pure-pair
geometric obstruction, without promoting it to a general all-pure theorem.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.EquiprobablePgmMinimality
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore)
open D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity
open D5.S3.Quantum.Measurement.EquiprobablePgmScores (diagonal_score)

/-- Every singleton has exactly the original random-guessing score, even when its
state is singular. This includes the one-label endpoint of the valid bounds. -/
theorem singleton_score {d N : ℕ} (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hN : 0 < N) (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1)
    (i : Fin N) : pgmScore ρ {i} = 1 / (N : ℝ) := by
  have h := centered_identity ρ hN hρ htr {i} (Finset.singleton_nonempty i)
  dsimp only at h
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one,
    div_one, one_smul] at h
  have hσ : ((1 / (N : ℂ)) • ρ i).PosSemidef := by
    apply (hρ i).smul
    apply Complex.nonneg_iff.mpr
    constructor
    · simp only [one_div, Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast]
      positivity
    · simp
  rw [(support_quarter_normalization _ hσ).2, sub_self] at h
  have hz : RHLinalg.frobSq (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
    simp [RHLinalg.frobSq]
  rw [hz] at h
  exact sub_eq_zero.mp h

/-- In one dimension every nonempty restricted PGM score is exactly 1/N. -/
theorem dimension_one_score {N : ℕ}
    (ρ : Fin N → Matrix (Fin 1) (Fin 1) ℂ) (hN : 0 < N)
    (htr : ∀ i, trace (ρ i) = 1) (B : Finset (Fin N)) (hB : B.Nonempty) :
    pgmScore ρ B = 1 / (N : ℝ) := by
  have hrho : ρ = fun _ => diagonal (fun _ : Fin 1 => (1 : ℂ)) := by
    funext i
    ext x y
    fin_cases x
    fin_cases y
    simpa [trace, Fin.sum_univ_one] using htr i
  rw [hrho]
  have hdiag := diagonal_score hN (fun (_ : Fin N) (_ : Fin 1) => 1)
    (by intro i x; norm_num) B
  norm_num only [Complex.ofReal_one] at hdiag
  rw [hdiag]
  have hcard : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  simp [Fin.sum_univ_one, hcard]

/-- For at most two labels the original comparison holds for every nonempty
label set, hence for every actual optimum's active set. -/
theorem at_most_two_labels {d N : ℕ}
    (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ) (hN : 0 < N) (hN2 : N ≤ 2)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1)
    (B : Finset (Fin N)) (hB : B.Nonempty) :
    ((B.card : ℝ) - 1) * (pgmScore ρ B - 1 / (N : ℝ)) ≤
      ((N : ℝ) - 1) * (pgmScore ρ Finset.univ - 1 / (N : ℝ)) := by
  by_cases hc : B.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    rw [singleton_score ρ hN hρ htr i, sub_self, mul_zero]
    exact mul_nonneg (by
      have hx : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      linarith)
      (sub_nonneg.mpr (random_guessing_le ρ hN hρ htr Finset.univ
        ⟨⟨0, hN⟩, Finset.mem_univ _⟩))
  · have hcard := Finset.card_le_univ B
    have hpos := hB.card_pos
    simp only [Fintype.card_fin] at hcard
    have heq : B.card = N := by omega
    have hfull : B = Finset.univ := Finset.eq_univ_of_card B (by simpa only [Fintype.card_fin] using heq)
    subst B
    simp

/-- A pure omitted Bloch vector inside the pure symmetric pair's dual ball has
no larger weak population. This is a limited geometric control only. -/
theorem pure_pair_population (z x y w : ℝ) (hz : 0 < z) (hz1 : z < 1)
    (hpure : x ^ 2 + y ^ 2 + w ^ 2 = 1)
    (hball : x ^ 2 + y ^ 2 + (w - z) ^ 2 ≤ 1 - z ^ 2) :
    z ≤ w ∧ (1 - w) / 2 ≤ (1 - z) / 2 ∧ 0 < (1 - z) / 2 := by
  have hw : z ≤ w := by nlinarith
  exact ⟨hw, by linarith, by linarith⟩

end D5.S3.Quantum.Measurement.EquiprobablePgmMinimality
