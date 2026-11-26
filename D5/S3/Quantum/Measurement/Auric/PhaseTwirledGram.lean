/- GID: D5/S3/Quantum/Measurement/Auric/PhaseTwirledGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/PhaseTwirledGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite diagonal phase average on rank-one Choi Gram matrices. -/

import D5.S3.Quantum.Measurement.Auric.FourthPhase
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

/-! # The finite diagonal phase average on rank-one Choi Gram matrices -/

namespace D5.S3.Quantum.Measurement.Auric.PhaseTwirledGram

open _root_.Matrix D5.S3.Quantum.Measurement.Auric.FourthPhase
open Finset
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

private def color (u i : n) : ℂ := if u = i then Complex.I else 1

private def phase (t : n → Fin 4) (i : n) : ℂ := ∏ u, color u i ^ (t u).val

omit [Fintype n] in
private theorem color_star_mul (u i : n) : star (color u i) * color u i = 1 := by
  by_cases h : u = i <;> simp [color, h, Complex.I_mul_I]

private theorem phase_star_mul (t : n → Fin 4) (i : n) : star (phase t i) * phase t i = 1 := by
  unfold phase
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro u _
  rw [star_pow, ← mul_pow, color_star_mul, one_pow]

/-- Each phase assignment is realized by an actual unitary on the same register. -/
def phaseUnitary (t : n → Fin 4) : Matrix.unitaryGroup n ℂ :=
  ⟨diagonal (phase t), by
    apply Matrix.mem_unitaryGroup_iff'.2
    change (diagonal (phase t))ᴴ * diagonal (phase t) = 1
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact phase_star_mul t i⟩

omit [Fintype n] in
private theorem color_character (u : n) (p : n × n) :
    color u p.1 * star (color u p.2) = character u p := by
  rcases p with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    rw [mul_comm, color_star_mul]
    simp [character]
  · by_cases hi : u = i
    · simp [color, character, hij, hi]
    · by_cases hj : u = j
      · subst u
        simp [color, character, hij, Ne.symm hij]
      · simp [color, character, hij, hi, hj]

private theorem phase_pair (t : n → Fin 4) (p : n × n) :
    phase t p.1 * star (phase t p.2) = ∏ u, character u p ^ (t u).val := by
  unfold phase
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u _
  rw [star_pow, ← mul_pow, color_character]

private def phaseGramCoefficient (t : n → Fin 4) (p q : n × n) : ℂ :=
  phase t p.1 * star (phase t p.2) * star (phase t q.1 * star (phase t q.2))

private theorem phaseGramCoefficient_eq (t : n → Fin 4) (p q : n × n) :
    phaseGramCoefficient t p q =
      ∏ u, (character u p * star (character u q)) ^ (t u).val := by
  unfold phaseGramCoefficient
  rw [phase_pair, phase_pair, star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u _
  rw [star_pow, mul_pow]

/-- The average over all phase assignments factors into the independent
one-coordinate averages, each realized by the diagonal phase unitaries. -/
theorem phase_gram_coefficient_average (p q : n × n) :
    (∑ t : n → Fin 4, phaseGramCoefficient t p q) / (4 : ℂ) ^ Fintype.card n =
      if (p.1 = p.2 ∧ q.1 = q.2) ∨ p = q then 1 else 0 := by
  rw [← independent_phase_average]
  simp_rw [phaseGramCoefficient_eq]
  let f (u : n) (k : Fin 4) : ℂ := (character u p * star (character u q)) ^ k.val
  change (∑ t : n → Fin 4, ∏ u, f u (t u)) / (4 : ℂ) ^ Fintype.card n = _
  rw [← Fintype.prod_sum f]
  have hd : (4 : ℂ) ^ Fintype.card n = ∏ _ : n, (4 : ℂ) := by simp
  rw [hd, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro u _
  simp [f, coordinateAverage, Fin.sum_univ_succ, div_eq_mul_inv, add_assoc]

/-- The unnormalized Choi vector of a single Kraus matrix, ordered by the
output and input coordinates of the Choi matrix. -/
def choiVector (K : Matrix n n ℂ) (p : n × n) : ℂ := K p.1 p.2

/-- The actual unitary phase average deletes exactly the off-diagonal entries
outside the coherent diagonal block and preserves each diagonal entry. -/
theorem phase_averaged_rank_one_gram (K : Matrix n n ℂ) (p q : n × n) :
    (∑ t : n → Fin 4,
      let U := (phaseUnitary t).val
      choiVector (U * K * Uᴴ) p * star (choiVector (U * K * Uᴴ) q)) /
        (4 : ℂ) ^ Fintype.card n =
      if (p.1 = p.2 ∧ q.1 = q.2) ∨ p = q then
        choiVector K p * star (choiVector K q) else 0 := by
  simp only [phaseUnitary, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    choiVector, Pi.star_apply]
  have he (t : n → Fin 4) :
      phase t p.1 * K p.1 p.2 * star (phase t p.2) *
          star (phase t q.1 * K q.1 q.2 * star (phase t q.2)) =
        phaseGramCoefficient t p q * (K p.1 p.2 * star (K q.1 q.2)) := by
    simp only [phaseGramCoefficient, star_mul]
    ring
  simp_rw [he, ← Finset.sum_mul]
  rw [mul_comm (∑ x : n → Fin 4, phaseGramCoefficient x p q), mul_div_assoc,
    phase_gram_coefficient_average]
  split_ifs <;> simp

/-- The Choi vector restricted to equal input and output coordinates. -/
def coherentVector (K : Matrix n n ℂ) (p : n × n) : ℂ :=
  if p.1 = p.2 then choiVector K p else 0

/-- What survives outside the coherent block is a positive diagonal matrix. -/
noncomputable def incoherentGram (K : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  diagonal fun p => if p.1 = p.2 then 0 else (Complex.normSq (choiVector K p) : ℂ)

theorem incoherentGram_psd (K : Matrix n n ℂ) : (incoherentGram K).PosSemidef := by
  rw [incoherentGram, Matrix.posSemidef_diagonal_iff]
  intro p
  by_cases hp : p.1 = p.2 <;> simp [hp, Complex.normSq_nonneg]

/-- The actual phase mixture has one coherent rank-one block and a positive
incoherent remainder. -/
theorem phase_averaged_gram_decomposition (K : Matrix n n ℂ) (p q : n × n) :
    (∑ t : n → Fin 4,
      let U := (phaseUnitary t).val
      choiVector (U * K * Uᴴ) p * star (choiVector (U * K * Uᴴ) q)) /
        (4 : ℂ) ^ Fintype.card n =
      (vecMulVec (coherentVector K) (star (coherentVector K)) + incoherentGram K) p q := by
  rw [phase_averaged_rank_one_gram]
  by_cases he : p = q
  · subst q
    by_cases hp : p.1 = p.2
    · simp [coherentVector, incoherentGram, vecMulVec, Pi.star_apply, hp]
    · simp [coherentVector, incoherentGram, vecMulVec, Pi.star_apply, hp,
        Complex.normSq_eq_conj_mul_self, Complex.star_def, mul_comm]
  · by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
      simp [coherentVector, incoherentGram, vecMulVec, Pi.star_apply, hp, hq, he]

end D5.S3.Quantum.Measurement.Auric.PhaseTwirledGram
