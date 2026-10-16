/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient
   mirror-E: none(waiver:explicit-spectral-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient.claim; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient.spectrum; result=D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient.result; claim=D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient.claim
   digest: Two rank-three boundary pencils alone do not imply the length-28 purity bound. -/

/-
proof_shape: result: content; pencil_psd: bind-only, consumed by result.
admission_basis: escape-witness
The spectrum is (2^9,1^19)/37. This refutes only the implication omitting L4;
it is not an APPT spectrum or a refutation of the APPT purity conjecture.
The declarations retain their original Lean namespace directly. Their physical
source owner and declaration GIDs are RankFourLength28PencilsInsufficient.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 128000000
set_option maxRecDepth 65536

open Matrix
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity
open QutritSpectralReduction

/-- Dropping L4 is a strictly weaker spectral relaxation, with an explicit counterexample. -/
def claim : Prop :=
  ∀ l : Fin 28 → ℝ, Antitone l → (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
    (QutritSpectralReduction.K1 (boundary l)).PosSemidef →
    (QutritSpectralReduction.K2 (boundary l)).PosSemidef →
    ∑ i, (l i)^2 ≤ (1 : ℝ)/25

noncomputable def spectrum (i : Fin 28) : ℝ := if i.val < 9 then 2/37 else 1/37

private theorem pencil_psd :
    (castMat (!![2/37,-1/37,-1/37; -1/37,2/37,-1/37;
      -1/37,-1/37,2/37] : Matrix (Fin 3) (Fin 3) ℚ)).PosSemidef := by
  apply psd_of_rat_ldl _ !![1,0,0; -1/2,1,0; -1/2,-1,1] ![2/37,3/74,0]
  · decide +kernel
  · decide +kernel

/-- The literal target is a negation of the literal Prop-valued claim. -/
theorem result : ¬ claim := by
  intro h
  have ho : Antitone spectrum := by
    intro i j hij
    simp only [spectrum]
    split_ifs <;> norm_num <;> omega
  have hn (i : Fin 28) : 0 ≤ spectrum i := by
    simp only [spectrum]
    split_ifs <;> norm_num
  have ht : (∑ i, spectrum i) = 1 := by
    norm_num [spectrum, Fin.sum_univ_succ]
  have h₁ : (QutritSpectralReduction.K1 (boundary spectrum)).PosSemidef := by
    convert pencil_psd using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [QutritSpectralReduction.K1, boundary, spectrum, castMat,
        Matrix.cons_val, Matrix.vecHead, Matrix.vecTail,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_two, Fin.succ,
        Fin.reduceFinMk]
      <;> dsimp only [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
      <;> norm_num
  have h₂ : (QutritSpectralReduction.K2 (boundary spectrum)).PosSemidef := by
    convert pencil_psd using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [QutritSpectralReduction.K2, boundary, spectrum, castMat,
        Matrix.cons_val, Matrix.vecHead, Matrix.vecTail,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_two, Fin.succ,
        Fin.reduceFinMk]
      <;> dsimp only [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
      <;> norm_num
  have hp := h spectrum ho hn ht h₁ h₂
  norm_num [spectrum, Fin.sum_univ_succ] at hp

end D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity
