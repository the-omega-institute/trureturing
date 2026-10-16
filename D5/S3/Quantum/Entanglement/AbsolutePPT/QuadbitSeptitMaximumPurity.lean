/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSeptitMaximumPurity
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSeptitMaximumPurity
   mirror-E: none(waiver:physical-density-spectral-join)
   anchors: []
   utility: none
   digest: The literal four-by-seven APPT purity maximum is 1/25, attained by the diagonal density (3,1^27)/30. -/

/-
proof_shape: density_bound: bind-only, consumed by result; result: content
  through the same-delivery RankFourLength28Purity.purity_bound inference.
admission_basis: escape-witness
escape_witness: The length-28 gap identity combines two boundary pencils
  with a rank-four mass inequality. One sorted physical spectrum supplies
  all three hypotheses. This physical application adds no certificate.
The diagonal reduction and normalized ray are reused from
  QuadbitQuintitMaximumPurity; the old four-by-five statement is preserved.
utility:none rationale: This is the universal density-matrix consequence
  of the separate length-28 proof, not a new finite certificate or checker.
Literature: Library/QuantumStates/hildebrand2007pptspectra.md.
No classification of all maximizers or assertion in other dimensions follows.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
import D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity
open QutritPerturbationAttainment QutritSpectralReduction

noncomputable section

/-- A literal density bound: APPT quantifies over every global unitary on the
actual product space. The two pencils and L4 below concern exactly one l. -/
private theorem density_bound (rho : Matrix (Fin 4 × Fin 7) (Fin 4 × Fin 7) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    (rho * rho).trace.re ≤ (1 / 25 : ℝ) := by
  classical
  let e : (Fin 4 × Fin 7) ≃ Fin 28 :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_prod])
  obtain ⟨l, ho, hn, ht, hdiag, hpur⟩ :=
    QuadbitQuintitMaximumPurity.diagonal_spectral_reduction e rho hrho htrace happt
  have hboth := QuadbitQuintitMaximumPurity.diagonal_necessary_both
    (by decide : 3 ≤ 4) (by decide : 3 ≤ 7) e l hdiag
  have hmass := UniformRankFourNecessary.uniform_rank_four_necessary
    (by decide : 4 ≤ 4) (by decide : 4 ≤ 7) e l hdiag
  have hb : QuadbitQuintitMaximumPurity.cornerBoundaryValues 28 (by decide) l =
      RankFourLength28Purity.boundary l := by
    funext q
    fin_cases q <;> rfl
  rw [hb] at hboth
  have hf : UniformRankFourNecessary.sumFirst 6 l =
      ∑ i : Fin 6, l ⟨i.val, by omega⟩ := by
    unfold UniformRankFourNecessary.sumFirst
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dif_pos (show i.val < 28 by omega)]
  have hl : UniformRankFourNecessary.sumLast 10 l =
      ∑ i : Fin 10, l ⟨18 + i.val, by omega⟩ := by
    unfold UniformRankFourNecessary.sumLast
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dif_pos (show 28 - 10 + i.val < 28 by omega)]
  rw [hf, hl] at hmass
  have h4 : 0 ≤ RankFourLength28Purity.L4 l := by
    exact sub_nonneg.mpr hmass
  rw [hpur]
  exact RankFourLength28Purity.purity_bound l ho hn ht hboth.1 hboth.2 h4

def claim : Prop :=
    (∀ rho : Matrix (Fin 4 × Fin 7) (Fin 4 × Fin 7) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) → APPT rho →
        (rho * rho).trace.re ≤ (1 / 25 : ℝ)) ∧
    (sSup {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin 7) (Fin 4 × Fin 7) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = p} = (1 / 25 : ℝ)) ∧
    ∃ rho : Matrix (Fin 4 × Fin 7) (Fin 4 × Fin 7) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 7 =>
        if ij = (0, 0) then (3 / 30 : ℂ) else (1 / 30 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (1 / 25 : ℝ)

/-- The direct lower bound reuses the existing arbitrary-dimension normalized
separable ray. No qutrit-only Kraus or projector-attainment statement is used. -/
theorem result : claim := by
  let v : Fin 4 × Fin 7 → ℂ := Pi.single (0, 0) 1
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by
    classical
    simp [v, dotProduct, Pi.single_apply]
  obtain ⟨hd, ht, ha, hp⟩ := QuadbitQuintitMaximumPurity.normalized_ray v hv
  have heq : QuadbitQuintitMaximumPurity.normalizedRay v =
      diagonal (fun ij : Fin 4 × Fin 7 =>
        if ij = (0, 0) then (3 / 30 : ℂ) else (1 / 30 : ℂ)) := by
    convert QuadbitQuintitMaximumPurity.normalized_basis_diagonal
      ((0, 0) : Fin 4 × Fin 7) using 1 <;> norm_num [v]
  norm_num at hp
  have hattain : ∃ rho : Matrix (Fin 4 × Fin 7) (Fin 4 × Fin 7) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (1 / 25 : ℝ) :=
    ⟨QuadbitQuintitMaximumPurity.normalizedRay v, ⟨hd, ht⟩, ha, hp⟩
  refine ⟨fun rho hd ha => density_bound rho hd.1 hd.2 ha, ?_,
    QuadbitQuintitMaximumPurity.normalizedRay v, heq, ⟨hd, ht⟩, ha, hp⟩
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
  · exact ⟨_, hattain⟩
  · rintro p ⟨rho, hd, ha, hp⟩
    rw [← hp]
    exact density_bound rho hd.1 hd.2 ha
  · intro w hw
    exact ⟨_, hattain, hw⟩

#print axioms result

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSeptitMaximumPurity
