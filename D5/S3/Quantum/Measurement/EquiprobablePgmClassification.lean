/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmClassification
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmClassification
   mirror-E: none(waiver:universal-povm-classification)
   anchors: []
   utility: none
   digest: Both signs and exact active sets of the actual symmetric qubit optimum. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmScores

/-!
This is the complete strict-positive active-set classification of Haobo Ma and
Wenlin Zhang (4 November 2026, new note only CC BY 4.0), with the symmetric
constructions credited to Hyunho Cha. The dual and uniqueness proofs are at
EquiprobablePgmSymmetric. The negative orientation is transported through an
actual unitary basis permutation, not postulated from a scalar symmetry.
Admission commitment: the actual complete active set and the strict failure
iff, including both signs and both equality boundaries.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.EquiprobablePgmClassification
open D5.S3.Quantum.FiniteDimensional (QubitMatrix)
open D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (success pgmScore)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)

/-- Exchange the two orthonormal basis vectors. -/
def basisFlip (M : QubitMatrix) : QubitMatrix := M.submatrix Fin.rev Fin.rev

private theorem basisFlip_involutive (M : QubitMatrix) : basisFlip (basisFlip M) = M := by
  ext i j
  simp [basisFlip]

private theorem flip_povm {N : ℕ} (E : Fin N → QubitMatrix) (hE : finitePOVM E) :
    finitePOVM (fun i => basisFlip (E i)) := by
  constructor
  · intro i
    exact (hE.1 i).submatrix Fin.rev
  · ext i j
    have h := congrArg (fun M : QubitMatrix => M (Fin.rev i) (Fin.rev j)) hE.2
    fin_cases i <;> fin_cases j <;>
      simpa [basisFlip, Matrix.sum_apply, Fin.rev] using h

private theorem flip_score {N : ℕ} (ρ E : Fin N → QubitMatrix) :
    success (fun i => basisFlip (ρ i)) (fun i => basisFlip (E i)) = success ρ E := by
  unfold success
  apply Finset.sum_congr rfl
  intro i _
  simp [basisFlip, trace, Matrix.mul_apply, Fin.sum_univ_two, Fin.rev]
  ring

private theorem flip_rho (a b c : ℝ) :
    rho (1 - a) b (1 - c) = fun i => basisFlip (rho a b c i) := by
  funext i
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [rho, basisFlip, Fin.rev] <;> push_cast <;> ring

private theorem flip_symmetric_score (a b c : ℝ) (E : Fin 3 → QubitMatrix) :
    success (rho (1 - a) b (1 - c)) (fun i => basisFlip (E i)) =
      success (rho a b c) E := by
  rw [flip_rho]
  exact flip_score _ _

/-- The three actual effects in the lower orientation, given in the original basis. -/
def lowerPovm (t : ℝ) : Fin 3 → QubitMatrix := fun i => basisFlip (upperPovm t i)

/-- The negative-sign three-active region has the same unique classification,
with the third effect supported on the second basis ray. -/
theorem lower_classification (a b c : ℝ) (hb : 0 < b) (hδ : b < a - c) :
    let t := b / (a - c)
    finitePOVM (lowerPovm t) ∧
      success (rho a b c) (lowerPovm t) = (1 + (a - c) + b * t) / 3 ∧
      ∀ E, finitePOVM E →
        ((∀ F, finitePOVM F → success (rho a b c) F ≤ success (rho a b c) E) ↔
          E = lowerPovm t) := by
  dsimp only
  have hd : (1 - c) - (1 - a) = a - c := by ring
  have hu := upper_classification (1 - a) b (1 - c) hb (by simpa only [hd] using hδ)
  dsimp only at hu
  rw [hd] at hu
  let t := b / (a - c)
  have hP := flip_povm (upperPovm t) hu.1
  have hback : (fun i => basisFlip (lowerPovm t i)) = upperPovm t := by
    funext i
    exact basisFlip_involutive _
  refine ⟨hP, ?_, ?_⟩
  · have h := flip_symmetric_score a b c (lowerPovm t)
    rw [hback] at h
    exact h.symm.trans hu.2.1
  · intro E hE
    constructor
    · intro hopt
      have hopt' : ∀ F, finitePOVM F →
          success (rho (1 - a) b (1 - c)) F ≤
            success (rho (1 - a) b (1 - c)) (fun i => basisFlip (E i)) := by
        intro F hF
        rw [flip_symmetric_score]
        have h := hopt (fun i => basisFlip (F i)) (flip_povm F hF)
        have hf := flip_symmetric_score a b c (fun i => basisFlip (F i))
        have hff : (fun i => basisFlip (basisFlip (F i))) = F := by
          funext i
          exact basisFlip_involutive _
        rw [hff] at hf
        exact hf.trans_le h
      have he := (hu.2.2 _ (flip_povm E hE)).mp hopt'
      funext i
      have hx := congrArg (fun F => basisFlip (F i)) he
      simpa only [basisFlip_involutive, lowerPovm] using hx
    · rintro rfl F hF
      have h := (hu.2.2 (upperPovm t) hu.1).mpr rfl
        (fun i => basisFlip (F i)) (flip_povm F hF)
      rw [flip_symmetric_score] at h
      have he := flip_symmetric_score a b c (lowerPovm t)
      rw [hback] at he
      exact h.trans_eq he

/-- The complete actual optimal POVM, with equality assigned to the two-active region. -/
def optimalPovm (a b c : ℝ) : Fin 3 → QubitMatrix :=
  if |c - a| ≤ b then pairPovm
  else if b < c - a then upperPovm (b / (c - a)) else lowerPovm (b / (a - c))

private theorem upper_nonzero (t : ℝ) (ht : t ^ 2 < 1) :
    ∀ i, upperPovm t i ≠ 0 := by
  intro i h
  fin_cases i
  · have he := congrArg (fun M : QubitMatrix => M 1 1) h
    norm_num [upperPovm, vecMulVec] at he
  · have he := congrArg (fun M : QubitMatrix => M 1 1) h
    norm_num [upperPovm, vecMulVec] at he
  · have he := congrArg (fun M : QubitMatrix => M 0 0) h
    have hz : (1 - t ^ 2 : ℝ) = 0 := by
      have he' : (((1 - t ^ 2 : ℝ) : ℂ)) = 0 := by simpa [upperPovm] using he
      exact_mod_cast he'
    linarith

private theorem pair_active :
    Finset.univ.filter (fun i => pairPovm i ≠ 0) = ({0, 1} : Finset (Fin 3)) := by
  have h0 : pairPovm 0 ≠ 0 := by
    intro h
    have he := congrArg (fun M : QubitMatrix => M 0 0) h
    norm_num [pairPovm, vecMulVec] at he
  have h1 : pairPovm 1 ≠ 0 := by
    intro h
    have he := congrArg (fun M : QubitMatrix => M 0 0) h
    norm_num [pairPovm, vecMulVec] at he
  ext i
  fin_cases i <;> simp [h0, h1, show pairPovm 2 = 0 from rfl]

/-- The complete classification is an equivalence for every actual complex POVM;
the active labels are exactly the pair in the closed pair region and all three otherwise. -/
theorem complete_classification (a b c : ℝ) (hb : 0 < b) :
    finitePOVM (optimalPovm a b c) ∧
      (∀ E, finitePOVM E →
        ((∀ F, finitePOVM F → success (rho a b c) F ≤ success (rho a b c) E) ↔
          E = optimalPovm a b c)) ∧
      Finset.univ.filter (fun i => optimalPovm a b c i ≠ 0) =
        if |c - a| ≤ b then {0, 1} else Finset.univ := by
  by_cases hδ : |c - a| ≤ b
  · simpa only [optimalPovm, if_pos hδ] using
      And.intro (pair_classification a b c hb hδ).1
        ⟨(pair_classification a b c hb hδ).2.2, pair_active⟩
  · have hr : c - a < -b ∨ b < c - a := by
      rcases lt_or_gt_of_ne (show c - a ≠ 0 by
        intro h; simp [h, hb.le] at hδ) with hl | hr
      · left
        rw [abs_of_neg hl] at hδ
        linarith
      · right
        rw [abs_of_pos hr] at hδ
        exact lt_of_not_ge hδ
    rcases hr with hl | hr
    · have hl' : b < a - c := by linarith
      have hn : ¬ b < c - a := by linarith
      have hc := lower_classification a b c hb hl'
      dsimp only at hc
      have ht0 : 0 < b / (a - c) := div_pos hb (hb.trans hl')
      have ht1 : b / (a - c) < 1 := (div_lt_one (hb.trans hl')).mpr hl'
      have hall (i) : lowerPovm (b / (a - c)) i ≠ 0 := by
        intro he
        have hx := congrArg basisFlip he
        have hz := upper_nonzero (b / (a - c)) (by nlinarith) i
        apply hz
        change basisFlip (basisFlip (upperPovm (b / (a - c)) i)) = basisFlip 0 at hx
        rw [basisFlip_involutive] at hx
        simpa [basisFlip] using hx
      simp only [optimalPovm, if_neg hδ, if_neg hn]
      refine ⟨hc.1, hc.2.2, ?_⟩
      ext i
      simp [hall i]
    · have hc := upper_classification a b c hb hr
      dsimp only at hc
      have ht0 : 0 < b / (c - a) := div_pos hb (hb.trans hr)
      have ht1 : b / (c - a) < 1 := (div_lt_one (hb.trans hr)).mpr hr
      have hall := upper_nonzero (b / (c - a)) (by nlinarith [ht0, ht1])
      simp only [optimalPovm, if_neg hδ, if_pos hr]
      refine ⟨hc.1, hc.2.2, ?_⟩
      ext i
      simp [hall i]

end D5.S3.Quantum.Measurement.EquiprobablePgmClassification
