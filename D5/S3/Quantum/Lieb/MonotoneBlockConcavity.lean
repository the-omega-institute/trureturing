/- GID: D5/S3/Quantum/Lieb/MonotoneBlockConcavity
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/MonotoneBlockConcavity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Doubled-space operator monotonicity yields positive-half-line concavity. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Lieb.JensenOperatorInequalityIImpIV
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Tactic.Module

/-!
The block-sandwich argument of Hansen, *The fast track to Löwner's theorem*,
arXiv:1112.0098v3, Theorem 2.1. Continuity is an explicit hypothesis here;
automatic continuity and the Löwner representing measure are not proved by this module.
The operators and functional calculus are actual bounded Hilbert-space operators.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Lieb.MonotoneBlockConcavity

open LownerHeinzTheorem JensenOperatorInequality
open scoped Topology

open private blockDiagonal_eq_blockOp blockOp_mul blockOp_add blockOp_smulR
  cfcR_blockDiagonal cfcR_conj_unitary_on
  from D5.S3.Quantum.Lieb.JensenOperatorInequalityIImpIV

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

omit [Nontrivial H] in
/-- An arbitrarily small first-corner perturbation controls an arbitrary off-diagonal
block once the second corner is allowed a sufficiently large scalar bound. -/
private theorem block_scalar_sandwich (M N D : L H) (hN : IsSelfAdjoint N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ bound : ℝ, 0 < bound ∧
      blockOp M D (star D) N ≤ blockDiagonal (M + ε • 1) (bound • 1) := by
  let T : L H := N + ε⁻¹ • (star D * D)
  let bound : ℝ := ‖T‖ + 1
  have hT : IsSelfAdjoint T := hN.add ((IsSelfAdjoint.all ε⁻¹).smul (IsSelfAdjoint.star_mul_self D))
  have hbound : T ≤ bound • (1 : L H) := by
    have hn := hT.le_algebraMap_norm_self
    simpa [bound, Algebra.algebraMap_eq_smul_one, add_smul] using
      hn.trans (le_add_of_nonneg_right (show (0 : L H) ≤ 1 from zero_le_one))
  let Q : L (HSum H) := blockOp (ε • 1) (-D) 0 0
  have hsquare : ε⁻¹ • (star Q * Q) =
      blockOp (ε • (1 : L H)) (-D) (-(star D)) (ε⁻¹ • (star D * D)) := by
    dsimp [Q]
    rw [blockOp_star, blockOp_mul, blockOp_smulR]
    congr 1 <;>
      simp [smul_mul_assoc, mul_smul_comm, smul_smul, hε.ne', mul_assoc]
  have hdiag : 0 ≤ blockDiagonal (0 : L H) (bound • 1 - T) :=
    blockDiagonal_nonneg (le_refl 0) (sub_nonneg.mpr hbound)
  have hsum : 0 ≤ ε⁻¹ • (star Q * Q) +
      blockDiagonal (0 : L H) (bound • 1 - T) :=
    add_nonneg (smul_nonneg (inv_nonneg.mpr hε.le) (star_mul_self_nonneg Q)) hdiag
  refine ⟨bound, by dsimp [bound]; positivity, sub_nonneg.mp ?_⟩
  convert hsum using 1
  rw [hsquare]
  simp only [blockDiagonal_eq_blockOp, blockOp_add]
  apply blockOp_ext <;> intro z <;>
    simp [sub_eq_add_neg, blockOp, T, smul_add, add_smul] <;> abel

private def rotation (a b : ℝ) : L (HSum H) :=
  blockOp (a • 1) (-(b • 1)) (b • 1) (a • 1)

omit [Nontrivial H] in
private theorem rotation_unitary {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    rotation (H := H) a b ∈ unitary (L (HSum H)) := by
  rw [Unitary.mem_iff]
  constructor <;>
    simp only [rotation, blockOp_star, star_smul, star_one, star_neg,
      star_trivial, blockOp_mul] <;>
    rw [← blockDiagonal_one (ℋ := H), blockDiagonal_eq_blockOp] <;>
    congr 1 <;>
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_neg, neg_mul,
      neg_neg, smul_smul] <;>
    match_scalars <;> nlinarith [hab]

omit [Nontrivial H] in
private theorem rotation_conjugate (a b : ℝ) (A B : L H) :
    star (rotation (H := H) a b) * blockDiagonal A B * rotation a b =
      blockOp (a ^ 2 • A + b ^ 2 • B) ((a * b) • (B - A))
        ((a * b) • (B - A)) (b ^ 2 • A + a ^ 2 • B) := by
  simp only [rotation, blockOp_star, star_smul, star_one, star_neg, star_trivial,
    blockDiagonal_eq_blockOp, blockOp_mul]
  congr 1 <;>
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, zero_mul, mul_zero,
      add_zero, zero_add, mul_neg, neg_mul, neg_neg, smul_smul] <;>
    module

omit [Nontrivial H] in
private theorem diagonal_strictly_positive {A B : L H}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    IsStrictlyPositive (blockDiagonal A B) := by
  have hu : IsUnit (A, B) := Prod.isUnit_iff.mpr ⟨hA.isUnit, hB.isUnit⟩
  have hd : IsUnit (blockDiagonal (ℋ := H) A B) := hu.map (blockDiagonalHom (ℋ := H))
  exact hd.isStrictlyPositive (blockDiagonal_nonneg hA.nonneg hB.nonneg)

omit [Nontrivial H] in
private theorem corner_mono {A B : L (HSum H)} (h : A ≤ B) :
    hsumProj H 0 ∘L A ∘L hsumIncl H 0 ≤ hsumProj H 0 ∘L B ∘L hsumIncl H 0 := by
  apply sub_nonneg.mp
  have hpos := ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp
    (sub_nonneg.mpr h)).adjoint_conj (hsumIncl H 0)
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr hpos
  simpa [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp] using hp

/-- Continuous functional calculus turns genuine operator monotonicity on the
two-fold Hilbert sum into concavity on the original Hilbert space. This also applies
to Hilbert spaces with infinite dimension and operators with infinite spectrum. -/
theorem monotone_double_space_concavity (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi 0))
    (hmono : LownerHeinzCore.OperatorMonotoneOn
      (𝓐 := L (HSum H)) (Set.Ioi 0) f)
    {A B : L H} (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • cfcR f A + t • cfcR f B ≤ cfcR f ((1 - t) • A + t • B) := by
  let a : ℝ := Real.sqrt (1 - t)
  let b : ℝ := Real.sqrt t
  have ha2 : a ^ 2 = 1 - t := Real.sq_sqrt (sub_nonneg.mpr ht1)
  have hb2 : b ^ 2 = t := Real.sq_sqrt ht0
  have hab : a ^ 2 + b ^ 2 = 1 := by rw [ha2, hb2]; ring
  let U : unitary (L (HSum H)) := ⟨rotation a b, rotation_unitary hab⟩
  let M : L H := (1 - t) • A + t • B
  let N : L H := t • A + (1 - t) • B
  let D : L H := (a * b) • (B - A)
  have hM : IsStrictlyPositive M := by
    by_cases ht : t = 1
    · simpa [M, ht] using hB
    · exact (hA.smul (sub_pos.mpr (lt_of_le_of_ne ht1 ht))).add_nonneg
        (smul_nonneg ht0 hB.nonneg)
  have hN : IsSelfAdjoint N := ((IsSelfAdjoint.all t).smul hA.isSelfAdjoint).add
    ((IsSelfAdjoint.all (1 - t)).smul hB.isSelfAdjoint)
  have hD : IsSelfAdjoint D := (IsSelfAdjoint.all (a * b)).smul (hB.isSelfAdjoint.sub hA.isSelfAdjoint)
  have hdiag := diagonal_strictly_positive hA hB
  have hW : IsStrictlyPositive (star (U : L (HSum H)) * blockDiagonal A B * (U : L (HSum H))) :=
    Unitary.isUnit_coe.isStrictlyPositive_star_left_conjugate_iff.mpr hdiag
  have hW_eq : star (U : L (HSum H)) * blockDiagonal A B * (U : L (HSum H)) =
      blockOp M D (star D) N := by
    simpa [U, M, N, D, ha2, hb2, hD.star_eq] using rotation_conjugate a b A B
  have hεineq (ε : ℝ) (hε : 0 < ε) :
      (1 - t) • cfcR f A + t • cfcR f B ≤ cfcR f (M + ε • 1) := by
    obtain ⟨bound, hbound, horder⟩ := block_scalar_sandwich M N D hN hε
    rw [← hW_eq] at horder
    have hupper := hW.of_le horder
    have hmε : IsStrictlyPositive (M + ε • (1 : L H)) :=
      hM.add_nonneg (smul_nonneg hε.le zero_le_one)
    have hboundpos : IsStrictlyPositive (bound • (1 : L H)) :=
      isStrictlyPositive_one.smul hbound
    have hfc := hmono hupper.nonneg hW.nonneg horder
      (fun _ hx => hupper.spectrum_pos hx) (fun _ hx => hW.spectrum_pos hx)
    change cfcR f (star (U : L (HSum H)) * blockDiagonal A B * (U : L (HSum H))) ≤
      cfcR f (blockDiagonal (M + ε • 1) (bound • 1)) at hfc
    have hfAB : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B) :=
      hf.mono (Set.union_subset (fun _ hx => hA.spectrum_pos hx)
        (fun _ hx => hB.spectrum_pos hx))
    have hfupper : ContinuousOn f
        (spectrum ℝ (M + ε • 1) ∪ spectrum ℝ (bound • (1 : L H))) :=
      hf.mono (Set.union_subset (fun _ hx => hmε.spectrum_pos hx)
        (fun _ hx => hboundpos.spectrum_pos hx))
    have hconj : cfcR f (star (U : L (HSum H)) * blockDiagonal A B *
        (U : L (HSum H))) = star (U : L (HSum H)) *
          cfcR f (blockDiagonal A B) * (U : L (HSum H)) := by
      simpa only [Unitary.coe_star] using cfcR_conj_unitary_on (Set.Ioi 0) f hf
        (fun _ hx => hdiag.spectrum_pos hx) U hdiag.isSelfAdjoint
    rw [hconj, cfcR_blockDiagonal f A B hA.isSelfAdjoint hB.isSelfAdjoint hfAB,
      cfcR_blockDiagonal f (M + ε • 1) (bound • 1)
        hmε.isSelfAdjoint hboundpos.isSelfAdjoint hfupper] at hfc
    have hc := corner_mono hfc
    rw [show star (U : L (HSum H)) * blockDiagonal (cfcR f A) (cfcR f B) * (U : L (HSum H)) =
      blockOp ((1 - t) • cfcR f A + t • cfcR f B)
        ((a * b) • (cfcR f B - cfcR f A))
        ((a * b) • (cfcR f B - cfcR f A))
        (t • cfcR f A + (1 - t) • cfcR f B) by
          simpa [U, ha2, hb2] using rotation_conjugate a b (cfcR f A) (cfcR f B)] at hc
    convert hc using 1 <;> ext x <;> simp [ContinuousLinearMap.comp_apply]
  have hshift (ε : ℝ) (hε : ε ∈ Set.Ici (0 : ℝ)) :
      IsStrictlyPositive (M + ε • (1 : L H)) :=
    hM.add_nonneg (smul_nonneg hε zero_le_one)
  have hc : ContinuousOn (fun ε : ℝ => cfcR f (M + ε • 1)) (Set.Ici 0) := by
    apply ContinuousOn.cfc_of_mem_nhdsSet f
      (isOpen_Ioi.mem_nhdsSet.mpr ?_) (by fun_prop)
      (fun ε hε => (hshift ε hε).isSelfAdjoint) hf
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨ε, hε, hx⟩ := hx
    exact (hshift ε hε).spectrum_pos hx
  have htend := ((hc.continuousWithinAt (show (0 : ℝ) ∈ Set.Ici 0 by simp)).mono
    Set.Ioi_subset_Ici_self).tendsto
  simpa [M] using ge_of_tendsto htend
    (Filter.mem_of_superset self_mem_nhdsWithin (fun ε hε => hεineq ε hε))

#print axioms monotone_double_space_concavity

end D5.S3.Quantum.Lieb.MonotoneBlockConcavity
