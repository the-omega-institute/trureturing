/- GID: D5/S3/Quantum/Lieb/AutomaticOperatorContinuity
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/AutomaticOperatorContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Operator monotonicity on one doubled Hilbert space forces scalar continuity and removes the continuity premise from operator concavity.
-/

import D5.S3.Quantum.Lieb.MonotoneBlockConcavity
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Order.Monotone

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Lieb.AutomaticOperatorContinuity

open LownerHeinzTheorem JensenOperatorInequality
open scoped Topology

open private block_scalar_sandwich rotation rotation_unitary rotation_conjugate
  diagonal_strictly_positive corner_mono
  from D5.S3.Quantum.Lieb.MonotoneBlockConcavity
open private cfcR_blockDiagonal cfcR_conj_unitary_on
  from D5.S3.Quantum.Lieb.JensenOperatorInequalityIImpIV

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

private lemma scalar_monotoneOn (f : ℝ → ℝ)
    (hmono : LownerHeinzCore.OperatorMonotoneOn
      (𝓐 := L (HSum H)) (Set.Ioi 0) f) :
    MonotoneOn f (Set.Ioi 0) := by
  intro x hx y hy hxy
  let K := L (HSum H)
  let ax : K := algebraMap ℝ K x
  let ay : K := algebraMap ℝ K y
  have hax : 0 ≤ ax := by
    simpa [ax, Algebra.algebraMap_eq_smul_one] using (smul_nonneg hx.le (show (0 : K) ≤ 1 from zero_le_one))
  have hay : 0 ≤ ay := by
    simpa [ay, Algebra.algebraMap_eq_smul_one] using (smul_nonneg hy.le (show (0 : K) ≤ 1 from zero_le_one))
  have haxy : ax ≤ ay := by
    simpa [ax, ay, Algebra.algebraMap_eq_smul_one] using
      (smul_le_smul_of_nonneg_right hxy (show (0 : K) ≤ 1 from zero_le_one))
  have haxspec : spectrum ℝ ax ⊆ Set.Ioi 0 := by
    rw [show ax = algebraMap ℝ K x by rfl]
    exact (CFC.spectrum_algebraMap_eq x).symm ▸ (by simpa [Set.singleton_subset_iff] using hx)
  have hayspec : spectrum ℝ ay ⊆ Set.Ioi 0 := by
    rw [show ay = algebraMap ℝ K y by rfl]
    exact (CFC.spectrum_algebraMap_eq y).symm ▸ (by simpa [Set.singleton_subset_iff] using hy)
  have h := hmono hay hax haxy hayspec haxspec
  rw [show cfcR f ax = algebraMap ℝ K (f x) by simp [ax],
    show cfcR f ay = algebraMap ℝ K (f y) by simp [ay]] at h
  have hs := (algebraMap_le_iff_le_spectrum (R := ℝ) (A := K)
    (r := f x) (a := algebraMap ℝ K (f y))).mp h
  simpa [CFC.spectrum_algebraMap_eq] using hs (f y) (by simp)

private lemma scalar_shifted_concavity (f : ℝ → ℝ)
    (hmono : LownerHeinzCore.OperatorMonotoneOn
      (𝓐 := L (HSum H)) (Set.Ioi 0) f)
    (hscalar : MonotoneOn f (Set.Ioi 0))
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    (1 - t) * f x + t * f y ≤ f ((1 - t) * x + t * y + ε) := by
  let K := L (HSum H)
  let X : L H := algebraMap ℝ (L H) x
  let Y : L H := algebraMap ℝ (L H) y
  have hX : IsStrictlyPositive X := by
    rw [X, ← Algebra.algebraMap_eq_smul_one]
    exact isStrictlyPositive_one.smul hx
  have hY : IsStrictlyPositive Y := by
    rw [Y, ← Algebra.algebraMap_eq_smul_one]
    exact isStrictlyPositive_one.smul hy
  let a : ℝ := Real.sqrt (1 - t)
  let b : ℝ := Real.sqrt t
  have ha2 : a ^ 2 = 1 - t := Real.sq_sqrt (sub_nonneg.mpr ht1)
  have hb2 : b ^ 2 = t := Real.sq_sqrt ht0
  have hab : a ^ 2 + b ^ 2 = 1 := by rw [ha2, hb2]; ring
  let U : unitary (L (HSum H)) := ⟨rotation a b, rotation_unitary hab⟩
  let M : L H := (1 - t) • X + t • Y
  let N : L H := t • X + (1 - t) • Y
  let D : L H := (a * b) • (Y - X)
  have hM : IsStrictlyPositive M := by
    by_cases ht : t = 1
    · simpa [M, ht] using hY
    · exact (hX.smul (sub_pos.mpr (lt_of_le_of_ne ht1 ht))).add_nonneg
        (smul_nonneg ht0 hY.nonneg)
  have hN : IsSelfAdjoint N := ((IsSelfAdjoint.all t).smul hX.isSelfAdjoint).add
    ((IsSelfAdjoint.all (1 - t)).smul hY.isSelfAdjoint)
  have hD : IsSelfAdjoint D := (IsSelfAdjoint.all (a * b)).smul
    (hY.isSelfAdjoint.sub hX.isSelfAdjoint)
  have hdiag := diagonal_strictly_positive hX hY
  have hW : IsStrictlyPositive
      (star (U : L (HSum H)) * blockDiagonal X Y * (U : L (HSum H))) :=
    Unitary.isUnit_coe.isStrictlyPositive_star_left_conjugate_iff.mpr hdiag
  have hW_eq : star (U : L (HSum H)) * blockDiagonal X Y * (U : L (HSum H)) =
      blockOp M D (star D) N := by
    simpa [U, M, N, D, ha2, hb2, hD.star_eq] using rotation_conjugate a b X Y
  have hspecXY : spectrum ℝ (blockDiagonal X Y) ⊆ ({x, y} : Set ℝ) := by
    intro z hz
    have hz' := (AlgHom.spectrum_apply_subset (blockDiagonalHom (ℋ := H)) (X, Y)) hz
    simpa [Prod.spectrum_eq, X, Y, CFC.spectrum_algebraMap_eq] using hz'
  have hcontXY : ContinuousOn f (spectrum ℝ X ∪ spectrum ℝ Y) := by
    apply (Set.toFinite ({x, y} : Set ℝ)).continuousOn.mono
    intro z hz
    rcases hz with hz | hz
    · exact Set.mem_insert_of_mem _ ((CFC.spectrum_algebraMap_eq x).symm ▸ hz)
    · exact Set.mem_insert _ ((CFC.spectrum_algebraMap_eq y).symm ▸ hz)
  have hεineq (ε : ℝ) (hε : 0 < ε) :
      (1 - t) • cfcR f X + t • cfcR f Y ≤ cfcR f (M + ε • 1) := by
    obtain ⟨bound, hbound, horder⟩ := block_scalar_sandwich M N D hN hε
    rw [← hW_eq] at horder
    have hupper := hW.of_le horder
    have hmε : IsStrictlyPositive (M + ε • (1 : L H)) :=
      hM.add_nonneg (smul_nonneg hε.le zero_le_one)
    have hboundpos : IsStrictlyPositive (bound • (1 : L H)) :=
      isStrictlyPositive_one.smul hbound
    have hfc := hmono hupper.nonneg hW.nonneg horder
      (fun _ hz => hupper.spectrum_pos hz) (fun _ hz => hW.spectrum_pos hz)
    change cfcR f (star (U : L (HSum H)) * blockDiagonal X Y * (U : L (HSum H))) ≤
      cfcR f (blockDiagonal (M + ε • 1) (bound • 1)) at hfc
    have hsM : spectrum ℝ (M + ε • (1 : L H)) ⊆
        ({(1 - t) * x + t * y + ε} : Set ℝ) := by
      simpa [M, X, Y, Algebra.algebraMap_eq_smul_one, smul_add, add_smul,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (CFC.spectrum_algebraMap_subset ((1 - t) * x + t * y + ε) :
          spectrum ℝ (algebraMap ℝ (L H) ((1 - t) * x + t * y + ε)) ⊆ _)
    have hsbound : spectrum ℝ (bound • (1 : L H)) ⊆ ({bound} : Set ℝ) := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        (CFC.spectrum_algebraMap_subset bound :
          spectrum ℝ (algebraMap ℝ (L H) bound) ⊆ ({bound} : Set ℝ))
    have hfupper : ContinuousOn f
        (spectrum ℝ (M + ε • 1) ∪ spectrum ℝ (bound • (1 : L H))) := by
      apply (Set.toFinite ({(1 - t) * x + t * y + ε, bound} : Set ℝ)).continuousOn.mono
      exact Set.union_subset hsM hsbound
    have hconj : cfcR f (star (U : L (HSum H)) * blockDiagonal X Y *
        (U : L (HSum H))) = star (U : L (HSum H)) *
          cfcR f (blockDiagonal X Y) * (U : L (HSum H)) := by
      simpa only [Unitary.coe_star] using cfcR_conj_unitary_on
        ({x, y} : Set ℝ) f ((Set.toFinite ({x, y} : Set ℝ)).continuousOn) hspecXY U
          hdiag.isSelfAdjoint
    rw [hconj, cfcR_blockDiagonal f X Y hX.isSelfAdjoint hY.isSelfAdjoint hcontXY,
      cfcR_blockDiagonal f (M + ε • 1) (bound • 1)
        hmε.isSelfAdjoint hboundpos.isSelfAdjoint hfupper] at hfc
    have hc := corner_mono hfc
    rw [show star (U : L (HSum H)) * blockDiagonal (cfcR f X) (cfcR f Y) *
        (U : L (HSum H)) =
      blockOp ((1 - t) • cfcR f X + t • cfcR f Y)
        ((a * b) • (cfcR f Y - cfcR f X))
        ((a * b) • (cfcR f Y - cfcR f X))
        (t • cfcR f X + (1 - t) • cfcR f Y) by
          simpa [U, ha2, hb2] using rotation_conjugate a b (cfcR f X) (cfcR f Y)] at hc
    convert hc using 1 <;> ext z <;> simp [ContinuousLinearMap.comp_apply]
  have hscalarOp :
      algebraMap ℝ (L H) ((1 - t) * f x + t * f y) ≤
        algebraMap ℝ (L H) (f ((1 - t) * x + t * y + ε)) := by
    simpa [M, X, Y, Algebra.algebraMap_eq_smul_one, cfcR, smul_add, add_smul,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hεineq ε hε
  have hs := (algebraMap_le_iff_le_spectrum (R := ℝ) (A := L H)
    (r := (1 - t) * f x + t * f y)
    (a := algebraMap ℝ (L H) (f ((1 - t) * x + t * y + ε)))).mp hscalarOp
  simpa [CFC.spectrum_algebraMap_eq] using
    hs (f ((1 - t) * x + t * y + ε)) (by simp)

theorem operator_monotone_double_space_continuousOn (f : ℝ → ℝ)
    (hmono : LownerHeinzCore.OperatorMonotoneOn
      (𝓐 := L (HSum H)) (Set.Ioi 0) f) :
    ContinuousOn f (Set.Ioi 0) := by
  have hscalar : MonotoneOn f (Set.Ioi 0) := scalar_monotoneOn f hmono
  sorry

theorem operator_monotone_double_space_concavity (f : ℝ → ℝ)
    (hmono : LownerHeinzCore.OperatorMonotoneOn
      (𝓐 := L (HSum H)) (Set.Ioi 0) f)
    {A B : L H} (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • cfcR f A + t • cfcR f B ≤
      cfcR f ((1 - t) • A + t • B) := by
  apply D5.S3.Quantum.Lieb.MonotoneBlockConcavity.monotone_double_space_concavity
    f (operator_monotone_double_space_continuousOn f hmono) hmono hA hB ht0 ht1

end D5.S3.Quantum.Lieb.AutomaticOperatorContinuity
