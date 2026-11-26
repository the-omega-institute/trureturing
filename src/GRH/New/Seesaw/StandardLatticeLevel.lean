import GRH.New.Seesaw.EqualLinesOrbit
import GRH.New.Filling.LatticeChart
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Under `Grading.SpansLattice`, the inclusion U(X) → U(V) maps a congruence
subgroup mod π into `Kf`; base case of the support bound. -/


open Filling Matrix Space
variable {E X ι} [Field E] [CMType E] [Fintype ι] [Fintype X] {ε s N} {V : Space E ι ε}
  (Y : Grading V N (X ⊕ _) s) {a π}
attribute [local simp] mul_assoc flagOrder BlockTriangular gradedLatticeBasis diagonal coe_divStar
  division_def

lemma Grading.hasNearLines_zero {x Q K n} (hL : Y.SpansLattice a π (divStar a ^ n)) (l : K ≤ Kf ..)
    (H : ∃ r ∈ Y.besselFin, r * x ∈ K) : Y.HasNearLines a Q n 0 x := by
  obtain ⟨⟨k, h, e⟩, r, hr, hk⟩ := hL, inv_surjective.exists.1 H
  refine ⟨_ * r * _ * (V.xFin * k⁻¹), _, ⟨.mul (M := V.ratCoordMatrixFin r) ?t ?g, by
    simpa using mul_mem h (l hk), (mul_apply_string_of_blockTriangular ?t ?g · |>.trans ?_)⟩,
    fun _ _ ↦ by rw [sub_self]; simp⟩ <;> simp [besselFin,
    mem_besselGroup_iff, ratCoordMatrix_inr, apply_ite, ↓reindex_equiv
    Y.indexEquiv] at hr <;> simp [reindex_equiv Y.indexEquiv, apply_ite Units.val, *] <;> grind

lemma Grading.inclXFin_mem_Kf {P u h} (hL : Y.SpansLattice a π u) (p : IsSplitSquarefree P N π)
    (H : h.1 ∈ congruenceGL (Ô E ∙ ↑π) .inr) : Y.inclXFin h ∈ Kf .. := hL.elim fun _ a ↦ by
  have r : IsIntMatrix _ (of _) := (a.1.isIntMatrix <| Y.indexEquiv <| .inl ·)
  by_cases Odd s <;> [have := isIntMatrix_scaleAt_sub_one π (Sum.inr ()) (by grind
    [IsSplitSquarefree]) H; have := H.1.isIntMatrix.sub .one] <;> simpa [show (Y.inclXFin h).1.1 =
    V.xFin⁻¹ * (V.ratCoordMatrixFin (Y.inclXFin h) - 1) * V.xFin + 1 by simp [ratCoordMatrixFin,
    sub_mul, mul_sub], mul_apply, ratCoordMatrixFin_inclXFin, Y.2, gradedGram, ↓inv_eq_left_inv
    gram_xFin, (reindex_equiv Y.indexEquiv).2, IsIntMatrix, apply_ite star, Matrix.mul_assoc,
    mem_Kf, *] using (r.isInt_conjTranspose.mul (this.mul r)).add .one
