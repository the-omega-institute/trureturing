/- GID: D5/S3/Zeros/GRH/Lib/Weil/Periods/DegreeOfT
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Periods/DegreeOfT
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Periods.DegreeOfT. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Periods/DegreeOfT.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Periods.FiniteBesselGroup
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Transfer of Bessel and Fourier–Jacobi periods under a theta lift (one unfolding step)
(known result; see Lib.Weil.Periods.UnfoldingStep).

This file: Minus the additive valuation, −ord_w, of a finite idele. The base point T: degree,
invariance modulo degree zero, T*T equals the shift. -/

/-- For a finite idele x, the integer −ord_w(x): the logarithm of its multiplicative valuation
at w, equal to −1 on a uniformiser. -/
noncomputable def ideleLogVal {E} [Field E] [NumberField E] (x : (𝔸f E)ˣ) w :=
  (Valued.v (x.1 w)).log

attribute [-instance] IsAddTorsionFree.of_isDomain_charZero instCharZeroOfIsSemireal

attribute [local simp] HasDegreeGe Grading.stringMap Grading.mem_besselGroup_iff entrywise

variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] [Fintype X] [Fintype X']
  {s ε ε' N} {V : Space E ι ε} {V' : Space E ι' ε'} (Y : Grading V N X s) {Y' :
  Grading V' N X' (s - 1)}

omit [Fintype X] [Fintype X'] in
lemma Grading.hasDegreeGe_neg_one_stringMap : HasDegreeGe Y'.gradeOf Y.gradeOf (-1)
  (Y.stringMap Y') := by simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv]; lia

/-- Let s' = s − 1. For g in `Grading.besselGroup` of Y and δ in that of Y', the map δTg − T has
degree at least 0, where T = `Grading.stringMap` and δ, g are read in rational coordinates. -/
lemma Grading.hasDegreeGe_zero_mul_stringMap_mul_sub {g δ} :
    g ∈ Y.besselGroup → δ ∈ Y'.besselGroup → HasDegreeGe Y'.gradeOf Y.gradeOf 0
  (V'.ratCoordMatrix δ * (Y.stringMap Y' * V.ratCoordMatrix g) - Y.stringMap Y') := by
  simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv]
  repeat' first | intro _ | constructor | grind [Finset.sum_eq_zero] | rw
    [Fintype.sum_eq_single ‹_›]

/-- For s' = s − 1, 𝖳*𝖳 is the shift `Grading.shift` of Y (X ↦ 0, e_i ↦ c·e_{i+1}, times −N at grade
0 and −Nc at grade 1); if Y, Y' have the same c, 𝖳𝖳* is the shift of Y'. -/
lemma Grading.formAdjoint_stringMap_mul_stringMap : V.formAdjoint V' (Y.stringMap Y') * Y.stringMap
  Y' = Y.shift ∧ (Y'.c = Y.c → Y.stringMap Y' * V.formAdjoint V' (Y.stringMap Y') =
  Y'.shift) := by
  cases s <;> simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv, Fin.sum_univ_castSucc,
    shift, ne_of_lt, apply_ite toAdele, Fin.forall_fin_succ', Fin.val_inj]
  simp [Y.formAdjoint_apply Y', apply_ite star, gradedGram, stringReversal]
  grind -etaStruct (splits := 20) [Y.3]
