/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/HoweArgument
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/HoweArgument
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Theta.HoweArgument. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Theta/HoweArgument.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta.JointHarmonicUnique
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta correspondence of discrete series for real unitary dual pairs; joint harmonics
(known result; see Lib.DiscreteSeries.Theta.LocalThetaCorrespondence).

This file: Howe's argument: joint harmonic generates Fock space modulo other K-types. -/

open MvPolynomial Submodule Int Fischer

/-- Howe's count: let G be a space of polynomials stable under the column action, containing a
joint harmonic, the images of the row operators E_aa − Λ_a and compact lowerings, and 𝔤P for
each row K-highest P of weight outside Λ + `HCParam.rootCone`. Then G is everything. -/
lemma IsJointHarmonic.howe_argument {R C ι} [Fintype R] [Fintype C] [Fintype ι] {ε ε' l l' y}
    {T : @FockDualPair R C ε ε' ι} (hΦ : IsJointHarmonic T l l' y) G (hG : ∀ X,
  G ∈ (T.swap.oscRows X).invtSubmodule) (h0 : y ∈ G) (hc : ∀ {ν} P X, l.IsKHighest T.oscRows ν P →
  ν - l.lowestKType ∉ l.rootCone → T.oscRows X P ∈ G) (K : ∀ a b {P}, ε a = ε b → l b < l a →
  T.oscRows.E b a P ∈ G) (L : ∀ a {P}, T.oscRows.E a a P - (l.lowestKType a : ℂ)
  • P ∈ G) : G = ⊤ := eq_top_iff'.2 fun _ ↦ (@Int.strongRec 0 (polyDegreeLE · ≤ G) (by
  grind [polyDegreeLE, restrictSupport_eq_span, span_le]) (fun j _ ih ↦ by
  by_contra; choose _ y hy o _ k using l'.exists_highest_vector (perpInDegree j G) (by grind
    [left_eq_inf, inf_le_left, sup_orthogonal_inf_of_hasOrthogonalProjection, sup_bot_eq]) fun _ _ ↦
    (mapsTo_perpInDegree · (hG _))
  have w a := sub_eq_zero.1 (eq_zero_of_mem_perpInDegree (sub_mem (mapsTo_perpInDegree rfl
    (fun _ h ↦ (G.sub_mem_iff_left (G.smul_mem _ h)).1 (L a)) hy) (smul_mem _ _ hy)) (L a))
  have t a b e f :=
    eq_zero_of_mem_perpInDegree (mapsTo_perpInDegree e (fun _ _ ↦ K a b e f) hy) mem_top
  have D : T.swap.IsRowHarmonic y := fun _ _ ↦ (fockLaplacian_eq_zero ih hy · rfl (hG _ ·))
  have V c s := (polarisation_eq_of_isCompactPrimitive hΦ.gap.1 t D ..).2 (w c) ∘
    hΦ.sign_mul_lowestKType_sub_nonneg c s
  grind [smul_mem, eq_zero_of_mem_perpInDegree, hΦ.unique ⟨o, k,
    fockLaplacian_eq_zero_of_isKHighest ⟨w, t⟩ fun a b k H ↦ fockLaplacian_eq_zero ih hy k
    rfl fun _ ↦ by_cases (fun h ↦ by cases Or.imp (V b (-1)) (V a 1) (by simp; grind [hΦ.1, IsMatch,
    int_unit_val_eq_one_or_neg_one, by simpa using h (-l)]) <;> simp_all [glOp,
    _root_.pderiv_comm (T.varEquiv _), Finset.sum_eq_zero])
    (hc _ _ H), ⟨w, t⟩, D⟩ hΦ.2.isPreJointHarmonic]) _) fun _ ↦ ofNat_le.2 ∘ le_totalDegree
