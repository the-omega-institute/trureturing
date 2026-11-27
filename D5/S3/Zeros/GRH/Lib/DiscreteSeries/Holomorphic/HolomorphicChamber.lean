/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicChamber
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicChamber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Holomorphic.HolomorphicChamber. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Holomorphic/HolomorphicChamber.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Holomorphic.HolomorphicMinor
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Holomorphic discrete series: highest coefficient and reproducing property (known
result; see Lib.DiscreteSeries.Holomorphic.HolomorphicExtension).

This file: Discrete series coefficient equals a product of minors in the holomorphic chamber. -/


open Finset Fintype GlModule HCParam.IsKHighest Int Finite

/-- Holomorphic discrete series: order o with signs +1 first, w K-dominant, w_i+γ ≤ w_j for ε_i
= 1, ε_j = −1, γ > 500n³+A+n+1, λ_i = w_i + (n+1)/2 − i with i the rank in o. Then λ has gap
500n³+A and ψ_λ = `holMinors` ε w on U(diag ε).

Known result: Holomorphic discrete series: highest coefficient and reproducing property. -/
lemma dsCoeff_eq_holMinors {n} [Fintype n] {ε o} (ho :
  @IsPosFirstOrder n ε o) [Nonempty n] A γ w (hu : IsKDominant ε o w) (hw : HasHolGap ε w γ)
  (h : 500 * card n ^ 3 + A + card n + 1 < γ) : let l : HCParam ε := 2 * w + twoRho (-o) ⊤
  l.HasLargeGap A ∧ ∀ g : USign ε, l.dsCoeff g = holMinors ε w g := ho.rec (by
  intro t _ l
  clear_value (L : l = _)
  simp [funext_iff, twoRho] at L
  have k a b (q : o a < o b) : ite (ε a = ε b) (l b < l a) (2 * (γ - card n) ≤ l b - l a) := by
    grind -abstractProof [IsKDominant, HasHolGap, twoRho, twoRho_lt_twoRho q, units_eq_one_or (ε _)]
  have hg : l.HasLargeGap A := ⟨(by grind -abstractProof [o · |>.lt_or_le <| o ·]),
    (by grind -abstractProof [card_lt_add_card_gt_add_one t ·]), gapThreshold.eq_1 n A ▸ mod_cast by grind -abstractProof⟩
  obtain ⟨rfl, x⟩ := (by grind -abstractProof [(by simpa [twoRho, ← sum_boole, ← sum_sub_distrib, add_assoc,
    ← sum_add_distrib] using (L · ▸ two_mul_lowestKType hg _ :))] : l.lowestKType = w),
    isKHighest_dsGenerator hg
  simpa [holMinorsPi, hg] using
    ((isHolOfWeight_coeffMap (c := fun _ g ↦ ⟨⟨(·.1.1 g), by simp⟩, by simp⟩) t (fun _ ↦ ⟨x.1, by
    have ⟨(a, b), m⟩ := exists_max fun (a, b) ↦
      ite (l.dsAction.E a b l.dsGenerator = 0) 0 (o b - o a)
    by_contra; have := casimir_bound hg.isUnitaryCasimirGe_dsAction.1
      ⟨(x.E_word_eq_wordWeight_smul [(a, b)] · |>.1), by simp +contextual [word,
      apply_apply_eq_swap_add_bracket, x.2, map_single_mul_single, DFunLike.ite_apply] at *; grind -abstractProof⟩
    simp [word, sub_mul] at *
    grind -abstractProof [x.2 a]⟩) (fun _ _ _ _ ↦ hasDerivAt_rightDeriv_expU _ _ _)
    (.mkPiAlgebra ..)).eq_holMinorsPi_mul ho (by simpa) (by simp [← dsCoeff_inv]) ![·]))
