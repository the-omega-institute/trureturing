/- GID: D5/S3/Zeros/GRH/Lib/GLn/Dual/DualWeights
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/Dual/DualWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.Dual.DualWeights. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/Dual/DualWeights.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.CompactLift.RallisFormula
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.TestRings
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Dual of a Weyl module by Jacobi's complementary minors; Cartan component (known result;
see Lib.GLn.Branching.Branching).

This file: Integral invariant pairing of opposite weights; it gives the values of `ofAlgForm`. -/

open NumberField Matrix Finset Fintype

/-- For weights with parameters l and −l there is an invariant integer bilinear pairing A with:
F_η(x, g) = A(η(g), ρ(x)v⁺) for algebraic forms η of the second weight; CA = `hookNumber` κ'
for an integer matrix C; each A(·, v) = ⟨v', ·⟩ with ‖v'‖ = ‖v‖. -/
lemma exists_dual_pairing_of_isHCParam {E n} [Field E] [CMType E] [Fintype n] {κ κ' : InfinitePlace
  E → _} {e e' l} [Nonempty n] (h : IsHCParam κ e l) (h' : IsHCParam κ' e' (-l)) : ∃ A : Matrix _
  _ ℤ, (∀ R [Field R] [CharZero R] g v' (v : _ → R), weylRep _ e' g *ᵥ v' ⬝ᵥ A.map (↑) *ᵥ weylRep κ
  e g *ᵥ v = v' ⬝ᵥ A.map (↑) *ᵥ v) ∧ (∀ s (η : AlgForm n κ' e') x g, ofAlgForm (-l) s η (x, g) =
  (dotProductBilin ℂ ℂ).compl₂ (A.map (↑)).mulVecLin (η.1 g) (conjWeylRep κ e x (highestVector κ
  l))) ∧ (∃ C : Matrix _ _ ℤ, ∀ v : _ → ℂ, C.map (↑) *ᵥ A.map (↑) *ᵥ v = (hookNumber κ' (rankAt n) :
  ℂ) • v) ∧ ∀ v, ∃ v', weylNormSq v' = weylNormSq v ∧ ∀ u, u ⬝ᵥ A.map (↑) *ᵥ v = gramForm v' u := by
  choose p q using (exists_equiv_decrPosition <| h · |>.1)
  obtain ⟨N, Q⟩ := h.exists_decrPosition_eq, by simpa using h'.eq_hcParameter
  obtain ⟨J, K, -, b, hJ, H⟩ := exists_dual_isometry (κ := κ') (κ' := κ) p _ rfl fun w j _ ↦ by
    grind [hcParameter, @N w j (by grind), @N w (j - 1) (by grind)]
  refine have L R [Field R] [CharZero R] g := ?_; have s v u := ?_; ⟨weylGram n κ' * J, L,
    fun _ _ _ _ ↦ .trans (by rw [algFormCoeff_apply, ← star_highestVector]; simp [*, highestVector])
        ((L ..).symm.trans congr($((conjWeylRep ..).self_inv_apply ..) ⬝ᵥ _)),
        ⟨_, fun v ↦ by simpa [↓← map_intCast_mul_mulVec, b, ↓Jᵀ.mul_smul,
        weylGram_isSymm.eq, ← Matrix.mul_assoc, ← diagonal_intCast] using
        (congr((Jᵀ * $(weylGram_mul_fockPairing (n := n) (κ := κ')) * Kᵀ)ᵀ.map (↑) *ᵥ v))⟩,
    fun v ↦ ⟨star (J.map (↑) *ᵥ v), congrArg _ ((s ..).symm.trans ?_), s v⟩⟩
  simp [-smul_mulVec, ↓map_intCast_mul_mulVec, weylRep, weylGram_mul_schur, dotProduct_mulVec,
    vecMul_mulVec, ← transpose_mul, ← by simpa [weylRep, ← inv_smul_eq_iff, mul_smul,
    _root_.zpow_add] using (((H R).2 g).trans congr(_ * weylRep κ $(funext fun τ ↦ show _ =
    e' τ + e τ by grind [Ico_self, hcParameter, diagramWeight_apply,
    N τ (Nat.sub_one_lt card_ne_zero), _=_ Ico_add_one_left_eq_Ioo]) g)), ← Matrix.mul_assoc]
  rw [map_intCast_mul_mulVec, gramForm_apply, star_star, ← dotProduct_transpose_mulVec,
    weylGram_isSymm.map]
  simp [← hJ, ↓map_intCast_mul_mulVec, star_mulVec_dotProduct, conjTranspose, transpose_map,
    Function.comp_def]
