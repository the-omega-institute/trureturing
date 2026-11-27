/- GID: D5/S3/Zeros/GRH/New/Exchange/ChainNorms
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/ChainNorms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.ChainNorms. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/ChainNorms.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.TriangleArrows
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Injectivity and norm of a chain of theta lifts (see New.Exchange.TriangleArrows).

This file: Chain of theta lifts is injective; its inner product and level index count. -/

namespace Data

open Finset Fintype Subgroup LevelPlaces
variable {P} (D : Data P) (ϑ : D.MFoldTwist)
seal dsKernel U

attribute [-simp] Bool.cond_eq_ite
attribute [local simp] Bool.cond_true Bool.cond_false

/-- There are a number C and an integer k such that, for all m-fold twists ϑ of modulus Q, [K₀ :
J_m] = C·N(Q)^k·δ^m·N_m/(N₀N₁^m). Here J_m is the level of `Data.lastResLevel`, δ =
`AuxPair.gramFactor` of the first auxiliary pair, N_n = `Data.triangleOrder` false ϑ n. -/
lemma stdLevelIndex_lastResLevel_eq : ∃ C, ∃ k : ℤ, ∀ ϑ :
  D.MFoldTwist, let w := triangleOrder false ϑ; stdLevelIndex (levelOf _ (D.lastResLevel ϑ)) = C *
    card (D.𝔪 ϑ 0).ResRing ^ k * (D.auxPair ϑ 1).gramFactor ^ D.m * w D.m / (w 0 * w 1 ^ D.m) := by
  choose k K using card_parabolic_blockNumber D.RowIndex (Fin _)
  use D.triangleOrder false 1 0 * (D.triangleOrder false 1 1 / (D.auxPair .one 1).gramFactor) ^ D.m,
    (k 1 - D.t * card D.RowIndex) * D.m - k D.m, fun ϑ ↦ ?_
  let := Prop.linearOrder
  have f n w : _ = Nat.card (GL (D.GridIndex false 0 n) _) :=
    K n (ResField ((D.levelPlaces ϑ).twistPlace w)) ▸ index_mul_card _
  simp +instances [inf_top_eq, inf_bot_eq, ↓fun R [CommRing R] ↦ (ext fun _ ↦ forall₂_congr
    (by simp! [lt_iff_le_and_ne]) : parabolic (R := R) (· ∉ Set.range (.inl : D.RowIndex ↪ D.Y 1)) =
    parabolic (blockNumber 1)), AuxPair.gramFactor, auxPair, AuxPair.rankDiff, triangleOrder,
    triangleModulus, lastResLevel, ← f 1, ← f D.m, auxLevel, index_rangeParabolic,
    card_levelModulus_resRing, LevelPlaces.card_GL_levelModulus, field, card_ResField,
    relIndex_levelOf, Nat.card_pi, index_pi_univ, div_pow,
    prod_eq_zero_iff, zpow_sub₀, zpow_add₀, zpow_mul, prod_pow,
    -Nat.card_eq_fintype_card, Bool.cond_false, -Bool.cond_eq_ite,
    @univ_eq_empty (D.levelPlaces .one).TwistIndex _ ⟨nofun⟩]
  field_simp [prod_eq_zero_iff, NeZero.ne]; ring!

/-- For forms x, y of level g on U(Y₀), ⟨ι_ϑx, ι_ϑy⟩ = [K₀ : J_m]·d·⟨ux, uy⟩, where J_m = the level
of `Data.lastResLevel` ϑ, d the dimension of the weight on Y_m, u the chain of m weighted lifts
Y₀ → Y_m of the triangle. -/
lemma inner_iotaAtLevel x y : let u := weightedChain (D.triangleOrder false) (D.triLift _) ϑ 0 D.m;
    inner ℂ (D.iotaAtLevel ϑ x) (D.iotaAtLevel ϑ y) = stdLevelIndex (levelOf _ (D.lastResLevel ϑ)) *
    card (WeylIndex (D.Y D.m) D.columnsY) * inner ℂ (u x.1) (u y.1) := by
  rw [LevelForm.inner_eq_petersson (D.spaceY _) D.isHCParam_Y]
  congr <;> simpa [weightedChain, triangleOrder, triangleModulus,
    LevelPlaces.card_GL_levelModulus] using! (D.spaceY _).ofAlgForm_toAlgForm D.isHCParam_Y _

/-- For every twist ϑ whose first m powers are twists, the composite ι_ϑ of the m theta lifts from
U(Y₀) to the definite U(Y_m) is injective on forms of principal level g on U(Y₀).

Proved from the norm formula `inner_iotaAtLevel`. -/
@[simp] lemma iotaAtLevel_injective : Function.Injective (D.iotaAtLevel ϑ) := .of_ker _ fun y e ↦
  (D.exists_isTriangle _).choose_spec.eq_zero_of_weightedChain D.m 0 (by simp) _
  (by simpa [e, -Fintype.card_pi] using! D.inner_iotaAtLevel ϑ y y)
