/- GID: D5/S3/Zeros/GRH/New/Exchange/CostOfSquares
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/CostOfSquares
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.CostOfSquares. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/CostOfSquares.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.TriangleNorms
import D5.S3.Zeros.GRH.New.SiegelWeil.DescentsVanishPlanes
import D5.S3.Zeros.GRH.New.Exchange.TriangleLevelExponent
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: general results applied to the objects of this proof.

This file: Cost in squares bookkeeping; exchange constants on the data cost one square. -/

namespace Data

open Finset Fintype Modulus MulChar
variable {P} {D : Data P} {n n' N : ℕ} {c c' : D.MFoldTwist → ℂ}

variable (D n c) in
/-- c costs n squares: for each family θ of fit twists (`Data.IsFitFamily`), the family
|c(θ_ι)/c(1)|⁻² has height (`HeightLe`) at most 2n t x^999. -/
def CostsSquares := ∀ θ, D.IsFitFamily θ → HeightLe (n * (2 * D.t * D.x ^ 999)) fun ι ↦
  (‖c (θ ι) / c 1‖ ^ 2 :)⁻¹

/-- Costs add in products: if the functions c, c′ on twists cost n and n′ squares in the sense
of `Data.CostsSquares`, and n + n′ ≤ N, then the pointwise product c·c′ costs N squares. -/
lemma CostsSquares.mul (h : D.CostsSquares n c) (h' : D.CostsSquares n' c') (e : n + n' ≤ N) :
  D.CostsSquares N (c * c')
  | θ, o => ((h θ o).mul (h' θ o)).mono (by grw [← e]; grind) (by simp [field])

/-- The residue ring of `Data.𝔪` = M^e·Q attached to ϑ has order (∏ N w)^e · ∏_{w ∈ Q} N w, the
first product running over the chosen places w above g. -/
lemma card_𝔪 e ϑ : card (D.𝔪 ϑ e).ResRing = (∏ i, (D.chosen i).q) ^ e * ϑ.levelNorm := by
  erw [LevelPlaces.card_levelModulus_resRing, prod_coe_sort, levelPlaces]

/-- If |c(ϑ)|² = C·|O_E/𝔪_ϑ|^k for all ϑ, with C real and k an integer independent of ϑ, and 𝔪_ϑ
= M^e Q(ϑ) the modulus `Data.𝔪`, then c costs 0 squares (`Data.CostsSquares`). -/
lemma CostsSquares.of_norm_sq_eq_mul_card_zpow e C (k : ℤ) (h : ∀ ϑ, ‖c ϑ‖ ^ 2 =
  C * card (D.𝔪 ϑ e).ResRing ^ k) : D.CostsSquares 0 c
  | _, o => o.heightLe_of_eq_zpow_mul (@.prod _ ∅ id 1 nofun) (by simp) fun _ _ ↦
    ⟨-k, by simp_all [div_pow, card_𝔪, mul_zpow, field, twist_one_spec]⟩

lemma CostsSquares.one : D.CostsSquares 0 1 := .of_norm_sq_eq_mul_card_zpow 0 1 0 (by simp)

/-- If ν is tame for the squarefree modulus 𝔪 (exponent e = 1) with character χ, then χ is
primitive: for each a ≠ 0 in O_E/𝔪 some χ(1 + ca) is neither 0 nor 1. -/
lemma isPrimitiveMulChar_of_isTameFor {ϑ ν γ χ} : IsTameFor (D.𝔪 ϑ 1) ν γ χ → IsPrimitiveMulChar χ
  | ⟨_, ψ, _, hψ, H⟩, a,
    n => have := matrix_ext_modulusResidue (x := !![a]) (y := 0) (D.levelPlaces ϑ).apart.1
    have ⟨w, m, _⟩ : ∃ w m, modulusResidue _ m a ≠ 0 := by by_contra!; simp_all [← Matrix.ext_iff]
    (ne_one_iff.1 ((hψ w).2 m)).elim fun x _ ↦
      (algebraMap_ResField_surjective w ((x - 1) / modulusResidue _ m a)).elim fun b (_ :
      modulusResidue _ m b = _) ↦ ⟨Modulus.reduction _ ⟨_, idem_mem_Ô {w}⟩ * ↑b, by
      simp_all [finprod_eq_single _ (Subtype.mk w m), apply_eq_zero_iff, charOfTamePart_apply]⟩

/-- Let (ν, z) be a pair ramified exactly at the chosen places, e ≥ 1, 1 ≤ n ≤ m. Each (νϑⁿ)⁻¹
is tame for the modulus 𝔪 = M^e Q(ϑ) (`Data.𝔪`), and every c with |c(ϑ)|² = C·Π(z) (`lValueProd`)
costs one square (`Data.CostsSquares`). -/
lemma exists_isTameFor_costsSquares_one (p : D.Pair) (r : p.IsRamified) e [NeZero e] (n :
  D.LiftIndex) : (∀ ϑ : D.MFoldTwist, IsTameFor (D.𝔪 ϑ e)
  (p.ν * ϑ.toAutChar ^ n.1)⁻¹ (p.c ·) (charOfTamePart _ (p.ψ * ϑ.ψ ^ n.1))⁻¹) ∧ ∀ {c C}, (∀ ϑ :
  D.MFoldTwist, ‖c ϑ‖ ^ 2 = C * lValueProd (D.𝔪 ϑ e).places (p.ν * ϑ.toAutChar ^ n.1)⁻¹ p.z) →
  D.CostsSquares 1 c := ⟨fun ϑ ↦ by simpa [Pi.neg_def] using! (isTameFor_of_hasWeight
  _ (p.hasWeight.mul (ϑ.powTwist n).hasWeight) r).inv, fun h θ o ↦ o.heightLe_of_eq_zpow_mul
  (.prod (s := Icc 1 p.z) fun _ _ ↦ (o.height_le n (p.lowerPoint _) 1 r).pow 2) (by simp [field,
  p.7.2]) fun ι _ ↦ ⟨-p.z ^ 2, have := p.lValueProd_eq 1 ((θ ι).powTwist n)
  by simp_all [div_pow, twist_one_spec, MFoldTwist.powTwist, TameChar.pow, places_modulus_eq_union]
     simp_all [field, sq, zpow_mul, pow_mul]⟩⟩
