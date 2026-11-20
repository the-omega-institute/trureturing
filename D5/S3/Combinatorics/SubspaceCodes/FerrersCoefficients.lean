/- GID: D5/S3/Combinatorics/SubspaceCodes/FerrersCoefficients
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubspaceCodes/FerrersCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The coefficients recover the full parameter tuple and enforce the two support cuts. -/

import D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The linear coefficient map -/

namespace D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine

open Module

section

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Algebra F E] [Finite E]
variable {K L : IntermediateField F E}

/-- Four coordinates in the larger subfield and one in the smaller subfield.

Used by
- `FerrersRankNine.codeMap`
- `FerrersRankNine.codeMap_rank` -/
abbrev Params {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) := L × L × L × L × K

private def paramU : Params K L →ₗ[F] E :=
  L.val.toLinearMap.comp (LinearMap.fst F _ _)

private def paramA1 : Params K L →ₗ[F] E :=
  L.val.toLinearMap.comp ((LinearMap.fst F _ _).comp (LinearMap.snd F _ _))

private def paramA2 : Params K L →ₗ[F] E :=
  L.val.toLinearMap.comp ((LinearMap.fst F _ _).comp
    ((LinearMap.snd F _ _).comp (LinearMap.snd F _ _)))

private def paramV (c : E) : Params K L →ₗ[F] E :=
  (L.val.toLinearMap.comp (LinearMap.fst F _ _) +
    ((LinearMap.mulLeft F c).comp K.val.toLinearMap).comp (LinearMap.snd F _ _)).comp
    ((LinearMap.snd F _ _).comp ((LinearMap.snd F _ _).comp (LinearMap.snd F _ _)))

private def paramA3 (b c : E) : Params K L →ₗ[F] E :=
  (LinearMap.mulLeft F (b ^ Fintype.card F ^ 3 - b)⁻¹).comp
    (paramV c - (LinearMap.mulLeft F b).comp paramU)

/-- The linear solution map for the two coefficient recovery equations.

Used by
- `FerrersRankNine.codeMap`
- `FerrersRankNine.codeMap_rank`
- `FerrersRankNine.codeMap_injective`
- `FerrersRankNine.codeMap_supported`
- `FerrersRankNine.exists_supported_dim27_with_rank` -/
def paramCoefficients (b c : E) : Params K L →ₗ[F] (Fin 4 → E) :=
  LinearMap.pi ![paramU - paramA3 b c, paramA1, paramA2, paramA3 b c]

omit [Finite E] in
private theorem paramA3_mul_delta (b c : E) (hb : b ^ Fintype.card F ^ 3 - b ≠ 0)
    (p : Params K L) :
    paramA3 b c p * (b ^ Fintype.card F ^ 3 - b) =
      (p.2.2.2.1 : E) + c * (p.2.2.2.2 : E) - b * (p.1 : E) := by
  change (b ^ Fintype.card F ^ 3 - b)⁻¹ * _ * (b ^ Fintype.card F ^ 3 - b) = _
  rw [mul_comm _ (b ^ Fintype.card F ^ 3 - b), ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  rfl

omit [Finite E] in
/-- The coefficient tuple determines all five parameters.

Used by
- `FerrersRankNine.codeMap_injective` -/
theorem paramCoefficients_injective {b : E} (hb : b ^ Fintype.card F ^ 3 - b ≠ 0)
    (β : Basis (Fin 4) K E) (hKL : K ≤ L)
    (hL : β.flag 2 = (IntermediateField.extendScalars hKL).toSubalgebra.toSubmodule) :
    Function.Injective (paramCoefficients (K := K) (L := L) b (β 2)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro p hp
  change paramCoefficients b (β 2) p = 0 at hp
  have hzero (i : Fin 4) := congrFun hp i
  have h3 : paramA3 b (β 2) p = 0 := hzero 3
  have h0 : (p.1 : E) = 0 := by
    have h := hzero 0
    change (p.1 : E) - paramA3 b (β 2) p = 0 at h
    simpa only [h3, sub_zero] using h
  have h1 : (p.2.1 : E) = 0 := hzero 1
  have h2 : (p.2.2.1 : E) = 0 := hzero 2
  have hv := paramA3_mul_delta b (β 2) hb p
  rw [h3, h0, zero_mul, mul_zero, sub_zero] at hv
  have hℓ : β.repr (p.2.2.2.1 : E) 2 = 0 := by
    apply β.mem_flag_iff_repr_eq_zero.mp
    · rw [hL]
      exact p.2.2.2.1.property
    · decide
  have hrepr := congrArg (fun x => β.repr x (2 : Fin 4)) hv
  have hmul : β 2 * (p.2.2.2.2 : E) = p.2.2.2.2 • β 2 := by
    rw [Algebra.smul_def, mul_comm, IntermediateField.algebraMap_apply]
  rw [hmul] at hrepr
  simp only [map_zero, Finsupp.zero_apply, map_add, Finsupp.add_apply, hℓ, zero_add, map_smul,
    Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hrepr
  have h4 : p.2.2.2.2 = 0 := hrepr.symm
  have hlast : (p.2.2.2.1 : E) = 0 := by
    rw [h4] at hv
    simpa using hv.symm
  exact Prod.ext (Subtype.ext h0) (Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2)
    (Prod.ext (Subtype.ext hlast) h4)))

private theorem pow_q_cubed_coe (hK : finrank F K = 3) (x : K) :
    (x : E) ^ Fintype.card F ^ 3 = (x : E) := by
  let : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F ^ 3 := by
    rw [Module.card_eq_pow_finrank (K := F), hK]
  conv_lhs => rw [← hc]
  exact congrArg (fun x : K => (x : E)) (FiniteField.pow_card x)

/-- Evaluate on the smaller intermediate field.

Used by
- `FerrersRankNine.codeMap_supported` -/
theorem evaluation_on_K (hK : finrank F K = 3) (b c : E) (p : Params K L) (x : K) :
    evaluateLinearized F E (paramCoefficients b c p) (x : E) =
      (p.1 : E) * (x : E) + (p.2.1 : E) * (x : E) ^ Fintype.card F +
        (p.2.2.1 : E) * (x : E) ^ Fintype.card F ^ 2 := by
  rw [evaluateLinearized_apply, Fin.sum_univ_four]
  change ((p.1 : E) - paramA3 b c p) * (x : E) ^ Fintype.card F ^ (0 : ℕ) +
    (p.2.1 : E) * (x : E) ^ Fintype.card F ^ (1 : ℕ) +
    (p.2.2.1 : E) * (x : E) ^ Fintype.card F ^ (2 : ℕ) +
    paramA3 b c p * (x : E) ^ Fintype.card F ^ (3 : ℕ) = _
  rw [pow_q_cubed_coe hK x]
  simp only [pow_zero, pow_one]
  ring

/-- Evaluate on the smaller field multiplied by the chosen vector.

Used by
- `FerrersRankNine.codeMap_supported` -/
theorem evaluation_on_bK (hK : finrank F K = 3) (b c : E)
    (hb : b ^ Fintype.card F ^ 3 - b ≠ 0) (p : Params K L) (x : K) :
    evaluateLinearized F E (paramCoefficients b c p) (b * (x : E)) =
      ((p.2.2.2.1 : E) + c * (p.2.2.2.2 : E)) * (x : E) +
        (p.2.1 : E) * (b * (x : E)) ^ Fintype.card F +
        (p.2.2.1 : E) * (b * (x : E)) ^ Fintype.card F ^ 2 := by
  rw [evaluateLinearized_apply, Fin.sum_univ_four]
  change ((p.1 : E) - paramA3 b c p) * (b * (x : E)) ^ Fintype.card F ^ (0 : ℕ) +
    (p.2.1 : E) * (b * (x : E)) ^ Fintype.card F ^ (1 : ℕ) +
    (p.2.2.1 : E) * (b * (x : E)) ^ Fintype.card F ^ (2 : ℕ) +
    paramA3 b c p * (b * (x : E)) ^ Fintype.card F ^ (3 : ℕ) = _
  rw [mul_pow b (x : E) (Fintype.card F ^ 3), pow_q_cubed_coe hK x]
  simp only [pow_zero, pow_one]
  have h := paramA3_mul_delta b c hb p
  linear_combination (x : E) * h

end

end D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine
