/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Places/FrobeniusOnRoots
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Places/FrobeniusOnRoots
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Places.FrobeniusOnRoots. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Places/FrobeniusOnRoots.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.PadicDecomposition
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Frobenius of Q_ℓ raises prime-to-ℓ roots of unity to powers of ℓ. -/


variable {ℓ} [Fact ℓ.Prime] {φ : Gp ℓ} {q M z}

lemma isUniformiser_ell : IsUniformiser (intQpBar ℓ) (Units.mk0 (ℓ : ℚ_[ℓ]) NeZero.out).1 := (by
  simpa [valuation_intQpBar_le_iff, norm_p_eq_inv] using ·.norm_lt_pow_iff_norm_le_pow_sub_one 0)

lemma valuation_natCast_eq_one : ¬ℓ ∣ M → intQpBar ℓ M = 1 := by
  erw [eq_iff_le_not_lt, valuation_intQpBar_lt_one_iff, PadicAlgCl.norm_extends _ M]; simp

lemma apply_eq_pow_of_isFrob (hφ : IsFrob (intQpBar ℓ) q φ) (hM : ¬ℓ ∣ M) : z ^ M = 1 → φ z = z ^
  q := by cases M; aesop; apply cycCharMod_eq_iff.1 (hφ.cycCharMod_eq (valuation_natCast_eq_one hM))

lemma exists_apply_eq_pow (hM : ¬ℓ ∣ M) (hz : z ^ M = 1) (g : Gp ℓ) : ∃ n, g z = z ^ ℓ ^ n :=
  isLocalGalois_padic.frobenius_spec.rec fun ⟨_, h⟩ H ↦
  (H.1 h).induction_on g (isClosed_setOf_smul z (∃ n, · = z ^ ℓ ^ n))
  fun ⟨n, i⟩ ↦ ⟨n, by grind [apply_eq_pow_of_isFrob ((h.pow n).mul_iff.2 i.2), residueCard_padic]⟩
