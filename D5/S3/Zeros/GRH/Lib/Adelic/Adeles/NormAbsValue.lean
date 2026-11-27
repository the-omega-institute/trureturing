/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Adeles/NormAbsValue
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Adeles/NormAbsValue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Adeles.NormAbsValue. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Adeles/NormAbsValue.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.AdeleNorm
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.AdelicModulus
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus
(known result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: The adelic norm preserves the modulus; valuation of the local norm. -/

open NumberField WithZeroMulInt FinitePlace Algebra Valued HeightOneSpectrum


variable {K L} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {w : FinPlace L}

/-- For number fields L/K, the norm preserves the module of finite ideles: |N_{L/K}(y)| = |y|
for every finite idele y of L. -/
lemma finIdeleAbs_adeleNorm y : finIdeleAbs (.map (adeleNorm K L) y) = finIdeleAbs y :=
  (pow_left_inj₀ ideleAbs_nonneg_and_ne_zero.1 ideleAbs_nonneg_and_ne_zero.1 (classNumber_ne_zero
  L)).1 (let ⟨_, ⟨x, rfl⟩, u, h, e⟩ := Subgroup.mem_sup.1 (pow_classNumber_mem_principal_sup y)
  by simpa [↓← map_pow, ← e, norm_def, v_adeleNorm_eq_one h, mem_idelesUnitOff.1 h, finIdeleAbs,
    ideleAbs] using (finIdeleAbs_principalIdele (x.map _)).trans (norm_norm.substr
    (finIdeleAbs_principalIdele x).symm))

@[simp] lemma norm_localNorm y : ‖(localNorm K w y).1‖ = ‖y.1‖ := by
  simp [← finIdeleAbs_locIdele, ← adeleNorm_locIdele, finIdeleAbs_adeleNorm]

lemma v_localNorm {f} (hf : (w.below K).q ^ f = w.q) y : v (localNorm K w y).1 = v y.1 ^ f :=
    (toNNReal_strictMono (one_lt_absNorm_nnreal _)).injective (NNReal.eq (by
  simpa [norm_def, toNNReal_neg_apply, ← hf, ← zpow_natCast, zpow_comm] using norm_localNorm y))
