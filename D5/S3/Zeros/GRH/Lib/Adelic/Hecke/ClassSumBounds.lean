/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Hecke/ClassSumBounds
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Hecke/ClassSumBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Hecke.ClassSumBounds. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Hecke/ClassSumBounds.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Construction.FockThetaFunctions
import D5.S3.Zeros.GRH.Lib.CM.FormalGroup.FormalHeight
import D5.S3.Zeros.GRH.Lib.LocalGL.Green.LabelIdempotents
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Formula.ZeroTermHeight
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter.LevelModulus
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.TestRings
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Abstract Hecke operators of a pair (G,K), level eigenspaces, weighted class sums (known
result; see Lib.Adelic.Hecke.ClassMean).

This file: Class sums stay integral after clearing automorphism orders; triangle inequality for
their norms. -/


open NumberField HasFiniteType Nat
variable {E V} [Field E] [CMType E] [Fintype V] {p} [Fact (Nat.Prime p)] {κ : InfinitePlace E → _}
  {G} [Group G] [TopologicalSpace G] {Γ K} [@HasFiniteType G _ Γ K _] {B} {f : G →
  WeylIndex V κ → ℂ}

lemma weylGauge_classSum_le_one g {e A} [PadicPlace p] (hA : ∀ x,
  Nat.card (classAut Γ K x) ∣ A) {c : ℂ} (h : ∀ x, weylGauge κ e g (c • f x) ≤ 1) : weylGauge κ e g
  ((A * c) • classSum Γ K f) ≤ 1 := by simpa [mul_smul,
  cast_smul_eq_nsmul] using! smul_classSum_mem (AddSubmonoid.mk ⟨{x | weylGauge .. ≤ 1},
  by simp_all [weylGauge, (IsUltrametricDist.norm_add_le_max ..).trans]⟩ (by simp [weylGauge])) hA h

lemma sqrt_weylNormSq_classSum_le (σ : ℂ ≃+* ℂ) (h : ∀ x, √(weylNormSq (σ ∘ f x)) ≤
  B) : √(weylNormSq (σ ∘ classSum Γ K f)) ≤ Nat.card (DoubleCosets Γ K) * B := by
  simp [classSum]; grw [sqrt_weylNormSq_sum_le]
  simp [← algebraMap_smul ℂ]; grw [cast_inv_le_one, h]; simp
