/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/CasimirOnPsi
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/CasimirOnPsi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.FlenstedJensen.CasimirOnPsi. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/FlenstedJensen/CasimirOnPsi.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen.PsiSmooth
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.SmoothMatrices
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Flensted-Jensen's function is a Casimir eigenfunction with value |λ|²−|ρ|². -/


open Matrix Filter Norms.L2Operator ContinuousMap GlModule U HCParam
variable {n} [Fintype n] {ε h} {l : n → ℤ}

lemma exists_equiv_fin_lt_iff (hl : l.Injective) : ∃ e : Fin (Fintype.card n) ≃ n, ∀ a b,
  l (e a) < l (e b)
  ↔ a < b := ⟨_, fun _ _ ↦ lt_iff_lt_of_le_iff_le (@monoEquivOfFin n _ (.lift' l hl) _ rfl).2⟩

/-- For a parameter λ of gap h, the Casimir operator Ω = Σ E_ab E_ba, acting by right
derivatives, satisfies Ωψ_λ = (|λ|² − |ρ|²) ψ_λ.

Known result: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series. -/
lemma casimir_dsCoeffSmooth {l : @HCParam n ε} [hg : l.HasGap h] :
  (rightDeriv ε ℂ).casimirK 1 l.dsCoeffSmooth = (l.casimirValue : ℂ) • l.dsCoeffSmooth := by
  ext g; have ⟨_, hF, e⟩ := isAnalyticFamily_flenstedJensen g l analyticAt_const rfl
  obtain ⟨⟨_, d, e'⟩, _⟩ :=
    exists_contDiff_eventuallyEq hF.restrictScalars.contDiffAt, hg.neg.signs_one
  let f : SmoothU ε _ := ⟨_, ⟨_, d⟩, rfl⟩
  have ⟨L, ψ⟩ : ∃ L : StrongDual ℂ _, l.dsCoeffSmooth.1 =ᶠ[_] L ∘ f.1 :=
    ⟨l.lowestKType.kTypeNormSq⁻¹ • strongIntegral (haarK ε)
    (evalCLM ℂ), .mono (continuous_mat.tendsto _ (e.and (e'.and (tendsto_id.const_mul _
    (isAccretive_blockDiagPart_inv_mul g).2.setOf_mem_nhds)))) (by simp +contextual [f,
    strongIntegral_eval, dsCoeff_eq_flenstedJensen hg (blockDiagPart_mem g), flenstedJensen,
    field])⟩
  suffices ((rightDeriv ε C(_, ℂ)).casimirK 1 f).1 g = ((-l).compactForm.casimirKValue (paramAddRho
    l) : ℂ) • f.1 g by convert congr(L $this) <;> simp [casimir,
    (rightDeriv_comp_clm _ (rightDeriv_comp_clm _ ψ)).eq_of_nhds, ↓ψ.eq_of_nhds, casimirKValue,
    casimirValue, twoRho_neg, ← sub_eq_of_eq_add (two_mul_paramAddRho hg _)]; grind [twoRho]
  ext k; exact ((rightDeriv ε _).onRange ⟨⟨(Germ.ofFun <| evalCLM ℂ k ∘ ·.1), by simp⟩, by tauto⟩
    fun _ _ h ↦ (rightDeriv_comp_clm (f' := 0) _ (Quotient.exact h.symm)).germ_eq.symm.trans
    (by simp)).rec fun σ s ↦ congr($((by simp [↓casimirK_one_adTwist, casimir, s] :
    LinearMap.rangeRestrict _ (casimirK _ _ f) = _).trans (IsKHighest.casimirK_eq_smul (σ :=
    σ.adTwist k) (.of_E_eq_smul fun a b q o ↦
    (s _ f).trans (Subtype.ext (Quot.sound (.mono (continuous_mat.tendsto
    _ ((e.and e').eventually_nhds.and (hF.congr e'.symm).eventually_analyticAt)) fun y ⟨hy, _,
    D⟩ ↦ congr($(rightDeriv_eq_fderiv D.hasFDerivAt (by tauto) _) k).trans
    (fderiv_eq_of_borel_equivariant 1 ((evalCLM ℂ k).hasFDerivAt.comp _ D.hasFDerivAt) o q
    ((y * ·) ∘ (k * · * k⁻¹)) (hy.mono (by intros; simp_all [hy.self_of_nhds, ← mul_assoc, diagChar,
    field, hg.isKDominant_neg_paramAddRho.weightMinors_mul_borel hg.1]))))))))).1.value)
