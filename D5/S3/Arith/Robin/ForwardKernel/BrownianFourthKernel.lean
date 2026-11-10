/- GID: D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Brownian pairing integrals and strict excess kurtosis for dyadic sampling. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.TriangularMeanSquare
import D5.S3.Arith.Robin.ForwardKernel.DyadicMacroMoments

/-! Fourth Brownian pairing integrals and the strict dyadic kurtosis inequality. -/

namespace D5.S3.Arith.Robin.ForwardKernel.BrownianFourthKernel

open Set MeasureTheory
open VarianceTransferDefs MomentTransferDefs DyadicMacroMoments

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The dyadic scale mixture has kurtosis strictly greater than three. -/
theorem three_lt_kurtosis_ratio {κ : ℝ} (hκ : 0 < κ) :
    3 < 3 * κ * (2 ^ (2 * κ) - 1) * Real.log 2 /
      (2 * (2 ^ κ - 1) ^ 2) := by
  have hm := dyadic_macro_moment_strict_mul hκ hκ
  have hp := dyadic_macro_moment_pos hκ
  have hr : 1 < dyadicMacroMoment (κ + κ) /
      (dyadicMacroMoment κ * dyadicMacroMoment κ) :=
    (lt_div_iff₀ (mul_pos hp hp)).mpr (by simpa only [one_mul] using hm)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : 0 < (2 : ℝ) ^ κ - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hκ)
  calc
    3 < 3 * (dyadicMacroMoment (κ + κ) /
        (dyadicMacroMoment κ * dyadicMacroMoment κ)) := by linarith
    _ = _ := by
      rw [dyadic_macro_moment_eq (add_pos hκ hκ), dyadic_macro_moment_eq hκ,
        show κ + κ = 2 * κ by ring]
      field_simp [hκ.ne', hl.ne', hpow.ne']

private def splitFour : (Fin 4 → ℝ) ≃ᵐ (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ))

private lemma splitFour_preserving :
    MeasurePreserving splitFour (cubeMeasure 4) ((cubeMeasure 2).prod (cubeMeasure 2)) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => unitMeasure)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin 4 => unitMeasure)
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm

/-- The profile-weighted Brownian covariance kernel on two coordinates. -/
def pairKernel (g : ℝ → ℝ) (s : Fin 2 → ℝ) : ℝ :=
  g (s 0) * g (s 1) * min (s 0) (s 1)

/-- An integrable profile gives an integrable Brownian covariance pair. -/
lemma pairKernel_integrable {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    Integrable (pairKernel g) (cubeMeasure 2) := by
  exact (measurePreserving_finTwoArrow unitMeasure).integrable_comp_of_integrable
    (TriangularMeanSquare.min_kernel_integrable hg)

/-- Integrating a Brownian covariance pair gives the min-kernel quadratic energy. -/
lemma integral_pairKernel {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    (∫ s, pairKernel g s ∂cubeMeasure 2) = Q g := by
  have hp := measurePreserving_finTwoArrow unitMeasure
  rw [show (∫ s, pairKernel g s ∂cubeMeasure 2) =
      ∫ p : ℝ × ℝ, g p.1 * g p.2 * min p.1 p.2 ∂unitMeasure.prod unitMeasure from
        hp.integral_comp' (fun p : ℝ × ℝ => g p.1 * g p.2 * min p.1 p.2)]
  have hi := hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)
    (g := fun p : ℝ × ℝ => g p.1 * g p.2 * min p.1 p.2)
    |>.mp (pairKernel_integrable hg)
  rw [integral_prod _ hi]
  simp only [Q, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]

/-- Integrable functions of two disjoint coordinate pairs factor under every permutation. -/
theorem pair_product_integrable_and_integral
    {F H : (Fin 2 → ℝ) → ℝ}
    (hF : Integrable F (cubeMeasure 2))
    (hH : Integrable H (cubeMeasure 2))
    (e : Equiv.Perm (Fin 4)) :
    Integrable
      (fun s : Fin 4 → ℝ =>
        F ![s (e 0), s (e 1)] * H ![s (e 2), s (e 3)])
      (cubeMeasure 4) ∧
    (∫ s : Fin 4 → ℝ,
      F ![s (e 0), s (e 1)] * H ![s (e 2), s (e 3)] ∂cubeMeasure 4) =
        (∫ u, F u ∂cubeMeasure 2) * (∫ v, H v ∂cubeMeasure 2) := by
  let K (s : Fin 4 → ℝ) := F ![s 0, s 1] * H ![s 2, s 3]
  have hK : K = (fun p => F p.1 * H p.2) ∘ splitFour := by
    funext s
    have hleft : (splitFour s).1 = ![s 0, s 1] := by
      funext i
      fin_cases i <;> rfl
    have hright : (splitFour s).2 = ![s 2, s 3] := by
      funext i
      fin_cases i <;> rfl
    simp only [Function.comp_apply, hleft, hright, K]
  have hKi : Integrable K (cubeMeasure 4) := by
    rw [hK]
    exact splitFour_preserving.integrable_comp_of_integrable (hF.mul_prod hH)
  have hKI : (∫ s, K s ∂cubeMeasure 4) =
      (∫ u, F u ∂cubeMeasure 2) * (∫ v, H v ∂cubeMeasure 2) := by
    rw [hK]
    exact (splitFour_preserving.integral_comp' (fun p => F p.1 * H p.2)).trans
      (integral_prod_mul F H)
  let ep := (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) e).symm
  have hep : MeasurePreserving ep (cubeMeasure 4) (cubeMeasure 4) :=
    (measurePreserving_piCongrLeft (fun _ : Fin 4 => unitMeasure) e).symm
  change Integrable (K ∘ ep) (cubeMeasure 4) ∧ _
  exact ⟨hep.integrable_comp_of_integrable hKi, (hep.integral_comp' K).trans hKI⟩

/-- The three Brownian pairings each contribute the square of the min-kernel energy. -/
theorem brownianW4_integral {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    (∫ s, (∏ i, g (s i)) * brownianW4 s ∂cubeMeasure 4) = 3 * Q g ^ 2 := by
  have hpair := pairKernel_integrable hg
  have h₁ := pair_product_integrable_and_integral hpair hpair (Equiv.refl _)
  have h₂ := pair_product_integrable_and_integral hpair hpair (Equiv.swap 1 2)
  have h₃ := pair_product_integrable_and_integral hpair hpair (Equiv.swap 1 3)
  rw [integral_pairKernel hg] at h₁ h₂ h₃
  simp only [Equiv.refl_apply, Equiv.swap_apply_def, pairKernel,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h₁ h₂ h₃
  norm_num at h₂ h₃
  have he (s : Fin 4 → ℝ) : (∏ i, g (s i)) * brownianW4 s =
      (g (s 0) * g (s 1) * min (s 0) (s 1)) *
        (g (s 2) * g (s 3) * min (s 2) (s 3)) +
      (g (s 0) * g (s 2) * min (s 0) (s 2)) *
        (g (s 1) * g (s 3) * min (s 1) (s 3)) +
      (g (s 0) * g (s 3) * min (s 0) (s 3)) *
        (g (s 2) * g (s 1) * min (s 2) (s 1)) := by
    rw [Fin.prod_univ_four]
    dsimp [brownianW4]
    rw [min_comm (s 2) (s 1)]
    ring
  simp_rw [he]
  have hadd := integral_add (h₁.1.add h₂.1) h₃.1
  have hadd12 := integral_add h₁.1 h₂.1
  simp only [Pi.add_apply] at hadd hadd12
  rw [hadd, hadd12, h₁.2, h₂.2, h₃.2]
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.BrownianFourthKernel
