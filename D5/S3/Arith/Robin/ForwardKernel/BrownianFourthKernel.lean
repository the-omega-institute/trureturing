/- GID: D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Brownian pairing integrals and strict excess kurtosis for dyadic sampling. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.TriangularMeanSquare
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Fourth Brownian pairing integrals and the strict dyadic kurtosis inequality. -/

namespace D5.S3.Arith.Robin.ForwardKernel.BrownianFourthKernel

open Set MeasureTheory
open VarianceTransferDefs MomentTransferDefs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma exp_pairing_strict {a : ℝ} (ha : 0 < a) :
    2 * (Real.exp a - 1) < a * (Real.exp a + 1) := by
  let f : ℝ → ℝ := fun t => t * (Real.exp t + 1) - 2 * (Real.exp t - 1)
  have hd (t : ℝ) : HasDerivAt f (1 + (t - 1) * Real.exp t) t := by
    convert ((hasDerivAt_id t).mul ((Real.hasDerivAt_exp t).add_const 1)).sub
      (((Real.hasDerivAt_exp t).sub_const 1).const_mul 2) using 1
    · rfl
    · simp only [id_eq]; ring
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (by fun_prop)
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hd t).deriv]
    have he := mul_lt_mul_of_pos_right (Real.add_one_lt_exp (neg_ne_zero.mpr ht.ne'))
      (Real.exp_pos t)
    rw [← Real.exp_add] at he
    simp only [neg_add_cancel, Real.exp_zero] at he
    nlinarith
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) ha.le ha
  simpa [f] using h

private lemma kurtosis_ratio_identity {κ : ℝ} (hκ : 0 < κ) :
    κ * (2 ^ (2 * κ) - 1) * Real.log 2 / (2 * (2 ^ κ - 1) ^ 2) =
      (κ * Real.log 2) * (Real.exp (κ * Real.log 2) + 1) /
        (2 * (Real.exp (κ * Real.log 2) - 1)) := by
  have ha : 0 < κ * Real.log 2 := mul_pos hκ (Real.log_pos (by norm_num))
  have he : Real.exp (κ * Real.log 2) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr ha)).ne'
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show Real.log 2 * (2 * κ) = κ * Real.log 2 + κ * Real.log 2 by ring,
    Real.exp_add, show Real.log 2 * κ = κ * Real.log 2 by ring]
  field_simp
  ring

/-- The dyadic scale mixture has kurtosis strictly greater than three. -/
theorem three_lt_kurtosis_ratio {κ : ℝ} (hκ : 0 < κ) :
    3 < 3 * κ * (2 ^ (2 * κ) - 1) * Real.log 2 /
      (2 * (2 ^ κ - 1) ^ 2) := by
  have ha : 0 < κ * Real.log 2 := mul_pos hκ (Real.log_pos (by norm_num))
  have hd : 0 < 2 * (Real.exp (κ * Real.log 2) - 1) := by
    exact mul_pos (by norm_num) (sub_pos.mpr (Real.one_lt_exp_iff.mpr ha))
  calc
    3 < 3 * ((κ * Real.log 2) * (Real.exp (κ * Real.log 2) + 1) /
        (2 * (Real.exp (κ * Real.log 2) - 1))) := by
      have h : 1 < (κ * Real.log 2) * (Real.exp (κ * Real.log 2) + 1) /
          (2 * (Real.exp (κ * Real.log 2) - 1)) :=
        (lt_div_iff₀ hd).mpr (by simpa only [one_mul] using exp_pairing_strict ha)
      linarith
    _ = _ := by rw [← kurtosis_ratio_identity hκ]; ring

private def splitFour : (Fin 4 → ℝ) ≃ᵐ (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ))

private lemma splitFour_preserving :
    MeasurePreserving splitFour (cubeMeasure 4) ((cubeMeasure 2).prod (cubeMeasure 2)) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => unitMeasure)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin 4 => unitMeasure)
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm

private def pairKernel (g : ℝ → ℝ) (s : Fin 2 → ℝ) : ℝ :=
  g (s 0) * g (s 1) * min (s 0) (s 1)

private lemma pairKernel_integrable {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    Integrable (pairKernel g) (cubeMeasure 2) := by
  exact (measurePreserving_finTwoArrow unitMeasure).integrable_comp_of_integrable
    (TriangularMeanSquare.min_kernel_integrable hg)

private lemma integral_pairKernel {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
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

private lemma pairing_integrable_and_integral {g : ℝ → ℝ} (hg : ProfileIntegrable g)
    (e : Equiv.Perm (Fin 4)) :
    Integrable (fun s =>
      g (s (e 0)) * g (s (e 1)) * g (s (e 2)) * g (s (e 3)) *
        (min (s (e 0)) (s (e 1)) * min (s (e 2)) (s (e 3)))) (cubeMeasure 4) ∧
    (∫ s, g (s (e 0)) * g (s (e 1)) * g (s (e 2)) * g (s (e 3)) *
        (min (s (e 0)) (s (e 1)) * min (s (e 2)) (s (e 3))) ∂cubeMeasure 4) = Q g ^ 2 := by
  let F (s : Fin 4 → ℝ) :=
    g (s 0) * g (s 1) * g (s 2) * g (s 3) *
      (min (s 0) (s 1) * min (s 2) (s 3))
  have hF : F = (fun p => pairKernel g p.1 * pairKernel g p.2) ∘ splitFour := by
    funext s
    change g (s 0) * g (s 1) * g (s 2) * g (s 3) *
      (min (s 0) (s 1) * min (s 2) (s 3)) =
      g (s 0) * g (s 1) * min (s 0) (s 1) *
        (g (s 2) * g (s 3) * min (s 2) (s 3))
    ring
  have hFi : Integrable F (cubeMeasure 4) := by
    rw [hF]
    exact splitFour_preserving.integrable_comp_of_integrable
      ((pairKernel_integrable hg).mul_prod (pairKernel_integrable hg))
  have hFI : (∫ s, F s ∂cubeMeasure 4) = Q g ^ 2 := by
    rw [hF]
    calc
      _ = ∫ p, pairKernel g p.1 * pairKernel g p.2
          ∂(cubeMeasure 2).prod (cubeMeasure 2) :=
        splitFour_preserving.integral_comp' (fun p => pairKernel g p.1 * pairKernel g p.2)
      _ = _ := by rw [integral_prod_mul, integral_pairKernel hg, pow_two]
  let ep := (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) e).symm
  have hep : MeasurePreserving ep (cubeMeasure 4) (cubeMeasure 4) :=
    (measurePreserving_piCongrLeft (fun _ : Fin 4 => unitMeasure) e).symm
  have heq : (fun s =>
      g (s (e 0)) * g (s (e 1)) * g (s (e 2)) * g (s (e 3)) *
        (min (s (e 0)) (s (e 1)) * min (s (e 2)) (s (e 3)))) = F ∘ ep := by
    rfl
  rw [heq]
  exact ⟨hep.integrable_comp_of_integrable hFi, (hep.integral_comp' F).trans hFI⟩

/-- The three Brownian pairings each contribute the square of the min-kernel energy. -/
theorem brownianW4_integral {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    (∫ s, (∏ i, g (s i)) * brownianW4 s ∂cubeMeasure 4) = 3 * Q g ^ 2 := by
  have h₁ := pairing_integrable_and_integral hg (Equiv.refl _)
  have h₂ := pairing_integrable_and_integral hg (Equiv.swap 1 2)
  have h₃ := pairing_integrable_and_integral hg (Equiv.swap 1 3)
  simp only [Equiv.refl_apply, Equiv.swap_apply_def] at h₁ h₂ h₃
  norm_num at h₂ h₃
  have he (s : Fin 4 → ℝ) : (∏ i, g (s i)) * brownianW4 s =
      g (s 0) * g (s 1) * g (s 2) * g (s 3) *
        (min (s 0) (s 1) * min (s 2) (s 3)) +
      g (s 0) * g (s 2) * g (s 1) * g (s 3) *
        (min (s 0) (s 2) * min (s 1) (s 3)) +
      g (s 0) * g (s 3) * g (s 2) * g (s 1) *
        (min (s 0) (s 3) * min (s 2) (s 1)) := by
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
