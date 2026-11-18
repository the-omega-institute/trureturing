/- GID: D5/S3/Analytic/CanonicalProducts/SummableLinearProduct
   generality: G
   mirror-B: D5/B/S3/Analytic/CanonicalProducts/SummableLinearProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summable complex linear products are entire and have zero exponential type. -/

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn


set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology

namespace D5.S3.Analytic.CanonicalProducts.SummableLinearProduct

/-- The actual unordered product of complex linear factors with summable coefficient
norms converges at every point, is entire, and has arbitrarily small exponential type.
No assumption on the cardinality of the index type or on nonvanishing is needed. -/
theorem entire_zero_type_of_summable_norm {I : Type*} (c : I → ℂ)
    (hc : Summable (fun i => ‖c i‖)) :
    (∀ z : ℂ, Multipliable (fun i => 1 + z * c i)) ∧
      Differentiable ℂ (fun z : ℂ => ∏' i, (1 + z * c i)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧
        ∀ z : ℂ, ‖∏' i, (1 + z * c i)‖ ≤ A * Real.exp (ε * ‖z‖) := by
  classical
  have hprod (z : ℂ) : Multipliable (fun i => 1 + z * c i) := by
    apply multipliable_one_add_of_summable
    simpa only [norm_mul] using hc.mul_left ‖z‖
  refine ⟨hprod, ?_, ?_⟩
  · -- The majorant depends on the compact set, not on the whole plane.
    have hlu : HasProdLocallyUniformlyOn
        (fun i (z : ℂ) => 1 + z * c i)
        (fun z : ℂ => ∏' i, (1 + z * c i)) (Set.univ : Set ℂ) := by
      apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
      intro S _hSuniv hS
      obtain ⟨R, _hRpos, hR⟩ := hS.isBounded.exists_pos_norm_le
      refine Summable.hasProdUniformlyOn_one_add hS (hc.mul_left R) ?_ ?_
      · exact Eventually.of_forall fun i z hz => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hR z hz) (norm_nonneg (c i))
      · intro i
        exact (continuous_id.mul continuous_const).continuousOn
    have hfinite (S : Finset I) : DifferentiableOn ℂ
        (fun z : ℂ => ∏ i ∈ S, (1 + z * c i)) Set.univ := by
      apply DifferentiableOn.fun_finsetProd
      intro i _hi
      exact ((differentiable_const (1 : ℂ)).add
        (differentiable_id.mul_const (c i))).differentiableOn
    exact differentiableOn_univ.mp
      (hlu.differentiableOn (Eventually.of_forall hfinite) isOpen_univ)
  · intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    have hsmall : Set.Iio (ε / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hhalf
    obtain ⟨K, hK⟩ := hc.vanishing hsmall
    let δ : ℝ := (ε / 2) / ((K.card : ℝ) + 1)
    have hdenom : 0 < (K.card : ℝ) + 1 :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
    have hδ : 0 < δ := div_pos hhalf hdenom
    have hbudget : (K.card : ℝ) * δ ≤ ε / 2 := by
      calc
        (K.card : ℝ) * δ ≤ ((K.card : ℝ) + 1) * δ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hδ.le
        _ = δ * ((K.card : ℝ) + 1) := mul_comm _ _
        _ = ε / 2 := div_mul_cancel₀ _ hdenom.ne'
    let A : ℝ := ∏ i ∈ K, (1 + ‖c i‖ / δ)
    have hA : 1 ≤ A := by
      apply Finset.one_le_prod₀
      intro i _hi
      exact le_add_of_nonneg_right (div_nonneg (norm_nonneg _) hδ.le)
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    -- This one-factor estimate absorbs any finite head into a constant.
    have hfactor (i : I) (r : ℝ) (hr : 0 ≤ r) :
        1 + r * ‖c i‖ ≤ (1 + ‖c i‖ / δ) * Real.exp (δ * r) := by
      have he1 : 1 ≤ Real.exp (δ * r) := Real.one_le_exp (mul_nonneg hδ.le hr)
      have helin : δ * r ≤ Real.exp (δ * r) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      calc
        1 + r * ‖c i‖ ≤ Real.exp (δ * r) + (‖c i‖ / δ) * Real.exp (δ * r) := by
          apply add_le_add he1
          calc
            r * ‖c i‖ = (‖c i‖ / δ) * (δ * r) := by
              rw [← mul_assoc, div_mul_cancel₀ _ hδ.ne']
              exact mul_comm _ _
            _ ≤ (‖c i‖ / δ) * Real.exp (δ * r) :=
              mul_le_mul_of_nonneg_left helin (div_nonneg (norm_nonneg _) hδ.le)
        _ = (1 + ‖c i‖ / δ) * Real.exp (δ * r) := by rw [add_mul, one_mul]
    have hnorm (S : Finset I) (z : ℂ) :
        ‖∏ i ∈ S, (1 + z * c i)‖ ≤ ∏ i ∈ S, (1 + ‖z‖ * ‖c i‖) := by
      rw [norm_prod]
      refine Finset.prod_le_prod₀ (fun i _hi => norm_nonneg _) ?_
      intro i _hi
      simpa only [norm_one, norm_mul] using norm_add_le (1 : ℂ) (z * c i)
    have hhead (z : ℂ) :
        ‖∏ i ∈ K, (1 + z * c i)‖ ≤ A * Real.exp ((ε / 2) * ‖z‖) := by
      calc
        ‖∏ i ∈ K, (1 + z * c i)‖ ≤ ∏ i ∈ K, (1 + ‖z‖ * ‖c i‖) := hnorm K z
        _ ≤ ∏ i ∈ K, ((1 + ‖c i‖ / δ) * Real.exp (δ * ‖z‖)) :=
          Finset.prod_le_prod₀
            (fun i _hi => add_nonneg zero_le_one (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
            (fun i _hi => hfactor i ‖z‖ (norm_nonneg z))
        _ = A * Real.exp ((K.card : ℝ) * (δ * ‖z‖)) := by
          rw [Finset.prod_mul_distrib, ← Real.exp_sum]
          simp only [Finset.sum_const, nsmul_eq_mul, A]
        _ ≤ A * Real.exp ((ε / 2) * ‖z‖) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          apply Real.exp_le_exp.mpr
          calc
            (K.card : ℝ) * (δ * ‖z‖) = ((K.card : ℝ) * δ) * ‖z‖ :=
              (mul_assoc _ _ _).symm
            _ ≤ (ε / 2) * ‖z‖ := mul_le_mul_of_nonneg_right hbudget (norm_nonneg z)
    have htail (T : Finset I) (hT : Disjoint T K) (z : ℂ) :
        ‖∏ i ∈ T, (1 + z * c i)‖ ≤ Real.exp ((ε / 2) * ‖z‖) := by
      have hsum : (∑ i ∈ T, ‖c i‖) ≤ ε / 2 :=
        (show (∑ i ∈ T, ‖c i‖) < ε / 2 from hK T hT).le
      calc
        ‖∏ i ∈ T, (1 + z * c i)‖ ≤ ∏ i ∈ T, (1 + ‖z‖ * ‖c i‖) := hnorm T z
        _ ≤ Real.exp (∑ i ∈ T, ‖z‖ * ‖c i‖) :=
          Real.prod_one_add_le_exp_sum T
            (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = Real.exp (‖z‖ * ∑ i ∈ T, ‖c i‖) := by rw [Finset.mul_sum]
        _ ≤ Real.exp ((ε / 2) * ‖z‖) := by
          apply Real.exp_le_exp.mpr
          calc
            ‖z‖ * (∑ i ∈ T, ‖c i‖) ≤ ‖z‖ * (ε / 2) :=
              mul_le_mul_of_nonneg_left hsum (norm_nonneg z)
            _ = (ε / 2) * ‖z‖ := mul_comm _ _
    refine ⟨A, hA, ?_⟩
    intro z
    -- It suffices to bound the cofinal family of finite sets containing K.
    have hbound : ∀ᶠ S : Finset I in atTop,
        ‖∏ i ∈ S, (1 + z * c i)‖ ≤ A * Real.exp (ε * ‖z‖) := by
      refine eventually_atTop.mpr ⟨K, ?_⟩
      intro S hKS
      rw [← Finset.prod_sdiff hKS, norm_mul]
      calc
        ‖∏ i ∈ S \ K, (1 + z * c i)‖ * ‖∏ i ∈ K, (1 + z * c i)‖ ≤
            Real.exp ((ε / 2) * ‖z‖) * (A * Real.exp ((ε / 2) * ‖z‖)) :=
          mul_le_mul (htail (S \ K) Finset.sdiff_disjoint z) (hhead z)
            (norm_nonneg _) (Real.exp_nonneg _)
        _ = A * Real.exp (ε * ‖z‖) := by
          rw [mul_left_comm, ← Real.exp_add, ← add_mul, add_halves]
    have hlimit : Tendsto (fun S : Finset I => ∏ i ∈ S, (1 + z * c i))
        atTop (𝓝 (∏' i, (1 + z * c i))) := (hprod z).hasProd
    exact le_of_tendsto hlimit.norm hbound

end D5.S3.Analytic.CanonicalProducts.SummableLinearProduct
