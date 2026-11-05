/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySpectralForm
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySpectralForm
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual paired coefficients represent the original free-root form on its whole domain. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator

/-! The original form energy in the actual positive boundary eigenbasis. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm

open FiniteSourceHardy (H)
open BiasedBoundaryTrace (G)
open BiasedBoundaryCentering (Pi C)
open BiasedBoundaryStopping (G0)
open BiasedBoundaryFreeRootForm (D K Sigma energy lift mean_Pi free_root_least_energy)
open BiasedBoundaryOperator (boundaryOperator actual_positive_spectral_exhaustion)
open InnerProductSpace Filter
open scoped Topology ENNReal

/-- The actual boundary eigenbasis gives the weighted energy of every original
form-domain vector, and the spectral support inequality holds on that whole domain. -/
theorem actual_spectral_form_energy :
    ∃ (b : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ),
      (∀ i, 0 < mu i) ∧ Antitone mu ∧ Tendsto mu atTop (nhds 0) ∧
      Monotone (fun i => (mu i)⁻¹) ∧
      Tendsto (fun i => (mu i)⁻¹) atTop atTop ∧
      (∀ i, ((b i).val,(mu i)⁻¹ • (b i).val) ∈ boundaryOperator.graph) ∧
      (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
      (∀ i, C (k i).val = Real.sqrt (mu i) • (b i).val) ∧
      (∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite) ∧
      (∀ F : D,
        HasSum (fun i => (b.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2 / mu i)
          (energy F.val)) ∧
      (∀ (lam : ℝ) (F : D),
        (∀ i, (mu i)⁻¹ < lam → b.repr ⟨Pi F.val,mean_Pi F.val⟩ i = 0) →
        lam * ‖Pi F.val‖^2 ≤ energy F.val) := by
  obtain ⟨b,k,mu,hp,hm,ht,hmi,hti,_,hgraph,hk,hC,_,_,hfinite⟩ :=
    actual_positive_spectral_exhaustion
  have hadjoint (i : ℕ) :
      C.adjoint (b i).val = Real.sqrt (mu i) • (k i).val := by
    apply smul_right_injective (M := H) (Real.sqrt_pos.mpr (hp i)).ne'
    calc
      Real.sqrt (mu i) • C.adjoint (b i).val =
          C.adjoint (Real.sqrt (mu i) • (b i).val) := (map_smul _ _ _).symm
      _ = C.adjoint (C (k i).val) := by rw [hC]
      _ = Sigma (k i).val := rfl
      _ = mu i • (k i).val := hk i
      _ = Real.sqrt (mu i) • (Real.sqrt (mu i) • (k i).val) := by
        rw [smul_smul,← pow_two,Real.sq_sqrt (hp i).le]
  have hcoeff (F : D) (i : ℕ) :
      b.repr ⟨Pi F.val,mean_Pi F.val⟩ i =
        Real.sqrt (mu i) * k.repr ⟨lift F,(free_root_least_energy F).1⟩ i := by
    rw [b.repr_apply_apply,k.repr_apply_apply]
    change inner ℝ (b i).val (Pi F.val) =
      Real.sqrt (mu i) * inner ℝ (k i).val (lift F)
    rw [← (free_root_least_energy F).2.1,← C.adjoint_inner_left,
      hadjoint,real_inner_smul_left]
  have hquot (F : D) (i : ℕ) :
      (b.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2 / mu i =
        (k.repr ⟨lift F,(free_root_least_energy F).1⟩ i)^2 := by
    rw [hcoeff,mul_pow,Real.sq_sqrt (hp i).le]
    field_simp [(hp i).ne']
  have hparseval (F : D) :
      HasSum (fun i => (k.repr ⟨lift F,(free_root_least_energy F).1⟩ i)^2)
        (energy F.val) := by
    have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      (k.repr ⟨lift F,(free_root_least_energy F).1⟩)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
      k.repr.norm_map] at h
    change HasSum _ (‖lift F‖^2) at h
    simpa only [← (free_root_least_energy F).2.2.2.1] using h
  refine ⟨b,k,mu,hp,hm,ht,hmi,hti,hgraph,hk,hC,hfinite,?_,?_⟩
  · intro F
    simpa only [hquot] using hparseval F
  · intro lam F hsupport
    have hb : HasSum (fun i => (b.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2)
        (‖Pi F.val‖^2) := by
      have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
        (b.repr ⟨Pi F.val,mean_Pi F.val⟩)
      simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
        b.repr.norm_map] at h
      change HasSum _ (‖Pi F.val‖^2) at h
      exact h
    apply hasSum_le _ (hb.mul_left lam) (hparseval F)
    intro i
    rw [← hquot]
    by_cases hi : (mu i)⁻¹ < lam
    · rw [hsupport i hi]
      simp
    · have hle : lam ≤ (mu i)⁻¹ := le_of_not_gt hi
      simpa only [div_eq_mul_inv,mul_comm] using
        mul_le_mul_of_nonneg_right hle
          (sq_nonneg (b.repr ⟨Pi F.val,mean_Pi F.val⟩ i))

#print axioms actual_spectral_form_energy

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm
