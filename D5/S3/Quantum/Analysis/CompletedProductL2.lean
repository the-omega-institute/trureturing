/- GID: D5/S3/Quantum/Analysis/CompletedProductL2
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CompletedProductL2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The completed complex Hilbert tensor of sigma-finite L2 spaces is unitarily the product L2 space by actual representative multiplication. -/
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.MetricSpace.Completion

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
open MeasureTheory Set Filter
open scoped TensorProduct InnerProductSpace ENNReal
namespace D5.S3.Quantum.Analysis.CompletedProductL2

/-- The completed Hilbert tensor unitary sends every pure tensor to the AE product
of the actual factor representatives. Finite measurable rectangle tests give
surjectivity without a basis or density assumption. -/
theorem exists_completed_product_unitary {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν] :
    ∃ U : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν),
      ∀ (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν),
        U ((f ⊗ₜ[ℂ] g : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
          UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν))
          =ᵐ[μ.prod ν] (fun z => f z.1 * g z.2) := by
  let productLp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) := by
    let u : X × Y → ℂ := fun z => f z.1 * g z.2
    have hm : AEStronglyMeasurable u (μ.prod ν) :=
      (Lp.aestronglyMeasurable f).comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd
    have hf : Integrable (fun x => ‖f x‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
    have hg : Integrable (fun y => ‖g y‖ ^ 2) ν :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
    have hu : MemLp u 2 (μ.prod ν) :=
      (memLp_two_iff_integrable_sq_norm hm).mpr (by
        simpa only [u, norm_mul, mul_pow] using hf.mul_prod hg)
    exact hu.toLp u
  let productBilinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) := by
    have hc (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
        productLp f g =ᵐ[μ.prod ν] (fun z => f z.1 * g z.2) :=
      MemLp.coeFn_toLp _
    refine
      { toFun := fun f =>
          { toFun := productLp f
            map_add' := ?_
            map_smul' := ?_ }
        map_add' := ?_
        map_smul' := ?_ }
    · intro g h
      apply Lp.ext
      filter_upwards [hc f (g + h), hc f g, hc f h,
        Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_add g h),
        Lp.coeFn_add (productLp f g) (productLp f h)] with z h₁ h₂ h₃ h₄ h₅
      simp only [Pi.add_apply, h₁, h₂, h₃, h₄, h₅, mul_add]
    · intro c g
      apply Lp.ext
      filter_upwards [hc f (c • g), hc f g,
        Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_smul c g),
        Lp.coeFn_smul c (productLp f g)] with z h₁ h₂ h₃ h₄
      simpa only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, h₁, h₂, h₃, h₄] using
        (mul_left_comm (f z.1) c (g z.2))
    · intro f g
      apply LinearMap.ext
      intro h
      change productLp (f + g) h = productLp f h + productLp g h
      apply Lp.ext
      filter_upwards [hc (f + g) h, hc f h, hc g h,
        Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add f g),
        Lp.coeFn_add (productLp f h) (productLp g h)] with z h₁ h₂ h₃ h₄ h₅
      simp only [Pi.add_apply, h₁, h₂, h₃, h₄, h₅, add_mul]
    · intro c f
      apply LinearMap.ext
      intro g
      change productLp (c • f) g = c • productLp f g
      apply Lp.ext
      filter_upwards [hc (c • f) g, hc f g,
        Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c f),
        Lp.coeFn_smul c (productLp f g)] with z h₁ h₂ h₃ h₄
      simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, h₁, h₂, h₃, h₄, mul_assoc]
  let algebraicIsometry : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) := by
    let T := TensorProduct.lift (productBilinear)
    have hp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
        T (f ⊗ₜ[ℂ] g) = productLp f g := rfl
    have hc (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
        productLp f g =ᵐ[μ.prod ν] (fun z => f z.1 * g z.2) :=
      MemLp.coeFn_toLp _
    apply T.isometryOfInner
    intro z w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul h k =>
            rw [hp, hp, TensorProduct.inner_tmul, L2.inner_def, L2.inner_def, L2.inner_def]
            calc
              (∫ z, inner ℂ (productLp f g z) (productLp h k z) ∂μ.prod ν)
                  = ∫ z : X × Y, inner ℂ (f z.1 * g z.2) (h z.1 * k z.2) ∂μ.prod ν :=
                by
                  apply integral_congr_ae
                  filter_upwards [hc f g, hc h k] with z hfg hhk
                  rw [hfg, hhk]
              _ = ∫ z : X × Y,
                  inner ℂ (f z.1) (h z.1) * inner ℂ (g z.2) (k z.2) ∂μ.prod ν := by
                apply integral_congr_ae
                filter_upwards with z
                simp only [RCLike.inner_apply, map_mul]
                ring
              _ = (∫ x, inner ℂ (f x) (h x) ∂μ) * ∫ y, inner ℂ (g y) (k y) ∂ν :=
                integral_prod_mul (μ := μ) (ν := ν)
                  (fun x => inner ℂ (f x) (h x)) (fun y => inner ℂ (g y) (k y))
        | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
    | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]
  let U : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) := by
    let T := algebraicIsometry
    let U := T.toContinuousLinearMap.fromCompletion
    have hU : Isometry U := by
      change Isometry (UniformSpace.Completion.extension T.toContinuousLinearMap)
      exact T.isometry.completion_extension
    exact
      { toLinearMap := U.toLinearMap
        norm_map' := hU.norm_map_of_map_zero U.map_zero }

  have lp_zero_of_finite_rectangles
      (u : Lp ℂ 2 (μ.prod ν))
      (hrect : ∀ (a : Set X), MeasurableSet a → μ a < ∞ →
        ∀ (b : Set Y), MeasurableSet b → ν b < ∞ →
          ∫ z in a ×ˢ b, u z ∂μ.prod ν = 0) : u =ᵐ[μ.prod ν] 0 := by
    let s := spanningSets μ
    let t := spanningSets ν
    have hs : ∀ n, MeasurableSet (s n) := measurableSet_spanningSets μ
    have ht : ∀ n, MeasurableSet (t n) := measurableSet_spanningSets ν
    have hμs : ∀ n, μ (s n) < ∞ := measure_spanningSets_lt_top μ
    have hνt : ∀ n, ν (t n) < ∞ := measure_spanningSets_lt_top ν
    have hcover_s : ⋃ n, s n = univ := iUnion_spanningSets μ
    have hcover_t : ⋃ n, t n = univ := iUnion_spanningSets ν
    have rectDetect {η : Measure (X × Y)} {v : X × Y → ℂ} (hv : Integrable v η)
        (hvr : ∀ (a : Set X), MeasurableSet a → ∀ (b : Set Y), MeasurableSet b →
          ∫ z in a ×ˢ b, v z ∂η = 0) : v =ᵐ[η] 0 := by
      have hvuniv : ∫ z, v z ∂η = 0 := by
        simpa only [univ_prod_univ, setIntegral_univ] using hvr univ .univ univ .univ
      have hall : ∀ (a : Set (X × Y)), MeasurableSet a → ∫ z in a, v z ∂η = 0 := by
        refine MeasurableSpace.induction_on_inter generateFrom_prod.symm
          isPiSystem_prod ?_ ?_ ?_ ?_
        · simp
        · rintro _ ⟨a, ha, b, hb, rfl⟩
          exact hvr a ha b hb
        · intro a ha hzero
          rw [setIntegral_compl ha hv, hvuniv, hzero, sub_self]
        · intro a hd ha hz
          rw [integral_iUnion ha hd hv.integrableOn]
          simp only [hz, tsum_zero]
      exact hv.ae_eq_zero_of_forall_setIntegral_eq_zero (fun a ha _ => hall a ha)
    have hlocal (n m : ℕ) :
        (s n ×ˢ t m).indicator (fun z => u z) =ᵐ[μ.prod ν] 0 := by
      have hC : (μ.prod ν) (s n ×ˢ t m) < ∞ := by
        rw [Measure.prod_prod]
        exact ENNReal.mul_lt_top (hμs n) (hνt m)
      have : IsFiniteMeasure ((μ.prod ν).restrict (s n ×ˢ t m)) :=
        (isFiniteMeasure_restrict.mpr hC.ne)
      have huC : IntegrableOn (fun z => u z) (s n ×ˢ t m) (μ.prod ν) :=
        ((Lp.memLp u).restrict (s n ×ˢ t m)).integrable (by norm_num)
      apply rectDetect (huC.integrable_indicator ((hs n).prod (ht m)))
      intro a ha b hb
      rw [setIntegral_indicator ((hs n).prod (ht m)), prod_inter_prod]
      exact hrect (a ∩ s n) (ha.inter (hs n))
        ((measure_mono inter_subset_right).trans_lt (hμs n))
        (b ∩ t m) (hb.inter (ht m))
        ((measure_mono inter_subset_right).trans_lt (hνt m))
    have hall : ∀ᵐ z ∂μ.prod ν, ∀ p : ℕ × ℕ,
        (s p.1 ×ˢ t p.2).indicator (fun w => u w) z = 0 :=
      ae_all_iff.mpr (fun p => hlocal p.1 p.2)
    filter_upwards [hall] with z hz
    have hx : z.1 ∈ ⋃ n, s n := by rw [hcover_s]; trivial
    have hy : z.2 ∈ ⋃ n, t n := by rw [hcover_t]; trivial
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp hy
    simpa only [indicator_of_mem (show z ∈ s n ×ˢ t m from ⟨hn, hm⟩), Pi.zero_apply]
      using hz (n, m)
  let M := LinearMap.range U.toLinearMap
  have hclosed : IsClosed (M : Set (Lp ℂ 2 (μ.prod ν))) :=
    U.isometry.isClosedEmbedding.isClosed_range
  have : CompleteSpace M := hclosed.completeSpace_coe
  have hpure (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : productLp f g ∈ M := by
    refine ⟨((f ⊗ₜ[ℂ] g : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
      UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)), ?_⟩
    change (algebraicIsometry).toContinuousLinearMap.fromCompletion
      ((f ⊗ₜ[ℂ] g : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
        UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)) = _
    rw [ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  have hz (u : Lp ℂ 2 (μ.prod ν)) (hu : u ∈ Mᗮ) : u = 0 := by
    apply Lp.ext
    apply EventuallyEq.trans (g := (0 : X × Y → ℂ)) ?_ (Lp.coeFn_zero ℂ 2 (μ.prod ν)).symm
    apply lp_zero_of_finite_rectangles u
    intro a ha hμa b hb hνb
    let f : Lp ℂ 2 μ := indicatorConstLp 2 ha hμa.ne (1 : ℂ)
    let g : Lp ℂ 2 ν := indicatorConstLp 2 hb hνb.ne (1 : ℂ)
    have hp : inner ℂ (productLp f g) u = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hpure f g) hu
    have hc : productLp f g =ᵐ[μ.prod ν] (fun z => f z.1 * g z.2) :=
      MemLp.coeFn_toLp _
    have hf : f =ᵐ[μ] a.indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn
    have hg : g =ᵐ[ν] b.indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn
    have he : (fun z => inner ℂ (productLp f g z) (u z))
        =ᵐ[μ.prod ν] (a ×ˢ b).indicator (fun z => u z) := by
      filter_upwards [hc, Measure.quasiMeasurePreserving_fst.ae hf,
        Measure.quasiMeasurePreserving_snd.ae hg] with z hc hf hg
      rw [hc, hf, hg]
      by_cases hx : z.1 ∈ a <;> by_cases hy : z.2 ∈ b <;>
        simp [hx, hy, RCLike.inner_apply]
    rw [L2.inner_def, integral_congr_ae he, integral_indicator (ha.prod hb)] at hp
    exact hp
  have hsurj : Function.Surjective U := by
    intro u
    obtain ⟨v, hv, w, hw, heq⟩ := Submodule.exists_add_mem_mem_orthogonal (K := M) u
    have hw0 := hz w hw
    obtain ⟨z, hzv⟩ := hv
    refine ⟨z, ?_⟩
    change U z = v at hzv
    exact hzv.trans (by simpa only [hw0, add_zero] using heq.symm)
  refine ⟨LinearIsometryEquiv.ofSurjective U hsurj, ?_⟩
  intro f g
  have he : U ((f ⊗ₜ[ℂ] g : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
      UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)) = productLp f g := by
    change algebraicIsometry.toContinuousLinearMap.fromCompletion _ = _
    rw [ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  change U _ =ᵐ[μ.prod ν] _
  rw [he]
  exact MemLp.coeFn_toLp _

end D5.S3.Quantum.Analysis.CompletedProductL2
