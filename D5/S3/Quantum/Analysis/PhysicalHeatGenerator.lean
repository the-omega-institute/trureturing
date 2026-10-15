/- GID: D5/S3/Quantum/Analysis/PhysicalHeatGenerator
   generality: I
   mirror-B: D5/B/S3/Quantum/Analysis/PhysicalHeatGenerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full right heat-generator graph is minus the actual Schwartz oscillator closure. -/
/-
Physical Hermite orthonormality, totality and graph closure retain their imported
source identities. General generator closedness and uniqueness import the selected
Scott Armstrong proofs from ContractionSemigroup. The new analytic join builds
the bounded complex heat operators and identifies both directions of their full
right-generator graph with the same differential Schwartz closure.
-/
import D5.S3.Quantum.Analysis.PhysicalGraphClosure
import D5.S3.Quantum.Analysis.Hermite.PhysicalProductOrthonormality
import Mathlib.Analysis.InnerProductSpace.Positive

import D5.S3.Quantum.Analysis.ContractionSemigroup

open Filter MeasureTheory SchwartzMap
open scoped Topology ENNReal NNReal InnerProductSpace ComplexConjugate lp
noncomputable section
namespace D5.S3.Quantum.Analysis.PhysicalHeatGenerator
open D5.S3.Quantum.Analysis.SchwartzCutoffGraph
open D5.S3.Quantum.Analysis.SchwartzWeakAdjoint
open D5.S3.Quantum.Analysis.PhysicalHermiteTests
open D5.S3.Quantum.Analysis.PhysicalGraphClosure
open D5.S3.Quantum.Analysis.Hermite.PhysicalProductTotality
open D5.S3.Quantum.Analysis.Hermite.PhysicalProductOrthonormality
open MarkovProcess.Semigroup

private def heatMultiplier {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) (t : ℝ≥0) : H →L[ℂ] H :=
  let M : ℓ²(ι, ℂ) →ₗ[ℂ] ℓ²(ι, ℂ) :=
    { toFun := fun c => ⟨fun i => (Real.exp (-(t : ℝ) * E i) : ℂ) * c i,
        (lp.memℓp c).mono' fun i => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
          exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (hE i)))⟩
      map_add' := fun c d => by
        apply Subtype.ext; funext i
        change _ * (c i + d i) = _ * c i + _ * d i
        exact mul_add _ _ _
      map_smul' := fun a c => by
        apply Subtype.ext; funext i
        change _ * (a * c i) = a * (_ * c i)
        ring }
  let B : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) := M.mkContinuous 1 fun c => by
    rw [one_mul]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro i
    change ‖(Real.exp (-(t : ℝ) * E i) : ℂ) * c i‖ ≤ ‖c i‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (hE i)))
  e.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (B.comp e.repr.toContinuousLinearEquiv.toContinuousLinearMap)

private theorem heat_coeff {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) (t : ℝ≥0) (f : H) (i : ι) :
    e.repr (heatMultiplier e E hE t f) i =
      (Real.exp (-(t : ℝ) * E i) : ℂ) * e.repr f i := by
  simp [heatMultiplier]

private theorem heat_basis {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) (t : ℝ≥0) (i : ι) :
    heatMultiplier e E hE t (e i) = Real.exp (-(t : ℝ) * E i) • e i := by
  classical
  apply e.repr.injective
  ext j
  rw [heat_coeff]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  simp only [e.repr_self, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : i = j
  · subst j; simp
  · simp [lp.single_apply, h, Ne.symm h]

private theorem heat_contraction {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) (t : ℝ≥0) (f : H) :
    ‖heatMultiplier e E hE t f‖ ≤ ‖f‖ := by
  rw [← e.repr.norm_map (heatMultiplier e E hE t f), ← e.repr.norm_map f]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  rw [heat_coeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (hE i)))

private theorem heat_continuous {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) (f : H) :
    Continuous (fun t : ℝ≥0 => heatMultiplier e E hE t f) := by
  classical
  let T := heatMultiplier e E hE
  have hc (t : ℝ≥0) (x y : H) : dist (T t x) (T t y) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub] using heat_contraction e E hE t (x-y)
  have hfinite (F : Finset ι) :
      Continuous (fun t : ℝ≥0 => T t (∑ i ∈ F, e.repr f i • e i)) := by
    have heq (t : ℝ≥0) : T t (∑ i ∈ F, e.repr f i • e i) =
        ∑ i ∈ F, Real.exp (-(t : ℝ) * E i) • (e.repr f i • e i) := by
      simp only [map_sum, map_smul, T, heat_basis, smul_comm (e.repr f _)]
    simp only [heq]
    exact continuous_finset_sum _ fun i _ =>
      (Real.continuous_exp.comp ((NNReal.continuous_coe.neg).mul_const _)).smul continuous_const
  rw [continuous_iff_continuousAt]
  intro t
  change Tendsto (fun s : ℝ≥0 => T s f) (𝓝 t) (𝓝 (T t f))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ha := Metric.tendsto_nhds.mp (e.hasSum_repr f) (ε/3) (by positivity)
  obtain ⟨F,hF⟩ := ha.exists
  let u := ∑ i ∈ F, e.repr f i • e i
  have hu : dist u f < ε/3 := hF
  have ht := Metric.tendsto_nhds.mp ((hfinite F).tendsto t) (ε/3) (by positivity)
  filter_upwards [ht] with s hs
  calc
    dist (T s f) (T t f) ≤ dist (T s f) (T s u) +
        dist (T s u) (T t u) + dist (T t u) (T t f) := dist_triangle4 _ _ _ _
    _ ≤ dist f u + dist (T s u) (T t u) + dist u f := by gcongr; exact hc s f u; exact hc t u f
    _ < ε/3 + ε/3 + ε/3 := by rw [dist_comm f u]; exact add_lt_add (add_lt_add hu hs) hu
    _ = ε := by ring

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Existence of physical heat with the complete right-generator graph. -/
theorem physical_heat_generator (d : ℕ) (h : ℝ) (m w : Fin d → ℝ)
    (hh : 0 < h) (hm : ∀ j, 0 < m j) (hw : ∀ j, 0 < w j) :
    let K := (schwartzOperator d (fun j => h^2/(2*m j)) (fun j => m j*w j^2/2)).closure
    let E := fun n : Fin d → ℕ => ∑ j, h*w j*((n j : ℝ)+1/2)
    ∃ (e : HilbertBasis (Fin d → ℕ) ℂ (Hilbert d))
      (T : ℝ≥0 → Hilbert d →L[ℂ] Hilbert d)
      (S : StronglyContinuousContractionSemigroup (Hilbert d)),
      (∀ n, (e n : Space d → ℂ) =ᵐ[volume] physicalHermite d h m w n) ∧
      (∀ t, S t = (T t).restrictScalars ℝ) ∧
      (∀ t f n, e.repr (T t f) n = (Real.exp (-(t : ℝ)*E n) : ℂ)*e.repr f n) ∧
      (∀ t, (T t).IsPositive) ∧
      (∀ f v : Hilbert d,
        Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (T t f-f)) (𝓝[>] 0) (𝓝 v) ↔
          (f,-v) ∈ K.graph) ∧
      (∀ R : StronglyContinuousContractionSemigroup (Hilbert d),
        (∀ f v, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t f-f))
          (𝓝[>] 0) (𝓝 v) ↔ (f,-v) ∈ K.graph) → R = S) ∧
      ((∀ n, E n = 0) → ∀ t, T t = ContinuousLinearMap.id ℂ (Hilbert d)) := by
  classical
  dsimp only
  let E := fun n : Fin d → ℕ => ∑ j, h*w j*((n j : ℝ)+1/2)
  have hE (n) : 0 ≤ E n := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg hh.le (hw j).le) (by positivity)
  choose φ hφ hd hcut using physical_hermite_tests d h m w hh hm hw
  have hvalue (n : Fin d → ℕ) (x : Space d) :
      value d h m w n x = physicalHermite d h m w n x := by
    rw [value, physicalHermite, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro j _
    have hell : 0 < width h (m j) (w j) := Real.sqrt_pos.2
      (div_pos hh (mul_pos (hm j) (hw j)))
    have hden : Real.sqrt (Real.sqrt Real.pi * width h (m j) (w j) * (n j).factorial) =
        Real.sqrt (width h (m j) (w j)) *
          Real.sqrt ((n j).factorial * Real.sqrt Real.pi) := by
      rw [← Real.sqrt_mul hell.le]
      congr 1; ring
    apply congrArg Complex.ofReal
    rw [hden]
    simp only [Polynomial.eval_map, Polynomial.aeval_def, width]
    congr 2 <;> ring
    rfl
  let v : (Fin d → ℕ) → Hilbert d := fun n => (φ n).toLp 2 volume
  have hv (n) : (v n : Space d → ℂ) =ᵐ[volume] physicalHermite d h m w n :=
    ((φ n).coeFn_toLp 2 volume).trans (ae_of_all _ fun x => (hφ n x).trans (hvalue n x))
  have hreal (n : Fin d → ℕ) (x : Space d) :
      conj (physicalHermite d h m w n x) = physicalHermite d h m w n x := by
    simp only [physicalHermite, map_prod, Complex.conj_ofReal]
  have hon : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro n k
    rw [L2.inner_def]
    calc
      (∫ x, ⟪v n x,v k x⟫_ℂ) = ∫ x, physicalHermite d h m w n x * physicalHermite d h m w k x := by
        apply integral_congr_ae
        filter_upwards [hv n,hv k] with x hn hk
        simp only [hn,hk,RCLike.inner_apply,hreal,mul_comm]
      _ = _ := physical_product_orthonormal_integral d h m w hh hm hw n k
  have hbot : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    change f = 0
    have hz := (physical_product_totality d h m w hh hm hw).2 f (Lp.memLp f) (fun n => by
      have hi : ⟪v n,f⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span ⟨n,rfl⟩)
      rw [L2.inner_def] at hi
      convert hi using 1
      apply integral_congr_ae
      filter_upwards [hv n] with x hn
      simp only [hn,RCLike.inner_apply,hreal,mul_comm])
    exact Lp.ext (hz.trans (Lp.coeFn_zero ℂ 2 volume).symm)
  let e := HilbertBasis.mkOfOrthogonalEqBot hon hbot
  have he (n) : e n = (φ n).toLp 2 volume := congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hon hbot) n
  have hc := physical_graph_closure d h m w hh hm hw φ hφ e he
  let K := (schwartzOperator d (fun j => h^2/(2*m j)) (fun j => m j*w j^2/2)).closure
  have hgraph (f g : Hilbert d) :
      (f,g) ∈ K.graph ↔ ∀ n, e.repr g n = (E n : ℂ)*e.repr f n := by
    dsimp only [K]
    rw [hc.2.2.1]
    simpa only [HilbertBasis.repr_apply_apply] using (hc.2.2.2.2.2.2.2.2 f g).2.1
  let T := heatMultiplier e E hE
  have hzero : T 0 = ContinuousLinearMap.id ℂ (Hilbert d) := by
    apply ContinuousLinearMap.ext
    intro f
    apply e.repr.injective
    ext n
    simp [T, heat_coeff]
  have hadd (s t : ℝ≥0) : T (s+t) = (T s).comp (T t) := by
    apply ContinuousLinearMap.ext
    intro f
    apply e.repr.injective
    ext n
    simp only [ContinuousLinearMap.comp_apply,T,heat_coeff,NNReal.coe_add]
    rw [neg_add, add_mul,Real.exp_add,Complex.ofReal_mul,mul_assoc]
  let S : StronglyContinuousContractionSemigroup (Hilbert d) :=
    { operator := fun t => (T t).restrictScalars ℝ
      operator_zero := by apply ContinuousLinearMap.ext; intro f; exact DFunLike.congr_fun hzero f
      operator_add := fun s t => by apply ContinuousLinearMap.ext; intro f; exact DFunLike.congr_fun (hadd s t) f
      opNorm_le_one := fun t => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
        (fun f => by simpa using heat_contraction e E hE t f)
      continuous_orbit := fun f => heat_continuous e E hE f }
  have hscalar {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (n : Fin d → ℕ) (z : V) :
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • ((Real.exp (-(t : ℝ)*E n)) • z-z))
        (𝓝[>] 0) (𝓝 ((-E n) • z)) := by
    have hd : HasDerivAt (fun s : ℝ => Real.exp (-s*E n) • z) ((-E n) • z) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).neg.mul_const (E n)).exp.smul_const z) using 1 <;> simp
    simpa only [zero_add,neg_zero,zero_mul,Real.exp_zero,one_smul] using
      MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_slope_add_of_hasDerivAt hd
  have hfinite (F : Finset (Fin d → ℕ)) (c : (Fin d → ℕ) → ℂ) :
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
        (T t (∑ n ∈ F,c n • e n) - ∑ n ∈ F,c n • e n)) (𝓝[>] 0)
        (𝓝 (-∑ n ∈ F,((E n : ℂ)*c n) • e n)) := by
    have hs := tendsto_finsetSum F (fun n _ => hscalar n (c n • e n))
    convert hs using 1
    · funext t
      simp only [map_sum,map_smul,T,heat_basis,← Finset.sum_sub_distrib,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [smul_comm (c n)]
    · simp only [← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      calc
        -(((E n : ℂ)*c n) • e n) = -((E n : ℂ) • (c n • e n)) := by rw [smul_smul]
        _ = -(E n • (c n • e n)) := congrArg Neg.neg (algebraMap_smul ℂ (E n) _)
        _ = (-E n) • (c n • e n) := (neg_smul _ _).symm
  have hmax (f v : Hilbert d) :
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (T t f-f)) (𝓝[>] 0) (𝓝 v) ↔
        (f,-v) ∈ K.graph := by
    constructor
    · intro hd
      apply (hgraph f (-v)).mpr
      intro n
      have hc := (((lp.evalCLM ℂ (fun _ : Fin d → ℕ => ℂ) 2 n).comp e.repr.toContinuousLinearEquiv.toContinuousLinearMap).continuous.tendsto v).comp hd
      have hs := hscalar n (e.repr f n)
      have hlim : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
          ((Real.exp (-(t : ℝ)*E n) : ℂ)*e.repr f n-e.repr f n))
          (𝓝[>] 0) (𝓝 (e.repr v n)) := by
        change Tendsto (fun t : ℝ≥0 => e.repr ((t : ℝ)⁻¹ • (T t f-f)) n)
          (𝓝[>] 0) (𝓝 (e.repr v n)) at hc
        simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,map_sub,T,heat_coeff,
          lp.coeFn_smul,lp.coeFn_sub,Pi.smul_apply,Pi.sub_apply,smul_eq_mul] using hc
      have heq := tendsto_nhds_unique hlim hs
      simpa [heq,RCLike.real_smul_eq_coe_mul] using congrArg Neg.neg heq
    · intro hfg
      have hkg : (f,-v) ∈ ((schwartzOperator d (fun j => h^2/(2*m j))
          (fun j => m j*w j^2/2)).domRestrict (Submodule.span ℂ (Set.range e))).closure.graph := by
        simpa only [K,hc.2.2.1] using hfg
      obtain ⟨u,hu,hi,huf,huv⟩ := (hc.2.2.2.2.2.2.2.2 f (-v)).2.2.2 hkg
      have hder (F) := hfinite F (fun n => ⟪e n,f⟫_ℂ)
      let q : Finset (Fin d → ℕ) → S.generatorDomain := fun F =>
        ⟨u F, S.mem_generatorDomain_of_tendsto (by simpa only [S,ContinuousLinearMap.coe_restrictScalars',hu] using hder F)⟩
      have hq (F) : S.generator (q F) = -((schwartzOperator d (fun j => h^2/(2*m j))
          (fun j => m j*w j^2/2)).domRestrict (Submodule.span ℂ (Set.range e))) (u F) := by
        apply S.generator_eq_of_tendsto
        simpa only [q,S,ContinuousLinearMap.coe_restrictScalars',hu,hi,E] using hder F
      have hlim : Tendsto (fun F => S.generator (q F)) atTop (𝓝 v) := by
        simpa only [hq,neg_neg] using huv.neg
      exact S.tendsto_differenceQuotient_of_tendsto_generator huf hlim
  refine ⟨e,T,S,?_,fun _ => rfl,fun t f n => heat_coeff e E hE t f n,?_,hmax,?_,?_⟩
  · intro n; rw [he]; exact hv n
  · intro t
    apply (T t).isPositive_iff_complex.mpr
    intro f
    have hs := e.hasSum_inner_mul_inner f (T t f)
    have hterm (n) : ⟪f,e n⟫_ℂ * ⟪e n,T t f⟫_ℂ =
        ((Real.exp (-(t : ℝ)*E n) * Complex.normSq (e.repr f n) : ℝ) : ℂ) := by
      rw [← e.repr_apply_apply (T t f) n, heat_coeff]
      rw [← inner_conj_symm, ← e.repr_apply_apply f n]
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.normSq_apply] <;> ring
    have him : (⟪f,T t f⟫_ℂ).im = 0 := by
      rw [← hs.tsum_eq,Complex.im_tsum hs.summable]
      simp only [hterm,Complex.ofReal_im,tsum_zero]
    have hre : 0 ≤ (⟪f,T t f⟫_ℂ).re := by
      rw [← hs.tsum_eq,Complex.re_tsum hs.summable]
      apply tsum_nonneg
      intro n
      rw [hterm,Complex.ofReal_re]
      exact mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)
    constructor
    · apply Complex.ext
      · simp
      · change 0 = (⟪T t f,f⟫_ℂ).im
        rw [← inner_conj_symm,Complex.conj_im,him,neg_zero]
    · change 0 ≤ (⟪T t f,f⟫_ℂ).re
      rw [← inner_conj_symm,Complex.conj_re]
      exact hre
  · intro R hR
    apply R.ext_of_generator S
    · ext f
      change (∃ v, Tendsto _ _ _) ↔ (∃ v, Tendsto _ _ _)
      exact exists_congr fun v => (hR f v).trans (hmax f v).symm
    · intro f hf hg
      have h1 := (hR f (R.generator ⟨f,hf⟩)).mp (R.tendsto_generator' ⟨f,hf⟩)
      have h2 := (hmax f (R.generator ⟨f,hf⟩)).mpr h1
      exact (S.generator_eq_of_tendsto ⟨f,hg⟩ h2).symm
  · intro hE0 t
    apply ContinuousLinearMap.ext
    intro f
    apply e.repr.injective
    ext n
    change e.repr (T t f) n = e.repr f n
    rw [heat_coeff,show E n = 0 from hE0 n]
    simp only [mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul]

#print axioms physical_heat_generator
end D5.S3.Quantum.Analysis.PhysicalHeatGenerator
