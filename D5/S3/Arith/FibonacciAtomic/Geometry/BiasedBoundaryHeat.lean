/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryHeat
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryHeat
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Real spectral heat on the original centered boundary space and its actual graph generator. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting
import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPolar
import D5.S3.Quantum.Analysis.ContractionSemigroup
import D5.S3.HilbertOperators.RealPositiveTrace
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! The multiplier and finite-span semigroup argument follow the standard construction in
`Quantum.Analysis.DiagonalHeat`, on the original real carrier. The generator closedness and
uniqueness supplies retain the Scott Armstrong attribution in `ContractionSemigroup`.
No new spectral exhaustion, inverse, polar decomposition, or counting result is asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryHeat

open BiasedBoundaryTrace (G)
open BiasedBoundaryStopping (G0)
open BiasedBoundaryFreeRootForm (K Sigma)
open BiasedBoundaryCentering (C Pi mean)
open BiasedBoundaryOperator (boundaryOperator)
open MarkovProcess.Semigroup Filter
open D5.S3.HilbertOperators.RealPositiveTrace (positiveTrace positive_trace_diagonal)
open scoped Topology ENNReal NNReal InnerProductSpace

private theorem heat_bound (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (t : ℝ≥0) (i : ℕ) : ‖Real.exp (-(t : ℝ) * (mu i)⁻¹) • (1 : ℝ →L[ℝ] ℝ)‖ ≤ 1 := by
  rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (inv_nonneg.mpr (hp i).le))

/-- The real bounded spectral heat multiplier on the entire original centered boundary space. -/
def heat (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (t : ℝ≥0) : G0 →L[ℝ] G0 :=
  e.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun i : ℕ => Real.exp (-(t : ℝ) * (mu i)⁻¹) • (1 : ℝ →L[ℝ] ℝ))
      (by norm_num : (0 : ℝ) ≤ 1) (heat_bound mu hp t)).comp
      e.repr.toLinearIsometry.toContinuousLinearMap)

private theorem heat_coeff (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (t : ℝ≥0) (x : G0) (i : ℕ) :
    e.repr (heat e mu hp t x) i = Real.exp (-(t : ℝ) * (mu i)⁻¹) * e.repr x i := by
  simp [heat]

private theorem heat_basis (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (t : ℝ≥0) (i : ℕ) :
    heat e mu hp t (e i) = Real.exp (-(t : ℝ) * (mu i)⁻¹) • e i := by
  classical
  apply e.repr.injective
  ext j
  rw [heat_coeff, map_smul]
  simp only [e.repr_self, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j; simp
  · simp [lp.single_apply, Ne.symm hij]

private theorem heat_contraction (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (t : ℝ≥0) (x : G0) :
    ‖heat e mu hp t x‖ ≤ ‖x‖ := by
  rw [← e.repr.norm_map (heat e mu hp t x), ← e.repr.norm_map x]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  rw [heat_coeff, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr t.coe_nonneg) (inv_nonneg.mpr (hp i).le)))

private theorem heat_continuous (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (x : G0) :
    Continuous (fun t : ℝ≥0 => heat e mu hp t x) := by
  classical
  let T := heat e mu hp
  have hc (t : ℝ≥0) (u v : G0) : dist (T t u) (T t v) ≤ dist u v := by
    simpa only [dist_eq_norm, ← map_sub] using heat_contraction e mu hp t (u-v)
  have hfinite (F : Finset ℕ) :
      Continuous (fun t : ℝ≥0 => T t (∑ i ∈ F, e.repr x i • e i)) := by
    have heq (t : ℝ≥0) : T t (∑ i ∈ F, e.repr x i • e i) =
        ∑ i ∈ F, Real.exp (-(t : ℝ) * (mu i)⁻¹) • (e.repr x i • e i) := by
      simp only [map_sum, map_smul, T, heat_basis, smul_comm (e.repr x _)]
    simp only [heq]
    exact continuous_finsetSum _ fun i _ =>
      (Real.continuous_exp.comp ((NNReal.continuous_coe.neg).mul_const _)).smul continuous_const
  rw [continuous_iff_continuousAt]
  intro t
  change Tendsto (fun s : ℝ≥0 => T s x) (𝓝 t) (𝓝 (T t x))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ha := Metric.tendsto_nhds.mp (e.hasSum_repr x) (ε/3) (by positivity)
  obtain ⟨F,hF⟩ := ha.exists
  let u := ∑ i ∈ F, e.repr x i • e i
  have hu : dist u x < ε/3 := hF
  have ht := Metric.tendsto_nhds.mp ((hfinite F).tendsto t) (ε/3) (by positivity)
  filter_upwards [ht] with s hs
  calc
    dist (T s x) (T t x) ≤ dist (T s x) (T s u) +
        dist (T s u) (T t u) + dist (T t u) (T t x) := dist_triangle4 _ _ _ _
    _ ≤ dist x u + dist (T s u) (T t u) + dist u x := by
      gcongr
      · exact hc s x u
      · exact hc t u x
    _ < ε/3 + ε/3 + ε/3 := by
      rw [dist_comm x u]
      exact add_lt_add (add_lt_add hu hs) hu
    _ = ε := by ring

private theorem scalar_derivative {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : ℝ) (z : V) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (Real.exp (-(t : ℝ)*a) • z-z))
      (𝓝[>] 0) (𝓝 ((-a) • z)) := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-s*a) • z) ((-a) • z) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).neg.mul_const a).exp.smul_const z) using 1 <;> simp
  simpa only [zero_add,neg_zero,zero_mul,Real.exp_zero,one_smul] using
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_slope_add_of_hasDerivAt hd


private theorem graph_coeff (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) (u h : G0) :
    (u.val,h.val) ∈ boundaryOperator.graph ↔
      ∀ i, e.repr h i = (mu i)⁻¹ * e.repr u i := by
  have hPi (v : G0) : Pi v.val = v.val := by
    rw [BiasedBoundaryCentering.centered_suffix_residual.2.2.1,
      show mean v.val = 0 from v.property, map_zero, sub_zero]
  rw [BiasedBoundaryPolar.graph_polar e k mu hp hk hC]
  constructor
  · rintro ⟨x,hh,hu⟩ i
    have hh' : h = BiasedBoundaryPolar.polar e k x := Subtype.ext hh
    have hu' : u = BiasedBoundaryPolar.polar e k (BiasedBoundaryPolar.covarianceK x) :=
      Subtype.ext ((hPi u).symm.trans hu)
    rw [hh',hu',BiasedBoundaryPolar.polar_coeff,BiasedBoundaryPolar.polar_coeff,
      BiasedBoundaryPolar.covariance_coeff e k mu hp hk hC]
    rw [← mul_assoc, inv_mul_cancel₀ (hp i).ne', one_mul]
  · intro hc
    refine ⟨(BiasedBoundaryPolar.polar e k).symm h, by simp, ?_⟩
    rw [hPi]
    apply congrArg Subtype.val
    apply e.repr.injective
    ext i
    rw [BiasedBoundaryPolar.polar_coeff,
      BiasedBoundaryPolar.covariance_coeff e k mu hp hk hC]
    have hi : k.repr ((BiasedBoundaryPolar.polar e k).symm h) i = e.repr h i := by
      simp [BiasedBoundaryPolar.polar]
    rw [hi, hc i, ← mul_assoc, mul_inv_cancel₀ (hp i).ne', one_mul]

private def semigroup (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) : StronglyContinuousContractionSemigroup G0 where
  operator := heat e mu hp
  operator_zero := by
    apply ContinuousLinearMap.ext
    intro f
    apply e.repr.injective
    ext i
    simp [heat_coeff]
  operator_add := by
    intro s t
    apply ContinuousLinearMap.ext
    intro f
    apply e.repr.injective
    ext i
    simp only [ContinuousLinearMap.comp_apply,heat_coeff,NNReal.coe_add]
    rw [neg_add, add_mul, Real.exp_add, mul_assoc]
  opNorm_le_one := fun t => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun x => by simpa using heat_contraction e mu hp t x)
  continuous_orbit := heat_continuous e mu hp

private theorem generator_iff (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) (u v : G0) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (heat e mu hp t u-u))
      (𝓝[>] 0) (𝓝 v) ↔ (u.val,(-v).val) ∈ boundaryOperator.graph := by
  classical
  let S := semigroup e mu hp
  have hfinite (F : Finset ℕ) (c : ℕ → ℝ) :
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
        (heat e mu hp t (∑ i ∈ F,c i • e i) - ∑ i ∈ F,c i • e i))
        (𝓝[>] 0) (𝓝 (-∑ i ∈ F,((mu i)⁻¹*c i) • e i)) := by
    have hs := tendsto_finsetSum F (fun i _ => scalar_derivative ((mu i)⁻¹) (c i • e i))
    convert hs using 1
    · funext t
      simp only [map_sum,map_smul,heat_basis,← Finset.sum_sub_distrib,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_comm (c i)]
    · simp only [← Finset.sum_neg_distrib,smul_smul,neg_mul,neg_smul]
  constructor
  · intro hd
    apply (graph_coeff e k mu hp hk hC u (-v)).mpr
    intro i
    have hc := (((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 i).comp
      e.repr.toContinuousLinearEquiv.toContinuousLinearMap).continuous.tendsto v).comp hd
    have hlim : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
        (Real.exp (-(t : ℝ)*(mu i)⁻¹)*e.repr u i-e.repr u i))
        (𝓝[>] 0) (𝓝 (e.repr v i)) := by
      change Tendsto (fun t : ℝ≥0 => e.repr ((t : ℝ)⁻¹ • (heat e mu hp t u-u)) i)
        (𝓝[>] 0) (𝓝 (e.repr v i)) at hc
      simpa only [map_smul,map_sub,heat_coeff,lp.coeFn_smul,lp.coeFn_sub,
        Pi.smul_apply,Pi.sub_apply,smul_eq_mul] using hc
    have heq := tendsto_nhds_unique hlim (scalar_derivative ((mu i)⁻¹) (e.repr u i))
    simpa [heq] using congrArg Neg.neg heq
  · intro hg
    have hc := (graph_coeff e k mu hp hk hC u (-v)).mp hg
    let q : Finset ℕ → S.generatorDomain := fun F =>
      ⟨∑ i ∈ F,e.repr u i • e i,
        S.mem_generatorDomain_of_tendsto (hfinite F (fun i => e.repr u i))⟩
    have hq (F : Finset ℕ) :
        S.generator (q F) = -∑ i ∈ F,((mu i)⁻¹*e.repr u i) • e i := by
      apply S.generator_eq_of_tendsto
      exact hfinite F (fun i => e.repr u i)
    have hv : Tendsto (fun F => S.generator (q F)) atTop (𝓝 v) := by
      have he : (fun F : Finset ℕ => S.generator (q F)) =
          (fun F : Finset ℕ => -∑ i ∈ F,e.repr (-v) i • e i) := by
        funext F
        simp only [hq,hc]
      rw [he]
      simpa only [HasSum, SummationFilter.unconditional_filter, Finset.sum_neg_distrib,
        neg_neg] using (e.hasSum_repr (-v)).neg
    have hu : Tendsto (fun F : Finset ℕ => (q F : G0)) atTop (𝓝 u) := by
      simpa only [q, HasSum, SummationFilter.unconditional_filter] using e.hasSum_repr u
    exact S.tendsto_differenceQuotient_of_tendsto_generator hu hv

private def Pi0 : G →L[ℝ] G0 :=
  Pi.codRestrict G0 BiasedBoundaryFreeRootForm.mean_Pi

private theorem Pi0_val (x : G0) : Pi0 x.val = x := by
  apply Subtype.ext
  change Pi x.val = x.val
  rw [BiasedBoundaryCentering.centered_suffix_residual.2.2.1,
    show mean x.val = 0 from x.property, map_zero, sub_zero]

private def fullModes (e : HilbertBasis ℕ ℝ G0) : Option ℕ → G
  | none => BiasedBoundaryPathSplit.constG 1
  | some i => (e i).val

private theorem fullModes_orthonormal (e : HilbertBasis ℕ ℝ G0) :
    Orthonormal ℝ (fullModes e) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | none =>
    cases j with
    | none =>
      change mean (BiasedBoundaryPathSplit.constG 1) = 1
      exact BiasedBoundaryCentering.centered_suffix_residual.2.1 1
    | some j =>
      change mean (e j).val = 0
      exact (e j).property
  | some i =>
    cases j with
    | none =>
      change inner ℝ (e i).val (BiasedBoundaryPathSplit.constG 1) = 0
      rw [real_inner_comm (BiasedBoundaryPathSplit.constG 1) (e i).val]
      exact (e i).property
    | some j =>
      simpa [fullModes] using (orthonormal_iff_ite.mp e.orthonormal i j)

private def fullBasis (e : HilbertBasis ℕ ℝ G0) : HilbertBasis (Option ℕ) ℝ G :=
  HilbertBasis.mkOfOrthogonalEqBot (fullModes_orthonormal e) (by
    apply le_antisymm _ bot_le
    intro x hx
    have hv (i : Option ℕ) : inner ℝ (fullModes e i) x = 0 :=
      (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨i,rfl⟩)
    have hm : mean x = 0 := hv none
    have hz : (⟨x,hm⟩ : G0) = 0 := by
      apply e.repr.injective
      ext i
      simpa [HilbertBasis.repr_apply_apply,fullModes] using hv (some i)
    exact congrArg Subtype.val hz)

private theorem fullBasis_apply (e : HilbertBasis ℕ ℝ G0) (i : Option ℕ) :
    fullBasis e i = fullModes e i := by simp [fullBasis]

/-- The actual ambient heat fixes constants and applies centered heat after orthogonal centering. -/
def fullHeat (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (t : ℝ≥0) : G →L[ℝ] G :=
  BiasedBoundaryPathSplit.constG.comp mean +
    G0.subtypeL.comp ((heat e mu hp t).comp Pi0)

private theorem fullHeat_mean (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (t : ℝ≥0) (F : G) : mean (fullHeat e mu hp t F) = mean F := by
  change mean (BiasedBoundaryPathSplit.constG (mean F)+(heat e mu hp t (Pi0 F)).val) = _
  rw [map_add,BiasedBoundaryCentering.centered_suffix_residual.2.1,
    show mean (heat e mu hp t (Pi0 F)).val = 0 from (heat e mu hp t (Pi0 F)).property,add_zero]

private theorem fullHeat_center (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (t : ℝ≥0) (F : G) :
    Pi0 (fullHeat e mu hp t F) = heat e mu hp t (Pi0 F) := by
  apply Subtype.ext
  change Pi (BiasedBoundaryPathSplit.constG (mean F)+(heat e mu hp t (Pi0 F)).val) = _
  rw [map_add,BiasedBoundaryCentering.Pi_const,zero_add]
  exact congrArg Subtype.val (Pi0_val _)

private theorem fullBasis_coeff (e : HilbertBasis ℕ ℝ G0) (F : G) :
    (fullBasis e).repr F none = mean F ∧
    ∀ i, (fullBasis e).repr F (some i) = e.repr (Pi0 F) i := by
  simp only [HilbertBasis.repr_apply_apply,fullBasis_apply,fullModes]
  refine ⟨rfl,?_⟩
  intro i
  exact (BiasedBoundaryFreeRootForm.inner_centered (e i).val F (e i).property).symm

private def fullMultiplier (mu : ℕ → ℝ) (t : ℝ≥0) : Option ℕ → ℝ
  | none => 1
  | some i => Real.exp (-(t : ℝ)*(mu i)⁻¹)

private theorem fullHeat_coeff (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (t : ℝ≥0) (F : G) (i : Option ℕ) :
    (fullBasis e).repr (fullHeat e mu hp t F) i =
      fullMultiplier mu t i * (fullBasis e).repr F i := by
  cases i with
  | none => rw [(fullBasis_coeff _ _).1,fullHeat_mean,(fullBasis_coeff _ _).1]; simp [fullMultiplier]
  | some i => rw [(fullBasis_coeff _ _).2,fullHeat_center,heat_coeff,
      (fullBasis_coeff _ _).2]; rfl

private theorem fullHeat_contraction (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (t : ℝ≥0) (F : G) : ‖fullHeat e mu hp t F‖ ≤ ‖F‖ := by
  rw [← (fullBasis e).repr.norm_map (fullHeat e mu hp t F), ← (fullBasis e).repr.norm_map F]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  rw [fullHeat_coeff,norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  cases i with
  | none => norm_num [fullMultiplier]
  | some i =>
    simp only [fullMultiplier,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr t.coe_nonneg) (inv_nonneg.mpr (hp i).le))

private def fullSemigroup (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) : StronglyContinuousContractionSemigroup G where
  operator := fullHeat e mu hp
  operator_zero := by
    apply ContinuousLinearMap.ext
    intro F
    apply (fullBasis e).repr.injective
    ext i
    rw [fullHeat_coeff]
    cases i <;> simp [fullMultiplier]
  operator_add := by
    intro s t
    apply ContinuousLinearMap.ext
    intro F
    apply (fullBasis e).repr.injective
    ext i
    simp only [ContinuousLinearMap.comp_apply,fullHeat_coeff]
    cases i with
    | none => simp [fullMultiplier]
    | some i => simp only [fullMultiplier,NNReal.coe_add]; rw [neg_add,add_mul,Real.exp_add,mul_assoc]
  opNorm_le_one := fun t => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun x => by simpa using fullHeat_contraction e mu hp t x)
  continuous_orbit := by
    intro F
    change Continuous (fun t : ℝ≥0 =>
      BiasedBoundaryPathSplit.constG (mean F)+(heat e mu hp t (Pi0 F)).val)
    exact continuous_const.add (G0.subtypeL.continuous.comp (heat_continuous e mu hp (Pi0 F)))

private theorem full_difference (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (t : ℝ≥0) (F : G) :
    fullHeat e mu hp t F-F = (heat e mu hp t (Pi0 F)-Pi0 F).val := by
  change BiasedBoundaryPathSplit.constG (mean F)+(heat e mu hp t (Pi0 F)).val-F =
    (heat e mu hp t (Pi0 F)).val-Pi F
  rw [BiasedBoundaryCentering.centered_suffix_residual.2.2.1]
  abel

private theorem graph_center (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) (F H : G) :
    (F,H) ∈ boundaryOperator.graph ↔ (Pi F,H) ∈ boundaryOperator.graph := by
  rw [BiasedBoundaryPolar.graph_polar e k mu hp hk hC,
    BiasedBoundaryPolar.graph_polar e k mu hp hk hC,
    BiasedBoundaryFreeRootForm.Pi_idem]

private theorem full_generator_iff (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K)
    (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hk : ∀ i, Sigma (k i).val = mu i • (k i).val)
    (hC : ∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) (F V : G) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (fullHeat e mu hp t F-F))
      (𝓝[>] 0) (𝓝 V) ↔ (F,-V) ∈ boundaryOperator.graph := by
  constructor
  · intro hd
    have hmean := (mean.continuous.tendsto V).comp hd
    have hm : mean V = 0 := by
      apply tendsto_nhds_unique hmean
      simpa only [Function.comp_def,map_smul,map_sub,fullHeat_mean,sub_self,smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
    let v : G0 := ⟨V,hm⟩
    have hproj := (Pi0.continuous.tendsto V).comp hd
    have hpv : Pi0 V = v := Pi0_val v
    have hlim : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
        (heat e mu hp t (Pi0 F)-Pi0 F)) (𝓝[>] 0) (𝓝 v) := by
      simpa only [Function.comp_def,map_smul,map_sub,fullHeat_center,hpv] using hproj
    exact (graph_center e k mu hp hk hC F (-V)).mpr
      ((generator_iff e k mu hp hk hC (Pi0 F) v).mp hlim)
  · intro hg
    obtain ⟨_,_,_,_,_,_,hw,_⟩ := BiasedBoundaryOperator.actual_self_adjoint_realization
    have hmean := ((BiasedBoundaryFreeRootForm.free_root_variational_graph.2.2.2.2.2
      F (-V)).mp ((hw F (-V)).mp hg)).1
    have hm : mean V = 0 := by simpa only [map_neg,neg_eq_zero] using hmean
    let v : G0 := ⟨V,hm⟩
    have hlim := (generator_iff e k mu hp hk hC (Pi0 F) v).mpr
      ((graph_center e k mu hp hk hC F (-V)).mp hg)
    have hinc := (G0.subtypeL.continuous.tendsto v).comp hlim
    simpa only [Function.comp_def,full_difference,Submodule.coe_smul_of_tower] using hinc

private theorem full_trace (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i) (t : ℝ≥0) :
    (fullHeat e mu hp t).IsPositive ∧
    positiveTrace (fullHeat e mu hp t) = 1+positiveTrace (heat e mu hp t) := by
  classical
  have hnonneg (i : Option ℕ) : 0 ≤ fullMultiplier mu t i := by
    cases i with
    | none => norm_num [fullMultiplier]
    | some i => exact (Real.exp_pos _).le
  have hdiag := positive_trace_diagonal (fullBasis e) (fullHeat e mu hp t)
    (fullMultiplier mu t) hnonneg (fullHeat_coeff e mu hp t)
  refine ⟨hdiag.1,?_⟩
  rw [hdiag.2,ENNReal.tsum_eq_add_tsum_ite none]
  have hsum := (Option.some_injective ℕ).tsum_eq
    (f := fun i : Option ℕ => if i = none then (0 : ℝ≥0∞)
      else ENNReal.ofReal (fullMultiplier mu t i)) (by
        intro i hi
        cases i with
        | none => simp at hi
        | some i => exact ⟨i,rfl⟩)
  change (1 : ℝ≥0∞)+_ = 1+positiveTrace (heat e mu hp t)
  congr 1
  rw [(positive_trace_diagonal e (heat e mu hp t) _
    (fun i => (Real.exp_pos _).le) (heat_coeff e mu hp t)).2]
  simpa only [fullMultiplier,Option.some_ne_none,ite_false] using hsum.symm

private theorem exponential_series (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => Real.exp (-x * ((n : ℝ)+1)))
      (Real.exp (-x) / (1-Real.exp (-x))) := by
  have hq : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  convert (hasSum_geometric_of_lt_one (Real.exp_pos (-x)).le hq).mul_left
    (Real.exp (-x)) using 1
  · funext n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  · rw [div_eq_mul_inv]

private theorem exponential_series_bounds (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) / x ≤ Real.exp (-x) / (1-Real.exp (-x)) ∧
    Real.exp (-x) / (1-Real.exp (-x)) ≤ 1/x := by
  have hq := Real.exp_pos (-x)
  have hq1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  have hd : 0 < 1-Real.exp (-x) := sub_pos.mpr hq1
  constructor
  · apply (div_le_div_iff₀ hx hd).mpr
    have he := Real.add_one_le_exp (-x)
    nlinarith [mul_nonneg hq.le (show 0 ≤ x-(1-Real.exp (-x)) by linarith)]
  · apply (div_le_div_iff₀ hd hx).mpr
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) hq.le
    have hid : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [hid] at he
    nlinarith

private theorem heat_estimates (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i)
    (hl : ∀ i : ℕ, ((i : ℝ)+1)/BiasedBoundaryCounting.B ≤ (mu i)⁻¹)
    (hu : ∀ i, (mu i)⁻¹ ≤ ((i : ℝ)+1)/BiasedBoundaryTrace.b)
    (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i => Real.exp (-(t : ℝ)*(mu i)⁻¹)) ∧
    positiveTrace (heat e mu hp t) < ⊤ ∧
    (BiasedBoundaryTrace.b/(t : ℝ))*Real.exp (-(t : ℝ)/BiasedBoundaryTrace.b) ≤
      (positiveTrace (heat e mu hp t)).toReal ∧
    (positiveTrace (heat e mu hp t)).toReal ≤ BiasedBoundaryCounting.B/(t : ℝ) ∧
    ((t : ℝ) ≤ BiasedBoundaryTrace.b →
      BiasedBoundaryTrace.b/(Real.exp 1*(t : ℝ)) ≤
        (positiveTrace (heat e mu hp t)).toReal) := by
  let b := BiasedBoundaryTrace.b
  let B := BiasedBoundaryCounting.B
  have hb : 0 < b := pow_pos BiasedBoundaryTrace.a_pos 2
  have hB : 0 < B := div_pos (mul_pos (by norm_num) Real.goldenRatio_pos) hb
  have htR : 0 < (t : ℝ) := ht
  have hL := exponential_series ((t : ℝ)/b) (div_pos htR hb)
  have hU := exponential_series ((t : ℝ)/B) (div_pos htR hB)
  have hle (i : ℕ) : Real.exp (-((t : ℝ)/b)*((i : ℝ)+1)) ≤
      Real.exp (-(t : ℝ)*(mu i)⁻¹) := by
    apply Real.exp_le_exp.mpr
    have hi := mul_le_mul_of_nonpos_left (hu i) (neg_nonpos.mpr t.coe_nonneg)
    convert hi using 1 <;> ring
  have hge (i : ℕ) : Real.exp (-(t : ℝ)*(mu i)⁻¹) ≤
      Real.exp (-((t : ℝ)/B)*((i : ℝ)+1)) := by
    apply Real.exp_le_exp.mpr
    have hi := mul_le_mul_of_nonpos_left (hl i) (neg_nonpos.mpr t.coe_nonneg)
    convert hi using 1 <;> ring
  have hs : Summable (fun i => Real.exp (-(t : ℝ)*(mu i)⁻¹)) :=
    hU.summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le) hge
  have htr := (positive_trace_diagonal e (heat e mu hp t) _
    (fun i => (Real.exp_pos _).le) (heat_coeff e mu hp t)).2
  have hreal : (positiveTrace (heat e mu hp t)).toReal =
      ∑' i, Real.exp (-(t : ℝ)*(mu i)⁻¹) := by
    rw [htr, ← ENNReal.ofReal_tsum_of_nonneg (fun i => (Real.exp_pos _).le) hs,
      ENNReal.toReal_ofReal (tsum_nonneg fun i => (Real.exp_pos _).le)]
  have hlo := (exponential_series_bounds ((t : ℝ)/b) (div_pos htR hb)).1.trans
    (hL.tsum_eq ▸ hL.summable.tsum_le_tsum hle hs)
  have hup := (hU.tsum_eq ▸ hs.tsum_le_tsum hge hU.summable).trans
    (exponential_series_bounds ((t : ℝ)/B) (div_pos htR hB)).2
  have hlow : (b/(t : ℝ))*Real.exp (-(t : ℝ)/b) ≤
      (positiveTrace (heat e mu hp t)).toReal := by
    have hid : (b/(t : ℝ))*Real.exp (-(t : ℝ)/b) =
        Real.exp (-((t : ℝ)/b))/((t : ℝ)/b) := by
      rw [show -(t : ℝ)/b = -((t : ℝ)/b) by ring]
      field_simp
    rw [hreal,hid]
    exact hlo
  refine ⟨hs,htr ▸ hs.tsum_ofReal_lt_top,hlow,?_,?_⟩
  · change (positiveTrace (heat e mu hp t)).toReal ≤ B/(t : ℝ)
    rw [hreal]
    simpa only [one_div_div] using hup
  · intro htb
    have hratio : (t : ℝ)/b ≤ 1 := (div_le_one hb).mpr htb
    have he : (Real.exp 1)⁻¹ ≤ Real.exp (-(t : ℝ)/b) := by
      rw [← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hratio
    have hm := mul_le_mul_of_nonneg_left he (div_pos hb htR).le
    have heq : b/(Real.exp 1*(t : ℝ)) = (b/(t : ℝ))*(Real.exp 1)⁻¹ := by ring
    rw [heq]
    exact hm.trans hlow

private theorem log_growth {α : Type*} (l : Filter α) (x y : α → ℝ)
    (hx : Tendsto x l atTop) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hbound : ∀ᶠ t in l, a*x t ≤ y t ∧ y t ≤ c*x t) :
    Tendsto (fun t => Real.log (y t)/Real.log (x t)) l (𝓝 1) := by
  have hlog := Real.tendsto_log_atTop.comp hx
  have hscale (b : ℝ) (hb : 0 < b) :
      Tendsto (fun t => Real.log (b*x t)/Real.log (x t)) l (𝓝 1) := by
    have hlim := ((tendsto_const_nhds (x := Real.log b)).div_atTop hlog).add_const 1
    simp only [zero_add] at hlim
    apply hlim.congr'
    filter_upwards [hx.eventually_gt_atTop 1] with t ht
    have hp : 0 < x t := lt_trans zero_lt_one ht
    rw [Real.log_mul hb.ne' hp.ne',add_div,div_self (Real.log_pos ht).ne']
    rfl
  apply (hscale a ha).squeeze' (hscale c hc)
  · filter_upwards [hbound,hx.eventually_gt_atTop 1] with t ht hx1
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (mul_pos ha (lt_trans zero_lt_one hx1)) ht.1) (Real.log_pos hx1).le
  · filter_upwards [hbound,hx.eventually_gt_atTop 1] with t ht hx1
    have hy := (mul_pos ha (lt_trans zero_lt_one hx1)).trans_le ht.1
    exact div_le_div_of_nonneg_right (Real.log_le_log hy ht.2) (Real.log_pos hx1).le

private theorem heat_log_limits (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i)
    (hl : ∀ i : ℕ, ((i : ℝ)+1)/BiasedBoundaryCounting.B ≤ (mu i)⁻¹)
    (hu : ∀ i, (mu i)⁻¹ ≤ ((i : ℝ)+1)/BiasedBoundaryTrace.b) :
    Tendsto (fun t : ℝ≥0 => Real.log (positiveTrace (heat e mu hp t)).toReal /
      Real.log (1/(t : ℝ))) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun t : ℝ≥0 => Real.log (positiveTrace (fullHeat e mu hp t)).toReal /
      Real.log (1/(t : ℝ))) (𝓝[>] 0) (𝓝 1) := by
  let b := BiasedBoundaryTrace.b
  let B := BiasedBoundaryCounting.B
  have hb : 0 < b := pow_pos BiasedBoundaryTrace.a_pos 2
  have hB : 0 < B := div_pos (mul_pos (by norm_num) Real.goldenRatio_pos) hb
  have hco : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
    have h : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        ((𝓝[>] (0 : ℝ≥0)).map NNReal.toReal) := tendsto_map
    simpa only [NNReal.map_coe_nhdsGT,NNReal.coe_zero] using h
  have hx : Tendsto (fun t : ℝ≥0 => 1/(t : ℝ)) (𝓝[>] 0) atTop := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hco
  have hsmall : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, 0 < t ∧ (t : ℝ) ≤ b := by
    filter_upwards [self_mem_nhdsWithin,
      (hco.mono_right inf_le_left).eventually (eventually_lt_nhds hb)] with t ht htb
    exact ⟨ht,htb.le⟩
  have hbounds : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0,
      (b/Real.exp 1)*(1/(t : ℝ)) ≤ (positiveTrace (heat e mu hp t)).toReal ∧
      (positiveTrace (heat e mu hp t)).toReal ≤ B*(1/(t : ℝ)) := by
    filter_upwards [hsmall] with t ht
    have h := heat_estimates e mu hp hl hu t ht.1
    constructor
    · convert h.2.2.2.2 ht.2 using 1 <;> ring
    · convert h.2.2.2.1 using 1 <;> ring
  constructor
  · exact log_growth _ _ _ hx _ _ (div_pos hb (Real.exp_pos _)) hB hbounds
  · apply log_growth _ _ _ hx (b/Real.exp 1) (B+b)
      (div_pos hb (Real.exp_pos _)) (add_pos hB hb)
    filter_upwards [hsmall,hbounds] with t ht h
    have hf := (heat_estimates e mu hp hl hu t ht.1).2.1
    rw [(full_trace e mu hp t).2,ENNReal.toReal_add (by norm_num) hf.ne,ENNReal.toReal_one]
    constructor
    · linarith
    · have h1 : 1 ≤ b/(t : ℝ) := (one_le_div (show 0 < (t : ℝ) from ht.1)).mpr ht.2
      calc
        1+(positiveTrace (heat e mu hp t)).toReal ≤ b/(t : ℝ)+B*(1/(t : ℝ)) :=
          add_le_add h1 h.2
        _ = (B+b)*(1/(t : ℝ)) := by ring

private theorem count_laplace (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i)
    (hcut : ∀ u : ℝ, ∃ q : Finset ℕ, ∀ i, i ∈ q ↔ (mu i)⁻¹ ≤ u)
    (t : ℝ≥0) (ht : 0 < t)
    (hs : Summable (fun i => Real.exp (-(t : ℝ)*(mu i)⁻¹))) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.exp (-(t : ℝ)*u)*(BiasedBoundaryCounting.positiveCount mu u : ℝ))
      (Set.Ioi 0) ∧
    (positiveTrace (heat e mu hp t)).toReal = (t : ℝ)*
      ∫ u : ℝ in Set.Ioi 0,
        Real.exp (-(t : ℝ)*u)*(BiasedBoundaryCounting.positiveCount mu u : ℝ) := by
  classical
  let f : ℕ → ℝ → ℝ := fun i => (Set.Ici (mu i)⁻¹).indicator
    (fun u => Real.exp (-(t : ℝ)*u))
  have htR : 0 < (t : ℝ) := ht
  have hinter (i : ℕ) : Set.Ici (mu i)⁻¹ ∩ Set.Ioi (0 : ℝ) = Set.Ici (mu i)⁻¹ := by
    apply Set.inter_eq_self_of_subset_left
    exact fun u hu => (inv_pos.mpr (hp i)).trans_le hu
  have hint (i : ℕ) : MeasureTheory.Integrable (f i)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    rw [f,MeasureTheory.integrable_indicator_iff measurableSet_Ici,
      MeasureTheory.IntegrableOn,MeasureTheory.Measure.restrict_restrict measurableSet_Ici,hinter]
    apply MeasureTheory.integrableOn_Ici_iff_integrableOn_Ioi.mpr
    exact integrableOn_exp_mul_Ioi (neg_neg_of_pos htR) _
  have hval (i : ℕ) : (∫ u : ℝ in Set.Ioi 0, f i u) =
      Real.exp (-(t : ℝ)*(mu i)⁻¹)/(t : ℝ) := by
    rw [f,MeasureTheory.integral_indicator measurableSet_Ici,
      MeasureTheory.Measure.restrict_restrict measurableSet_Ici,hinter,
      MeasureTheory.integral_Ici_eq_integral_Ioi,
      integral_exp_mul_Ioi (neg_neg_of_pos htR)]
    ring
  have hnorm (i : ℕ) (u : ℝ) : ‖f i u‖ = f i u := by
    rw [Real.norm_eq_abs,abs_of_nonneg]
    exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have hsum : Summable (fun i => ∫ u : ℝ in Set.Ioi 0, ‖f i u‖) := by
    simp_rw [hnorm,hval]
    exact hs.div_const _
  have hcount (u : ℝ) : (∑' i, f i u) =
      Real.exp (-(t : ℝ)*u)*(BiasedBoundaryCounting.positiveCount mu u : ℝ) := by
    obtain ⟨q,hq⟩ := hcut u
    have hset : {i : ℕ | (mu i)⁻¹ ≤ u} = (q : Set ℕ) := by
      ext i
      exact (hq i).symm
    have hcard : BiasedBoundaryCounting.positiveCount mu u = q.card := by
      simp [BiasedBoundaryCounting.positiveCount,hset]
    rw [tsum_eq_sum (s := q) (fun i hi => by
      simp only [f,Set.indicator,Set.mem_Ici]
      exact if_neg (not_congr (hq i)).mp hi),hcard]
    simp only [f,Set.indicator,Set.mem_Ici]
    rw [Finset.sum_congr rfl (fun i hi => if_pos ((hq i).mp hi))]
    simp [mul_comm]
  have hfun : (fun u => ∑' i, f i u) =
      (fun u => Real.exp (-(t : ℝ)*u)*(BiasedBoundaryCounting.positiveCount mu u : ℝ)) :=
    funext hcount
  have hlin : (∫⁻ u : ℝ, ∑' i, ‖f i u‖ₑ
      ∂(MeasureTheory.volume.restrict (Set.Ioi 0))) < ⊤ := by
    rw [MeasureTheory.lintegral_tsum (fun i => (hint i).aestronglyMeasurable.enorm)]
    simp_rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hint _)]
    exact hsum.tsum_ofReal_lt_top
  have hmeas (i : ℕ) : Measurable (f i) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.indicator
      measurableSet_Ici
  have hintsum : MeasureTheory.Integrable (fun u => ∑' i, f i u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    refine ⟨(Measurable.tsum hmeas).aestronglyMeasurable,?_⟩
    exact lt_of_le_of_lt (MeasureTheory.lintegral_mono fun u => enorm_tsum_le_tsum_enorm) hlin
  refine ⟨by simpa only [hfun] using hintsum,?_⟩
  have heq := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum
  rw [hfun] at heq
  have htr := (positive_trace_diagonal e (heat e mu hp t) _
    (fun i => (Real.exp_pos _).le) (heat_coeff e mu hp t)).2
  rw [htr, ← ENNReal.ofReal_tsum_of_nonneg (fun i => (Real.exp_pos _).le) hs,
    ENNReal.toReal_ofReal (tsum_nonneg fun i => (Real.exp_pos _).le), ← heq]
  simp_rw [hval]
  rw [tsum_div_const]
  field_simp

/-- One actual ordered family generates the original operator on every centered vector.
The strong generator equivalence includes the entire original domain, not only finite sums. -/
theorem actual_heat :
    ∃ (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ)
      (hp : ∀ i, 0 < mu i),
      Antitone mu ∧ Tendsto mu atTop (𝓝 0) ∧
      (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
      (∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) ∧
      Tendsto (fun lam : ℝ => Real.log (BiasedBoundaryCounting.positiveCount mu lam : ℝ) /
        Real.log lam) atTop (𝓝 1) ∧
      Tendsto (fun j : ℕ => Real.log (BiasedBoundaryCounting.positiveEigenvalue mu j) /
        Real.log (j : ℝ)) atTop (𝓝 1) ∧
      ∃ S : StronglyContinuousContractionSemigroup G0,
        (∀ t, S t = heat e mu hp t) ∧
        (∀ t, (S t).IsPositive ∧ positiveTrace (S t) =
          ∑' i, ENNReal.ofReal (Real.exp (-(t : ℝ) * (mu i)⁻¹))) ∧
        (∀ t : ℝ≥0, 0 < t →
          Summable (fun i => Real.exp (-(t : ℝ)*(mu i)⁻¹)) ∧
          positiveTrace (S t) < ⊤ ∧
          (BiasedBoundaryTrace.b/(t : ℝ))*Real.exp (-(t : ℝ)/BiasedBoundaryTrace.b) ≤
            (positiveTrace (S t)).toReal ∧
          (positiveTrace (S t)).toReal ≤ BiasedBoundaryCounting.B/(t : ℝ) ∧
          ((t : ℝ) ≤ BiasedBoundaryTrace.b →
            BiasedBoundaryTrace.b/(Real.exp 1*(t : ℝ)) ≤ (positiveTrace (S t)).toReal)) ∧
        (∀ t : ℝ≥0, 0 < t →
          MeasureTheory.IntegrableOn
            (fun u : ℝ => Real.exp (-(t : ℝ)*u)*(BiasedBoundaryCounting.positiveCount mu u : ℝ))
            (Set.Ioi 0) ∧
          (positiveTrace (S t)).toReal = (t : ℝ)*∫ u : ℝ in Set.Ioi 0,
            Real.exp (-(t : ℝ)*u)*(BiasedBoundaryCounting.positiveCount mu u : ℝ)) ∧
        (∀ u v : G0, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S t u-u))
          (𝓝[>] 0) (𝓝 v) ↔ (u.val,(-v).val) ∈ boundaryOperator.graph) ∧
        (∀ R : StronglyContinuousContractionSemigroup G0,
          (∀ u v : G0, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t u-u))
            (𝓝[>] 0) (𝓝 v) ↔ (u.val,(-v).val) ∈ boundaryOperator.graph) → R = S) ∧
        ∃ T : StronglyContinuousContractionSemigroup G,
          (∀ t, T t = fullHeat e mu hp t) ∧
          (∀ t, (T t).IsPositive ∧ positiveTrace (T t) = 1+positiveTrace (S t)) ∧
          (∀ t : ℝ≥0, 0 < t → positiveTrace (T t) < ⊤ ∧
            (positiveTrace (T t)).toReal = 1+(positiveTrace (S t)).toReal) ∧
          Tendsto (fun t : ℝ≥0 => Real.log (positiveTrace (S t)).toReal /
            Real.log (1/(t : ℝ))) (𝓝[>] 0) (𝓝 1) ∧
          Tendsto (fun t : ℝ≥0 => Real.log (positiveTrace (T t)).toReal /
            Real.log (1/(t : ℝ))) (𝓝[>] 0) (𝓝 1) ∧
          (∀ t c, T t (BiasedBoundaryPathSplit.constG c) = BiasedBoundaryPathSplit.constG c) ∧
          (∀ t (x : G0), T t x.val = (S t x).val) ∧
          (∀ F V : G, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (T t F-F))
            (𝓝[>] 0) (𝓝 V) ↔ (F,-V) ∈ boundaryOperator.graph) ∧
          (∀ R : StronglyContinuousContractionSemigroup G,
            (∀ F V : G, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t F-F))
              (𝓝[>] 0) (𝓝 V) ↔ (F,-V) ∈ boundaryOperator.graph) → R = T) := by
  obtain ⟨e,k,mu,hp,hm,ht,hmi,hti,hg,hk,hC,hrest⟩ :=
    BiasedBoundaryCounting.actual_spectral_counting.2
  rcases hrest with ⟨hcut,hzero,hstrict,hgap,hupper,hlower,hlinear,heig⟩
  have hl (i : ℕ) : ((i : ℝ)+1)/BiasedBoundaryCounting.B ≤ (mu i)⁻¹ := by
    simpa [BiasedBoundaryCounting.positiveEigenvalue] using (heig (i+1) (by omega)).1
  have hu (i : ℕ) : (mu i)⁻¹ ≤ ((i : ℝ)+1)/BiasedBoundaryTrace.b := by
    simpa [BiasedBoundaryCounting.positiveEigenvalue] using (heig (i+1) (by omega)).2
  let S := semigroup e mu hp
  have hmax := generator_iff e k mu hp hk hC
  have hb : 0 < BiasedBoundaryTrace.b := pow_pos BiasedBoundaryTrace.a_pos 2
  have hB : 0 < BiasedBoundaryCounting.B :=
    div_pos (mul_pos (by norm_num) Real.goldenRatio_pos) hb
  have hcount : Tendsto (fun lam : ℝ =>
      Real.log (BiasedBoundaryCounting.positiveCount mu lam : ℝ)/Real.log lam) atTop (𝓝 1) := by
    apply log_growth _ _ _ tendsto_id (BiasedBoundaryTrace.b/2) BiasedBoundaryCounting.B
      (div_pos hb (by norm_num)) hB
    filter_upwards [eventually_ge_atTop (2/BiasedBoundaryTrace.b)] with lam hlam
    exact hlinear lam hlam
  have heigen : Tendsto (fun j : ℕ =>
      Real.log (BiasedBoundaryCounting.positiveEigenvalue mu j)/Real.log (j : ℝ)) atTop (𝓝 1) := by
    apply log_growth _ _ _ tendsto_natCast_atTop_atTop
      BiasedBoundaryCounting.B⁻¹ BiasedBoundaryTrace.b⁻¹ (inv_pos.mpr hB) (inv_pos.mpr hb)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
    simpa only [div_eq_mul_inv,mul_comm] using heig j hj
  refine ⟨e,k,mu,hp,hm,ht,hk,hC,hcount,heigen,S,fun _ => rfl,?_,?_,?_,hmax,?_,?_⟩
  · intro t
    exact positive_trace_diagonal e (heat e mu hp t) _ (fun i => (Real.exp_pos _).le)
      (heat_coeff e mu hp t)
  · exact fun t ht => heat_estimates e mu hp hl hu t ht
  · intro t ht
    apply count_laplace e mu hp _ t ht (heat_estimates e mu hp hl hu t ht).1
    intro u
    obtain ⟨q,r,hq,_⟩ := hcut u
    exact ⟨q,hq⟩
  · intro R hR
    apply R.ext_of_generator S
    · ext u
      change (∃ v, Tendsto _ _ _) ↔ (∃ v, Tendsto _ _ _)
      exact exists_congr fun v => (hR u v).trans (hmax u v).symm
    · intro u hu hv
      have h1 := (hR u (R.generator ⟨u,hu⟩)).mp (R.tendsto_generator' ⟨u,hu⟩)
      have h2 := (hmax u (R.generator ⟨u,hu⟩)).mpr h1
      exact (S.generator_eq_of_tendsto ⟨u,hv⟩ h2).symm
  · let T := fullSemigroup e mu hp
    have hgen := full_generator_iff e k mu hp hk hC
    refine ⟨T,fun _ => rfl,full_trace e mu hp,?_,
      (heat_log_limits e mu hp hl hu).1,(heat_log_limits e mu hp hl hu).2,?_,?_,hgen,?_⟩
    · intro t ht
      have hf := (heat_estimates e mu hp hl hu t ht).2.1
      change positiveTrace (fullHeat e mu hp t) < ⊤ ∧
        (positiveTrace (fullHeat e mu hp t)).toReal = 1+(positiveTrace (heat e mu hp t)).toReal
      rw [(full_trace e mu hp t).2]
      refine ⟨ENNReal.add_lt_top.mpr ⟨by norm_num,hf⟩,?_⟩
      rw [ENNReal.toReal_add (by norm_num) hf.ne,ENNReal.toReal_one]
    · intro t c
      change BiasedBoundaryPathSplit.constG (mean (BiasedBoundaryPathSplit.constG c))+
        (heat e mu hp t (Pi0 (BiasedBoundaryPathSplit.constG c))).val = _
      have hz : Pi0 (BiasedBoundaryPathSplit.constG c) = 0 := by
        apply Subtype.ext
        exact BiasedBoundaryCentering.Pi_const c
      rw [BiasedBoundaryCentering.centered_suffix_residual.2.1,hz,map_zero]
      simp
    · intro t x
      change BiasedBoundaryPathSplit.constG (mean x.val)+
        (heat e mu hp t (Pi0 x.val)).val = _
      rw [show mean x.val = 0 from x.property,map_zero,zero_add,Pi0_val]
      rfl
    · intro R hR
      apply R.ext_of_generator T
      · ext F
        change (∃ V, Tendsto _ _ _) ↔ (∃ V, Tendsto _ _ _)
        exact exists_congr fun V => (hR F V).trans (hgen F V).symm
      · intro F hF hT
        have h1 := (hR F (R.generator ⟨F,hF⟩)).mp (R.tendsto_generator' ⟨F,hF⟩)
        have h2 := (hgen F (R.generator ⟨F,hF⟩)).mpr h1
        exact (T.generator_eq_of_tendsto ⟨F,hT⟩ h2).symm
#print axioms actual_heat

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryHeat
