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
    (hl : ∀ i, ((i : ℝ)+1)/BiasedBoundaryCounting.B ≤ (mu i)⁻¹)
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
    rw [hreal]
    convert hlo using 1 <;> dsimp [b] at *
    · congr 1 <;> ring
    · field_simp
  refine ⟨hs,htr ▸ hs.tsum_ofReal_lt_top,hlow,?_,?_⟩
  · rw [hreal]
    convert hup using 1
    field_simp
  · intro htb
    have hratio : (t : ℝ)/b ≤ 1 := (div_le_one hb).mpr htb
    have he : (Real.exp 1)⁻¹ ≤ Real.exp (-(t : ℝ)/b) := by
      rw [← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      linarith
    have hm := mul_le_mul_of_nonneg_left he (div_pos hb htR).le
    have heq : b/(Real.exp 1*(t : ℝ)) = (b/(t : ℝ))*(Real.exp 1)⁻¹ := by ring
    rw [heq]
    exact hm.trans hlow

/-- One actual ordered family generates the original operator on every centered vector.
The strong generator equivalence includes the entire original domain, not only finite sums. -/
theorem actual_centered_heat :
    ∃ (e : HilbertBasis ℕ ℝ G0) (k : HilbertBasis ℕ ℝ K) (mu : ℕ → ℝ)
      (hp : ∀ i, 0 < mu i),
      Antitone mu ∧ Tendsto mu atTop (𝓝 0) ∧
      (∀ i, Sigma (k i).val = mu i • (k i).val) ∧
      (∀ i, C (k i).val = Real.sqrt (mu i) • (e i).val) ∧
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
        (∀ u v : G0, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S t u-u))
          (𝓝[>] 0) (𝓝 v) ↔ (u.val,(-v).val) ∈ boundaryOperator.graph) ∧
        (∀ R : StronglyContinuousContractionSemigroup G0,
          (∀ u v : G0, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t u-u))
            (𝓝[>] 0) (𝓝 v) ↔ (u.val,(-v).val) ∈ boundaryOperator.graph) → R = S) := by
  obtain ⟨e,k,mu,hp,hm,ht,hmi,hti,hg,hk,hC,hrest⟩ :=
    BiasedBoundaryCounting.actual_spectral_counting.2
  rcases hrest with ⟨hcut,hzero,hstrict,hgap,hupper,hlower,hlinear,heig⟩
  have hl (i : ℕ) : ((i : ℝ)+1)/BiasedBoundaryCounting.B ≤ (mu i)⁻¹ := by
    simpa [BiasedBoundaryCounting.positiveEigenvalue] using (heig (i+1) (by omega)).1
  have hu (i : ℕ) : (mu i)⁻¹ ≤ ((i : ℝ)+1)/BiasedBoundaryTrace.b := by
    simpa [BiasedBoundaryCounting.positiveEigenvalue] using (heig (i+1) (by omega)).2
  let S := semigroup e mu hp
  have hmax := generator_iff e k mu hp hk hC
  refine ⟨e,k,mu,hp,hm,ht,hk,hC,S,fun _ => rfl,?_,?_,hmax,?_⟩
  · intro t
    exact positive_trace_diagonal e (heat e mu hp t) _ (fun i => (Real.exp_pos _).le)
      (heat_coeff e mu hp t)
  · exact fun t ht => heat_estimates e mu hp hl hu t ht
  ·
    intro R hR
    apply R.ext_of_generator S
    · ext u
      change (∃ v, Tendsto _ _ _) ↔ (∃ v, Tendsto _ _ _)
      exact exists_congr fun v => (hR u v).trans (hmax u v).symm
    · intro u hu hv
      have h1 := (hR u (R.generator ⟨u,hu⟩)).mp (R.tendsto_generator' ⟨u,hu⟩)
      have h2 := (hmax u (R.generator ⟨u,hu⟩)).mpr h1
      exact (S.generator_eq_of_tendsto ⟨u,hv⟩ h2).symm
#print axioms actual_centered_heat

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryHeat
