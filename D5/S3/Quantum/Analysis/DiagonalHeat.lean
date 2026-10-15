/- GID: D5/S3/Quantum/Analysis/DiagonalHeat
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/DiagonalHeat
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-span diagonal closure and its whole-space strong heat generator. -/
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0; docs/reports/heat-suppliers/markovprocess-LICENSE.txt.
The selected right-slope argument is from scottnarmstrong/MarkovProcess at
dbade0d12c4f84179441a9df7d7147df7a8bcaa0, Semigroup/Generator.

The heat multiplier, continuity and generator arguments adapt the generic private
proofs in PhysicalHeatGenerator. Real semigroup closedness and uniqueness now
import the general ContractionSemigroup source, with its preserved Scott Armstrong
Apache-2.0 attribution and source selection. EigenbasisClosure retains the attributed PhysLean self-adjointness proof.
No originality is claimed for these standard operator constructions.
-/
import D5.S3.Quantum.Analysis.EigenbasisGraphCore
import D5.S3.Quantum.Analysis.ContractionSemigroup
import D5.S3.Quantum.Analysis.TraceClass.GeneralProduct
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology ENNReal NNReal InnerProductSpace ComplexConjugate lp ComplexOrder
noncomputable section
namespace D5.S3.Quantum.Analysis.DiagonalHeat
open MarkovProcess.Semigroup
open D5.S3.Quantum.Analysis.EigenbasisClosure
open D5.S3.Quantum.Analysis.EigenbasisGraphCore
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual algebraic finite-span operator. -/
def finiteOperator (e : HilbertBasis ι ℂ H) (h : ι → ℝ) : H →ₗ.[ℂ] H where
  domain := Submodule.span ℂ (Set.range e)
  toFun := (Finsupp.linearCombination ℂ (fun i => (h i : ℂ) • e i)).comp
    e.orthonormal.linearIndependent.repr

/-- The Hamiltonian is the genuine partial-map closure of the finite-span map. -/
def hamiltonian (e : HilbertBasis ι ℂ H) (h : ι → ℝ) : H →ₗ.[ℂ] H :=
  (finiteOperator e h).closure

/-- The algebraic operator has its exact diagonal action on every genuine basis vector. -/
theorem finite_basis (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (i : ι) :
    finiteOperator e h ⟨e i, Submodule.subset_span ⟨i,rfl⟩⟩ = (h i : ℂ) • e i := by
  classical
  let x : Submodule.span ℂ (Set.range e) := ⟨e i,Submodule.subset_span ⟨i,rfl⟩⟩
  have hx : e.orthonormal.linearIndependent.repr x = Finsupp.single i 1 :=
    e.orthonormal.linearIndependent.repr_eq (by simp [x])
  change Finsupp.linearCombination ℂ _ (e.orthonormal.linearIndependent.repr x) = _
  rw [hx]
  simp

/-- Transport an actually bounded real diagonal multiplier through the full basis. -/
def multiplier (e : HilbertBasis ι ℂ H) (a : ι → ℝ) (M : ℝ≥0)
    (ha : ∀ i, |a i| ≤ M) : H →L[ℂ] H :=
  let L : ℓ²(ι,ℂ) →ₗ[ℂ] ℓ²(ι,ℂ) :=
    { toFun := fun c => ⟨fun i => (a i : ℂ) * c i,
        ((lp.memℓp c).const_mul (M : ℂ)).mono' fun i => by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg M.coe_nonneg]
          exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)⟩
      map_add' := fun c d => by apply Subtype.ext; funext i; exact mul_add _ _ _
      map_smul' := fun z c => by apply Subtype.ext; funext i; change _ * (z * _) = z * (_ * _); ring }
  let B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ) := L.mkContinuous M fun c => by
    calc
      ‖L c‖ ≤ ‖(M : ℂ) • c‖ := by
        apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        intro i
        change ‖(a i : ℂ) * c i‖ ≤ ‖(M : ℂ) * c i‖
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg M.coe_nonneg]
        exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)
      _ = (M : ℝ) * ‖c‖ := by rw [lp.norm_const_smul (by norm_num : (2 : ℝ≥0∞) ≠ 0)]; simp
  e.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (B.comp e.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem multiplier_coeff (e : HilbertBasis ι ℂ H) (a : ι → ℝ) (M : ℝ≥0)
    (ha : ∀ i, |a i| ≤ M) (x : H) (i : ι) :
    e.repr (multiplier e a M ha x) i = (a i : ℂ) * e.repr x i := by
  simp [multiplier]

theorem multiplier_basis (e : HilbertBasis ι ℂ H) (a : ι → ℝ) (M : ℝ≥0)
    (ha : ∀ i, |a i| ≤ M) (i : ι) :
    multiplier e a M ha (e i) = a i • e i := by
  classical
  apply e.repr.injective
  ext j
  rw [multiplier_coeff, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  simp only [e.repr_self, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : i = j
  · subst j; simp
  · simp [lp.single_apply, h, Ne.symm h]

/-- Nonnegative real coefficients give positivity of the actual whole-space map. -/
theorem multiplier_positive (e : HilbertBasis ι ℂ H) (a : ι → ℝ) (M : ℝ≥0)
    (ha : ∀ i, |a i| ≤ M) (hpos : ∀ i, 0 ≤ a i) :
    (multiplier e a M ha).IsPositive := by
  let A := multiplier e a M ha
  apply A.isPositive_iff_complex.mpr
  intro f
  have hs := e.hasSum_inner_mul_inner f (A f)
  have hterm (i) : ⟪f,e i⟫_ℂ * ⟪e i,A f⟫_ℂ =
      ((a i * Complex.normSq (e.repr f i) : ℝ) : ℂ) := by
    rw [← e.repr_apply_apply (A f) i, multiplier_coeff]
    rw [← inner_conj_symm, ← e.repr_apply_apply f i]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.normSq_apply] <;> ring
  have him : (⟪f,A f⟫_ℂ).im = 0 := by
    rw [← hs.tsum_eq,Complex.im_tsum hs.summable]
    simp only [hterm,Complex.ofReal_im,tsum_zero]
  have hre : 0 ≤ (⟪f,A f⟫_ℂ).re := by
    rw [← hs.tsum_eq,Complex.re_tsum hs.summable]
    exact tsum_nonneg fun i => by rw [hterm,Complex.ofReal_re]; exact mul_nonneg (hpos i) (Complex.normSq_nonneg _)
  constructor
  · apply Complex.ext
    · simp
    · change 0 = (⟪A f,f⟫_ℂ).im
      rw [← inner_conj_symm,Complex.conj_im,him,neg_zero]
  · change 0 ≤ (⟪A f,f⟫_ℂ).re
    rw [← inner_conj_symm,Complex.conj_re]
    exact hre

private theorem heat_bound (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) (t : ℝ≥0) (i : ι) :
    |Real.exp (-(t : ℝ) * h i)| ≤ (1 : ℝ≥0) := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (hh i))

/-- The heat acts on the entire Hilbert space, including the zero eigenspace. -/
def heat (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (t : ℝ≥0) : H →L[ℂ] H :=
  multiplier e (fun i => Real.exp (-(t : ℝ) * h i)) 1 (heat_bound h hh t)

private theorem heat_coeff (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (t : ℝ≥0) (x : H) (i : ι) :
    e.repr (heat e h hh t x) i = (Real.exp (-(t : ℝ) * h i) : ℂ) * e.repr x i :=
  multiplier_coeff e _ _ _ x i

private theorem heat_basis (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (t : ℝ≥0) (i : ι) : heat e h hh t (e i) = Real.exp (-(t : ℝ) * h i) • e i :=
  multiplier_basis e _ _ _ i
private theorem heat_contraction {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) (t : ℝ≥0) (f : H) :
    ‖heat e E hE t f‖ ≤ ‖f‖ := by
  rw [← e.repr.norm_map (heat e E hE t f), ← e.repr.norm_map f]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  rw [heat_coeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (hE i)))

private theorem heat_continuous {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) (f : H) :
    Continuous (fun t : ℝ≥0 => heat e E hE t f) := by
  classical
  let T := heat e E hE
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


private theorem scalar_derivative {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (a : ℝ) (z : V) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • ((Real.exp (-(t : ℝ)*a)) • z-z))
      (𝓝[>] 0) (𝓝 ((-a) • z)) := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-s*a) • z) ((-a) • z) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).neg.mul_const (a)).exp.smul_const z) using 1 <;> simp
  simpa only [zero_add,neg_zero,zero_mul,Real.exp_zero,one_smul] using
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_slope_add_of_hasDerivAt hd

set_option backward.isDefEq.respectTransparency false in
/-- The full generator, full weighted domain and self-adjoint closure belong to the same K. -/
theorem diagonal_heat (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) :
    IsSelfAdjoint (hamiltonian e h) ∧
    Dense ((hamiltonian e h).domain : Set H) ∧
    (∀ x y, (x,y) ∈ (hamiltonian e h).graph ↔
      ∀ i, e.repr y i = (h i : ℂ) * e.repr x i) ∧
    (∀ x, x ∈ (hamiltonian e h).domain ↔
      Memℓp (fun i => (h i : ℂ) * e.repr x i) 2) ∧
    (∀ t x i, e.repr (heat e h hh t x) i =
      (Real.exp (-(t : ℝ)*h i) : ℂ)*e.repr x i) ∧
    (∀ t, (heat e h hh t).IsPositive) ∧
    ∃ S : StronglyContinuousContractionSemigroup H,
      (∀ t, S t = (heat e h hh t).restrictScalars ℝ) ∧
      (∀ x v : H, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (heat e h hh t x-x))
        (𝓝[>] 0) (𝓝 v) ↔ (x,-v) ∈ (hamiltonian e h).graph) ∧
      (∀ R : StronglyContinuousContractionSemigroup H,
        (∀ x v, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t x-x))
          (𝓝[>] 0) (𝓝 v) ↔ (x,-v) ∈ (hamiltonian e h).graph) → R = S) := by
  classical
  let K := hamiltonian e h
  let T := heat e h hh
  have hsa := (eigenbasis_closable_selfAdjoint e (finiteOperator e h) h rfl (finite_basis e h)).2
  have hc := eigenbasis_graph_coefficients e (finiteOperator e h) h rfl (finite_basis e h)
  have hgraph (x y : H) : (x,y) ∈ K.graph ↔ ∀ i, e.repr y i = (h i : ℂ)*e.repr x i := by
    simpa only [K,hamiltonian,HilbertBasis.repr_apply_apply] using (hc x y).1
  have hzero : T 0 = ContinuousLinearMap.id ℂ H := by
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
  let S : StronglyContinuousContractionSemigroup H :=
    { operator := fun t => (T t).restrictScalars ℝ
      operator_zero := by apply ContinuousLinearMap.ext; intro f; exact DFunLike.congr_fun hzero f
      operator_add := fun s t => by apply ContinuousLinearMap.ext; intro f; exact DFunLike.congr_fun (hadd s t) f
      opNorm_le_one := fun t => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
        (fun f => by simpa using heat_contraction e h hh t f)
      continuous_orbit := fun f => heat_continuous e h hh f }
  have hfinite (F : Finset ι) (c : ι → ℂ) :
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
        (T t (∑ n ∈ F,c n • e n) - ∑ n ∈ F,c n • e n)) (𝓝[>] 0)
        (𝓝 (-∑ n ∈ F,((h n : ℂ)*c n) • e n)) := by
    have hs : Tendsto (fun t : ℝ≥0 => ∑ n ∈ F,
        (t : ℝ)⁻¹ • (Real.exp (-(t : ℝ)*h n) • (c n • e n) - c n • e n))
        (𝓝[>] 0) (𝓝 (∑ n ∈ F, (-h n) • (c n • e n))) :=
      tendsto_finsetSum F (fun n _ => scalar_derivative (h n) (c n • e n))
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
        -(((h n : ℂ)*c n) • e n) = -((h n : ℂ) • (c n • e n)) := by rw [smul_smul]
        _ = -(h n • (c n • e n)) := congrArg Neg.neg (algebraMap_smul ℂ (h n) _)
        _ = (-h n) • (c n • e n) := (neg_smul _ _).symm
  have hmax (f v : H) :
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (T t f-f)) (𝓝[>] 0) (𝓝 v) ↔
        (f,-v) ∈ K.graph := by
    constructor
    · intro hd
      apply (hgraph f (-v)).mpr
      intro n
      have hc := (((lp.evalCLM ℂ (fun _ : ι => ℂ) 2 n).comp e.repr.toContinuousLinearEquiv.toContinuousLinearMap).continuous.tendsto v).comp hd
      have hs := scalar_derivative (h n) (e.repr f n)
      have hlim : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
          ((Real.exp (-(t : ℝ)*h n) : ℂ)*e.repr f n-e.repr f n))
          (𝓝[>] 0) (𝓝 (e.repr v n)) := by
        change Tendsto (fun t : ℝ≥0 => e.repr ((t : ℝ)⁻¹ • (T t f-f)) n)
          (𝓝[>] 0) (𝓝 (e.repr v n)) at hc
        simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,map_sub,T,heat_coeff,
          lp.coeFn_smul,lp.coeFn_sub,Pi.smul_apply,Pi.sub_apply,smul_eq_mul] using hc
      have heq := tendsto_nhds_unique hlim hs
      simpa [heq,RCLike.real_smul_eq_coe_mul] using congrArg Neg.neg heq
    · intro hfg
      have hcoeff := (hgraph f (-v)).mp hfg
      obtain ⟨u,hu,hi,huf,huv⟩ := (hc f (-v)).2.1 (by
        simpa only [HilbertBasis.repr_apply_apply] using hcoeff)
      have hder (F) := hfinite F (fun n => ⟪e n,f⟫_ℂ)
      let q : Finset ι → S.generatorDomain := fun F =>
        ⟨u F, S.mem_generatorDomain_of_tendsto (by simpa only [S,ContinuousLinearMap.coe_restrictScalars',hu] using hder F)⟩
      have hq (F) : S.generator (q F) = -(finiteOperator e h) (u F) := by
        apply S.generator_eq_of_tendsto
        simpa only [q,S,ContinuousLinearMap.coe_restrictScalars',hu,hi] using hder F
      have hlim : Tendsto (fun F => S.generator (q F)) atTop (𝓝 v) := by
        simpa only [hq,neg_neg] using huv.neg
      exact S.tendsto_differenceQuotient_of_tendsto_generator huf hlim
  refine ⟨hsa, hsa.dense_domain, hgraph, ?_, fun t x i => heat_coeff e h hh t x i,
    fun t => multiplier_positive e _ _ _ (fun i => (Real.exp_pos _).le), S,
    fun _ => rfl, hmax, ?_⟩
  · intro x
    simpa only [K,hamiltonian,HilbertBasis.repr_apply_apply] using (hc x 0).2.2
  · intro R hR
    apply R.ext_of_generator S
    · ext f
      change (∃ v, Tendsto _ _ _) ↔ (∃ v, Tendsto _ _ _)
      exact exists_congr fun v => (hR f v).trans (hmax f v).symm
    · intro f hf hg
      have h1 := (hR f (R.generator ⟨f,hf⟩)).mp (R.tendsto_generator' ⟨f,hf⟩)
      have h2 := (hmax f (R.generator ⟨f,hf⟩)).mpr h1
      exact (S.generator_eq_of_tendsto ⟨f,hg⟩ h2).symm

#print axioms diagonal_heat
end D5.S3.Quantum.Analysis.DiagonalHeat
