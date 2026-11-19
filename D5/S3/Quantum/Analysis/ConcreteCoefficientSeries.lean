/- GID: D5/S3/Quantum/Analysis/ConcreteCoefficientSeries
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/ConcreteCoefficientSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual square-summable concrete coefficient series in the inherited dual norm. -/

import D5.S3.Quantum.Analysis.ConcreteCoefficientPredual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # The concrete series source class -/

noncomputable section

open Set Filter Topology
open scoped ComplexOrder InnerProductSpace BigOperators
open D5.S3.Quantum.Analysis.NormalFunctionals
open D5.S3.Quantum.Analysis.ConcreteCoefficientPredual

namespace D5.S3.Quantum.Analysis.ConcreteCoefficientSeries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H)

/-- The standard concrete class is specified by actual countable coefficient sums,
with two square-summable vector sequences; no closure predicate is its definition. -/
def IsCoefficientSeries (φ : StrongDual ℂ M.toStarSubalgebra) : Prop :=
  ∃ ξ η : ℕ → H, Summable (fun n => ‖ξ n‖ ^ 2) ∧ Summable (fun n => ‖η n‖ ^ 2) ∧
    ∀ a : M.toStarSubalgebra, φ a = ∑' n, ⟪ξ n, (a : H →L[ℂ] H) (η n)⟫_ℂ

private theorem coefficient_norm_le (ξ η : H) : ‖coefficient M ξ η‖ ≤ ‖ξ‖ * ‖η‖ := by
  unfold coefficient
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

private theorem coefficient_mem (ξ η : H) : coefficient M ξ η ∈ coefficientSpace M :=
  (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨(ξ, η), rfl⟩)

/-- The independently defined series class is contained in the closed coefficient space. -/
theorem series_mem_coefficientSpace {φ : StrongDual ℂ M.toStarSubalgebra}
    (hφ : IsCoefficientSeries M φ) : φ ∈ coefficientSpace M := by
  obtain ⟨ξ, η, hξ, hη, he⟩ := hφ
  have hp : Summable (fun n => ‖ξ n‖ * ‖η n‖) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun n => by nlinarith [sq_nonneg (‖ξ n‖ - ‖η n‖)]) ((hξ.add hη).div_const 2)
  have hn : Summable (fun n => ‖coefficient M (ξ n) (η n)‖) :=
    hp.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => coefficient_norm_le M _ _)
  have hs := hn.of_norm
  have heq : φ = ∑' n, coefficient M (ξ n) (η n) := by
    ext a
    rw [he]
    exact ((hs.hasSum.map (ContinuousLinearMap.apply ℂ ℂ a)
      (ContinuousLinearMap.apply ℂ ℂ a).continuous).tsum_eq)
  rw [heq]
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hs.hasSum
    (Eventually.of_forall fun s => (coefficientSpace M).sum_mem
      (fun n _ => coefficient_mem M (ξ n) (η n)))

/-- Standard concrete coefficient series are intrinsically normal in M. -/
theorem series_order_normal {φ : StrongDual ℂ M.toStarSubalgebra}
    (hφ : IsCoefficientSeries M φ) : IsOrderNormal φ :=
  coefficientSpace_le_normalDual M (series_mem_coefficientSpace M hφ)

private theorem coefficient_add_left (ξ ζ η : H) :
    coefficient M (ξ + ζ) η = coefficient M ξ η + coefficient M ζ η := by
  ext a
  exact inner_add_left _ _ _

private theorem coefficient_smul_left (c : ℂ) (ξ η : H) :
    coefficient M (c • ξ) η = (star c) • coefficient M ξ η := by
  ext a
  exact inner_smul_left _ _ _

private theorem coefficient_add_right (ξ η ζ : H) :
    coefficient M ξ (η + ζ) = coefficient M ξ η + coefficient M ξ ζ := by
  ext a
  change ⟪ξ, (a : H →L[ℂ] H) (η + ζ)⟫_ℂ = _
  rw [map_add, inner_add_right]
  rfl

private theorem coefficient_smul_right (c : ℂ) (ξ η : H) :
    coefficient M ξ (c • η) = c • coefficient M ξ η := by
  ext a
  change ⟪ξ, (a : H →L[ℂ] H) (c • η)⟫_ℂ = _
  rw [map_smul, inner_smul_right]
  rfl

/-- Every bounded functional on E is evaluation at an actual element of M,
with equality of the actual operator norms. -/
theorem dual_evaluation (Λ : StrongDual ℂ (coefficientSpace M)) :
    ∃ a : M.toStarSubalgebra, (∀ φ : coefficientSpace M, Λ φ = φ.val a) ∧ ‖a‖ = ‖Λ‖ := by
  obtain ⟨L, hL, hnL⟩ := exists_extension_norm_eq (coefficientSpace M) Λ
  let B (ξ : H) : StrongDual ℂ H :=
    (show H →ₗ[ℂ] ℂ from
      { toFun := fun η => L (coefficient M ξ η)
        map_add' := fun η ζ => by rw [coefficient_add_right, map_add]
        map_smul' := fun c η => by rw [coefficient_smul_right, map_smul]; rfl
      }).mkContinuous (‖L‖ * ‖ξ‖) (by
        intro η
        exact (L.le_opNorm _).trans (by
          calc
            ‖L‖ * ‖coefficient M ξ η‖ ≤ ‖L‖ * (‖ξ‖ * ‖η‖) := by
              gcongr; exact coefficient_norm_le M ξ η
            _ = ‖L‖ * ‖ξ‖ * ‖η‖ := by ring))
  let w (ξ : H) : H := (InnerProductSpace.toDual ℂ H).symm (B ξ)
  have hw (ξ η : H) : ⟪w ξ, η⟫_ℂ = L (coefficient M ξ η) :=
    InnerProductSpace.toDual_symm_apply
  let Tlin : H →ₗ[ℂ] H :=
    { toFun := w
      map_add' := fun ξ ζ => by
        apply ext_inner_right ℂ
        intro η
        rw [inner_add_left, hw, hw, hw, coefficient_add_left, map_add]
      map_smul' := fun c ξ => by
        apply ext_inner_right ℂ
        intro η
        rw [inner_smul_left, hw, hw, coefficient_smul_left, map_smul]
        rfl }
  have hbound (ξ : H) : ‖Tlin ξ‖ ≤ ‖L‖ * ‖ξ‖ := by
    change ‖(InnerProductSpace.toDual ℂ H).symm (B ξ)‖ ≤ _
    rw [(InnerProductSpace.toDual ℂ H).symm.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _
  let T : H →L[ℂ] H := Tlin.mkContinuous ‖L‖ hbound
  let A : H →L[ℂ] H := T.adjoint
  have hrep (ξ η : H) : ⟪ξ, A η⟫_ℂ = L (coefficient M ξ η) := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact hw ξ η
  have hmem : A ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro b hb
    have hc (ξ η : H) : coefficient M ξ (b η) = coefficient M (b.adjoint ξ) η := by
      ext a
      change ⟪ξ, (a : H →L[ℂ] H) (b η)⟫_ℂ = ⟪b.adjoint ξ, (a : H →L[ℂ] H) η⟫_ℂ
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact congrArg (fun C : H →L[ℂ] H => ⟪ξ, C η⟫_ℂ)
        ((VonNeumannAlgebra.mem_commutant_iff.mp hb) a.val a.property)
    ext η
    apply ext_inner_left ℂ
    intro ξ
    change ⟪ξ, b (A η)⟫_ℂ = ⟪ξ, A (b η)⟫_ℂ
    rw [← ContinuousLinearMap.adjoint_inner_left, hrep, hrep, hc]
  let a : M.toStarSubalgebra := ⟨A, hmem⟩
  have hclosed : IsClosed {φ : StrongDual ℂ M.toStarSubalgebra | L φ = φ a} :=
    isClosed_eq L.continuous (by fun_prop)
  have hspan : ∀ φ ∈ Submodule.span ℂ (Set.range fun p : H × H => coefficient M p.1 p.2),
      L φ = φ a := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨⟨ξ, η⟩, rfl⟩ := hφ
      exact (hrep ξ η).symm
    | zero => simp
    | add φ ψ _ _ hφ hψ => simp only [map_add, hφ, hψ, ContinuousLinearMap.add_apply]
    | smul c φ _ hφ => simp only [map_smul, hφ, ContinuousLinearMap.smul_apply]
  have hagree (φ : coefficientSpace M) : Λ φ = φ.val a := by
    rw [← hL φ]
    exact closure_minimal hspan hclosed φ.property
  have hAnorm : ‖a‖ ≤ ‖Λ‖ := by
    change ‖T.adjoint‖ ≤ ‖Λ‖
    rw [ContinuousLinearMap.adjoint.norm_map, ← hnL]
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  refine ⟨a, hagree, le_antisymm hAnorm ?_⟩
  apply Λ.opNorm_le_bound (norm_nonneg a)
  intro φ
  rw [hagree]
  exact (φ.val.le_opNorm a).trans_eq (mul_comm _ _)

private def coefficientBall : Set (coefficientSpace M) :=
  {φ | ∃ ξ η : H, φ.val = coefficient M ξ η ∧ ‖ξ‖ * ‖η‖ ≤ 1}

/-- The unit ball of E is generated in norm by finite real convex combinations
of actual coefficients with product budget at most one. -/
theorem closure_convex_coefficientBall :
    closure (convexHull ℝ (coefficientBall M)) = Metric.closedBall (0 : coefficientSpace M) 1 := by
  have hz : (0 : coefficientSpace M) ∈ coefficientBall M := by
    refine ⟨0, 0, ?_, by simp⟩
    ext a
    simp [coefficient]
  have hs : coefficientBall M ⊆ Metric.closedBall 0 1 := by
    rintro φ ⟨ξ, η, he, hn⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖φ.val‖ ≤ 1
    rw [he]
    exact (coefficient_norm_le M ξ η).trans hn
  apply le_antisymm
  · exact closure_minimal (convexHull_min hs (convex_closedBall _ _)) Metric.isClosed_closedBall
  · intro φ hφ
    by_contra hφout
    obtain ⟨Λ, c, hc, hφc⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      (convex_convexHull ℝ (coefficientBall M)).closure isClosed_closure hφout
    have hc0 : 0 < c := by
      simpa using hc 0 (subset_closure (subset_convexHull ℝ (coefficientBall M) hz))
    obtain ⟨a, ha, hna⟩ := dual_evaluation M Λ
    have han : ‖a‖ ≤ c := by
      change ‖(a : H →L[ℂ] H)‖ ≤ c
      apply ContinuousLinearMap.opNorm_le_of_re_inner_le hc0.le
      intro η ξ hη hξ
      let ψ : coefficientSpace M := ⟨coefficient M ξ η, coefficient_mem M ξ η⟩
      have hψ : ψ ∈ closure (convexHull ℝ (coefficientBall M)) :=
        subset_closure (subset_convexHull ℝ (coefficientBall M)
          ⟨ξ, η, rfl, by rw [hξ, hη]; norm_num⟩)
      have hh := hc ψ hψ
      rw [ha ψ] at hh
      change (⟪ξ, (a : H →L[ℂ] H) η⟫_ℂ).re < c at hh
      simpa only [RCLike.re_eq_complex_re, inner_re_symm] using hh.le
    have hpn : ‖φ‖ ≤ 1 := by simpa using hφ
    have hle : (Λ φ).re ≤ c := calc
      _ ≤ ‖Λ φ‖ := Complex.re_le_norm _
      _ ≤ ‖Λ‖ * ‖φ‖ := Λ.le_opNorm φ
      _ ≤ c * 1 := mul_le_mul (by rwa [← hna]) hpn (norm_nonneg _) hc0.le
      _ = c := mul_one c
    exact (not_lt_of_ge hle) hφc

private theorem finite_coefficient_decomposition {φ : coefficientSpace M}
    (hφ : φ ∈ convexHull ℝ (coefficientBall M)) :
    ∃ n : ℕ, ∃ ξ η : Fin n → H,
      φ.val = ∑ i, coefficient M (ξ i) (η i) ∧ ∑ i, ‖ξ i‖ * ‖η i‖ ≤ 1 := by
  classical
  obtain ⟨ι, hι, w, z, hw, hsum, hz, hread⟩ := mem_convexHull_iff_exists_fintype.mp hφ
  letI := hι
  choose ξ η he hn using hz
  let e := Fintype.equivFin ι
  have hval : φ.val = ∑ i : ι, coefficient M (ξ i) ((w i : ℂ) • η i) := by
    rw [← hread]
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro i _
    change w i • (z i).val = coefficient M (ξ i) ((w i : ℂ) • η i)
    rw [coefficient_smul_right, Complex.coe_smul, he]
  have hcost : ∑ i : ι, ‖ξ i‖ * ‖(w i : ℂ) • η i‖ ≤ 1 := by
    calc
      _ = ∑ i : ι, w i * (‖ξ i‖ * ‖η i‖) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
        ring
      _ ≤ ∑ i : ι, w i * 1 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hn i) (hw i)
      _ = 1 := by simp [hsum]
  refine ⟨Fintype.card ι, fun i => ξ (e.symm i), fun i => (w (e.symm i) : ℂ) • η (e.symm i), ?_, ?_⟩
  · exact hval.trans (e.symm.sum_comp _).symm
  · exact (e.symm.sum_comp _).le.trans hcost

private theorem balance_coefficient (ξ η : H) :
    ∃ x y : H, coefficient M x y = coefficient M ξ η ∧
      ‖x‖ ^ 2 = ‖ξ‖ * ‖η‖ ∧ ‖y‖ ^ 2 = ‖ξ‖ * ‖η‖ := by
  by_cases hξ : ξ = 0
  · subst ξ
    exact ⟨0, 0, by ext a; simp [coefficient], by simp, by simp⟩
  by_cases hη : η = 0
  · subst η
    exact ⟨0, 0, by ext a; simp [coefficient], by simp, by simp⟩
  have hξn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hηn : ‖η‖ ≠ 0 := norm_ne_zero_iff.mpr hη
  let c : ℝ := Real.sqrt (‖ξ‖ * ‖η‖)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = ‖ξ‖ * ‖η‖ := Real.sq_sqrt (by positivity)
  have hscalar : (c / ‖ξ‖) * (c / ‖η‖) = 1 := by
    field_simp
    nlinarith [hc2]
  refine ⟨((c / ‖ξ‖ : ℝ) : ℂ) • ξ, ((c / ‖η‖ : ℝ) : ℂ) • η, ?_, ?_, ?_⟩
  · rw [coefficient_smul_left, coefficient_smul_right, smul_smul]
    have he : star ((c / ‖ξ‖ : ℝ) : ℂ) * ((c / ‖η‖ : ℝ) : ℂ) = 1 := by
      simpa only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Complex.ofReal_one] using congrArg Complex.ofReal hscalar
    rw [he, one_smul]
  · have he : ‖((c / ‖ξ‖ : ℝ) : ℂ) • ξ‖ = c := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_mul_cancel₀ c hξn
    rw [he, hc2]
  · have he : ‖((c / ‖η‖ : ℝ) : ℂ) • η‖ = c := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_mul_cancel₀ c hηn
    rw [he, hc2]

private theorem finite_coefficient_approximation (φ : coefficientSpace M) :
    ∃ n : ℕ, ∃ ξ η : Fin n → H,
      (∑ i, ‖ξ i‖ ^ 2 ≤ ‖φ‖) ∧ (∑ i, ‖η i‖ ^ 2 ≤ ‖φ‖) ∧
      ‖φ.val - ∑ i, coefficient M (ξ i) (η i)‖ ≤ (1 / 2 : ℝ) * ‖φ‖ := by
  classical
  by_cases hφ : φ = 0
  · subst φ
    exact ⟨0, Fin.elim0, Fin.elim0, by simp, by simp, by simp⟩
  have hφn : ‖φ‖ ≠ 0 := norm_ne_zero_iff.mpr hφ
  have hφv : ‖φ.val‖ ≠ 0 := hφn
  let q : coefficientSpace M := ‖φ‖⁻¹ • φ
  have hq : q ∈ closure (convexHull ℝ (coefficientBall M)) := by
    rw [closure_convex_coefficientBall, Metric.mem_closedBall, dist_zero_right]
    simp [q, norm_smul, hφv]
  obtain ⟨ψ, hψ, hd⟩ := Metric.mem_closure_iff.mp hq (1 / 2) (by norm_num)
  obtain ⟨n, x, y, he, hb⟩ := finite_coefficient_decomposition M hψ
  let y' : Fin n → H := fun i => (‖φ‖ : ℂ) • y i
  have hcost : ∑ i, ‖x i‖ * ‖y' i‖ ≤ ‖φ‖ := by
    calc
      _ = ‖φ‖ * ∑ i, ‖x i‖ * ‖y i‖ := by
        simp only [y', norm_smul, Complex.norm_real, norm_norm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg φ)
      _ = ‖φ‖ := mul_one _
  have hval : ∑ i, coefficient M (x i) (y' i) = ‖φ‖ • ψ.val := by
    change (∑ i, coefficient M (x i) ((‖φ‖ : ℂ) • y i)) = _
    simp only [coefficient_smul_right, ← Finset.smul_sum, ← he]
    rw [Complex.coe_smul]
  have hr : ‖φ.val - ∑ i, coefficient M (x i) (y' i)‖ ≤ (1 / 2 : ℝ) * ‖φ‖ := by
    rw [hval]
    have heq : φ.val - ‖φ‖ • ψ.val = ‖φ‖ • (q.val - ψ.val) := by
      change φ.val - ‖φ.val‖ • ψ.val =
        ‖φ.val‖ • ((‖φ.val‖⁻¹ • φ.val) - ψ.val)
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hφv, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg φ)]
    rw [dist_eq_norm] at hd
    exact (mul_le_mul_of_nonneg_left hd.le (norm_nonneg φ)).trans_eq (mul_comm _ _)
  choose ξ η hcoeff hx hy using fun i => balance_coefficient M (x i) (y' i)
  exact ⟨n, ξ, η, by simpa only [hx] using hcost,
    by simpa only [hy] using hcost, by simpa only [hcoeff] using hr⟩

/-- Every member of the norm-closed coefficient space has an actual standard
square-summable coefficient-series representation. -/
theorem coefficientSpace_series (φ : coefficientSpace M) : IsCoefficientSeries M φ.val := by
  classical
  choose N X Y hX hY hR using finite_coefficient_approximation M
  let s (ψ : coefficientSpace M) : coefficientSpace M :=
    ⟨∑ i, coefficient M (X ψ i) (Y ψ i),
      (coefficientSpace M).sum_mem (fun i _ => coefficient_mem M _ _)⟩
  let residual (ψ : coefficientSpace M) : coefficientSpace M := ψ - s ψ
  let r (n : ℕ) : coefficientSpace M := residual^[n] φ
  have hres (ψ : coefficientSpace M) : ‖residual ψ‖ ≤ (1 / 2 : ℝ) * ‖ψ‖ := hR ψ
  have hr (n : ℕ) : ‖r n‖ ≤ (1 / 2 : ℝ) ^ n * ‖φ‖ := by
    induction n with
    | zero => simp [r]
    | succ n ih =>
      dsimp only [r]
      rw [Function.iterate_succ_apply']
      change ‖residual (r n)‖ ≤ _
      calc
        _ ≤ (1 / 2 : ℝ) * ‖r n‖ := hres (r n)
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * ‖φ‖) := by gcongr
        _ = (1 / 2 : ℝ) ^ (n + 1) * ‖φ‖ := by ring
  let I := (Σ n : ℕ, Fin (N (r n)))
  let ξ : I → H := fun i => X (r i.1) i.2
  let η : I → H := fun i => Y (r i.1) i.2
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖φ‖) :=
    summable_geometric_two.mul_right _
  have hξ : Summable (fun i : I => ‖ξ i‖ ^ 2) := by
    apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    apply hgeom.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => sq_nonneg _))
    intro n
    simpa only [tsum_fintype] using (hX (r n)).trans (hr n)
  have hη : Summable (fun i : I => ‖η i‖ ^ 2) := by
    apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    apply hgeom.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => sq_nonneg _))
    intro n
    simpa only [tsum_fintype] using (hY (r n)).trans (hr n)
  have hp : Summable (fun i : I => ‖ξ i‖ * ‖η i‖) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun i => by nlinarith [sq_nonneg (‖ξ i‖ - ‖η i‖)]) ((hξ.add hη).div_const 2)
  have hn : Summable (fun i : I => ‖coefficient M (ξ i) (η i)‖) :=
    hp.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => coefficient_norm_le M _ _)
  have hs := hn.of_norm
  have hlayers : HasSum (fun n : ℕ => (s (r n)).val)
      (∑' i : I, coefficient M (ξ i) (η i)) :=
    hs.hasSum.sigma (fun n => hasSum_fintype _)
  have hstep (n : ℕ) : r (n + 1) = r n - s (r n) := by
    change residual^[n + 1] φ = residual (residual^[n] φ)
    exact Function.iterate_succ_apply' residual n φ
  have hpartial (n : ℕ) : (∑ i ∈ Finset.range n, (s (r i)).val) = φ.val - (r n).val := by
    induction n with
    | zero => simp [r]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hstep]
      change φ.val - (r n).val + (s (r n)).val = φ.val - ((r n).val - (s (r n)).val)
      abel
  have hrzero : Tendsto (fun n : ℕ => (r n).val) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) hr
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖φ‖
    simpa using h
  have heq : (∑' i : I, coefficient M (ξ i) (η i)) = φ.val := by
    apply tendsto_nhds_unique hlayers.tendsto_sum_nat
    simp only [hpartial]
    simpa using tendsto_const_nhds.sub hrzero
  have hsum : HasSum (fun i : I => coefficient M (ξ i) (η i)) φ.val := heq ▸ hs.hasSum
  let e : I → ℕ := Encodable.encode
  have he : Function.Injective e := Encodable.encode_injective
  let x : ℕ → H := Function.extend e ξ 0
  let y : ℕ → H := Function.extend e η 0
  have hxnorm : (fun n => ‖x n‖ ^ 2) = Function.extend e (fun i => ‖ξ i‖ ^ 2) 0 := by
    funext n
    by_cases h : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := h
      simp only [x, he.extend_apply]
    · simp only [x, Function.extend_apply' _ _ _ h, Pi.zero_apply, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have hynorm : (fun n => ‖y n‖ ^ 2) = Function.extend e (fun i => ‖η i‖ ^ 2) 0 := by
    funext n
    by_cases h : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := h
      simp only [y, he.extend_apply]
    · simp only [y, Function.extend_apply' _ _ _ h, Pi.zero_apply, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have hc : (fun n => coefficient M (x n) (y n)) =
      Function.extend e (fun i => coefficient M (ξ i) (η i)) 0 := by
    funext n
    by_cases h : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := h
      simp only [x, y, he.extend_apply]
    · simp only [x, y, Function.extend_apply' _ _ _ h, Pi.zero_apply]
      ext a
      simp [coefficient]
  refine ⟨x, y, ?_, ?_, ?_⟩
  · rw [hxnorm]
    exact (summable_extend_zero he).mpr hξ
  · rw [hynorm]
    exact (summable_extend_zero he).mpr hη
  · intro a
    have ht : HasSum (fun n => coefficient M (x n) (y n)) φ.val := by
      rw [hc]
      exact (hasSum_extend_zero he).mpr hsum
    exact ((ht.map (ContinuousLinearMap.apply ℂ ℂ a)
      (ContinuousLinearMap.apply ℂ ℂ a).continuous).tsum_eq).symm

/-- Equality with the independently defined standard series class, in the actual
restricted dual norm. No intrinsic-normal-to-predual converse is assumed. -/
theorem mem_coefficientSpace_iff_series (φ : StrongDual ℂ M.toStarSubalgebra) :
    φ ∈ coefficientSpace M ↔ IsCoefficientSeries M φ :=
  ⟨fun hφ => coefficientSpace_series M ⟨φ, hφ⟩, series_mem_coefficientSpace M⟩

#print axioms series_mem_coefficientSpace
#print axioms series_order_normal
#print axioms dual_evaluation
#print axioms closure_convex_coefficientBall
#print axioms coefficientSpace_series
#print axioms mem_coefficientSpace_iff_series

end D5.S3.Quantum.Analysis.ConcreteCoefficientSeries
