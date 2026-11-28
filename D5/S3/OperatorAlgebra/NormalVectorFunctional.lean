/- GID: D5/S3/OperatorAlgebra/NormalVectorFunctional
   generality: G
   mirror-B: none(waiver:covered-by-hyperfinite-type-ii1-factor-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A bounded increasing net of positive operators in a concrete von Neumann algebra converges strongly to its least upper bound. -/

import OmegaBuild.Commands
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
Omega original.

A bounded increasing net of positive operators in a concrete von Neumann algebra
converges strongly to its least upper bound. Vector expectations preserve this bound.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.NormalVectorFunctional

open Filter ContinuousLinearMap
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real expectation of an operator at a vector. -/
def expectation (x : H) (A : H →L[ℂ] H) : ℝ := (⟪x, A x⟫_ℂ).re

omit [CompleteSpace H] in
private theorem expectation_mono (x : H) : Monotone (expectation x) := by
  intro A B h
  have hq := (le_def.mp h).re_inner_nonneg_right x
  change 0 ≤ (⟪x, (B - A) x⟫_ℂ).re at hq
  simpa only [expectation, sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using hq

omit [CompleteSpace H] in
private theorem expectation_smul (x : H) (r : ℝ) (A : H →L[ℂ] H) :
    expectation x (r • A) = r * expectation x A := by
  unfold expectation
  rw [smul_apply]
  change (⟪x, r • A x⟫_ℂ).re = _
  rw [← algebraMap_smul ℂ r (A x)]
  change (⟪x, (r : ℂ) • A x⟫_ℂ).re = _
  rw [inner_smul_right, Complex.mul_re]
  simp

private theorem deviation_sq_le (D : H →L[ℂ] H) (hD : 0 ≤ D)
    (r : ℝ) (hB : D ≤ algebraMap ℝ (H →L[ℂ] H) r) (x : H) :
    ‖D x‖ ^ 2 ≤ r * expectation x D := by
  let Q := CFC.sqrt D
  have hQ : star Q = Q := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)).star_eq
  have hs : Q * Q = D := CFC.sqrt_mul_sqrt_self D
  have hle := star_left_conjugate_le_conjugate hB Q
  rw [hQ, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, hs] at hle
  have he : Q * D * Q = star D * D := by
    rw [(IsSelfAdjoint.of_nonneg hD).star_eq, ← hs]
    simp only [mul_assoc]
  rw [he] at hle
  have hp := expectation_mono x hle
  rw [expectation_smul] at hp
  change (⟪x, (star D) (D x)⟫_ℂ).re ≤ _ at hp
  rw [star_eq_adjoint, adjoint_inner_right] at hp
  change RCLike.re (⟪D x, D x⟫_ℂ) ≤ _ at hp
  rwa [← InnerProductSpace.norm_sq_eq_re_inner] at hp

omit [CompleteSpace H] in
private theorem expectation_tendsto {ι : Type*} {l : Filter ι}
    {T : ι → H →L[ℂ] H} {S : H →L[ℂ] H} {x : H}
    (hT : Tendsto (fun i => T i x) l (𝓝 (S x))) :
    Tendsto (fun i => expectation x (T i)) l (𝓝 (expectation x S)) :=
  Complex.continuous_re.continuousAt.tendsto.comp (tendsto_const_nhds.inner hT)

omit [CompleteSpace H] in
private theorem nonneg_of_strong_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → H →L[ℂ] H} {S : H →L[ℂ] H}
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 (S x)))
    (hpos : ∀ᶠ i in l, 0 ≤ T i) : 0 ≤ S := by
  apply nonneg_iff_isPositive.mpr
  apply isPositive_def.mpr
  constructor
  · intro x y
    apply tendsto_nhds_unique_of_eventuallyEq ((hT x).inner tendsto_const_nhds)
      (tendsto_const_nhds.inner (hT y))
    filter_upwards [hpos] with i hi
    exact (nonneg_iff_isPositive.mp hi).inner_left_eq_inner_right x y
  · intro x
    change 0 ≤ (⟪S x, x⟫_ℂ).re
    have hh : Tendsto (fun i => (⟪T i x, x⟫_ℂ).re) l (𝓝 ((⟪S x, x⟫_ℂ).re)) :=
      Complex.continuous_re.continuousAt.tendsto.comp ((hT x).inner tendsto_const_nhds)
    apply ge_of_tendsto hh
    exact hpos.mono fun i hi => (nonneg_iff_isPositive.mp hi).re_inner_nonneg_left x

private theorem cauchy_eval_atTop {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (T : ι → H →L[ℂ] H) (hMono : Monotone T) (hPos : ∀ i, 0 ≤ T i)
    {r : ℝ} (hr : 0 ≤ r) (hBound : ∀ i, T i ≤ algebraMap ℝ (H →L[ℂ] H) r) (x : H) :
    Cauchy (Filter.map (fun i => T i x) atTop) := by
  let q := fun i => expectation x (T i)
  have hq : Monotone q := (expectation_mono x).comp hMono
  have hQ : BddAbove (Set.range q) :=
    ⟨expectation x (algebraMap ℝ (H →L[ℂ] H) r), by
      rintro _ ⟨i, rfl⟩
      exact expectation_mono x (hBound i)⟩
  let Q := ⨆ i, q i
  have hlimit : Tendsto q atTop (𝓝 Q) := tendsto_atTop_ciSup hq hQ
  have hδ : Tendsto (fun i => r * (Q - q i)) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using (hlimit.const_sub Q).const_mul r
  have hstep {i j : ι} (hij : i ≤ j) : dist (T j x) (T i x) ^ 2 ≤ r * (Q - q i) := by
    let D := T j - T i
    have hD : 0 ≤ D := sub_nonneg.mpr (hMono hij)
    have hB : D ≤ algebraMap ℝ (H →L[ℂ] H) r :=
      (sub_le_self _ (hPos i)).trans (hBound j)
    have h := deviation_sq_le D hD r hB x
    have he : expectation x D = q j - q i := by
      simp only [D, q, expectation, sub_apply, inner_sub_right, Complex.sub_re]
    rw [he] at h
    rw [dist_eq_norm]
    exact h.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right (le_ciSup hQ j) _) hr)
  apply cauchy_map_iff'.mpr
  intro S hS
  obtain ⟨ε, hε, hSb⟩ := Metric.mem_uniformity_dist.mp hS
  have hev := hδ.eventually (gt_mem_nhds (sq_pos_of_pos (half_pos hε)))
  rcases eventually_atTop.mp hev with ⟨N, hN⟩
  rw [prod_atTop_atTop_eq, mem_map]
  change ∀ᶠ p : ι × ι in atTop, (T p.1 x, T p.2 x) ∈ S
  have : IsDirectedOrder (ι × ι) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    obtain ⟨d, had, hbd⟩ := exists_ge_ge a.2 b.2
    exact ⟨(c, d), ⟨hac, had⟩, ⟨hbc, hbd⟩⟩⟩
  rw [eventually_atTop]
  refine ⟨(N, N), fun ⟨i,j⟩ ⟨hi,hj⟩ => hSb ?_⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hd {i : ι} (hi : N ≤ i) (hik : i ≤ k) : dist (T k x) (T i x) < ε / 2 :=
    (sq_lt_sq₀ dist_nonneg (half_pos hε).le).mp ((hstep hik).trans_lt (hN i hi))
  change dist (T i x) (T j x) < ε
  calc
    _ ≤ dist (T i x) (T k x) + dist (T k x) (T j x) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by rw [dist_comm]; exact hd hi hik) (hd hj hjk)
    _ = ε := add_halves ε

set_option maxHeartbeats 500000 in
/-- A bounded increasing positive net converges strongly to its operator supremum. -/
theorem exists_isLUB_strong_tendsto {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (M : VonNeumannAlgebra H) (T : ι → H →L[ℂ] H) (hM : ∀ i, T i ∈ M)
    (hMono : Monotone T) (hPos : ∀ i, 0 ≤ T i)
    {r : ℝ} (hr : 0 ≤ r) (hBound : ∀ i, T i ≤ algebraMap ℝ (H →L[ℂ] H) r) :
    ∃ S, S ∈ M ∧ IsLUB (Set.range T) S ∧
      ∀ x, Tendsto (fun i => T i x) atTop (𝓝 (S x)) := by
  have hC (x : H) : ∃ y, Tendsto (fun i => T i x) atTop (𝓝 y) :=
    cauchy_map_iff_exists_tendsto.mp (cauchy_eval_atTop T hMono hPos hr hBound x)
  choose F hF using hC
  let L : H →ₗ[ℂ] H :=
    { toFun := F
      map_add' x y := tendsto_nhds_unique_of_eventuallyEq (hF (x + y)) ((hF x).add (hF y))
        (Eventually.of_forall fun i => map_add (T i) x y)
      map_smul' c x := tendsto_nhds_unique_of_eventuallyEq (hF (c • x))
        ((hF x).const_smul c) (Eventually.of_forall fun i => map_smul (T i) c x) }
  have hnorm (x : H) : ‖L x‖ ≤ r * ‖x‖ := by
    apply le_of_tendsto (hF x).norm
    exact Eventually.of_forall fun i =>
      ((T i).le_opNorm x).trans (mul_le_mul_of_nonneg_right
        ((CStarAlgebra.norm_le_iff_le_algebraMap (T i) hr (hPos i)).mpr (hBound i)) (norm_nonneg x))
  let S := L.mkContinuous r hnorm
  have hS (x : H) : Tendsto (fun i => T i x) atTop (𝓝 (S x)) := hF x
  refine ⟨S, ?_, ⟨?_, ?_⟩, hS⟩
  · rw [← VonNeumannAlgebra.commutant_commutant M, VonNeumannAlgebra.mem_commutant_iff]
    intro R hR
    ext x
    have hx := tendsto_nhds_unique_of_eventuallyEq
      (R.continuous.continuousAt.tendsto.comp (hS x)) (hS (R x)) ?_
    · exact hx
    · exact Eventually.of_forall fun i =>
        DFunLike.congr_fun (VonNeumannAlgebra.mem_commutant_iff.mp hR (T i) (hM i)).symm x
  · rintro _ ⟨i, rfl⟩
    apply sub_nonneg.mp
    exact nonneg_of_strong_tendsto (fun x => (hS x).sub_const (T i x))
      ((eventually_ge_atTop i).mono fun j hij => sub_nonneg.mpr (hMono hij))
  · intro B hB
    apply sub_nonneg.mp
    exact nonneg_of_strong_tendsto (fun x => (hS x).const_sub (B x))
      (Eventually.of_forall fun i => sub_nonneg.mpr (hB (Set.mem_range_self i)))

/-- A vector expectation preserves the supremum of a bounded increasing positive net. -/
theorem exists_isLUB_expectation {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (M : VonNeumannAlgebra H) (T : ι → H →L[ℂ] H) (hM : ∀ i, T i ∈ M)
    (hMono : Monotone T) (hPos : ∀ i, 0 ≤ T i)
    {r : ℝ} (hr : 0 ≤ r) (hBound : ∀ i, T i ≤ algebraMap ℝ (H →L[ℂ] H) r) :
    ∃ S, S ∈ M ∧ IsLUB (Set.range T) S ∧
      ∀ x, IsLUB (Set.range (fun i => expectation x (T i))) (expectation x S) := by
  obtain ⟨S, hSM, hSL, hS⟩ := exists_isLUB_strong_tendsto M T hM hMono hPos hr hBound
  refine ⟨S, hSM, hSL, fun x => ⟨?_, ?_⟩⟩
  · rintro _ ⟨i, rfl⟩
    exact expectation_mono x (hSL.1 (Set.mem_range_self i))
  · intro B hB
    exact le_of_tendsto (expectation_tendsto (hS x)) <|
      Eventually.of_forall fun i => hB (Set.mem_range_self i)

end Omega.NormalVectorFunctional
