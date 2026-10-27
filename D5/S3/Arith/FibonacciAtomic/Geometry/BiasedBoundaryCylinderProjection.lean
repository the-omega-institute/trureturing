/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.L2Space]
   utility: none
   digest: Actual normalized cylinder averages form the finite cylinder projection. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering
import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffixEnergy
import D5.S0.Computability.Coding.BiasedMassFrontier

/-! Cylinder averages on the original biased boundary Hilbert space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (Edge H)
open BiasedBoundaryTrace (Omega M G cylinder indicator)
open BiasedBoundaryPathSplit (constG S boundary_path_split)
open BiasedBoundaryCentering (mean Pi C centered_suffix_residual)
open BiasedBoundaryConditionalLaw (prepend tail pullback conditional conditional_pullback_law)
open D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)
open D5.S0.Computability.Coding.BiasedMassFrontier (rayPrefix)
open MeasureTheory Filter
open scoped BigOperators ENNReal

/-- The actual normalized atom integral as a continuous functional. -/
def atomMean (p : Edge) : G →L[ℝ] ℝ :=
  (M.real (cylinder p.val))⁻¹ • innerSL ℝ (indicator p)

/-- The finite actual cylinder-average operator on the original L2(M). -/
def Q (A : Finset Edge) : G →L[ℝ] G :=
  ∑ p ∈ A, (atomMean p).smulRight (indicator p)

/-- The actual cylinder-constant subspace. -/
def V (A : Finset Edge) : Submodule ℝ G :=
  Submodule.span ℝ (indicator '' (A : Set Edge))

private theorem cylinder_ray (p : Address) (ω : Omega) :
    ω ∈ cylinder p ↔ p = rayPrefix ω p.length := by
  constructor
  · intro h
    apply List.ext_getElem (by simp [rayPrefix])
    intro i hi hj
    have he := h i (Finset.mem_range.mpr hi)
    simpa [rayPrefix, List.getD_eq_getElem?_getD, hi] using he.symm
  · intro h
    intro i hi
    have hi' : i < p.length := Finset.mem_range.mp hi
    change ω i = p.getD i false
    rw [h]
    simp [rayPrefix, List.getD_eq_getElem?_getD, hi']

private theorem cylinders_disjoint (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge))) {p q : Edge}
    (hp : p ∈ A) (hq : q ∈ A) (hne : p ≠ q) :
    Disjoint (cylinder p.val) (cylinder q.val) := by
  apply Set.disjoint_left.mpr
  intro ω hωp hωq
  have he (u v : Address) (hu : u = rayPrefix ω u.length)
      (hv : v = rayPrefix ω v.length) (hl : u.length ≤ v.length) : u <+: v := by
    apply List.prefix_iff_getElem?.mpr
    intro i hi
    have hiu : i < u.length := by simpa using hi
    have hiv : i < v.length := lt_of_lt_of_le hiu hl
    have hgu : u[i]? = some (ω i) := by
      simpa [rayPrefix, hiu] using congrArg (fun w : Address => w[i]?) hu
    have hgv : v[i]? = some (ω i) := by
      simpa [rayPrefix, hiv] using congrArg (fun w : Address => w[i]?) hv
    have hget : u[i] = ω i := by simpa [hiu] using hgu
    simpa [hget] using hgv
  have hpu : p.val ∈ Subtype.val '' (A : Set Edge) := ⟨p, hp, rfl⟩
  have hqu : q.val ∈ Subtype.val '' (A : Set Edge) := ⟨q, hq, rfl⟩
  apply hne
  apply Subtype.ext
  rcases le_total p.val.length q.val.length with h | h
  · exact hA hpu hqu (he _ _ ((cylinder_ray _ _).mp hωp) ((cylinder_ray _ _).mp hωq) h)
  · exact (hA hqu hpu (he _ _ ((cylinder_ray _ _).mp hωq) ((cylinder_ray _ _).mp hωp) h)).symm

private theorem atomMean_integral (p : Edge) (F : G) :
    atomMean p F = (M.real (cylinder p.val))⁻¹ * ∫ ω in cylinder p.val, F ω ∂M := by
  change (M.real (cylinder p.val))⁻¹ * inner ℝ (indicator p) F = _
  congr 1
  exact L2.inner_indicatorConstLp_one _ _ F

private theorem prepend_embedding (p : Address) : Topology.IsClosedEmbedding (prepend p) := by
  have hc : Continuous (prepend p) := by
    apply continuous_pi
    intro i
    by_cases hi : i < p.length
    · simpa [prepend, hi] using (continuous_const : Continuous (fun _ : Omega => p.getD i false))
    · simpa [prepend, hi] using
        (continuous_apply (i-p.length) : Continuous (fun ω : Omega => ω (i-p.length)))
  apply hc.isClosedEmbedding
  intro ω η h
  have he := congrArg (tail p.length) h
  simpa only [conditional_pullback_law.2.2.2.2.2.2.2] using he

private theorem atomMean_pullback (p : Edge) (F : G) :
    atomMean p F = mean (pullback p.val F) := by
  rw [atomMean_integral, centered_suffix_residual.1]
  rw [integral_congr_ae (conditional_pullback_law.2.2.2.2.1 p.val F)]
  change _ = ∫ ω, F (prepend p.val ω) ∂M
  rw [(conditional_pullback_law.2.2.1 p.val).integral_comp
    (prepend_embedding p.val).measurableEmbedding]
  simp [conditional, integral_smul_measure, measureReal_def, ENNReal.toReal_inv]

private theorem indicator_inner_self (p : Edge) :
    inner ℝ (indicator p) (indicator p) = M.real (cylinder p.val) := by
  change inner ℝ (indicatorConstLp 2 _ _ (1 : ℝ))
    (indicatorConstLp 2 _ _ (1 : ℝ)) = _
  rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, Set.inter_self]

private theorem indicator_inner_other (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge))) {p q : Edge}
    (hp : p ∈ A) (hq : q ∈ A) (hne : p ≠ q) :
    inner ℝ (indicator p) (indicator q) = 0 := by
  have hd := Set.disjoint_iff_inter_eq_empty.mp (cylinders_disjoint A hA hp hq hne)
  change inner ℝ (indicatorConstLp 2 _ _ (1 : ℝ)) (indicatorConstLp 2 _ _ (1 : ℝ)) = 0
  rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, hd]
  simp

private theorem atomMean_indicator (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge))) {p q : Edge}
    (hp : p ∈ A) (hq : q ∈ A) : atomMean p (indicator q) = if p = q then 1 else 0 := by
  change (M.real (cylinder p.val))⁻¹ * inner ℝ (indicator p) (indicator q) = _
  by_cases he : p = q
  · subst q
    rw [indicator_inner_self, ite_eq_left rfl, inv_mul_cancel₀]
    exact (ENNReal.toReal_pos (conditional_pullback_law.1 p.val) (measure_ne_top _ _)).ne'
  · rw [indicator_inner_other A hA hp hq he, mul_zero, ite_eq_right he]

private theorem Q_apply (A : Finset Edge) (F : G) :
    Q A F = ∑ p ∈ A, atomMean p F • indicator p := by
  simp [Q]

private theorem Q_mem (A : Finset Edge) (F : G) : Q A F ∈ V A := by
  classical
  rw [Q_apply]
  apply Submodule.sum_mem
  intro p hp
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩)

private theorem Q_indicator (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge))) {p : Edge} (hp : p ∈ A) :
    Q A (indicator p) = indicator p := by
  classical
  rw [Q_apply]
  rw [Finset.sum_eq_single p]
  · rw [atomMean_indicator A hA hp hp, ite_eq_left rfl, one_smul]
  · intro q hq hne
    rw [atomMean_indicator A hA hq hp, ite_eq_right hne, zero_smul]
  · exact fun hn => (hn hp).elim

private theorem inner_Q (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge))) {p : Edge}
    (hp : p ∈ A) (F : G) : inner ℝ (indicator p) (Q A F) = inner ℝ (indicator p) F := by
  classical
  rw [Q_apply]
  rw [inner_sum, Finset.sum_eq_single p]
  · rw [inner_smul_right, indicator_inner_self]
    change ((M.real (cylinder p.val))⁻¹ * inner ℝ (indicator p) F) * M.real (cylinder p.val) = _
    have hm : M.real (cylinder p.val) ≠ 0 :=
      (ENNReal.toReal_pos (conditional_pullback_law.1 p.val) (measure_ne_top _ _)).ne'
    field_simp
  · intro q hq hne
    rw [inner_smul_right, indicator_inner_other A hA hp hq hne.symm, mul_zero]
  · exact fun hn => (hn hp).elim

private theorem residual_orthogonal (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge))) (F : G) :
    F-Q A F ∈ (V A)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, hp, rfl⟩ := hg
    rw [inner_sub_right, inner_Q A hA hp F, sub_self]
  | zero => simp
  | add g h hg hh ihg ihh => simp [inner_add_left, ihg, ihh]
  | smul c g hg ih => simp [inner_smul_left, ih]

instance (A : Finset Edge) : FiniteDimensional ℝ (V A) :=
  FiniteDimensional.span_of_finite ℝ ((Finset.finite_toSet A).image indicator)

/-- The operator is built from actual normalized atom integrals and is exactly
the orthogonal projection onto the actual cylinder-constant subspace. -/
theorem cylinder_average_projection (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge))) :
    (∀ (p : Edge) (F : G), atomMean p F =
      (M.real (cylinder p.val))⁻¹ * ∫ ω in cylinder p.val, F ω ∂M) ∧
    (∀ (p : Edge) (F : G), atomMean p F = mean (pullback p.val F)) ∧
    (∀ F : G, Q A F = (V A).starProjection F) ∧
    (∀ p ∈ A, Q A (indicator p) = indicator p) := by
  refine ⟨atomMean_integral, atomMean_pullback, ?_, fun p hp => Q_indicator A hA hp⟩
  intro F
  exact ((V A).eq_starProjection_of_mem_orthogonal (Q_mem A F)
    (residual_orthogonal A hA F)).symm

private theorem Q_ae (A : Finset Edge) (F : G) :
    Q A F =ᵐ[M] (fun ω => ∑ p ∈ A,
      atomMean p F * (cylinder p.val).indicator (fun _ => (1 : ℝ)) ω) := by
  classical
  rw [Q_apply]
  induction A using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := M))
  | @insert p A hp ih =>
    rw [Finset.sum_insert hp]
    filter_upwards [Lp.coeFn_add (atomMean p F • indicator p)
      (∑ q ∈ A, atomMean q F • indicator q),
      Lp.coeFn_smul (atomMean p F) (indicator p),
      (show indicator p =ᵐ[M] (cylinder p.val).indicator (fun _ => (1 : ℝ)) from
        indicatorConstLp_coeFn), ih] with ω ha hs hi hsum
    rw [ha, hs, hi, hsum, Finset.sum_insert hp]
    rfl

private theorem Q_pullback (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge))) {p : Edge}
    (hp : p ∈ A) (F : G) : pullback p.val (Q A F) = constG (atomMean p F) := by
  classical
  have hq : Q A F =ᵐ[conditional p.val] (fun _ => atomMean p F) := by
    have ha := Measure.ae_smul_measure (ae_restrict_of_ae (Q_ae A F))
      ((M (cylinder p.val))⁻¹)
    have hm := Measure.ae_smul_measure
      (ae_restrict_mem (BiasedBoundaryTrace.indicator._proof_1 p))
      ((M (cylinder p.val))⁻¹)
    filter_upwards [ha, hm] with ω hsum hω
    rw [hsum, Finset.sum_eq_single p]
    · simp [hω]
    · intro q hq hne
      have hn : ω ∉ cylinder q.val := fun hh =>
        (Set.disjoint_left.mp (cylinders_disjoint A hA hp hq hne.symm)) hω hh
      simp [hn]
    · exact fun hn => (hn hp).elim
  have hc := (conditional_pullback_law.2.2.1 p.val).quasiMeasurePreserving.ae_eq_comp hq
  apply Lp.ext
  filter_upwards [conditional_pullback_law.2.2.2.2.1 p.val (Q A F), hc,
    boundary_path_split.2.2.2.1 (atomMean p F)] with ω h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

private theorem norm_sq_integral (F : G) : ‖F‖ ^ 2 = ∫ ω, (F ω) ^ 2 ∂M := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply, pow_two]

private theorem pullback_norm_sq (p : Edge) (F : G) :
    M.real (cylinder p.val) * ‖pullback p.val F‖ ^ 2 =
      ∫ ω in cylinder p.val, (F ω) ^ 2 ∂M := by
  rw [norm_sq_integral]
  have hae : (fun ω => (pullback p.val F ω)^2) =ᵐ[M]
      (fun ω => (F (prepend p.val ω))^2) :=
    (conditional_pullback_law.2.2.2.2.1 p.val F).fun_comp (fun x : ℝ => x^2)
  rw [integral_congr_ae hae]
  rw [(conditional_pullback_law.2.2.1 p.val).integral_comp
    (prepend_embedding p.val).measurableEmbedding (fun ω => (F ω)^2)]
  rw [conditional, integral_smul_measure, ENNReal.toReal_inv]
  change M.real (cylinder p.val) *
    ((M.real (cylinder p.val))⁻¹ * ∫ ω in cylinder p.val, (F ω)^2 ∂M) = _
  have hm : M.real (cylinder p.val) ≠ 0 :=
    (ENNReal.toReal_pos (conditional_pullback_law.1 p.val) (measure_ne_top _ _)).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]

private theorem partition_norm_sq (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge)))
    (hcover : ∀ ω : Omega, ∃ p ∈ A, ω ∈ cylinder p.val) (F : G) :
    ‖F‖ ^ 2 = ∑ p ∈ A, M.real (cylinder p.val) * ‖pullback p.val F‖ ^ 2 := by
  have hu : (⋃ p ∈ A, cylinder p.val) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hcover ω
  have hi : Integrable (fun ω => (F ω)^2) M := by
    simpa only [Real.inner_apply, pow_two] using (L2.integrable_inner (𝕜 := ℝ) F F)
  rw [norm_sq_integral, ← setIntegral_univ, ← hu]
  rw [integral_biUnion_finset A
    (fun p _ => BiasedBoundaryTrace.indicator._proof_1 p)
    (fun p hp q hq hne => cylinders_disjoint A hA hp hq hne)
    (fun _ _ => hi.integrableOn)]
  apply Finset.sum_congr rfl
  intro p hp
  exact (pullback_norm_sq p F).symm

private theorem atomMean_const (p : Edge) (c : ℝ) : atomMean p (constG c) = c := by
  rw [atomMean_integral,
    integral_congr_ae (ae_restrict_of_ae (boundary_path_split.2.2.2.1 c)), integral_const]
  change (M.real (cylinder p.val))⁻¹ * (M.real (cylinder p.val) * c) = c
  rw [← mul_assoc, inv_mul_cancel₀
    (ENNReal.toReal_pos (conditional_pullback_law.1 p.val) (measure_ne_top _ _)).ne', one_mul]

private theorem Q_const (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge)))
    (hcover : ∀ ω : Omega, ∃ p ∈ A, ω ∈ cylinder p.val) (c : ℝ) :
    Q A (constG c) = constG c := by
  classical
  apply Lp.ext
  filter_upwards [Q_ae A (constG c), boundary_path_split.2.2.2.1 c] with ω hq hc
  obtain ⟨p, hp, hω⟩ := hcover ω
  rw [hq, hc, Finset.sum_eq_single p]
  · rw [atomMean_const]
    simp [hω]
  · intro q hq hne
    have hn : ω ∉ cylinder q.val := fun hh =>
      (Set.disjoint_left.mp (cylinders_disjoint A hA hp hq hne.symm)) hω hh
    simp [hn]
  · exact fun hn => (hn hp).elim

private theorem Q_mean (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge)))
    (hcover : ∀ ω : Omega, ∃ p ∈ A, ω ∈ cylinder p.val) (F : G) :
    mean (Q A F) = mean F := by
  change inner ℝ (constG 1) (Q A F) = inner ℝ (constG 1) F
  rw [(cylinder_average_projection A hA).2.2.1]
  rw [← Submodule.inner_starProjection_left_eq_right]
  rw [← (cylinder_average_projection A hA).2.2.1, Q_const A hA hcover]

private theorem Q_Pi (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge)))
    (hcover : ∀ ω : Omega, ∃ p ∈ A, ω ∈ cylinder p.val) (F : G) :
    Q A (Pi F) = Pi (Q A F) := by
  rw [centered_suffix_residual.2.2.1, map_sub, Q_const A hA hcover,
    centered_suffix_residual.2.2.1, Q_mean A hA hcover]

/-- On an actual cylinder partition the constructed average has a constant
conditional pullback, and the centered residual has the exact weighted norm. -/
theorem partition_centered_residual (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge)))
    (hcover : ∀ ω : Omega, ∃ p ∈ A, ω ∈ cylinder p.val) :
    (∀ p ∈ A, ∀ F : G, pullback p.val (Q A F) = constG (atomMean p F)) ∧
    (∀ p ∈ A, ∀ z : H, pullback p.val (C z-Q A (C z)) = C (S p.val z)) ∧
    (∀ F : G, ‖F‖ ^ 2 =
      ∑ p ∈ A, M.real (cylinder p.val) * ‖pullback p.val F‖ ^ 2) ∧
    (∀ z : H, ‖C z-Q A (C z)‖ ^ 2 =
      ∑ p ∈ A, M.real (cylinder p.val) * ‖C (S p.val z)‖ ^ 2) ∧
    (∀ c : ℝ, Q A (constG c) = constG c) ∧
    (∀ F : G, Q A (Pi F) = Pi (Q A F)) := by
  have hlocal (p : Edge) (hp : p ∈ A) (z : H) :
      pullback p.val (C z-Q A (C z)) = C (S p.val z) := by
    rw [map_sub, Q_pullback A hA hp, atomMean_pullback,
      ← centered_suffix_residual.2.2.1, centered_suffix_residual.2.2.2.2.1]
  refine ⟨fun p hp F => Q_pullback A hA hp F, hlocal,
    partition_norm_sq A hA hcover, ?_, Q_const A hA hcover, Q_Pi A hA hcover⟩
  intro z
  rw [partition_norm_sq A hA hcover]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hlocal p hp z]

/-- The actual residual of an actual cylinder partition obeys the threshold
estimate whenever each of its actual cylinder masses is at most t. -/
theorem bounded_partition_residual (A : Finset Edge)
    (hA : IsPrefixFree (Subtype.val '' (A : Set Edge)))
    (hcover : ∀ ω : Omega, ∃ p ∈ A, ω ∈ cylinder p.val)
    (t : ℝ) (ht : 0 ≤ t) (hm : ∀ p ∈ A, M.real (cylinder p.val) ≤ t) (z : H) :
    ‖C z-Q A (C z)‖ ^ 2 ≤ Real.goldenRatio * t * ‖z‖ ^ 2 := by
  classical
  rw [(partition_centered_residual A hA hcover).2.2.2.1]
  have hAi : IsPrefixFree ((A.image Subtype.val : Finset Address) : Set Address) := by
    simpa only [Finset.coe_image] using hA
  have hb := BiasedBoundarySuffixEnergy.weighted_centered_suffix_energy
    (A.image Subtype.val) hAi (fun p => M.real (cylinder p)) t ht (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨ENNReal.toReal_nonneg, hm q hq⟩) z
  rw [Finset.sum_image] at hb
  · exact hb
  · exact fun _ _ _ _ he => Subtype.ext he

#print axioms cylinder_average_projection
#print axioms partition_centered_residual
#print axioms bounded_partition_residual

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderProjection
