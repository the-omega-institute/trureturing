/- GID: D5/S3/Geometry/SphereSectionAvoidance
   generality: G
   mirror-B: D5/B/S3/Geometry/SphereSectionAvoidance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Roots]
   utility: none
   digest: Finite avoidance in open round-sphere patches. -/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic

/-! Classical finite general-position construction using rational circle arcs.
The carrier has dimension at least two: no avoidance claim is made for a
two-point sphere. All radii are strictly positive. -/

noncomputable section
public section

open Set Metric Topology
open scoped InnerProductSpace Polynomial

namespace D5.S3.Geometry.SphereSectionAvoidance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A rational parametrization of a circle through `x`, with tangent `v`. -/
def circleArc (x v : E) (t : ℝ) : E :=
  ((1 - t ^ 2) / (1 + t ^ 2)) • x + ((2 * t) / (1 + t ^ 2)) • v

private theorem arc_den_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

private theorem circleArc_zero (x v : E) : circleArc x v 0 = x := by
  simp [circleArc]

private theorem continuous_circleArc (x v : E) : Continuous (circleArc x v) := by
  unfold circleArc
  have hc : Continuous (fun t : ℝ => 1 + t ^ 2) := by fun_prop
  exact (((continuous_const.sub (continuous_id.pow 2)).div₀ hc
    (fun t => (arc_den_pos t).ne')).smul continuous_const).add
    (((continuous_const.mul continuous_id).div₀ hc
      (fun t => (arc_den_pos t).ne')).smul continuous_const)

private theorem norm_circleArc {x v : E} {r : ℝ} (hr : 0 < r)
    (hx : ‖x‖ = r) (hv : ‖v‖ = r) (hxv : ⟪x, v⟫_ℝ = 0) (t : ℝ) :
    ‖circleArc x v t‖ = r := by
  have hid : ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 +
      ((2 * t) / (1 + t ^ 2)) ^ 2 = 1 := by
    field_simp
    ring
  have hsq : ‖circleArc x v t‖ ^ 2 = r ^ 2 := by
    simp only [circleArc, norm_add_sq_real, real_inner_smul_left,
      real_inner_smul_right, hxv, mul_zero, add_zero,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hx, hv]
    nlinarith [hid]
  nlinarith [norm_nonneg (circleArc x v t)]

private def sectionPolynomial (a b c : ℝ) : ℝ[X] :=
  Polynomial.C (a - c) + Polynomial.C (2 * b) * Polynomial.X +
    Polynomial.C (-a - c) * Polynomial.X ^ 2

private theorem sectionPolynomial_ne_zero {a b c : ℝ}
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) : sectionPolynomial a b c ≠ 0 := by
  intro hp
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hp
  have h1 := congrArg (fun p : ℝ[X] => p.coeff 1) hp
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) hp
  simp only [sectionPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_zero] at h0 h1 h2
  norm_num at h0 h1 h2
  rcases h with h | h | h <;> apply h <;> linarith

private theorem arc_section_root {x v a : E} {b t : ℝ}
    (h : ⟪a, circleArc x v t⟫_ℝ = b) :
    (sectionPolynomial ⟪a, x⟫_ℝ ⟪a, v⟫_ℝ b).IsRoot t := by
  simp only [circleArc, inner_add_right, real_inner_smul_right] at h
  change Polynomial.eval t _ = 0
  simp only [sectionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  have hn := (arc_den_pos t).ne'
  field_simp at h
  nlinarith [h]

private theorem exists_arc_avoiding {ι : Type*} [Finite ι]
    (x v : E) (a : ι → E) (b : ι → ℝ)
    (h : ∀ i, ⟪a i, x⟫_ℝ ≠ 0 ∨ ⟪a i, v⟫_ℝ ≠ 0 ∨ b i ≠ 0)
    {U : Set E} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ t : ℝ, circleArc x v t ∈ U ∧ ∀ i, ⟪a i, circleArc x v t⟫_ℝ ≠ b i := by
  have h0 : (0 : ℝ) ∈ circleArc x v ⁻¹' U := by simpa [circleArc_zero] using hx
  have hopen : IsOpen (circleArc x v ⁻¹' U) := hU.preimage (continuous_circleArc x v)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds h0)
  let bad : Set ℝ := ⋃ i, {t | (sectionPolynomial ⟪a i, x⟫_ℝ ⟪a i, v⟫_ℝ (b i)).IsRoot t}
  have hbad : bad.Finite := Set.finite_iUnion fun i =>
    Polynomial.finite_setOfPred_isRoot (sectionPolynomial_ne_zero (h i))
  obtain ⟨t, ht, hnot⟩ := (Set.Ioo_infinite (by linarith : -ε < ε)).exists_notMem_finite hbad
  refine ⟨t, hball ?_, fun i hi => hnot ?_⟩
  · simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using ht
  · exact Set.mem_iUnion.mpr ⟨i, arc_section_root hi⟩

private theorem exists_tangent [FiniteDimensional ℝ E]
    (hd : 2 ≤ Module.finrank ℝ E) {x : E} (hx : x ≠ 0) :
    ∃ v : E, ⟪x, v⟫_ℝ = 0 ∧ v ≠ 0 := by
  have hdim := (ℝ ∙ x).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hx] at hdim
  have hp : 0 < Module.finrank ℝ (ℝ ∙ x)ᗮ := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hp
  refine ⟨v, Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property, ?_⟩
  intro h
  apply hv
  exact Subtype.ext h

/-- Every nonempty ambient-open patch of a positive-radius sphere avoids any
finite family of affine hyperplanes with nonzero normals. The ambient space
here is the actual linear carrier, so its dimension must be at least two. -/
theorem exists_on_sphere_avoiding_sections [FiniteDimensional ℝ E]
    (hd : 2 ≤ Module.finrank ℝ E) {r : ℝ} (hr : 0 < r)
    {U : Set E} (hU : IsOpen U) (hpatch : ∃ x ∈ U, ‖x‖ = r)
    {ι : Type*} [Finite ι] (a : ι → E) (b : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    ∃ y ∈ U, ‖y‖ = r ∧ ∀ i, ⟪a i, y⟫_ℝ ≠ b i := by
  classical
  obtain ⟨x, hxU, hxr⟩ := hpatch
  have hx0 : x ≠ 0 := by intro hx; simp [hx] at hxr; linarith
  let J := {i : ι // ⟪a i, x⟫_ℝ = 0 ∧ b i = 0}
  obtain ⟨v, hxv, hv0, hvavoid⟩ : ∃ v : E, ⟪x, v⟫_ℝ = 0 ∧ v ≠ 0 ∧
      ∀ i : J, ⟪a i.val, v⟫_ℝ ≠ 0 := by
    by_cases hJ : Nonempty J
    · let p := (ℝ ∙ x)ᗮ
      let f (i : J) : Module.Dual ℝ E := (innerSL ℝ (a i.val)).toLinearMap
      obtain ⟨v, hvp, hv⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists p f
        (fun i => ⟨a i.val,
          Submodule.mem_orthogonal_singleton_iff_inner_left.mpr i.property.1,
          by
            change ⟪a i.val, a i.val⟫_ℝ ≠ 0
            exact (real_inner_self_pos.mpr (ha i.val)).ne'⟩)
      refine ⟨v, Submodule.mem_orthogonal_singleton_iff_inner_right.mp hvp, ?_, hv⟩
      intro hv0
      obtain ⟨i⟩ := hJ
      simpa [hv0] using hv i
    · obtain ⟨v, hvx, hv⟩ := exists_tangent hd hx0
      exact ⟨v, hvx, hv, fun i => (hJ ⟨i⟩).elim⟩
  let w := (r / ‖v‖) • v
  have hw : ‖w‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr (norm_pos_iff.mpr hv0))]
    exact div_mul_cancel₀ r (norm_ne_zero_iff.mpr hv0)
  have hxw : ⟪x, w⟫_ℝ = 0 := by
    dsimp only [w]
    rw [real_inner_smul_right, hxv, mul_zero]
  have hwavoid (i : J) : ⟪a i.val, w⟫_ℝ ≠ 0 := by
    simpa only [w, real_inner_smul_right, ne_eq, mul_eq_zero, not_or] using
      And.intro (ne_of_gt (div_pos hr (norm_pos_iff.mpr hv0))) (hvavoid i)
  obtain ⟨t, htU, ht⟩ := exists_arc_avoiding x w a b (fun i => by
    by_cases hax : ⟪a i, x⟫_ℝ = 0
    · by_cases hb : b i = 0
      · exact Or.inr (Or.inl (hwavoid ⟨i, hax, hb⟩))
      · exact Or.inr (Or.inr hb)
    · exact Or.inl hax) hU hxU
  exact ⟨circleArc x w t, htU, norm_circleArc hr hxr hw hxw t, ht⟩

private theorem exists_on_sphere_avoiding_proper_sections [FiniteDimensional ℝ E]
    (hd : 2 ≤ Module.finrank ℝ E) {r : ℝ} (hr : 0 < r)
    {U : Set E} (hU : IsOpen U) (hpatch : ∃ x ∈ U, ‖x‖ = r)
    {ι : Type*} [Finite ι] (a : ι → E) (b : ι → ℝ)
    (ha : ∀ i, a i = 0 → b i ≠ 0) :
    ∃ y ∈ U, ‖y‖ = r ∧ ∀ i, ⟪a i, y⟫_ℝ ≠ b i := by
  classical
  obtain ⟨y, hyU, hyr, hy⟩ := exists_on_sphere_avoiding_sections hd hr hU hpatch
    (fun i : {i // a i ≠ 0} => a i.val) (fun i => b i.val) (fun i => i.property)
  refine ⟨y, hyU, hyr, fun i => ?_⟩
  by_cases hi : a i = 0
  · simpa [hi] using (ha i hi).symm
  · exact hy ⟨i, hi⟩

/-- Simultaneous avoidance of proper affine sections and collisions on an
actual affine sphere in a linear carrier. The properness condition is the
exact nonvanishing of the restricted normal or of its constant equation;
no supplied geometric choice function is assumed. -/
theorem exists_on_affine_sphere_avoiding [FiniteDimensional ℝ E]
    (K : Submodule ℝ E) (hd : 2 ≤ Module.finrank ℝ K) (c : E)
    {R : ℝ} (hR : 0 < R) {U : Set E} (hU : IsOpen U)
    (hpatch : ∃ w : K, c + (w : E) ∈ U ∧ ‖w‖ = R)
    {ι κ : Type*} [Finite ι] [Finite κ] (z : ι → E) (q : κ → E)
    (hproper : ∀ i, K.orthogonalProjectionOnto (z i - c) = 0 →
      R ^ 2 + ‖z i - c‖ ^ 2 ≠ 1) :
    ∃ w : K, c + (w : E) ∈ U ∧ ‖w‖ = R ∧
      (∀ i, dist (c + (w : E)) (z i) ≠ 1) ∧
      ∀ j, c + (w : E) ≠ q j := by
  classical
  let J := {j : κ // q j ≠ c}
  let a : ι ⊕ J → K := Sum.elim
    (fun i => K.orthogonalProjectionOnto (z i - c))
    (fun j => K.orthogonalProjectionOnto (q j.val - c))
  let b : ι ⊕ J → ℝ := Sum.elim
    (fun i => (R ^ 2 + ‖z i - c‖ ^ 2 - 1) / 2)
    (fun j => ‖q j.val - c‖ ^ 2)
  have hnormal (i : ι ⊕ J) : a i = 0 → b i ≠ 0 := by
    rcases i with i | j
    · intro hi hb
      apply hproper i hi
      change (R ^ 2 + ‖z i - c‖ ^ 2 - 1) / 2 = 0 at hb
      linarith
    · intro _ hb
      apply j.property
      have hq : ‖q j.val - c‖ = 0 := by
        change ‖q j.val - c‖ ^ 2 = 0 at hb
        nlinarith [norm_nonneg (q j.val - c)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hq)
  have hcont : Continuous (fun w : K => c + (w : E)) :=
    continuous_const.add continuous_subtype_val
  obtain ⟨w, hwU, hwR, hw⟩ := exists_on_sphere_avoiding_proper_sections hd hR
    (hU.preimage hcont) hpatch a b hnormal
  have hproj (v : E) : ⟪K.orthogonalProjectionOnto v, w⟫_ℝ = ⟪v, (w : E)⟫_ℝ := by
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w v
  refine ⟨w, hwU, hwR, fun i hi => hw (.inl i) ?_, fun j hj => ?_⟩
  · change ⟪K.orthogonalProjectionOnto (z i - c), w⟫_ℝ =
      (R ^ 2 + ‖z i - c‖ ^ 2 - 1) / 2
    rw [hproj]
    have hdist : dist (c + (w : E)) (z i) ^ 2 =
        ‖w‖ ^ 2 - 2 * ⟪z i - c, (w : E)⟫_ℝ + ‖z i - c‖ ^ 2 := by
      rw [dist_eq_norm]
      have heq : c + (w : E) - z i = (w : E) - (z i - c) := by abel
      rw [heq, norm_sub_sq_real, real_inner_comm]
      rfl
    rw [hi, hwR] at hdist
    linarith
  · by_cases hjc : q j = c
    · have hw0 : w = 0 := by simpa [hjc] using hj
      have : ‖w‖ = 0 := by simp [hw0]
      linarith
    · apply hw (.inr ⟨j, hjc⟩)
      change ⟪K.orthogonalProjectionOnto (q j - c), w⟫_ℝ = ‖q j - c‖ ^ 2
      rw [hproj]
      have hwq : (w : E) = q j - c := by rw [← hj]; abel
      rw [hwq, real_inner_self_eq_norm_sq]

end D5.S3.Geometry.SphereSectionAvoidance
