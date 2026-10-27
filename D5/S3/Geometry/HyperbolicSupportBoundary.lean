/- GID: D5/S3/Geometry/HyperbolicSupportBoundary
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicSupportBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Geometry/Hyperideal/ActualRaysJointAngle.actual_rays_joint_angle]
   utility: none
   digest: Interior and frontier of finite Lorentz support regions in a native hyperbolic plane. -/

import D5.S3.Geometry.Hyperideal.ActualRaysJointAngle
import D5.S3.Geometry.HyperbolicTopology
import Mathlib.Topology.Maps.Basic
import Mathlib.Tactic

/-! Finite support inequalities in the topology of a complete native hyperbolic plane. -/

noncomputable section
open scoped BigOperators Topology
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.ActualRaysJointAngle
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace D5.S3.Geometry.HyperbolicSupportBoundary

set_option autoImplicit false

/-- The complete region cut out in the given actual plane. -/
def supportRegion {ι : Type*} (e : UpperHalfPlane → HyperbolicThreeSpace)
    (A : ι → Fin 4 → ℝ) : Set UpperHalfPlane :=
  {z | ∀ i, lorentz (A i) (lift (e z)) ≤ 0}

private theorem lift_continuous : Continuous lift := by
  have hc : Continuous (fun p : HyperbolicThreeSpace => p.coordinates) :=
    (D5.S3.Geometry.HyperbolicTopology.coordinatesHomeomorph (E := ℂ)).continuous
  have hh : Continuous (fun p : HyperbolicThreeSpace => height p.coordinates) :=
    (WithLp.continuous_snd 2 ℂ ℝ).comp (continuous_subtype_val.comp hc)
  have hx : Continuous (fun p : HyperbolicThreeSpace => p.coordinates.val.fst.re) :=
    Complex.continuous_re.comp ((WithLp.continuous_fst 2 ℂ ℝ).comp
      (continuous_subtype_val.comp hc))
  have hy : Continuous (fun p : HyperbolicThreeSpace => p.coordinates.val.fst.im) :=
    Complex.continuous_im.comp ((WithLp.continuous_fst 2 ℂ ℝ).comp
      (continuous_subtype_val.comp hc))
  have hn (p : HyperbolicThreeSpace) : height p.coordinates ≠ 0 :=
    p.coordinates.property.ne'
  apply continuous_pi
  intro i
  fin_cases i
  · exact hx.div hh hn
  · exact hy.div hh hn
  · exact ((((hx.pow 2).add (hy.pow 2)).add (hh.pow 2)).sub continuous_const).div
      (continuous_const.mul hh) (fun p => mul_ne_zero (by norm_num) (hn p))
  · exact ((((hx.pow 2).add (hy.pow 2)).add (hh.pow 2)).add continuous_const).div
      (continuous_const.mul hh) (fun p => mul_ne_zero (by norm_num) (hn p))

set_option maxHeartbeats 1000000 in
/-- Every remaining support has a strict feasible witness in the same plane.
Then the strict inequalities describe its full interior, and their active
equalities describe its full frontier, in the native plane topology. -/
theorem support_region_boundary {ι : Type*} [Finite ι]
    (e : UpperHalfPlane → HyperbolicThreeSpace) (he : Isometry e)
    (N : Fin 4 → ℝ)
    (hplane : range e = {p | lorentz N (lift p) = 0})
    (A : ι → Fin 4 → ℝ)
    (hw : ∀ i, ∃ y ∈ supportRegion e A, lorentz (A i) (lift (e y)) < 0) :
    interior (supportRegion e A) =
      {z | ∀ i, lorentz (A i) (lift (e z)) < 0} ∧
    frontier (supportRegion e A) =
      {z ∈ supportRegion e A | ∃ i, lorentz (A i) (lift (e z)) = 0} := by
  classical
  let R := supportRegion e A
  let L := fun i z => lorentz (A i) (lift (e z))
  have hLc (i : ι) : Continuous (L i) := by
    dsimp only [L, lorentz]
    exact continuous_finsetSum _ fun k _ =>
      continuous_const.mul ((continuous_apply k).comp (lift_continuous.comp he.continuous))
  have hclosed : IsClosed R := by
    change IsClosed {z | ∀ i, L i z ≤ 0}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (hLc i) continuous_const
  have hzero (x : UpperHalfPlane) (i : ι) (hxi : L i x = 0) :
      x ∉ interior R := by
    obtain ⟨y, hy, hiy⟩ := hw i
    have hxy : e x ≠ e y := by
      intro h
      have hL : L i x = L i y := congrArg (fun p => lorentz (A i) (lift p)) h
      rw [hxi] at hL
      exact (ne_of_lt hiy) hL.symm
    let Y := lift (e x)
    let Z := lift (e y)
    let d := dist (e x) (e y)
    have hd : 0 < d := dist_pos.mpr hxy
    have hs : 0 < Real.sinh d := Real.sinh_pos_iff.mpr hd
    have hYY : lorentz Y Y = -1 := lift_unit (e x)
    have hZZ : lorentz Z Z = -1 := lift_unit (e y)
    have hYZ : lorentz Y Z = -Real.cosh d := lift_cosh (e x) (e y)
    have hZY : lorentz Z Y = -Real.cosh d := by rw [lorentz_symm, hYZ]
    let U := (-Real.cosh d / Real.sinh d) • Y + (1 / Real.sinh d) • Z
    have hYU : lorentz Y U = 0 := by
      dsimp only [U]
      rw [lorentz_right, hYY, hYZ]
      ring
    have hUU : lorentz U U = 1 := by
      dsimp only [U]
      rw [lorentz_linear, hYY, hZZ, hYZ, hZY]
      field_simp [hs.ne']
      nlinarith [Real.cosh_sq_sub_sinh_sq d]
    have hNp (z : UpperHalfPlane) : lorentz N (lift (e z)) = 0 := by
      have hz : e z ∈ range e := mem_range_self z
      rw [hplane] at hz
      exact hz
    have hNU : lorentz N U = 0 := by
      dsimp only [U]
      rw [lorentz_right, hNp x, hNp y]
      ring
    have hAiU : lorentz (A i) U = L i y / Real.sinh d := by
      dsimp only [U]
      rw [lorentz_right]
      change (-Real.cosh d / Real.sinh d) * L i x +
        (1 / Real.sinh d) * L i y = _
      rw [hxi]
      ring
    obtain ⟨g, _, hg, _, _, _, hglift, _⟩ :=
      actual_rays_joint_angle Y U U hYY (lift_time (e x)) hUU hUU hYU hYU
        (by rw [hUU]; norm_num)
    have hg0' : g 0 = e x := by
      apply lift_injective
      rw [hglift]
      simp [Y]
    have hgrange (t : ℝ) : g t ∈ range e := by
      rw [hplane]
      change lorentz N (lift (g t)) = 0
      rw [hglift, lorentz_right, hNp x, hNU]
      ring
    let c : ℝ → UpperHalfPlane := fun t => Classical.choose (hgrange t)
    have hc (t : ℝ) : e (c t) = g t := Classical.choose_spec (hgrange t)
    have hcc : Continuous c := he.isEmbedding.continuous_iff.mpr
      (by simpa only [Function.comp_def, hc] using hg.continuous)
    have hc0 : c 0 = x := he.injective ((hc 0).trans hg0')
    have hout (t : ℝ) (ht : t < 0) : c t ∉ R := by
      intro hin
      have hle : L i (c t) ≤ 0 := hin i
      have hread : L i (c t) = Real.sinh t * (L i y / Real.sinh d) := by
        dsimp only [L]
        rw [hc, hglift, lorentz_right]
        change Real.cosh t * L i x + Real.sinh t * lorentz (A i) U = _
        rw [hxi, hAiU]
        ring
      rw [hread] at hle
      exact (not_lt_of_ge hle) (mul_pos_of_neg_of_neg
        (Real.sinh_neg_iff.mpr ht) (div_neg_of_neg_of_pos hiy hs))
    intro hx
    have hnhds : R ∈ 𝓝 (c 0) := by
      simpa only [hc0] using mem_interior_iff_mem_nhds.mp hx
    have hpre : {t | c t ∈ R} ∈ 𝓝 (0 : ℝ) := hcc.continuousAt.eventually hnhds
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hpre
    have ht : -ε / 2 < 0 := by linarith
    apply hout (-ε / 2) ht
    apply hb
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg ht]
    linarith
  have hi : interior R = {z | ∀ i, L i z < 0} := by
    apply Subset.antisymm
    · intro x hx i
      have hle : L i x ≤ 0 := interior_subset hx i
      exact lt_of_le_of_ne hle (fun h => hzero x i h hx)
    · apply interior_maximal
      · exact fun x hx i => (hx i).le
      · simp only [Set.ofPred_forall]
        exact isOpen_iInter_of_finite fun i => isOpen_lt (hLc i) continuous_const
  refine ⟨hi, ?_⟩
  ext x
  rw [frontier, hclosed.closure_eq, hi]
  change (x ∈ R ∧ ¬ ∀ i, L i x < 0) ↔ (x ∈ R ∧ ∃ i, L i x = 0)
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨i, hi⟩ := not_forall.mp hn
    exact ⟨hx, i, le_antisymm (hx i) (le_of_not_gt hi)⟩
  · rintro ⟨hx, i, hi⟩
    exact ⟨hx, fun h => (ne_of_lt (h i)) hi⟩

end D5.S3.Geometry.HyperbolicSupportBoundary
