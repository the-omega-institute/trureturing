/- GID: D5/S3/Geometry/Hyperideal/SameBodyInwardGerms
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SameBodyInwardGerms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse, mathlib/module/Mathlib.Topology.Separation.Hausdorff]
   utility: none
   digest: Same-image eight-halfspace recovery, native face traces and twelve inward truncation ridge germs with genuine normal sections. -/

import D5.S3.Geometry.Hyperideal.ActualRaysJointAngle
import D5.S3.Geometry.HyperbolicPlaneRealization
import D5.S3.Geometry.Hyperideal.FourCycleCurvature

noncomputable section
open scoped BigOperators Matrix Topology
open Filter
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace D5.S3.Geometry.Hyperideal.SameBodyInwardGerms

set_option autoImplicit false

def capRow (l : Fin 6 → ℝ) (x : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ j, lengthGram l i j * x j

def originalMidpoint (l : Fin 6 → ℝ) (i j : Fin 4) : Fin 4 → ℝ :=
  (1 / 2 : ℝ) • endpoint l i j + (1 / 2 : ℝ) • endpoint l j i

def truncationMidpoint (l : Fin 6 → ℝ) (i k j h : Fin 4) : Fin 4 → ℝ :=
  (1 / 2 : ℝ) • endpoint l i j + (1 / 2 : ℝ) • endpoint l i h

def complementQuad (i k j h : Fin 4) : Prop :=
  i ≠ k ∧ i ≠ j ∧ i ≠ h ∧ k ≠ j ∧ k ≠ h ∧ j ≠ h

private theorem complementQuad_exists {i k : Fin 4} (hik : i ≠ k) :
    ∃ j h, complementQuad i k j h := by
  fin_cases i <;> fin_cases k <;> simp_all [complementQuad] <;> decide

private lemma capRow_add (l : Fin 6 → ℝ) (x y : Fin 4 → ℝ) (i : Fin 4) :
    capRow l (x + y) i = capRow l x i + capRow l y i := by
  simp [capRow, Finset.sum_add_distrib, mul_add]

private lemma capRow_smul (l : Fin 6 → ℝ) (a : ℝ) (x : Fin 4 → ℝ) (i : Fin 4) :
    capRow l (a • x) i = a * capRow l x i := by
  simp only [capRow, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ j, lengthGram l i j * (a * x j)) =
        ∑ j, a * (lengthGram l i j * x j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = a * ∑ j, lengthGram l i j * x j := by
      rw [Finset.mul_sum]

private lemma capRow_originalMidpoint (l : Fin 6 → ℝ) (i j r : Fin 4) :
    capRow l (originalMidpoint l i j) r =
      (1 / 2 : ℝ) * capRow l (endpoint l i j) r +
        (1 / 2 : ℝ) * capRow l (endpoint l j i) r := by
  simp only [originalMidpoint, capRow_add, capRow_smul]

private lemma capRow_truncationMidpoint (l : Fin 6 → ℝ) (i k j h r : Fin 4) :
    capRow l (truncationMidpoint l i k j h) r =
      (1 / 2 : ℝ) * capRow l (endpoint l i j) r +
        (1 / 2 : ℝ) * capRow l (endpoint l i h) r := by
  simp only [truncationMidpoint, capRow_add, capRow_smul]

private lemma convex_cutBody (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) :
    Convex ℝ (cutBody l) := by
  rw [← (cut_body_polytope l hl).2.1]
  exact convex_convexHull ℝ _

private lemma originalMidpoint_mem (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    {i j : Fin 4} (hij : i ≠ j) : originalMidpoint l i j ∈ cutBody l := by
  have hconv := convex_cutBody l hl
  have hi := (cut_body_polytope l hl).2.2.2 i j hij |>.1
  have hj := (cut_body_polytope l hl).2.2.2 j i hij.symm |>.1
  exact hconv hi hj (by norm_num) (by norm_num) (by norm_num)

private lemma truncationMidpoint_mem (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    {i k j h : Fin 4} (hq : complementQuad i k j h) :
    truncationMidpoint l i k j h ∈ cutBody l := by
  have hconv := convex_cutBody l hl
  have hij : i ≠ j := hq.2.1
  have hih : i ≠ h := hq.2.2.1
  have hi := (cut_body_polytope l hl).2.2.2 i j hij |>.1
  have hh := (cut_body_polytope l hl).2.2.2 i h hih |>.1
  exact hconv hi hh (by norm_num) (by norm_num) (by norm_num)

/-- The midpoint of an original edge has precisely the two side supports
    complementary to that edge; every cap inequality is strict. -/
private theorem original_midpoint_supports (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    {i j : Fin 4} (hij : i ≠ j) :
    let x := originalMidpoint l i j
    x ∈ cutBody l ∧
      0 < x i ∧ 0 < x j ∧
      (∀ k, k ≠ i → k ≠ j → x k = 0) ∧
      (∀ r, capRow l x r < 0) := by
  dsimp
  have hmem := originalMidpoint_mem l hl hij
  have he := (cut_body_polytope l hl).2.2.2 i j hij
  have he' := (cut_body_polytope l hl).2.2.2 j i hij.symm
  rcases he with ⟨hei, hxi, hxj, hzero, hcap, hstrict⟩
  rcases he' with ⟨hej, hyj, hyi, hzero', hcap', hstrict'⟩
  refine ⟨hmem, ?_, ?_, ?_, ?_⟩
  · change 0 < (1 / 2 : ℝ) * endpoint l i j i + (1 / 2 : ℝ) * endpoint l j i i
    rw [show endpoint l i j i = endpoint l i j i by rfl]
    have : 0 < endpoint l j i i := hyi
    positivity
  · change 0 < (1 / 2 : ℝ) * endpoint l i j j + (1 / 2 : ℝ) * endpoint l j i j
    have : 0 < endpoint l i j j := hxj
    positivity
  · intro k hki hkj
    change (1 / 2 : ℝ) * endpoint l i j k + (1 / 2 : ℝ) * endpoint l j i k = 0
    rw [hzero k hki hkj, hzero' k hkj hki]
    ring
  · intro r
    rw [capRow_originalMidpoint]
    by_cases hri : r = i
    · subst r
      have hs : capRow l (endpoint l j i) i < 0 := by
        simpa [capRow] using hstrict' i hij
      rw [show capRow l (endpoint l i j) i = 0 by simpa [capRow] using hcap]
      linarith
    by_cases hrj : r = j
    · subst r
      have hs : capRow l (endpoint l i j) j < 0 := by
        simpa [capRow] using hstrict j hij.symm
      rw [show capRow l (endpoint l j i) j = 0 by simpa [capRow] using hcap']
      linarith
    have hs₁ : capRow l (endpoint l i j) r < 0 := by
      simpa [capRow] using hstrict r hri
    have hs₂ : capRow l (endpoint l j i) r < 0 := by
      simpa [capRow] using hstrict' r hrj
    linarith

/-- The midpoint of an ordered cap-i/side-k ridge has exactly cap i and side
    k active, while all other cap rows and side coordinates are strict. -/
private theorem truncation_midpoint_supports (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    {i k j h : Fin 4} (hq : complementQuad i k j h) :
    let x := truncationMidpoint l i k j h
    x ∈ cutBody l ∧
      capRow l x i = 0 ∧ x k = 0 ∧
      (∀ r, r ≠ i → capRow l x r < 0) ∧
      0 < x i ∧ 0 < x j ∧ 0 < x h := by
  dsimp
  have hmem := truncationMidpoint_mem l hl hq
  have hij : i ≠ j := hq.2.1
  have hih : i ≠ h := hq.2.2.1
  have hkj : k ≠ j := hq.2.2.2.1
  have hkh : k ≠ h := hq.2.2.2.2.1
  have he := (cut_body_polytope l hl).2.2.2 i j hij
  have he' := (cut_body_polytope l hl).2.2.2 i h hih
  rcases he with ⟨hei, hxi, hxj, hzj, hcap, hstrict⟩
  rcases he' with ⟨heh, hyi, hyh, hzh, hcap', hstrict'⟩
  refine ⟨hmem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [capRow_truncationMidpoint,
      show capRow l (endpoint l i j) i = 0 by simpa [capRow] using hcap,
      show capRow l (endpoint l i h) i = 0 by simpa [capRow] using hcap']; ring
  · change (1 / 2 : ℝ) * endpoint l i j k + (1 / 2 : ℝ) * endpoint l i h k = 0
    rw [hzj k hq.1.symm hkj, hzh k hq.1.symm hkh]
    ring
  · intro r hri
    rw [capRow_truncationMidpoint]
    have hs₁ : capRow l (endpoint l i j) r < 0 := by
      simpa [capRow] using hstrict r hri
    have hs₂ : capRow l (endpoint l i h) r < 0 := by
      simpa [capRow] using hstrict' r hri
    linarith
  · change 0 < (1 / 2 : ℝ) * endpoint l i j i + (1 / 2 : ℝ) * endpoint l i h i
    positivity
  · change 0 < (1 / 2 : ℝ) * endpoint l i j j + (1 / 2 : ℝ) * endpoint l i h j
    have hs₁ : 0 < endpoint l i j j := hxj
    have hs₂ : endpoint l i h j = 0 := hzh j hij.symm hq.2.2.2.2.2
    rw [hs₂]
    positivity
  · change 0 < (1 / 2 : ℝ) * endpoint l i j h + (1 / 2 : ℝ) * endpoint l i h h
    have hs₁ : endpoint l i j h = 0 := hzj h hih.symm hq.2.2.2.2.2.symm
    rw [hs₁]
    positivity

/- The side normals are the negative Lorentz duals of the SAME row frame.
   No new body or normalization is introduced. -/
def sideNormal (m : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : Fin 4 → ℝ :=
  fun k => -(![(1 : ℝ),1,1,-1] k) * m⁻¹ k i

def recovered (m : Matrix (Fin 4) (Fin 4) ℝ) (p : HyperbolicThreeSpace) : Fin 4 → ℝ :=
  lift p ᵥ* m⁻¹

private lemma side_pair (m : Matrix (Fin 4) (Fin 4) ℝ) (W : Fin 4 → ℝ) (i : Fin 4) :
    lorentz W (sideNormal m i) = -(W ᵥ* m⁻¹) i := by
  simp [lorentz, sideNormal, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

private lemma lorentz_vec (m : Matrix (Fin 4) (Fin 4) ℝ) (b W : Fin 4 → ℝ) :
    lorentz (b ᵥ* m) W = ∑ i, b i * lorentz (m i) W := by
  simp [lorentz, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

private lemma gram_symm (l : Fin 6 → ℝ) (i j : Fin 4) :
    lengthGram l i j = lengthGram l j i := by
  fin_cases i <;> fin_cases j <;> rfl

private lemma frame_cap (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ∀ i j, lorentz (m i) (m j) = lengthGram l i j)
    (b : Fin 4 → ℝ) (i : Fin 4) :
    lorentz (b ᵥ* m) (m i) = capRow l b i := by
  rw [lorentz_vec]
  simp_rw [hg, gram_symm l _ i]
  simp [capRow, mul_comm]

private lemma frame_quad (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ∀ i j, lorentz (m i) (m j) = lengthGram l i j) (b : Fin 4 → ℝ) :
    lorentz (b ᵥ* m) (b ᵥ* m) = gramQuadratic l b := by
  rw [lorentz_vec]
  simp_rw [lorentz_symm (m _) (b ᵥ* m), frame_cap l m hg]
  rfl

private lemma recover_frame (m : Matrix (Fin 4) (Fin 4) ℝ) (hm : m.det ≠ 0)
    (p : HyperbolicThreeSpace) : recovered m p ᵥ* m = lift p := by
  simp [recovered, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hm)]

private lemma realized_lift (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* m ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3 - y 2)) (y 1 / (y 3 - y 2)), 1 / (y 3 - y 2)))
    (v : cutBody l) : lift (f v) = radial l v.val ᵥ* m := by
  obtain ⟨y, hy, hu, ht, hc⟩ := hf v
  exact (lift_of_coordinates _ _ hu ht hc).trans hy

private lemma recovered_realized (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (hm : m.det ≠ 0) (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* m ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3 - y 2)) (y 1 / (y 3 - y 2)), 1 / (y 3 - y 2)))
    (v : cutBody l) : recovered m (f v) = radial l v.val := by
  simp [recovered, realized_lift l m f hf v, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hm)]

private lemma capRow_div (l : Fin 6 → ℝ) (b : Fin 4 → ℝ) (a : ℝ) (i : Fin 4) :
    capRow l (fun k => b k / a) i = capRow l b i / a := by
  simp [capRow, mul_div_assoc, Finset.sum_div]

private lemma quad_div (l : Fin 6 → ℝ) (b : Fin 4 → ℝ) (a : ℝ) :
    gramQuadratic l (fun k => b k / a) = gramQuadratic l b / a^2 := by
  simp [gramQuadratic, Fin.sum_univ_succ, div_eq_mul_inv, mul_pow]
  ring

private lemma recover_point (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (m : Matrix (Fin 4) (Fin 4) ℝ) (hm : m.det ≠ 0)
    (hg : ∀ i j, lorentz (m i) (m j) = lengthGram l i j)
    (p : HyperbolicThreeSpace)
    (hs : ∀ i, lorentz (lift p) (sideNormal m i) ≤ 0)
    (hc : ∀ i, lorentz (lift p) (m i) ≤ 0) :
    ∃ x : cutBody l,
      x.val = (fun i => recovered m p i / ∑ j, recovered m p j) ∧
      radial l x.val = recovered m p := by
  let b := recovered m p
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    have := hs i
    rw [side_pair] at this
    exact neg_nonpos.mp this
  have hq : gramQuadratic l b = -1 := by
    rw [← frame_quad l m hg, recover_frame m hm, lift_unit]
  have hb0 : b ≠ 0 := by
    intro hz
    simp [hz, gramQuadratic] at hq
  have hsum : 0 < ∑ j, b j := by
    have hn : 0 ≤ ∑ j, b j := Finset.sum_nonneg fun i _ => hb i
    apply lt_of_le_of_ne hn
    intro heq
    have hz : ∀ i, b i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).mp heq.symm i (Finset.mem_univ i)
    exact hb0 (funext hz)
  let x : Fin 4 → ℝ := fun i => b i / ∑ j, b j
  have hx : x ∈ cutBody l := by
    refine ⟨⟨fun i => div_nonneg (hb i) hsum.le, ?_⟩, ?_⟩
    · simp [x, ← Finset.sum_div, hsum.ne']
    · intro i
      have hi : capRow l b i ≤ 0 := by
        rw [← frame_cap l m hg, recover_frame m hm]
        exact hc i
      change capRow l x i ≤ 0
      rw [show x = (fun k => b k / ∑ j, b j) by rfl, capRow_div]
      exact div_nonpos_of_nonpos_of_nonneg hi hsum.le
  have hqx : gramQuadratic l x = -1 / (∑ j, b j)^2 := by
    dsimp [x]
    rw [quad_div, hq]
  have hroot : Real.sqrt (-gramQuadratic l x) = 1 / ∑ j, b j := by
    have hnx : 0 < -gramQuadratic l x :=
      neg_pos.mpr ((shared_radial_body l hl).2.2.2.1 x hx)
    have he : (Real.sqrt (-gramQuadratic l x) * (∑ j, b j))^2 = 1 := by
      rw [mul_pow, Real.sq_sqrt hnx.le, hqx]
      field_simp
    have hp := mul_pos (Real.sqrt_pos.mpr hnx) hsum
    have heq : Real.sqrt (-gramQuadratic l x) * (∑ j, b j) = 1 := by nlinarith
    exact (eq_div_iff hsum.ne').mpr heq
  refine ⟨⟨x, hx⟩, rfl, ?_⟩
  ext i
  simp [radial, x, hroot, hsum.ne', b]

/-- Exact reconstruction in the image of the fixed original realization,
    using all four outward side and all four outward cap inequalities. -/
theorem same_body_halfspaces (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (m : Matrix (Fin 4) (Fin 4) ℝ) (hm : m.det ≠ 0)
    (hg : ∀ i j, lorentz (m i) (m j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* m ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3 - y 2)) (y 1 / (y 3 - y 2)), 1 / (y 3 - y 2))) :
    range f = {p | (∀ i, lorentz (lift p) (sideNormal m i) ≤ 0) ∧
      (∀ i, lorentz (lift p) (m i) ≤ 0)} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    have hr : 0 < Real.sqrt (-gramQuadratic l x.val) :=
      Real.sqrt_pos.mpr (neg_pos.mpr ((shared_radial_body l hl).2.2.2.1 x.val x.property))
    constructor
    · intro i
      rw [side_pair]
      change -recovered m (f x) i ≤ 0
      rw [recovered_realized l m hm f hf]
      exact neg_nonpos.mpr (div_nonneg (x.property.1.1 i) hr.le)
    · intro i
      rw [realized_lift l m f hf, frame_cap l m hg]
      exact (capRow_div l x.val _ i) ▸
        div_nonpos_of_nonpos_of_nonneg (x.property.2 i) hr.le
  · intro hp
    obtain ⟨x, hx, hr⟩ := recover_point l hl m hm hg p hp.1 hp.2
    refine ⟨x, ?_⟩
    apply lift_injective
    rw [realized_lift l m f hf, hr, recover_frame m hm]

private lemma diagonal_gram (l : Fin 6 → ℝ) (i : Fin 4) : lengthGram l i i = 1 := by
  fin_cases i <;> rfl

private lemma side_duality (m : Matrix (Fin 4) (Fin 4) ℝ) (hm : m.det ≠ 0)
    (i j : Fin 4) : lorentz (m j) (sideNormal m i) = -((1 : Matrix (Fin 4) (Fin 4) ℝ) j i) := by
  rw [side_pair]
  change -(m * m⁻¹) j i = _
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hm)]

set_option maxHeartbeats 800000 in
-- The spatial Cauchy-Schwarz reduction uses nonlinear polynomial elimination.
private lemma orthogonal_positive (Y W : Fin 4 → ℝ)
    (hY : lorentz Y Y = -1) (horth : lorentz Y W = 0) (hW : W ≠ 0) :
    0 < lorentz W W := by
  by_contra h
  have hn : lorentz W W ≤ 0 := le_of_not_gt h
  have hcs : (Y 0 * W 0 + Y 1 * W 1 + Y 2 * W 2)^2 ≤
      (Y 0^2 + Y 1^2 + Y 2^2) * (W 0^2 + W 1^2 + W 2^2) := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin 3 => Y i.castSucc) (fun i : Fin 3 => W i.castSucc))
  simp [lorentz, Fin.sum_univ_succ] at hY horth hn ⊢
  have ha : 0 ≤ Y 0^2 + Y 1^2 + Y 2^2 := by positivity
  have hb : 0 ≤ W 0^2 + W 1^2 + W 2^2 := by positivity
  have hle : (Y 0^2 + Y 1^2 + Y 2^2) * (W 0^2 + W 1^2 + W 2^2) ≤
      (Y 0^2 + Y 1^2 + Y 2^2) * (W 3^2) :=
    mul_le_mul_of_nonneg_left (by nlinarith [hn]) ha
  have he : Y 0 * W 0 + Y 1 * W 1 + Y 2 * W 2 = Y 3 * W 3 := by linarith
  have heq : Y 0^2 + Y 1^2 + Y 2^2 = Y 3^2 - 1 := by nlinarith
  rw [he] at hcs
  rw [heq] at hle
  have ht : W 3 = 0 := by nlinarith [sq_nonneg (W 3)]
  have h0 : W 0 = 0 := by nlinarith [sq_nonneg (W 1), sq_nonneg (W 2)]
  have h1 : W 1 = 0 := by nlinarith [sq_nonneg (W 0), sq_nonneg (W 2)]
  have h2 : W 2 = 0 := by nlinarith [sq_nonneg (W 0), sq_nonneg (W 1)]
  apply hW
  ext i
  fin_cases i <;> simp [ht, h0, h1, h2]

/-- The exact frozen radial realization data, with all six source conditions.
    This records witnesses; image recovery and all germ conclusions are proved. -/
structure OriginalModel (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace) : Prop where
  positive : ∀ q, 0 < l q
  strictCosines : ∀ q,
    -1 < FourCycleEnvelopes.cosine
      (Real.cosh (l (FourCycleCurvature.frame q 0)))
      (Real.cosh (l (FourCycleCurvature.frame q 1)))
      (Real.cosh (l (FourCycleCurvature.frame q 2)))
      (Real.cosh (l (FourCycleCurvature.frame q 3)))
      (Real.cosh (l (FourCycleCurvature.frame q 4)))
      (Real.cosh (l (FourCycleCurvature.frame q 5))) ∧
    FourCycleEnvelopes.cosine
      (Real.cosh (l (FourCycleCurvature.frame q 0)))
      (Real.cosh (l (FourCycleCurvature.frame q 1)))
      (Real.cosh (l (FourCycleCurvature.frame q 2)))
      (Real.cosh (l (FourCycleCurvature.frame q 3)))
      (Real.cosh (l (FourCycleCurvature.frame q 4)))
      (Real.cosh (l (FourCycleCurvature.frame q 5))) < 1
  gram : ∀ i j, lorentz (m i) (m j) = lengthGram l i j
  det_pos : 0 < m.det
  continuous : Continuous f
  injective : Function.Injective f
  coordinates : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* m ∧
    lorentz y y = -1 ∧ 0 < y 3 ∧
    (f v).coordinates.val = WithLp.toLp 2
      (Complex.mk (y 0 / (y 3 - y 2)) (y 1 / (y 3 - y 2)), 1 / (y 3 - y 2))

private lemma realized_sides (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace) (H : OriginalModel l m f)
    (x : cutBody l) (i : Fin 4) :
    lorentz (lift (f x)) (sideNormal m i) = -x.val i / Real.sqrt (-gramQuadratic l x.val) := by
  rw [side_pair]
  change -recovered m (f x) i = _
  rw [recovered_realized l m H.det_pos.ne' f H.coordinates]
  simp [radial, neg_div]

private lemma realized_caps (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace) (H : OriginalModel l m f)
    (x : cutBody l) (i : Fin 4) :
    lorentz (lift (f x)) (m i) = capRow l x.val i / Real.sqrt (-gramQuadratic l x.val) := by
  rw [realized_lift l m f H.coordinates, frame_cap l m H.gram]
  exact capRow_div l x.val _ i

private lemma side_positive (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace) (H : OriginalModel l m f) (k : Fin 4) :
    0 < lorentz (sideNormal m k) (sideNormal m k) := by
  classical
  obtain ⟨i, hi⟩ := exists_ne k
  obtain ⟨j, h, hq⟩ := complementQuad_exists hi
  let x : cutBody l := ⟨originalMidpoint l i j, originalMidpoint_mem l H.positive hq.2.1⟩
  have hs := original_midpoint_supports l H.positive hq.2.1
  apply orthogonal_positive (lift (f x)) _ (lift_unit _)
  · rw [realized_sides l m f H, show x.val k = 0 from hs.2.2.2.1 k hq.1.symm hq.2.2.2.1]
    simp
  · intro hz
    have hd := side_duality m H.det_pos.ne' k k
    rw [hz] at hd
    simp [lorentz] at hd

/-- All eight full native planes and their exact traces in this same f-image. -/
theorem same_body_face_planes (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace) (H : OriginalModel l m f) :
    ∃ es ec : Fin 4 → UpperHalfPlane → HyperbolicThreeSpace,
      (∀ i, Isometry (es i) ∧ range (es i) = {p | lorentz (lift p) (sideNormal m i) = 0} ∧
        f '' {x | x.val i = 0} = range f ∩ range (es i)) ∧
      (∀ i, Isometry (ec i) ∧ range (ec i) = {p | lorentz (lift p) (m i) = 0} ∧
        f '' {x | capRow l x.val i = 0} = range f ∩ range (ec i)) := by
  classical
  have hs (i : Fin 4) := HyperbolicPlaneRealization.supporting_plane_isometry
    (sideNormal m i) (side_positive l m f H i)
  have hc (i : Fin 4) := HyperbolicPlaneRealization.supporting_plane_isometry
    (m i) (by rw [H.gram, diagonal_gram]; norm_num)
  choose es hes hps using hs
  choose ec hec hpc using hc
  refine ⟨es, ec, ?_, ?_⟩
  · intro i
    refine ⟨hes i, hps i, ?_⟩
    rw [hps]
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_range_self x, by
        change lorentz (lift (f x)) (sideNormal m i) = 0
        rw [realized_sides l m f H, show x.val i = 0 from hx]; simp⟩
    · rintro ⟨⟨x, rfl⟩, hp⟩
      refine ⟨x, ?_, rfl⟩
      change lorentz (lift (f x)) (sideNormal m i) = 0 at hp
      rw [realized_sides l m f H] at hp
      have hr := Real.sqrt_pos.mpr (neg_pos.mpr ((shared_radial_body l H.positive).2.2.2.1 x.val x.property))
      exact neg_eq_zero.mp ((div_eq_zero_iff.mp hp).resolve_right hr.ne')
  · intro i
    refine ⟨hec i, hpc i, ?_⟩
    rw [hpc]
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_range_self x, by
        change lorentz (lift (f x)) (m i) = 0
        rw [realized_caps l m f H, show capRow l x.val i = 0 from hx]; simp⟩
    · rintro ⟨⟨x, rfl⟩, hp⟩
      refine ⟨x, ?_, rfl⟩
      change lorentz (lift (f x)) (m i) = 0 at hp
      rw [realized_caps l m f H] at hp
      have hr := Real.sqrt_pos.mpr (neg_pos.mpr ((shared_radial_body l H.positive).2.2.2.1 x.val x.property))
      exact (div_eq_zero_iff.mp hp).resolve_right hr.ne'

private lemma lorentz_scale (X W : Fin 4 → ℝ) (a b : ℝ) :
    lorentz (a • X) (b • W) = a * b * lorentz X W := by
  simpa using lorentz_linear X X W W a 0 b 0

private lemma lorentz_ray (Y U N : Fin 4 → ℝ) (t : ℝ) :
    lorentz (Real.cosh t • Y + Real.sinh t • U) N =
      Real.cosh t * lorentz Y N + Real.sinh t * lorentz U N := by
  simpa using lorentz_linear Y U N N (Real.cosh t) (Real.sinh t) 1 0

private lemma lorentz_ray_continuous (Y U N : Fin 4 → ℝ) :
    Continuous (fun t : ℝ => lorentz (Real.cosh t • Y + Real.sinh t • U) N) := by
  simp_rw [lorentz_ray]
  fun_prop

private lemma germ_preimages (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace) (H : OriginalModel l m f)
    (g : ℝ → HyperbolicThreeSpace) (hg : Isometry g) (ε : ℝ)
    (hs : ∀ t ∈ Ico (0 : ℝ) ε, ∀ i, lorentz (lift (g t)) (sideNormal m i) ≤ 0)
    (hc : ∀ t ∈ Ico (0 : ℝ) ε, ∀ i, lorentz (lift (g t)) (m i) ≤ 0) :
    ∃ v : Ico (0 : ℝ) ε → cutBody l, Continuous v ∧ ∀ t, f (v t) = g t := by
  letI : CompactSpace (cutBody l) := isCompact_iff_compactSpace.mp
    (shared_radial_body l H.positive).1
  let e := (H.continuous.isClosedEmbedding H.injective).isEmbedding.toHomeomorph
  have him (t : Ico (0 : ℝ) ε) : g t ∈ range f := by
    rw [same_body_halfspaces l H.positive m H.det_pos.ne' H.gram f H.coordinates]
    exact ⟨hs t t.property, hc t t.property⟩
  let w : Ico (0 : ℝ) ε → range f := fun t => ⟨g t, him t⟩
  refine ⟨fun t => e.symm (w t), ?_, ?_⟩
  · exact e.symm.continuous.comp ((hg.continuous.comp continuous_subtype_val).subtype_mk _)
  · intro t
    have he := e.apply_symm_apply (w t)
    exact congrArg Subtype.val he

set_option maxHeartbeats 800000 in
-- This construction retains the support, inverse, plane and metric witnesses together.
/-- Two actual global face rays, their positive original-body preimages and
    their unrestricted native comparison-angle limit at an ordered cap/side ridge. -/
theorem truncation_inward_germs (l : Fin 6 → ℝ) (m : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace) (H : OriginalModel l m f)
    {i k : Fin 4} (hik : i ≠ k) :
    ∃ j h : Fin 4, ∃ hq : complementQuad i k j h,
    let x : cutBody l := ⟨truncationMidpoint l i k j h, truncationMidpoint_mem l H.positive hq⟩
    ∃ ε : ℝ, 0 < ε ∧ ∃ gc gs : ℝ → HyperbolicThreeSpace,
      Isometry gc ∧ Isometry gs ∧ gc 0 = f x ∧ gs 0 = f x ∧
      (∀ t, lift (gc t) = Real.cosh t • lift (f x) +
        Real.sinh t • ((-1 / Real.sqrt (lorentz (sideNormal m k) (sideNormal m k))) • sideNormal m k)) ∧
      (∀ t, lift (gs t) = Real.cosh t • lift (f x) + Real.sinh t • ((-1 : ℝ) • m i)) ∧
      (∃ vc vs : Ico (0 : ℝ) ε → cutBody l,
        Continuous vc ∧ Continuous vs ∧
        (∀ t, f (vc t) = gc t ∧ f (vs t) = gs t ∧
          capRow l (vc t).val i = 0 ∧ (vs t).val k = 0) ∧
        (∀ t, 0 < t.val →
          0 < (vc t).val k ∧ capRow l (vs t).val i < 0 ∧
          (∀ r, r ≠ k → 0 < (vc t).val r ∧ 0 < (vs t).val r) ∧
          (∀ r, r ≠ i → capRow l (vc t).val r < 0 ∧ capRow l (vs t).val r < 0))) ∧
      (∃ es ec : UpperHalfPlane → HyperbolicThreeSpace,
        Isometry es ∧ Isometry ec ∧
        range es = {p | lorentz (lift p) (sideNormal m k) = 0} ∧
        range ec = {p | lorentz (lift p) (m i) = 0} ∧
        f '' {v | v.val k = 0} = range f ∩ range es ∧
        f '' {v | capRow l v.val i = 0} = range f ∩ range ec ∧
        (∀ t ∈ Ico (0 : ℝ) ε, gc t ∈ range ec ∧ gs t ∈ range es)) ∧
      (∃ T : Fin 4 → ℝ, ∃ en : UpperHalfPlane → HyperbolicThreeSpace,
        ∃ gr : ℝ → HyperbolicThreeSpace,
        let z : cutBody l := ⟨endpoint l i j, (cut_body_polytope l H.positive).2.2.2 i j hq.2.1 |>.1⟩
        let D := dist (f x) (f z)
        0 < D ∧
        T = (1 / Real.sinh D) • lift (f z) + (-Real.cosh D / Real.sinh D) • lift (f x) ∧
        lorentz T T = 1 ∧ lorentz (lift (f x)) T = 0 ∧
        lorentz T (sideNormal m k) = 0 ∧ lorentz T (m i) = 0 ∧
        Isometry en ∧ range en = {p | lorentz (lift p) T = 0} ∧
        (∀ t, gc t ∈ range en ∧ gs t ∈ range en) ∧
        Isometry gr ∧ gr 0 = f x ∧ gr D = f z ∧
        (∀ t, lift (gr t) = Real.cosh t • lift (f x) + Real.sinh t • T) ∧
        (∀ t ∈ Icc (0 : ℝ) D, ∃ v : cutBody l,
          v.val ∈ segment ℝ x.val z.val ∧ f v = gr t)) ∧
      Tendsto (fun z : ℝ × ℝ => Real.arccos
        ((z.1^2 + z.2^2 - dist (gc z.1) (gs z.2)^2) / (2 * z.1 * z.2)))
        (𝓝[Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)] ((0 : ℝ), (0 : ℝ))) (𝓝 (Real.pi / 2)) := by
  classical
  obtain ⟨j, h, hq⟩ := complementQuad_exists hik
  refine ⟨j, h, hq, ?_⟩
  dsimp only
  let x : cutBody l := ⟨truncationMidpoint l i k j h, truncationMidpoint_mem l H.positive hq⟩
  let Y := lift (f x)
  let n := sideNormal m k
  let r := Real.sqrt (lorentz n n)
  let U := (-1 / r) • n
  let V := (-1 : ℝ) • m i
  have hn : 0 < lorentz n n := side_positive l m f H k
  have hr : 0 < r := Real.sqrt_pos.mpr hn
  have hr2 : r^2 = lorentz n n := Real.sq_sqrt hn.le
  have hU : lorentz U U = 1 := by
    rw [show U = (-1 / r) • n by rfl, lorentz_scale]
    field_simp
    nlinarith [hr2]
  have hV : lorentz V V = 1 := by
    rw [show V = (-1 : ℝ) • m i by rfl, lorentz_scale, H.gram, diagonal_gram]
    norm_num
  have hnk : lorentz n (m i) = 0 := by
    rw [lorentz_symm, side_duality m H.det_pos.ne']
    simp [hq.1]
  have hx := truncation_midpoint_supports l H.positive hq
  have hYi : lorentz Y (m i) = 0 := by
    rw [show Y = lift (f x) by rfl, realized_caps l m f H,
      show capRow l x.val i = 0 from hx.2.1]
    simp
  have hYk : lorentz Y n = 0 := by
    rw [show Y = lift (f x) by rfl, realized_sides l m f H,
      show x.val k = 0 from hx.2.2.1]
    simp
  have hYU : lorentz Y U = 0 := by
    rw [show U = (-1 / r) • n by rfl]
    simpa [hYk] using lorentz_scale Y n 1 (-1 / r)
  have hYV : lorentz Y V = 0 := by
    simpa [V, hYi] using lorentz_scale Y (m i) 1 (-1)
  have hUV : lorentz U V = 0 := by
    change lorentz ((-1 / r) • n) ((-1 : ℝ) • m i) = 0
    rw [lorentz_scale, hnk]
    ring
  have hUi : lorentz U (m i) = 0 := by
    simpa [U, hnk] using lorentz_scale n (m i) (-1 / r) 1
  have hVk : lorentz V n = 0 := by
    simpa [V, lorentz_symm (m i) n, hnk] using lorentz_scale (m i) n (-1) 1
  have hUk : lorentz U n < 0 := by
    rw [show U = (-1 / r) • n by rfl]
    have he : lorentz ((-1 / r) • n) n = (-1 / r) * lorentz n n := by
      simpa using lorentz_scale n n (-1 / r) 1
    rw [he]
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) hr) hn
  have hVi : lorentz V (m i) = -1 := by
    simpa [V, H.gram, diagonal_gram] using lorentz_scale (m i) (m i) (-1) 1
  obtain ⟨gc, gs, hgc, hgs, hgc0, hgs0, hlc, hls, hlaw, hb, hang⟩ :=
    ActualRaysJointAngle.actual_rays_joint_angle Y U V (lift_unit _) (lift_time _)
      hU hV hYU hYV (by rw [hUV]; norm_num)
  have hp : project Y (lift_unit _) (lift_time _) = f x := by
    apply lift_injective
    exact lift_of_coordinates _ _ (lift_unit _) (lift_time _) rfl
  rw [hp] at hgc0 hgs0
  have hbaseSide (a : Fin 4) (ha : a ≠ k) : lorentz Y (sideNormal m a) < 0 := by
    have hxa : 0 < x.val a := by
      have hall : a = i ∨ a = k ∨ a = j ∨ a = h := by
        rcases hq with ⟨h1, h2, h3, h4, h5, h6⟩
        omega
      rcases hall with hai | hak | haj | hah
      · subst a; exact hx.2.2.2.2.1
      · exact (ha hak).elim
      · subst a; exact hx.2.2.2.2.2.1
      · subst a; exact hx.2.2.2.2.2.2
    rw [show Y = lift (f x) by rfl, realized_sides l m f H]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hxa)
      (Real.sqrt_pos.mpr (neg_pos.mpr ((shared_radial_body l H.positive).2.2.2.1 x.val x.property)))
  have hbaseCap (a : Fin 4) (ha : a ≠ i) : lorentz Y (m a) < 0 := by
    rw [show Y = lift (f x) by rfl, realized_caps l m f H]
    exact div_neg_of_neg_of_pos (hx.2.2.2.1 a ha)
      (Real.sqrt_pos.mpr (neg_pos.mpr ((shared_radial_body l H.positive).2.2.2.1 x.val x.property)))
  have hevs : ∀ᶠ t : ℝ in 𝓝 0, ∀ a, a ≠ k →
      lorentz (lift (gc t)) (sideNormal m a) < 0 ∧
      lorentz (lift (gs t)) (sideNormal m a) < 0 := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases ha : a = k
    · exact Filter.Eventually.of_forall fun _ h => (h ha).elim
    · have hc : ∀ᶠ t : ℝ in 𝓝 0, lorentz (Real.cosh t • Y + Real.sinh t • U) (sideNormal m a) < 0 :=
        (lorentz_ray_continuous Y U (sideNormal m a)).continuousAt.eventually_lt
        continuousAt_const (by simpa using hbaseSide a ha)
      have hs : ∀ᶠ t : ℝ in 𝓝 0, lorentz (Real.cosh t • Y + Real.sinh t • V) (sideNormal m a) < 0 :=
        (lorentz_ray_continuous Y V (sideNormal m a)).continuousAt.eventually_lt
        continuousAt_const (by simpa using hbaseSide a ha)
      filter_upwards [hc, hs] with t hc hs hne
      simpa [hlc, hls] using And.intro hc hs
  have hevc : ∀ᶠ t : ℝ in 𝓝 0, ∀ a, a ≠ i →
      lorentz (lift (gc t)) (m a) < 0 ∧ lorentz (lift (gs t)) (m a) < 0 := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases ha : a = i
    · exact Filter.Eventually.of_forall fun _ h => (h ha).elim
    · have hc : ∀ᶠ t : ℝ in 𝓝 0, lorentz (Real.cosh t • Y + Real.sinh t • U) (m a) < 0 :=
        (lorentz_ray_continuous Y U (m a)).continuousAt.eventually_lt
        continuousAt_const (by simpa using hbaseCap a ha)
      have hs : ∀ᶠ t : ℝ in 𝓝 0, lorentz (Real.cosh t • Y + Real.sinh t • V) (m a) < 0 :=
        (lorentz_ray_continuous Y V (m a)).continuousAt.eventually_lt
        continuousAt_const (by simpa using hbaseCap a ha)
      filter_upwards [hc, hs] with t hc hs hne
      simpa [hlc, hls] using And.intro hc hs
  obtain ⟨ε, hε, hmarg⟩ := Metric.mem_nhds_iff.mp (hevs.and hevc)
  have hmarg' (t : ℝ) (ht : t ∈ Ico (0 : ℝ) ε) :=
    hmarg (show t ∈ Metric.ball (0 : ℝ) ε from by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg ht.1] using ht.2)
  have hcactive (t : ℝ) : lorentz (lift (gc t)) (m i) = 0 := by
    rw [hlc, lorentz_ray, hYi, hUi]; ring
  have hsactive (t : ℝ) : lorentz (lift (gs t)) n = 0 := by
    rw [hls, lorentz_ray, hYk, hVk]; ring
  have hccross (t : ℝ) (ht : 0 ≤ t) : lorentz (lift (gc t)) n ≤ 0 := by
    rw [hlc, lorentz_ray, hYk]
    simpa using mul_nonpos_of_nonneg_of_nonpos (Real.sinh_nonneg_iff.mpr ht) hUk.le
  have hscross (t : ℝ) (ht : 0 ≤ t) : lorentz (lift (gs t)) (m i) ≤ 0 := by
    rw [hls, lorentz_ray, hYi, hVi]
    simpa using neg_nonpos.mpr (Real.sinh_nonneg_iff.mpr ht)
  have hcs (t : ℝ) (ht : t ∈ Ico (0 : ℝ) ε) (a : Fin 4) :
      lorentz (lift (gc t)) (sideNormal m a) ≤ 0 := by
    by_cases ha : a = k
    · subst a; exact hccross t ht.1
    · exact ((hmarg' t ht).1 a ha).1.le
  have hss (t : ℝ) (ht : t ∈ Ico (0 : ℝ) ε) (a : Fin 4) :
      lorentz (lift (gs t)) (sideNormal m a) ≤ 0 := by
    by_cases ha : a = k
    · subst a; exact (hsactive t).le
    · exact ((hmarg' t ht).1 a ha).2.le
  have hcc (t : ℝ) (ht : t ∈ Ico (0 : ℝ) ε) (a : Fin 4) :
      lorentz (lift (gc t)) (m a) ≤ 0 := by
    by_cases ha : a = i
    · subst a; exact (hcactive t).le
    · exact ((hmarg' t ht).2 a ha).1.le
  have hsc (t : ℝ) (ht : t ∈ Ico (0 : ℝ) ε) (a : Fin 4) :
      lorentz (lift (gs t)) (m a) ≤ 0 := by
    by_cases ha : a = i
    · subst a; exact hscross t ht.1
    · exact ((hmarg' t ht).2 a ha).2.le
  obtain ⟨vc, hvc, hfc⟩ := germ_preimages l m f H gc hgc ε hcs hcc
  obtain ⟨vs, hvs, hfs⟩ := germ_preimages l m f H gs hgs ε hss hsc
  have hroot (v : cutBody l) : 0 < Real.sqrt (-gramQuadratic l v.val) :=
    Real.sqrt_pos.mpr (neg_pos.mpr ((shared_radial_body l H.positive).2.2.2.1 v.val v.property))
  have hvcCap (t : Ico (0 : ℝ) ε) : capRow l (vc t).val i = 0 := by
    have he := hcactive t
    rw [← hfc t, realized_caps l m f H] at he
    exact (div_eq_zero_iff.mp he).resolve_right (hroot _).ne'
  have hvsSide (t : Ico (0 : ℝ) ε) : (vs t).val k = 0 := by
    have he := hsactive t
    rw [← hfs t, realized_sides l m f H] at he
    exact neg_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right (hroot _).ne')
  obtain ⟨es, ec, hes, hec⟩ := same_body_face_planes l m f H
  let z : cutBody l := ⟨endpoint l i j, (cut_body_polytope l H.positive).2.2.2 i j hq.2.1 |>.1⟩
  let Z := lift (f z)
  let D := dist (f x) (f z)
  have hxz : f x ≠ f z := by
    intro he
    have hv := congrArg (fun v : cutBody l => v.val h) (H.injective he)
    have hz0 : z.val h = 0 :=
      ((cut_body_polytope l H.positive).2.2.2 i j hq.2.1).2.2.2.1 h hq.2.2.1.symm hq.2.2.2.2.2.symm
    rw [hz0] at hv
    have hxpos : 0 < x.val h := hx.2.2.2.2.2.2
    linarith
  have hD : 0 < D := dist_pos.mpr hxz
  have hd : Real.sinh D ≠ 0 := (Real.sinh_pos_iff.mpr hD).ne'
  let T := (1 / Real.sinh D) • Z + (-Real.cosh D / Real.sinh D) • Y
  have hYY : lorentz Y Y = -1 := lift_unit _
  have hZZ : lorentz Z Z = -1 := lift_unit _
  have hYZ : lorentz Y Z = -Real.cosh D := lift_cosh _ _
  have hZY : lorentz Z Y = -Real.cosh D := (lorentz_symm _ _).trans hYZ
  have hT : lorentz T T = 1 := by
    dsimp only [T]
    rw [lorentz_linear, hYY, hZZ, hYZ, hZY]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq D]
  have hYT : lorentz Y T = 0 := by
    dsimp only [T]
    rw [lorentz_right, hYZ, hYY]
    ring
  have hZi : lorentz Z (m i) = 0 := by
    rw [show Z = lift (f z) by rfl, realized_caps l m f H]
    have hz0 := ((cut_body_polytope l H.positive).2.2.2 i j hq.2.1).2.2.2.2.1
    change capRow l z.val i / _ = 0
    rw [show capRow l z.val i = 0 from hz0]
    simp
  have hZk : lorentz Z n = 0 := by
    rw [show Z = lift (f z) by rfl, realized_sides l m f H]
    have hz0 := ((cut_body_polytope l H.positive).2.2.2 i j hq.2.1).2.2.2.1 k hq.1.symm hq.2.2.2.1
    rw [show z.val k = 0 from hz0]
    simp
  have hTi : lorentz T (m i) = 0 := by
    have he := lorentz_linear Z Y (m i) (m i) (1 / Real.sinh D)
      (-Real.cosh D / Real.sinh D) 1 0
    simpa [T, hZi, hYi] using he
  have hTk : lorentz T n = 0 := by
    have he := lorentz_linear Z Y n n (1 / Real.sinh D)
      (-Real.cosh D / Real.sinh D) 1 0
    simpa [T, hZk, hYk] using he
  have hTU : lorentz T U = 0 := by
    simpa [U, hTk] using lorentz_scale T n 1 (-1 / r)
  have hTV : lorentz T V = 0 := by
    simpa [V, hTi] using lorentz_scale T (m i) 1 (-1)
  obtain ⟨gr, gu, hgr, hgu, hgr0, hgu0, hlr, hlu, _, _, _⟩ :=
    ActualRaysJointAngle.actual_rays_joint_angle Y T U hYY (lift_time _)
      hT hU hYT hYU (by rw [hTU]; norm_num)
  rw [hp] at hgr0
  have hgrD : gr D = f z := by
    apply lift_injective
    rw [hlr]
    change Real.cosh D • Y + Real.sinh D • T = Z
    ext a
    simp [T, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  obtain ⟨en, hen, hpn⟩ := HyperbolicPlaneRealization.supporting_plane_isometry T (by rw [hT]; norm_num)
  have hsection (t : ℝ) : gc t ∈ range en ∧ gs t ∈ range en := by
    rw [hpn]
    change lorentz (lift (gc t)) T = 0 ∧ lorentz (lift (gs t)) T = 0
    rw [hlc, hls, lorentz_ray, lorentz_ray, lorentz_symm Y T,
      lorentz_symm U T, lorentz_symm V T, lorentz_symm T Y, hYT, hTU, hTV]
    constructor <;> ring
  obtain ⟨gseg, hgseg, hgseg0, hgseg1, himseg, hbetseg⟩ :=
    same_body_metric_segments l H.positive m f H.injective H.coordinates x z
  have hgrseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
      ∃ v : cutBody l, v.val ∈ segment ℝ x.val z.val ∧ f v = gr t := by
    have hb : dist (f x) (gr t) + dist (gr t) (f z) = D := by
      rw [← hgr0, ← hgrD, hgr.dist_eq, hgr.dist_eq]
      simp [Real.dist_eq, abs_of_nonneg ht.1, abs_of_nonpos (sub_nonpos.mpr ht.2)]
    have hgmem : gr t ∈ range gseg := by
      rw [hbetseg]
      exact hb
    rw [himseg] at hgmem
    exact hgmem
  refine ⟨ε, hε, gc, gs, hgc, hgs, hgc0, hgs0, hlc, hls, ?_, ?_, ?_, ?_⟩
  · refine ⟨vc, vs, hvc, hvs, fun t => ⟨hfc t, hfs t, hvcCap t, hvsSide t⟩, ?_⟩
    intro t ht
    have hcneg : lorentz (lift (gc t)) n < 0 := by
      rw [hlc, lorentz_ray, hYk]
      simpa using mul_neg_of_pos_of_neg (Real.sinh_pos_iff.mpr ht) hUk
    have hsneg : lorentz (lift (gs t)) (m i) < 0 := by
      rw [hls, lorentz_ray, hYi, hVi]
      simpa using neg_neg_of_pos (Real.sinh_pos_iff.mpr ht)
    rw [← hfc t, realized_sides l m f H] at hcneg
    rw [← hfs t, realized_caps l m f H] at hsneg
    rw [div_lt_iff₀ (hroot _)] at hcneg hsneg
    refine ⟨by linarith, by simpa using hsneg, ?_, ?_⟩
    · intro a ha
      have hc := ((hmarg' t t.property).1 a ha).1
      have hs := ((hmarg' t t.property).1 a ha).2
      rw [← hfc t, realized_sides l m f H] at hc
      rw [← hfs t, realized_sides l m f H] at hs
      rw [div_lt_iff₀ (hroot _)] at hc hs
      exact ⟨by linarith, by linarith⟩
    · intro a ha
      have hc := ((hmarg' t t.property).2 a ha).1
      have hs := ((hmarg' t t.property).2 a ha).2
      rw [← hfc t, realized_caps l m f H] at hc
      rw [← hfs t, realized_caps l m f H] at hs
      rw [div_lt_iff₀ (hroot _)] at hc hs
      simpa using And.intro hc hs
  · refine ⟨es k, ec i, (hes k).1, (hec i).1, (hes k).2.1, (hec i).2.1,
      (hes k).2.2, (hec i).2.2, ?_⟩
    intro t ht
    rw [(hec i).2.1, (hes k).2.1]
    exact ⟨hcactive t, hsactive t⟩
  · exact ⟨T, en, gr, hD, rfl, hT, hYT, hTk, hTi, hen, hpn, hsection, hgr, hgr0, hgrD, hlr, hgrseg⟩
  · simpa [hUV, Real.arccos_zero] using hang

end D5.S3.Geometry.Hyperideal.SameBodyInwardGerms
