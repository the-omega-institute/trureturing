/- GID: D5/S3/Geometry/Hyperideal/LengthGramActualHalfspaces
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramActualHalfspaces
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Maps.Basic]
   utility: none
   digest: The supplied radial image is an intersection of eight Lorentz halfspaces with unit outward normals and ambient facet patches. -/

import D5.S3.Geometry.Hyperideal.CapTraceHull
import D5.S3.Geometry.HyperbolicPlaneRealization
import D5.S3.Geometry.HyperbolicSupportBoundary
import Mathlib.Tactic

/-! Eight Lorentz halfspaces for a supplied length-Gram realization.

Gram-dual row normals and the supplied cap normals describe exactly the image
of the supplied radial map into hyperbolic three-space. Closed and strict sign
conditions describe its region, ambient interior and frontier. Explicit points
with one active support give native hyperbolic-plane facet patches and witnesses
that each halfspace is essential.

Side labels are the coefficient supports: `Sum.inl i` is `x i ≥ 0`, and
`Sum.inr i` is `(lengthGram l *ᵥ x) i ≤ 0`. The six edge indices are
01, 02, 03, 23, 13, 12.
-/

noncomputable section
open scoped BigOperators Matrix Topology
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.ActualRaysJointAngle
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicPlaneRealization

namespace D5.S3.Geometry.Hyperideal.LengthGramActualHalfspaces
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev V := Fin 4 → ℝ
abbrev Support := CapTraceHull.Support

/-- The Gram duals of the supplied rows, not a newly chosen frame. -/
def dual (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : V :=
  ((lengthGram l)⁻¹ i) ᵥ* M

def weight (l : Fin 6 → ℝ) : Support → ℝ
  | Sum.inl i => Real.sqrt ((lengthGram l)⁻¹ i i)
  | Sum.inr _ => 1

/-- All eight signs point outwards. The caps retain the supplied rows M_i. -/
def outward (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : Support → V
  | Sum.inl i => (-(weight l (Sum.inl i))⁻¹) • dual l M i
  | Sum.inr i => M i

def value (A : Support → V) (a : Support) (p : HyperbolicThreeSpace) : ℝ :=
  lorentz (lift p) (A a)

def region (A : Support → V) : Set HyperbolicThreeSpace :=
  {p | ∀ a, value A a p ≤ 0}

def strictRegion (A : Support → V) : Set HyperbolicThreeSpace :=
  {p | ∀ a, value A a p < 0}

private lemma gram_diag (l : Fin 6 → ℝ) (i : Fin 4) : lengthGram l i i = 1 := by
  fin_cases i <;> rfl

private lemma gram_symm (l : Fin 6 → ℝ) (i j : Fin 4) :
    lengthGram l i j = lengthGram l j i := by
  fin_cases i <;> fin_cases j <;> rfl

private lemma gram_off (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (i j : Fin 4) (hij : i ≠ j) : lengthGram l i j < -1 := by
  have hc (k : Fin 6) := Real.one_lt_cosh.mpr (ne_of_gt (hl k))
  fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | exact neg_lt_neg (hc 0)
    | exact neg_lt_neg (hc 1)
    | exact neg_lt_neg (hc 2)
    | exact neg_lt_neg (hc 3)
    | exact neg_lt_neg (hc 4)
    | exact neg_lt_neg (hc 5)

private def minorEdges : Fin 4 → Fin 3 → Fin 6 :=
  ![![5,4,3], ![1,2,3], ![0,2,4], ![0,1,5]]

private lemma cofactor_diagonal (l : Fin 6 → ℝ) (i : Fin 4) :
    (lengthGram l).adjugate i i =
      1 - Real.cosh (l (minorEdges i 0))^2 - Real.cosh (l (minorEdges i 1))^2 -
      Real.cosh (l (minorEdges i 2))^2 - 2 * Real.cosh (l (minorEdges i 0)) *
        Real.cosh (l (minorEdges i 1)) * Real.cosh (l (minorEdges i 2)) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;>
    norm_num [lengthGram, minorEdges, Matrix.det_fin_three,
      Matrix.submatrix_apply, Fin.succAbove] <;> ring

private lemma dual_diagonal_positive (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hG : (lengthGram l).det < 0) (i : Fin 4) : 0 < (lengthGram l)⁻¹ i i := by
  have hc (k : Fin 6) : 1 < Real.cosh (l k) :=
    Real.one_lt_cosh.mpr (ne_of_gt (hl k))
  have hminor : (lengthGram l).adjugate i i < 0 := by
    rw [cofactor_diagonal]
    have ha := hc (minorEdges i 0)
    have hb := hc (minorEdges i 1)
    have hd := hc (minorEdges i 2)
    have hp : 0 < 2 * Real.cosh (l (minorEdges i 0)) *
        Real.cosh (l (minorEdges i 1)) * Real.cosh (l (minorEdges i 2)) := by positivity
    nlinarith [sq_nonneg (Real.cosh (l (minorEdges i 0)) - 1),
      sq_nonneg (Real.cosh (l (minorEdges i 1)) - 1),
      sq_nonneg (Real.cosh (l (minorEdges i 2)) - 1)]
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr hG) hminor

private lemma weight_positive (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hG : (lengthGram l).det < 0) (a : Support) : 0 < weight l a := by
  cases a with
  | inl i => exact Real.sqrt_pos.mpr (dual_diagonal_positive l hl hG i)
  | inr i => exact zero_lt_one

private lemma frame_pair (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (x z : V) :
    lorentz (x ᵥ* M) (z ᵥ* M) = ∑ i, x i * ∑ j, lengthGram l i j * z j := by
  calc
    _ = ∑ i, ∑ j, x i * z j * lorentz (M i) (M j) := by
      simp [lorentz, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
      ring
    _ = _ := by
      simp only [hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private lemma frame_dual (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hG : (lengthGram l).det < 0) (x : V) (i : Fin 4) :
    lorentz (x ᵥ* M) (dual l M i) = x i := by
  have hunit : IsUnit (lengthGram l).det := isUnit_iff_ne_zero.mpr (ne_of_lt hG)
  calc
    _ = ∑ j, x j * ∑ k, lengthGram l j k * (lengthGram l)⁻¹ i k :=
      frame_pair l M hg x ((lengthGram l)⁻¹ i)
    _ = ∑ j, x j * ((lengthGram l)⁻¹ * lengthGram l) i j := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [gram_symm l j k, mul_comm]
    _ = x i := by
      rw [Matrix.nonsing_inv_mul _ hunit]
      simp [Matrix.one_apply, mul_ite, eq_comm]

private lemma frame_cap (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (x : V) (i : Fin 4) :
    lorentz (x ᵥ* M) (M i) = ∑ j, lengthGram l i j * x j := by
  have hs : (Pi.single i 1 : V) ᵥ* M = M i := by
    ext k
    simp [Matrix.vecMul, dotProduct, Pi.single_apply, ite_mul]
  rw [← hs, frame_pair l M hg]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro j _
  rw [gram_symm l j i, mul_comm]

private lemma frame_outward (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hG : (lengthGram l).det < 0) (x : V) (a : Support) :
    lorentz (x ᵥ* M) (outward l M a) = CapTraceHull.support l a x / weight l a := by
  cases a with
  | inl i =>
    have hs := lorentz_right (x ᵥ* M) (dual l M i) (dual l M i)
      (-(weight l (Sum.inl i))⁻¹) 0
    simp only [zero_smul, add_zero, zero_mul, add_zero] at hs
    rw [frame_dual l M hg hG] at hs
    simpa [outward, CapTraceHull.support, div_eq_mul_inv, mul_comm] using hs
  | inr i => simpa [outward, weight, CapTraceHull.support] using frame_cap l M hg x i

private lemma outward_unit (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hG : (lengthGram l).det < 0) (a : Support) :
    lorentz (outward l M a) (outward l M a) = 1 := by
  cases a with
  | inr i => exact (hg i i).trans (gram_diag l i)
  | inl i =>
    have hp := dual_diagonal_positive l hl hG i
    have hr := (weight_positive l hl hG (Sum.inl i)).ne'
    have hs : (weight l (Sum.inl i))^2 = (lengthGram l)⁻¹ i i := Real.sq_sqrt hp.le
    have hn : lorentz (dual l M i) (dual l M i) = (lengthGram l)⁻¹ i i :=
      frame_dual l M hg hG ((lengthGram l)⁻¹ i) i
    have hb := lorentz_linear (dual l M i) (dual l M i) (dual l M i) (dual l M i)
      (-(weight l (Sum.inl i))⁻¹) 0 (-(weight l (Sum.inl i))⁻¹) 0
    simp only [zero_smul, add_zero, zero_mul, mul_zero, zero_add] at hb
    change lorentz ((-(weight l (Sum.inl i))⁻¹) • dual l M i)
      ((-(weight l (Sum.inl i))⁻¹) • dual l M i) = 1
    rw [hb, hn, ← hs]
    field_simp [hr] <;> ring

private lemma gram_scale (l : Fin 6 → ℝ) (x : V) (c : ℝ) :
    gramQuadratic l (c • x) = c^2 * gramQuadratic l x := by
  simp [gramQuadratic, Fin.sum_univ_succ]
  ring

section Supplied
variable (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
  (f : cutBody l → HyperbolicThreeSpace)
  (hframe : ∀ v, ∃ y : V, y = (radial l v.val) ᵥ* M ∧
    lorentz y y = -1 ∧ 0 < y 3 ∧
    (f v).coordinates.val = WithLp.toLp 2
      (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))

include hframe

private lemma supplied_lift (v : cutBody l) : lift (f v) = (radial l v.val) ᵥ* M := by
  obtain ⟨y, hy, hu, ht, hc⟩ := hframe v
  exact (lift_of_coordinates _ _ hu ht hc).trans hy

private lemma image_value (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hG : (lengthGram l).det < 0) (v : cutBody l) (a : Support) :
    value (outward l M) a (f v) = CapTraceHull.support l a v.val /
      (Real.sqrt (-gramQuadratic l v.val) * weight l a) := by
  have hr : radial l v.val = (Real.sqrt (-gramQuadratic l v.val))⁻¹ • v.val := by
    ext i
    simp [radial, div_eq_mul_inv, mul_comm]
  rw [value, supplied_lift l M f hframe, frame_outward l M hg hG, hr,
    map_smul, smul_eq_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The converse reconstructs every actual point satisfying all closed signs.
It includes all equality boundaries and uses the original supplied f. -/
theorem same_image_halfspaces (hl : ∀ k, 0 < l k)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hM : 0 < M.det) (hG : (lengthGram l).det < 0) :
    range f = region (outward l M) := by
  have hMd : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.ne'
  have hw := weight_positive l hl hG
  ext p
  constructor
  · rintro ⟨v, rfl⟩ a
    rw [image_value l M f hframe hg hG]
    exact div_nonpos_of_nonpos_of_nonneg (CapTraceHull.support_body l _ v.property a)
      (mul_nonneg (Real.sqrt_nonneg _) (hw a).le)
  · intro hp
    let x : V := lift p ᵥ* M⁻¹
    have hxM : x ᵥ* M = lift p := by
      dsimp only [x]
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hMd, Matrix.vecMul_one]
    have hx (i : Fin 4) : 0 ≤ x i := by
      have hi := hp (Sum.inl i)
      change lorentz (lift p) (outward l M (Sum.inl i)) ≤ 0 at hi
      rw [← hxM, frame_outward l M hg hG] at hi
      have hi' := (div_le_iff₀ (hw (Sum.inl i))).mp hi
      simpa [CapTraceHull.support] using hi'
    have hrow (i : Fin 4) : ∑ j, lengthGram l i j * x j ≤ 0 := by
      have hi := hp (Sum.inr i)
      change lorentz (lift p) (M i) ≤ 0 at hi
      rw [← hxM, frame_cap l M hg] at hi
      exact hi
    have hq : gramQuadratic l x = -1 := by
      change (∑ i, x i * ∑ j, lengthGram l i j * x j) = -1
      rw [← frame_pair l M hg x x, hxM, lift_unit]
    let s := ∑ i, x i
    have hs : 0 < s := by
      have hn : 0 ≤ s := Finset.sum_nonneg fun i _ => hx i
      by_contra h
      have hz : s = 0 := le_antisymm (le_of_not_gt h) hn
      have hz' : ∀ i, x i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hx j)).mp hz i (Finset.mem_univ i)
      have hx0 : x = 0 := funext hz'
      simp [hx0, gramQuadratic] at hq
    let v : V := fun i => x i / s
    have hvscale : v = s⁻¹ • x := by ext i; simp [v, div_eq_mul_inv, mul_comm]
    have hv : v ∈ cutBody l := by
      refine ⟨⟨fun i => div_nonneg (hx i) hs.le, ?_⟩, ?_⟩
      · change (∑ i, x i / s) = 1
        rw [← Finset.sum_div]
        exact div_self hs.ne'
      · intro i
        change (∑ j, lengthGram l i j * (x j / s)) ≤ 0
        simp only [← mul_div_assoc, ← Finset.sum_div]
        exact div_nonpos_of_nonpos_of_nonneg (hrow i) hs.le
    have hroot : Real.sqrt (-gramQuadratic l v) = s⁻¹ := by
      rw [hvscale, gram_scale, hq]
      have he : -(s⁻¹ ^ 2 * (-1 : ℝ)) = (s⁻¹)^2 := by ring
      rw [he, Real.sqrt_sq (inv_nonneg.mpr hs.le)]
    have hrad : radial l v = x := by
      ext i
      change v i / Real.sqrt (-gramQuadratic l v) = x i
      rw [hroot]
      dsimp only [v]
      field_simp [hs.ne']
    refine ⟨⟨v, hv⟩, lift_injective ?_⟩
    rw [supplied_lift l M f hframe, hrad, hxM]

end Supplied

/-- A_i is the sum of the three coshes adjacent to i, using the original G. -/
def capWeight (l : Fin 6 → ℝ) (i : Fin 4) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, -lengthGram l i j

/-- Explicit points with exactly one active coefficient support. -/
def facetWitness (l : Fin 6 → ℝ) : Support → V
  | Sum.inl i => fun j => if j = i then 0 else 1 / 3
  | Sum.inr i => fun j => if j = i then capWeight l i / (capWeight l i + 3)
      else 1 / (capWeight l i + 3)

private lemma isolated_coefficient_witness (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (a : Support) :
    facetWitness l a ∈ cutBody l ∧
    CapTraceHull.support l a (facetWitness l a) = 0 ∧
    ∀ b, b ≠ a → CapTraceHull.support l b (facetWitness l a) < 0 := by
  classical
  have hc (k : Fin 6) : 1 < Real.cosh (l k) :=
    Real.one_lt_cosh.mpr (ne_of_gt (hl k))
  cases a with
  | inl i =>
    have hr (r : Fin 4) : CapTraceHull.support l (Sum.inr r)
        (facetWitness l (Sum.inl i)) < 0 := by
      fin_cases i <;> fin_cases r <;>
        simp [CapTraceHull.support, facetWitness, lengthGram, Fin.sum_univ_succ] <;>
        linarith [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · intro j
      simp only [facetWitness]
      split_ifs <;> norm_num
    · fin_cases i <;> norm_num [facetWitness, Fin.sum_univ_succ]
    · intro r
      simpa [CapTraceHull.support] using (hr r).le
    · simp [CapTraceHull.support, facetWitness]
    · intro b hb
      cases b with
      | inl j =>
        have hji : j ≠ i := fun h => hb (congrArg Sum.inl h)
        simp [CapTraceHull.support, facetWitness, hji]
      | inr r => exact hr r
  | inr i =>
    let A := capWeight l i
    let D := A + 3
    have hrowi : (∑ j, lengthGram l i j) = 1 - A := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), gram_diag]
      dsimp [A, capWeight]
      rw [Finset.sum_neg_distrib]
      ring
    have hA : 3 < A := by
      have hcard : (Finset.univ.erase i).card = 3 := by simp
      have hn : (Finset.univ.erase i).Nonempty := Finset.card_pos.mp (by omega)
      have he (j : Fin 4) (hj : j ∈ Finset.univ.erase i) : 1 < -lengthGram l i j := by
        simpa using neg_lt_neg (gram_off l hl i j (Finset.ne_of_mem_erase hj).symm)
      calc
        3 = ∑ j ∈ Finset.univ.erase i, (1 : ℝ) := by simp
        _ < A := by
          apply Finset.sum_lt_sum
          · intro j hj; exact (he j hj).le
          · obtain ⟨j, hj⟩ := hn
            exact ⟨j, hj, he j hj⟩
    have hD : 0 < D := by dsimp [D]; linarith
    have hpos (j : Fin 4) : 0 < facetWitness l (Sum.inr i) j := by
      by_cases hj : j = i
      · simpa [facetWitness, hj, A, D] using div_pos (by linarith : 0 < A) hD
      · simpa [facetWitness, hj, A, D] using one_div_pos.mpr hD
    have hsum : ∑ j, facetWitness l (Sum.inr i) j = 1 := by
      change (∑ j : Fin 4, if j = i then A / D else 1 / D) = 1
      fin_cases i <;> simp [Fin.sum_univ_succ] <;> dsimp [D] <;>
        field_simp [show A + 3 ≠ 0 from hD.ne'] <;> ring
    have hvec : facetWitness l (Sum.inr i) =
        D⁻¹ • ((fun _ : Fin 4 => (1 : ℝ)) + (A - 1) • Pi.single i 1) := by
      ext j
      by_cases hj : j = i <;> simp [facetWitness, hj, A, D, div_eq_mul_inv] <;> ring
    have hsingle (r : Fin 4) :
        CapTraceHull.support l (Sum.inr r) (Pi.single i 1) = lengthGram l r i := by
      simp [CapTraceHull.support, Pi.single_apply, mul_ite]
    have hone (r : Fin 4) :
        CapTraceHull.support l (Sum.inr r) (fun _ => (1 : ℝ)) = ∑ j, lengthGram l r j := by
      simp [CapTraceHull.support]
    have hrow (r : Fin 4) : CapTraceHull.support l (Sum.inr r)
        (facetWitness l (Sum.inr i)) =
        ((∑ j, lengthGram l r j) + (A - 1) * lengthGram l r i) / D := by
      rw [hvec, map_smul, map_add, map_smul, smul_eq_mul, smul_eq_mul, hsingle, hone]
      ring
    have hones (r : Fin 4) : (∑ j, lengthGram l r j) < 0 := by
      have hb := (shared_radial_body l hl).2.2.1 r
      have he : (∑ j, lengthGram l r j * (1 / 4 : ℝ)) =
          (∑ j, lengthGram l r j) / 4 := by simp [div_eq_mul_inv, Finset.sum_mul]
      rw [he] at hb
      linarith
    have hzero : CapTraceHull.support l (Sum.inr i) (facetWitness l (Sum.inr i)) = 0 := by
      rw [hrow, hrowi, gram_diag]
      ring
    have hrest (r : Fin 4) (hri : r ≠ i) :
        CapTraceHull.support l (Sum.inr r) (facetWitness l (Sum.inr i)) < 0 := by
      rw [hrow]
      apply div_neg_of_neg_of_pos _ hD
      exact add_neg (hones r) (mul_neg_of_pos_of_neg (by linarith)
        (lt_trans (gram_off l hl r i hri) (by norm_num)))
    refine ⟨⟨⟨fun j => (hpos j).le, hsum⟩, ?_⟩, hzero, ?_⟩
    · intro r
      by_cases hr : r = i
      · subst r; simpa [CapTraceHull.support] using hzero.le
      · simpa [CapTraceHull.support] using (hrest r hr).le
    · intro b hb
      cases b with
      | inl j => simpa [CapTraceHull.support] using neg_neg_of_pos (hpos j)
      | inr r => exact hrest r (fun h => hb (congrArg Sum.inr h))

private lemma value_continuous (A : Support → V) (a : Support) :
    Continuous (value A a) := by
  have hc := D5.S3.Geometry.HyperbolicSupportBoundary.lift_continuous
  unfold value lorentz
  exact continuous_finsetSum _ fun k _ =>
    (continuous_const.mul ((continuous_apply k).comp hc)).mul continuous_const

/-- A native actual global line transverse to any unit spacelike support.
This is extracted from the existing joint-ray theorem with U = V = w. -/
private lemma crossing (w : V) (hw : lorentz w w = 1) (p : HyperbolicThreeSpace)
    (hp : lorentz (lift p) w = 0) :
    ∃ g : ℝ → HyperbolicThreeSpace, Isometry g ∧ g 0 = p ∧
      ∀ t, lorentz (lift (g t)) w = Real.sinh t := by
  obtain ⟨g, _, hg, _, _, _, hglift, _⟩ :=
    actual_rays_joint_angle (lift p) w w (lift_unit p) (lift_time p)
      hw hw hp hp (by rw [hw]; norm_num)
  refine ⟨g, hg, ?_, ?_⟩
  · apply lift_injective
    rw [hglift]
    simp
  · intro t
    rw [hglift, lorentz_symm, lorentz_right, lorentz_symm w (lift p), hp, hw]
    ring

/-- Ambient H3 topology: an active support is crossed outside arbitrarily close
to the point. No statement about interior in a supporting H2 is used here. -/
private lemma ambient_boundary (A : Support → V)
    (hu : ∀ a, lorentz (A a) (A a) = 1) :
    IsClosed (region A) ∧ interior (region A) = strictRegion A ∧
    frontier (region A) = {p ∈ region A | ∃ a, value A a p = 0} := by
  have hc : IsClosed (region A) := by
    unfold region
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_le (value_continuous A a) continuous_const
  have hz (p : HyperbolicThreeSpace) (a : Support) (ha : value A a p = 0) :
      p ∉ interior (region A) := by
    obtain ⟨g, hg, hg0, hread⟩ := crossing (A a) (hu a) p ha
    intro hp
    have hn : region A ∈ 𝓝 (g 0) := by
      rw [hg0]
      exact mem_interior_iff_mem_nhds.mp hp
    have hpre : {t | g t ∈ region A} ∈ 𝓝 (0 : ℝ) :=
      hg.continuous.continuousAt.eventually hn
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hpre
    have ht : 0 < ε / 2 := by linarith
    have hin : g (ε/2) ∈ region A := hb (by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
      linarith)
    have hh := hin a
    change lorentz (lift (g (ε/2))) (A a) ≤ 0 at hh
    rw [hread] at hh
    exact (not_lt_of_ge hh) (Real.sinh_pos_iff.mpr ht)
  have hi : interior (region A) = strictRegion A := by
    apply Subset.antisymm
    · intro p hp a
      exact lt_of_le_of_ne (interior_subset hp a) (fun h => hz p a h hp)
    · apply interior_maximal
      · exact fun p hp a => (hp a).le
      · unfold strictRegion
        simp only [Set.ofPred_forall]
        exact isOpen_iInter_of_finite fun a => isOpen_lt (value_continuous A a) continuous_const
  refine ⟨hc, hi, ?_⟩
  ext p
  rw [frontier, hc.closure_eq, hi]
  change (p ∈ region A ∧ ¬ ∀ a, value A a p < 0) ↔
    (p ∈ region A ∧ ∃ a, value A a p = 0)
  constructor
  · rintro ⟨hp, hn⟩
    obtain ⟨a, ha⟩ := not_forall.mp hn
    exact ⟨hp, a, le_antisymm (hp a) (le_of_not_gt ha)⟩
  · rintro ⟨hp, a, ha⟩
    exact ⟨hp, fun h => (ne_of_lt (h a)) ha⟩

private lemma complete_halfspace (A : Support → V)
    (hu : ∀ a, lorentz (A a) (A a) = 1) (a : Support) :
    IsClosed {p | value A a p ≤ 0} ∧
    ∃ e : UpperHalfPlane → HyperbolicThreeSpace, Isometry e ∧
      range e = {p | value A a p = 0} ∧
      frontier {p | value A a p ≤ 0} = range e := by
  obtain ⟨e, he, hplane⟩ := supporting_plane_isometry (A a) (by rw [hu]; norm_num)
  have hb := (ambient_boundary (fun _ : Support => A a) (fun _ => hu a)).2.2
  have hR : region (fun _ : Support => A a) = {p | value A a p ≤ 0} := by
    ext p
    simp [region, value]
  have hf : frontier {p | value A a p ≤ 0} = {p | value A a p = 0} := by
    rw [← hR, hb]
    ext p
    constructor
    · rintro ⟨_, b, hb⟩
      exact hb
    · intro hp
      exact ⟨fun _ => hp.le, Sum.inl 0, hp⟩
  exact ⟨isClosed_le (value_continuous A a) continuous_const,
    e, he, hplane, hf.trans hplane.symm⟩

private lemma native_patch_and_removal (A : Support → V)
    (hu : ∀ a, lorentz (A a) (A a) = 1) (a : Support) (p : HyperbolicThreeSpace)
    (hp : value A a p = 0) (hs : ∀ b, b ≠ a → value A b p < 0) :
    (∃ e : UpperHalfPlane → HyperbolicThreeSpace, ∃ U : Set UpperHalfPlane,
      Isometry e ∧ range e = {q | value A a q = 0} ∧
      IsOpen U ∧ U.Nonempty ∧ e '' U ⊆ {q ∈ region A | value A a q = 0}) ∧
    (∃ q, 0 < value A a q ∧ ∀ b, b ≠ a → value A b q < 0) := by
  classical
  obtain ⟨_, e, he, hplane, _⟩ := complete_halfspace A hu a
  have hpr : p ∈ range e := by rw [hplane]; exact hp
  obtain ⟨z, hz⟩ := hpr
  let U := {z : UpperHalfPlane | ∀ b, b ≠ a → value A b (e z) < 0}
  have hU : IsOpen U := by
    dsimp only [U]
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro b
    by_cases hb : b ≠ a
    · simpa [hb] using isOpen_lt ((value_continuous A b).comp he.continuous) continuous_const
    · simp [hb]
  have hUn : U.Nonempty := ⟨z, by simpa [U, hz] using hs⟩
  have hpatch : e '' U ⊆ {q ∈ region A | value A a q = 0} := by
    rintro q ⟨y, hy, rfl⟩
    have hzero : value A a (e y) = 0 := by
      have h : e y ∈ range e := mem_range_self y
      rw [hplane] at h
      exact h
    refine ⟨fun b => ?_, hzero⟩
    by_cases hb : b = a
    · subst b; exact hzero.le
    · exact (hy b hb).le
  refine ⟨⟨e, U, he, hplane, hU, hUn, hpatch⟩, ?_⟩
  obtain ⟨g, hg, hg0, hread⟩ := crossing (A a) (hu a) p hp
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ b, b ≠ a → value A b (g t) < 0 := by
    apply Filter.eventually_all.mpr
    intro b
    by_cases hb : b ≠ a
    · have hc0 : ContinuousAt (fun t : ℝ => value A b (g t)) (0 : ℝ) :=
        ((value_continuous A b).comp hg.continuous).continuousAt
      have hlt0 : value A b (g 0) < (0 : ℝ) := by
        rw [hg0]
        exact hs b hb
      have h : ∀ᶠ t in 𝓝 (0 : ℝ), value A b (g t) < 0 :=
        hc0.eventually_lt
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ)) hlt0
      exact h.mono fun t ht _ => ht
    · exact Filter.Eventually.of_forall fun _ h => (hb h).elim
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hnear
  have ht : 0 < ε / 2 := by linarith
  refine ⟨g (ε/2), ?_, hb ?_⟩
  · change 0 < lorentz (lift (g (ε/2))) (A a)
    rw [hread]
    exact Real.sinh_pos_iff.mpr ht
  · simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith

private lemma gram_determinant (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) :
    (lengthGram l).det = -(M.det)^2 := by
  let J : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![(1 : ℝ),1,1,-1]
  have hJ : J.det = -1 := by simp [J, Matrix.det_diagonal, Fin.prod_univ_succ]
  have hcong : M * J * M.transpose = lengthGram l := by
    ext i j
    simpa [J, Matrix.mul_apply, Fin.sum_univ_succ, lorentz,
      sub_eq_add_neg, add_assoc] using hg i j
  rw [← hcong, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hJ]
  ring

private lemma oriented_regions (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hG : (lengthGram l).det < 0) :
    region (outward l M) = {p | ∀ i,
      0 ≤ lorentz (lift p) (dual l M i) ∧ lorentz (lift p) (M i) ≤ 0} ∧
    strictRegion (outward l M) = {p | ∀ i,
      0 < lorentz (lift p) (dual l M i) ∧ lorentz (lift p) (M i) < 0} := by
  have hw := weight_positive l hl hG
  have hs (p : HyperbolicThreeSpace) (i : Fin 4) :
      value (outward l M) (Sum.inl i) p =
        -lorentz (lift p) (dual l M i) / weight l (Sum.inl i) := by
    change lorentz (lift p) ((-(weight l (Sum.inl i))⁻¹) • dual l M i) = _
    calc
      _ = (-(weight l (Sum.inl i))⁻¹) * lorentz (lift p) (dual l M i) := by
        simpa using lorentz_right (lift p) (dual l M i) (dual l M i)
          (-(weight l (Sum.inl i))⁻¹) 0
      _ = _ := by ring
  constructor
  · ext p
    constructor
    · intro hp i
      refine ⟨?_, hp (Sum.inr i)⟩
      have hi := hp (Sum.inl i)
      rw [hs] at hi
      have hh := (div_le_iff₀ (hw (Sum.inl i))).mp hi
      linarith
    · intro hp a
      cases a with
      | inl i =>
        rw [hs]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hp i).1) (hw _).le
      | inr i => exact (hp i).2
  · ext p
    constructor
    · intro hp i
      refine ⟨?_, hp (Sum.inr i)⟩
      have hi := hp (Sum.inl i)
      rw [hs] at hi
      have hh := (div_lt_iff₀ (hw (Sum.inl i))).mp hi
      linarith
    · intro hp a
      cases a with
      | inl i =>
        rw [hs]
        exact div_neg_of_neg_of_pos (neg_neg_of_pos (hp i).1) (hw _)
      | inr i => exact (hp i).2

/-- Finite same-witness reconstruction and genuine ambient facets.

The raw telescope is the one supplied by `shared_radial_body`: the six lengths
are independent; admissibility restricts their realizability. Orientation,
continuity, injectivity, compactness and nonemptiness are retained at this raw
entry even when a smaller internal argument does not need all of them.

The conclusion identifies actual supports and actual facet patches. It does not
identify parent charts, face markings, gluing maps, dihedral data or orbits.
-/
theorem same_supplied_actual_halfspaces
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hadmissible :
      -1 < FourCycleEnvelopes.cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
        (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) ∧
      FourCycleEnvelopes.cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
        (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) < 1)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hgram : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hM : 0 < M.det) (hG : (lengthGram l).det < 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hcontinuous : Continuous f) (hinjective : Function.Injective f)
    (hcompact : IsCompact (range f)) (hnonempty : (range f).Nonempty)
    (hframe : ∀ v, ∃ y : V, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2))) :
    (lengthGram l).det = -(M.det)^2 ∧
    (∀ i, 0 < (lengthGram l)⁻¹ i i) ∧
    (∀ i j, lorentz (dual l M i) (M j) = if i = j then 1 else 0) ∧
    (∀ i j, lorentz (dual l M i) (dual l M j) = (lengthGram l)⁻¹ i j) ∧
    (∀ a, lorentz (outward l M a) (outward l M a) = 1) ∧
    range f = region (outward l M) ∧
    range f = {p | ∀ i, 0 ≤ lorentz (lift p) (dual l M i) ∧ lorentz (lift p) (M i) ≤ 0} ∧
    interior (range f) = strictRegion (outward l M) ∧
    interior (range f) = {p | ∀ i,
      0 < lorentz (lift p) (dual l M i) ∧ lorentz (lift p) (M i) < 0} ∧
    f ⟨(fun _ : Fin 4 => (1 : ℝ)/4), (shared_radial_body l hl).2.1⟩ ∈ interior (range f) ∧
    (interior (range f)).Nonempty ∧
    IsClosed (range f) ∧
    frontier (range f) = {p ∈ range f | ∃ a, value (outward l M) a p = 0} ∧
    (∀ a, IsClosed {p | value (outward l M) a p ≤ 0} ∧
      ∃ e : UpperHalfPlane → HyperbolicThreeSpace, Isometry e ∧
        range e = {p | value (outward l M) a p = 0} ∧
        frontier {p | value (outward l M) a p ≤ 0} = range e) ∧
    (∀ a, f '' {v : cutBody l | CapTraceHull.support l a v.val = 0} =
      {p ∈ range f | value (outward l M) a p = 0}) ∧
    (∀ a, ∃ v : cutBody l, v.val = facetWitness l a ∧
      value (outward l M) a (f v) = 0 ∧
      ∀ b, b ≠ a → value (outward l M) b (f v) < 0) ∧
    (∀ a, ∃ e : UpperHalfPlane → HyperbolicThreeSpace, ∃ U : Set UpperHalfPlane,
      Isometry e ∧ range e = {p | value (outward l M) a p = 0} ∧
      IsOpen U ∧ U.Nonempty ∧
      e '' U ⊆ f '' {v : cutBody l | CapTraceHull.support l a v.val = 0}) ∧
    (∀ a, ∃ p, 0 < value (outward l M) a p ∧
      ∀ b, b ≠ a → value (outward l M) b p < 0) ∧
    (∀ a, range f ⊂ {p | ∀ b, b ≠ a → value (outward l M) b p ≤ 0}) ∧
    Function.Injective (outward l M) := by
  classical
  let A := outward l M
  have hu := outward_unit l hl M hgram hG
  have hw := weight_positive l hl hG
  have himage := same_image_halfspaces l M f hframe hl hgram hM hG
  have htop := ambient_boundary A hu
  have horient := oriented_regions l hl M hG
  have hMdG : IsUnit (lengthGram l).det := isUnit_iff_ne_zero.mpr (ne_of_lt hG)
  have hdualM (i j : Fin 4) :
      lorentz (dual l M i) (M j) = if i = j then 1 else 0 := by
    rw [dual, frame_cap l M hgram]
    have he : (∑ k, lengthGram l j k * (lengthGram l)⁻¹ i k) =
        ((lengthGram l)⁻¹ * lengthGram l) i j := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [gram_symm l j k, mul_comm]
    rw [he, Matrix.nonsing_inv_mul _ hMdG]
    simp [Matrix.one_apply]
  have hroot (v : cutBody l) : 0 < Real.sqrt (-gramQuadratic l v.val) :=
    Real.sqrt_pos.mpr (neg_pos.mpr ((shared_radial_body l hl).2.2.2.1 v.val v.property))
  have hden (v : cutBody l) (a : Support) :
      0 < Real.sqrt (-gramQuadratic l v.val) * weight l a := mul_pos (hroot v) (hw a)
  have hzero (v : cutBody l) (a : Support) :
      value A a (f v) = 0 ↔ CapTraceHull.support l a v.val = 0 := by
    rw [image_value l M f hframe hgram hG]
    constructor
    · intro hz
      exact (div_eq_zero_iff.mp hz).resolve_right (hden v a).ne'
    · intro hz
      rw [hz, zero_div]
  have htrace (a : Support) : f '' {v : cutBody l | CapTraceHull.support l a v.val = 0} =
      {p ∈ range f | value A a p = 0} := by
    ext p
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨mem_range_self v, (hzero v a).mpr hv⟩
    · rintro ⟨⟨v, rfl⟩, hv⟩
      exact ⟨v, (hzero v a).mp hv, rfl⟩
  let v : Support → cutBody l := fun a =>
    ⟨facetWitness l a, (isolated_coefficient_witness l hl a).1⟩
  have hv0 (a : Support) : value A a (f (v a)) = 0 :=
    (hzero (v a) a).mpr (isolated_coefficient_witness l hl a).2.1
  have hvs (a b : Support) (hb : b ≠ a) : value A b (f (v a)) < 0 := by
    rw [image_value l M f hframe hgram hG]
    exact div_neg_of_neg_of_pos ((isolated_coefficient_witness l hl a).2.2 b hb) (hden _ _)
  have hfacets (a : Support) := native_patch_and_removal A hu a (f (v a)) (hv0 a) (hvs a)
  have hinside : f ⟨(fun _ : Fin 4 => (1 : ℝ)/4), (shared_radial_body l hl).2.1⟩ ∈
      interior (range f) := by
    rw [himage, htop.2.1]
    intro a
    rw [image_value l M f hframe hgram hG]
    apply div_neg_of_neg_of_pos _ (hden _ _)
    cases a with
    | inl i => norm_num [CapTraceHull.support]
    | inr i => simpa [CapTraceHull.support] using (shared_radial_body l hl).2.2.1 i
  refine ⟨gram_determinant l M hgram, dual_diagonal_positive l hl hG, hdualM,
    (fun i j => frame_dual l M hgram hG ((lengthGram l)⁻¹ i) j), hu,
    himage, himage.trans horient.1, ?_, ?_, hinside, ⟨_, hinside⟩, ?_, ?_,
    complete_halfspace A hu, htrace, (fun a => ⟨v a, rfl, hv0 a, hvs a⟩),
    ?_, (fun a => (hfacets a).2), ?_, ?_⟩
  · rw [himage]
    exact htop.2.1
  · rw [himage, htop.2.1]
    exact horient.2
  · rw [himage]
    exact htop.1
  · rw [himage]
    exact htop.2.2
  · intro a
    obtain ⟨e, U, he, hp, ho, hn, hsub⟩ := (hfacets a).1
    refine ⟨e, U, he, hp, ho, hn, ?_⟩
    rw [htrace]
    simpa only [himage] using hsub
  · intro a
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro p hp b _
      rw [himage] at hp
      exact hp b
    · intro heq
      obtain ⟨p, hp, hrest⟩ := (hfacets a).2
      have hmem : p ∈ range f := by
        rw [heq]
        exact fun b hb => (hrest b hb).le
      rw [himage] at hmem
      exact (not_lt_of_ge (hmem a)) hp
  · intro a b hab
    by_contra hne
    have hb := hvs a b (Ne.symm hne)
    have he : value A a (f (v a)) = value A b (f (v a)) := by
      exact congrArg (fun w => lorentz (lift (f (v a))) w) hab
    rw [hv0 a] at he
    exact (ne_of_lt hb) he.symm

end D5.S3.Geometry.Hyperideal.LengthGramActualHalfspaces
