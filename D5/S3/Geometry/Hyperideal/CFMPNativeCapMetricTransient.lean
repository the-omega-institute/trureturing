import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments

namespace NativeCornerExtractionSource
set_option autoImplicit false

abbrev V := Fin 4 → ℝ

def J : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![(1 : ℝ), 1, 1, -1]

def B : LinearMap.BilinForm ℝ V := Matrix.toBilin' J

private theorem B_apply (u v : V) : B u v = lorentz u v := by
  simp [B, J, Matrix.toBilin'_apply, Matrix.diagonal_apply,
    lorentz, Fin.sum_univ_succ] <;> ring

private theorem B_symm (u v : V) : B u v = B v u := by
  rw [B_apply, B_apply]
  exact lorentz_symm u v

private theorem B_nondegenerate : B.Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' J
  norm_num [J, Matrix.det_diagonal, Fin.prod_univ_succ]

private theorem lift_norm (p : HyperbolicThreeSpace) :
    B (lift p) (lift p) = -1 := by
  rw [B_apply]
  exact lift_unit p

private theorem norm_one_ne_zero (u : V) (hu : B u u = 1) : u ≠ 0 := by
  intro hz
  rw [hz, LinearMap.BilinForm.zero_left] at hu
  norm_num at hu

private theorem lift_ne_zero (p : HyperbolicThreeSpace) : lift p ≠ 0 := by
  intro hz
  have hu := lift_norm p
  rw [hz, LinearMap.BilinForm.zero_left] at hu
  norm_num at hu

def capFacet (P : Set HyperbolicThreeSpace) (c : Fin 4 → V) (i : Fin 4) :
    Set HyperbolicThreeSpace := {p | p ∈ P ∧ B (c i) (lift p) = 0}

def sideFacet (P : Set HyperbolicThreeSpace) (n : Fin 4 → V) (i : Fin 4) :
    Set HyperbolicThreeSpace := {p | p ∈ P ∧ B (n i) (lift p) = 0}

/-- An independent support-normal/corner representation. The orthogonality field
is the Lorentz tangent-normal interpretation of actual incident support planes.
This structure does not assert a whole-facet topological characterization. -/
structure NativeSupportCorners where
  P : Set HyperbolicThreeSpace
  cap : Fin 4 → V
  side : Fin 4 → V
  corner : Fin 4 → Fin 4 → HyperbolicThreeSpace
  cap_unit : ∀ i, B (cap i) (cap i) = 1
  side_unit : ∀ i, B (side i) (side i) = 1
  body_halfspaces : P = {p | (∀ i, B (cap i) (lift p) ≤ 0) ∧
    (∀ i, B (side i) (lift p) ≤ 0)}
  corner_mem : ∀ i j, i ≠ j → corner i j ∈ P
  cap_incidence : ∀ i j, i ≠ j → ∀ r,
    corner i j ∈ capFacet P cap r ↔ r = i
  side_incidence : ∀ i j, i ≠ j → ∀ r,
    corner i j ∈ sideFacet P side r ↔ r ≠ i ∧ r ≠ j
  orthogonal_incidence : ∀ j i, j ≠ i → B (cap j) (side i) = 0

private theorem cap_zero_iff (d : NativeSupportCorners)
    (i j r : Fin 4) (hij : i ≠ j) :
    B (d.cap r) (lift (d.corner i j)) = 0 ↔ r = i := by
  simpa only [capFacet, Set.mem_setOf_eq, d.corner_mem i j hij, true_and]
    using d.cap_incidence i j hij r

private theorem side_zero_iff (d : NativeSupportCorners)
    (i j r : Fin 4) (hij : i ≠ j) :
    B (d.side r) (lift (d.corner i j)) = 0 ↔ r ≠ i ∧ r ≠ j := by
  simpa only [sideFacet, Set.mem_setOf_eq, d.corner_mem i j hij, true_and]
    using d.side_incidence i j hij r

private theorem cap_strict (d : NativeSupportCorners)
    (i j r : Fin 4) (hij : i ≠ j) (hri : r ≠ i) :
    B (d.cap r) (lift (d.corner i j)) < 0 := by
  have hm := d.corner_mem i j hij
  rw [d.body_halfspaces] at hm
  have hle := hm.1 r
  have hne : B (d.cap r) (lift (d.corner i j)) ≠ 0 := by
    intro hz
    exact hri ((cap_zero_iff d i j r hij).mp hz)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact (hne heq).elim

private theorem side_strict (d : NativeSupportCorners)
    (i j r : Fin 4) (hij : i ≠ j) (hn : ¬ (r ≠ i ∧ r ≠ j)) :
    B (d.side r) (lift (d.corner i j)) < 0 := by
  have hm := d.corner_mem i j hij
  rw [d.body_halfspaces] at hm
  have hle := hm.2 r
  have hne : B (d.side r) (lift (d.corner i j)) ≠ 0 := by
    intro hz
    exact hn ((side_zero_iff d i j r hij).mp hz)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact (hne heq).elim

private theorem corners_ne (d : NativeSupportCorners)
    (i j : Fin 4) (hij : i ≠ j) : d.corner i j ≠ d.corner j i := by
  intro heq
  have hzero := (cap_zero_iff d i j i hij).mpr rfl
  have hstrict := cap_strict d j i i hij.symm hij
  rw [heq] at hzero
  linarith

def spanPair (u v : V) : Submodule ℝ V := Submodule.span ℝ ({u, v} : Set V)

private theorem independent_pair_from_actual_evaluation
    (u v : V) (f : Module.Dual ℝ V) (hu : u ≠ 0)
    (hfu : f u = 0) (hfv : f v ≠ 0) :
    LinearIndependent ℝ (![u, v] : Fin 2 → V) := by
  apply linearIndependent_fin2.mpr
  constructor
  · change v ≠ 0
    intro hv
    exact hfv (by rw [hv, map_zero])
  · intro a ha
    change a • v = u at ha
    have hmul : a * f v = 0 := by
      simpa only [map_smul, smul_eq_mul, hfu] using congrArg f ha
    have ha0 : a = 0 := (mul_eq_zero.mp hmul).resolve_right hfv
    rw [ha0, zero_smul] at ha
    exact hu ha.symm

private theorem spanPair_rank (u v : V)
    (huv : LinearIndependent ℝ (![u, v] : Fin 2 → V)) :
    Module.finrank ℝ (spanPair u v) = 2 := by
  have hrange : Set.range (![u, v] : Fin 2 → V) = ({u, v} : Set V) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hxu | hxv
      · exact ⟨0, hxu.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp hxv).symm⟩
  change Module.finrank ℝ (Submodule.span ℝ ({u, v} : Set V)) = 2
  rw [← hrange]
  exact finrank_span_eq_card huv

private theorem mem_orthogonal_spanPair (u v x : V)
    (hu : B u x = 0) (hv : B v x = 0) :
    x ∈ B.orthogonal (spanPair u v) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  obtain ⟨a, b, hy⟩ := Submodule.mem_span_pair.mp hy
  rw [← hy, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left, hu, hv]
  ring

private theorem spanPair_le (u v : V) (S : Submodule ℝ V)
    (hu : u ∈ S) (hv : v ∈ S) : spanPair u v ≤ S := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hxu | hxv
  · subst x; exact hu
  · have hxv' : x = v := Set.mem_singleton_iff.mp hxv
    subst x; exact hv

def ridgePlane (d : NativeSupportCorners) (k h : Fin 4) : Submodule ℝ V :=
  B.orthogonal (spanPair (d.side k) (d.side h))

structure RidgeExtraction (d : NativeSupportCorners) (i j k h : Fin 4) : Prop where
  lateral_independent : LinearIndependent ℝ (![d.side k, d.side h] : Fin 2 → V)
  endpoint_independent : LinearIndependent ℝ
    (![lift (d.corner i j), lift (d.corner j i)] : Fin 2 → V)
  cap_independent : LinearIndependent ℝ (![d.cap i, d.cap j] : Fin 2 → V)
  orthogonal_rank : Module.finrank ℝ (ridgePlane d k h) = 2
  endpoint_span : spanPair (lift (d.corner i j)) (lift (d.corner j i)) = ridgePlane d k h
  cap_span : spanPair (d.cap i) (d.cap j) = ridgePlane d k h

theorem actual_corner_ridge_extraction (d : NativeSupportCorners)
    (i j k h : Fin 4) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (hhi : h ≠ i) (hhj : h ≠ j)
    (hkh : k ≠ h) : RidgeExtraction d i j k h := by
  have hn0 := norm_one_ne_zero (d.side k) (d.side_unit k)
  have hYk : B (lift (d.corner i h)) (d.side k) = 0 := by
    rw [B_symm]
    exact (side_zero_iff d i h k hhi.symm).mpr ⟨hki, hkh⟩
  have hYh : B (lift (d.corner i h)) (d.side h) ≠ 0 := by
    rw [B_symm]
    exact ne_of_lt (side_strict d i h h hhi.symm (by simp))
  have hn := independent_pair_from_actual_evaluation
    (d.side k) (d.side h) (B (lift (d.corner i h))) hn0 hYk hYh
  have hXi : B (d.cap i) (lift (d.corner i j)) = 0 :=
    (cap_zero_iff d i j i hij).mpr rfl
  have hZi : B (d.cap i) (lift (d.corner j i)) < 0 :=
    cap_strict d j i i hij.symm hij
  have hXj : B (d.cap j) (lift (d.corner i j)) < 0 :=
    cap_strict d i j j hij hij.symm
  have hX := independent_pair_from_actual_evaluation
    (lift (d.corner i j)) (lift (d.corner j i)) (B (d.cap i))
    (lift_ne_zero _) hXi (ne_of_lt hZi)
  have hc := independent_pair_from_actual_evaluation
    (d.cap i) (d.cap j) (B (lift (d.corner i j)))
    (norm_one_ne_zero _ (d.cap_unit i))
    ((B_symm _ _).trans hXi) (by rw [B_symm]; exact ne_of_lt hXj)
  have hdim : Module.finrank ℝ (ridgePlane d k h) = 2 := by
    rw [ridgePlane, LinearMap.BilinForm.finrank_orthogonal B_nondegenerate,
      spanPair_rank _ _ hn]
    norm_num [V, Module.finrank_fin_fun]
  have hXk : B (d.side k) (lift (d.corner i j)) = 0 :=
    (side_zero_iff d i j k hij).mpr ⟨hki, hkj⟩
  have hXh : B (d.side h) (lift (d.corner i j)) = 0 :=
    (side_zero_iff d i j h hij).mpr ⟨hhi, hhj⟩
  have hZk : B (d.side k) (lift (d.corner j i)) = 0 :=
    (side_zero_iff d j i k hij.symm).mpr ⟨hkj, hki⟩
  have hZh : B (d.side h) (lift (d.corner j i)) = 0 :=
    (side_zero_iff d j i h hij.symm).mpr ⟨hhj, hhi⟩
  have hXle : spanPair (lift (d.corner i j)) (lift (d.corner j i)) ≤
      ridgePlane d k h := spanPair_le _ _ _
        (mem_orthogonal_spanPair _ _ _ hXk hXh)
        (mem_orthogonal_spanPair _ _ _ hZk hZh)
  have hcle : spanPair (d.cap i) (d.cap j) ≤ ridgePlane d k h := by
    apply spanPair_le
    · apply mem_orthogonal_spanPair
      · rw [B_symm]; exact d.orthogonal_incidence i k hki.symm
      · rw [B_symm]; exact d.orthogonal_incidence i h hhi.symm
    · apply mem_orthogonal_spanPair
      · rw [B_symm]; exact d.orthogonal_incidence j k hkj.symm
      · rw [B_symm]; exact d.orthogonal_incidence j h hhj.symm
  exact ⟨hn, hX, hc, hdim,
    Submodule.eq_of_le_of_finrank_eq hXle ((spanPair_rank _ _ hX).trans hdim.symm),
    Submodule.eq_of_le_of_finrank_eq hcle ((spanPair_rank _ _ hc).trans hdim.symm)⟩

private theorem complements (i j : Fin 4) (hij : i ≠ j) :
    ∃ k h : Fin 4, k ≠ i ∧ k ≠ j ∧ h ≠ i ∧ h ≠ j ∧ k ≠ h := by
  fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | decide

theorem actual_corner_diagonal_ne_zero (d : NativeSupportCorners) (i : Fin 4) :
    B (d.cap i) (d.side i) ≠ 0 := by
  intro hdiag
  let j : Fin 4 := if i = 0 then 1 else 0
  have hij : i ≠ j := by
    dsimp [j]
    split_ifs with hi
    · subst i; decide
    · exact hi
  obtain ⟨k, h, hki, hkj, hhi, hhj, hkh⟩ := complements i j hij
  have hex := actual_corner_ridge_extraction d i j k h hij hki hkj hhi hhj hkh
  have hZi : lift (d.corner j i) ∈ spanPair (d.cap i) (d.cap j) := by
    rw [hex.cap_span, ← hex.endpoint_span]
    exact Submodule.subset_span (by simp)
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hZi
  have hzero : B (lift (d.corner j i)) (d.side i) = 0 := by
    rw [← hab, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left,
      hdiag, d.orthogonal_incidence j i hij.symm]
    ring
  have hstrict := side_strict d j i i hij.symm (by simp)
  rw [B_symm] at hzero
  linarith

theorem actual_corner_cap_independent (d : NativeSupportCorners) :
    LinearIndependent ℝ d.cap := by
  let f : Fin 4 → Module.Dual ℝ V := fun i =>
    (B (d.cap i) (d.side i))⁻¹ • B (d.side i)
  apply LinearIndependent.of_pairwise_dual_eq_zero_one d.cap f
  · intro i j hij
    change (B (d.cap i) (d.side i))⁻¹ * B (d.side i) (d.cap j) = 0
    rw [B_symm (d.side i) (d.cap j), d.orthogonal_incidence j i hij.symm, mul_zero]
  · intro i
    change (B (d.cap i) (d.side i))⁻¹ * B (d.side i) (d.cap i) = 1
    rw [B_symm (d.side i) (d.cap i)]
    exact inv_mul_cancel₀ (actual_corner_diagonal_ne_zero d i)

theorem actual_corner_side_independent (d : NativeSupportCorners) :
    LinearIndependent ℝ d.side := by
  let f : Fin 4 → Module.Dual ℝ V := fun i =>
    (B (d.cap i) (d.side i))⁻¹ • B (d.cap i)
  apply LinearIndependent.of_pairwise_dual_eq_zero_one d.side f
  · intro i j hij
    change (B (d.cap i) (d.side i))⁻¹ * B (d.cap i) (d.side j) = 0
    rw [d.orthogonal_incidence i j hij, mul_zero]
  · intro i
    change (B (d.cap i) (d.side i))⁻¹ * B (d.cap i) (d.side i) = 1
    exact inv_mul_cancel₀ (actual_corner_diagonal_ne_zero d i)

theorem actual_corner_cap_det_ne_zero (d : NativeSupportCorners) :
    Matrix.det (Matrix.of d.cap) ≠ 0 := by
  have hrows : LinearIndependent ℝ (Matrix.of d.cap).row := by
    change LinearIndependent ℝ d.cap
    exact actual_corner_cap_independent d
  have hunit : IsUnit (Matrix.of d.cap) :=
    (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of d.cap)).mp hrows
  have hdet : IsUnit (Matrix.det (Matrix.of d.cap)) :=
    (Matrix.isUnit_iff_isUnit_det (Matrix.of d.cap)).mp hunit
  exact isUnit_iff_ne_zero.mp hdet

theorem actual_corner_length_positive (d : NativeSupportCorners)
    (i j : Fin 4) (hij : i ≠ j) :
    0 < dist (d.corner i j) (d.corner j i) :=
  dist_pos.mpr (corners_ne d i j hij)

/-! Transient source-only metric bridge. The carrier's statements and original
proof suppliers are preserved, with elaboration repairs above. This entire file
is UNCOMPILED and temporary; zero declarations are retained as repository API. -/

/-- Transient bind-only coefficient solve in a Lorentz two-plane. The sign of
`B u Y` selects the oriented unit normal, rather than its negative. -/
private theorem oriented_span_normal (X Y u : V) (c : ℝ)
    (hc : 1 < c) (hXX : B X X = -1) (hYY : B Y Y = -1)
    (hXY : B X Y = -c) (hu : u ∈ spanPair X Y)
    (huu : B u u = 1) (huX : B u X = 0) (huY : B u Y < 0) :
    u = (c / Real.sqrt (c ^ 2 - 1)) • X -
      (1 / Real.sqrt (c ^ 2 - 1)) • Y := by
  let s := Real.sqrt (c ^ 2 - 1)
  have hz : 0 < c ^ 2 - 1 := by nlinarith only [hc]
  have hs : 0 < s := Real.sqrt_pos.mpr hz
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hs2 : s ^ 2 = c ^ 2 - 1 := Real.sq_sqrt hz.le
  have hYX : B Y X = -c := (B_symm Y X).trans hXY
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hu
  have horth : a * (-1) + b * (-c) = 0 := by
    have h := huX
    rw [← hab, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left,
      hXX, hYX] at h
    exact h
  have ha : a = -(b * c) := by linarith only [horth]
  have hnorm : a * a * (-1) + a * b * (-c) +
      b * a * (-c) + b * b * (-1) = 1 := by
    calc
      _ = B (a • X + b • Y) (a • X + b • Y) := by
        rw [B_apply, lorentz_linear]
        simp only [← B_apply, hXX, hYY, hXY, hYX]
      _ = 1 := by simpa only [hab] using huu
  have hb2 : b ^ 2 * (c ^ 2 - 1) = 1 := by
    rw [ha] at hnorm
    nlinarith only [hnorm]
  have hcross : a * (-c) + b * (-1) < 0 := by
    have h := huY
    rw [← hab, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left,
      hXY, hYY] at h
    exact h
  have hbz : b * (c ^ 2 - 1) < 0 := by
    rw [ha] at hcross
    nlinarith only [hcross]
  have hbneg : b < 0 := by
    by_contra hn
    have hb0 : 0 ≤ b := le_of_not_gt hn
    have hnonneg := mul_nonneg hb0 hz.le
    linarith only [hnonneg, hbz]
  have hbsneg : b * s < 0 := mul_neg_of_neg_of_pos hbneg hs
  have hbs2 : (b * s) ^ 2 = 1 := by
    rw [mul_pow, hs2]
    exact hb2
  have hfactor : (b * s - 1) * (b * s + 1) = 0 := by
    nlinarith only [hbs2]
  have hbs : b * s = -1 := by
    rcases mul_eq_zero.mp hfactor with hplus | hminus
    · linarith only [hplus, hbsneg]
    · linarith only [hminus]
  have hb : b = -1 / s := (eq_div_iff hs0).mpr hbs
  have ha' : a = c / s := by
    rw [ha, hb]
    ring
  change u = (c / s) • X - (1 / s) • Y
  rw [← hab, ha', hb]
  simp only [sub_eq_add_neg, neg_div, neg_smul]

/-- Transient native binding: both oriented caps are recovered from the actual
paired endpoints. No cap-pair product is supplied as a hypothesis. -/
theorem actual_corner_oriented_caps (d : NativeSupportCorners)
    (i j : Fin 4) (hij : i ≠ j) :
    let X := lift (d.corner i j)
    let Y := lift (d.corner j i)
    let c := Real.cosh (dist (d.corner i j) (d.corner j i))
    let s := Real.sqrt (c ^ 2 - 1)
    1 < c ∧ 0 < s ∧
      d.cap i = (c / s) • X - (1 / s) • Y ∧
      d.cap j = (c / s) • Y - (1 / s) • X := by
  let X := lift (d.corner i j)
  let Y := lift (d.corner j i)
  let c := Real.cosh (dist (d.corner i j) (d.corner j i))
  let s := Real.sqrt (c ^ 2 - 1)
  change 1 < c ∧ 0 < s ∧
    d.cap i = (c / s) • X - (1 / s) • Y ∧
    d.cap j = (c / s) • Y - (1 / s) • X
  have hc : 1 < c :=
    Real.one_lt_cosh.mpr (ne_of_gt (actual_corner_length_positive d i j hij))
  have hz : 0 < c ^ 2 - 1 := by nlinarith only [hc]
  have hs : 0 < s := Real.sqrt_pos.mpr hz
  have hXX : B X X = -1 := lift_norm (d.corner i j)
  have hYY : B Y Y = -1 := lift_norm (d.corner j i)
  have hXY : B X Y = -c := by
    change B (lift (d.corner i j)) (lift (d.corner j i)) = -c
    rw [B_apply]
    exact lift_cosh (d.corner i j) (d.corner j i)
  have hYX : B Y X = -c := (B_symm Y X).trans hXY
  obtain ⟨k, h, hki, hkj, hhi, hhj, hkh⟩ := complements i j hij
  have hex := actual_corner_ridge_extraction d i j k h hij hki hkj hhi hhj hkh
  have hi : d.cap i ∈ spanPair X Y := by
    change d.cap i ∈ spanPair (lift (d.corner i j)) (lift (d.corner j i))
    rw [hex.endpoint_span, ← hex.cap_span]
    exact Submodule.subset_span (by simp)
  have hj : d.cap j ∈ spanPair Y X := by
    have hj' : d.cap j ∈ spanPair X Y := by
      change d.cap j ∈ spanPair (lift (d.corner i j)) (lift (d.corner j i))
      rw [hex.endpoint_span, ← hex.cap_span]
      exact Submodule.subset_span (by simp)
    simpa only [spanPair, Set.pair_comm] using hj'
  refine ⟨hc, hs, ?_, ?_⟩
  · exact oriented_span_normal X Y (d.cap i) c hc hXX hYY hXY hi
      (d.cap_unit i) ((cap_zero_iff d i j i hij).mpr rfl)
      (cap_strict d j i i hij.symm hij)
  · exact oriented_span_normal Y X (d.cap j) c hc hYY hXX hYX hj
      (d.cap_unit j) ((cap_zero_iff d j i j hij.symm).mpr rfl)
      (cap_strict d i j j hij hij.symm)

/-- Transient bind-only bilinear expansion of the two oriented formulas. -/
theorem actual_corner_cap_pair (d : NativeSupportCorners)
    (i j : Fin 4) (hij : i ≠ j) :
    B (d.cap i) (d.cap j) =
      -Real.cosh (dist (d.corner i j) (d.corner j i)) := by
  let X := lift (d.corner i j)
  let Y := lift (d.corner j i)
  let c := Real.cosh (dist (d.corner i j) (d.corner j i))
  let s := Real.sqrt (c ^ 2 - 1)
  obtain ⟨hc, hs, hi, hj⟩ := actual_corner_oriented_caps d i j hij
  change 1 < c at hc
  change 0 < s at hs
  change d.cap i = (c / s) • X - (1 / s) • Y at hi
  change d.cap j = (c / s) • Y - (1 / s) • X at hj
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hz : 0 < c ^ 2 - 1 := by nlinarith only [hc]
  have hs2 : s ^ 2 = c ^ 2 - 1 := Real.sq_sqrt hz.le
  have hXX : B X X = -1 := lift_norm (d.corner i j)
  have hYY : B Y Y = -1 := lift_norm (d.corner j i)
  have hXY : B X Y = -c := by
    change B (lift (d.corner i j)) (lift (d.corner j i)) = -c
    rw [B_apply]
    exact lift_cosh (d.corner i j) (d.corner j i)
  have hYX : B Y X = -c := (B_symm Y X).trans hXY
  have hc2 : c * s ^ 2 = c * (c ^ 2 - 1) :=
    congrArg (fun t : ℝ => c * t) hs2
  change B (d.cap i) (d.cap j) = -c
  rw [hi, hj]
  simp only [sub_eq_add_neg, ← neg_smul]
  rw [B_apply, lorentz_linear]
  simp only [← B_apply, hXX, hYY, hXY, hYX]
  field_simp [hs0] <;> nlinarith only [hs2, hc2]

/-- Transient actual metric data, in the original order 01,02,03,23,13,12. -/
def actualLengths (d : NativeSupportCorners) : Fin 6 → ℝ :=
  ![dist (d.corner 0 1) (d.corner 1 0),
    dist (d.corner 0 2) (d.corner 2 0),
    dist (d.corner 0 3) (d.corner 3 0),
    dist (d.corner 2 3) (d.corner 3 2),
    dist (d.corner 1 3) (d.corner 3 1),
    dist (d.corner 1 2) (d.corner 2 1)]

/-- Transient bind-only finite assembly of the carrier's strict lengths. -/
theorem actualLengths_positive (d : NativeSupportCorners) :
    ∀ k, 0 < actualLengths d k := by
  intro k
  fin_cases k
  · exact actual_corner_length_positive d 0 1 (by decide)
  · exact actual_corner_length_positive d 0 2 (by decide)
  · exact actual_corner_length_positive d 0 3 (by decide)
  · exact actual_corner_length_positive d 2 3 (by decide)
  · exact actual_corner_length_positive d 1 3 (by decide)
  · exact actual_corner_length_positive d 1 2 (by decide)

/-- Transient literal Gram-entry identity. Reversed ordered endpoints use the
symmetry of the actual metric, and diagonal entries use `cap_unit`. -/
theorem actual_corner_cap_gram_entries (d : NativeSupportCorners) :
    (fun i j => B (d.cap i) (d.cap j)) = lengthGram (actualLengths d) := by
  funext i j
  by_cases hij : i = j
  · subst j
    rw [d.cap_unit]
    fin_cases i <;> simp [lengthGram]
  · rw [actual_corner_cap_pair d i j hij]
    fin_cases i <;> fin_cases j <;>
      simp_all [lengthGram, actualLengths, dist_comm] <;>
      exact congrArg Real.cosh (dist_comm _ _)

/-- Transient matrix assembly with cap vectors as ROWS, so the congruence is
`C * J * C.transpose`. This statement makes no determinant or inverse claim. -/
theorem actual_corner_cap_matrix (d : NativeSupportCorners) :
    Matrix.of d.cap * J * Matrix.transpose (Matrix.of d.cap) =
        lengthGram (actualLengths d) := by
  have hrows (i j : Fin 4) :
      (Matrix.of d.cap * J * Matrix.transpose (Matrix.of d.cap)) i j =
      B (d.cap i) (d.cap j) := by
    rw [B_apply]
    simp [J, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
      Matrix.of_apply, lorentz, Fin.sum_univ_succ]
    <;> ring
  ext i j
  rw [hrows]
  exact congrFun (congrFun (actual_corner_cap_gram_entries d) i) j

end NativeCornerExtractionSource

#check NativeCornerExtractionSource.actual_corner_ridge_extraction
#print axioms NativeCornerExtractionSource.actual_corner_ridge_extraction
#check NativeCornerExtractionSource.actual_corner_diagonal_ne_zero
#print axioms NativeCornerExtractionSource.actual_corner_diagonal_ne_zero
#check NativeCornerExtractionSource.actual_corner_cap_independent
#print axioms NativeCornerExtractionSource.actual_corner_cap_independent
#check NativeCornerExtractionSource.actual_corner_side_independent
#print axioms NativeCornerExtractionSource.actual_corner_side_independent
#check NativeCornerExtractionSource.actual_corner_cap_det_ne_zero
#print axioms NativeCornerExtractionSource.actual_corner_cap_det_ne_zero
#check NativeCornerExtractionSource.actual_corner_length_positive
#print axioms NativeCornerExtractionSource.actual_corner_length_positive
#check NativeCornerExtractionSource.actual_corner_oriented_caps
#print axioms NativeCornerExtractionSource.actual_corner_oriented_caps
#check NativeCornerExtractionSource.actual_corner_cap_pair
#print axioms NativeCornerExtractionSource.actual_corner_cap_pair
#check NativeCornerExtractionSource.actualLengths
#print axioms NativeCornerExtractionSource.actualLengths
#check NativeCornerExtractionSource.actualLengths_positive
#print axioms NativeCornerExtractionSource.actualLengths_positive
#check NativeCornerExtractionSource.actual_corner_cap_gram_entries
#print axioms NativeCornerExtractionSource.actual_corner_cap_gram_entries
#check NativeCornerExtractionSource.actual_corner_cap_matrix
#print axioms NativeCornerExtractionSource.actual_corner_cap_matrix
