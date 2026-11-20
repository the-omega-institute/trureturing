/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ThinSliceGrayReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ThinSliceGrayReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fintype]
   utility: none
   digest: Reconstruction of an actual balanced cubic cube support from a thin coordinate half. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ThinCoordinateSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicalSubdivisionRigidity
import D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import Mathlib.Logic.Equiv.Fintype

/-! The actual thin half determines a total signed comparison with the Gray support. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ThinSliceGrayReconstruction

open scoped BigOperators
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsSwitching IsBalanced switchingVector)
local notation "flip" => BalancedCriticalSpectrum.flip
open CubicalSubdivisionRigidity (gridHigh gridMiddle gridSupport)
open BalancedCubeLowerBound (coordinateSlice)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_row edge from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open BalancedCubeGirth (flip_comm)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open BalancedCriticalSpectrum (switching_sq)
open private flip_value from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicalSubdivisionRigidity

private def standardOrigin : Q 9 :=
  fun q => !decide ((@finProdFinEquiv 3 3).symm q = ((2 : Fin 3), (2 : Fin 3)))

private def standardDirection (h : Bool × Fin 3) : Fin 9 :=
  finProdFinEquiv ((if h.1 then 1 else 0 : Fin 3), h.2)

private def standardRoot : Q 9 := flip standardOrigin (standardDirection (false, 0))

private theorem standard_high (h : Bool × Fin 3) :
    gridHigh standardRoot standardDirection h = flip standardOrigin (standardDirection h) := by
  simp [gridHigh, standardRoot]

private theorem standard_middle (i j : Fin 3) :
    gridMiddle standardRoot standardDirection (i, j) =
      flip (flip standardOrigin (standardDirection (false, i))) (standardDirection (true, j)) := by
  rw [gridMiddle, standard_high]

private theorem standard_point (f : GrayGridComponent.PointData 3) (hf : f 2 = 2) :
    GrayGridComponent.point f =
      gridMiddle standardRoot standardDirection (f 0, f 1) := by
  rw [standard_middle]
  funext q
  obtain ⟨⟨r, c⟩, rfl⟩ := finProdFinEquiv.surjective q
  fin_cases r <;>
    simp [GrayGridComponent.point, flip_value, standardOrigin,
      standardDirection, hf]

private theorem standard_line (p : GrayGridComponent.LineData 3)
    (hp : GrayGridComponent.line p 8 = false) :
    ∃ h, GrayGridComponent.line p = gridHigh standardRoot standardDirection h := by
  change (if h : (2 : Fin 3) = p.1 then true else !decide ((2 : Fin 3) = p.2 ⟨2, h⟩)) = false at hp
  have hb : (2 : Fin 3) ≠ p.1 := by
    intro he
    rw [dite_eq_left he] at hp
    contradiction
  rw [dite_eq_right hb] at hp
  have hf : p.2 ⟨2, hb⟩ = 2 := by
    exact (of_decide_eq_true (Bool.eq_true_of_not_eq_false' hp)).symm
  rcases p with ⟨r, f⟩
  fin_cases r
  · change f ⟨2, by decide⟩ = 2 at hf
    refine ⟨(true, f ⟨1, by decide⟩), ?_⟩
    rw [standard_high]
    funext q
    obtain ⟨⟨r, c⟩, rfl⟩ := finProdFinEquiv.surjective q
    fin_cases r <;>
      simp [GrayGridComponent.line, flip_value, standardOrigin,
        standardDirection, hf]
  · change f ⟨2, by decide⟩ = 2 at hf
    refine ⟨(false, f ⟨0, by decide⟩), ?_⟩
    rw [standard_high]
    funext q
    obtain ⟨⟨r, c⟩, rfl⟩ := finProdFinEquiv.surjective q
    fin_cases r <;>
      simp [GrayGridComponent.line, flip_value, standardOrigin,
        standardDirection, hf]
  · exact (hb rfl).elim

private theorem standard_high_mem (h : Bool × Fin 3) :
    gridHigh standardRoot standardDirection h ∈ GrayGridComponent.support 3 ∧
      gridHigh standardRoot standardDirection h 8 = false := by
  let p : GrayGridComponent.LineData 3 :=
    ⟨if h.1 then 0 else 1, fun r => if r.val = 2 then 2 else h.2⟩
  have he : gridHigh standardRoot standardDirection h = GrayGridComponent.line p := by
    rw [standard_high]
    funext q
    obtain ⟨⟨r, c⟩, rfl⟩ := (@finProdFinEquiv 3 3).surjective q
    rcases h with ⟨s, i⟩
    cases s <;> fin_cases r <;>
      simp [p, GrayGridComponent.line, flip_value, standardOrigin,
        standardDirection]
  rw [he]
  constructor
  · simp [GrayGridComponent.support]
  · rcases h with ⟨s, i⟩
    cases s <;> simp [GrayGridComponent.line, p,
      show finProdFinEquiv.symm (8 : Fin 9) = ((2 : Fin 3), (2 : Fin 3)) from rfl]

private theorem standard_middle_mem (i j : Fin 3) :
    gridMiddle standardRoot standardDirection (i, j) ∈ GrayGridComponent.support 3 ∧
      gridMiddle standardRoot standardDirection (i, j) 8 = false := by
  let f : GrayGridComponent.PointData 3 := ![i, j, 2]
  have he := standard_point f (by simp [f])
  have he' : GrayGridComponent.point f =
      gridMiddle standardRoot standardDirection (i, j) := by simpa [f] using he
  rw [← he']
  constructor
  · simp [GrayGridComponent.support]
  · simp [GrayGridComponent.point, f,
      show finProdFinEquiv.symm (8 : Fin 9) = ((2 : Fin 3), (2 : Fin 3)) from rfl]

private theorem standard_half (x : Q 9) :
    x ∈ GrayGridComponent.support 3 ∧ x 8 = false ↔
      x ∈ gridSupport standardRoot standardDirection := by
  constructor
  · rintro ⟨hx, hb⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hx
      have hf : f 2 = 2 := by
        change (!decide ((2 : Fin 3) = f 2)) = false at hb
        exact (of_decide_eq_true (Bool.eq_true_of_not_eq_false' hb)).symm
      rw [standard_point f hf]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(f 0, f 1), Finset.mem_univ _, rfl⟩)
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨h, he⟩ := standard_line p hb
      rw [he]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨h, Finset.mem_univ _, rfl⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hx
      exact standard_high_mem h
    · obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hx
      exact standard_middle_mem i j

private theorem directions_avoid_cut (C : Finset (Q 9)) (b : Bool)
    (X : Q 9) (d : Bool × Fin 3 → Fin 9)
    (hS : coordinateSlice C b = gridSupport X d) :
    (∀ h, d h ≠ 0) ∧ (flip X (d (false, 0))) 0 = b := by
  let O := flip X (d (false, 0))
  have hH (h : Bool × Fin 3) : (flip O (d h)) 0 = b := by
    have hx : gridHigh X d h ∈ coordinateSlice C b := by
      rw [hS]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨h, Finset.mem_univ _, rfl⟩)
    exact (Finset.mem_filter.mp hx).2
  have hM (i j : Fin 3) : (flip (flip O (d (false, i))) (d (true, j))) 0 = b := by
    have hx : gridMiddle X d (i, j) ∈ coordinateSlice C b := by
      rw [hS]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact (Finset.mem_filter.mp hx).2
  have hd (h : Bool × Fin 3) : d h ≠ 0 := by
    rcases h with ⟨s, i⟩
    cases s
    · intro he
      have hh := hM i 0
      rw [flip_comm, he, BalancedCriticalSpectrum.flip_apply_same, hH] at hh
      cases b <;> simp_all
    · intro he
      have hh := hM 0 i
      rw [he, BalancedCriticalSpectrum.flip_apply_same, hH] at hh
      cases b <;> simp_all
  refine ⟨hd, ?_⟩
  change O 0 = b
  simpa only [BalancedCriticalSpectrum.flip, Function.update_of_ne
    (hd (false, 0)).symm] using hH (false, 0)

private theorem extend_directions (d : Bool × Fin 3 → Fin 9)
    (hd : Function.Injective d) (hz : ∀ h, d h ≠ 0) :
    ∃ pi : Fin 9 ≃ Fin 9, (∀ h, pi (standardDirection h) = d h) ∧ pi 8 = 0 := by
  let f : Option (Bool × Fin 3) → Fin 9 := fun h => h.elim 8 standardDirection
  let t : Option (Bool × Fin 3) → Fin 9 := fun h => h.elim 0 d
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        rcases b with ⟨s, i⟩
        cases s <;> simp [f, standardDirection, finProdFinEquiv, Fin.ext_iff] at hab
        all_goals omega
    | some a =>
      cases b with
      | none =>
        rcases a with ⟨s, i⟩
        cases s <;> simp [f, standardDirection, finProdFinEquiv, Fin.ext_iff] at hab
        all_goals omega
      | some b =>
        apply congrArg some
        have he := finProdFinEquiv.injective hab
        rcases a with ⟨s, i⟩; rcases b with ⟨r, j⟩
        cases s <;> cases r <;> simp_all [f, standardDirection]
  have ht : Function.Injective t := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact (hz b hab.symm).elim
    | some a =>
      cases b with
      | none => exact (hz a hab).elim
      | some b => exact congrArg some (hd hab)
  obtain ⟨pi, hp⟩ := Equiv.Perm.exists_extending_pair f t hf ht
  exact ⟨pi, fun h => hp (some h), hp none⟩

private def affineCube (pi : Fin 9 ≃ Fin 9) (O : Q 9) : Q 9 ≃ Q 9 where
  toFun x k := (x (pi.symm k) ^^ standardOrigin (pi.symm k)) ^^ O k
  invFun y i := (y (pi i) ^^ O (pi i)) ^^ standardOrigin i
  left_inv x := by
    funext i
    simp
  right_inv y := by
    funext k
    simp

private theorem affine_flip (pi : Fin 9 ≃ Fin 9) (O : Q 9) (x : Q 9) (i : Fin 9) :
    affineCube pi O (flip x i) = flip (affineCube pi O x) (pi i) := by
  funext k
  by_cases hk : k = pi i
  · subst k
    simp [affineCube, BalancedCriticalSpectrum.flip]
  · have hi : pi.symm k ≠ i := by
      intro he
      exact hk (by simpa using congrArg pi he)
    simp [affineCube, BalancedCriticalSpectrum.flip, hk, hi]

private theorem affine_origin (pi : Fin 9 ≃ Fin 9) (O : Q 9) :
    affineCube pi O standardOrigin = O := by
  funext k
  simp [affineCube]

private theorem geometric_comparison (C : Finset (Q 9)) (b : Bool)
    (X : Q 9) (d : Bool × Fin 3 → Fin 9) (hd : Function.Injective d)
    (hS : coordinateSlice C b = gridSupport X d) :
    ∃ (g : Q 9 ≃ Q 9) (pi : Fin 9 ≃ Fin 9),
      (∀ x i, g (flip x i) = flip (g x) (pi i)) ∧
      (∀ x, (g x) 0 = b ↔ x 8 = false) ∧
      (∀ y, y ∈ coordinateSlice C b ↔
        g.symm y ∈ GrayGridComponent.support 3 ∧ (g.symm y) 8 = false) := by
  obtain ⟨hz, hO⟩ := directions_avoid_cut C b X d hS
  obtain ⟨pi, hp, hcut⟩ := extend_directions d hd hz
  let O := flip X (d (false, 0))
  let g := affineCube pi O
  have hg : ∀ x i, g (flip x i) = flip (g x) (pi i) := affine_flip pi O
  have hhigh (h : Bool × Fin 3) :
      g (gridHigh standardRoot standardDirection h) = gridHigh X d h := by
    rw [standard_high, hg, hp, affine_origin]
    rfl
  have hmid (ij : Fin 3 × Fin 3) :
      g (gridMiddle standardRoot standardDirection ij) = gridMiddle X d ij := by
    rw [gridMiddle, hg, hhigh, hp]
    rfl
  have himage : (gridSupport standardRoot standardDirection).image g = gridSupport X d := by
    simp only [gridSupport, Finset.image_union, Finset.image_image,
      Function.comp_def, hhigh, hmid]
  refine ⟨g, pi, hg, ?_, ?_⟩
  · intro x
    have hi : pi.symm 0 = 8 := (pi.symm_apply_eq).mpr hcut.symm
    change (((x (pi.symm 0) ^^ standardOrigin (pi.symm 0)) ^^ O 0) = b) ↔ _
    change O 0 = b at hO
    rw [hi, show standardOrigin 8 = false from rfl, hO]
    cases b <;> cases x 8 <;> decide
  · intro y
    rw [hS, ← himage, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [Equiv.symm_apply_apply] using (standard_half x).mpr hx
    · intro hy
      exact ⟨g.symm y, (standard_half _).mp hy, g.apply_symm_apply y⟩

private theorem eigenvector_half_unique {n : ℕ} (u v : Q n → ℝ) (a : ℝ)
    (k : Fin n) (b : Bool)
    (hu : (huangMatrix n).mulVec u = a • u)
    (hv : (huangMatrix n).mulVec v = a • v)
    (hh : ∀ x, x k = b → u x = v x) : u = v := by
  funext x
  by_cases hx : x k = b
  · exact hh x hx
  · let y := flip x k
    have hy : y k = b := by
      simp only [y, BalancedCriticalSpectrum.flip_apply_same]
      cases h : x k <;> cases b <;> simp_all
    have he : ∑ i : Fin n, edge y i * u (flip y i) =
        ∑ i : Fin n, edge y i * v (flip y i) := by
      rw [← matrix_row, ← matrix_row, hu, hv]
      simp only [Pi.smul_apply, smul_eq_mul, hh y hy]
    have hr : ∀ i ∈ Finset.univ.erase k,
        edge y i * u (flip y i) = edge y i * v (flip y i) := by
      intro i hi
      rw [hh (flip y i) (by
        simpa [BalancedCriticalSpectrum.flip,
          (Finset.mem_erase.mp hi).1.symm] using hy)]
    have hs := Finset.sum_congr rfl hr
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hs] at he
    have he' : edge y k * u x = edge y k * v x := by
      simpa only [y, BalancedCriticalSpectrum.flip_flip] using add_left_cancel he
    have hn : edge y k ≠ 0 := by
      have h := SupportedEigenSaturation.matrix_sq_of_adj
        (BalancedCriticalSpectrum.flip_adj y k)
      change edge y k ^ 2 = 1 at h
      intro hz
      rw [hz] at h
      norm_num at h
    exact mul_left_cancel₀ hn he'

private theorem switching_grid_alignment (X : Q 9) (d : Bool × Fin 3 → Fin 9)
    (s t : Q 9 → ℝ) (hs : IsSwitching (gridSupport X d) s)
    (ht : IsSwitching (gridSupport X d) t) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ ∀ x ∈ gridSupport X d, s x = c * t x := by
  let q := fun x => s x * t x
  have hH (h : Bool × Fin 3) : gridHigh X d h ∈ gridSupport X d :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨h, Finset.mem_univ _, rfl⟩)
  have hM (i j : Fin 3) : gridMiddle X d (i, j) ∈ gridSupport X d :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  have hedge {x y : Q 9} (hx : x ∈ gridSupport X d) (hy : y ∈ gridSupport X d)
      (hxy : (hypercube 9).Adj x y) : q x = q y := by
    have he : s x * s y = t x * t y := (hs.2 x hx y hy hxy).symm.trans
      (ht.2 x hx y hy hxy)
    calc
      q x = s x * t x * (s y) ^ 2 := by rw [switching_sq hs hy, mul_one]
      _ = (s x * s y) * (s y * t x) := by ring
      _ = (t x * t y) * (s y * t x) := by rw [he]
      _ = (t x) ^ 2 * q y := by dsimp [q]; ring
      _ = q y := by rw [switching_sq ht hx, one_mul]
  have hAM (i j : Fin 3) :
      q (gridHigh X d (false, i)) = q (gridMiddle X d (i, j)) :=
    hedge (hH _) (hM _ _) (BalancedCriticalSpectrum.flip_adj _ _)
  have hBM (i j : Fin 3) :
      q (gridHigh X d (true, j)) = q (gridMiddle X d (i, j)) := by
    apply hedge (hH _) (hM _ _)
    have he : gridMiddle X d (i, j) =
        flip (gridHigh X d (true, j)) (d (false, i)) := by
      exact flip_comm _ _ _
    rw [he]
    exact BalancedCriticalSpectrum.flip_adj _ _
  let c := q (gridHigh X d (false, 0))
  have hB (j : Fin 3) : q (gridHigh X d (true, j)) = c :=
    (hBM 0 j).trans (hAM 0 j).symm
  have hA (i : Fin 3) : q (gridHigh X d (false, i)) = c :=
    (hAM i 0).trans ((hBM i 0).symm.trans (hB 0))
  refine ⟨c, ?_, ?_⟩
  · dsimp [c, q]
    rw [mul_pow, switching_sq hs (hH _), switching_sq ht (hH _), mul_one]
  · intro x hx
    have hq : q x = c := by
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨⟨s, i⟩, _, rfl⟩ := Finset.mem_image.mp hx
        cases s
        · exact hA i
        · exact hB i
      · obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hx
        exact (hAM i j).symm.trans (hA i)
    calc
      s x = s x * (t x) ^ 2 := by rw [switching_sq ht hx, mul_one]
      _ = q x * t x := by dsimp [q]; ring
      _ = c * t x := by rw [hq]

private theorem transported_switching (g : Q 9 ≃ Q 9) (pi : Fin 9 ≃ Fin 9)
    (hg : ∀ x i, g (flip x i) = flip (g x) (pi i))
    (theta : Q 9 → ℝ) (hunit : ∀ x, theta x = 1 ∨ theta x = -1)
    (hedge : ∀ x i, huangMatrix 9 (g x) (g (flip x i)) =
      theta x * huangMatrix 9 x (flip x i) * theta (flip x i)) :
    IsSwitching ((GrayGridComponent.support 3).image g)
      (fun y => theta (g.symm y) * GrayGridComponent.switching 3 (g.symm y)) := by
  have hs := GrayGridComponent.support_isSwitching 3
  have hmem (y : Q 9) : y ∈ (GrayGridComponent.support 3).image g ↔
      g.symm y ∈ GrayGridComponent.support 3 := by
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      simpa using hx
    · intro hy
      exact Finset.mem_image.mpr ⟨g.symm y, hy, g.apply_symm_apply y⟩
  constructor
  · intro y hy
    rcases hunit (g.symm y) with h | h <;>
      rcases hs.1 (g.symm y) ((hmem y).mp hy) with ht | ht <;> simp [h, ht]
  · intro x hx y hy hxy
    obtain ⟨j, hj⟩ := adjacent_exists_flip hxy
    let i := pi.symm j
    have he : y = g (flip (g.symm x) i) := by
      rw [hg, g.apply_symm_apply]
      simpa [i] using hj
    have hed := hedge (g.symm x) i
    rw [g.apply_symm_apply x] at hed
    rw [he]
    dsimp only
    simp only [g.symm_apply_apply]
    have hys : flip (g.symm x) i ∈ GrayGridComponent.support 3 := by
      have := (hmem y).mp hy
      simpa only [he, g.symm_apply_apply] using this
    rw [hed, hs.2 (g.symm x) ((hmem x).mp hx) _ hys
      (BalancedCriticalSpectrum.flip_adj _ _)]
    ring

set_option maxHeartbeats 400000 in
-- The total cube construction and full spectral transport elaborate in one proof.
/-- A thin actual coordinate half forces the entire original balanced cubic
support to be a genuine cube-symmetry image of the Gray incidence support. -/
theorem thin_slice_gray_reconstruction {C : Finset (Q 9)} (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card ≤ 16) :
    ∃ (g : Q 9 ≃ Q 9) (pi : Fin 9 ≃ Fin 9),
      (∀ x i, g (flip x i) = flip (g x) (pi i)) ∧
      C = (GrayGridComponent.support 3).image g := by
  obtain ⟨_, _, hsub⟩ := ThinCoordinateSlice.thin_coordinate_slice hC hr hb b hs
  obtain ⟨X, d, hd, hS, _⟩ :=
    CubicalSubdivisionRigidity.cubical_subdivision_normal_form (coordinateSlice C b) hsub
  obtain ⟨g, pi, hg, hcut, hhalf⟩ := geometric_comparison C b X d hd hS
  obtain ⟨theta, htheta, hedge, hcov⟩ := HuangCubeCovariance.exists_signed_covariance g pi hg
  let T := (GrayGridComponent.support 3).image g
  let t := fun y => theta (g.symm y) * GrayGridComponent.switching 3 (g.symm y)
  have ht : IsSwitching T t := transported_switching g pi hg theta htheta hedge
  obtain ⟨s, hswitch⟩ := hb
  have hST (y : Q 9) (hy : y ∈ coordinateSlice C b) : y ∈ T :=
    Finset.mem_image.mpr ⟨g.symm y, ((hhalf y).mp hy).1, g.apply_symm_apply y⟩
  have hsS : IsSwitching (gridSupport X d) s := by
    rw [← hS]
    exact ⟨fun y hy => hswitch.1 y (Finset.mem_filter.mp hy).1,
      fun x hx y hy hxy => hswitch.2 x (Finset.mem_filter.mp hx).1
        y (Finset.mem_filter.mp hy).1 hxy⟩
  have htS : IsSwitching (gridSupport X d) t := by
    rw [← hS]
    exact ⟨fun y hy => ht.1 y (hST y hy),
      fun x hx y hy hxy => ht.2 x (hST x hx) y (hST y hy) hxy⟩
  obtain ⟨c, hc, halign⟩ := switching_grid_alignment X d s t hsS htS
  let z := switchingVector C s
  let w := switchingVector T t
  have hwpush : w = fun y => theta (g.symm y) *
      switchingVector (GrayGridComponent.support 3) (GrayGridComponent.switching 3) (g.symm y) := by
    funext y
    have hm : y ∈ T ↔ g.symm y ∈ GrayGridComponent.support 3 := by
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        simpa using hx
      · intro hy
        exact Finset.mem_image.mpr ⟨g.symm y, hy, g.apply_symm_apply y⟩
    simp [w, switchingVector, hm, t, mul_ite]
  have hz : (huangMatrix 9).mulVec z = (3 : ℝ) • z :=
    BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C s hr hswitch
  have hw : (huangMatrix 9).mulVec w = (3 : ℝ) • w := by
    rw [hwpush, hcov, BalancedCriticalSpectrum.ambient_eigenvector
      (GrayGridComponent.support 3) (GrayGridComponent.switching 3)
      (GrayGridComponent.component_regular 3) (GrayGridComponent.support_isSwitching 3)]
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hwhole : z = c • w := by
    apply eigenvector_half_unique z (c • w) 3 0 b hz
    · rw [Matrix.mulVec_smul, hw, smul_comm]
    · intro y hy
      have hys : y ∈ coordinateSlice C b ↔ y ∈ C := by
        simp [coordinateSlice, hy]
      have hyt : y ∈ T ↔ y ∈ C := by
        have hi : (g.symm y) 8 = false := (hcut _).mp (by simpa using hy)
        rw [← hys, hhalf]
        simpa only [hi, and_true] using
          (show y ∈ T ↔ g.symm y ∈ GrayGridComponent.support 3 from by
            constructor
            · intro h
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
              simpa using hx
            · intro h
              exact Finset.mem_image.mpr ⟨g.symm y, h, g.apply_symm_apply y⟩)
      by_cases hyC : y ∈ C
      · have he := halign y (by rw [← hS]; exact hys.mpr hyC)
        simpa [z, w, switchingVector, hyC, hyt.mpr hyC] using he
      · simp [z, w, switchingVector, hyC, mt hyt.mp hyC]
  refine ⟨g, pi, hg, ?_⟩
  have hcn : c ≠ 0 := by intro h; rw [h] at hc; norm_num at hc
  ext y
  change y ∈ C ↔ y ∈ T
  have he := congrFun hwhole y
  change z y = c * w y at he
  constructor
  · intro hy
    by_contra hn
    have hzunit := switching_sq hswitch hy
    have hzero : s y = 0 := by
      simpa only [z, w, switchingVector, ite_eq_left hy, ite_eq_right hn, mul_zero] using he
    rw [hzero] at hzunit
    norm_num at hzunit
  · intro hy
    by_contra hn
    have htunit := switching_sq ht hy
    have htzero : t y = 0 := by
      have hprod : c * t y = 0 := by
        simpa only [z, w, switchingVector, ite_eq_left hy, ite_eq_right hn] using he.symm
      exact (mul_eq_zero.mp hprod).resolve_left hcn
    rw [htzero] at htunit
    norm_num at htunit

#print axioms thin_slice_gray_reconstruction

end D5.S3.Combinatorics.Graph.HypercubeCritical.ThinSliceGrayReconstruction
