/- GID: D5/S3/Quantum/SpinFactor/OriginalPureRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinFactor/OriginalPureRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.CrossProduct]
   utility: none
   digest: Pure direction, finite-parameter saturation, and global sign for the original total relation. -/

import D5.S3.Quantum.SpinFactor.OriginalDContract
import D5.S3.Geometry.TwoAxisFiniteRotation
import Mathlib.LinearAlgebra.CrossProduct

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.SpinFactor.OriginalPureRigidity

open OriginalDContract

abbrev pure (x : Vec) : E := (0, x)

/-- The known linear evaluation map, never a change of the original relation. -/
def lift (n : Vec) (a : E) : Vec := a.2 + a.1 • n

/-- The basic original-D identities used by the pure argument. The bound is
the determinant inequality for the original unit-mass evaluation. Label
rotation is an identity of the same total D, not linearity in either slot. -/
structure PureSuppliers (D : E → E → E) : Prop where
  antisymmetric : skew D
  axis_zero : ∀ a b : E, crossProduct a.2 b.2 = 0 → D a b = 0
  difference : ∀ a b c : E, finiteDifference D a b c = 0
  bound : ∀ (n : Vec), dot n n = 1 → ∀ a b : E,
    ((D a b).1 + dot n (D a b).2) ^ 2 ≤
      dot (crossProduct (lift n a) (lift n b)) (crossProduct (lift n a) (lift n b))
  label_rotation : ∀ (a b : E) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
    D a b = D (c • a + s • b) ((-s) • a + c • b)

private theorem dot_nonneg (x : Vec) : 0 ≤ dot x x := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

private theorem dot_pos {x : Vec} (hx : x ≠ 0) : 0 < dot x x := by
  exact lt_of_le_of_ne (dot_nonneg x)
    (Ne.symm (fun h => hx (dotProduct_self_eq_zero.mp h)))

private theorem dot_symm (x y : Vec) : dot x y = dot y x := dotProduct_comm _ _

private theorem dot_add_left (x y z : Vec) : dot (x + y) z = dot x z + dot y z :=
  add_dotProduct x y z

private theorem dot_add_right (x y z : Vec) : dot x (y + z) = dot x y + dot x z :=
  dotProduct_add x y z

private theorem dot_sub_left (x y z : Vec) : dot (x - y) z = dot x z - dot y z :=
  sub_dotProduct x y z

private theorem dot_sub_right (x y z : Vec) : dot x (y - z) = dot x y - dot x z :=
  dotProduct_sub x y z

private theorem dot_smul_left (a : ℝ) (x y : Vec) : dot (a • x) y = a * dot x y := by
  simpa only [smul_eq_mul] using (smul_dotProduct a x y)

private theorem dot_smul_right (a : ℝ) (x y : Vec) : dot x (a • y) = a * dot x y := by
  simpa only [smul_eq_mul] using (dotProduct_smul a x y)

/-- A finite real root diagonalizes the two-label Gram matrix. Only the
known vector arithmetic is normalized; no unknown D value is expanded. -/
private theorem orthogonalize (D : E → E → E) (h : PureSuppliers D) (x y : Vec) :
    ∃ u v : Vec, dot u v = 0 ∧
      D (pure x) (pure y) = D (pure u) (pure v) ∧ crossProduct x y = crossProduct u v := by
  by_cases hxy : dot x y = 0
  · exact ⟨x, y, hxy, rfl, rfl⟩
  let A := dot x x
  let B := dot y y
  let C := dot x y
  let R := Real.sqrt ((A - B) ^ 2 + 4 * C ^ 2)
  have hC : C ≠ 0 := hxy
  have hR : R ^ 2 = (A - B) ^ 2 + 4 * C ^ 2 := by
    apply Real.sq_sqrt
    positivity
  let t := (B - A + R) / (2 * C)
  have ht : C * t ^ 2 + (A - B) * t - C = 0 := by
    dsimp [t]
    field_simp [hC]
    nlinarith [hR, congrArg (fun q : ℝ => C * q) hR]
  let r := Real.sqrt (1 + t ^ 2)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr0 := ne_of_gt hr
  have hrsq : r ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  let c := 1 / r
  let s := t / r
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    field_simp [hr0]
    nlinarith [hrsq]
  let u := c • x + s • y
  let v := (-s) • x + c • y
  have huv : dot u v = 0 := by
    have he : dot u v = (C * (1 - t ^ 2) + (B - A) * t) / r ^ 2 := by
      simp only [u, v, dot_add_left, dot_add_right, dot_smul_left,
        dot_smul_right, dot_symm y x]
      change (c * (-s * A) + c * (c * C)) + (s * (-s * C) + s * (c * B)) = _
      dsimp [c, s]
      field_simp [hr0] <;> ring
    rw [he, show C * (1 - t ^ 2) + (B - A) * t = 0 by nlinarith [ht], zero_div]
  have hc : crossProduct u v = crossProduct x y := by
    simp only [u, v, LinearMap.map_add₂, map_add, LinearMap.map_smul₂,
      map_smul, cross_self, smul_zero, zero_add, add_zero,
      ← cross_anticomm x y]
    funext i
    have hi := congrArg (fun a : ℝ => a * crossProduct x y i) hcs
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hi]
  refine ⟨u, v, huv, ?_, hc.symm⟩
  simpa [pure, u, v] using h.label_rotation (pure x) (pure y) c s hcs

private theorem jordan_zero_left (a : E) : jordan 0 a = 0 := by
  ext i <;> simp [jordan, dot]

private theorem jordan_zero_right (a : E) : jordan a 0 = 0 := by
  ext i <;> simp [jordan, dot]

private theorem cross_perp_left (x y : Vec) : dot x (crossProduct x y) = 0 :=
  dot_self_cross x y

private theorem cross_perp_right (x y : Vec) : dot y (crossProduct x y) = 0 :=
  dot_cross_self x y

private theorem cross_sq (x y : Vec) :
    dot (crossProduct x y) (crossProduct x y) = dot x x * dot y y - dot x y ^ 2 := by
  simpa only [dot, pow_two, dotProduct_comm y x] using (cross_dot_cross x y x y)

/-- The determinant bound is evaluated at an actual positive original
evaluation. Only the known Jordan product and vector coordinates are expanded. -/
private theorem original_unit_bound (D : E → E → E) (hP : P2 D)
    (n : Vec) (hn : dot n n = 1) (a b : E) :
    ((D a b).1 + dot n (D a b).2) ^ 2 ≤
      dot (crossProduct (lift n a) (lift n b))
        (crossProduct (lift n a) (lift n b)) := by
  let α : Evaluation := ⟨1, n, by simp [vnorm, hn]⟩
  have he (u v : E) :
      evaluate α (jordan u v) = dot (lift n u) (lift n v) := by
    dsimp only [evaluate, α, jordan, lift]
    simp only [one_mul, dot_add_left, dot_add_right, dot_smul_left,
      dot_smul_right, hn, dot_symm u.2 n]
    ring
  have hb := p2_determinant_bound D hP α a b
  rw [he a a, he b b, he a b] at hb
  simpa only [evaluate, α, one_mul, cross_sq] using hb

/-- Each field is supplied by the same arbitrary original D's P2 and PB.
No unit-row, scaling, continuity or extra positivity premise is introduced. -/
private theorem original_pure_suppliers (D : E → E → E)
    (hP : P2 D) (hPB : PB D) : PureSuppliers D where
  antisymmetric := p2_skew D hP
  axis_zero := collinear_zero D hP hPB
  difference := (pb_iff_finite_difference D).mp hPB
  bound := original_unit_bound D hP
  label_rotation a b c s hcs := by
    simpa only [sub_eq_add_neg, neg_smul, add_comm] using
      (OriginalDContract.label_rotation D hP hPB c s hcs a b)

private theorem perpendicular_cross_ne {x y : Vec}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : dot x y = 0) : crossProduct x y ≠ 0 := by
  intro h
  have hw := cross_sq x y
  rw [h, hxy] at hw
  have hp := mul_pos (dot_pos hx) (dot_pos hy)
  simp only [dot, dotProduct_zero, sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true] at hw
  nlinarith

/-- A zero second outer label in the original finite difference forces the
Jordan zero face. No additive or homogeneous behavior of D is used. -/
private theorem orthogonal_zero_face (D : E → E → E) (h : PureSuppliers D)
    {x y : Vec} (hy : y ≠ 0) (hxy : dot x y = 0) :
    (D (pure x) (pure y)).1 = 0 ∧ dot y (D (pure x) (pure y)).2 = 0 := by
  have hzero (a : E) : D a 0 = 0 :=
    h.axis_zero a 0 (map_zero (crossProduct a.2))
  have hj : jordan (pure x) (pure y) = 0 := by
    ext i <;> simp [pure, jordan, hxy]
  have hf := h.difference (pure x) (pure y) 0
  have hz : (2 : ℝ) • jordan (pure y) (D (pure x) (pure y)) = 0 := by
    simpa [finiteDifference, hzero, hj, jordan_zero_right, jordan_zero_left] using hf
  have hz' : jordan (pure y) (D (pure x) (pure y)) = 0 :=
    (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have hv : (D (pure x) (pure y)).1 • y = 0 := by
    simpa [jordan, pure] using congrArg Prod.snd hz'
  exact ⟨(smul_eq_zero.mp hv).resolve_right hy,
    by simpa [jordan, pure] using congrArg Prod.fst hz'⟩

private theorem normal_line {x y z : Vec} (hw : crossProduct x y ≠ 0)
    (hxz : dot x z = 0) (hyz : dot y z = 0) :
    ∃ k : ℝ, z = k • crossProduct x y := by
  let w := crossProduct x y
  have hwz : crossProduct w z = 0 := by
    change crossProduct (crossProduct x y) z = 0
    rw [cross_cross_eq_smul_sub_smul]
    simp only [hxz, hyz, zero_smul, sub_zero]
  have he : dot w w • z = dot w z • w := by
    have ht := cross_cross_eq_smul_sub_smul' w w z
    change crossProduct w (crossProduct w z) = dot w z • w - dot w w • z at ht
    rw [hwz, map_zero] at ht
    exact (sub_eq_zero.mp ht.symm).symm
  have hww : dot w w ≠ 0 := ne_of_gt (dot_pos hw)
  refine ⟨dot w z / dot w w, ?_⟩
  funext i
  have hi := congrFun he i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  field_simp [hww]
  nlinarith [hi]

private theorem orthogonal_direction (D : E → E → E) (h : PureSuppliers D)
    {x y : Vec} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : dot x y = 0) :
    ∃ k : ℝ, D (pure x) (pure y) = (0, k • crossProduct x y) := by
  obtain ⟨hs, hyz⟩ := orthogonal_zero_face D h hy hxy
  have hswap := orthogonal_zero_face D h (x := y) (y := x) hx
    (by rwa [dot_symm])
  have hxz : dot x (D (pure x) (pure y)).2 = 0 := by
    have hsk := h.antisymmetric (pure x) (pure y)
    rw [hsk] at hswap
    simpa [dot, dotProduct_neg] using hswap.2
  obtain ⟨k, hk⟩ := normal_line (perpendicular_cross_ne hx hy hxy) hxz hyz
  exact ⟨k, Prod.ext hs hk⟩

private theorem two_bounded_squares {f g T : ℝ}
    (hf : f ^ 2 ≤ T) (hg : g ^ 2 ≤ T) : (f - g) ^ 2 ≤ 4 * T := by
  nlinarith [sq_nonneg (f + g)]

/-- The same fixed inner pair is tested at every finite lambda. The original
outer D values are not scaled, expanded, or sent to a limit. -/
private theorem saturation_estimate (D : E → E → E) (h : PureSuppliers D)
    {x y : Vec} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : dot x y = 0)
    {k : ℝ} (hk : D (pure x) (pure y) = (0, k • crossProduct x y)) (l : ℝ) :
    (1 - k ^ 2) * l ^ 2 * dot x x * dot y y ≤ 1 + k ^ 2 * dot y y := by
  let A := dot x x
  let B := dot y y
  let Y := Real.sqrt B
  let r := Real.sqrt (l ^ 2 * A + 1)
  let w := crossProduct x y
  have hA : 0 < A := dot_pos hx
  have hB : 0 < B := dot_pos hy
  have hY : 0 < Y := Real.sqrt_pos.2 hB
  have hYsq : Y ^ 2 = B := Real.sq_sqrt hB.le
  have hrarg : 0 < l ^ 2 * A + 1 := by positivity
  have hr : 0 < r := Real.sqrt_pos.2 hrarg
  have hrsq : r ^ 2 = l ^ 2 * A + 1 := Real.sq_sqrt hrarg.le
  have hY0 := ne_of_gt hY
  have hr0 := ne_of_gt hr
  let n := (-l / r) • x + (1 / (r * Y)) • y
  have hn : dot n n = 1 := by
    dsimp [n]
    simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right,
      hxy, dot_symm y x, mul_zero, zero_mul, add_zero, zero_add]
    change (-l / r) * ((-l / r) * A) +
      (1 / (r * Y)) * ((1 / (r * Y)) * B) = 1
    rw [← hYsq]
    field_simp [hr0, hY0]
    nlinarith [hrsq, congrArg (fun q : ℝ => q * Y ^ 2) hrsq]
  let c : E := (r, l • x)
  let p : E := (-l * A, y + k • w - r • x)
  let q : E := (l * A, y - k • w + r • x)
  have hac : D (pure x) c = 0 := by
    apply h.axis_zero
    simpa [c, pure, map_smul, cross_self]
  have hab : jordan (pure x) (pure y) = 0 := by
    ext i <;> simp [jordan, pure, hxy]
  have hacj : jordan (pure x) c = (l * A, r • x) := by
    ext i <;> simp [jordan, pure, c, A, dot, dotProduct_smul, mul_comm]
  have hp : pure y + D (pure x) (pure y) - jordan (pure x) c = p := by
    rw [hk, hacj]
    apply Prod.ext
    · simp [pure, p]; ring
    · rfl
  have hq : pure y - D (pure x) (pure y) + jordan (pure x) c = q := by
    rw [hk, hacj]
    apply Prod.ext
    · simp [pure, q]
    · rfl
  have hfd : D p c - D q c = (0, (2 * l * A) • y) := by
    have hf := h.difference (pure x) (pure y) c
    rw [finiteDifference, hp, hq, hab, hac] at hf
    simp only [add_zero, zero_add, jordan_zero_right, smul_zero, add_zero] at hf
    have hwperp : dot y w = 0 := cross_perp_right x y
    apply Prod.ext
    · have hs := congrArg Prod.fst hf
      simp [jordan, pure, hk, hacj, dot_sub_right, dot_smul_right,
        hwperp, dot_symm y x, hxy] at hs
      nlinarith [hs]
    · funext i
      have hv := congrArg (fun a : E => a.2 i) hf
      simp [jordan, pure, hk, hacj, A, Pi.smul_apply, smul_eq_mul] at hv ⊢
      nlinarith [hv]
  have hnc : lift n c = (1 / Y) • y := by
    funext i
    simp [lift, n, c, Pi.smul_apply, smul_eq_mul]
    field_simp [hr0, hY0] <;> ring
  have hrcancel : -r + l * l * A / r = -1 / r := by
    field_simp [hr0]
    nlinarith [hrsq]
  have hL (sg : ℝ) :
      lift n (-sg * l * A, y + sg • (k • w - r • x)) =
        (1 - sg * l * A / (r * Y)) • y + (sg * k) • w +
          (sg * (-1 / r)) • x := by
    have he : lift n (-sg * l * A, y + sg • (k • w - r • x)) =
        (1 - sg * l * A / (r * Y)) • y + (sg * k) • w +
          (sg * (-r + l * l * A / r)) • x := by
      funext i
      simp only [lift, n, Prod.fst, Prod.snd, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    simpa only [hrcancel] using he
  have hdet (sg : ℝ) :
      dot (crossProduct (lift n (-sg * l * A, y + sg • (k • w - r • x))) (lift n c))
        (crossProduct (lift n (-sg * l * A, y + sg • (k • w - r • x))) (lift n c)) =
      sg ^ 2 * (A / r ^ 2 + k ^ 2 * A * B) := by
    have hww : dot w w = A * B := by simpa [w, A, B, hxy] using cross_sq x y
    have hxw : dot x w = 0 := cross_perp_left x y
    have hwx : dot w x = 0 := by rw [dot_symm]; exact hxw
    have hcross : crossProduct w y = -B • x := by
      change crossProduct (crossProduct x y) y = -B • x
      rw [cross_cross_eq_smul_sub_smul]
      simp [hxy, B, dot, neg_smul]
    have he : crossProduct (lift n (-sg * l * A, y + sg • (k • w - r • x))) (lift n c) =
        (-sg * k * Y) • x + (-sg / (r * Y)) • w := by
      rw [hL, hnc]
      simp only [LinearMap.map_add₂, LinearMap.map_smul₂, map_smul,
        cross_self, smul_zero, zero_add, hcross]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp only [w]
      rw [← hYsq]
      field_simp [hr0, hY0] <;> ring
    rw [he]
    simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right,
      hxw, hwx, hww, mul_zero, zero_mul, add_zero, zero_add]
    rw [← hYsq]
    field_simp [hr0, hY0] <;> ring
  let f := (D p c).1 + dot n (D p c).2
  let g := (D q c).1 + dot n (D q c).2
  have hf : f ^ 2 ≤ A / r ^ 2 + k ^ 2 * A * B := by
    have hp' : p = (-(1 : ℝ) * l * A, y + (1 : ℝ) • (k • w - r • x)) := by
      ext i <;> simp [p] <;> ring
    have hd := hdet (1 : ℝ)
    rw [← hp'] at hd
    simp only [one_pow, one_mul] at hd
    have hh := h.bound n hn p c
    rw [hd] at hh
    exact hh
  have hg : g ^ 2 ≤ A / r ^ 2 + k ^ 2 * A * B := by
    have he : q = (-(-1) * l * A, y + (-1 : ℝ) • (k • w - r • x)) := by
      ext i <;> simp [q] <;> ring
    have hd := hdet (-1 : ℝ)
    rw [← he] at hd
    norm_num at hd
    have hh := h.bound n hn q c
    rw [hd] at hh
    exact hh
  have hny : dot n y = Y / r := by
    simp only [n, dot_add_left, dot_smul_left, hxy, mul_zero, zero_add]
    change (1 / (r * Y)) * B = Y / r
    rw [← hYsq]
    field_simp [hr0, hY0] <;> ring
  have hfg : f - g = 2 * l * A * Y / r := by
    have hv := congrArg (fun a : E => a.1 + dot n a.2) hfd
    change (D p c).1 - (D q c).1 + dot n ((D p c).2 - (D q c).2) =
      0 + dot n ((2 * l * A) • y) at hv
    rw [zero_add, dot_sub_right, dot_smul_right, hny] at hv
    dsimp [f, g]
    linarith [hv]
  have hh := two_bounded_squares hf hg
  rw [hfg] at hh
  have hh' : l ^ 2 * A ^ 2 * B ≤ A + k ^ 2 * A * B * r ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg r)
    have hleft : (2 * l * A * Y / r) ^ 2 * r ^ 2 = 4 * l ^ 2 * A ^ 2 * B := by
      rw [← hYsq]
      field_simp [hr0] <;> ring
    have hright : (4 * (A / r ^ 2 + k ^ 2 * A * B)) * r ^ 2 =
        4 * (A + k ^ 2 * A * B * r ^ 2) := by
      field_simp [hr0] <;> ring
    rw [hleft, hright] at hmul
    nlinarith [hmul]
  rw [hrsq] at hh'
  change (1 - k ^ 2) * l ^ 2 * A * B ≤ 1 + k ^ 2 * B
  apply (mul_le_mul_left hA).mp
  nlinarith [hh']

/-- Orthogonal nonzero pure inputs have saturated original output. The proof
uses only finite original labels in the bound and finite difference. -/
theorem orthogonal_saturation (D : E → E → E) (h : PureSuppliers D)
    {x y : Vec} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : dot x y = 0) :
    ∃ k : ℝ, k ^ 2 = 1 ∧ D (pure x) (pure y) = (0, k • crossProduct x y) := by
  obtain ⟨k, hk⟩ := orthogonal_direction D h hx hy hxy
  have hA : 0 < dot x x := dot_pos hx
  have hB : 0 < dot y y := dot_pos hy
  have hww : 0 < dot (crossProduct x y) (crossProduct x y) :=
    dot_pos (perpendicular_cross_ne hx hy hxy)
  let w := crossProduct x y
  let W := Real.sqrt (dot w w)
  have hW : 0 < W := Real.sqrt_pos.2 hww
  have hWsq : W ^ 2 = dot w w := Real.sq_sqrt hww.le
  have hW0 := ne_of_gt hW
  have hn : dot (W⁻¹ • w) (W⁻¹ • w) = 1 := by
    simp only [dot_smul_left, dot_smul_right]
    rw [← hWsq]
    field_simp [hW0]
  have hb := h.bound (W⁻¹ • w) hn (pure x) (pure y)
  rw [hk] at hb
  have hkle : k ^ 2 ≤ 1 := by
    simp only [lift, pure, zero_smul, add_zero, zero_add,
      dot_smul_left, dot_smul_right] at hb
    change (W⁻¹ * (k * dot w w)) ^ 2 ≤ dot w w at hb
    rw [← hWsq] at hb
    have hc : W⁻¹ * (k * W ^ 2) = k * W := by
      field_simp [hW0] <;> ring
    rw [hc] at hb
    apply (mul_le_mul_right (sq_pos_of_pos hW)).mp
    nlinarith [hb]
  have hkge : 1 ≤ k ^ 2 := by
    by_contra hnot
    have hklt : k ^ 2 < 1 := lt_of_not_ge hnot
    let C := (1 - k ^ 2) * dot x x * dot y y
    have hC : 0 < C := mul_pos (mul_pos (sub_pos.mpr hklt) hA) hB
    let l := Real.sqrt ((1 + k ^ 2 * dot y y + 1) / C)
    have hlarg : 0 ≤ (1 + k ^ 2 * dot y y + 1) / C := by positivity
    have hl : l ^ 2 * C = 1 + k ^ 2 * dot y y + 1 := by
      rw [show l ^ 2 = (1 + k ^ 2 * dot y y + 1) / C from Real.sq_sqrt hlarg]
      exact div_mul_cancel₀ _ (ne_of_gt hC)
    have he := saturation_estimate D h hx hy hxy hk l
    dsimp [C] at hl
    nlinarith [he, hl]
  exact ⟨k, le_antisymm hkle hkge, hk⟩

/-- Direction and amplitude, including zero and dependent pairs, after exact
label orthogonalization. No property of D under scalar scaling is inferred or
used before the conclusion. -/
theorem pure_pair_saturation (D : E → E → E) (h : PureSuppliers D) (x y : Vec) :
    ∃ k : ℝ, k ^ 2 = 1 ∧ D (pure x) (pure y) = (0, k • crossProduct x y) := by
  by_cases hw : crossProduct x y = 0
  · exact ⟨1, by norm_num, by simpa [hw] using h.axis_zero (pure x) (pure y) hw⟩
  obtain ⟨a, b, hab, hD, hcross⟩ := orthogonalize D h x y
  have ha : a ≠ 0 := by intro ha; apply hw; simpa [ha, LinearMap.map_zero₂] using hcross
  have hb : b ≠ 0 := by intro hb; apply hw; simpa [hb, map_zero] using hcross
  obtain ⟨k, hk, he⟩ := orthogonal_saturation D h ha hb hab
  exact ⟨k, hk, by rw [hD, he, hcross]⟩

private theorem pure_square (D : E → E → E) (h : PureSuppliers D) (x y : Vec) :
    dot (D (pure x) (pure y)).2 (D (pure x) (pure y)).2 =
      dot (crossProduct x y) (crossProduct x y) := by
  obtain ⟨k, hk, he⟩ := pure_pair_saturation D h x y
  rw [he]
  simp only [dot_smul_left, dot_smul_right]
  calc
    k * (k * dot (crossProduct x y) (crossProduct x y)) =
        k ^ 2 * dot (crossProduct x y) (crossProduct x y) := by ring
    _ = dot (crossProduct x y) (crossProduct x y) := by rw [hk, one_mul]

/-- A transverse comparison in one nonunit row. Both outer values are values
of the same original D. The squared output comparison uses pair saturation,
not a sign or scaling assumption on either outer pair. -/
theorem transverse_sign (D : E → E → E) (h : PureSuppliers D)
    {x y z : Vec} (hx : dot x x ≠ 1)
    (hxy : dot x y = 0) (hxz : dot x z = 0)
    (hyz : dot y z ≠ 0) (ht : dot x (crossProduct y z) ≠ 0)
    {k l : ℝ} (hk : k ^ 2 = 1) (hl : l ^ 2 = 1)
    (hky : D (pure x) (pure y) = (0, k • crossProduct x y))
    (hlz : D (pure x) (pure z) = (0, l • crossProduct x z)) : k = l := by
  let p := y + k • crossProduct x y
  let q := z + l • crossProduct x z
  let p' := y - k • crossProduct x y
  let q' := z - l • crossProduct x z
  have hjy : jordan (pure x) (pure y) = 0 := by
    ext i <;> simp [jordan, pure, hxy]
  have hjz : jordan (pure x) (pure z) = 0 := by
    ext i <;> simp [jordan, pure, hxz]
  have hjdy : jordan (pure y) (D (pure x) (pure y)) = 0 := by
    rw [hky]
    ext i <;> simp [jordan, pure, dot_smul_right, cross_perp_right]
  have hjdz : jordan (pure z) (D (pure x) (pure z)) = 0 := by
    rw [hlz]
    ext i <;> simp [jordan, pure, dot_smul_right, cross_perp_right]
  have he : D (pure p) (pure q) = D (pure p') (pure q') := by
    have hf := h.difference (pure x) (pure y) (pure z)
    have hf' : D (pure p) (pure q) - D (pure p') (pure q') = 0 := by
      simpa [finiteDifference, hjy, hjz, hjdy, hjdz, hky, hlz,
        p, q, p', q', pure, jordan_zero_right, sub_eq_add_neg] using hf
    exact sub_eq_zero.mp hf'
  have hsq : dot (crossProduct p q) (crossProduct p q) = dot (crossProduct p' q') (crossProduct p' q') := by
    calc
      dot (crossProduct p q) (crossProduct p q) =
          dot (D (pure p) (pure q)).2 (D (pure p) (pure q)).2 :=
        (pure_square D h p q).symm
      _ = dot (D (pure p') (pure q')).2 (D (pure p') (pure q')).2 := by rw [he]
      _ = dot (crossProduct p' q') (crossProduct p' q') := pure_square D h p' q'
  have hycross : dot y (crossProduct x z) = -dot x (crossProduct y z) := by
    change y ⬝ᵥ (x ⨯₃ z) = -(x ⬝ᵥ (y ⨯₃ z))
    rw [triple_product_permutation y x z, ← cross_anticomm y z, dotProduct_neg]
  have hcrossz : dot (crossProduct x y) z = dot x (crossProduct y z) := by
    rw [dot_symm]
    exact triple_product_permutation z x y
  have hcrosscross : dot (crossProduct x y) (crossProduct x z) = dot x x * dot y z := by
    have hc := cross_dot_cross x y x z
    simpa [hxz, hxy, dot] using hc
  have hexpand :
      dot (crossProduct p q) (crossProduct p q) - dot (crossProduct p' q') (crossProduct p' q') =
        4 * (1 + k * l * dot x x) * (l - k) * dot y z * dot x (crossProduct y z) := by
    simp only [cross_sq, p, q, p', q', dot_add_left, dot_add_right,
      dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right,
      cross_perp_right, dot_symm (crossProduct x y) y, dot_symm (crossProduct x z) z,
      hycross, hcrossz, hcrosscross]
    ring
  by_contra hne
  have hkl : k * l = -1 := by
    have heq : k = -l :=
      (sq_eq_sq_iff_eq_or_eq_neg.mp (hk.trans hl.symm)).resolve_left hne
    rw [heq]
    nlinarith [hl]
  have hdiff : l - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hproduct : (1 + k * l * dot x x) * (l - k) * dot y z * dot x (crossProduct y z) = 0 := by
    nlinarith [hexpand, hsq]
  have hfactor : 1 + k * l * dot x x = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right ht)).resolve_right hyz)).resolve_right hdiff
  rw [hkl] at hfactor
  exact hx (by linarith)

private theorem plane_coordinates {x y z : Vec}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : dot x y = 0)
    (hxz : dot x z = 0) (hz : z ≠ 0) :
    dot z y ≠ 0 ∨ dot z (crossProduct x y) ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hc : crossProduct (crossProduct x y) z = 0 := by
    change crossProduct (crossProduct x y) z = 0
    rw [cross_cross_eq_smul_sub_smul]
    simp [hxz, dot_symm y z, hn.1]
  have hw := cross_dot_cross (crossProduct x y) z (crossProduct x y) z
  change dot (crossProduct (crossProduct x y) z) (crossProduct (crossProduct x y) z) =
    dot (crossProduct x y) (crossProduct x y) * dot z z -
      dot (crossProduct x y) z * dot z (crossProduct x y) at hw
  rw [hc, hn.2] at hw
  have hp := mul_pos (dot_pos (perpendicular_cross_ne hx hy hxy)) (dot_pos hz)
  simp [dot] at hw
  nlinarith

private theorem choose_transverse_parameter {A u v : ℝ}
    (hA : 0 < A) (huv : u ≠ 0 ∨ v ≠ 0) :
    ∃ t : ℝ, t > 0 ∧ u + t * v ≠ 0 ∧ -v + t * A * u ≠ 0 := by
  by_cases hu : u = 0
  · have hv := huv.resolve_left (not_not_intro hu)
    exact ⟨1, by norm_num, by simpa [hu] using hv, by simpa [hu] using neg_ne_zero.mpr hv⟩
  by_cases hv : v = 0
  · refine ⟨1, by norm_num, by simpa [hv] using hu, ?_⟩
    simpa [hv] using mul_ne_zero (ne_of_gt hA) hu
  have hAu : A * u ≠ 0 := mul_ne_zero (ne_of_gt hA) hu
  obtain ⟨t, ht⟩ := exists_gt (max 0 (max (-u / v) (v / (A * u))))
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht1 : -u / v < t := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have ht2 : v / (A * u) < t := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  refine ⟨t, ht0, ?_, ?_⟩
  · intro he
    have heq : -u / v = t := (div_eq_iff hv).2 (by linarith)
    exact (ne_of_lt ht1) heq
  · intro he
    have heq : v / (A * u) = t := (div_eq_iff hAu).2 (by nlinarith)
    exact (ne_of_lt ht2) heq

/-- Every nonzero perpendicular direction belongs to the same sign row at a
fixed nonunit x. The intermediate direction is chosen outside two actual
forbidden lines; no generic-position premise is added to the result. -/
theorem nonunit_row_sign (D : E → E → E) (h : PureSuppliers D)
    {x y z : Vec} (hx : x ≠ 0) (hunit : dot x x ≠ 1)
    (hy : y ≠ 0) (hz : z ≠ 0) (hxy : dot x y = 0) (hxz : dot x z = 0)
    {k l : ℝ} (hk : k ^ 2 = 1) (hl : l ^ 2 = 1)
    (hky : D (pure x) (pure y) = (0, k • crossProduct x y))
    (hlz : D (pure x) (pure z) = (0, l • crossProduct x z)) : k = l := by
  obtain ⟨t, ht, ht1, ht2⟩ := choose_transverse_parameter (dot_pos hx)
    (plane_coordinates hx hy hxy hxz hz)
  let q := y + t • crossProduct x y
  have hxq : dot x q = 0 := by
    simp [q, dot_add_right, dot_smul_right, hxy, cross_perp_left]
  have hyq : dot y q ≠ 0 := by
    simpa [q, dot_add_right, dot_smul_right, cross_perp_right] using ne_of_gt (dot_pos hy)
  have hzq : dot z q ≠ 0 := by
    simpa [q, dot_add_right, dot_smul_right] using ht1
  have hty : dot x (crossProduct y q) ≠ 0 := by
    have he : dot x (crossProduct y q) = t * dot x x * dot y y := by
      simp only [q, map_add, map_smul, cross_self,
        zero_add, dot_smul_right]
      change t * (x ⬝ᵥ (y ⨯₃ (x ⨯₃ y))) = _
      rw [cross_cross_eq_smul_sub_smul']
      simp [dotProduct_sub, dotProduct_smul, hxy, dot, mul_comm, mul_left_comm, mul_assoc]
    rw [he]
    exact mul_ne_zero (mul_ne_zero (ne_of_gt ht) (ne_of_gt (dot_pos hx))) (ne_of_gt (dot_pos hy))
  have htz : dot x (crossProduct z q) ≠ 0 := by
    have he : dot x (crossProduct z q) = -dot z (crossProduct x y) + t * dot x x * dot z y := by
      simp only [q, map_add, map_smul, dot_add_right, dot_smul_right]
      have ha : dot x (crossProduct z y) = -dot z (crossProduct x y) := by
        rw [show crossProduct z y = -crossProduct y z from (cross_anticomm y z).symm]
        simpa [dot, dotProduct_neg] using
          (congrArg Neg.neg (triple_product_permutation z x y)).symm
      rw [ha]
      change _ + t * (x ⬝ᵥ (z ⨯₃ (x ⨯₃ y))) = _
      rw [cross_cross_eq_smul_sub_smul']
      simp [dotProduct_sub, dotProduct_smul, hxz, dot_symm x y, hxy, dot,
        mul_comm, mul_left_comm, mul_assoc]
    rw [he]
    exact ht2
  obtain ⟨m, hm, hmq⟩ := pure_pair_saturation D h x q
  have hkm := transverse_sign D h hunit hxy hxq hyq hty hk hm hky hmq
  have hlm := transverse_sign D h hunit hxz hxq hzq htz hl hm hlz hmq
  exact hkm.trans hlm.symm

/-- A purely Euclidean supplier, with no reference to the unknown D. -/
def CommonNonunitPerpendicular : Prop :=
  ∀ a b : Vec, ∃ z : Vec,
    z ≠ 0 ∧ dot a z = 0 ∧ dot b z = 0 ∧ dot z z ≠ 1

/-- Transport the geometry supplier through the original coordinates and
multiply its unit vector by two. The geometry existence proof is reused. -/
private theorem common_nonunit_perpendicular : CommonNonunitPerpendicular := by
  intro a b
  obtain ⟨n, hn, han, hbn⟩ :=
    D5.S3.Geometry.TwoAxisFiniteRotation.unit_perpendicular_pair
      (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  let v : Vec := WithLp.ofLp n
  have hv : dot v v = 1 := by
    have hs := EuclideanSpace.real_norm_sq_eq n
    rw [hn] at hs
    simpa only [one_pow, dot, dotProduct, v, pow_two] using hs.symm
  have hav : dot a v = 0 := by
    simpa [PiLp.inner_apply, RCLike.inner_apply, dot, dotProduct, v, mul_comm] using han
  have hbv : dot b v = 0 := by
    simpa [PiLp.inner_apply, RCLike.inner_apply, dot, dotProduct, v, mul_comm] using hbn
  let z : Vec := (2 : ℝ) • v
  have hzz : dot z z = 4 := by
    norm_num [z, dot_smul_left, dot_smul_right, hv]
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro hz
    rw [hz] at hzz
    norm_num [dot] at hzz
  · simp only [z, dot_smul_right, hav, mul_zero]
  · simp only [z, dot_smul_right, hbv, mul_zero]
  · rw [hzz]
    norm_num

private theorem reverse_orientation (D : E → E → E) (h : PureSuppliers D)
    {x y : Vec} {e : ℝ} (he : D (pure x) (pure y) = (0, e • crossProduct x y)) :
    D (pure y) (pure x) = (0, e • crossProduct y x) := by
  rw [h.antisymmetric (pure x) (pure y), he, ← cross_anticomm x y]
  simp

private theorem common_nonunit_sign (D : E → E → E) (h : PureSuppliers D)
    (hperp : CommonNonunitPerpendicular) :
    ∃ e : ℝ, e ^ 2 = 1 ∧ ∀ a b : Vec, dot a b = 0 →
      (dot a a ≠ 1 ∨ dot b b ≠ 1) →
      D (pure a) (pure b) = (0, e • crossProduct a b) := by
  let a₀ : Vec := ![2, 0, 0]
  let b₀ : Vec := ![0, 2, 0]
  have ha₀ : a₀ ≠ 0 := by
    intro hh
    have hi := congrFun hh 0
    norm_num [a₀] at hi
  have hb₀ : b₀ ≠ 0 := by
    intro hh
    have hi := congrFun hh 1
    norm_num [b₀] at hi
  have hab₀ : dot a₀ b₀ = 0 := by norm_num [a₀, b₀, dot, dotProduct, Fin.sum_univ_succ]
  have hunit₀ : dot a₀ a₀ ≠ 1 := by norm_num [a₀, dot, dotProduct, Fin.sum_univ_succ]
  obtain ⟨e, he, he₀⟩ := pure_pair_saturation D h a₀ b₀
  have hfirst (a b : Vec) (ha : a ≠ 0) (hb : b ≠ 0)
      (hab : dot a b = 0) (hunit : dot a a ≠ 1) :
      D (pure a) (pure b) = (0, e • crossProduct a b) := by
    obtain ⟨z, hz, haz, ha₀z, hzunit⟩ := hperp a a₀
    obtain ⟨k, hk, hkab⟩ := pure_pair_saturation D h a b
    obtain ⟨l, hl, hlaz⟩ := pure_pair_saturation D h a z
    obtain ⟨m, hm, hma₀z⟩ := pure_pair_saturation D h a₀ z
    have hkl := nonunit_row_sign D h ha hunit hb hz hab haz hk hl hkab hlaz
    have hme := nonunit_row_sign D h ha₀ hunit₀ hz hb₀ ha₀z hab₀ hm he hma₀z he₀
    have hlm := nonunit_row_sign D h hz hzunit ha ha₀
      (by rwa [dot_symm]) (by rwa [dot_symm]) hl hm
      (reverse_orientation D h hlaz) (reverse_orientation D h hma₀z)
    have hke : k = e := hkl.trans (hlm.trans hme)
    simpa only [hke] using hkab
  refine ⟨e, he, ?_⟩
  intro a b hab hunit
  by_cases ha : a = 0
  · subst a
    simpa [pure, LinearMap.map_zero₂] using
      h.axis_zero (pure 0) (pure b) (LinearMap.map_zero₂ crossProduct b)
  by_cases hb : b = 0
  · subst b
    simpa [pure, map_zero] using
      h.axis_zero (pure a) (pure 0) (map_zero (crossProduct a))
  rcases hunit with hunit | hunit
  · exact hfirst a b ha hb hab hunit
  · exact reverse_orientation D h (hfirst b a hb ha (by rwa [dot_symm]) hunit)

/-- The unit/unit bootstrap. The value at (x,2y) is obtained independently
from the already classified nonunit pairs. In particular this argument never
substitutes `D(x,2y)=2 D(x,y)` for an unclassified unit pair. -/
private theorem unit_pair_sign (D : E → E → E) (h : PureSuppliers D)
    {e : ℝ} (he : e ^ 2 = 1)
    (hoff : ∀ a b : Vec, dot a b = 0 →
      (dot a a ≠ 1 ∨ dot b b ≠ 1) →
      D (pure a) (pure b) = (0, e • crossProduct a b))
    {x y : Vec} (hx : dot x x = 1) (hy : dot y y = 1) (hxy : dot x y = 0) :
    D (pure x) (pure y) = (0, e • crossProduct x y) := by
  obtain ⟨k, hk, hky⟩ := pure_pair_saturation D h x y
  by_cases hke : k = e
  · simpa only [hke] using hky
  have hkneg : k = -e :=
    (sq_eq_sq_iff_eq_or_eq_neg.mp (hk.trans he.symm)).resolve_left hke
  let w := crossProduct x y
  have hww : dot w w = 1 := by simpa [w, hx, hy, hxy] using cross_sq x y
  have hyw : dot y w = 0 := cross_perp_right x y
  have hwy : dot w y = 0 := by rwa [dot_symm]
  have hycw : crossProduct y w = x := by
    change crossProduct y (crossProduct x y) = x
    rw [cross_cross_eq_smul_sub_smul']
    simpa [hy, hxy, dot]
  have hwcy : crossProduct w y = -x := by rw [← cross_anticomm y w, hycw]
  have htwo : D (pure x) (pure (2 • y)) = (0, (2 * e) • w) := by
    have hd := hoff x (2 • y)
      (by simp [dot_smul_right, hxy])
      (Or.inr (by norm_num [dot_smul_left, dot_smul_right, hy]))
    simpa [map_smul, w, smul_smul, mul_comm] using hd
  let p := y - e • w
  let q := (2 : ℝ) • y + (2 * e) • w
  let p' := y + e • w
  let q' := (2 : ℝ) • y - (2 * e) • w
  have hp : dot p p = 2 := by
    simp only [p, dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right,
      hy, hww, hyw, hwy]
    nlinarith [he]
  have hp' : dot p' p' = 2 := by
    simp only [p', dot_add_left, dot_add_right, dot_smul_left, dot_smul_right,
      hy, hww, hyw, hwy]
    nlinarith [he]
  have hpq : dot p q = 0 := by
    simp only [p, q, dot_sub_left, dot_add_right, dot_smul_left, dot_smul_right,
      hy, hww, hyw, hwy]
    nlinarith [he]
  have hpq' : dot p' q' = 0 := by
    simp only [p', q', dot_add_left, dot_sub_right, dot_smul_left, dot_smul_right,
      hy, hww, hyw, hwy]
    nlinarith [he]
  have hcross : crossProduct p q = (4 * e) • x := by
    simp only [p, q, map_add, LinearMap.map_sub₂, LinearMap.map_smul₂,
      map_smul, cross_self, hycw, hwcy, smul_zero, zero_add, sub_zero]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcross' : crossProduct p' q' = (-4 * e) • x := by
    simp only [p', q', map_sub, LinearMap.map_add₂, LinearMap.map_smul₂,
      map_smul, cross_self, hycw, hwcy, smul_zero, zero_add, add_zero,
      sub_zero]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hDp : D (pure p) (pure q) = (0, (4 : ℝ) • x) := by
    rw [hoff p q hpq (Or.inl (by rw [hp]; norm_num)), hcross]
    congr 1
    rw [smul_smul]
    have hc : e * (4 * e) = 4 := by nlinarith [he]
    rw [hc]
  have hDp' : D (pure p') (pure q') = (0, (-4 : ℝ) • x) := by
    rw [hoff p' q' hpq' (Or.inl (by rw [hp']; norm_num)), hcross']
    congr 1
    rw [smul_smul]
    have hc : e * (-4 * e) = -4 := by nlinarith [he]
    rw [hc]
  have hjy : jordan (pure x) (pure y) = 0 := by ext i <;> simp [jordan, pure, hxy]
  have hjtwo : jordan (pure x) (pure (2 • y)) = 0 := by
    ext i <;> simp [jordan, pure, dot_smul_right, hxy]
  have hjdy : jordan (pure y) (D (pure x) (pure y)) = 0 := by
    rw [hky, hkneg]
    ext i <;> simp [jordan, pure, dot_smul_right, hyw, w]
  have hjdtwo : jordan (pure (2 • y)) (D (pure x) (pure (2 • y))) = 0 := by
    rw [htwo]
    ext i <;> simp [jordan, pure, dot_smul_left, dot_smul_right, hyw]
  have heq : D (pure p) (pure q) = D (pure p') (pure q') := by
    have hf := h.difference (pure x) (pure y) (pure (2 • y))
    have hf' : D (pure p) (pure q) - D (pure p') (pure q') = 0 := by
      simpa [finiteDifference, hjy, hjtwo, hjdy, hjdtwo, hky, hkneg, htwo,
        p, q, p', q', pure, w, neg_smul, sub_eq_add_neg] using hf
    exact sub_eq_zero.mp hf'
  rw [hDp, hDp'] at heq
  have hxzero : x = 0 := by
    funext i
    have hi := congrArg (fun a : E => a.2 i) heq
    simp only [Prod.snd, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Pi.zero_apply]
    linarith
  have hcontra := hx
  rw [hxzero] at hcontra
  norm_num [dot] at hcontra

/-- One single sign controls every pure pair under the basic and Euclidean
interfaces, including zero, proportional, nonorthogonal, unit, nonunit and
unequal-length inputs. -/
theorem global_pure_of_suppliers (D : E → E → E) (h : PureSuppliers D)
    (hperp : CommonNonunitPerpendicular) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ x y : Vec, D (pure x) (pure y) = (0, e • crossProduct x y) := by
  obtain ⟨e, he, hoff⟩ := common_nonunit_sign D h hperp
  have horth (x y : Vec) (hxy : dot x y = 0) :
      D (pure x) (pure y) = (0, e • crossProduct x y) := by
    by_cases hx : dot x x = 1
    · by_cases hy : dot y y = 1
      · exact unit_pair_sign D h he hoff hx hy hxy
      · exact hoff x y hxy (Or.inr hy)
    · exact hoff x y hxy (Or.inl hx)
  have hesign : e = 1 ∨ e = -1 := by
    have hp : (e - 1) * (e + 1) = 0 := by nlinarith [he]
    rcases mul_eq_zero.mp hp with hp | hp
    · left; linarith
    · right; linarith
  refine ⟨e, hesign, ?_⟩
  intro x y
  obtain ⟨a, b, hab, hD, hcross⟩ := orthogonalize D h x y
  rw [hD, horth a b hab, hcross]

/-- Original directed complex P2 and literal PB alone force one global real
orientation on every pure input of the same arbitrary total original D. -/
theorem global_pure (D : E → E → E) (hP : P2 D) (hPB : PB D) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ x y : Vec, D (pure x) (pure y) = (0, e • OriginalDContract.cross x y) := by
  exact global_pure_of_suppliers D (original_pure_suppliers D hP hPB)
    common_nonunit_perpendicular

end D5.S3.Quantum.SpinFactor.OriginalPureRigidity
