/- GID: D5/S3/Quantum/SpinFactor/OriginalResidual
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinFactor/OriginalResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.CrossProduct]
   utility: none
   digest: Pure phase substitutions and saturated support faces of the original scalar-vector residual. -/

import D5.S3.Quantum.SpinFactor.OriginalDContract
import D5.S3.Geometry.TwoAxisFiniteRotation

noncomputable section
open scoped BigOperators Matrix InnerProductSpace

namespace D5.S3.Quantum.SpinFactor.OriginalResidual

open OriginalDContract
open _root_.D5.S3.Geometry

/-- The difference from the fixed pure orientation, in the original output space. -/
def residual (D : E → E → E) (e s t : ℝ) (x y : Vec) : E :=
  D (s, x) (t, y) - (0, e • cross x y)

/-- The original-coordinate action of a known Euclidean isometry. -/
def rotate (R : TwoAxisFiniteRotation.Orthogonal) (x : Vec) : Vec :=
  WithLp.ofLp (R (WithLp.toLp 2 x))

private def rotationLinear (R : TwoAxisFiniteRotation.Orthogonal) : Vec →ₗ[ℝ] Vec :=
  (WithLp.linearEquiv 2 ℝ Vec).toLinearMap ∘ₗ R.toLinearMap ∘ₗ
    (WithLp.linearEquiv 2 ℝ Vec).symm.toLinearMap

private theorem rotation_dot (R : TwoAxisFiniteRotation.Orthogonal) (x y : Vec) :
    dot (rotate R x) (rotate R y) = dot x y := by
  have h := R.inner_map_map (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simpa [dot, rotate, PiLp.inner_apply, Real.inner_apply] using h

private theorem rotation_cross (R : TwoAxisFiniteRotation.Orthogonal)
    (hR : TwoAxisFiniteRotation.determinant R = 1) (x y : Vec) :
    cross (rotate R x) (rotate R y) = rotate R (cross x y) := by
  let M := LinearMap.toMatrix' (rotationLinear R)
  have hm (v : Vec) : M *ᵥ v = rotate R v :=
    LinearMap.toMatrix'_mulVec (rotationLinear R) v
  have hd : M.det = 1 := by
    rw [LinearMap.det_toMatrix']
    change LinearMap.det
      ((WithLp.linearEquiv 2 ℝ Vec).toLinearMap ∘ₗ R.toLinearMap ∘ₗ
        (WithLp.linearEquiv 2 ℝ Vec).symm.toLinearMap) = 1
    rw [LinearMap.det_conj]
    exact hR
  have htriple (u v z : Vec) :
      dot (rotate R u) (cross (rotate R v) (rotate R z)) = dot u (cross v z) := by
    have hmat : ![rotate R u, rotate R v, rotate R z] = ![u, v, z] * M.transpose := by
      ext i j
      fin_cases i <;>
        simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using
          congrFun (hm (Fin.cases u (Fin.cases v (fun _ => z)) i)) j
    change (rotate R u) ⬝ᵥ ((rotate R v) ⨯₃ (rotate R z)) = u ⬝ᵥ (v ⨯₃ z)
    rw [triple_product_eq_det, triple_product_eq_det, hmat,
      Matrix.det_mul, Matrix.det_transpose, hd, mul_one]
  apply dotProduct_eq_iff.mp
  intro z
  let u : Vec := rotate R⁻¹ z
  have hu : rotate R u = z := by simp [u, rotate]
  rw [← hu, dotProduct_comm]
  change dot (rotate R u) (cross (rotate R x) (rotate R y)) =
    dot (rotate R (cross x y)) (rotate R u)
  rw [htriple, rotation_dot]
  exact dotProduct_comm _ _

private theorem rotation_injective (R : TwoAxisFiniteRotation.Orthogonal) :
    Function.Injective (rotate R) := by
  intro x y h
  have h' := congrArg (rotate R⁻¹) h
  simpa [rotate] using h'

/-- The explicit inverse of the known map `v ↦ v + e (q × v)` when `e²=1`. -/
def cayleyPreimage (e : ℝ) (q x : Vec) : Vec :=
  (1 / (1 + dot q q)) • (x - e • cross q x + dot q x • q)

/-- The opposite Cayley image, keeping the original vector coordinates. -/
def cayleyImage (e : ℝ) (q x : Vec) : Vec :=
  cayleyPreimage e q x - e • cross q (cayleyPreimage e q x)

private theorem pure_phase_transport (D : E → E → E) (hPB : PB D)
    (e : ℝ) (he : e = 1 ∨ e = -1)
    (hpure : ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y))
    (q B C : Vec) :
    residual D e (-dot q C) (dot q B)
        (B + e • cross q B) (C + e • cross q C) =
      residual D e (dot q C) (-dot q B)
        (B - e • cross q B) (C - e • cross q C) := by
  have h := (pb_iff_finite_difference D).mp hPB (0, q) (0, B) (0, C)
  have hr : (0, B) + D (0, q) (0, B) - jordan (0, q) (0, C) =
      (-dot q C, B + e • cross q B) := by
    rw [hpure]
    ext i <;> simp [jordan]
  have hs : (0, C) + jordan (0, q) (0, B) + D (0, q) (0, C) =
      (dot q B, C + e • cross q C) := by
    rw [hpure]
    ext i <;> simp [jordan]
  have hr' : (0, B) - D (0, q) (0, B) + jordan (0, q) (0, C) =
      (dot q C, B - e • cross q B) := by
    rw [hpure]
    ext i <;> simp [jordan]
  have hs' : (0, C) - jordan (0, q) (0, B) - D (0, q) (0, C) =
      (-dot q B, C - e • cross q C) := by
    rw [hpure]
    ext i <;> simp [jordan]
  have hc :
      (2 : ℝ) • jordan (0, B) (D (0, q) (0, B) - jordan (0, q) (0, C)) +
        (2 : ℝ) • jordan (0, C) (jordan (0, q) (0, B) + D (0, q) (0, C)) =
      (0, e • cross (B - e • cross q B) (C - e • cross q C)) -
        (0, e • cross (B + e • cross q B) (C + e • cross q C)) := by
    rw [hpure, hpure]
    rcases he with rfl | rfl <;>
      apply Prod.ext <;>
      simp [jordan, dot, cross, dotProduct, Fin.sum_univ_three, smul_eq_mul] <;>
      try ring
    all_goals funext i; fin_cases i <;> simp [cross, smul_eq_mul] <;> ring
  simp only [finiteDifference, hr, hs, hr', hs'] at h
  rw [add_assoc, hc] at h
  unfold residual
  exact sub_eq_zero.mp (by convert h using 1 <;> abel)

private theorem cayley_preimage_laws (e : ℝ) (he : e = 1 ∨ e = -1) (q x : Vec) :
    cayleyPreimage e q x + e • cross q (cayleyPreimage e q x) = x ∧
      dot q (cayleyPreimage e q x) = dot q x := by
  have hn : 0 ≤ dot q q := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (q i))
  have hd : 1 + dot q q ≠ 0 := by linarith
  have hd' : 1 + (q 0 * q 0 + q 1 * q 1 + q 2 * q 2) ≠ 0 := by
    simpa only [dot, dotProduct, Fin.sum_univ_three] using hd
  constructor
  · rcases he with rfl | rfl <;>
      funext i <;> fin_cases i <;>
      simp [cayleyPreimage, dot, cross, dotProduct, Fin.sum_univ_three,
        smul_eq_mul] <;> field_simp [hd'] <;> ring
  · rcases he with rfl | rfl <;>
      simp [cayleyPreimage, dot, cross, dotProduct, Fin.sum_univ_three,
        smul_eq_mul] <;> field_simp [hd'] <;> ring

private theorem residual_neg (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (e s t : ℝ) (x y : Vec) :
    residual D e (-s) (-t) (-x) (-y) = residual D e s t x y := by
  have h := label_rotation D hP hPB (-1) 0 (by norm_num) (s, x) (t, y)
  have hD : D (-s, -x) (-t, -y) = D (s, x) (t, y) := by
    simpa using h.symm
  unfold residual
  rw [hD]
  have hc : cross (-x) (-y) = cross x y := by
    funext i
    fin_cases i <;> simp [cross] <;> ring
  rw [hc]

/-- Every finite Cayley parameter is obtained from an actual pure PB triple.
The output residual is fixed; it is not rotated. No regularity of D is used. -/
theorem cayley_residual (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (e : ℝ) (he : e = 1 ∨ e = -1)
    (hpure : ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y))
    (s t : ℝ) (x y q : Vec) (hqx : dot q x = t) (hqy : dot q y = -s) :
    residual D e s t x y =
      residual D e s t (-cayleyImage e q x) (-cayleyImage e q y) := by
  let B := cayleyPreimage e q x
  let C := cayleyPreimage e q y
  have hB := cayley_preimage_laws e he q x
  have hC := cayley_preimage_laws e he q y
  have hqB : dot q B = t := hB.2.trans hqx
  have hqC : dot q C = -s := hC.2.trans hqy
  have hf := pure_phase_transport D hPB e he hpure q B C
  have hf' : residual D e s t x y =
      residual D e (-s) (-t) (cayleyImage e q x) (cayleyImage e q y) := by
    simpa only [B, C, hB.1, hC.1, hqB, hqC, neg_neg, cayleyImage] using hf
  have hn := residual_neg D hP hPB e s t
    (-cayleyImage e q x) (-cayleyImage e q y)
  exact hf'.trans (by simpa only [neg_neg] using hn)

private theorem cayley_injective (e : ℝ) (q : Vec) :
    Function.Injective (fun v : Vec => v + e • cross q v) := by
  intro u v h
  have hz : (u - v) + e • cross q (u - v) = 0 := by
    change (u - v) + e • (q ⨯₃ (u - v)) = 0
    rw [map_sub]
    have h' : u - v + e • (cross q u - cross q v) = 0 := by
      funext i
      have hi := congrFun h i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
      linarith
    exact h'
  have hd := congrArg (fun z : Vec => dot (u - v) z) hz
  have hv : dot (u - v) (u - v) = 0 := by
    simpa only [dot, dotProduct_add, dotProduct_smul, dot_cross_self,
      mul_zero, add_zero, dotProduct_zero] using hd
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hv)

/-- Reconstruction uses only the two original Gram entries and the fixed
axis equation. The finite parameter is constructed from the changed first
vector; the unchanged branch is treated separately. -/
private theorem axis_cayley_reconstruction (e : ℝ) (he : e = 1 ∨ e = -1)
    (s t : ℝ) (x y x' y' : Vec) (hw : cross x y ≠ 0)
    (hxx : dot x' x' = dot x x)
    (hxy : dot x' y' = dot x y)
    (hk : s • x' + t • y' + e • cross x' y' =
      s • x + t • y + e • cross x y) :
    (x' = x ∧ y' = y) ∨ ∃ q : Vec,
      dot q x = t ∧ dot q y = -s ∧
      -cayleyImage e q x = x' ∧ -cayleyImage e q y = y' := by
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have hx : x ≠ 0 := by intro h; subst x; exact hw (by simp [cross])
  by_cases hfix : x' = x
  · left
    refine ⟨hfix, ?_⟩
    subst x'
    let v := y' - y
    have hxv : dot x v = 0 := by
      simp only [v, dot, dotProduct_sub]
      exact sub_eq_zero.mpr hxy
    have hv : t • v + e • cross x v = 0 := by
      change t • (y' - y) + e • (x ⨯₃ (y' - y)) = 0
      rw [map_sub]
      funext i
      have hi := congrFun hk i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
      linarith
    have hsq := congrArg (fun u : Vec => dot u u) hv
    have hcx : dot (cross x v) (cross x v) = dot x x * dot v v := by
      change (x ⨯₃ v) ⬝ᵥ (x ⨯₃ v) = _
      rw [cross_dot_cross]
      change dot x x * dot v v - dot x v * dot v x = _
      simp [hxv]
    have hperp : dot v (cross x v) = 0 := dot_cross_self x v
    have hperp' : dot (cross x v) v = 0 := by
      simpa [dot, dotProduct_comm] using hperp
    have heq : (t ^ 2 + dot x x) * dot v v = 0 := by
      have hz : t * (t * dot v v) + e * (e * dot (cross x v) (cross x v)) = 0 := by
        simpa only [dot, add_dotProduct, dotProduct_add, smul_dotProduct,
          dotProduct_smul, hperp, hperp', mul_zero, zero_add, add_zero,
          dotProduct_zero] using hsq
      rw [hcx] at hz
      rcases he with rfl | rfl <;> nlinarith [hz]
    have hpos : 0 < t ^ 2 + dot x x := by
      have hxp : 0 < dot x x := lt_of_le_of_ne
        (Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i)))
        (by intro h; exact hx (dotProduct_self_eq_zero.mp h.symm))
      positivity
    have hv0 := dotProduct_self_eq_zero.mp
      ((mul_eq_zero.mp heq).resolve_left (ne_of_gt hpos))
    exact sub_eq_zero.mp hv0
  · right
    let B := (1 / 2 : ℝ) • (x - x')
    let U := (1 / 2 : ℝ) • (x + x')
    let C := (1 / 2 : ℝ) • (y - y')
    let V := (1 / 2 : ℝ) • (y + y')
    have hBU : dot B U = 0 := by
      calc
        dot B U = (1 / 4 : ℝ) * (dot x x - dot x' x') := by
          simp only [B, U, dot, smul_dotProduct, dotProduct_smul,
            sub_dotProduct, dotProduct_add, smul_eq_mul]
          rw [dotProduct_comm x x']
          ring
        _ = 0 := by rw [hxx]; ring
    have hBV : dot B V + dot U C = 0 := by
      calc
        dot B V + dot U C = (1 / 2 : ℝ) * (dot x y - dot x' y') := by
          simp only [B, V, U, C, dot, smul_dotProduct, dotProduct_smul,
            sub_dotProduct, add_dotProduct, dotProduct_add, dotProduct_sub, smul_eq_mul]
          ring
        _ = 0 := by rw [hxy]; ring
    have haxis : s • B + t • C + e • (cross B V + cross U C) = 0 := by
      funext i
      have hi := congrFun hk i
      fin_cases i <;>
        simp [B, U, C, V, cross, smul_eq_mul] at hi ⊢ <;> nlinarith only [hi]
    have hB : B ≠ 0 := by
      intro h
      apply hfix
      funext i
      have hi := congrFun h i
      simp [B, smul_eq_mul] at hi
      linarith
    let A := dot B B
    have hA : 0 < A := lt_of_le_of_ne
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg (B i)))
      (by intro h; exact hB (dotProduct_self_eq_zero.mp h.symm))
    have hA0 : A ≠ 0 := ne_of_gt hA
    let q := (t / A) • B + (e / A) • cross B U
    have hqB : dot q B = t := by
      have hc : dot (cross B U) B = 0 := by
        rw [dot, dotProduct_comm]
        exact dot_self_cross B U
      simp only [q, dot, add_dotProduct, smul_dotProduct, smul_eq_mul]
      change t / A * A + e / A * dot (cross B U) B = t
      rw [hc]
      field_simp [hA0]
    have hqcross : cross q B = e • U := by
      change ((t / A) • B + (e / A) • (B ⨯₃ U)) ⨯₃ B = e • U
      rw [map_add, map_smul, map_smul, cross_self, smul_zero, zero_add,
        cross_cross_eq_smul_sub_smul]
      have hUB : dot U B = 0 := by simpa [dot, dotProduct_comm] using hBU
      change (e / A) • (A • U - dot U B • B) = e • U
      rw [hUB, zero_smul, sub_zero, smul_smul]
      congr 1
      field_simp [hA0]
    have hU : U = e • cross q B := by rw [hqcross, smul_smul, hee, one_smul]
    have hqC : dot q C = -s := by
      have hscalar := congrArg (fun z : Vec => dot B z) haxis
      have htr : dot B (cross (cross q B) C) = dot q C * A - dot B C * t := by
        change B ⬝ᵥ ((q ⨯₃ B) ⨯₃ C) = _
        rw [cross_cross_eq_smul_sub_smul, dotProduct_sub, dotProduct_smul,
          dotProduct_smul]
        have hBq : dot B q = t := by simpa [dot, dotProduct_comm] using hqB
        change dot q C * A - dot B C * dot B q = _
        rw [hBq]
      have hz : s * A + t * dot B C +
          e * (e * (dot q C * A - dot B C * t)) = 0 := by
        rw [hU] at hscalar
        simpa only [dot, dotProduct_add, dotProduct_smul, map_smul,
          dot_self_cross, htr, add_zero, zero_add, dotProduct_zero] using hscalar
      have hz' : (s + dot q C) * A = 0 := by
        rcases he with rfl | rfl <;> nlinarith [hz]
      have hsum := (mul_eq_zero.mp hz').resolve_right hA0
      linarith
    let d := cross q C - e • V
    have hBd : cross B d = 0 := by
      have hBq : dot B q = t := by simpa [dot, dotProduct_comm] using hqB
      have hUC : cross U C = e • (dot q C • B - dot B C • q) := by
        rw [hU]
        change (e • (q ⨯₃ B)) ⨯₃ C = _
        rw [map_smul, cross_cross_eq_smul_sub_smul]
        rfl
      have hd : cross B d = -(s • B + t • C + e • (cross B V + cross U C)) := by
        change B ⨯₃ ((q ⨯₃ C) - e • V) = _
        rw [map_sub, map_smul, cross_cross_eq_smul_sub_smul', hUC]
        change dot B C • q - dot B q • C - e • cross B V = _
        rw [hBq, hqC]
        rcases he with rfl | rfl <;>
          funext i <;> simp [smul_eq_mul] <;> ring
      rw [hd, haxis, neg_zero]
    have hdotBd : dot B d = 0 := by
      have ht : dot B (cross q C) = -dot C (cross q B) := by
        simp [dot, cross, dotProduct, Fin.sum_univ_three]
        ring
      change dot B (cross q C - e • V) = 0
      simp only [dot, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      change dot B (cross q C) - e * dot B V = 0
      rw [ht, hqcross]
      have hCU : dot C U = dot U C := dotProduct_comm _ _
      simp only [dot, dotProduct_smul, smul_eq_mul]
      change -(e * dot C U) - e * dot B V = 0
      rw [hCU]
      linear_combination -e * hBV
    have hd0 : d = 0 := by
      have hc := cross_dot_cross B d B d
      change dot (cross B d) (cross B d) =
        A * dot d d - dot B d * dot d B at hc
      rw [hBd, hdotBd] at hc
      have hz : A * dot d d = 0 := by simpa [dot] using hc.symm
      exact dotProduct_self_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hA0)
    have hqcrossC : cross q C = e • V := sub_eq_zero.mp hd0
    have hV : V = e • cross q C := by rw [hqcrossC, smul_smul, hee, one_smul]
    have hxsplit : B + U = x := by funext i; simp [B, U, smul_eq_mul]; ring
    have hysplit : C + V = y := by funext i; simp [C, V, smul_eq_mul]; ring
    have hxminus : B - U = -x' := by funext i; simp [B, U, smul_eq_mul]; ring
    have hyminus : C - V = -y' := by funext i; simp [C, V, smul_eq_mul]; ring
    have hplusB : B + e • cross q B = x := by rw [← hU, hxsplit]
    have hplusC : C + e • cross q C = y := by rw [← hV, hysplit]
    have hpreB : cayleyPreimage e q x = B :=
      cayley_injective e q ((cayley_preimage_laws e he q x).1.trans hplusB.symm)
    have hpreC : cayleyPreimage e q y = C :=
      cayley_injective e q ((cayley_preimage_laws e he q y).1.trans hplusC.symm)
    refine ⟨q, ?_, ?_, ?_, ?_⟩
    · rw [← hplusB]
      simpa only [dot, dotProduct_add, dotProduct_smul, dot_self_cross,
        mul_zero, add_zero] using hqB
    · rw [← hplusC]
      simpa only [dot, dotProduct_add, dotProduct_smul, dot_self_cross,
        mul_zero, add_zero] using hqC
    · unfold cayleyImage
      rw [hpreB, ← hU, hxminus, neg_neg]
    · unfold cayleyImage
      rw [hpreC, ← hV, hyminus, neg_neg]

/-- The full first residual circle, including its identity rotation, follows
from the same pure formula and PB by a finite reconstructed substitution. -/
theorem local_full_circle (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (e : ℝ) (he : e = 1 ∨ e = -1)
    (hpure : ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y))
    (s t : ℝ) (x y : Vec) (hw : cross x y ≠ 0)
    (R : TwoAxisFiniteRotation.Orthogonal)
    (hR : R ∈ TwoAxisFiniteRotation.axisCircle
      (WithLp.toLp 2 (s • x + t • y + e • cross x y))) :
    residual D e s t (rotate R x) (rotate R y) = residual D e s t x y := by
  have hk : s • rotate R x + t • rotate R y + e • cross (rotate R x) (rotate R y) =
      s • x + t • y + e • cross x y := by
    rw [rotation_cross R hR.1]
    have h := congrArg WithLp.ofLp hR.2
    simpa only [map_add, map_smul, rotate] using h
  obtain hfix | ⟨q, hqx, hqy, hix, hiy⟩ := axis_cayley_reconstruction e he s t x y
    (rotate R x) (rotate R y) hw (rotation_dot R x x)
    (rotation_dot R x y) hk
  · rw [hfix.1, hfix.2]
  · rw [← hix, ← hiy]
    exact (cayley_residual D hP hPB e he hpure s t x y q hqx hqy).symm

private theorem residual_swap (D : E → E → E) (hP : P2 D)
    (e s t : ℝ) (x y : Vec) :
    residual D e t s y x = -residual D e s t x y := by
  have hc : cross y x = -cross x y := cross_anticomm x y |>.symm
  have hc0 : (0, e • cross y x : E) = -(0, e • cross x y) := by
    apply Prod.ext <;> simp [hc]
  unfold residual
  rw [p2_skew D hP, hc0]
  abel

private theorem local_second_circle (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (e : ℝ) (he : e = 1 ∨ e = -1)
    (hpure : ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y))
    (s t : ℝ) (x y : Vec) (hw : cross x y ≠ 0)
    (R : TwoAxisFiniteRotation.Orthogonal)
    (hR : R ∈ TwoAxisFiniteRotation.axisCircle
      (WithLp.toLp 2 (s • x + t • y - e • cross x y))) :
    residual D e s t (rotate R x) (rotate R y) = residual D e s t x y := by
  have hswap : cross y x ≠ 0 := by
    rw [show cross y x = -cross x y from (cross_anticomm x y).symm]
    exact neg_ne_zero.mpr hw
  have haxis : t • y + s • x + e • cross y x = s • x + t • y - e • cross x y := by
    rw [show cross y x = -cross x y from (cross_anticomm x y).symm, smul_neg]
    abel
  have h := local_full_circle D hP hPB e he hpure t s y x hswap R
    (by simpa only [haxis] using hR)
  rw [residual_swap D hP, residual_swap D hP] at h
  exact neg_injective h

private theorem residual_axes_nonparallel (e : ℝ) (he : e = 1 ∨ e = -1)
    (s t : ℝ) (hst : s ≠ 0 ∨ t ≠ 0) (x y : Vec) (hw : cross x y ≠ 0) :
    ⟪WithLp.toLp 2 (s • x + t • y + e • cross x y),
      WithLp.toLp 2 (s • x + t • y - e • cross x y)⟫_ℝ ^ 2 <
      ‖WithLp.toLp 2 (s • x + t • y + e • cross x y)‖ ^ 2 *
        ‖WithLp.toLp 2 (s • x + t • y - e • cross x y)‖ ^ 2 := by
  let l := s • x + t • y
  let w := cross x y
  have hl : l ≠ 0 := by
    intro hl
    have hsw : s • cross x y = 0 := by
      have hz := congrArg (fun v : Vec => cross v y) hl
      change (s • x + t • y) ⨯₃ y = 0 ⨯₃ y at hz
      simpa only [map_add, map_smul, cross_self, smul_zero, add_zero, map_zero] using hz
    have hs : s = 0 := (smul_eq_zero.mp hsw).resolve_right hw
    have hy : y ≠ 0 := by intro h; subst y; exact hw (by simp [cross])
    have hty : t • y = 0 := by simpa only [l, hs, zero_smul, zero_add] using hl
    have ht : t = 0 := (smul_eq_zero.mp hty).resolve_right hy
    exact hst.elim (fun h => h hs) (fun h => h ht)
  have hL : 0 < dot l l := lt_of_le_of_ne
    (Finset.sum_nonneg (fun i _ => mul_self_nonneg (l i)))
    (by intro h; exact hl (dotProduct_self_eq_zero.mp h.symm))
  have hW : 0 < dot w w := lt_of_le_of_ne
    (Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i)))
    (by intro h; exact hw (dotProduct_self_eq_zero.mp h.symm))
  have hlw : dot l w = 0 := by
    change (s • x + t • y) ⬝ᵥ (x ⨯₃ y) = 0
    simp only [add_dotProduct, smul_dotProduct, dot_self_cross,
      dot_cross_self, smul_zero, add_zero]
  have hwl : dot w l = 0 := by simpa [dot, dotProduct_comm] using hlw
  simp only [dot] at hL hW hlw hwl
  have hn (v : Vec) : ‖WithLp.toLp 2 v‖ ^ 2 = dot v v := by
    rw [← real_inner_self_eq_norm_sq]
    simp [dot, PiLp.inner_apply, Real.inner_apply]
  rw [hn, hn]
  simp only [PiLp.inner_apply, Real.inner_apply]
  change dot (l + e • w) (l - e • w) ^ 2 <
    dot (l + e • w) (l + e • w) * dot (l - e • w) (l - e • w)
  simp only [dot, add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hlw, hwl]
  rcases he with rfl | rfl <;> nlinarith [mul_pos hL hW]

private theorem residual_rotation_invariant (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (e : ℝ) (he : e = 1 ∨ e = -1)
    (hpure : ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y))
    (s t : ℝ) (hst : s ≠ 0 ∨ t ≠ 0) (x y : Vec) (hw : cross x y ≠ 0)
    (R : TwoAxisFiniteRotation.Orthogonal) (hR : TwoAxisFiniteRotation.determinant R = 1) :
    residual D e s t (rotate R x) (rotate R y) = residual D e s t x y := by
  let a : TwoAxisFiniteRotation.Space :=
    WithLp.toLp 2 (s • x + t • y + e • cross x y)
  let b : TwoAxisFiniteRotation.Space :=
    WithLp.toLp 2 (s • x + t • y - e • cross x y)
  let F : (TwoAxisFiniteRotation.Space × TwoAxisFiniteRotation.Space) → E :=
    fun p => residual D e s t (WithLp.ofLp p.1) (WithLp.ofLp p.2)
  apply TwoAxisFiniteRotation.moving_axis_invariance F
    (WithLp.toLp 2 x, WithLp.toLp 2 y) a b
    (residual_axes_nonparallel e he s t hst x y hw) ?_ R hR
  intro O hO T hT
  have hwO : cross (rotate O x) (rotate O y) ≠ 0 := by
    rw [rotation_cross O hO]
    intro hz
    exact hw (rotation_injective O (by simpa [rotate] using hz))
  have hplus : WithLp.toLp 2
      (s • rotate O x + t • rotate O y + e • cross (rotate O x) (rotate O y)) = O a := by
    rw [rotation_cross O hO]
    simp [a, rotate, map_add, map_smul]
  have hminus : WithLp.toLp 2
      (s • rotate O x + t • rotate O y - e • cross (rotate O x) (rotate O y)) = O b := by
    rw [rotation_cross O hO]
    simp [b, rotate, map_add, map_sub, map_smul]
  rcases hT with hT | hT
  · have h := local_full_circle D hP hPB e he hpure s t (rotate O x) (rotate O y) hwO T
      (by simpa only [hplus] using hT)
    simpa only [F, TwoAxisFiniteRotation.rotatePair, rotate] using h
  · have h := local_second_circle D hP hPB e he hpure s t (rotate O x) (rotate O y) hwO T
      (by simpa only [hminus] using hT)
    simpa only [F, TwoAxisFiniteRotation.rotatePair, rotate] using h

private def matrixEquiv (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hL : M.transpose * M = 1) (hR : M * M.transpose = 1) :
    TwoAxisFiniteRotation.Space ≃ₗ[ℝ] TwoAxisFiniteRotation.Space where
  toFun x := WithLp.toLp 2 (M *ᵥ WithLp.ofLp x)
  invFun x := WithLp.toLp 2 (M.transpose *ᵥ WithLp.ofLp x)
  left_inv x := by
    change WithLp.toLp 2 (M.transpose *ᵥ (M *ᵥ WithLp.ofLp x)) = x
    rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
    rfl
  right_inv x := by
    change WithLp.toLp 2 (M *ᵥ (M.transpose *ᵥ WithLp.ofLp x)) = x
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    rfl
  map_add' x y := by
    change WithLp.toLp 2 (M *ᵥ (WithLp.ofLp x + WithLp.ofLp y)) = _
    rw [Matrix.mulVec_add]
    rfl
  map_smul' c x := by
    change WithLp.toLp 2 (M *ᵥ (c • WithLp.ofLp x)) = _
    rw [Matrix.mulVec_smul]
    rfl

private def matrixRotation (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hL : M.transpose * M = 1) (hR : M * M.transpose = 1) :
    TwoAxisFiniteRotation.Orthogonal :=
  (matrixEquiv M hL hR).isometryOfInner (by
    intro x y
    change inner ℝ (WithLp.toLp 2 (M *ᵥ WithLp.ofLp x))
      (WithLp.toLp 2 (M *ᵥ WithLp.ofLp y)) = inner ℝ x y
    simp only [PiLp.inner_apply, Real.inner_apply]
    change (M *ᵥ WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp y) =
      WithLp.ofLp x ⬝ᵥ WithLp.ofLp y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, hL, Matrix.one_mulVec])

private theorem matrixRotation_det (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hL : M.transpose * M = 1) (hR : M * M.transpose = 1) :
    TwoAxisFiniteRotation.determinant (matrixRotation M hL hR) = M.det := by
  have hf : rotationLinear (matrixRotation M hL hR) = Matrix.toLin' M := by
    ext x i
    rfl
  have hd : LinearMap.det (rotationLinear (matrixRotation M hL hR)) = M.det := by
    rw [hf, ← LinearMap.det_toMatrix', LinearMap.toMatrix'_toLin']
  change LinearMap.det
    ((WithLp.linearEquiv 2 ℝ Vec).toLinearMap ∘ₗ
      (matrixRotation M hL hR).toLinearMap ∘ₗ
        (WithLp.linearEquiv 2 ℝ Vec).symm.toLinearMap) = M.det at hd
  rw [LinearMap.det_conj] at hd
  exact hd

private def halfSigns : Fin 4 → Vec :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

private def cycleMatrix : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ :=
  ![1, !![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0]]

private def probeMatrix (h : Fin 4) (c : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (halfSigns h) * cycleMatrix c

private theorem probe_orthogonal (h : Fin 4) (c : Fin 3) :
    (probeMatrix h c).transpose * probeMatrix h c = 1 ∧
      probeMatrix h c * (probeMatrix h c).transpose = 1 := by
  constructor <;> ext i j <;>
    fin_cases h <;> fin_cases c <;> fin_cases i <;> fin_cases j <;>
    norm_num [probeMatrix, halfSigns, cycleMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.diagonal_apply]

private def probeRotation (h : Fin 4) (c : Fin 3) : TwoAxisFiniteRotation.Orthogonal :=
  matrixRotation (probeMatrix h c) (probe_orthogonal h c).1 (probe_orthogonal h c).2

private theorem probe_det (h : Fin 4) (c : Fin 3) :
    TwoAxisFiniteRotation.determinant (probeRotation h c) = 1 := by
  rw [probeRotation, matrixRotation_det]
  fin_cases h <;> fin_cases c <;>
    norm_num [probeMatrix, halfSigns, cycleMatrix, Matrix.det_fin_three,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

private theorem four_faces (a A B C Q : ℝ)
    (h₀ : |a + A + B + C| ≤ Q) (h₁ : |a + A - B - C| ≤ Q)
    (h₂ : |a - A + B - C| ≤ Q) (h₃ : |a - A - B + C| ≤ Q) :
    |a| + |A| ≤ Q := by
  obtain ⟨hl₀, hu₀⟩ := abs_le.mp h₀
  obtain ⟨hl₁, hu₁⟩ := abs_le.mp h₁
  obtain ⟨hl₂, hu₂⟩ := abs_le.mp h₂
  obtain ⟨hl₃, hu₃⟩ := abs_le.mp h₃
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 A with hA | hA
  · rw [abs_of_nonneg ha, abs_of_nonneg hA]; linarith
  · rw [abs_of_nonneg ha, abs_of_nonpos hA]; linarith
  · rw [abs_of_nonpos ha, abs_of_nonneg hA]; linarith
  · rw [abs_of_nonpos ha, abs_of_nonpos hA]; linarith

private theorem probe_coordinate_bound (a Q : ℝ) (n z : Vec)
    (h : ∀ (j : Fin 4) (c : Fin 3),
      |a + dot (rotate (probeRotation j c) n) z| ≤ Q) (i j : Fin 3) :
    |a| + |n j * z i| ≤ Q := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 3, (cycleMatrix c *ᵥ n) i = n j := by
    fin_cases i <;> fin_cases j <;>
      first | exact ⟨0, by simp [cycleMatrix]⟩ | exact ⟨1, by simp [cycleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]⟩
        | exact ⟨2, by simp [cycleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]⟩
  let v := cycleMatrix c *ᵥ n
  have hfaces : ∀ k : Fin 4,
      |a + (halfSigns k 0 * v 0 * z 0 + halfSigns k 1 * v 1 * z 1 +
        halfSigns k 2 * v 2 * z 2)| ≤ Q := by
    intro k
    have hk := h k c
    simpa only [probeRotation, matrixRotation, matrixEquiv, rotate, probeMatrix,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, dot, dotProduct,
      Fin.sum_univ_three, v] using hk
  have h₀ := hfaces 0
  have h₁ := hfaces 1
  have h₂ := hfaces 2
  have h₃ := hfaces 3
  simp only [halfSigns, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, one_mul, neg_one_mul] at h₀ h₁ h₂ h₃
  have hi : |a| + |v i * z i| ≤ Q := by
    fin_cases i
    · apply four_faces a (v 0 * z 0) (v 1 * z 1) (v 2 * z 2) Q
      · convert h₀ using 1 <;> congr 1 <;> ring
      · convert h₁ using 1 <;> congr 1 <;> ring
      · convert h₂ using 1 <;> congr 1 <;> ring
      · convert h₃ using 1 <;> congr 1 <;> ring
    · apply four_faces a (v 1 * z 1) (v 0 * z 0) (v 2 * z 2) Q
      · convert h₀ using 1 <;> congr 1 <;> ring
      · convert h₂ using 1 <;> congr 1 <;> ring
      · convert h₁ using 1 <;> congr 1 <;> ring
      · convert h₃ using 1 <;> congr 1 <;> ring
    · apply four_faces a (v 2 * z 2) (v 0 * z 0) (v 1 * z 1) Q
      · convert h₀ using 1 <;> congr 1 <;> ring
      · convert h₃ using 1 <;> congr 1 <;> ring
      · convert h₁ using 1 <;> congr 1 <;> ring
      · convert h₂ using 1 <;> congr 1 <;> ring
  simpa only [v, hc] using hi

private theorem unit_coordinate (n : Vec) (hn : dot n n = 1) :
    ∃ j : Fin 3, (1 / 2 : ℝ) ≤ |n j| := by
  by_contra h
  push_neg at h
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have ha₀ := abs_nonneg (n 0)
  have ha₁ := abs_nonneg (n 1)
  have ha₂ := abs_nonneg (n 2)
  have hs₀ := sq_abs (n 0)
  have hs₁ := sq_abs (n 1)
  have hs₂ := sq_abs (n 2)
  have hp₀ := mul_pos (sub_pos.mpr h₀) (show 0 < 1 / 2 + |n 0| by positivity)
  have hp₁ := mul_pos (sub_pos.mpr h₁) (show 0 < 1 / 2 + |n 1| by positivity)
  have hp₂ := mul_pos (sub_pos.mpr h₂) (show 0 < 1 / 2 + |n 2| by positivity)
  simp only [dot, dotProduct, Fin.sum_univ_three] at hn
  nlinarith

private theorem support_zero_case (δ Z : ℝ) (hZ : 0 ≤ Z)
    (h : |δ| + Z ≤ 0) : δ = 0 ∧ Z = 0 := by
  have hz : Z = 0 := le_antisymm (by linarith [abs_nonneg δ]) hZ
  refine ⟨abs_eq_zero.mp (by linarith [abs_nonneg δ]), hz⟩

/-- The two saturated faces exclude any scalar and vector residual. The
vectors w,p are the actual cross and scalar-vector difference, not replacement
inputs for D. This statement also includes p=0 and the equality |p|=|w|. -/
theorem saturated_support_zero (e δ Z : ℝ) (he : e = 1 ∨ e = -1)
    (hZ : 0 ≤ Z) (w p : Vec) (hw : w ≠ 0) (hwp : dot w p = 0)
    (hbound : ∀ n : Vec, dot n n = 1 →
      |δ + e * dot n w| + Z ≤ vnorm (w + cross n p)) :
    δ = 0 ∧ Z = 0 := by
  let a := dot w w
  let b := dot p p
  let c := cross w p
  have ha : 0 < a := by
    apply lt_of_le_of_ne
    · exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
    · intro h
      exact hw (dotProduct_self_eq_zero.mp h.symm)
  have hpw : dot p w = 0 := by simpa [dot, dotProduct_comm] using hwp
  have hcw : dot c w = 0 := by
    change (w ⨯₃ p) ⬝ᵥ w = 0
    rw [dotProduct_comm]
    exact dot_self_cross w p
  have hwc : dot w c = 0 := by simpa [dot, dotProduct_comm] using hcw
  have hcp : dot c p = 0 := by
    change (w ⨯₃ p) ⬝ᵥ p = 0
    rw [dotProduct_comm]
    exact dot_cross_self w p
  have hpc : dot p c = 0 := by simpa [dot, dotProduct_comm] using hcp
  have hcc : dot c c = a * b := by
    change (w ⨯₃ p) ⬝ᵥ (w ⨯₃ p) = a * b
    rw [cross_dot_cross]
    change a * b - dot w p * dot p w = a * b
    rw [hwp, hpw]
    ring
  have hcross : cross c p = -b • w := by
    change (w ⨯₃ p) ⨯₃ p = -b • w
    rw [cross_cross_eq_smul_sub_smul]
    change dot w p • p - b • w = -b • w
    simp [hwp, neg_smul]
  have hpp : cross p p = 0 := by exact cross_self p
  have ha0 : a ≠ 0 := ne_of_gt ha
  by_cases hba : a ≤ b
  · have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hba)
    let r := Real.sqrt (b - a)
    have hr : r ^ 2 = b - a := Real.sq_sqrt (sub_nonneg.mpr hba)
    let n := (1 / b) • (c + r • p)
    have hnn : dot n n = 1 := by
      calc
        dot n n = (1 / b) ^ 2 * (dot c c + r * dot c p +
            r * dot p c + r ^ 2 * b) := by
          simp only [n, b, dot, smul_dotProduct, dotProduct_smul, add_dotProduct,
            dotProduct_add, smul_eq_mul]
          ring
        _ = 1 := by
          rw [hcc, hcp, hpc]
          field_simp [hb0]
          nlinarith [congrArg (fun u : ℝ => b * u) hr]
    have hnw : dot n w = 0 := by
      simp [n, dot, smul_dotProduct, add_dotProduct, hcw, hpw, smul_eq_mul]
    have hnp : cross n p = -w := by
      change ((1 / b) • (c + r • p)) ⨯₃ p = -w
      rw [map_smul, map_add, map_smul, hpp, smul_zero, add_zero, hcross, smul_smul]
      have hcoef : (1 / b) * (-b) = -1 := by field_simp [hb0]
      rw [hcoef, neg_one_smul]
    have hf := hbound n hnn
    rw [hnw, hnp] at hf
    simpa [vnorm, dot] using support_zero_case δ Z hZ (by simpa [vnorm, dot] using hf)
  · have hab : b < a := lt_of_not_ge hba
    let J := Real.sqrt (a - b)
    have hJ : J ^ 2 = a - b := Real.sq_sqrt (sub_nonneg.mpr (le_of_lt hab))
    have hJ0 : 0 ≤ J := Real.sqrt_nonneg _
    have test (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
        |δ + e * (σ * J)| + Z ≤ J := by
      let n := (1 / a) • (c + (σ * J) • w)
      have hnn : dot n n = 1 := by
        calc
          dot n n = (1 / a) ^ 2 * (dot c c + (σ * J) * dot c w +
              (σ * J) * dot w c + (σ * J) ^ 2 * a) := by
            simp only [n, a, dot, smul_dotProduct, dotProduct_smul, add_dotProduct,
              dotProduct_add, smul_eq_mul]
            ring
          _ = 1 := by
            rw [hcc, hcw, hwc]
            rcases hσ with rfl | rfl <;>
              field_simp [ha0] <;>
              nlinarith [hJ, congrArg (fun u : ℝ => a * u) hJ,
                congrArg (fun u : ℝ => a ^ 2 * u) hJ]
      have hnw : dot n w = σ * J := by
        simp only [n, dot, smul_dotProduct, add_dotProduct, smul_eq_mul]
        change (1 / a) * (dot c w + (σ * J) * a) = σ * J
        rw [hcw]
        field_simp [ha0]
      have hnp : cross n p = (1 / a) • (-b • w + (σ * J) • c) := by
        change ((1 / a) • (c + (σ * J) • w)) ⨯₃ p = _
        rw [map_smul, map_add, map_smul, hcross]
        rfl
      have hnorm : vnorm (w + cross n p) = J := by
        rw [hnp]
        unfold vnorm
        have hsq : dot (w + (1 / a) • (-b • w + (σ * J) • c))
            (w + (1 / a) • (-b • w + (σ * J) • c)) = J ^ 2 := by
          calc
            _ = a + (1 / a) * (-b * a + (σ * J) * dot w c) +
                (1 / a) * (-b * a + (σ * J) * dot c w) +
                (1 / a) ^ 2 *
                  ((-b) * ((-b) * a + (σ * J) * dot w c) +
                    (σ * J) * ((-b) * dot c w + (σ * J) * dot c c)) := by
              simp only [a, dot, add_dotProduct, dotProduct_add, smul_dotProduct,
                dotProduct_smul, smul_eq_mul]
              ring
            _ = J ^ 2 := by
              rw [hcw, hwc, hcc]
              rcases hσ with rfl | rfl <;>
                field_simp [ha0] <;>
                nlinarith [hJ, congrArg (fun u : ℝ => a * u) hJ,
                  congrArg (fun u : ℝ => b * u) hJ,
                  congrArg (fun u : ℝ => a ^ 2 * u) hJ,
                  congrArg (fun u : ℝ => a * b * u) hJ,
                  congrArg (fun u : ℝ => b ^ 2 * u) hJ]
        rw [hsq, Real.sqrt_sq hJ0]
      simpa only [hnw, hnorm] using hbound n hnn
    have hp := test 1 (Or.inl rfl)
    have hm := test (-1) (Or.inr rfl)
    simp only [one_mul, neg_one_mul, mul_neg] at hp hm
    rcases he with rfl | rfl
    · have hp' := (abs_le.mp (le_trans (le_add_of_nonneg_right hZ) hp))
      have hm' := (abs_le.mp (le_trans (le_add_of_nonneg_right hZ) hm))
      have hδ : δ = 0 := by linarith [hp'.2, hm'.1]
      refine ⟨hδ, ?_⟩
      rw [hδ, zero_add, one_mul, abs_of_nonneg hJ0] at hp
      linarith
    · have hp' := (abs_le.mp (le_trans (le_add_of_nonneg_right hZ) hp))
      have hm' := (abs_le.mp (le_trans (le_add_of_nonneg_right hZ) hm))
      have hδ : δ = 0 := by linarith [hp'.1, hm'.2]
      refine ⟨hδ, ?_⟩
      rw [hδ, zero_add, neg_one_mul, abs_neg, abs_of_nonneg hJ0] at hp
      linarith

private theorem unit_evaluation_bound (D : E → E → E) (hP : P2 D)
    (n : Vec) (hn : dot n n = 1) (a b : E) :
    ((D a b).1 + dot n (D a b).2) ^ 2 ≤
      dot (cross a.2 b.2 + cross n (a.1 • b.2 - b.1 • a.2))
        (cross a.2 b.2 + cross n (a.1 • b.2 - b.1 • a.2)) := by
  let α : Evaluation := ⟨1, n, by simp [vnorm, hn]⟩
  let L : E → Vec := fun a => a.2 + a.1 • n
  have hj (a b : E) : evaluate α (jordan a b) = dot (L a) (L b) := by
    have hsym : dot a.2 n = dot n a.2 := dotProduct_comm _ _
    simp only [evaluate, α, jordan, L, one_mul, dot, dotProduct_add,
      dotProduct_sub, dotProduct_smul, smul_dotProduct, add_dotProduct, smul_eq_mul]
    rw [hn, hsym]
    ring
  have hc : cross (L a) (L b) = cross a.2 b.2 + cross n (a.1 • b.2 - b.1 • a.2) := by
    funext i
    fin_cases i <;> simp [L, cross, smul_eq_mul] <;> ring
  have hgram : dot (L a) (L a) * dot (L b) (L b) - dot (L a) (L b) ^ 2 =
      dot (cross a.2 b.2 + cross n (a.1 • b.2 - b.1 • a.2))
        (cross a.2 b.2 + cross n (a.1 • b.2 - b.1 • a.2)) := by
    rw [← hc]
    change (L a) ⬝ᵥ (L a) * ((L b) ⬝ᵥ (L b)) - ((L a) ⬝ᵥ (L b)) ^ 2 =
      ((L a) ⨯₃ (L b)) ⬝ᵥ ((L a) ⨯₃ (L b))
    rw [cross_dot_cross]
    have hsym : (L b) ⬝ᵥ (L a) = (L a) ⬝ᵥ (L b) := dotProduct_comm _ _
    rw [hsym]
    ring
  have hb := p2_determinant_bound D hP α a b
  simp only [hj] at hb
  rw [hgram] at hb
  simpa only [evaluate, α, one_mul] using hb

private theorem orbit_evaluation_bound (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (e : ℝ) (he : e = 1 ∨ e = -1)
    (hpure : ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y))
    (s t : ℝ) (hst : s ≠ 0 ∨ t ≠ 0) (x y : Vec) (hw : cross x y ≠ 0)
    (n : Vec) (hn : dot n n = 1)
    (R : TwoAxisFiniteRotation.Orthogonal) (hR : TwoAxisFiniteRotation.determinant R = 1) :
    |(residual D e s t x y).1 + e * dot n (cross x y) +
      dot (rotate R n) (residual D e s t x y).2| ≤
        vnorm (cross x y + cross n (s • y - t • x)) := by
  have hF := residual_rotation_invariant D hP hPB e he hpure s t hst x y hw R hR
  have hD : D (s, rotate R x) (t, rotate R y) =
      residual D e s t x y + (0, e • rotate R (cross x y)) := by
    calc
      _ = residual D e s t (rotate R x) (rotate R y) +
          (0, e • cross (rotate R x) (rotate R y)) := by simp only [residual, sub_add_cancel]
      _ = _ := by rw [hF, rotation_cross R hR]
  have hp : s • rotate R y - t • rotate R x = rotate R (s • y - t • x) := by
    change s • rotationLinear R y - t • rotationLinear R x = rotationLinear R _
    rw [map_sub, map_smul, map_smul]
  have hcore : cross (rotate R x) (rotate R y) +
      cross (rotate R n) (s • rotate R y - t • rotate R x) =
        rotate R (cross x y + cross n (s • y - t • x)) := by
    rw [hp, rotation_cross R hR, rotation_cross R hR]
    exact (rotationLinear R).map_add _ _ |>.symm
  have hleft : (D (s, rotate R x) (t, rotate R y)).1 +
      dot (rotate R n) (D (s, rotate R x) (t, rotate R y)).2 =
        (residual D e s t x y).1 + e * dot n (cross x y) +
          dot (rotate R n) (residual D e s t x y).2 := by
    rw [hD]
    change _ + dot (rotate R n)
      ((residual D e s t x y).2 + e • rotate R (cross x y)) = _
    simp only [dot, dotProduct_add, dotProduct_smul, smul_eq_mul]
    change _ + (dot (rotate R n) (residual D e s t x y).2 +
      e * dot (rotate R n) (rotate R (cross x y))) = _
    rw [rotation_dot]
    ring
  have hnR : dot (rotate R n) (rotate R n) = 1 := (rotation_dot R n n).trans hn
  have hb := unit_evaluation_bound D hP (rotate R n) hnR
    (s, rotate R x) (t, rotate R y)
  change ((D (s, rotate R x) (t, rotate R y)).1 +
    dot (rotate R n) (D (s, rotate R x) (t, rotate R y)).2) ^ 2 ≤
      dot (cross (rotate R x) (rotate R y) + cross (rotate R n)
        (s • rotate R y - t • rotate R x))
      (cross (rotate R x) (rotate R y) + cross (rotate R n)
        (s • rotate R y - t • rotate R x)) at hb
  rw [hleft, hcore, rotation_dot] at hb
  have hv : vnorm (cross x y + cross n (s • y - t • x)) ^ 2 =
      dot (cross x y + cross n (s • y - t • x))
        (cross x y + cross n (s • y - t • x)) :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
  have hv0 : 0 ≤ vnorm (cross x y + cross n (s • y - t • x)) := Real.sqrt_nonneg _
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The exact fixed-sign pure conclusion suffices for every original input.
The only other premises are the original all-evaluation P2 and literal PB.
Finite-word generation is used through moving-axis transport, with no
continuity or equivariance premise for the unknown D. -/
theorem all_inputs_of_pure (D : E → E → E) (hP : P2 D) (hPB : PB D)
    (hpure : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ x y : Vec, D (0, x) (0, y) = (0, e • cross x y)) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ (s t : ℝ) (x y : Vec), D (s, x) (t, y) = (0, e • cross x y) := by
  obtain ⟨e, he, hpure⟩ := hpure
  refine ⟨e, he, ?_⟩
  intro s t x y
  by_cases hw : cross x y = 0
  · rw [collinear_zero D hP hPB (s, x) (t, y) hw, hw, smul_zero]
    rfl
  by_cases hst : s = 0 ∧ t = 0
  · rcases hst with ⟨rfl, rfl⟩
    exact hpure x y
  have hst' : s ≠ 0 ∨ t ≠ 0 := by tauto
  let f := residual D e s t x y
  have hwp : dot (cross x y) (s • y - t • x) = 0 := by
    have hx : dot (cross x y) x = 0 := by rw [dot, dotProduct_comm]; exact dot_self_cross x y
    have hy : dot (cross x y) y = 0 := by rw [dot, dotProduct_comm]; exact dot_cross_self x y
    simp only [dot, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    change s * dot (cross x y) y - t * dot (cross x y) x = 0
    rw [hx, hy]
    ring
  have hz (i : Fin 3) : f.1 = 0 ∧ (1 / 2 : ℝ) * |f.2 i| = 0 := by
    apply saturated_support_zero e f.1 ((1 / 2 : ℝ) * |f.2 i|) he
      (by positivity) (cross x y) (s • y - t • x) hw hwp
    intro n hn
    obtain ⟨j, hj⟩ := unit_coordinate n hn
    have hprobe (k : Fin 4) (c : Fin 3) :
        |(f.1 + e * dot n (cross x y)) + dot (rotate (probeRotation k c) n) f.2| ≤
          vnorm (cross x y + cross n (s • y - t • x)) :=
      orbit_evaluation_bound D hP hPB e he hpure s t hst' x y hw n hn
        (probeRotation k c) (probe_det k c)
    have hb := probe_coordinate_bound (f.1 + e * dot n (cross x y))
      (vnorm (cross x y + cross n (s • y - t • x))) n f.2 hprobe i j
    rw [abs_mul] at hb
    have hmul := mul_le_mul_of_nonneg_right hj (abs_nonneg (f.2 i))
    linarith
  have hf : f = 0 := by
    apply Prod.ext (hz 0).1
    funext i
    have hi := (hz i).2
    have habs : |f.2 i| = 0 := by linarith
    exact abs_eq_zero.mp habs
  exact sub_eq_zero.mp hf

end D5.S3.Quantum.SpinFactor.OriginalResidual
