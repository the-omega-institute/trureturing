/- GID: D5/S3/Topology/JBComplexification
   generality: G
   mirror-B: D5/B/S3/Topology/JBComplexification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.QuadraticAlgebra.Basic]
   utility: none
   digest: Original-norm JB complexification and quadratic preservation of the original square cone. -/

module

public import D5.S3.Topology.JBAlgebra
public import D5.S3.Topology.JBPositiveShift
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-! Original-norm complexification and quadratic positivity for complete raw JB algebras. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.JBComplexification

variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]

/-- The two JB square laws, on the given real algebra and its given norm. -/
class SquareLaws (R : Type*) [NormedCommRing R] : Prop where
  square_norm : ∀ r : R, ‖r ^ 2‖ = ‖r‖ ^ 2
  square_mono : ∀ r s : R, ‖r ^ 2‖ ≤ ‖r ^ 2 + s ^ 2‖

/-- The usual complexification, including the zero algebra. -/
abbrev Complexification (R : Type*) [CommRing R] := QuadraticAlgebra R (-1) 0

/-- The actual square-sum norm, before installing a metric. -/
def squareNorm (z : Complexification R) : ℝ := Real.sqrt ‖z.re ^ 2 + z.im ^ 2‖

omit [NormedAlgebra ℝ R] in
private lemma squareNorm_nonneg (z : Complexification R) : 0 ≤ squareNorm z :=
  Real.sqrt_nonneg _

omit [NormedAlgebra ℝ R] in
private lemma squareNorm_sq (z : Complexification R) :
    squareNorm z ^ 2 = ‖z.re ^ 2 + z.im ^ 2‖ := Real.sq_sqrt (norm_nonneg _)

omit [NormedAlgebra ℝ R] in
private lemma component_le (L : SquareLaws R) (z : Complexification R) :
    ‖z.re‖ ≤ squareNorm z ∧ ‖z.im‖ ≤ squareNorm z := by
  have hr := L.square_mono z.re z.im
  have hi := L.square_mono z.im z.re
  rw [L.square_norm] at hr hi
  rw [add_comm (z.im ^ 2)] at hi
  have hs := squareNorm_sq z
  have hn := squareNorm_nonneg z
  constructor <;> nlinarith [norm_nonneg z.re, norm_nonneg z.im]

omit [NormedAlgebra ℝ R] in
private lemma dot_le (L : SquareLaws R) (z w : Complexification R) :
    ‖z.re * w.re + z.im * w.im‖ ≤ squareNorm z * squareNorm w := by
  have hid : (z.re * w.re + z.im * w.im) ^ 2 +
      (z.re * w.im - z.im * w.re) ^ 2 =
      (z.re ^ 2 + z.im ^ 2) * (w.re ^ 2 + w.im ^ 2) := by ring
  have h := L.square_mono (z.re * w.re + z.im * w.im)
    (z.re * w.im - z.im * w.re)
  rw [L.square_norm, hid] at h
  have hp := norm_mul_le (z.re ^ 2 + z.im ^ 2) (w.re ^ 2 + w.im ^ 2)
  rw [← squareNorm_sq z, ← squareNorm_sq w] at hp
  have hn := mul_nonneg (squareNorm_nonneg z) (squareNorm_nonneg w)
  nlinarith [norm_nonneg (z.re * w.re + z.im * w.im)]

omit [NormedAlgebra ℝ R] in
private lemma triangle (L : SquareLaws R) (z w : Complexification R) :
    squareNorm (z + w) ≤ squareNorm z + squareNorm w := by
  let d := z.re * w.re + z.im * w.im
  have hid : (z + w).re ^ 2 + (z + w).im ^ 2 =
      (z.re ^ 2 + z.im ^ 2) + (w.re ^ 2 + w.im ^ 2) + (d + d) := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, d]
    ring
  have h := norm_add_le ((z.re ^ 2 + z.im ^ 2) + (w.re ^ 2 + w.im ^ 2)) (d + d)
  have hz := norm_add_le (z.re ^ 2 + z.im ^ 2) (w.re ^ 2 + w.im ^ 2)
  have hd := norm_add_le d d
  rw [← hid, ← squareNorm_sq (z + w)] at h
  rw [← squareNorm_sq z, ← squareNorm_sq w] at hz
  have hdot := dot_le L z w
  have hn := squareNorm_nonneg (z + w)
  have hnz := squareNorm_nonneg z
  have hnw := squareNorm_nonneg w
  change ‖d‖ ≤ _ at hdot
  nlinarith

private lemma real_smul (t : ℝ) (z : Complexification R) :
    squareNorm (t • z) = ‖t‖ * squareNorm z := by
  have hid : (t • z).re ^ 2 + (t • z).im ^ 2 =
      (t ^ 2) • (z.re ^ 2 + z.im ^ 2) := by
    change (t • z.re) ^ 2 + (t • z.im) ^ 2 = _
    simp only [Algebra.smul_def, map_pow]
    ring
  simp only [squareNorm, hid, norm_smul, norm_pow]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

omit [NormedAlgebra ℝ R] in
private lemma definite (L : SquareLaws R) (z : Complexification R) :
    squareNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    obtain ⟨hr, hi⟩ := component_le L z
    rw [h] at hr hi
    exact QuadraticAlgebra.ext (norm_eq_zero.mp (le_antisymm hr (norm_nonneg _)))
      (norm_eq_zero.mp (le_antisymm hi (norm_nonneg _)))
  · rintro rfl
    simp [squareNorm]

instance complexNorm : Norm (Complexification R) := ⟨squareNorm⟩

theorem normCore (L : SquareLaws R) : NormedSpace.Core ℝ (Complexification R) where
  norm_nonneg := squareNorm_nonneg
  norm_smul := real_smul
  norm_triangle := triangle L
  norm_eq_zero_iff := definite L

instance complexNormedAddCommGroup [L : SquareLaws R] :
    NormedAddCommGroup (Complexification R) := NormedAddCommGroup.ofCore (normCore L)

omit [NormedAlgebra ℝ R] in
theorem squareNorm_mul_le (z w : Complexification R) :
    squareNorm (z * w) ≤ squareNorm z * squareNorm w := by
  have hid : (z * w).re ^ 2 + (z * w).im ^ 2 =
      (z.re ^ 2 + z.im ^ 2) * (w.re ^ 2 + w.im ^ 2) := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    ring
  have hp := norm_mul_le (z.re ^ 2 + z.im ^ 2) (w.re ^ 2 + w.im ^ 2)
  rw [← squareNorm_sq z, ← squareNorm_sq w, ← hid, ← squareNorm_sq (z * w)] at hp
  have hn := mul_nonneg (squareNorm_nonneg z) (squareNorm_nonneg w)
  nlinarith [squareNorm_nonneg (z * w)]

instance complexNormedCommRing [SquareLaws R] : NormedCommRing (Complexification R) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := squareNorm_mul_le

/-- Complex scalars act by the actual real and imaginary components. -/
def scalarHom : ℂ →+* Complexification R where
  toFun c := ⟨algebraMap ℝ R c.re, algebraMap ℝ R c.im⟩
  map_one' := by apply QuadraticAlgebra.ext <;> simp only [Complex.one_re,
    Complex.one_im, map_one, map_zero, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by ext <;> simp
  map_add' c d := by ext <;> simp
  map_mul' c d := by
    apply QuadraticAlgebra.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, map_add, map_sub, map_mul] <;> ring

instance complexAlgebra : Algebra ℂ (Complexification R) := scalarHom.toAlgebra

theorem squareNorm_complex_smul (c : ℂ) (z : Complexification R) :
    squareNorm (c • z) = ‖c‖ * squareNorm z := by
  have hid : (c • z).re ^ 2 + (c • z).im ^ 2 =
      (c.re ^ 2 + c.im ^ 2) • (z.re ^ 2 + z.im ^ 2) := by
    change ((scalarHom c * z).re) ^ 2 + ((scalarHom c * z).im) ^ 2 = _
    change ((algebraMap ℝ R c.re) * z.re + (-1) * (algebraMap ℝ R c.im) * z.im) ^ 2 +
      ((algebraMap ℝ R c.re) * z.im + (algebraMap ℝ R c.im) * z.re +
        0 * (algebraMap ℝ R c.im) * z.im) ^ 2 = _
    simp only [Algebra.smul_def, map_add, map_pow]
    ring
  simp only [squareNorm, hid, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (sq_nonneg c.re) (sq_nonneg c.im))]
  rw [Real.sqrt_mul (add_nonneg (sq_nonneg c.re) (sq_nonneg c.im)),
    ← Complex.norm_eq_sqrt_sq_add_sq]

instance complexNormedAlgebra [SquareLaws R] : NormedAlgebra ℂ (Complexification R) where
  norm_smul_le c z := le_of_eq (squareNorm_complex_smul c z)

instance complexStarModule : StarModule ℂ (Complexification R) where
  star_smul c z := by
    change star (scalarHom c * z) = scalarHom (star c) * star z
    rw [star_mul, mul_comm]
    congr 1
    apply QuadraticAlgebra.ext <;> simp [scalarHom]

/-- The two coordinate maps, with the ordinary product norm on their codomain. -/
def coordinates : Complexification R ≃ₗ[ℝ] R × R where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NormedAlgebra ℝ R] in
private lemma norm_upper (L : SquareLaws R) (z : Complexification R) :
    squareNorm z ≤ ‖z.re‖ + ‖z.im‖ := by
  have h := norm_add_le (z.re ^ 2) (z.im ^ 2)
  rw [L.square_norm, L.square_norm, ← squareNorm_sq z] at h
  nlinarith [squareNorm_nonneg z, norm_nonneg z.re, norm_nonneg z.im,
    mul_nonneg (norm_nonneg z.re) (norm_nonneg z.im)]

instance complexCompleteSpace [L : SquareLaws R] [CompleteSpace R] :
    CompleteSpace (Complexification R) := by
  have hl : LipschitzWith 1 (coordinates (R := R)) := by
    simpa using AddMonoidHomClass.lipschitz_of_bound (coordinates (R := R)) 1 (fun z => by
      change max ‖z.re‖ ‖z.im‖ ≤ 1 * squareNorm z
      simpa only [one_mul] using max_le (component_le L z).1 (component_le L z).2)
  have ha : AntilipschitzWith 2 (coordinates (R := R)) :=
    AddMonoidHomClass.antilipschitz_of_bound (coordinates (R := R)) (fun z => by
      have h := norm_upper L z
      change squareNorm z ≤ (2 : ℝ) * max ‖z.re‖ ‖z.im‖
      linarith [le_max_left ‖z.re‖ ‖z.im‖, le_max_right ‖z.re‖ ‖z.im‖])
  exact (completeSpace_congr (e := (coordinates (R := R)).toEquiv)
    (ha.isUniformEmbedding hl.uniformContinuous)).mpr inferInstance

/-- The real subalgebra consisting of exactly the selfadjoint elements. -/
def realPart : Subalgebra ℝ (Complexification R) where
  carrier := {z | IsSelfAdjoint z}
  zero_mem' := .zero _
  one_mem' := .one _
  add_mem' := fun hx hy => hx.add hy
  mul_mem' := fun hx hy => hx.mul hy
  algebraMap_mem' t := by
    change star (QuadraticAlgebra.C (algebraMap ℝ R t) : Complexification R) =
      QuadraticAlgebra.C (algebraMap ℝ R t)
    apply QuadraticAlgebra.ext <;> simp

/-- The real algebra isomorphism onto the actual selfadjoint part. -/
def realEquiv : R ≃ₐ[ℝ] realPart (R := R) where
  toFun r := ⟨QuadraticAlgebra.C r, by apply QuadraticAlgebra.ext <;> simp⟩
  invFun z := z.val.re
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · rfl
    · have h := congrArg QuadraticAlgebra.im z.property
      change -z.val.im = z.val.im at h
      have hz : (2 : ℝ) • z.val.im = 0 := by
        rw [two_smul]
        exact neg_eq_iff_add_eq_zero.mp h
      exact (smul_eq_zero.mp hz).resolve_left (by norm_num) |>.symm
  map_mul' r s := by apply Subtype.ext; apply QuadraticAlgebra.ext <;> simp
  map_add' r s := by apply Subtype.ext; exact QuadraticAlgebra.C_add r s
  commutes' t := by apply Subtype.ext; rfl

/-- The real-algebra identification preserves precisely the original norm. -/
theorem realEquiv_isometry [L : SquareLaws R] : Isometry (realEquiv (R := R)) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro r
  change Real.sqrt ‖r ^ 2 + (0 : R) ^ 2‖ = ‖r‖
  rw [zero_pow (by decide : 2 ≠ 0), add_zero, L.square_norm,
    Real.sqrt_sq (norm_nonneg _)]

/-- The same identification, bundled as a real linear isometric equivalence. -/
def realIsometry [SquareLaws R] : R ≃ₗᵢ[ℝ] realPart (R := R) where
  __ := (realEquiv (R := R)).toLinearEquiv
  norm_map' r := by simpa using realEquiv_isometry.dist_eq r 0

instance complexCStarRing [L : SquareLaws R] : CStarRing (Complexification R) where
  norm_mul_self_le z := by
    let q := z.re ^ 2 + z.im ^ 2
    have hid : star z * z = (QuadraticAlgebra.C q : Complexification R) := by
      apply QuadraticAlgebra.ext <;>
        simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
          QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
          QuadraticAlgebra.re_C, QuadraticAlgebra.im_C, q] <;> ring
    have hr := (realIsometry (R := R)).norm_map q
    change squareNorm (QuadraticAlgebra.C q : Complexification R) = ‖q‖ at hr
    change squareNorm z * squareNorm z ≤ squareNorm (star z * z)
    rw [hid, hr]
    exact le_of_eq (by simpa only [q, pow_two] using squareNorm_sq z)

instance complexCommCStarAlgebra [SquareLaws R] [CompleteSpace R] :
    CommCStarAlgebra (Complexification R) where

section Original

open JBAlgebra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X}

/-- The actual closed single-generated subspace with its inherited norm. -/
def Generated (_A : Data X S u) (a : X) := ↥(generated S u a)

instance generatedNormedAddCommGroup (A : Data X S u) (a : X) :
    NormedAddCommGroup (Generated A a) :=
  inferInstanceAs (NormedAddCommGroup ↥(generated S u a))

instance generatedNormedSpace (A : Data X S u) (a : X) :
    NormedSpace ℝ (Generated A a) :=
  inferInstanceAs (NormedSpace ℝ ↥(generated S u a))

instance generatedMul (A : Data X S u) (a : X) : Mul (Generated A a) :=
  ⟨fun x y => ⟨S x.val y.val, (generated_algebra A a).1 x.val x.property y.val y.property⟩⟩

instance generatedOne (A : Data X S u) (a : X) : One (Generated A a) :=
  ⟨⟨u, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨0, rfl⟩)⟩⟩

instance generatedCommRing (A : Data X S u) (a : X) : CommRing (Generated A a) where
  __ := (inferInstance : AddCommGroup (Generated A a))
  mul_assoc x y z := Subtype.ext <|
    (generated_algebra A a).2.1 x.val x.property y.val y.property z.val z.property
  mul_comm x y := Subtype.ext (A.symm x.val y.val)
  one_mul x := Subtype.ext (A.unit_mul x.val)
  mul_one x := Subtype.ext ((A.symm x.val u).trans (A.unit_mul x.val))
  left_distrib x y z := Subtype.ext ((S x.val).map_add y.val z.val)
  right_distrib x y z := Subtype.ext <|
    congrArg (fun f : X →ₗ[ℝ] X => f z.val) (S.map_add x.val y.val)
  zero_mul x := Subtype.ext <|
    congrArg (fun f : X →ₗ[ℝ] X => f x.val) S.map_zero
  mul_zero x := Subtype.ext (S x.val).map_zero

instance generatedNormedCommRing (A : Data X S u) (a : X) :
    NormedCommRing (Generated A a) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := A.product_norm x.val y.val

instance generatedAlgebra (A : Data X S u) (a : X) : Algebra ℝ (Generated A a) where
  algebraMap :=
    { toFun t := t • (1 : Generated A a)
      map_one' := one_smul ℝ _
      map_zero' := zero_smul ℝ _
      map_add' t s := add_smul t s _
      map_mul' t s := by
        apply Subtype.ext
        change (t * s) • u = S (t • u) (s • u)
        simp only [map_smul, LinearMap.smul_apply, A.unit_mul, smul_smul]
        rw [mul_comm] }
  commutes' t x := mul_comm _ _
  smul_def' t x := by
    apply Subtype.ext
    change t • x.val = S (t • u) x.val
    simp only [map_smul, LinearMap.smul_apply, A.unit_mul]

instance generatedNormedAlgebra (A : Data X S u) (a : X) :
    NormedAlgebra ℝ (Generated A a) where
  norm_smul_le := norm_smul_le

instance generatedSquareLaws (A : Data X S u) (a : X) : SquareLaws (Generated A a) where
  square_norm x := by
    rw [pow_two]
    change ‖S x.val x.val‖ = ‖x.val‖ ^ 2
    exact A.square_norm x.val
  square_mono x y := by
    rw [pow_two, pow_two]
    change ‖S x.val x.val‖ ≤ ‖S x.val x.val + S y.val y.val‖
    exact A.square_mono x.val y.val

instance generatedCompleteSpace (A : Data X S u) (a : X) [CompleteSpace X] :
    CompleteSpace (Generated A a) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The concrete complexification of the actual generated JB algebra. -/
abbrev GeneratedComplex (A : Data X S u) (a : X) := Complexification (Generated A a)

end Original

open JBAlgebra JBPositiveShift
open scoped _root_.Topology

private theorem inverse_of_lower {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    [SquareLaws R] [CompleteSpace R] (a : R) (M : ℝ) (hM : 0 ≤ M)
    (hlower : ∀ r : R, ‖r‖ ≤ M * ‖a * r‖) : ∃ b : R, a * b = 1 := by
  let Z := Complexification R
  let g := gelfandStarTransform Z
  let c : Z := QuadraticAlgebra.C a
  have hc : IsUnit c := by
    by_contra hn
    obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hn
    let ε : ℝ := (M + 1)⁻¹
    have hε : 0 < ε := inv_pos.mpr (by linarith)
    let f : C(WeakDual.characterSpace ℂ Z, ℂ) :=
      ⟨fun ψ => (((‖g c ψ‖ + ε)⁻¹ : ℝ) : ℂ), by
        exact Complex.continuous_ofReal.comp
          (((map_continuous (g c)).norm.add continuous_const).inv₀
            (fun ψ => ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _) hε)))⟩
    let z : Z := g.symm f
    have hz : star z = z := by
      apply g.injective
      change g (star z) = g z
      rw [map_star]
      rw [show g z = f from g.apply_symm_apply f]
      change star f = f
      ext ψ
      simp [f]
    let r : R := (realEquiv (R := R)).symm ⟨z, hz⟩
    have hr : (QuadraticAlgebra.C r : Z) = z :=
      congrArg Subtype.val ((realEquiv (R := R)).apply_symm_apply ⟨z, hz⟩)
    have hnorm (b : R) : ‖g (QuadraticAlgebra.C b)‖ = ‖b‖ := by
      calc
        ‖g (QuadraticAlgebra.C b)‖ = ‖(QuadraticAlgebra.C b : Z)‖ :=
          (gelfandTransform_isometry Z).norm_map_of_map_zero (map_zero _) _
        _ = ‖b‖ := (realIsometry (R := R)).norm_map b
    have hprod : ‖a * r‖ ≤ 1 := by
      rw [← hnorm (a * r), QuadraticAlgebra.C_mul, map_mul, hr]
      rw [show g z = f from g.apply_symm_apply f]
      change ‖g c * f‖ ≤ 1
      apply (ContinuousMap.norm_le _ zero_le_one).mpr
      intro ψ
      change ‖g c ψ * f ψ‖ ≤ 1
      rw [norm_mul]
      change ‖g c ψ‖ * ‖(((‖g c ψ‖ + ε)⁻¹ : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
      exact (mul_inv_le_iff₀ (by positivity)).mpr (by linarith)
    have hrM : ‖r‖ ≤ M := (hlower r).trans (by nlinarith)
    have hpoint := f.norm_coe_le_norm φ
    have hgc : g c φ = 0 := hφ
    have hf : ‖f φ‖ = M + 1 := by
      change ‖(((‖g c φ‖ + ε)⁻¹ : ℝ) : ℂ)‖ = _
      rw [hgc, norm_zero, zero_add, Complex.norm_real, Real.norm_eq_abs]
      simp only [ε, inv_inv]
      exact abs_of_pos (by linarith)
    rw [hf] at hpoint
    have hfr : ‖f‖ = ‖r‖ := by
      rw [← hnorm r, hr]
      congr 1
      exact (g.apply_symm_apply f).symm
    rw [hfr] at hpoint
    linarith
  obtain ⟨v, hv⟩ := hc
  refine ⟨(↑v⁻¹ : Z).re, ?_⟩
  have he : c * (↑v⁻¹ : Z) = 1 := by rw [← hv]; exact v.val_inv
  have h := congrArg QuadraticAlgebra.re he
  change a * (↑v⁻¹ : Z).re + (-1) * 0 * (↑v⁻¹ : Z).im = 1 at h
  simpa using h

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X} [CompleteSpace X]

/-- An ambient quadratic inverse cannot hide a zero in the original single-generator spectrum.
The inverse returned here lies in the actual closed generated subspace of the same carrier. -/
theorem generated_inverse_of_quadratic_bijective (A : Data X S u) (a : X)
    (hQ : Function.Bijective (quadratic S a)) :
    ∃ b : X, b ∈ generated S u a ∧ S a b = u := by
  let Q : X →L[ℝ] X := (2 : ℝ) • ((lmul A a).comp (lmul A a)) - lmul A (S a a)
  have hq : ∀ v : X, Q v = quadratic S a v := fun _ => rfl
  let e : X ≃L[ℝ] X := ContinuousLinearEquiv.ofBijective Q
    (LinearMap.ker_eq_bot.mpr hQ.1) (LinearMap.range_eq_top.mpr hQ.2)
  let M : ℝ := ‖e.symm.toContinuousLinearMap‖
  have hlow (v : X) : ‖v‖ ≤ M * ‖quadratic S a v‖ := by
    calc
      ‖v‖ = ‖e.symm (e v)‖ := by rw [e.symm_apply_apply]
      _ ≤ M * ‖e v‖ := e.symm.toContinuousLinearMap.le_opNorm (e v)
      _ = M * ‖quadratic S a v‖ := rfl
  let R := Generated A a
  have ha : a ∈ generated S u a := by
    have h : npow S u a 1 ∈ generated S u a :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, rfl⟩)
    simpa only [npow, A.symm a u, A.unit_mul] using h
  let ar : R := ⟨a, ha⟩
  have hrestricted (r : R) : ‖r‖ ≤ M * ‖(ar * ar) * r‖ := by
    have hassoc := (generated_algebra A a).2.1 a ha a ha r.val r.property
    have hquad : quadratic S a r.val = S (S a a) r.val := by
      rw [quadratic, ← hassoc, two_smul, add_sub_cancel_right]
    have h := hlow r.val
    rw [hquad] at h
    exact h
  obtain ⟨b, hb⟩ := inverse_of_lower (ar * ar) M (norm_nonneg _) hrestricted
  refine ⟨(ar * b).val, (ar * b).property, ?_⟩
  have h : ar * (ar * b) = 1 := by rw [← mul_assoc, hb]
  exact congrArg Subtype.val h


#print axioms generated_inverse_of_quadratic_bijective

lemma real_character_value {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    [SquareLaws R] [CompleteSpace R] (r : R)
    (φ : WeakDual.characterSpace ℂ (Complexification R)) :
    (((φ (QuadraticAlgebra.C r)).re : ℝ) : ℂ) = φ (QuadraticAlgebra.C r) := by
  have hs : IsSelfAdjoint (QuadraticAlgebra.C r : Complexification R) := by
    apply QuadraticAlgebra.ext <;> simp
  exact (Complex.ofReal_eq_re_of_isSelfAdjoint (hs.map φ)).mp rfl

lemma real_character_scalar {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    [SquareLaws R] [CompleteSpace R] (t : ℝ)
    (φ : WeakDual.characterSpace ℂ (Complexification R)) :
    φ (QuadraticAlgebra.C (t • (1 : R))) = (t : ℂ) := by
  have h : (QuadraticAlgebra.C (t • (1 : R)) : Complexification R) =
      algebraMap ℂ (Complexification R) (t : ℂ) := by
    change (QuadraticAlgebra.C (t • (1 : R)) : Complexification R) = scalarHom (t : ℂ)
    apply QuadraticAlgebra.ext <;> simp [scalarHom, Algebra.smul_def]
  rw [h]
  exact AlgHomClass.commutes φ _

lemma real_gelfand_norm {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    [SquareLaws R] [CompleteSpace R] (r : R) :
    ‖gelfandStarTransform (Complexification R) (QuadraticAlgebra.C r)‖ = ‖r‖ := by
  calc
    _ = ‖(QuadraticAlgebra.C r : Complexification R)‖ :=
      (gelfandTransform_isometry _).norm_map_of_map_zero (map_zero _) _
    _ = ‖r‖ := (realIsometry (R := R)).norm_map r

private theorem positive_root_of_char_nonneg {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    [SquareLaws R] [CompleteSpace R] (a : R)
    (ha : ∀ φ : WeakDual.characterSpace ℂ (Complexification R),
      0 ≤ (φ (QuadraticAlgebra.C a)).re) :
    ∃ r : R, r * r = a ∧ ∀ φ : WeakDual.characterSpace ℂ (Complexification R),
      0 ≤ (φ (QuadraticAlgebra.C r)).re := by
  let Z := Complexification R
  let g := gelfandStarTransform Z
  let f : C(WeakDual.characterSpace ℂ Z, ℂ) :=
    ⟨fun φ => (Real.sqrt ((g (QuadraticAlgebra.C a) φ).re) : ℂ),
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (Complex.continuous_re.comp (map_continuous _)))⟩
  let z := g.symm f
  have hz : star z = z := by
    apply g.injective
    change g (star z) = g z
    rw [map_star, show g z = f from g.apply_symm_apply f]
    ext φ
    simp [f]
  let r := (realEquiv (R := R)).symm ⟨z, hz⟩
  have hr : (QuadraticAlgebra.C r : Z) = z :=
    congrArg Subtype.val ((realEquiv (R := R)).apply_symm_apply ⟨z, hz⟩)
  refine ⟨r, ?_⟩
  have hsquare : r * r = a := by
    have hh : (QuadraticAlgebra.C (r * r) : Z) = QuadraticAlgebra.C a := by
      apply g.injective
      change g (QuadraticAlgebra.C (r * r)) = g (QuadraticAlgebra.C a)
      rw [QuadraticAlgebra.C_mul, map_mul, hr,
        show g z = f from g.apply_symm_apply f]
      ext φ
      change (Real.sqrt ((φ (QuadraticAlgebra.C a)).re) : ℂ) *
        (Real.sqrt ((φ (QuadraticAlgebra.C a)).re) : ℂ) = _
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ha φ), real_character_value a φ]
      rfl
    exact congrArg QuadraticAlgebra.re hh
  refine ⟨hsquare, ?_⟩
  intro φ
  have he : g (QuadraticAlgebra.C r) = f := by
    rw [hr]
    exact g.apply_symm_apply f
  have hh := congrArg (fun k : C(WeakDual.characterSpace ℂ Z, ℂ) => (k φ).re) he
  change (φ (QuadraticAlgebra.C r)).re = Real.sqrt ((φ (QuadraticAlgebra.C a)).re) at hh
  rw [hh]
  exact Real.sqrt_nonneg _

private theorem square_of_char_nonneg {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    [SquareLaws R] [CompleteSpace R] (a : R)
    (ha : ∀ φ : WeakDual.characterSpace ℂ (Complexification R),
      0 ≤ (φ (QuadraticAlgebra.C a)).re) : ∃ r : R, r * r = a := by
  obtain ⟨r, hr, _⟩ := positive_root_of_char_nonneg a ha
  exact ⟨r, hr⟩

private theorem square_of_center_bound {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    [SquareLaws R] [CompleteSpace R] (a : R) (t : ℝ) (_ht : 0 ≤ t)
    (h : ‖a - t • 1‖ ≤ t) : ∃ r : R, r * r = a := by
  apply square_of_char_nonneg a
  intro φ
  let g := gelfandStarTransform (Complexification R)
  have hn := (g (QuadraticAlgebra.C (a - t • 1))).norm_coe_le_norm φ
  rw [real_gelfand_norm] at hn
  have he : φ (QuadraticAlgebra.C (a - t • 1)) =
      (((φ (QuadraticAlgebra.C a)).re - t : ℝ) : ℂ) := by
    calc
      _ = φ (QuadraticAlgebra.C a) - (t : ℂ) := by
        rw [QuadraticAlgebra.C_sub, map_sub, real_character_scalar]
      _ = (((φ (QuadraticAlgebra.C a)).re : ℝ) : ℂ) - (t : ℂ) :=
        congrArg (fun v : ℂ => v - (t : ℂ)) (real_character_value a φ).symm
      _ = _ := (Complex.ofReal_sub _ _).symm
  change ‖φ (QuadraticAlgebra.C (a - t • 1))‖ ≤ _ at hn
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hn
  have := (abs_le.mp (hn.trans h)).1
  linarith

private theorem center_bound_square {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    [SquareLaws R] [CompleteSpace R] (r : R) :
    ‖r * r - ‖r * r‖ • 1‖ ≤ ‖r * r‖ := by
  let Z := Complexification R
  let g := gelfandStarTransform Z
  rw [← real_gelfand_norm (r * r - ‖r * r‖ • 1)]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro φ
  let v : ℝ := (φ (QuadraticAlgebra.C r)).re
  have hcr : φ (QuadraticAlgebra.C r) = (v : ℂ) := (real_character_value r φ).symm
  have hv : φ (QuadraticAlgebra.C (r * r)) = ((v * v : ℝ) : ℂ) := by
    rw [QuadraticAlgebra.C_mul, map_mul, hcr, Complex.ofReal_mul]
  have hb := (g (QuadraticAlgebra.C (r * r))).norm_coe_le_norm φ
  rw [real_gelfand_norm] at hb
  change ‖φ (QuadraticAlgebra.C (r * r))‖ ≤ _ at hb
  rw [hv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg v)] at hb
  change ‖φ (QuadraticAlgebra.C (r * r - ‖r * r‖ • 1))‖ ≤ _
  rw [QuadraticAlgebra.C_sub, map_sub, hv, real_character_scalar,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by nlinarith [mul_self_nonneg v], by nlinarith [norm_nonneg (r * r)]⟩

theorem square_iff_center (A : Data X S u) (p : X) :
    (∃ x : X, S x x = p) ↔ ‖p - ‖p‖ • u‖ ≤ ‖p‖ := by
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ∈ generated S u x := by
      have h : npow S u x 1 ∈ generated S u x :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, rfl⟩)
      simpa only [npow, A.symm x u, A.unit_mul] using h
    exact center_bound_square (R := Generated A x) ⟨x, hx⟩
  · intro hp
    have hmem : p ∈ generated S u p := by
      have h : npow S u p 1 ∈ generated S u p :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, rfl⟩)
      simpa only [npow, A.symm p u, A.unit_mul] using h
    obtain ⟨r, hr⟩ := square_of_center_bound (R := Generated A p) ⟨p, hmem⟩
      ‖p‖ (norm_nonneg _) hp
    exact ⟨r.val, congrArg Subtype.val hr⟩

theorem square_of_ambient_center (A : Data X S u) (p : X) (t : ℝ) (ht : 0 ≤ t)
    (hp : ‖p - t • u‖ ≤ t) : ∃ x : X, S x x = p := by
  have hmem : p ∈ generated S u p := by
    have h : npow S u p 1 ∈ generated S u p :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, rfl⟩)
    simpa only [npow, A.symm p u, A.unit_mul] using h
  obtain ⟨r, hr⟩ := square_of_center_bound (R := Generated A p) ⟨p, hmem⟩ t ht hp
  exact ⟨r.val, congrArg Subtype.val hr⟩

private theorem square_closed (A : Data X S u) :
    IsClosed {p : X | ∃ x : X, S x x = p} := by
  have he : {p : X | ∃ x : X, S x x = p} = {p : X | ‖p - ‖p‖ • u‖ ≤ ‖p‖} :=
    Set.ext fun p => square_iff_center A p
  rw [he]
  exact isClosed_le (continuous_id.sub (continuous_id.norm.smul continuous_const)).norm
    continuous_id.norm

private theorem square_neighborhood (A : Data X S u) (p : X)
    (hp : ∃ x : X, S x x = p) (hQ : Function.Bijective (quadratic S p)) :
    ∃ ε > 0, ∀ y : X, ‖y - p‖ < ε → ∃ x : X, S x x = y := by
  obtain ⟨b, hb, hpb⟩ := generated_inverse_of_quadratic_bijective A p hQ
  let R := Generated A p
  have hmem : p ∈ generated S u p := by
    have h : npow S u p 1 ∈ generated S u p :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, rfl⟩)
    simpa only [npow, A.symm p u, A.unit_mul] using h
  let pr : R := ⟨p, hmem⟩
  let br : R := ⟨b, hb⟩
  have hmul : pr * br = 1 := Subtype.ext hpb
  let t : ℝ := ‖p‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hcenter : ‖p - t • u‖ < t := by
    change ‖pr - t • (1 : R)‖ < t
    rw [← real_gelfand_norm (R := R)]
    apply (ContinuousMap.norm_lt_iff _ ht).mpr
    intro φ
    let v : ℝ := (φ (QuadraticAlgebra.C pr)).re
    have hval : φ (QuadraticAlgebra.C pr) = (v : ℂ) :=
      (real_character_value pr φ).symm
    have hnonneg : 0 ≤ v := by
      have hh := (square_iff_center A p).mp hp
      have hn := (gelfandStarTransform (Complexification R)
        (QuadraticAlgebra.C (pr - ‖p‖ • 1))).norm_coe_le_norm φ
      rw [real_gelfand_norm] at hn
      change ‖φ (QuadraticAlgebra.C (pr - ‖p‖ • 1))‖ ≤ ‖p - ‖p‖ • u‖ at hn
      rw [QuadraticAlgebra.C_sub, map_sub, real_character_scalar, hval,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hn
      have h := (abs_le.mp (hn.trans hh)).1
      linarith
    have hne : v ≠ 0 := by
      intro hv
      have he := congrArg (fun r : R => φ (QuadraticAlgebra.C r)) hmul
      rw [QuadraticAlgebra.C_mul, map_mul, hval, hv, Complex.ofReal_zero,
        zero_mul, QuadraticAlgebra.C_one, map_one] at he
      exact zero_ne_one he
    have hv : 0 < v := lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hn := (gelfandStarTransform (Complexification R)
      (QuadraticAlgebra.C pr)).norm_coe_le_norm φ
    rw [real_gelfand_norm] at hn
    change ‖φ (QuadraticAlgebra.C pr)‖ ≤ ‖p‖ at hn
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv] at hn
    change ‖φ (QuadraticAlgebra.C (pr - t • 1))‖ < t
    rw [QuadraticAlgebra.C_sub, map_sub, real_character_scalar, hval,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by linarith, by dsimp [t]; linarith [norm_nonneg p]⟩
  refine ⟨t - ‖p - t • u‖, sub_pos.mpr hcenter, fun y hy => ?_⟩
  apply square_of_ambient_center A y t ht.le
  have he : y - t • u = (y - p) + (p - t • u) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

private theorem path_stays_square (A : Data X S u) (c : ℝ → X) (hc : Continuous c)
    (hinv : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective (quadratic S (c t)))
    (h1 : ∃ x : X, S x x = c 1) : ∃ x : X, S x x = c 0 := by
  let I := Set.Icc (0 : ℝ) 1
  have : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let K : Set I := {t | ∃ x : X, S x x = c t}
  have hclosed : IsClosed K := (square_closed A).preimage (hc.comp continuous_subtype_val)
  have hopen : IsOpen K := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨ε, hε, hnear⟩ := square_neighborhood A (c t) ht (hinv t t.property)
    have hf := (hc.comp continuous_subtype_val).continuousAt (x := t)
    filter_upwards [hf.eventually (Metric.ball_mem_nhds (c t) hε)] with s hs
    exact hnear _ (by simpa only [Metric.mem_ball, dist_eq_norm, Function.comp_apply] using hs)
  have hall : K = Set.univ := (show IsClopen K from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨1, by constructor <;> norm_num⟩, h1⟩
  have hzero : (⟨0, by constructor <;> norm_num⟩ : I) ∈ K := by rw [hall]; trivial
  exact hzero

omit [CompleteSpace X] in
private def productContinuous (A : Data X S u) : X →L[ℝ] X →L[ℝ] X :=
  S.mkContinuous₂ 1 (fun x y => by simpa using A.product_norm x y)

omit [CompleteSpace X] in
private theorem quadratic_continuous (A : Data X S u) {T : Type*} [TopologicalSpace T]
    {f g : T → X} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => quadratic S (f t) (g t)) := by
  have hP {v w : T → X} (hv : Continuous v) (hw : Continuous w) :
      Continuous (fun t => S (v t) (w t)) :=
    (productContinuous A).continuous₂.comp (hv.prodMk hw)
  exact ((hP hf (hP hf hg)).const_smul (2 : ℝ)).sub (hP (hP hf hf) hg)

private theorem square_shift (A : Data X S u) (y : X) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ z : X, S z z = S y y + δ • u := by
  apply square_of_ambient_center A _ (‖S y y‖ + δ) (by positivity)
  have he : S y y + δ • u - (‖S y y‖ + δ) • u = S y y - ‖S y y‖ • u := by module
  rw [he]
  exact ((square_iff_center A (S y y)).mp ⟨y, rfl⟩).trans (by linarith)

private theorem shifted_quadratic_square (A : Data X S u) (x y : X)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ z : X, S z z = quadratic S (S x x + ε • u) (S y y + δ • u) := by
  let c : ℝ → X := fun t => quadratic S
    ((1 - t) • (S x x + ε • u) + t • u) (S y y + δ • u)
  have hc : Continuous c := quadratic_continuous A
    (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)) continuous_const
  have hinv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      Function.Bijective (quadratic S (c t)) := by
    let a := (1 - t) • (S x x + ε • u) + t • u
    let s := (1 - t) * ε + t
    have hs : 0 < s := by
      dsimp [s]
      by_cases h : t = 1
      · simp [h]
      · have ht1 : t < 1 := lt_of_le_of_ne ht.2 h
        nlinarith [ht.1]
    have ha : S ((Real.sqrt (1 - t)) • x) ((Real.sqrt (1 - t)) • x) + s • u = a := by
      simp only [map_smul, LinearMap.smul_apply, smul_smul,
        Real.mul_self_sqrt (sub_nonneg.mpr ht.2)]
      dsimp [a, s]
      module
    have hA : Function.Bijective (quadratic S a) := by
      rw [← ha]
      exact positive_shift_quadratic_bijective A _ s hs
    have hB := positive_shift_quadratic_bijective A y δ hδ
    have hh := hA.comp (hB.comp hA)
    simpa only [Function.comp_def, ← fundamental_identity A] using hh
  have h1 : ∃ z : X, S z z = c 1 := by
    have he : c 1 = S y y + δ • u := by
      simp only [c, sub_self, zero_smul, one_smul, zero_add,
        quadratic, A.unit_mul, two_smul, add_sub_cancel_right]
    rw [he]
    exact square_shift A y δ hδ.le
  simpa only [c, sub_zero, one_smul, zero_smul, add_zero] using path_stays_square A c hc hinv h1

private theorem square_quadratic_square (A : Data X S u) (x y : X) :
    ∃ z : X, S z z = quadratic S (S x x) (S y y) := by
  have hc : Continuous (fun t : ℝ => quadratic S (S x x + t • u) (S y y + t • u)) :=
    quadratic_continuous A (continuous_const.add (continuous_id.smul continuous_const))
      (continuous_const.add (continuous_id.smul continuous_const))
  have ht : Filter.Tendsto (fun t : ℝ => quadratic S (S x x + t • u) (S y y + t • u))
      (𝓝[>] 0) (𝓝 (quadratic S (S x x) (S y y))) := by
    simpa only [zero_smul, add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  apply (square_closed A).mem_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact shifted_quadratic_square A x y t t ht ht

private theorem positive_root_inverse {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    [SquareLaws R] [CompleteSpace R] (b : R)
    (hb : ∀ φ : WeakDual.characterSpace ℂ (Complexification R),
      0 < (φ (QuadraticAlgebra.C b)).re) :
    ∃ c d t : R, c * c = b ∧ c * d = 1 ∧ t * t = d := by
  obtain ⟨c, hc, hcp⟩ := positive_root_of_char_nonneg b (fun φ => (hb φ).le)
  have hcpos (φ : WeakDual.characterSpace ℂ (Complexification R)) :
      0 < (φ (QuadraticAlgebra.C c)).re := by
    have hne : (φ (QuadraticAlgebra.C c)).re ≠ 0 := by
      intro hzero
      have he := congrArg (fun r : R => φ (QuadraticAlgebra.C r)) hc
      have hv : φ (QuadraticAlgebra.C c) = 0 := by
        rw [← real_character_value c φ, hzero, Complex.ofReal_zero]
      rw [QuadraticAlgebra.C_mul, map_mul, hv, zero_mul] at he
      have hr := congrArg Complex.re he
      simp only [Complex.zero_re] at hr
      linarith [hb φ]
    exact lt_of_le_of_ne (hcp φ) (Ne.symm hne)
  let Z := Complexification R
  let g := gelfandStarTransform Z
  have hgunit : IsUnit (g (QuadraticAlgebra.C c)) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro φ hzero
    have h : (φ (QuadraticAlgebra.C c)).re = 0 := congrArg Complex.re hzero
    linarith [hcpos φ]
  have hu : IsUnit (QuadraticAlgebra.C c : Z) := by
    have h := hgunit.map g.symm.toRingHom
    change IsUnit (g.symm (g (QuadraticAlgebra.C c))) at h
    rw [g.symm_apply_apply] at h
    exact h
  obtain ⟨v, hv⟩ := hu
  let d : R := (↑v⁻¹ : Z).re
  have hcd : c * d = 1 := by
    have he : (QuadraticAlgebra.C c : Z) * (↑v⁻¹ : Z) = 1 := by
      rw [← hv]
      exact v.val_inv
    have h := congrArg QuadraticAlgebra.re he
    change c * d + (-1) * 0 * (↑v⁻¹ : Z).im = 1 at h
    simpa using h
  have hdpos (φ : WeakDual.characterSpace ℂ Z) :
      0 ≤ (φ (QuadraticAlgebra.C d)).re := by
    let cv : ℝ := (φ (QuadraticAlgebra.C c)).re
    let dv : ℝ := (φ (QuadraticAlgebra.C d)).re
    have hcv : φ (QuadraticAlgebra.C c) = (cv : ℂ) := (real_character_value c φ).symm
    have hdv : φ (QuadraticAlgebra.C d) = (dv : ℂ) := (real_character_value d φ).symm
    have he := congrArg (fun r : R => φ (QuadraticAlgebra.C r)) hcd
    rw [QuadraticAlgebra.C_mul, map_mul, hcv, hdv, QuadraticAlgebra.C_one, map_one] at he
    have hr : cv * dv = 1 := by
      have h := congrArg Complex.re he
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.one_re] using h
    have hpos : 0 < cv := hcpos φ
    change 0 ≤ dv
    nlinarith
  obtain ⟨t, ht⟩ := square_of_char_nonneg d hdpos
  exact ⟨c, d, t, hc, hcd, ht⟩

private theorem arbitrary_quadratic_shift_square (A : Data X S u) (a y : X)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ z : X, S z z = quadratic S a (S y y + δ • u) := by
  let R := Generated A y
  have hmem : y ∈ generated S u y := by
    have h : npow S u y 1 ∈ generated S u y :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, rfl⟩)
    simpa only [npow, A.symm y u, A.unit_mul] using h
  let yr : R := ⟨y, hmem⟩
  let b : R := yr * yr + δ • 1
  have hbpos (φ : WeakDual.characterSpace ℂ (Complexification R)) :
      0 < (φ (QuadraticAlgebra.C b)).re := by
    let v : ℝ := (φ (QuadraticAlgebra.C yr)).re
    have hv : φ (QuadraticAlgebra.C yr) = (v : ℂ) := (real_character_value yr φ).symm
    change 0 < (φ (QuadraticAlgebra.C (yr * yr + δ • 1))).re
    rw [QuadraticAlgebra.C_add, map_add, QuadraticAlgebra.C_mul, map_mul,
      real_character_scalar, hv]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  obtain ⟨c, d, t, hcc, hcd, htt⟩ := positive_root_inverse b hbpos
  have hccX : S c.val c.val = S y y + δ • u := congrArg Subtype.val hcc
  have httX : S t.val t.val = d.val := congrArg Subtype.val htt
  have hUu (v : X) : quadratic S u v = v := by
    simp only [quadratic, A.unit_mul, two_smul, add_sub_cancel_right]
  have hUc (v : X) : quadratic S v u = S v v := by
    have hu (w : X) : S w u = w := (A.symm w u).trans (A.unit_mul w)
    rw [quadratic, hu, hu, two_smul, add_sub_cancel_right]
  have hQcc (v : X) : quadratic S (S y y + δ • u) v =
      quadratic S c.val (quadratic S c.val v) := by
    have h := fundamental_identity A c.val u v
    simpa only [hUc, hUu, hccX] using h
  have hB := positive_shift_quadratic_bijective A y δ hδ
  have hcinj : Function.Injective (quadratic S c.val) := by
    intro v w hvw
    apply hB.1
    rw [hQcc, hQcc, hvw]
  have hccd : (c * c) * d = c := by rw [mul_assoc, hcd, mul_one]
  have hqR : (2 : ℝ) • (c * (c * d)) - (c * c) * d = c := by
    rw [hcd, mul_one, hccd, two_smul, add_sub_cancel_right]
  have hqcd : quadratic S c.val d.val = c.val := congrArg Subtype.val hqR
  have hinvc (v : X) : quadratic S d.val (quadratic S c.val v) = v := by
    apply hcinj
    rw [← fundamental_identity A, hqcd]
  have hsquare : S (quadratic S c.val a) (quadratic S c.val a) =
      quadratic S c.val (quadratic S a (S y y + δ • u)) := by
    have h := fundamental_identity A c.val a u
    simpa only [hUc, hccX] using h
  obtain ⟨z, hz⟩ := square_quadratic_square A t.val (quadratic S c.val a)
  rw [httX, hsquare, hinvc] at hz
  exact ⟨z, hz⟩

/-- Every quadratic representation preserves the actual original square cone of an arbitrary
complete real six-law JB algebra. The square root belongs to the same original carrier. -/
theorem quadratic_preserves_squares (A : Data X S u) (a x : X) :
    ∃ y : X, quadratic S a (S x x) = S y y := by
  have hc : Continuous (fun t : ℝ => quadratic S a (S x x + t • u)) :=
    quadratic_continuous A continuous_const
      (continuous_const.add (continuous_id.smul continuous_const))
  have ht : Filter.Tendsto (fun t : ℝ => quadratic S a (S x x + t • u))
      (𝓝[>] 0) (𝓝 (quadratic S a (S x x))) := by
    simpa only [zero_smul, add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hsq : ∃ y : X, S y y = quadratic S a (S x x) := by
    apply (square_closed A).mem_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact arbitrary_quadratic_shift_square A a x t ht
  obtain ⟨y, hy⟩ := hsq
  exact ⟨y, hy.symm⟩

#print axioms quadratic_preserves_squares

end D5.S3.Topology.JBComplexification
