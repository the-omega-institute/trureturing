/- GID: D5/S3/Topology/JBComplexification
   generality: G
   mirror-B: D5/B/S3/Topology/JBComplexification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.QuadraticAlgebra.Basic]
   utility: none
   digest: The square-sum norm on the complexification of an associative real JB algebra. -/

module

public import D5.S3.Topology.JBAlgebra
public import D5.S3.Topology.JBPositiveShift
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-! Complexification with the original JB square-sum norm. -/

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

instance complexNormedSpaceReal [L : SquareLaws R] :
    NormedSpace ℝ (Complexification R) := NormedSpace.ofCore (normCore L)

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

end D5.S3.Topology.JBComplexification
