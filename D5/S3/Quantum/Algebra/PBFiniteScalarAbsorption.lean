/- GID: D5/S3/Quantum/Algebra/PBFiniteScalarAbsorption
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBFiniteScalarAbsorption
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum]
   utility: none
   digest: Original PB and positive tables absorb scalar first images against semidefinite finite matrix second images. -/

import D5.S3.Quantum.Algebra.PBOriginalReadoutRealization
import Mathlib.Analysis.Matrix.Spectrum

/-! Scalar-first-image rigidity on literal original labels in finite matrix evaluations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped InnerProductSpace Matrix ComplexOrder

namespace D5.S3.Quantum.Algebra.PBFiniteScalarAbsorption
open PBActualOuterBudget PBOriginalReadoutRealization

section Readout
variable {E H : Type*} [AddCommGroup E] [Module ℝ E]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E}
local notation "⟪" x ", " y "⟫" => inner ℝ x y

private theorem collinear_read_zero (R : Readout (H := H) J u D ⊤)
    (x y : E) (v : H) (t : ℝ) (h : R.op y v = t • R.op x v) :
    reading R v (D x y) = 0 := by
  have hp := R.p2 v x y
  change reading R v (D x y) ^ 2 ≤
    reading R v (J x x) * reading R v (J y y) - reading R v (J x y) ^ 2 at hp
  rw [reading_jordan R (by trivial) (by trivial),
    reading_jordan R (by trivial) (by trivial),
    reading_jordan R (by trivial) (by trivial), h] at hp
  simp only [real_inner_smul_left, real_inner_smul_right] at hp
  nlinarith [sq_nonneg (reading R v (D x y))]

private theorem proportional_image_zero (R : Readout (H := H) J u D ⊤)
    (a : E) (t : ℝ) : R.op (D a (t • a)) = 0 := by
  apply (R.symmetric _).inner_map_self_eq_zero.mp
  intro v
  rw [real_inner_comm]
  exact collinear_read_zero R a (t • a) v t (by simp)

private theorem scalar_jordan (R : Readout (H := H) J u D ⊤)
    (a : E) (μ : ℝ) (ha : R.op a = μ • LinearMap.id) (b : E) :
    R.op (J a b) = μ • R.op b := by
  rw [R.jordan a (by trivial) b (by trivial), ha]
  ext v
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_smul]
  module

/-- For every eigenvector of the same original output, literal PB outer labels
force its eigenvalue times the second-input expectation to vanish. No sign or
nonzero-vector hypothesis is required. -/
private theorem scalar_eigen_pb (R : Readout (H := H) J u D ⊤) (hPB : PB J D)
    (a b : E) (μ Z : ℝ) (ha : R.op a = μ • LinearMap.id)
    (v : H) (hv : R.op (D a b) v = Z • v) :
    Z * reading R v b = 0 := by
  let k : ℝ := Z / (1 + μ ^ 2)
  let c := k • a
  let ν := D a b - J a c
  let ω := J a b + D a c
  have hk : (1 + μ ^ 2) * k = Z := by
    dsimp [k]
    field_simp
  have hc : R.op c = (k * μ) • LinearMap.id := by
    simp [c, ha, smul_smul]
  have hdc : R.op (D a c) = 0 := proportional_image_zero R a k
  have hjc := scalar_jordan R a μ ha c
  have hjb := scalar_jordan R a μ ha b
  have hν : R.op ν v = Z • v - (μ * (k * μ)) • v := by
    simp [ν, hv, hjc, hc, smul_smul]
  have hω : R.op ω = μ • R.op b := by simp [ω, hjb, hdc]
  have hplus : R.op (c + ω) v = μ • R.op (b + ν) v := by
    simp only [map_add, LinearMap.add_apply, hc, hω, LinearMap.smul_apply,
      LinearMap.id_apply, hν]
    rw [← hk]
    module
  have hminus : R.op (c - ω) v = (-μ) • R.op (b - ν) v := by
    simp only [map_sub, LinearMap.sub_apply, hc, hω, LinearMap.smul_apply,
      LinearMap.id_apply, hν]
    rw [← hk]
    module
  have hp := collinear_read_zero R (b + ν) (c + ω) v μ hplus
  have hm := collinear_read_zero R (b - ν) (c - ω) v (-μ) hminus
  have hpb := congrArg (reading R v) (hPB a b c)
  change reading R v (D (b + ν) (c + ω) - D (b - ν) (c - ω)) =
    reading R v ((-2 : ℝ) • (J b ν + J c ω)) at hpb
  simp only [map_sub, map_smul, map_add, smul_eq_mul, hp, hm, sub_self] at hpb
  rw [reading_jordan R (by trivial) (by trivial),
    reading_jordan R (by trivial) (by trivial)] at hpb
  simp only [hν, hc, LinearMap.smul_apply, LinearMap.id_apply, hω,
    inner_sub_right, real_inner_smul_right, real_inner_smul_left] at hpb
  change Z * ⟪v, R.op b v⟫ = 0
  rw [real_inner_comm v (R.op b v)] at hpb
  nlinarith
end Readout

section Matrix
variable {A E P n : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype n] [DecidableEq n]
local instance : InnerProductSpace ℝ (EuclideanSpace ℂ n) :=
  InnerProductSpace.complexToReal

private def evalOp (q : E →ₗ[ℝ] selfAdjoint (Matrix n n ℂ)) :
    E →ₗ[ℝ] (EuclideanSpace ℂ n →ₗ[ℝ] EuclideanSpace ℂ n) where
  toFun a := ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
    (q a : Matrix n n ℂ)).toLinearMap.restrictScalars ℝ
  map_add' a b := by ext v; simp
  map_smul' r a := by
    apply LinearMap.ext
    intro v
    change (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (↑(q (r • a))) v =
      r • (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (↑(q a)) v
    rw [map_smul, selfAdjoint.val_smul]
    exact congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n => T v)
      (((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv.toAlgHom.restrictScalars
        ℝ).toLinearMap.map_smul r (q a : Matrix n n ℂ))

private def evalReadout (O : OriginalData (A := A) (E := E) P)
    (q : E →ₗ[ℝ] selfAdjoint (Matrix n n ℂ))
    (hu : (q O.u : Matrix n n ℂ) = 1)
    (hJ : ∀ a b, (q (O.J a b) : Matrix n n ℂ) =
      (1 / 2 : ℝ) • ((q a : Matrix n n ℂ) * q b + (q b : Matrix n n ℂ) * q a))
    (hpositive : ∀ a, 0 ≤ O.i a → (q a : Matrix n n ℂ).PosSemidef) :
    Readout (H := EuclideanSpace ℂ n) O.J O.u O.D ⊤ where
  op := evalOp q
  symmetric a := ((q a).property.map Matrix.toEuclideanCLM).isSymmetric.restrictScalars
  unit := by ext v; simp [evalOp, hu]
  jordan a _ b _ := by
    have hr (r : ℝ) (M : Matrix n n ℂ) :
        (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (r • M) =
          r • (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) M :=
      ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv.toAlgHom.restrictScalars
        ℝ).toLinearMap.map_smul r M
    ext v
    simp [evalOp, hJ, hr]
  p2 v a b := by
    let f : E →ₗ[ℝ] ℝ := {
      toFun c := inner ℝ v (evalOp q c v)
      map_add' c d := by simp [inner_add_right]
      map_smul' r c := by simp [real_inner_smul_right] }
    have hf (c : E) (hc : 0 ≤ O.i c) : 0 ≤ f c := by
      exact (Matrix.isPositive_toEuclideanLin_iff.mpr
        (hpositive c hc)).re_inner_nonneg_right v
    exact (positive_table_transfer O.J O.D {c | 0 ≤ O.i c} O.preparation
      O.exact_cone O.raw_p2 f hf a b).2

/-- A real-linear unital Jordan evaluation into all finite selfadjoint complex
matrices absorbs the original scalar first image when the actual second image
is positive or negative semidefinite. Density or surjectivity is not needed for
this first step. The original total response is never replaced by a quotient. -/
theorem semidefinite_second_image (O : OriginalData (A := A) (E := E) P)
    (q : E →ₗ[ℝ] selfAdjoint (Matrix n n ℂ))
    (hu : (q O.u : Matrix n n ℂ) = 1)
    (hJ : ∀ a b, (q (O.J a b) : Matrix n n ℂ) =
      (1 / 2 : ℝ) • ((q a : Matrix n n ℂ) * q b + (q b : Matrix n n ℂ) * q a))
    (hpositive : ∀ a, 0 ≤ O.i a → (q a : Matrix n n ℂ).PosSemidef)
    (hPB : PB O.J O.D) (a b : E) (μ : ℝ)
    (ha : (q a : Matrix n n ℂ) = μ • (1 : Matrix n n ℂ))
    (hb : (q b : Matrix n n ℂ).PosSemidef ∨
      (-(q b : Matrix n n ℂ)).PosSemidef) :
    q (O.D a b) = 0 := by
  let R := evalReadout O q hu hJ hpositive
  have hs : R.op a = μ • LinearMap.id := by
    apply LinearMap.ext
    intro v
    change (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (↑(q a)) v = μ • v
    rw [ha]
    change ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv.toAlgHom.restrictScalars
      ℝ).toLinearMap (μ • (1 : Matrix n n ℂ)) v = _
    rw [map_smul]
    simp
  apply Subtype.ext
  change (q (O.D a b) : Matrix n n ℂ) = 0
  by_contra hn
  obtain ⟨w, Z, hZ, hw, he⟩ :=
    Matrix.IsHermitian.exists_eigenvector_of_ne_zero (q (O.D a b)).property hn
  let v : EuclideanSpace ℂ n := WithLp.toLp 2 w
  have hv : R.op (O.D a b) v = Z • v := by
    exact congrArg (WithLp.toLp 2) he
  have hp := scalar_eigen_pb R hPB a b μ Z hs v hv
  have hz : reading R v b = 0 := (mul_eq_zero.mp hp).resolve_left hZ
  have hc : star w ⬝ᵥ (q b : Matrix n n ℂ) *ᵥ w = 0 := by
    apply Complex.ext
    · change (inner ℂ v ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
        (q b : Matrix n n ℂ) v)).re = 0 at hz
      simpa only [EuclideanSpace.inner_eq_star_dotProduct,
        Matrix.ofLp_toEuclideanCLM, v, WithLp.ofLp_toLp, dotProduct_comm, Complex.zero_re] using hz
    · exact Matrix.IsHermitian.im_star_dotProduct_mulVec_self (q b).property w
  have hbw : (q b : Matrix n n ℂ) *ᵥ w = 0 := by
    rcases hb with hb | hb
    · exact hb.dotProduct_mulVec_zero_iff.mp hc
    · have hc' : star w ⬝ᵥ (-(q b : Matrix n n ℂ)) *ᵥ w = 0 := by simp only [Matrix.neg_mulVec, dotProduct_neg, hc, neg_zero]
      have ht := hb.dotProduct_mulVec_zero_iff.mp hc'
      simpa only [Matrix.neg_mulVec, neg_eq_zero] using ht
  have hbv : R.op b v = 0 := by exact congrArg (WithLp.toLp 2) hbw
  have hzero := collinear_read_zero R a b v 0 (by simp [hbv])
  change inner ℝ v (R.op (O.D a b) v) = 0 at hzero
  rw [hv, real_inner_smul_right] at hzero
  have hvne : v ≠ 0 := (WithLp.toLp_eq_zero 2).ne.mpr hw
  exact (mul_ne_zero hZ (ne_of_gt (real_inner_self_pos.mpr hvne))) hzero

#print axioms semidefinite_second_image
end Matrix

end D5.S3.Quantum.Algebra.PBFiniteScalarAbsorption
