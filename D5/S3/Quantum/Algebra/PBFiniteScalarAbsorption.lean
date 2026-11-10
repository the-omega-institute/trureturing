/- GID: D5/S3/Quantum/Algebra/PBFiniteScalarAbsorption
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBFiniteScalarAbsorption
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum]
   utility: none
   digest: Finite matrix scalar-image absorption and Jordan orthogonality. -/

import D5.S3.Quantum.Algebra.PBOriginalReadoutRealization
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Scalar-first-image rigidity on literal original labels in finite matrix evaluations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped InnerProductSpace Matrix ComplexOrder

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/28642 -/

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
private theorem correction_pb (R : Readout (H := H) J u D ⊤) (hPB : PB J D)
    (a b c : E) (μ : ℝ) (ha : R.op a = μ • LinearMap.id)
    (hdc : R.op (D a c) = 0) (v : H)
    (hcv : (1 + μ ^ 2) • R.op c v = μ • R.op (D a b) v) :
    inner ℝ (R.op b v) (R.op (D a b) v) = 0 := by
  let ν := D a b - J a c
  let ω := J a b + D a c
  have hν : R.op ν v = R.op (D a b) v - μ • R.op c v := by
    simp [ν, scalar_jordan R a μ ha]
  have hω : R.op ω = μ • R.op b := by
    simp [ω, scalar_jordan R a μ ha, hdc]
  have hcv' : R.op c v = μ • R.op (D a b) v - μ ^ 2 • R.op c v := by
    calc
      _ = (1 + μ ^ 2) • R.op c v - μ ^ 2 • R.op c v := by module
      _ = _ := by rw [hcv]
  have hp := collinear_read_zero R (b + ν) (c + ω) v μ (by
    simp only [map_add, LinearMap.add_apply, hν, hω, LinearMap.smul_apply]
    conv_lhs => rw [hcv']
    module)
  have hm := collinear_read_zero R (b - ν) (c - ω) v (-μ) (by
    simp only [map_sub, LinearMap.sub_apply, hν, hω, LinearMap.smul_apply]
    conv_lhs => rw [hcv']
    module)
  have he := congrArg (reading R v) (hPB a b c)
  change reading R v (D (b + ν) (c + ω) - D (b - ν) (c - ω)) =
    reading R v ((-2 : ℝ) • (J b ν + J c ω)) at he
  simp only [map_sub, map_smul, map_add, smul_eq_mul, hp, hm, sub_self] at he
  rw [reading_jordan R (by trivial) (by trivial),
    reading_jordan R (by trivial) (by trivial)] at he
  simp only [hν, hω, LinearMap.smul_apply, inner_sub_right,
    real_inner_smul_right] at he
  rw [real_inner_comm (R.op b v) (R.op c v)] at he
  nlinarith

private theorem quadratic_read_zero (S T : H →ₗ[ℝ] H)
    (w : H) (hw : inner ℝ w (S w) ≠ 0)
    (h : ∀ v, inner ℝ v (S v) ≠ 0 → inner ℝ v (T v) = 0) :
    ∀ v, inner ℝ v (T v) = 0 := by
  intro v
  let f : Polynomial ℝ := Polynomial.C (inner ℝ v (S v)) +
    Polynomial.C (inner ℝ v (S w) + inner ℝ w (S v)) * Polynomial.X +
    Polynomial.C (inner ℝ w (S w)) * Polynomial.X ^ 2
  let g : Polynomial ℝ := Polynomial.C (inner ℝ v (T v)) +
    Polynomial.C (inner ℝ v (T w) + inner ℝ w (T v)) * Polynomial.X +
    Polynomial.C (inner ℝ w (T w)) * Polynomial.X ^ 2
  have hf (t : ℝ) : f.eval t = inner ℝ (v + t • w) (S (v + t • w)) := by
    simp [f, map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    ring
  have hg (t : ℝ) : g.eval t = inner ℝ (v + t • w) (T (v + t • w)) := by
    simp [g, map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    ring
  have hfg : f * g = 0 := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_mul, Polynomial.eval_zero]
    by_cases ht : f.eval t = 0
    · simp [ht]
    · rw [hg, h (v + t • w) (by rwa [← hf]), mul_zero]
  have hfne : f ≠ 0 := by
    intro hfz
    have he := congrArg (fun p : Polynomial ℝ => p.coeff 2) hfz
    have he' : inner ℝ w (S w) = 0 := by simpa [f] using he
    exact hw he'
  have hgz : g = 0 := (mul_eq_zero.mp hfg).resolve_left hfne
  have he := congrArg (fun p : Polynomial ℝ => p.coeff 0) hgz
  simpa [g] using he

end Readout

section Matrix
variable {A E P n : Type*}
variable [CStarAlgebra A] [PartialOrder A]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype n] [DecidableEq n]
open scoped Matrix.Norms.L2Operator MatrixOrder
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

private theorem evalOp_injective (q : E →ₗ[ℝ] selfAdjoint (Matrix n n ℂ))
    (x : E) (hx : evalOp q x = 0) : q x = 0 := by
  apply Subtype.ext
  change (q x : Matrix n n ℂ) = 0
  apply (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).injective
  rw [map_zero]
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun T : EuclideanSpace ℂ n →ₗ[ℝ] EuclideanSpace ℂ n => T v) hx

private theorem eval_skew (O : OriginalData (A := A) (E := E) P)
    (q : E →ₗ[ℝ] selfAdjoint (Matrix n n ℂ))
    (hu : (q O.u : Matrix n n ℂ) = 1)
    (hJ : ∀ a b, (q (O.J a b) : Matrix n n ℂ) =
      (1 / 2 : ℝ) • ((q a : Matrix n n ℂ) * q b + (q b : Matrix n n ℂ) * q a))
    (hpositive : ∀ a, 0 ≤ O.i a → (q a : Matrix n n ℂ).PosSemidef)
    (a b : E) : q (O.D b a) = -q (O.D a b) := by
  let R := evalReadout O q hu hJ hpositive
  have hz : q (O.D b a + O.D a b) = 0 := by
    apply evalOp_injective q
    apply (R.symmetric _).inner_map_self_eq_zero.mp
    intro v
    rw [real_inner_comm]
    let f := reading R v
    have hf (c : E) (hc : 0 ≤ O.i c) : 0 ≤ f c :=
      (Matrix.isPositive_toEuclideanLin_iff.mpr (hpositive c hc)).re_inner_nonneg_right v
    have ht := (positive_table_transfer O.J O.D {c | 0 ≤ O.i c} O.preparation
      O.exact_cone O.raw_p2 f hf a b).1.1
    have he := congrArg Complex.im (congrFun (congrFun ht 0) 1)
    have hd : f (O.D b a) = -f (O.D a b) := by
      simpa [originalTable, Matrix.conjTranspose_apply] using he
    change f (O.D b a + O.D a b) = 0
    simp [hd]
  simpa only [map_add, add_eq_zero_iff_eq_neg] using hz

private theorem zero_second_image (O : OriginalData (A := A) (E := E) P)
    (q : E →ₗ[ℝ] selfAdjoint (Matrix n n ℂ))
    (hu : (q O.u : Matrix n n ℂ) = 1)
    (hJ : ∀ a b, (q (O.J a b) : Matrix n n ℂ) =
      (1 / 2 : ℝ) • ((q a : Matrix n n ℂ) * q b + (q b : Matrix n n ℂ) * q a))
    (hpositive : ∀ a, 0 ≤ O.i a → (q a : Matrix n n ℂ).PosSemidef)
    (a b : E) (hb : q b = 0) : q (O.D a b) = 0 := by
  let R := evalReadout O q hu hJ hpositive
  apply evalOp_injective q
  apply (R.symmetric _).inner_map_self_eq_zero.mp
  intro v
  rw [real_inner_comm]
  exact collinear_read_zero R a b v 0 (by simp [R, evalReadout, evalOp, hb])

private theorem positive_square_lift (O : OriginalData (A := A) (E := E) P)
    (q : E →ₗ[ℝ] selfAdjoint (Matrix n n ℂ)) (hq : Function.Surjective q)
    (hJ : ∀ a b, (q (O.J a b) : Matrix n n ℂ) =
      (1 / 2 : ℝ) • ((q a : Matrix n n ℂ) * q b + (q b : Matrix n n ℂ) * q a))
    (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    ∃ e : E, (q (O.J e e) : Matrix n n ℂ) = M := by
  obtain ⟨e, he⟩ := hq ⟨CFC.sqrt M, IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)⟩
  refine ⟨e, ?_⟩
  have he' : (q e : Matrix n n ℂ) = CFC.sqrt M := congrArg Subtype.val he
  rw [hJ, he']
  have ht : (1 / 2 : ℝ) • (CFC.sqrt M * CFC.sqrt M +
      CFC.sqrt M * CFC.sqrt M) = CFC.sqrt M * CFC.sqrt M := by module
  rw [ht, CFC.sqrt_mul_sqrt_self M hM.nonneg]

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

/-- A dense linear finite-matrix evaluation forces the second image to be
Jordan orthogonal to the same actual scalar-first-image response. -/
theorem scalar_second_jordan_zero (O : OriginalData (A := A) (E := E) P)
    (q : E →ₗ[ℝ] selfAdjoint (Matrix n n ℂ))
    (hu : (q O.u : Matrix n n ℂ) = 1)
    (hJ : ∀ a b, (q (O.J a b) : Matrix n n ℂ) =
      (1 / 2 : ℝ) • ((q a : Matrix n n ℂ) * q b + (q b : Matrix n n ℂ) * q a))
    (hpositive : ∀ a, 0 ≤ O.i a → (q a : Matrix n n ℂ).PosSemidef)
    (hPB : PB O.J O.D) (hdense : DenseRange q) (a b : E) (μ : ℝ)
    (ha : (q a : Matrix n n ℂ) = μ • (1 : Matrix n n ℂ)) :
    q (O.J b (O.D a b)) = 0 := by
  let R := evalReadout O q hu hJ hpositive
  let H := O.D a b
  let incl : selfAdjoint (Matrix n n ℂ) →ₗ[ℝ] Matrix n n ℂ := {
    toFun := Subtype.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
    FiniteDimensional.of_injective incl Subtype.coe_injective
  have hsurj : Function.Surjective q := by
    have hc : IsClosed (Set.range q) := (LinearMap.range q).closed_of_finiteDimensional
    intro M
    simpa only [hc.closure_eq, Set.mem_range] using hdense M
  have hs : R.op a = μ • LinearMap.id := by
    apply LinearMap.ext
    intro v
    change (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (↑(q a)) v = μ • v
    rw [ha]
    change ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv.toAlgHom.restrictScalars
      ℝ).toLinearMap (μ • (1 : Matrix n n ℂ)) v = _
    rw [map_smul]
    simp
  have hinj (x : E) (hx : R.op x = 0) : q x = 0 := by
    apply Subtype.ext
    change (q x : Matrix n n ℂ) = 0
    apply (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).injective
    rw [map_zero]
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun T : EuclideanSpace ℂ n →ₗ[ℝ] EuclideanSpace ℂ n => T v) hx
  have hzero : q H = 0 → q (O.J b H) = 0 := by
    intro hz
    apply Subtype.ext
    simpa [hz] using hJ b H
  by_cases hH : q H = 0
  · exact hzero hH
  by_cases hμ : μ = 0
  · have hz : R.op H = 0 := by
      apply (R.symmetric H).inner_map_self_eq_zero.mp
      intro v
      rw [real_inner_comm]
      have hp := R.p2 v a b
      change reading R v H ^ 2 ≤
        reading R v (O.J a a) * reading R v (O.J b b) - reading R v (O.J a b) ^ 2 at hp
      rw [reading_jordan R (by trivial) (by trivial),
        reading_jordan R (by trivial) (by trivial),
        reading_jordan R (by trivial) (by trivial)] at hp
      simp only [hs, hμ, zero_smul, LinearMap.zero_apply, inner_zero_left,
        inner_zero_right, zero_mul] at hp
      change reading R v H = 0
      nlinarith [sq_nonneg (reading R v H)]
    exact (hH (hinj H hz)).elim
  have hnonzero : ∃ w : EuclideanSpace ℂ n, inner ℝ w (R.op H w) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hz : R.op H = 0 := (R.symmetric H).inner_map_self_eq_zero.mp
      (fun w => by rw [real_inner_comm]; exact hh w)
    exact hH (hinj H hz)
  obtain ⟨w, hw⟩ := hnonzero
  have hread : ∀ v : EuclideanSpace ℂ n, inner ℝ v (R.op H v) ≠ 0 →
      inner ℝ v (R.op (O.J b H) v) = 0 := by
    intro v hv
    let τ : ℝ := μ / (1 + μ ^ 2)
    let W : EuclideanSpace ℂ n := τ • R.op H v
    let r : ℝ := inner ℝ v W
    have hτ : τ ≠ 0 := div_ne_zero hμ (by positivity)
    have hr : r ≠ 0 := by simpa [r, W, real_inner_smul_right] using mul_ne_zero hτ hv
    let M : Matrix n n ℂ := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
      (InnerProductSpace.rankOne ℂ W W)
    have hM : M.PosSemidef := by
      apply Matrix.isPositive_toEuclideanLin_iff.mp
      simpa only [M, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
        StarAlgEquiv.apply_symm_apply] using
        (InnerProductSpace.isPositive_rankOne_self W).toLinearMap
    let C : Matrix n n ℂ := r⁻¹ • M
    have hsemi : C.PosSemidef ∨ (-C).PosSemidef := by
      by_cases hrp : 0 ≤ r⁻¹
      · exact Or.inl (hM.smul hrp)
      · right
        have hp := hM.smul (le_of_lt (neg_pos.mpr (lt_of_not_ge hrp)))
        simpa only [C, neg_smul] using hp
    obtain ⟨c, hc⟩ : ∃ c : E, (q c : Matrix n n ℂ) = C := by
      rcases hsemi with hp | hp
      · obtain ⟨e, he⟩ := positive_square_lift O q hsurj hJ C hp
        exact ⟨O.J e e, he⟩
      · obtain ⟨e, he⟩ := positive_square_lift O q hsurj hJ (-C) hp
        exact ⟨-O.J e e, by simpa using congrArg Neg.neg he⟩
    have hdc : R.op (O.D a c) = 0 := by
      have hd := semidefinite_second_image O q hu hJ hpositive hPB a c μ ha
        (by simpa only [hc] using hsemi)
      change evalOp q (O.D a c) = 0
      apply LinearMap.ext
      intro z
      simp [evalOp, hd]
    have hrC : inner ℂ W v = (r : ℂ) := by
      have hsym := ((q H).property.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))).isSymmetric
      apply Complex.ext
      · change (inner ℂ W v).re = r
        exact inner_re_symm (𝕜 := ℂ) W v
      · change (inner ℂ W v).im = 0
        change (inner ℂ (τ • (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
          (q H : Matrix n n ℂ) v) v).im = 0
        have him : (inner ℂ ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
            (q H : Matrix n n ℂ) v) v).im = 0 := hsym.im_inner_apply_self v
        rw [inner_smul_left_eq_smul (𝕝 := ℝ)]
        simpa only [← RCLike.im_eq_complex_im, RCLike.smul_im, mul_zero] using
          congrArg (fun t : ℝ => τ * t) him
    have hact : R.op c v = W := by
      change (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (q c : Matrix n n ℂ) v = W
      rw [hc]
      have ht : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) C =
          r⁻¹ • InnerProductSpace.rankOne ℂ W W := by
        change ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv.toAlgHom.restrictScalars
          ℝ).toLinearMap (r⁻¹ • M) = _
        rw [map_smul]
        change r⁻¹ • ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) M) = _
        change r⁻¹ • ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
          ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm _)) = _
        rw [StarAlgEquiv.apply_symm_apply]
      rw [ht]
      simp only [smul_apply, InnerProductSpace.rankOne_apply, hrC]
      simp [hr]
    have hcv : (1 + μ ^ 2) • R.op c v = μ • R.op H v := by
      rw [hact]
      simp only [W, smul_smul]
      congr 1
      dsimp [τ]
      field_simp
    have ht := correction_pb R hPB a b c μ hs hdc v hcv
    exact (reading_jordan R (by trivial) (by trivial) v).trans ht
  have hall := quadratic_read_zero (R.op H) (R.op (O.J b H)) w hw hread
  apply hinj
  exact (R.symmetric _).inner_map_self_eq_zero.mp
    (fun v => by rw [real_inner_comm]; exact hall v)

/-- The second fixed table is an actual original PB call. Image-zero labels
remain in its arguments; only their images and their P2 readings are simplified. -/
theorem scalar_second_actual_table (O : OriginalData (A := A) (E := E) P)
    (q : E →ₗ[ℝ] selfAdjoint (Matrix n n ℂ))
    (hu : (q O.u : Matrix n n ℂ) = 1)
    (hJ : ∀ a b, (q (O.J a b) : Matrix n n ℂ) =
      (1 / 2 : ℝ) • ((q a : Matrix n n ℂ) * q b + (q b : Matrix n n ℂ) * q a))
    (hpositive : ∀ a, 0 ≤ O.i a → (q a : Matrix n n ℂ).PosSemidef)
    (hPB : PB O.J O.D) (a b : E) (μ : ℝ)
    (ha : (q a : Matrix n n ℂ) = μ • (1 : Matrix n n ℂ)) :
    let ν := O.D b a - O.J b (μ • b)
    let ω := O.J b a + O.D b (μ • b)
    let x := a + ν
    let y := μ • b + ω
    (q x : Matrix n n ℂ) = μ • (1 - (q b : Matrix n n ℂ) ^ 2) - q (O.D a b) ∧
    (q y : Matrix n n ℂ) = (2 * μ) • (q b : Matrix n n ℂ) ∧
    q (O.D x y) = (2 * μ) • q (O.D a b) := by
  let R := evalReadout O q hu hJ hpositive
  have hprop : q (O.D b (μ • b)) = 0 :=
    evalOp_injective q _ (proportional_image_zero R b μ)
  have hskew := eval_skew O q hu hJ hpositive a b
  have hjba : (q (O.J b a) : Matrix n n ℂ) = μ • (q b : Matrix n n ℂ) := by
    rw [hJ, ha, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
    module
  have hjbb : (q (O.J b (μ • b)) : Matrix n n ℂ) =
      μ • ((q b : Matrix n n ℂ) ^ 2) := by
    rw [hJ]
    simp only [map_smul, selfAdjoint.val_smul, Matrix.mul_smul, Matrix.smul_mul, pow_two]
    module
  have hminus : q (μ • b - (O.J b a + O.D b (μ • b))) = 0 := by
    apply Subtype.ext
    simp only [map_sub, map_add, map_smul, AddSubgroupClass.coe_sub,
      AddSubgroup.coe_add, selfAdjoint.val_smul, hjba, hprop, ZeroMemClass.coe_zero]
    module
  have hm := zero_second_image O q hu hJ hpositive
    (a - (O.D b a - O.J b (μ • b))) _ hminus
  have he := congrArg (fun e : E => (q e : Matrix n n ℂ)) (hPB b a (μ • b))
  dsimp only at he ⊢
  have hν : (q (O.D b a - O.J b (μ • b)) : Matrix n n ℂ) =
      -(q (O.D a b) : Matrix n n ℂ) - μ • ((q b : Matrix n n ℂ) ^ 2) := by
    simp only [map_sub, AddSubgroupClass.coe_sub, hskew, NegMemClass.coe_neg, hjbb]
  have hω : (q (O.J b a + O.D b (μ • b)) : Matrix n n ℂ) =
      μ • (q b : Matrix n n ℂ) := by simp [hjba, hprop]
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_add, AddSubgroup.coe_add, ha, hν]
    module
  · simp only [map_add, map_smul, AddSubgroup.coe_add, selfAdjoint.val_smul, hjba, hprop, ZeroMemClass.coe_zero]
    module
  · apply Subtype.ext
    have hrhs : (q ((-2 : ℝ) •
        (O.J a (O.D b a - O.J b (μ • b)) +
          O.J (μ • b) (O.J b a + O.D b (μ • b)))) : Matrix n n ℂ) =
        (2 * μ) • (q (O.D a b) : Matrix n n ℂ) := by
      rw [q.map_smul (-2) _, q.map_add (O.J a _) _]
      change (-2 : ℝ) • ((q (O.J a _) : Matrix n n ℂ) + (q (O.J (μ • b) _) : Matrix n n ℂ)) = _
      rw [hJ a _, hJ (μ • b) _, ha, hν, hω]
      simp only [q.map_smul μ b, selfAdjoint.val_smul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, one_mul, mul_one, pow_two]
      module
    rw [q.map_sub _ _, hm] at he
    change (q (O.D _ _) : Matrix n n ℂ) - 0 = _ at he
    rw [sub_zero, hrhs] at he
    exact he

#print axioms scalar_second_jordan_zero
#print axioms semidefinite_second_image
end Matrix

end D5.S3.Quantum.Algebra.PBFiniteScalarAbsorption
