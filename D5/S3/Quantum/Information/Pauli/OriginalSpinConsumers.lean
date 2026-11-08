/- GID: D5/S3/Quantum/Information/Pauli/OriginalSpinConsumers
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/Pauli/OriginalSpinConsumers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.CrossProduct, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Both Pauli orientations preserve original spin evaluations and all finite directed Gram tables. -/

import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import D5.S3.Quantum.Algebra.PauliFixedProductFamily
import D5.S3.Quantum.Measurement.FourQubitParentConstruction
import D5.S3.Quantum.SpinFactor.OriginalDContract

/-! Both matrix orientations on the original spin carrier, cone and norm. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix WithLp
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers

abbrev Vec := _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.Vec
abbrev E := _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.E
abbrev vnorm : Vec → ℝ :=
  _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.vnorm
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Relation := E → E → E

private def euclideanVec (v : Vec) : EuclideanSpace ℝ (Fin 3) := toLp 2 v

private theorem dot_euclidean (x y : Vec) :
    inner ℝ (euclideanVec x) (euclideanVec y) =
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot x y := by
  simp [euclideanVec,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot,
    PiLp.inner_apply, dotProduct, Fin.sum_univ_three, RCLike.inner_apply]
  ring

private theorem euclideanVec_norm (v : Vec) : ‖euclideanVec v‖ = vnorm v := by
  rw [norm_eq_sqrt_real_inner, dot_euclidean]
  rfl

/-- The original scalar/vector coordinates, with their original unit. -/
abbrev unit : E := _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.unit

/-- Coordinate transport to the existing spin-product supplier; it changes no norm on `E`. -/
def toFamily : E →ₗ[ℝ] _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.J where
  toFun a := toLp 2 ![a.1, a.2 0, a.2 1, a.2 2]
  map_add' a b := by ext i; fin_cases i <;> rfl
  map_smul' r a := by ext i; fin_cases i <;> rfl

def ofFamily : _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.J →ₗ[ℝ] E where
  toFun a := (a 0, fun i => a (i.succ))
  map_add' a b := by
    apply Prod.ext
    · rfl
    · ext i; fin_cases i <;> rfl
  map_smul' r a := by
    apply Prod.ext
    · rfl
    · ext i; fin_cases i <;> rfl

/-- The supplied Jordan multiplication, transported to real scalar plus real Euclidean three-space. -/
def jordan (a b : E) : E := _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.jordan a b

/-- The supplied cross channel as a real bilinear map on the original carrier. -/
def cross : E →ₗ[ℝ] E →ₗ[ℝ] E where
  toFun a := ofFamily.comp ((_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.C (toFamily a)).comp toFamily)
  map_add' a b := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' r a := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- `false` is the usual matrix product, `true` its opposite. -/
def sign (opposite : Bool) : ℝ := if opposite then 1 else -1

def fixed (opposite : Bool) : E →ₗ[ℝ] E →ₗ[ℝ] E := sign opposite • cross

/-- The original spin order-unit norm, rather than the Euclidean norm on four coordinates. -/
abbrev originalNorm : E → ℝ :=
  _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.originalNorm

abbrev cone : E → Prop :=
  _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cone

/-- The full unnormalized positive evaluation family. -/
def evaluate (m : ℝ) (v : Vec) (a : E) : ℝ :=
  m * a.1 + _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot v a.2

/-- Positivity is tested on the original spin cone. -/
def PositiveEvaluation (α : E →ₗ[ℝ] ℝ) : Prop := ∀ a, cone a → 0 ≤ α a

def evaluationLinear (m : ℝ) (v : Vec) : E →ₗ[ℝ] ℝ where
  toFun := evaluate m v
  map_add' a b := by simp [evaluate,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot, dotProduct, Fin.sum_univ_three]; ring
  map_smul' r a := by simp [evaluate,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot, dotProduct, Fin.sum_univ_three]; ring

def phi (a : E) : Mat :=
  _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB a.1
    (euclideanVec a.2)
def density (m : ℝ) (v : Vec) : Mat :=
  (1 / 2 : ℂ) • _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB m
    (euclideanVec v)

/-- Multiplication order is fixed once for the whole carrier. -/
def product (opposite : Bool) (A B : Mat) : Mat := if opposite then B * A else A * B

/-- Every entry, including each diagonal, uses the actual directed relation. -/
def gram {ι : Type*} (D : Relation) (m : ℝ) (v : Vec) (a : ι → E) : Matrix ι ι ℂ :=
  fun i j => (evaluate m v (jordan (a i) (a j)) : ℂ) -
    Complex.I * (evaluate m v (D (a i) (a j)) : ℂ)

abbrev P2 : (Relation → Prop) :=
  _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.P2

abbrev PB : (Relation → Prop) :=
  _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.PB

def OriginalContinuous (D : Relation) : Prop :=
  ∀ a b : E, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ a' b' : E, originalNorm (a' - a) < δ → originalNorm (b' - b) < δ →
      originalNorm (D a' b' - D a b) < η

private theorem jordan_coordinates (a b : E) :
    jordan a b =
      (a.1 * b.1 + _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot a.2 b.2,
        a.1 • b.2 + b.1 • a.2) := by
  rfl

private theorem jordan_supplier (a b : E) :
    jordan a b =
      ofFamily (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S
        (toFamily a) (toFamily b)) := by
  apply Prod.ext
  · simp [jordan, ofFamily, toFamily,
      _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S,
      _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.spin,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.jordan,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot,
      PiLp.inner_apply, dotProduct, Fin.sum_univ_three, RCLike.inner_apply]
    ring
  · ext i
    fin_cases i <;> simp [jordan, ofFamily, toFamily,
      _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S,
      _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.spin,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.jordan]

private theorem cross_coordinates (a b : E) :
    cross a b =
      (0, _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross a.2 b.2) := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp [cross, ofFamily, toFamily,
      _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.C,
      _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.cross,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross, cross_apply]

private theorem fixed_coordinates (opposite : Bool) (a b : E) :
    fixed opposite a b =
      (0, sign opposite •
        _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross a.2 b.2) := by
  simp [fixed, cross_coordinates]

private theorem fixed_crossD (opposite : Bool) (a b : E) :
    fixed opposite a b =
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.crossD
        (if opposite then .plus else .minus) a b := by
  cases opposite <;> simp [fixed_coordinates, sign,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.crossD]

private theorem phi_hermitian (a : E) : (phi a).IsHermitian :=
  _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_hermitian
    a.1 (euclideanVec a.2)

private theorem phi_star (a : E) : (phi a)ᴴ = phi a := (phi_hermitian a).eq

private theorem phi_product (opposite : Bool) (a b : E) :
    product opposite (phi a) (phi b) =
      phi (jordan a b) - Complex.I • phi (fixed opposite a b) := by
  cases opposite <;> ext i j <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [product, phi, euclideanVec, jordan_coordinates, fixed_coordinates, sign,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross, dotProduct,
      _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula, Matrix.mul_apply, Fin.sum_univ_two,
      PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      cross_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem density_positive (m : ℝ) (v : Vec) :
    (density m v).PosSemidef ↔ vnorm v ≤ m := by
  rw [density, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.half_scalarB_posSemidef_iff,
    euclideanVec_norm]

private theorem density_mass (m : ℝ) (v : Vec) : (density m v).trace = (m : ℂ) := by
  simp [density, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula, Matrix.trace, Fin.sum_univ_two]
  ring

private theorem evaluation_positive (m : ℝ) (v : Vec) :
    PositiveEvaluation (evaluationLinear m v) ↔ vnorm v ≤ m := by
  have hnorm (x : Vec) : 0 ≤ vnorm x := Real.sqrt_nonneg _
  have hneg : vnorm (-v) = vnorm v := by
    simp [vnorm, _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.vnorm,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot]
  constructor
  · intro h
    have hm : 0 ≤ m := by
      have hh := h (1, 0) (by
        simp [cone, _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cone,
          _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.vnorm,
          _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot])
      simpa [evaluationLinear, evaluate,
        _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot] using hh
    have hv := h (vnorm v, -v) (by
      change vnorm (-v) ≤ vnorm v
      rw [hneg])
    have hsq : vnorm v ^ 2 =
        _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot v v := by
      rw [← euclideanVec_norm, ← dot_euclidean]
      exact (real_inner_self_eq_norm_sq _).symm
    change 0 ≤ m * vnorm v +
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot v (-v) at hv
    have hd : _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot v (-v) =
        -(vnorm v ^ 2) := by
      rw [_root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot, dotProduct_neg]
      exact congrArg Neg.neg hsq.symm
    rw [hd] at hv
    by_cases hz : vnorm v = 0
    · simpa [hz] using hm
    · have hn : 0 < vnorm v := lt_of_le_of_ne (hnorm v) (Ne.symm hz)
      nlinarith
  · intro hm a ha
    have hm0 : 0 ≤ m := (hnorm v).trans hm
    have hin := real_inner_le_norm (euclideanVec (-v)) (euclideanVec a.2)
    rw [dot_euclidean, euclideanVec_norm, euclideanVec_norm, hneg] at hin
    simp only [_root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot,
      neg_dotProduct] at hin
    have hmul := mul_le_mul hm ha (hnorm a.2) hm0
    change 0 ≤ m * a.1 + v ⬝ᵥ a.2
    change vnorm v * vnorm a.2 ≤ m * a.1 at hmul
    linarith

private theorem evaluation_representation (α : E →ₗ[ℝ] ℝ) :
    ∃ m : ℝ, ∃ v : Vec, ∀ a : E, α a = evaluate m v a := by
  let e : Fin 3 → E := fun i =>
    (0, fun j => if i = j then 1 else 0)
  let m : ℝ := α unit
  let v : Vec := ![α (e 0), α (e 1), α (e 2)]
  refine ⟨m, v, ?_⟩
  intro a
  have he : a = a.1 • unit + ∑ i : Fin 3, a.2 i • e i := by
    apply Prod.ext
    · simp [unit, _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.unit,
        e, Fin.sum_univ_three]
    · ext i
      fin_cases i <;> simp [unit, _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.unit,
        e, Fin.sum_univ_three]
  calc
    α a = α (a.1 • unit + ∑ i : Fin 3, a.2 i • e i) := congrArg α he
    _ = evaluate m v a := by
      simp [map_add, map_sum, map_smul, evaluate, m, v,
        _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot,
        dotProduct, Fin.sum_univ_three]
      ring

private theorem positive_evaluation_complete (α : E →ₗ[ℝ] ℝ)
    (hα : PositiveEvaluation α) :
    ∃ m : ℝ, ∃ v : Vec, vnorm v ≤ m ∧ ∀ a : E, α a = evaluate m v a := by
  obtain ⟨m, v, he⟩ := evaluation_representation α
  refine ⟨m, v, (evaluation_positive m v).mp ?_, he⟩
  intro a ha
  change 0 ≤ evaluate m v a
  rw [← he]
  exact hα a ha

private theorem trace_evaluate (m : ℝ) (v : Vec) (a : E) :
    (density m v * phi a).trace = (evaluate m v a : ℂ) := by
  apply Complex.ext <;>
    simp [density, phi, euclideanVec, evaluate,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot,
      _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
      _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, PiLp.inner_apply,
      dotProduct, Fin.sum_univ_three, RCLike.inner_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem original_order_interval (a : E) (r : ℝ) :
    (((r : ℂ) • (1 : Mat) - phi a).PosSemidef ∧
      ((r : ℂ) • (1 : Mat) + phi a).PosSemidef) ↔ originalNorm a ≤ r := by
  have hm : (r : ℂ) • (1 : Mat) - phi a =
      _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB
        (r - a.1) (euclideanVec (-a.2)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phi, euclideanVec,
        _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
        _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula] <;> ring
  have hp : (r : ℂ) • (1 : Mat) + phi a =
      _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB
        (r + a.1) (euclideanVec a.2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phi, euclideanVec,
        _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
        _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula] <;> ring
  rw [hm, hp,
    _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_posSemidef_iff,
    _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_posSemidef_iff,
    show euclideanVec (-a.2) = -euclideanVec a.2 from rfl,
    norm_neg, euclideanVec_norm]
  constructor
  · rintro ⟨hm, hp⟩
    have h : |a.1| ≤ r - vnorm a.2 := abs_le.mpr ⟨by linarith, by linarith⟩
    dsimp [originalNorm, _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.originalNorm]
    linarith
  · intro h
    dsimp [originalNorm, _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.originalNorm] at h
    exact ⟨by linarith [le_abs_self a.1], by linarith [neg_le_abs a.1]⟩

private theorem density_surjective (ρ : Mat) (hρ : ρ.PosSemidef) :
    ∃ m : ℝ, ∃ v : Vec, vnorm v ≤ m ∧ ρ = density m v := by
  let m : ℝ := ρ.trace.re
  let v : Vec := fun i =>
    (_root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch ρ) i
  have he : ρ = density m v := by
    calc
      ρ = _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB
          (ρ.trace.re / 2) ((1 / 2 : ℝ) • euclideanVec v) :=
        _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.hermitian_decomposition
          ρ hρ.isHermitian
      _ = density m v := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [m, density,
            _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
            _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula] <;> ring
  refine ⟨m, v, (density_positive m v).mp ?_, he⟩
  exact he ▸ hρ

private theorem phi_positive (a : E) : (phi a).PosSemidef ↔ cone a := by
  rw [phi,
    _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_posSemidef_iff,
    euclideanVec_norm]
  rfl

private theorem gram_trace (opposite : Bool) (m : ℝ) (v : Vec) (a b : E) :
    (evaluate m v (jordan a b) : ℂ) -
        Complex.I * (evaluate m v (fixed opposite a b) : ℂ) =
      (density m v * product opposite (phi a) (phi b)).trace := by
  rw [phi_product]
  simp [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    trace_evaluate]

private theorem gram_transpose {ι : Type*} (m : ℝ) (v : Vec) (a : ι → E) :
    gram (fun a b => fixed true a b) m v a = (gram (fun a b => fixed false a b) m v a)ᵀ := by
  ext i j
  change _ = gram (fun a b => fixed false a b) m v a j i
  simp only [gram, gram_trace, product, Bool.false_eq_true, ↓reduceIte]

/-- The usual-order quadratic form is the trace of one positive conjugation of the density. -/
private theorem gram_quadratic_trace {ι : Type*} [Fintype ι]
    (m : ℝ) (v : Vec) (a : ι → E) (c : ι → ℂ) :
    star c ⬝ᵥ (gram (fun a b => fixed false a b) m v a *ᵥ c) =
      (density m v *
        ((∑ i, c i • phi (a i))ᴴ * (∑ j, c j • phi (a j)))).trace := by
  classical
  simp only [gram, gram_trace, product, Bool.false_eq_true, ↓reduceIte,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_smul,
    phi_star]
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem gram_usual_hermitian {ι : Type*} (m : ℝ) (v : Vec) (a : ι → E) :
    (gram (fun a b => fixed false a b) m v a).IsHermitian := by
  ext i j
  apply Complex.ext <;>
    simp [gram, evaluate, euclideanVec, jordan_coordinates, fixed_coordinates, sign,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross, dotProduct,
      PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      cross_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem fixed_gram_positive {ι : Type*} [Fintype ι]
    (opposite : Bool) (m : ℝ) (v : Vec) (hm : vnorm v ≤ m) (a : ι → E) :
    (gram (fun a b => fixed opposite a b) m v a).PosSemidef := by
  classical
  have usual : (gram (fun a b => fixed false a b) m v a).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gram_usual_hermitian m v a)
    intro c
    rw [gram_quadratic_trace]
    let Z : Mat := ∑ i, c i • phi (a i)
    have h := ((density_positive m v).mpr hm).mul_mul_conjTranspose_same Z
    have ht := h.trace_nonneg
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm Z] at ht
    simpa only [Z, Matrix.mul_assoc] using ht
  cases opposite
  · exact usual
  · rw [gram_transpose]
    exact usual.transpose

private theorem fixed_contract_p2 (opposite : Bool) :
    P2 (fun a b => fixed opposite a b) := by
  intro α a b
  let labels : Fin 2 → E := ![a, b]
  have h := fixed_gram_positive opposite α.mass α.vector α.positive labels
  have he : _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.gram2
      (fun a b => fixed opposite a b) α a b =
        gram (fun a b => fixed opposite a b) α.mass α.vector labels := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [he]
  exact h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem fixed_phase_balance (opposite : Bool) : PB (fun a b => fixed opposite a b) := by
  intro α a b c
  cases opposite <;>
    simp [PB,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.squareReadout,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.phaseR,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.phaseS,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.evaluate,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.jordan,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot,
      fixed_coordinates, sign,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross,
      dotProduct, Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail,
      Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul] <;> ring

private theorem fixed_R (opposite : Bool) (a b c : E) :
    jordan (jordan a b) c - jordan a (jordan b c) =
      fixed opposite (fixed opposite a b) c - fixed opposite a (fixed opposite b c) := by
  let a₀ := toFamily a
  let b₀ := toFamily b
  let c₀ := toFamily c
  have h₁ := _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.spin_commutator a₀ b₀ c₀
  have h₂ := _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.spin_commutator b₀ c₀ a₀
  rw [_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.s_comm c₀ a₀,
    _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.s_comm b₀ a₀,
    _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.s_comm c₀
      (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S a₀ b₀),
    _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.c_anti
      (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.C b₀ c₀) a₀] at h₂
  simp only [neg_neg] at h₂
  have hsum :
      _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S
          (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S a₀ b₀) c₀ -
        _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S a₀
          (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S b₀ c₀) =
      _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.C
          (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.C a₀ b₀) c₀ -
        _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.C a₀
          (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.C b₀ c₀) := by
    calc
      _ = -(_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S a₀
            (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S b₀ c₀) -
          _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S b₀
            (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S a₀ c₀)) -
        (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S b₀
            (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S a₀ c₀) -
          _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S
            (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S a₀ b₀) c₀) := by abel
      _ = _ := by rw [h₁, h₂]; abel
  have hround (x : _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.J) :
      toFamily (ofFamily x) = x := by
    ext i
    fin_cases i <;> rfl
  have hs := congrArg ofFamily hsum
  simp only [map_sub] at hs
  cases opposite <;>
    simpa [jordan_supplier, hround, a₀, b₀, c₀, fixed, sign, cross,
      LinearMap.comp_apply] using hs

private theorem originalNorm_nonneg (a : E) : 0 ≤ originalNorm a :=
  add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

private theorem originalNorm_add (a b : E) :
    originalNorm (a + b) ≤ originalNorm a + originalNorm b := by
  have hvec : vnorm (a.2 + b.2) ≤ vnorm a.2 + vnorm b.2 := by
    rw [← euclideanVec_norm, ← euclideanVec_norm, ← euclideanVec_norm]
    simpa [euclideanVec] using (norm_add_le (euclideanVec a.2) (euclideanVec b.2))
  change |a.1 + b.1| + vnorm (a.2 + b.2) ≤
    (|a.1| + vnorm a.2) + (|b.1| + vnorm b.2)
  linarith [abs_add_le a.1 b.1, hvec]

private theorem cross_norm (x y : Vec) :
    vnorm (_root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross x y) ≤
      vnorm x * vnorm y := by
  rw [← euclideanVec_norm, ← euclideanVec_norm, ← euclideanVec_norm]
  change ‖toLp 2 (x ⨯₃ y)‖ ≤ ‖toLp 2 x‖ * ‖toLp 2 y‖
  rw [InnerProductGeometry.norm_toLp_symm_crossProduct]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (Real.sin_le_one _)

private theorem fixed_bound (opposite : Bool) (a b : E) :
    originalNorm (fixed opposite a b) ≤ originalNorm a * originalNorm b := by
  have h := cross_norm a.2 b.2
  have ha : vnorm a.2 ≤ originalNorm a := le_add_of_nonneg_left (abs_nonneg _)
  have hb : vnorm b.2 ≤ originalNorm b := le_add_of_nonneg_left (abs_nonneg _)
  have hmul := mul_le_mul ha hb (Real.sqrt_nonneg _) (originalNorm_nonneg _)
  cases opposite <;> simpa [originalNorm,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.originalNorm,
    fixed_coordinates, sign, vnorm,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.vnorm,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot] using h.trans hmul

private theorem fixed_difference_bound (opposite : Bool) (a b a' b' : E) :
    originalNorm (fixed opposite a b - fixed opposite a' b') ≤
      originalNorm (a - a') * originalNorm b +
        originalNorm a' * originalNorm (b - b') := by
  have he : fixed opposite a b - fixed opposite a' b' =
      fixed opposite (a - a') b + fixed opposite a' (b - b') := by
    simp [map_sub, LinearMap.sub_apply]
  rw [he]
  exact (originalNorm_add _ _).trans
    (add_le_add (fixed_bound opposite _ _) (fixed_bound opposite _ _))

private theorem fixed_continuous (opposite : Bool) : OriginalContinuous (fun a b => fixed opposite a b) := by
  intro a b η hη
  let K : ℝ := originalNorm a + originalNorm b + 1
  have hK : 0 < K := by
    dsimp [K]
    linarith [originalNorm_nonneg a, originalNorm_nonneg b]
  let δ : ℝ := min 1 (η / K)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hη hK)
  refine ⟨δ, hδ, ?_⟩
  intro a' b' ha hb
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδη : δ * K ≤ η := (le_div_iff₀ hK).mp (min_le_right _ _)
  have hb' : originalNorm b' < originalNorm b + δ := by
    have he : b' = (b' - b) + b := by abel
    calc
      originalNorm b' = originalNorm ((b' - b) + b) := congrArg originalNorm he
      _ ≤ originalNorm (b' - b) + originalNorm b := originalNorm_add _ _
      _ < originalNorm b + δ := by linarith
  have hmain := fixed_difference_bound opposite a' b' a b
  have hna := originalNorm_nonneg a
  have hnb' := originalNorm_nonneg b'
  have hfirst : originalNorm (a' - a) * originalNorm b' ≤ δ * originalNorm b' :=
    mul_le_mul_of_nonneg_right ha.le hnb'
  have hsecond : originalNorm a * originalNorm (b' - b) ≤ originalNorm a * δ :=
    mul_le_mul_of_nonneg_left hb.le hna
  have hstrict : δ * originalNorm b' < δ * (originalNorm b + 1) :=
    mul_lt_mul_of_pos_left (lt_of_lt_of_le hb' (add_le_add_right hδ1 _)) hδ
  calc
    originalNorm (fixed opposite a' b' - fixed opposite a b) ≤
        δ * originalNorm b' + originalNorm a * δ := hmain.trans (add_le_add hfirst hsecond)
    _ < δ * K := by dsimp [K]; nlinarith
    _ ≤ η := hδη

/-- All conclusions refer to the same total relation on the original spin carrier. -/
structure Consequences (D : Relation) : Prop where
  p2 : P2 D
  pb : PB D
  unit_left : ∀ (r : ℝ) (b : E), D (r • unit) b = 0
  unit_right : ∀ (r : ℝ) (a : E), D a (r • unit) = 0
  translation : ∀ (r q : ℝ) (a b : E), D (a + r • unit) (b + q • unit) = D a b
  add_left : ∀ a b c, D (a + b) c = D a c + D b c
  add_right : ∀ a b c, D a (b + c) = D a b + D a c
  smul_left : ∀ (r : ℝ) (a b : E), D (r • a) b = r • D a b
  smul_right : ∀ (r : ℝ) (a b : E), D a (r • b) = r • D a b
  bound : ∀ a b, originalNorm (D a b) ≤ originalNorm a * originalNorm b
  difference_bound : ∀ a b a' b', originalNorm (D a b - D a' b') ≤
    originalNorm (a - a') * originalNorm b + originalNorm a' * originalNorm (b - b')
  continuous : OriginalContinuous D
  finite_gram : ∀ (n : ℕ) (m : ℝ) (v : Vec), vnorm v ≤ m →
    ∀ a : Fin n → E, (gram D m v a).PosSemidef
  reassociation : ∀ a b c, jordan (jordan a b) c - jordan a (jordan b c) =
    D (D a b) c - D a (D b c)

/-- The same cone, norm and all-mass evaluations in the Pauli realization. -/
def MatrixInterfaces (opposite : Bool) (D : Relation) : Prop :=
      (∀ m v, (density m v).PosSemidef ↔ vnorm v ≤ m) ∧
      (∀ m v, (density m v).trace = (m : ℂ)) ∧
      (∀ m v, PositiveEvaluation (evaluationLinear m v) ↔ vnorm v ≤ m) ∧
      (∀ α : E →ₗ[ℝ] ℝ, PositiveEvaluation α →
        ∃ m : ℝ, ∃ v : Vec, vnorm v ≤ m ∧ ∀ a, α a = evaluate m v a) ∧
      (∀ m v a, (density m v * phi a).trace = (evaluate m v a : ℂ)) ∧
      (∀ a, (phi a).PosSemidef ↔ cone a) ∧
      (∀ (a : E) (r : ℝ), (((r : ℂ) • (1 : Mat) - phi a).PosSemidef ∧
        ((r : ℂ) • (1 : Mat) + phi a).PosSemidef) ↔ originalNorm a ≤ r) ∧
      (∀ ρ : Mat, ρ.PosSemidef → ∃ m : ℝ, ∃ v : Vec, vnorm v ≤ m ∧ ρ = density m v) ∧
      (∀ a b, product opposite (phi a) (phi b) =
        phi (jordan a b) - Complex.I • phi (D a b))

/-- A single global cross orientation supplies both original relations and all original consumers.
The sign is fixed before any input, evaluation, finite label family or complex coefficient. -/
theorem same_D_consequences (opposite : Bool) (D : Relation)
    (hD : ∀ a b,
      D a b =
        _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.crossD
          (if opposite then .plus else .minus) a b) :
    Consequences D ∧ MatrixInterfaces opposite D := by
  have hfixed : ∀ a b, D a b = fixed opposite a b := by
    intro a b
    exact (hD a b).trans (fixed_crossD opposite a b).symm
  have he : D = fun a b => fixed opposite a b :=
    funext fun a => funext (hfixed a)
  subst D
  refine ⟨?_, density_positive, density_mass, evaluation_positive,
    positive_evaluation_complete, trace_evaluate,
    phi_positive,
    original_order_interval, density_surjective, phi_product opposite⟩
  refine {
    p2 := fixed_contract_p2 opposite
    pb := fixed_phase_balance opposite
    unit_left := ?_
    unit_right := ?_
    translation := ?_
    add_left := ?_
    add_right := ?_
    smul_left := ?_
    smul_right := ?_
    bound := fixed_bound opposite
    difference_bound := fixed_difference_bound opposite
    continuous := fixed_continuous opposite
    finite_gram := fun n m v hm a => fixed_gram_positive opposite m v hm a
    reassociation := fixed_R opposite }
  · intro r b
    simp [fixed_coordinates, unit,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.unit,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross]
  · intro r a
    simp [fixed_coordinates, unit,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.unit,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross]
  · intro r q a b
    simp [fixed_coordinates, unit,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.unit,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross]
  · intro a b c
    exact LinearMap.congr_fun ((fixed opposite).map_add a b) c
  · intro a b c
    exact (fixed opposite a).map_add b c
  · intro r a b
    exact LinearMap.congr_fun ((fixed opposite).map_smul r a) b
  · intro r a b
    exact (fixed opposite a).map_smul r b

end D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
