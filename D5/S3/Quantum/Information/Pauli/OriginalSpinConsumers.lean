/- GID: D5/S3/Quantum/Information/Pauli/OriginalSpinConsumers
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/Pauli/OriginalSpinConsumers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.CrossProduct, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Both Pauli orientations preserve original spin evaluations and all finite directed Gram tables. -/

import D5.S3.Quantum.Algebra.PauliFixedProductFamily
import D5.S3.Quantum.Measurement.FourQubitParentConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix WithLp
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers

abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev E := ℝ × Vec
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Relation := E → E → E

/-- The original scalar/vector coordinates, with their original unit. -/
def unit : E := (1, 0)

/-- Coordinate transport to the existing spin-product supplier; it changes no norm on `E`. -/
def toFamily : E →ₗ[ℝ] _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.J where
  toFun a := toLp 2 ![a.1, a.2 0, a.2 1, a.2 2]
  map_add' a b := by ext i; fin_cases i <;> rfl
  map_smul' r a := by ext i; fin_cases i <;> rfl

def ofFamily : _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.J →ₗ[ℝ] E where
  toFun a := (a 0, toLp 2 ![a 1, a 2, a 3])
  map_add' a b := by
    apply Prod.ext
    · rfl
    · ext i; fin_cases i <;> rfl
  map_smul' r a := by
    apply Prod.ext
    · rfl
    · ext i; fin_cases i <;> rfl

/-- The supplied Jordan multiplication, transported to real scalar plus real Euclidean three-space. -/
def jordan (a b : E) : E := ofFamily (_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S (toFamily a) (toFamily b))

/-- The supplied cross channel as a real bilinear map on the original carrier. -/
def cross : E →ₗ[ℝ] E →ₗ[ℝ] E where
  toFun a := ofFamily.comp ((_root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.C (toFamily a)).comp toFamily)
  map_add' a b := by ext c; simp [map_add]
  map_smul' r a := by ext c; simp [map_smul]

/-- `false` is the usual matrix product, `true` its opposite. -/
def sign (opposite : Bool) : ℝ := if opposite then 1 else -1

def fixed (opposite : Bool) : E →ₗ[ℝ] E →ₗ[ℝ] E := sign opposite • cross

/-- The original spin order-unit norm, rather than the Euclidean norm on four coordinates. -/
def originalNorm (a : E) : ℝ := |a.1| + ‖a.2‖

def cone (a : E) : Prop := ‖a.2‖ ≤ a.1

/-- The full unnormalized positive evaluation family. -/
def evaluate (m : ℝ) (v : Vec) (a : E) : ℝ := m * a.1 + inner ℝ v a.2

/-- Positivity is tested on the original spin cone. -/
def PositiveEvaluation (α : E →ₗ[ℝ] ℝ) : Prop := ∀ a, cone a → 0 ≤ α a

def evaluationLinear (m : ℝ) (v : Vec) : E →ₗ[ℝ] ℝ where
  toFun := evaluate m v
  map_add' a b := by simp [evaluate, inner_add_right]; ring
  map_smul' r a := by simp [evaluate, inner_smul_right]; ring

def phi (a : E) : Mat := _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB a.1 a.2
def density (m : ℝ) (v : Vec) : Mat := (1 / 2 : ℂ) • _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB m v

/-- Multiplication order is fixed once for the whole carrier. -/
def product (opposite : Bool) (A B : Mat) : Mat := if opposite then B * A else A * B

/-- Every entry, including each diagonal, uses the actual directed relation. -/
def gram {ι : Type*} (D : Relation) (m : ℝ) (v : Vec) (a : ι → E) : Matrix ι ι ℂ :=
  fun i j => (evaluate m v (jordan (a i) (a j)) : ℂ) -
    Complex.I * (evaluate m v (D (a i) (a j)) : ℂ)

def P2 (D : Relation) : Prop :=
  ∀ (m : ℝ) (v : Vec), ‖v‖ ≤ m → ∀ a : Fin 2 → E, (gram D m v a).PosSemidef

def squareReadout (D : Relation) (m : ℝ) (v : Vec) (b c : E) : ℝ :=
  evaluate m v (jordan b b + jordan c c + 2 • D b c)

def phaseLeft (D : Relation) (a b c : E) (t : ℝ) : E :=
  b + t • D a b - t • jordan a c

def phaseRight (D : Relation) (a b c : E) (t : ℝ) : E :=
  c + t • jordan a b + t • D a c

def PB (D : Relation) : Prop :=
  ∀ (m : ℝ) (v : Vec), ‖v‖ ≤ m → ∀ a b c : E,
    squareReadout D m v (phaseLeft D a b c 1) (phaseRight D a b c 1) =
    squareReadout D m v (phaseLeft D a b c (-1)) (phaseRight D a b c (-1))

def OriginalContinuous (D : Relation) : Prop :=
  ∀ a b : E, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ a' b' : E, originalNorm (a' - a) < δ → originalNorm (b' - b) < δ →
      originalNorm (D a' b' - D a b) < η

private theorem jordan_coordinates (a b : E) :
    jordan a b = (a.1 * b.1 + inner ℝ a.2 b.2, a.1 • b.2 + b.1 • a.2) := by
  apply Prod.ext
  · simp [jordan, ofFamily, toFamily, _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S, _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.spin, PiLp.inner_apply,
      Fin.sum_univ_three, RCLike.inner_apply]
    ring
  · ext i
    fin_cases i <;> simp [jordan, ofFamily, toFamily, _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.S, _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.spin]

private theorem cross_coordinates (a b : E) :
    cross a b = (0, toLp 2 (crossProduct a.2 b.2)) := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp [cross, ofFamily, toFamily, _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.C, _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily.cross, cross_apply]

private theorem fixed_coordinates (opposite : Bool) (a b : E) :
    fixed opposite a b = (0, sign opposite • toLp 2 (crossProduct a.2 b.2)) := by
  simp [fixed, cross_coordinates]

private theorem phi_hermitian (a : E) : (phi a).IsHermitian :=
  _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_hermitian a.1 a.2

private theorem phi_star (a : E) : (phi a)ᴴ = phi a := (phi_hermitian a).eq

private theorem phi_product (opposite : Bool) (a b : E) :
    product opposite (phi a) (phi b) =
      phi (jordan a b) - Complex.I • phi (fixed opposite a b) := by
  cases opposite <;> ext i j <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [product, phi, jordan_coordinates, fixed_coordinates, sign,
      _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula, Matrix.mul_apply, Fin.sum_univ_two,
      PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      cross_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem density_positive (m : ℝ) (v : Vec) :
    (density m v).PosSemidef ↔ ‖v‖ ≤ m :=
  _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.half_scalarB_posSemidef_iff m v

private theorem density_mass (m : ℝ) (v : Vec) : (density m v).trace = (m : ℂ) := by
  simp [density, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula, Matrix.trace, Fin.sum_univ_two]
  ring

private theorem evaluation_positive (m : ℝ) (v : Vec) :
    PositiveEvaluation (evaluationLinear m v) ↔ ‖v‖ ≤ m := by
  constructor
  · intro h
    have hm : 0 ≤ m := by
      simpa [evaluationLinear, evaluate, unit] using h unit (by simp [cone, unit])
    have hv := h (‖v‖, -v) (by simp [cone])
    have hv' : 0 ≤ m * ‖v‖ - ‖v‖ ^ 2 := by
      simpa [evaluationLinear, evaluate, inner_neg_right, real_inner_self_eq_norm_sq,
        sub_eq_add_neg] using hv
    by_cases hz : ‖v‖ = 0
    · simpa [hz] using hm
    · have hn : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  · intro hm a ha
    have hm0 : 0 ≤ m := (norm_nonneg _).trans hm
    have hin := real_inner_le_norm (-v) a.2
    rw [inner_neg_left, norm_neg] at hin
    have hmul := mul_le_mul hm ha (norm_nonneg a.2) hm0
    change 0 ≤ m * a.1 + inner ℝ v a.2
    linarith

private theorem evaluation_representation (α : E →ₗ[ℝ] ℝ) :
    ∃ m : ℝ, ∃ v : Vec, ∀ a : E, α a = evaluate m v a := by
  let e : Fin 3 → E := fun i => (0, EuclideanSpace.single i 1)
  let m : ℝ := α unit
  let v : Vec := toLp 2 ![α (e 0), α (e 1), α (e 2)]
  refine ⟨m, v, ?_⟩
  intro a
  have he : a = a.1 • unit + ∑ i : Fin 3, a.2 i • e i := by
    apply Prod.ext
    · simp [unit, e, Fin.sum_univ_three]
    · ext i
      fin_cases i <;> simp [unit, e, Fin.sum_univ_three, PiLp.single_apply]
  calc
    α a = α (a.1 • unit + ∑ i : Fin 3, a.2 i • e i) := congrArg α he
    _ = evaluate m v a := by
      simp [map_add, map_sum, map_smul, evaluate, m, v, PiLp.inner_apply,
        Fin.sum_univ_three, RCLike.inner_apply]
      ring

private theorem positive_evaluation_complete (α : E →ₗ[ℝ] ℝ)
    (hα : PositiveEvaluation α) :
    ∃ m : ℝ, ∃ v : Vec, ‖v‖ ≤ m ∧ ∀ a : E, α a = evaluate m v a := by
  obtain ⟨m, v, he⟩ := evaluation_representation α
  refine ⟨m, v, (evaluation_positive m v).mp ?_, he⟩
  intro a ha
  change 0 ≤ evaluate m v a
  rw [← he]
  exact hα a ha

private theorem trace_evaluate (m : ℝ) (v : Vec) (a : E) :
    (density m v * phi a).trace = (evaluate m v a : ℂ) := by
  apply Complex.ext <;>
    simp [density, phi, evaluate, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, PiLp.inner_apply,
      Fin.sum_univ_three, RCLike.inner_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem original_order_interval (a : E) (r : ℝ) :
    (((r : ℂ) • (1 : Mat) - phi a).PosSemidef ∧
      ((r : ℂ) • (1 : Mat) + phi a).PosSemidef) ↔ originalNorm a ≤ r := by
  have hm : (r : ℂ) • (1 : Mat) - phi a =
      _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB (r - a.1) (-a.2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phi, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
        _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula] <;> ring
  have hp : (r : ℂ) • (1 : Mat) + phi a =
      _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB (r + a.1) a.2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phi, _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
        _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula] <;> ring
  rw [hm, hp,
    _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_posSemidef_iff,
    _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_posSemidef_iff, norm_neg]
  constructor
  · rintro ⟨hm, hp⟩
    have h : |a.1| ≤ r - ‖a.2‖ := abs_le.mpr ⟨by linarith, by linarith⟩
    dsimp [originalNorm]
    linarith
  · intro h
    dsimp [originalNorm] at h
    exact ⟨by linarith [le_abs_self a.1], by linarith [neg_le_abs a.1]⟩

private theorem density_surjective (ρ : Mat) (hρ : ρ.PosSemidef) :
    ∃ m : ℝ, ∃ v : Vec, ‖v‖ ≤ m ∧ ρ = density m v := by
  let m : ℝ := ρ.trace.re
  let v : Vec := _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch ρ
  have he : ρ = density m v := by
    calc
      ρ = _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB
          (ρ.trace.re / 2) ((1 / 2 : ℝ) • v) :=
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

private theorem gram_trace (opposite : Bool) (m : ℝ) (v : Vec) (a b : E) :
    (evaluate m v (jordan a b) : ℂ) -
        Complex.I * (evaluate m v (fixed opposite a b) : ℂ) =
      (density m v * product opposite (phi a) (phi b)).trace := by
  rw [phi_product]
  simp [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    trace_evaluate]

private theorem gram_transpose {ι : Type*} (m : ℝ) (v : Vec) (a : ι → E) :
    gram (fixed true) m v a = (gram (fixed false) m v a)ᵀ := by
  ext i j
  change _ = gram (fixed false) m v a j i
  simp only [gram, gram_trace, product, Bool.false_eq_true, ↓reduceIte]

/-- The usual-order quadratic form is the trace of one positive conjugation of the density. -/
private theorem gram_quadratic_trace {ι : Type*} [Fintype ι]
    (m : ℝ) (v : Vec) (a : ι → E) (c : ι → ℂ) :
    star c ⬝ᵥ (gram (fixed false) m v a *ᵥ c) =
      (density m v *
        ((∑ i, c i • phi (a i))ᴴ * (∑ j, c j • phi (a j)))).trace := by
  classical
  simp only [gram, gram_trace, product, Bool.false_eq_true, ↓reduceIte,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_smul,
    phi_star]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul]
  ring

private theorem gram_usual_hermitian {ι : Type*} (m : ℝ) (v : Vec) (a : ι → E) :
    (gram (fixed false) m v a).IsHermitian := by
  ext i j
  apply Complex.ext <;>
    simp [gram, evaluate, jordan_coordinates, fixed_coordinates, sign,
      PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      cross_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem fixed_gram_positive {ι : Type*} [Fintype ι]
    (opposite : Bool) (m : ℝ) (v : Vec) (hm : ‖v‖ ≤ m) (a : ι → E) :
    (gram (fixed opposite) m v a).PosSemidef := by
  classical
  have usual : (gram (fixed false) m v a).PosSemidef := by
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

private theorem fixed_phase_balance (opposite : Bool) : PB (fixed opposite) := by
  intro m v _ a b c
  cases opposite <;>
    simp [PB, squareReadout, phaseLeft, phaseRight, evaluate,
      jordan_coordinates, fixed_coordinates, sign, PiLp.inner_apply,
      Fin.sum_univ_three, RCLike.inner_apply, cross_apply] <;> ring

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
    simpa [a₀, b₀, c₀, jordan, fixed, sign, cross, hround] using hs

private theorem originalNorm_nonneg (a : E) : 0 ≤ originalNorm a :=
  add_nonneg (abs_nonneg _) (norm_nonneg _)

private theorem originalNorm_add (a b : E) :
    originalNorm (a + b) ≤ originalNorm a + originalNorm b := by
  change |a.1 + b.1| + ‖a.2 + b.2‖ ≤ (|a.1| + ‖a.2‖) + (|b.1| + ‖b.2‖)
  linarith [abs_add_le a.1 b.1, norm_add_le a.2 b.2]

private theorem cross_norm (x y : Vec) :
    ‖(toLp 2 (crossProduct x y) : Vec)‖ ≤ ‖x‖ * ‖y‖ := by
  let z : Vec := toLp 2 (crossProduct x y)
  have hi (p q : Vec) : inner ℝ p q =
      (fun i => p i) ⬝ᵥ (fun i => q i) := by
    simp [PiLp.inner_apply, dotProduct, RCLike.inner_apply, mul_comm]
  have hquad := cross_dot_cross (fun i => x i) (fun i => y i)
    (fun i => x i) (fun i => y i)
  change (fun i => z i) ⬝ᵥ (fun i => z i) = _ at hquad
  rw [← hi z z, ← hi x x, ← hi y y, ← hi x y, ← hi y x,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm y x] at hquad
  have h : ‖(toLp 2 (crossProduct x y) : Vec)‖ ^ 2 + (inner ℝ x y) ^ 2 =
      ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    dsimp [z] at hquad
    nlinarith only [hquad]
  nlinarith [norm_nonneg (toLp 2 (crossProduct x y) : Vec),
    mul_nonneg (norm_nonneg x) (norm_nonneg y), sq_nonneg (inner ℝ x y)]

private theorem fixed_bound (opposite : Bool) (a b : E) :
    originalNorm (fixed opposite a b) ≤ originalNorm a * originalNorm b := by
  have h := cross_norm a.2 b.2
  have ha : ‖a.2‖ ≤ originalNorm a := le_add_of_nonneg_left (abs_nonneg _)
  have hb : ‖b.2‖ ≤ originalNorm b := le_add_of_nonneg_left (abs_nonneg _)
  have hmul := mul_le_mul ha hb (norm_nonneg _) (originalNorm_nonneg _)
  cases opposite <;> simpa [originalNorm, fixed_coordinates, sign] using h.trans hmul

private theorem fixed_difference_bound (opposite : Bool) (a b a' b' : E) :
    originalNorm (fixed opposite a b - fixed opposite a' b') ≤
      originalNorm (a - a') * originalNorm b +
        originalNorm a' * originalNorm (b - b') := by
  have he : fixed opposite a b - fixed opposite a' b' =
      fixed opposite (a - a') b + fixed opposite a' (b - b') := by
    simp [map_sub, LinearMap.sub_apply]
    abel
  rw [he]
  exact (originalNorm_add _ _).trans
    (add_le_add (fixed_bound opposite _ _) (fixed_bound opposite _ _))

private theorem fixed_continuous (opposite : Bool) : OriginalContinuous (fixed opposite) := by
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
    mul_lt_mul_of_pos_left (lt_of_lt_of_le hb' (add_le_add_left hδ1 _)) hδ
  calc
    originalNorm (fixed opposite a' b' - fixed opposite a b) ≤
        δ * originalNorm b' + originalNorm a * δ := hmain.trans (add_le_add hfirst hsecond)
    _ < δ * K := by dsimp [K]; nlinarith
    _ ≤ η := hδη

/-- All conclusions refer to the same total relation on the original spin carrier. -/
structure Consequences (D : Relation) : Prop where
  p2 : P2 D
  pb : PB D
  unit_left : ∀ r b, D (r • unit) b = 0
  unit_right : ∀ r a, D a (r • unit) = 0
  translation : ∀ r q a b, D (a + r • unit) (b + q • unit) = D a b
  add_left : ∀ a b c, D (a + b) c = D a c + D b c
  add_right : ∀ a b c, D a (b + c) = D a b + D a c
  smul_left : ∀ r a b, D (r • a) b = r • D a b
  smul_right : ∀ r a b, D a (r • b) = r • D a b
  bound : ∀ a b, originalNorm (D a b) ≤ originalNorm a * originalNorm b
  difference_bound : ∀ a b a' b', originalNorm (D a b - D a' b') ≤
    originalNorm (a - a') * originalNorm b + originalNorm a' * originalNorm (b - b')
  continuous : OriginalContinuous D
  finite_gram : ∀ (n : ℕ) (m : ℝ) (v : Vec), ‖v‖ ≤ m →
    ∀ a : Fin n → E, (gram D m v a).PosSemidef
  reassociation : ∀ a b c, jordan (jordan a b) c - jordan a (jordan b c) =
    D (D a b) c - D a (D b c)

/-- The same cone, norm and all-mass evaluations in the Pauli realization. -/
def MatrixInterfaces (opposite : Bool) (D : Relation) : Prop :=
      (∀ m v, (density m v).PosSemidef ↔ ‖v‖ ≤ m) ∧
      (∀ m v, (density m v).trace = (m : ℂ)) ∧
      (∀ m v, PositiveEvaluation (evaluationLinear m v) ↔ ‖v‖ ≤ m) ∧
      (∀ α : E →ₗ[ℝ] ℝ, PositiveEvaluation α →
        ∃ m : ℝ, ∃ v : Vec, ‖v‖ ≤ m ∧ ∀ a, α a = evaluate m v a) ∧
      (∀ m v a, (density m v * phi a).trace = (evaluate m v a : ℂ)) ∧
      (∀ a, (phi a).PosSemidef ↔ cone a) ∧
      (∀ a r, (((r : ℂ) • (1 : Mat) - phi a).PosSemidef ∧
        ((r : ℂ) • (1 : Mat) + phi a).PosSemidef) ↔ originalNorm a ≤ r) ∧
      (∀ ρ : Mat, ρ.PosSemidef → ∃ m : ℝ, ∃ v : Vec, ‖v‖ ≤ m ∧ ρ = density m v) ∧
      (∀ a b, product opposite (phi a) (phi b) =
        phi (jordan a b) - Complex.I • phi (D a b))

/-- A single global cross orientation supplies both original relations and all original consumers.
The sign is fixed before any input, evaluation, finite label family or complex coefficient. -/
theorem same_D_consequences (opposite : Bool) (D : Relation)
    (hD : ∀ a b, D a b = fixed opposite a b) :
    Consequences D ∧ MatrixInterfaces opposite D := by
  have he : D = fun a b => fixed opposite a b := funext fun a => funext (hD a)
  subst D
  refine ⟨?_, density_positive, density_mass, evaluation_positive,
    positive_evaluation_complete, trace_evaluate,
    (fun a => _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_posSemidef_iff a.1 a.2),
    original_order_interval, density_surjective, phi_product opposite⟩
  refine {
    p2 := fun m v hm a => fixed_gram_positive opposite m v hm a
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
    simp [fixed_coordinates, unit, cross_apply]
  · intro r a
    simp [fixed_coordinates, unit, cross_apply]
  · intro r q a b
    simp [fixed_coordinates, unit]
  · intro a b c
    exact LinearMap.congr_fun ((fixed opposite).map_add a b) c
  · intro a b c
    exact (fixed opposite a).map_add b c
  · intro r a b
    exact LinearMap.congr_fun ((fixed opposite).map_smul r a) b
  · intro r a b
    exact (fixed opposite a).map_smul r b

end D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
