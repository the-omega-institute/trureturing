import OmegaBuild.Commands
import Mathlib.Data.Matrix.Basis
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Omega original.

Elementary generators and upper-triangular coordinates for a real diagonal
orthogonal Lie algebra whose diagonal entries square to one. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix

namespace OmegaMath.OrthogonalMatrixGenerators

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (σ : ι → ℝ)

def metric : Matrix ι ι ℝ := diagonal σ

variable (hs : ∀ i, σ i * σ i = 1)

include hs in
omit [Fintype ι] [LinearOrder ι] in
private theorem sign_ne_zero (i : ι) : σ i ≠ 0 :=
  fun h => by simpa [h] using hs i

def generator (a b : ι) : Matrix ι ι ℝ :=
  single a b (σ b) - single b a (σ a)

omit [Fintype ι] in
theorem generator_swap (a b : ι) : generator σ b a = -generator σ a b := by
  simp [generator, neg_sub]

omit [Fintype ι] in
theorem generator_diag (a : ι) : generator σ a a = 0 := sub_self _

theorem generator_mem (a b : ι) : (generator σ a b)ᵀ * metric σ + metric σ * generator σ a b = 0 := by
  ext i j
  simp only [metric, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.transpose_apply, Matrix.zero_apply, generator, Matrix.sub_apply, Matrix.single_apply]
  by_cases h₁ : a = i <;> by_cases h₂ : b = i <;>
    by_cases h₃ : a = j <;> by_cases h₄ : b = j <;> simp_all

omit [Fintype ι] in
theorem metric_symm (i j : ι) : metric σ i j = metric σ j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp [metric, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

private theorem single_product (a b c d : ι) :
    (single a b (σ b) : Matrix ι ι ℝ) * single c d (σ d) =
      metric σ b c • single a d (σ d) := by
  by_cases h : b = c
  · subst c
    simp [metric]
  · simp [h, Matrix.single_mul_single_of_ne, metric, Matrix.diagonal_apply_ne]

theorem generator_commutator (a b c d : ι) :
    generator σ a b * generator σ c d - generator σ c d * generator σ a b =
      metric σ b c • generator σ a d - metric σ a c • generator σ b d -
        metric σ b d • generator σ a c + metric σ a d • generator σ b c := by
  simp only [generator, Matrix.sub_mul, Matrix.mul_sub, single_product σ, smul_sub,
    metric_symm σ c a, metric_symm σ c b, metric_symm σ d a, metric_symm σ d b]
  abel

def orthogonalSubspace : Submodule ℝ (Matrix ι ι ℝ) where
  carrier := {X | Xᵀ * metric σ + metric σ * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change _ + _ = 0 at hX hY ⊢
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := by
    intro r X hX
    change _ + _ = 0 at hX ⊢
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

private theorem orthogonal_entries (X : Matrix ι ι ℝ) (hX : X ∈ orthogonalSubspace σ) (i j : ι) :
    X j i * σ j + σ i * X i j = 0 := by
  change Xᵀ * metric σ + metric σ * X = 0 at hX
  simpa [metric, Matrix.mul_diagonal, Matrix.diagonal_mul] using congr_fun (congr_fun hX i) j

abbrev OrderedPair (ι : Type*) [LT ι] := {p : ι × ι // p.1 < p.2}

def generators (p : OrderedPair ι) : Matrix ι ι ℝ := generator σ p.val.1 p.val.2

def coordinates : Matrix ι ι ℝ →ₗ[ℝ] (OrderedPair ι → ℝ) where
  toFun X p := X p.val.1 p.val.2 * σ p.val.2
  map_add' X Y := by ext p; simp [add_mul]
  map_smul' r X := by ext p; simp [mul_assoc]

omit [Fintype ι] in
private theorem basis_forward (p q : OrderedPair ι) :
    generators σ p q.val.1 q.val.2 = if p = q then σ q.val.2 else 0 := by
  have h : ¬ (p.val.2 = q.val.1 ∧ p.val.1 = q.val.2) := by
    rintro ⟨he, he'⟩
    have hp := p.property
    rw [he, he'] at hp
    exact (not_lt_of_gt q.property) hp
  by_cases hpq : p = q
  · subst q
    simp [generators, generator, h]
  · have h' : ¬ (p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) :=
      fun he => hpq (Subtype.ext (Prod.ext he.1 he.2))
    simp [generators, generator, h, h', hpq]

include hs

private theorem coordinates_sum (c : OrderedPair ι → ℝ) :
    coordinates σ (∑ p, c p • generators σ p) = c := by
  ext q
  change (∑ p, c p • generators σ p) q.val.1 q.val.2 * σ q.val.2 = c q
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, basis_forward σ]
  rw [Finset.sum_eq_single q]
  · simp [mul_assoc, hs]
  · intro p _ hp
    simp [hp]
  · simp

omit [Fintype ι] in
theorem coordinates_generator (p q : OrderedPair ι) :
    coordinates σ (generators σ q) p = if p = q then 1 else 0 := by
  change generators σ q p.val.1 p.val.2 * σ p.val.2 = _
  rw [basis_forward σ]
  by_cases h : p = q <;> simp [h, Ne.symm, hs]

private theorem eq_of_coordinates {X Y : Matrix ι ι ℝ}
    (hX : X ∈ orthogonalSubspace σ) (hY : Y ∈ orthogonalSubspace σ)
    (h : coordinates σ X = coordinates σ Y) : X = Y := by
  have upper (i j : ι) (hij : i < j) : X i j = Y i j := by
    have he := congr_fun h ⟨(i, j), hij⟩
    exact mul_right_cancel₀ (sign_ne_zero σ hs j) he
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact upper i j hij
  · have hx := orthogonal_entries σ X hX i i
    have hy := orthogonal_entries σ Y hY i i
    apply mul_right_cancel₀ (sign_ne_zero σ hs i)
    linarith only [hx, hy]
  · have hx := orthogonal_entries σ X hX j i
    have hy := orthogonal_entries σ Y hY j i
    rw [upper j i hji] at hx
    apply mul_right_cancel₀ (sign_ne_zero σ hs i)
    linarith only [hx, hy]

theorem generator_expansion (X : Matrix ι ι ℝ) (hX : X ∈ orthogonalSubspace σ) :
    (∑ p : OrderedPair ι, (X p.val.1 p.val.2 * σ p.val.2) • generators σ p) = X := by
  apply eq_of_coordinates σ hs _ hX (coordinates_sum σ hs (coordinates σ X))
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _
    (generator_mem σ p.val.1 p.val.2)

theorem generator_linearIndependent : LinearIndependent ℝ (generators σ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc q
  have h := congr_arg (coordinates σ) hc
  rw [coordinates_sum σ hs, map_zero] at h
  exact congr_fun h q

def coordinateEquiv : (orthogonalSubspace σ) ≃ₗ[ℝ] (OrderedPair ι → ℝ) :=
  LinearEquiv.ofBijective ((coordinates σ).comp (orthogonalSubspace σ).subtype)
    ⟨fun X Y h => Subtype.ext (eq_of_coordinates σ hs X.property Y.property h),
      fun c => ⟨⟨∑ p, c p • generators σ p, Submodule.sum_mem _
        fun p _ => Submodule.smul_mem _ _ (generator_mem σ p.val.1 p.val.2)⟩,
        coordinates_sum σ hs c⟩⟩

end OmegaMath.OrthogonalMatrixGenerators
