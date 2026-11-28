/- GID: D5/S3/OperatorAlgebra/TracialRegularRepresentation
   generality: G
   mirror-B: none(waiver:covered-by-hyperfinite-type-ii1-factor-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Hilbert space of a faithful algebraic trace with bounded left multiplication. -/

import OmegaBuild.Commands
import D5.S3.OperatorAlgebra.BicommutantStrongDensity
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Tactic.NoncommRing

/-! Omega original.
The Hilbert space of a faithful algebraic trace with bounded left multiplication. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.TracialRegularRepresentation

open UniformSpace.Completion
open scoped ComplexConjugate InnerProductSpace

variable (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- A trace and an algebraic certificate of boundedness for each left multiplier. -/
structure TraceData where
  trace : A →ₗ[ℂ] ℂ
  one : trace 1 = 1
  cyclic : ∀ x y, trace (x * y) = trace (y * x)
  star' : ∀ x, trace (star x) = star (trace x)
  positive : ∀ x, 0 ≤ (trace (star x * x)).re
  faithful : ∀ x, trace (star x * x) = 0 → x = 0
  bounded : ∀ a : A, ∃ (c : ℝ) (b : A), 0 ≤ c ∧ (c ^ 2 : ℂ) • 1 - star a * a = star b * b

variable {A} (t : TraceData A)

/-- The algebraic domain equipped with the trace inner product. -/
def Domain (_ : TraceData A) := A

instance : Ring (Domain t) := inferInstanceAs (Ring A)
instance : Algebra ℂ (Domain t) := inferInstanceAs (Algebra ℂ A)
instance : StarRing (Domain t) := inferInstanceAs (StarRing A)
instance : StarModule ℂ (Domain t) := inferInstanceAs (StarModule ℂ A)

private def unmodel (x : Domain t) : A := x

@[instance_reducible] private def innerCore : InnerProductSpace.Core ℂ (Domain t) where
  inner x y := t.trace (star (unmodel t x) * unmodel t y)
  conj_inner_symm x y := by
    change star (t.trace (star (unmodel t y) * unmodel t x)) = _
    rw [← t.star', star_mul, star_star]
  re_inner_nonneg := t.positive
  add_left x y z := by
    change t.trace (star (unmodel t x + unmodel t y) * unmodel t z) = _
    rw [star_add, add_mul, map_add]
  smul_left x y r := by
    change t.trace (star (r • unmodel t x) * unmodel t y) = _
    rw [star_smul, smul_mul_assoc, map_smul, smul_eq_mul]
    rfl
  definite := t.faithful

local instance : InnerProductSpace.Core ℂ (Domain t) := innerCore t

instance : NormedAddCommGroup (Domain t) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Domain t)
instance : InnerProductSpace ℂ (Domain t) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (Domain t))

theorem inner_domain (x y : Domain t) : ⟪x, y⟫_ℂ = t.trace (star (unmodel t x) * unmodel t y) := rfl

private theorem norm_sq (x : Domain t) :
    ‖x‖ ^ 2 = (t.trace (star (unmodel t x) * unmodel t x)).re :=
  InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x

/-- The tracial Hilbert completion. -/
abbrev Hilbert := UniformSpace.Completion (Domain t)

/-- The cyclic vector represented by the algebra unit. -/
def vacuum : Hilbert t := ((1 : Domain t) : Hilbert t)

private theorem leftBound (a : Domain t) :
    ∃ c : ℝ, ∀ x : Domain t, ‖a * x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, b, hc, hb⟩ := t.bounded a
  change (c ^ 2 : ℂ) • (1 : A) - star (unmodel t a) * unmodel t a = star b * b at hb
  refine ⟨c, fun x => (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp ?_⟩
  have h : star (b * (unmodel t x)) * (b * (unmodel t x)) =
      (c ^ 2 : ℂ) • (star (unmodel t x) * (unmodel t x))
        - star ((unmodel t a) * (unmodel t x)) * ((unmodel t a) * (unmodel t x)) := by
    calc
      _ = star (unmodel t x) * (star b * b) * (unmodel t x) := by simp only [star_mul, mul_assoc]
      _ = _ := by
        rw [← hb, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, star_mul]
        simp only [mul_assoc]
  have hp := t.positive (b * (unmodel t x))
  rw [h, map_sub, map_smul, smul_eq_mul, Complex.sub_re, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul] at hp
  rw [mul_pow, norm_sq, norm_sq]
  change (t.trace (star (unmodel t a * unmodel t x) * (unmodel t a * unmodel t x))).re ≤ _
  exact sub_nonneg.mp hp

private theorem norm_star_domain (a : Domain t) : ‖star a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq, norm_sq]
  change (t.trace (star (star (unmodel t a)) * star (unmodel t a))).re = _
  rw [star_star]
  exact congrArg Complex.re (t.cyclic (unmodel t a) (star (unmodel t a)))

private def leftDomain (a : Domain t) : Domain t →L[ℂ] Domain t :=
  LinearMap.mkContinuous (LinearMap.mul ℂ (Domain t) a) (leftBound t a).choose
    (leftBound t a).choose_spec

private def rightDomain (a : Domain t) : Domain t →L[ℂ] Domain t := by
  let h := leftBound t (star a)
  refine LinearMap.mkContinuous ((LinearMap.mul ℂ (Domain t)).flip a) h.choose fun x => ?_
  change ‖x * a‖ ≤ h.choose * ‖x‖
  rw [← norm_star_domain t (x * a), star_mul, ← norm_star_domain t x]
  exact h.choose_spec (star x)

/-- Bounded left multiplication extended from the trace domain. -/
def left (a : Domain t) : Hilbert t →L[ℂ] Hilbert t := (leftDomain t a).completion

/-- Bounded right multiplication extended from the trace domain. -/
def right (a : Domain t) : Hilbert t →L[ℂ] Hilbert t := (rightDomain t a).completion

@[simp] theorem left_coe (a x : Domain t) : left t a x = (↑(a * x) : Hilbert t) := by
  rw [left, ContinuousLinearMap.completion_apply_coe]
  rfl

@[simp] theorem right_coe (a x : Domain t) : right t a x = (↑(x * a) : Hilbert t) := by
  rw [right, ContinuousLinearMap.completion_apply_coe]
  rfl

theorem left_commute_right (a b : Domain t) : Commute (left t a) (right t b) := by
  change left t a * right t b = right t b * left t a
  ext x
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp only [ContinuousLinearMap.mul_apply, right_coe, left_coe, mul_assoc]

theorem left_star (a : Domain t) : left t (star a) = star (left t a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    simp only [left_coe, inner_coe, inner_domain]
    change t.trace (star (star (unmodel t a) * unmodel t x) * unmodel t y) =
      t.trace (star (unmodel t x) * (unmodel t a * unmodel t y))
    simp only [star_mul, star_star, mul_assoc]

/-- The concrete von Neumann algebra generated by bounded left multipliers. -/
def bicommutant : VonNeumannAlgebra (Hilbert t) :=
  ⟨StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (Set.range (left t))), by simp⟩

private theorem range_union_star : Set.range (left t) ∪ star (Set.range (left t)) =
    Set.range (left t) := by
  rw [Set.union_eq_left]
  rintro z ⟨a, ha⟩
  refine ⟨star a, ?_⟩
  rw [left_star]
  exact congrArg star ha |>.trans (star_star z)

private theorem mem_bicommutant {z : Hilbert t →L[ℂ] Hilbert t} :
    z ∈ bicommutant t ↔ z ∈ Set.centralizer (Set.centralizer (Set.range (left t))) := by
  change z ∈ SetLike.coe (StarSubalgebra.centralizer ℂ
    (SetLike.coe (StarSubalgebra.centralizer ℂ (Set.range (left t))))) ↔ _
  rw [StarSubalgebra.coe_centralizer_centralizer, range_union_star]

theorem left_mem_bicommutant (a : Domain t) : left t a ∈ bicommutant t := by
  apply (mem_bicommutant t).mpr
  exact Set.subset_centralizer_centralizer ⟨a, rfl⟩

theorem commute_right_of_mem {z : Hilbert t →L[ℂ] Hilbert t}
    (hz : z ∈ bicommutant t) (a : Domain t) : Commute z (right t a) := by
  have hz' := (mem_bicommutant t).mp hz
  have hr : right t a ∈ Set.centralizer (Set.range (left t)) := by
    rintro _ ⟨b, rfl⟩
    exact (left_commute_right t b a).eq
  exact (show Commute (right t a) z from hz' _ hr).symm

/-- The vacuum is separating for the bicommutant. -/
theorem eq_zero_of_vacuum {z : Hilbert t →L[ℂ] Hilbert t}
    (hz : z ∈ bicommutant t) (h : z (vacuum t) = 0) : z = 0 := by
  ext x
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    have hx : right t x (vacuum t) = (x : Hilbert t) := by simp [vacuum]
    have hc : z (right t x (vacuum t)) = right t x (z (vacuum t)) :=
      DFunLike.congr_fun (commute_right_of_mem t hz x).eq _
    rw [hx, h, map_zero] at hc
    exact hc

theorem right_star (a : Domain t) : right t (star a) = star (right t a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    simp only [right_coe, inner_coe, inner_domain]
    change t.trace (star (unmodel t x * star (unmodel t a)) * unmodel t y) =
      t.trace (star (unmodel t x) * (unmodel t y * unmodel t a))
    rw [star_mul, star_star, mul_assoc, t.cyclic (unmodel t a), mul_assoc]

private def domainStar : Domain t →L⋆[ℂ] Domain t :=
  (starLinearEquiv ℂ : Domain t ≃ₗ⋆[ℂ] Domain t).toLinearMap.mkContinuous 1
    (fun x => by
      change ‖star x‖ ≤ 1 * ‖x‖
      rw [norm_star_domain, one_mul])

private def hilbertStar : Hilbert t →L⋆[ℂ] Hilbert t := (domainStar t).completion

private theorem hilbertStar_coe (x : Domain t) : hilbertStar t x = (↑(star x) : Hilbert t) := by
  rw [hilbertStar, ContinuousLinearMap.completion_apply_coe]
  rfl

private theorem hilbertStar_symm (x y : Hilbert t) :
    ⟪hilbertStar t x, y⟫_ℂ = ⟪hilbertStar t y, x⟫_ℂ := by
  induction x, y using induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    simp only [hilbertStar_coe, inner_coe, inner_domain]
    change t.trace (star (star (unmodel t x)) * unmodel t y) =
      t.trace (star (star (unmodel t y)) * unmodel t x)
    rw [star_star, star_star, t.cyclic]

private theorem adjoint_vacuum {z : Hilbert t →L[ℂ] Hilbert t} (hz : z ∈ bicommutant t) :
    star z (vacuum t) = hilbertStar t (z (vacuum t)) := by
  apply ext_inner_right ℂ
  intro x
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    have hcomm : z (right t x (vacuum t)) = right t x (z (vacuum t)) :=
      DFunLike.congr_fun (commute_right_of_mem t hz x).eq _
    have hx : right t x (vacuum t) = (x : Hilbert t) := by simp [vacuum]
    have hxx : star (right t x) (vacuum t) = (↑(star x) : Hilbert t) := by
      rw [← right_star]
      simp [vacuum]
    calc
      ⟪star z (vacuum t), (x : Hilbert t)⟫_ℂ = ⟪vacuum t, z x⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_left z _ _
      _ = ⟪vacuum t, right t x (z (vacuum t))⟫_ℂ := by rw [← hcomm, hx]
      _ = ⟪star (right t x) (vacuum t), z (vacuum t)⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_left (right t x) _ _).symm
      _ = _ := by rw [hxx, hilbertStar_symm, hilbertStar_coe]

/-- The vector functional at the algebra unit. -/
def vacuumTrace (z : Hilbert t →L[ℂ] Hilbert t) : ℂ := ⟪vacuum t, z (vacuum t)⟫_ℂ

theorem vacuumTrace_cyclic {z w : Hilbert t →L[ℂ] Hilbert t}
    (hz : z ∈ bicommutant t) (hw : w ∈ bicommutant t) :
    vacuumTrace t (z * w) = vacuumTrace t (w * z) := by
  calc
    vacuumTrace t (z * w) = ⟪star z (vacuum t), w (vacuum t)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left z _ _).symm
    _ = ⟪star w (vacuum t), z (vacuum t)⟫_ℂ := by
      rw [adjoint_vacuum t hz, adjoint_vacuum t hw, hilbertStar_symm]
    _ = vacuumTrace t (w * z) := ContinuousLinearMap.adjoint_inner_left w _ _

theorem vacuumTrace_one : vacuumTrace t 1 = 1 := by
  simp only [vacuumTrace, ContinuousLinearMap.one_apply, vacuum, inner_coe, inner_domain]
  change t.trace (star (1 : A) * 1) = 1
  rw [star_one, one_mul, t.one]

theorem vacuumTrace_faithful {z : Hilbert t →L[ℂ] Hilbert t}
    (hz : z ∈ bicommutant t) :
    vacuumTrace t (star z * z) = (‖z (vacuum t)‖ ^ 2 : ℝ) ∧
    (vacuumTrace t (star z * z) = 0 ↔ z = 0) := by
  have he : vacuumTrace t (star z * z) = (‖z (vacuum t)‖ ^ 2 : ℝ) := by
    simp only [vacuumTrace, ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  refine ⟨he, ?_⟩
  rw [he]
  constructor
  · intro h
    apply eq_zero_of_vacuum t hz
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (Complex.ofReal_eq_zero.mp h))
  · rintro rfl
    simp

/-- The left regular representation as a unital star-algebra homomorphism. -/
def leftHom : Domain t →⋆ₐ[ℂ] (Hilbert t →L[ℂ] Hilbert t) where
  toFun := left t
  map_star' := left_star t
  map_one' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp
  map_mul' a b := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp [ContinuousLinearMap.mul_apply, mul_assoc]
  map_zero' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp
  map_add' a b := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp [add_mul, coe_add]
  commutes' c := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      change left t (algebraMap ℂ (Domain t) c) x = _
      rw [left_coe, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, coe_smul]
      simp [Algebra.algebraMap_eq_smul_one]

theorem leftHom_injective : Function.Injective (leftHom t) := by
  intro a b h
  apply UniformSpace.Completion.coe_injective (α := Domain t)
  have he := DFunLike.congr_fun h (vacuum t)
  change left t a (vacuum t) = left t b (vacuum t) at he
  simpa [vacuum] using he

theorem vacuumTrace_left (a : Domain t) : vacuumTrace t (left t a) = t.trace (unmodel t a) := by
  simp only [vacuumTrace, vacuum, left_coe, mul_one, inner_coe, inner_domain]
  change t.trace (star (1 : A) * unmodel t a) = _
  rw [star_one, one_mul]

/-- Algebraic left multipliers approximate bicommutant operators on every finite family. -/
theorem exists_algebraic_approximation {ι : Type*} [Fintype ι]
    {z : Hilbert t →L[ℂ] Hilbert t} (hz : z ∈ bicommutant t)
    (x : ι → Hilbert t) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : Domain t, ∀ i, ‖left t a (x i) - z (x i)‖ < ε := by
  have hz' : z ∈ Set.centralizer (Set.centralizer (SetLike.coe (leftHom t).range)) :=
    (mem_bicommutant t).mp hz
  obtain ⟨S, ⟨a, rfl⟩, hS⟩ :=
    Omega.BicommutantStrongDensity.exists_approximation (leftHom t).range hz' x hε
  exact ⟨a, hS⟩

open Filter Topology in
/-- The strong limit of an increasing sequence of orthogonal projections is a projection. -/
theorem strong_projection_limit {P : ℕ → Hilbert t →L[ℂ] Hilbert t}
    {S : Hilbert t →L[ℂ] Hilbert t} (hp : ∀ n, IsStarProjection (P n))
    (hm : Monotone P) (hs : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 (S x))) :
    IsStarProjection S := by
  constructor
  · change S * S = S
    ext x
    change S (S x) = S x
    have hfix (n : ℕ) : S (P n x) = P n x := by
      apply tendsto_nhds_unique (hs (P n x))
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with m hnm
      have he := (hp n).le_iff_mul_eq_right (hp m) |>.mp (hm hnm)
      exact (DFunLike.congr_fun he x).symm
    have hl : Tendsto (fun n => S (P n x)) atTop (𝓝 (S (S x))) :=
      (S.continuous.tendsto _).comp (hs x)
    exact tendsto_nhds_unique hl ((hs x).congr fun n => (hfix n).symm)
  · change star S = S
    refine (ContinuousLinearMap.eq_adjoint_iff S S).mpr ?_ |>.symm
    intro x y
    have hl := (hs x).inner (𝕜 := ℂ) (tendsto_const_nhds (x := y))
    have hr := (tendsto_const_nhds (x := x)).inner (𝕜 := ℂ) (hs y)
    apply tendsto_nhds_unique hl
    apply hr.congr
    intro n
    exact ((ContinuousLinearMap.eq_adjoint_iff (P n) (P n)).mp
      (hp n).isSelfAdjoint.star_eq.symm x y).symm

/-- A bicommutant element commuting with the algebraic domain is scalar when cyclic
functionals on the domain are scalar multiples of its trace. -/
theorem scalar_of_commute_left
    (hunique : ∀ φ : Domain t →ₗ[ℂ] ℂ, φ 1 = 1 →
      (∀ a b, φ (a * b) = φ (b * a)) → φ = (t.trace : Domain t →ₗ[ℂ] ℂ))
    {z : Hilbert t →L[ℂ] Hilbert t} (hz : z ∈ bicommutant t)
    (hcomm : ∀ a : Domain t, Commute z (left t a)) :
    z = vacuumTrace t z • 1 := by
  let φ : Domain t →ₗ[ℂ] ℂ :=
    { toFun := fun a => vacuumTrace t (z * left t a)
      map_add' := by
        intro a b
        change vacuumTrace t (z * leftHom t (a + b)) =
          vacuumTrace t (z * leftHom t a) + vacuumTrace t (z * leftHom t b)
        simp [map_add, mul_add, vacuumTrace, inner_add_right]
      map_smul' := by
        intro c a
        change vacuumTrace t (z * leftHom t (c • a)) = c • vacuumTrace t (z * leftHom t a)
        simp [map_smul, mul_smul_comm, vacuumTrace, inner_smul_right, smul_eq_mul] }
  have hφ : ∀ a b, φ (a * b) = φ (b * a) := by
    intro a b
    change vacuumTrace t (z * leftHom t (a * b)) =
      vacuumTrace t (z * leftHom t (b * a))
    rw [map_mul (leftHom t), map_mul (leftHom t), ← mul_assoc, ← mul_assoc]
    change vacuumTrace t (z * left t a * left t b) =
      vacuumTrace t (z * left t b * left t a)
    rw [vacuumTrace_cyclic t (mul_mem hz (left_mem_bicommutant t a))
      (left_mem_bicommutant t b), ← mul_assoc, ← (hcomm b).eq]
  have hval : φ 1 = vacuumTrace t z := by
    change vacuumTrace t (z * leftHom t 1) = _
    rw [map_one, mul_one]
  let τ : Domain t →ₗ[ℂ] ℂ := t.trace
  have hnormalized : φ + (1 - φ 1) • τ = τ := by
    apply hunique
    · change φ 1 + (1 - φ 1) * t.trace 1 = 1
      rw [t.one, mul_one, add_sub_cancel]
    · intro a b
      change φ (a * b) + (1 - φ 1) * τ (a * b) =
        φ (b * a) + (1 - φ 1) * τ (b * a)
      have hτ : τ (a * b) = τ (b * a) := t.cyclic a b
      rw [hφ a b, hτ]
  have hscalar (a : Domain t) : φ a = φ 1 * t.trace a := by
    have he := DFunLike.congr_fun hnormalized a
    change φ a + (1 - φ 1) * t.trace a = t.trace a at he
    apply add_right_cancel (b := (1 - φ 1) * t.trace a)
    rw [he, sub_mul, one_mul, add_sub_cancel]
  have hv : z (vacuum t) = vacuumTrace t z • vacuum t := by
    apply ext_inner_left ℂ
    intro x
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      have he := hscalar (star x)
      rw [hval] at he
      change vacuumTrace t (z * left t (star x)) =
        vacuumTrace t z * t.trace (unmodel t (star x)) at he
      rw [(hcomm (star x)).eq] at he
      simp only [vacuumTrace, ContinuousLinearMap.mul_apply, left_star,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] at he
      have hx : left t x (vacuum t) = (x : Hilbert t) := by simp [vacuum]
      rw [hx] at he
      rw [inner_smul_right, vacuum, inner_coe, inner_domain]
      change ⟪(x : Hilbert t), z (vacuum t)⟫_ℂ =
        vacuumTrace t z * t.trace (star (unmodel t x) * 1)
      rw [mul_one]
      exact he
  have hm : z - vacuumTrace t z • 1 ∈ bicommutant t := by
    change z - vacuumTrace t z • 1 ∈ (bicommutant t).toStarSubalgebra
    exact sub_mem hz (SMulMemClass.smul_mem (vacuumTrace t z) (one_mem _))
  apply sub_eq_zero.mp (eq_zero_of_vacuum t hm ?_)
  simpa using sub_eq_zero.mpr hv

end Omega.TracialRegularRepresentation
