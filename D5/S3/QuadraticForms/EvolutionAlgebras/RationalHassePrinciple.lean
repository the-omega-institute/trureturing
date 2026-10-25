/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational tensor scalar extension and full multiplication isomorphisms. -/

module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic

/-! Rational evolution products and their unrestricted multiplication isomorphisms. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.RationalHassePrinciple

open scoped TensorProduct
open Module

/-- A bilinear multiplication, without associativity or a unit. -/
abbrev Product (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  V →ₗ[K] V →ₗ[K] V

/-- Perfection means that all pair products linearly span the carrier. -/
def Perfect {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (μ : Product K V) : Prop :=
  Submodule.span K {z | ∃ x y, μ x y = z} = ⊤

/-- A natural basis is an ordinary vector-space basis with vanishing mixed products. -/
def Natural {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V) : Prop :=
  ∀ i j, i ≠ j → μ (b i) (b j) = 0

/-- Isomorphisms impose only linear bijectivity and multiplication preservation. -/
def Isomorphic {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (μ : Product K V) (ν : Product K W) : Prop :=
  ∃ f : V ≃ₗ[K] W, ∀ x y, f (μ x y) = ν (f x) (f y)

/-- Finite-dimensional rational evolution algebras with a rational natural basis. -/
structure RationalEvolutionAlgebra where
  Carrier : Type
  [addCommGroup : AddCommGroup Carrier]
  [rationalModule : Module ℚ Carrier]
  [finiteDimensional : FiniteDimensional ℚ Carrier]
  multiplication : Product ℚ Carrier
  natural : ∃ n : ℕ, ∃ b : Basis (Fin n) ℚ Carrier, Natural multiplication b

attribute [instance] RationalEvolutionAlgebra.addCommGroup
  RationalEvolutionAlgebra.rationalModule RationalEvolutionAlgebra.finiteDimensional

/-- The full scalar-extension isomorphism relation, on tensor products themselves. -/
def IsomorphicOver (F : Type) [Field F] [Algebra ℚ F]
    (A B : RationalEvolutionAlgebra) : Prop :=
  Isomorphic (LinearMap.BilinMap.baseChange F A.multiplication)
    (LinearMap.BilinMap.baseChange F B.multiplication)

/-- Kaygorodov--Martin Gonzalez--Viruel, Conjecture 7, in its complete existence form. -/
def claim : Prop :=
  ∃ A B : RationalEvolutionAlgebra,
    Perfect A.multiplication ∧ Perfect B.multiplication ∧
    IsomorphicOver ℝ A B ∧
    (∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      IsomorphicOver (Padic p) A B) ∧
    ¬ Isomorphic A.multiplication B.multiplication

section Monomiality

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

private theorem natural_expansion {n : ℕ} (μ : Product K V)
    (b : Basis (Fin n) K V) (hb : Natural μ b) (x y : V) :
    μ x y = ∑ i, (b.equivFun x i * b.equivFun y i) • μ (b i) (b i) := by
  classical
  calc
    μ x y = μ (∑ i, b.equivFun x i • b i) (∑ j, b.equivFun y j • b j) := by
      rw [b.sum_equivFun, b.sum_equivFun]
    _ = ∑ i, ∑ j, (b.equivFun x i * b.equivFun y j) • μ (b i) (b j) := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = ∑ i, (b.equivFun x i * b.equivFun y i) • μ (b i) (b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_eq_single i
      · intro j hj hji
        rw [hb i j (Ne.symm hji), smul_zero]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim

private theorem natural_structure_map {n : ℕ} (μ : Product K V)
    (b : Basis (Fin n) K V) (hb : Natural μ b) :
    ∃ M : (Fin n → K) →ₗ[K] (Fin n → K),
      ∀ x y, b.equivFun (μ x y) = M (b.equivFun x * b.equivFun y) := by
  classical
  let e := Pi.basisFun K (Fin n)
  let M := e.constr K (fun i => b.equivFun (μ (b i) (b i)))
  refine ⟨M, ?_⟩
  intro x y
  rw [natural_expansion μ b hb x y, map_sum]
  simp [M, e]

private theorem perfect_structure_injective {n : ℕ} (ν : Product K W)
    (b : Basis (Fin n) K W) (hp : Perfect ν)
    (M : (Fin n → K) →ₗ[K] (Fin n → K))
    (hM : ∀ x y, b.equivFun (ν x y) = M (b.equivFun x * b.equivFun y)) :
    Function.Injective M := by
  have hspan : Submodule.span K {z | ∃ x y, ν x y = z} ≤
      (LinearMap.range M).comap b.equivFun.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, y, rfl⟩
    exact ⟨b.equivFun x * b.equivFun y, (hM x y).symm⟩
  have hs : Function.Surjective M := by
    intro z
    have hz : b.equivFun.symm z ∈ Submodule.span K {z | ∃ x y, ν x y = z} := by
      rw [hp]
      trivial
    have hh := hspan hz
    change b.equivFun (b.equivFun.symm z) ∈ LinearMap.range M at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact LinearMap.mem_range.mp hh
  exact (LinearMap.injective_iff_surjective).mpr hs

private theorem row_nonzero {n : ℕ} (b : Basis (Fin n) K V)
    (c : Basis (Fin n) K W) (f : V ≃ₗ[K] W) (i : Fin n) :
    ∃ j, c.equivFun (f (b j)) i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := f.surjective (c i)
  have hcoord : c.equivFun (f x) i =
      ∑ j, b.equivFun x j * c.equivFun (f (b j)) i := by
    calc
      c.equivFun (f x) i = c.equivFun (f (∑ j, b.equivFun x j • b j)) i := by
        rw [b.sum_equivFun x]
      _ = ∑ j, b.equivFun x j * c.equivFun (f (b j)) i := by
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hx, c.equivFun_self] at hcoord
  simp [h] at hcoord

private theorem column_nonzero {n : ℕ} (b : Basis (Fin n) K V)
    (c : Basis (Fin n) K W) (f : V ≃ₗ[K] W) (j : Fin n) :
    ∃ i, c.equivFun (f (b j)) i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hz : c.equivFun (f (b j)) = 0 := by
    funext i
    exact h i
  have hz' : c.equivFun (f (b j)) = c.equivFun 0 := by simpa using hz
  have hfzero : f (b j) = 0 := c.equivFun.injective hz'
  have hbzero : b j = 0 := f.injective (by simpa using hfzero)
  exact b.linearIndependent.ne_zero j hbzero

/-- Perfection forces every arbitrary algebra isomorphism to be monomial.
The natural bases may differ and the field is unrestricted. -/
theorem isomorphism_monomial {n : ℕ} (μ : Product K V) (ν : Product K W)
    (b : Basis (Fin n) K V) (c : Basis (Fin n) K W)
    (hb : Natural μ b) (hc : Natural ν c) (hp : Perfect ν)
    (f : V ≃ₗ[K] W) (hf : ∀ x y, f (μ x y) = ν (f x) (f y)) :
    ∃ σ : Equiv.Perm (Fin n), ∃ t : Fin n → K,
      (∀ i, t i ≠ 0) ∧
      (∀ i j, c.equivFun (f (b j)) i = if σ i = j then t i else 0) := by
  classical
  let p : Fin n → Fin n → K := fun i j => c.equivFun (f (b j)) i
  obtain ⟨M, hM⟩ := natural_structure_map ν c hc
  have hMi := perfect_structure_injective ν c hp M hM
  have hrow_zero (i j k : Fin n) (hjk : j ≠ k) : p i j * p i k = 0 := by
    have hprod : ν (f (b j)) (f (b k)) = 0 := by
      rw [← hf, hb j k hjk, map_zero]
    have hzero : M (c.equivFun (f (b j)) * c.equivFun (f (b k))) = 0 := by
      rw [← hM, hprod, map_zero]
    have hz : c.equivFun (f (b j)) * c.equivFun (f (b k)) = 0 :=
      hMi (by simpa using hzero)
    exact congr_fun hz i
  have hrow_at_most (i : Fin n) {j k : Fin n} (hj : p i j ≠ 0) (hk : p i k ≠ 0) :
      j = k := by
    by_contra hne
    exact (mul_ne_zero hj hk) (hrow_zero i j k hne)
  have hrow : ∀ i : Fin n, ∃! j : Fin n, p i j ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := row_nonzero b c f i
    exact ⟨j, by simpa [p] using hj, fun k hk =>
      (hrow_at_most i (j := j) (k := k) (by simpa [p] using hj)
        (by simpa [p] using hk)).symm⟩
  let s : Fin n → Fin n := fun i => Classical.choose (hrow i)
  have hs_ne (i : Fin n) : p i (s i) ≠ 0 := (Classical.choose_spec (hrow i)).1
  have hs_unique (i : Fin n) {j : Fin n} (hj : p i j ≠ 0) : j = s i :=
    (Classical.choose_spec (hrow i)).2 j hj
  have hs_surj : Function.Surjective s := by
    intro j
    obtain ⟨i, hi⟩ := column_nonzero b c f j
    exact ⟨i, (hs_unique i (by simpa [p] using hi)).symm⟩
  have hs_inj : Function.Injective s := Finite.injective_iff_surjective.mpr hs_surj
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective s ⟨hs_inj, hs_surj⟩
  let t : Fin n → K := fun i => p i (s i)
  refine ⟨σ, t, hs_ne, ?_⟩
  intro i j
  by_cases h : s i = j
  · change p i j = if s i = j then t i else 0
    simp [t, h]
  · have hz : p i j = 0 := by
      by_contra hpj
      exact h (hs_unique i hpj).symm
    change p i j = if s i = j then t i else 0
    simp [h, hz]

end Monomiality

end D5.S3.QuadraticForms.EvolutionAlgebras.RationalHassePrinciple
