/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/RationalHassePrinciple
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational tensor scalar extension and full multiplication isomorphisms. -/

module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Flat.Basic
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


/-- The coefficient of the j-th basis vector in the square of the i-th. -/
noncomputable def structureCoefficient {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V)
    (i j : Fin n) : K := b.repr (μ (b i) (b i)) j

private theorem monomial_map_coordinate {n m : ℕ}
    (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (e : Fin n ≃ Fin m) (d : Fin n → Kˣ) (f : V ≃ₗ[K] W)
    (hf : ∀ i, f (b i) = (d i : K) • c (e i)) (x : V) (j : Fin n) :
    c.equivFun (f x) (e j) = b.equivFun x j * (d j : K) := by
  classical
  conv_lhs => rw [← b.sum_equivFun x]
  simp only [map_sum, map_smul, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    c.equivFun_self]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [e.injective.ne hij]
  · simp

private theorem isomorphism_basis_equations {n m : ℕ}
    (μ : Product K V) (ν : Product K W)
    (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (hb : Natural μ b) (hc : Natural ν c) (hp : Perfect ν)
    (f : V ≃ₗ[K] W) (hf : ∀ x y, f (μ x y) = ν (f x) (f y)) :
    ∃ e : Fin n ≃ Fin m, ∃ d : Fin n → Kˣ,
      (∀ i, f (b i) = (d i : K) • c (e i)) ∧
      ∀ i j, structureCoefficient μ b i j * (d j : K) =
        (d i : K) ^ 2 * structureCoefficient ν c (e i) (e j) := by
  classical
  have hnm : n = m := by
    have hdim := f.finrank_eq
    rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c] at hdim
    simpa using hdim
  subst m
  obtain ⟨σ, t, ht, hcoord⟩ := isomorphism_monomial μ ν b c hb hc hp f hf
  let e : Fin n ≃ Fin n := σ.symm
  let d : Fin n → Kˣ := fun i => Units.mk0 (t (e i)) (ht (e i))
  have hfb (i : Fin n) : f (b i) = (d i : K) • c (e i) := by
    apply c.equivFun.injective
    ext j
    simp only [hcoord, map_smul, Pi.smul_apply, smul_eq_mul, c.equivFun_self]
    change (if σ j = i then t j else 0) = t (σ.symm i) *
      (if σ.symm i = j then 1 else 0)
    by_cases h : j = σ.symm i
    · subst j
      simp
    · have h' : σ j ≠ i := by
        intro h'
        exact h (σ.injective (by simpa using h'))
      simp [h', Ne.symm h]
  refine ⟨e, d, hfb, ?_⟩
  intro i j
  have h := congrArg (fun z => c.equivFun z (e j)) (hf (b i) (b i))
  rw [monomial_map_coordinate b c e d f hfb] at h
  simpa [hfb, structureCoefficient, Basis.equivFun_apply, pow_two,
    smul_smul, mul_assoc] using h

private theorem monomial_equations_realize {n m : ℕ}
    (μ : Product K V) (ν : Product K W)
    (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (hb : Natural μ b) (hc : Natural ν c)
    (e : Fin n ≃ Fin m) (d : Fin n → Kˣ)
    (heq : ∀ i j, structureCoefficient μ b i j * (d j : K) =
      (d i : K) ^ 2 * structureCoefficient ν c (e i) (e j)) :
    ∃ f : V ≃ₗ[K] W, (∀ i, f (b i) = (d i : K) • c (e i)) ∧
      ∀ x y, f (μ x y) = ν (f x) (f y) := by
  classical
  let c' : Basis (Fin n) K W := (c.reindex e.symm).unitsSMul d
  let f : V ≃ₗ[K] W := b.equiv c' (Equiv.refl _)
  have hfb (i : Fin n) : f (b i) = (d i : K) • c (e i) := by
    simp [f, c', Basis.unitsSMul_apply, Units.smul_def]
  have hsquare (i : Fin n) : f (μ (b i) (b i)) = ν (f (b i)) (f (b i)) := by
    apply c.equivFun.injective
    ext k
    obtain ⟨j, rfl⟩ := e.surjective k
    rw [monomial_map_coordinate b c e d f hfb]
    simpa [hfb, structureCoefficient, Basis.equivFun_apply, pow_two,
      smul_smul, mul_assoc] using heq i j
  have hmaps : μ.compr₂ f.toLinearMap = ν.compl₁₂ f.toLinearMap f.toLinearMap := by
    apply LinearMap.ext_basis b b
    intro i j
    change f (μ (b i) (b j)) = ν (f (b i)) (f (b j))
    by_cases hij : i = j
    · subst j
      exact hsquare i
    · rw [hb i j hij, map_zero, hfb, hfb]
      simp [hc (e i) (e j) (e.injective.ne hij)]
  exact ⟨f, hfb, fun x y => congrArg (fun M : V →ₗ[K] V →ₗ[K] W => M x y) hmaps⟩


/-- Arbitrary multiplication-preserving linear bijections are exactly the monomial
solutions of the square-coefficient equations. The two finite dimensions are independent. -/
theorem isomorphic_iff_monomial_equations {n m : ℕ}
    (μ : Product K V) (ν : Product K W)
    (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (hb : Natural μ b) (hc : Natural ν c) (hp : Perfect ν) :
    Isomorphic μ ν ↔ ∃ e : Fin n ≃ Fin m, ∃ d : Fin n → Kˣ,
      ∀ i j, structureCoefficient μ b i j * (d j : K) =
        (d i : K) ^ 2 * structureCoefficient ν c (e i) (e j) := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨e, d, _, heq⟩ := isomorphism_basis_equations μ ν b c hb hc hp f hf
    exact ⟨e, d, heq⟩
  · rintro ⟨e, d, heq⟩
    obtain ⟨f, _, hf⟩ := monomial_equations_realize μ ν b c hb hc e d heq
    exact ⟨f, hf⟩

private theorem natural_baseChange (F : Type*) [Field F] [Algebra K F]
    {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b) :
    Natural (LinearMap.BilinMap.baseChange F μ) (b.baseChange F) := by
  intro i j hij
  simp [Basis.baseChange_apply, hb i j hij]

private theorem perfect_baseChange (F : Type*) [Field F] [Algebra K F]
    (μ : Product K V) (hp : Perfect μ) : Perfect (LinearMap.BilinMap.baseChange F μ) := by
  unfold Perfect at *
  apply top_unique
  calc
    ⊤ = (Submodule.span K {z | ∃ x y, μ x y = z}).baseChange F := by
      rw [hp, Submodule.baseChange_top]
    _ = Submodule.span F (TensorProduct.mk K F V 1 '' {z | ∃ x y, μ x y = z}) :=
      Submodule.baseChange_span F _
    _ ≤ Submodule.span F {z | ∃ x y, LinearMap.BilinMap.baseChange F μ x y = z} := by
      apply Submodule.span_le.mpr
      rintro z ⟨v, ⟨x, y, rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨1 ⊗ₜ[K] x, 1 ⊗ₜ[K] y, ?_⟩
      simp

private theorem structureCoefficient_baseChange (F : Type*) [Field F] [Algebra K F]
    {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V) (i j : Fin n) :
    structureCoefficient (LinearMap.BilinMap.baseChange F μ) (b.baseChange F) i j =
      algebraMap K F (structureCoefficient μ b i j) := by
  simp [structureCoefficient, Algebra.smul_def]

end Monomiality


/-- The monomial equations describe the actual tensor scalar-extension relation.
Only rational target perfection is needed; it ascends to the extended multiplication. -/
theorem isomorphic_over_iff_monomial_equations (F : Type) [Field F] [Algebra ℚ F]
    (A B : RationalEvolutionAlgebra) {n m : ℕ}
    (b : Basis (Fin n) ℚ A.Carrier) (c : Basis (Fin m) ℚ B.Carrier)
    (hb : Natural A.multiplication b) (hc : Natural B.multiplication c)
    (hp : Perfect B.multiplication) :
    IsomorphicOver F A B ↔ ∃ e : Fin n ≃ Fin m, ∃ d : Fin n → Fˣ,
      ∀ i j, algebraMap ℚ F (structureCoefficient A.multiplication b i j) * (d j : F) =
        (d i : F) ^ 2 * algebraMap ℚ F (structureCoefficient B.multiplication c (e i) (e j)) := by
  unfold IsomorphicOver
  rw [isomorphic_iff_monomial_equations _ _ (b.baseChange F) (c.baseChange F)
    (natural_baseChange F _ b hb) (natural_baseChange F _ c hc)
    (perfect_baseChange F _ hp)]
  simp only [structureCoefficient_baseChange]


section Components

attribute [local instance] Classical.propDecidable

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Weak components of the directed relation of nonzero square coefficients. -/
abbrev WeakComponent {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V) :=
  Quotient (Relation.EqvGen.setoid (fun i j => structureCoefficient μ b i j ≠ 0))

/-- The weak component containing a basis index. -/
def componentIndex {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V)
    (i : Fin n) : WeakComponent μ b := Quotient.mk _ i

private theorem componentIndex_of_coefficient {n : ℕ} (μ : Product K V)
    (b : Basis (Fin n) K V) {i j : Fin n} (h : structureCoefficient μ b i j ≠ 0) :
    componentIndex μ b i = componentIndex μ b j :=
  Quotient.sound (Relation.EqvGen.rel _ _ h)

/-- A coordinate submodule for a fibre of an arbitrary partition of a finite basis. -/
def coordinateSpace {n : ℕ} {Q : Type*} (b : Basis (Fin n) K V)
    (π : Fin n → Q) (q : Q) : Submodule K V where
  carrier := {x | ∀ i, π i ≠ q → b.equivFun x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp only [map_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
  smul_mem' := by
    intro a x hx i hi
    simp only [map_smul, Pi.smul_apply, hx i hi, smul_zero]

private theorem coordinateSpace_eq_span {n : ℕ} {Q : Type*}
    (b : Basis (Fin n) K V) (π : Fin n → Q) (q : Q) :
    coordinateSpace b π q = Submodule.span K (b '' {i | π i = q}) := by
  ext x
  rw [b.mem_span_image, Finsupp.support_subset_iff]
  rfl

private noncomputable def coordinateProjection {n : ℕ} {Q : Type*}
    (b : Basis (Fin n) K V) (π : Fin n → Q) (q : Q) : V →ₗ[K] V := by
  classical
  exact b.equivFun.symm.toLinearMap.comp
    (LinearMap.pi (fun i => if π i = q then (LinearMap.proj i).comp b.equivFun.toLinearMap else 0))

private theorem coordinateProjection_repr {n : ℕ} {Q : Type*}
    (b : Basis (Fin n) K V) (π : Fin n → Q) (q : Q) (x : V) (i : Fin n) :
    b.equivFun (coordinateProjection b π q x) i =
      if π i = q then b.equivFun x i else 0 := by
  classical
  change b.equivFun (b.equivFun.symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  change (if π i = q then (LinearMap.proj i).comp b.equivFun.toLinearMap else 0) x = _
  split_ifs <;> rfl

private theorem coordinateProjection_mem {n : ℕ} {Q : Type*}
    (b : Basis (Fin n) K V) (π : Fin n → Q) (q : Q) (x : V) :
    coordinateProjection b π q x ∈ coordinateSpace b π q := by
  intro i hi
  rw [coordinateProjection_repr, ite_eq_right hi]

private theorem coordinateProjection_fixed {n : ℕ} {Q : Type*}
    (b : Basis (Fin n) K V) (π : Fin n → Q) (q : Q)
    (x : coordinateSpace b π q) : coordinateProjection b π q x = x := by
  classical
  apply b.equivFun.injective
  ext i
  rw [coordinateProjection_repr]
  split_ifs with h
  · rfl
  · exact (x.property i h).symm

private theorem coordinateProjection_basis {n : ℕ} {Q : Type*}
    (b : Basis (Fin n) K V) (π : Fin n → Q) (q : Q) (i : Fin n) :
    coordinateProjection b π q (b i) = if π i = q then b i else 0 := by
  classical
  apply b.equivFun.injective
  ext j
  simp only [coordinateProjection_repr, Basis.equivFun_self, apply_ite, map_zero,
    ite_apply, Pi.zero_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [h]

private theorem coordinateProjection_mul {n : ℕ} {Q : Type*}
    (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b)
    (π : Fin n → Q)
    (hπ : ∀ i j, structureCoefficient μ b i j ≠ 0 → π i = π j)
    (q : Q) (x y : V) :
    coordinateProjection b π q (μ x y) =
      μ (coordinateProjection b π q x) (coordinateProjection b π q y) := by
  classical
  have hsquare (i : Fin n) : coordinateProjection b π q (μ (b i) (b i)) =
      if π i = q then μ (b i) (b i) else 0 := by
    apply b.equivFun.injective
    ext j
    rw [coordinateProjection_repr]
    by_cases hij : structureCoefficient μ b i j = 0
    · have hz : b.equivFun (μ (b i) (b i)) j = 0 := hij
      split_ifs <;> simp_all
    · have hh := hπ i j hij
      rw [hh]
      split_ifs <;> simp
  have hm : μ.compr₂ (coordinateProjection b π q) =
      μ.compl₁₂ (coordinateProjection b π q) (coordinateProjection b π q) := by
    apply LinearMap.ext_basis b b
    intro i j
    change coordinateProjection b π q (μ (b i) (b j)) =
      μ (coordinateProjection b π q (b i)) (coordinateProjection b π q (b j))
    rw [coordinateProjection_basis, coordinateProjection_basis]
    by_cases hij : i = j
    · subst j
      rw [hsquare]
      split_ifs <;> simp
    · rw [hb i j hij]
      split_ifs <;> simp [hb i j hij]
  exact congrArg (fun M : Product K V => M x y) hm


private theorem coordinateProjection_balance {n : ℕ} {Q : Type*}
    (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b)
    (π : Fin n → Q) (q : Q) (x y : V) :
    μ (coordinateProjection b π q x) y = μ x (coordinateProjection b π q y) := by
  classical
  rw [natural_expansion μ b hb, natural_expansion μ b hb]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coordinateProjection_repr]
  split_ifs <;> simp

private theorem coordinateProjection_left {n : ℕ} {Q : Type*}
    (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b)
    (π : Fin n → Q)
    (hπ : ∀ i j, structureCoefficient μ b i j ≠ 0 → π i = π j)
    (q : Q) (x y : V) :
    coordinateProjection b π q (μ x y) = μ (coordinateProjection b π q x) y := by
  rw [coordinateProjection_mul μ b hb π hπ,
    ← coordinateProjection_balance μ b hb π q,
    coordinateProjection_fixed b π q ⟨_, coordinateProjection_mem b π q x⟩]

private theorem coordinateSpace_left {n : ℕ} {Q : Type*}
    (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b)
    (π : Fin n → Q)
    (hπ : ∀ i j, structureCoefficient μ b i j ≠ 0 → π i = π j)
    (q : Q) (x : coordinateSpace b π q) (y : V) :
    μ x y ∈ coordinateSpace b π q := by
  have h := coordinateProjection_mem b π q (μ x y)
  rwa [coordinateProjection_left μ b hb π hπ,
    coordinateProjection_fixed b π q x] at h

private theorem coordinateSpace_right {n : ℕ} {Q : Type*}
    (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b)
    (π : Fin n → Q)
    (hπ : ∀ i j, structureCoefficient μ b i j ≠ 0 → π i = π j)
    (q : Q) (x : V) (y : coordinateSpace b π q) :
    μ x y ∈ coordinateSpace b π q := by
  have h := coordinateSpace_left μ b hb π hπ q y x
  have hc : μ (y : V) x = μ x y := by
    rw [natural_expansion μ b hb, natural_expansion μ b hb]
    simp only [mul_comm]
  rwa [hc] at h

private theorem coordinateProjection_other {n : ℕ} {Q : Type*}
    (b : Basis (Fin n) K V) (π : Fin n → Q) {q r : Q} (hqr : q ≠ r)
    (x : coordinateSpace b π r) : coordinateProjection b π q x = 0 := by
  apply b.equivFun.injective
  ext i
  rw [coordinateProjection_repr]
  by_cases hi : π i = q
  · have hir : π i ≠ r := by rw [hi]; exact hqr
    simp only [hi, ↓reduceIte, x.property i hir, map_zero, Pi.zero_apply]
  · simp [hi]

private theorem coordinateSpace_cross {n : ℕ} {Q : Type*}
    (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b)
    (π : Fin n → Q)
    {q r : Q} (hqr : q ≠ r) (x : coordinateSpace b π q)
    (y : coordinateSpace b π r) : μ x y = 0 := by
  calc
    μ (x : V) (y : V) = μ (coordinateProjection b π q x) y := by
      rw [coordinateProjection_fixed b π q x]
    _ = μ x (coordinateProjection b π q y) := coordinateProjection_balance μ b hb π q x y
    _ = 0 := by rw [coordinateProjection_other b π hqr y]; simp

/-- Restriction of a bilinear multiplication to an actual left ideal submodule. -/
def restrictedProduct (μ : Product K V) (S : Submodule K V)
    (hS : ∀ (x : S) (y : V), μ x y ∈ S) : Product K S where
  toFun x :=
    { toFun := fun y => ⟨μ x y, hS x y⟩
      map_add' := by intro y z; apply Subtype.ext; exact map_add (μ (x : V)) (y : V) (z : V)
      map_smul' := by intro a y; apply Subtype.ext; exact map_smul (μ (x : V)) a (y : V) }
  map_add' := by
    intro x y
    ext z
    exact congrArg (fun f : V →ₗ[K] V => f (z : V)) (map_add μ (x : V) (y : V))
  map_smul' := by
    intro a x
    ext z
    exact congrArg (fun f : V →ₗ[K] V => f (z : V)) (map_smul μ a (x : V))

private theorem coordinateSpace_perfect {n : ℕ} {Q : Type*}
    (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b) (hp : Perfect μ)
    (π : Fin n → Q)
    (hπ : ∀ i j, structureCoefficient μ b i j ≠ 0 → π i = π j) (q : Q) :
    Perfect (restrictedProduct μ (coordinateSpace b π q)
      (coordinateSpace_left μ b hb π hπ q)) := by
  let P : V →ₗ[K] coordinateSpace b π q :=
    (coordinateProjection b π q).codRestrict _ (coordinateProjection_mem b π q)
  have hsurj : Function.Surjective P := by
    intro x
    exact ⟨x, Subtype.ext (coordinateProjection_fixed b π q x)⟩
  unfold Perfect
  apply top_unique
  calc
    ⊤ = (Submodule.span K {z | ∃ x y, μ x y = z}).map P := by
      rw [hp, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    _ = Submodule.span K (P '' {z | ∃ x y, μ x y = z}) := Submodule.map_span _ _
    _ ≤ _ := by
      apply Submodule.span_le.mpr
      rintro z ⟨v, ⟨x, y, rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨P x, P y, ?_⟩
      apply Subtype.ext
      exact (coordinateProjection_mul μ b hb π hπ q x y).symm

/-- The actual submodule belonging to a weak support component. -/
abbrev componentSpace {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V)
    (q : WeakComponent μ b) := coordinateSpace b (componentIndex μ b) q

private theorem componentSpace_eq_span {n : ℕ} (μ : Product K V)
    (b : Basis (Fin n) K V) (q : WeakComponent μ b) :
    componentSpace μ b q = Submodule.span K (b '' {i | componentIndex μ b i = q}) :=
  coordinateSpace_eq_span b _ q

/-- Multiplication on a weak support component, inherited from the original product. -/
def componentProduct {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V)
    (hb : Natural μ b) (q : WeakComponent μ b) : Product K (componentSpace μ b q) :=
  restrictedProduct μ _ (by
    exact coordinateSpace_left μ b hb _
      (fun _ _ h => componentIndex_of_coefficient μ b h) q)

/-- Weak component spans are two-sided ideals, are mutually orthogonal, and are perfect
whenever the original natural-basis product is perfect. -/
theorem component_ideals_perfect {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V)
    (hb : Natural μ b) (hp : Perfect μ) :
    (∀ q : WeakComponent μ b,
      componentSpace μ b q = Submodule.span K (b '' {i | componentIndex μ b i = q}) ∧
      (∀ (x : componentSpace μ b q) (y : V), μ x y ∈ componentSpace μ b q) ∧
      (∀ (x : V) (y : componentSpace μ b q), μ x y ∈ componentSpace μ b q) ∧
      Perfect (componentProduct μ b hb q)) ∧
    (∀ (q r : WeakComponent μ b), q ≠ r →
      ∀ (x : componentSpace μ b q) (y : componentSpace μ b r), μ x y = 0) := by
  constructor
  · intro q
    exact ⟨coordinateSpace_eq_span b _ q,
      coordinateSpace_left μ b hb _ (fun _ _ h => componentIndex_of_coefficient μ b h) q,
      coordinateSpace_right μ b hb _ (fun _ _ h => componentIndex_of_coefficient μ b h) q,
      coordinateSpace_perfect μ b hb hp _ (fun _ _ h => componentIndex_of_coefficient μ b h) q⟩
  · intro q r hqr x y
    exact coordinateSpace_cross μ b hb _ hqr x y


private noncomputable def coordinateDecomposition {n : ℕ} {Q : Type*} [Fintype Q]
    (b : Basis (Fin n) K V) (π : Fin n → Q) :
    V ≃ₗ[K] (∀ q : Q, coordinateSpace b π q) where
  toFun x q := ⟨coordinateProjection b π q x, coordinateProjection_mem b π q x⟩
  invFun z := ∑ q, (z q : V)
  left_inv x := by
    apply b.equivFun.injective
    ext i
    simp only [map_sum, Finset.sum_apply, coordinateProjection_repr]
    simp [eq_comm]
  right_inv z := by
    funext q
    apply Subtype.ext
    change coordinateProjection b π q (∑ r, (z r : V)) = (z q : V)
    rw [map_sum]
    rw [Finset.sum_eq_single q]
    · exact coordinateProjection_fixed b π q (z q)
    · intro r hr hrq
      exact coordinateProjection_other b π (Ne.symm hrq) (z r)
    · simp
  map_add' x y := by ext q; exact map_add (coordinateProjection b π q) x y
  map_smul' a x := by ext q; exact map_smul (coordinateProjection b π q) a x

private theorem coordinateDecomposition_mul {n : ℕ} {Q : Type*} [Fintype Q]
    (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b)
    (π : Fin n → Q)
    (hπ : ∀ i j, structureCoefficient μ b i j ≠ 0 → π i = π j)
    (x y : V) (q : Q) :
    coordinateDecomposition b π (μ x y) q =
      restrictedProduct μ (coordinateSpace b π q) (coordinateSpace_left μ b hb π hπ q)
        (coordinateDecomposition b π x q) (coordinateDecomposition b π y q) := by
  apply Subtype.ext
  exact coordinateProjection_mul μ b hb π hπ q x y

/-- Multiplicative linear bijections on matched component ideals reconstruct an
unrestricted multiplicative linear bijection of the original products. -/
theorem isomorphic_of_component_matching {n m : ℕ}
    (μ : Product K V) (ν : Product K W) (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (hb : Natural μ b) (hc : Natural ν c)
    (e : WeakComponent μ b ≃ WeakComponent ν c)
    (h : ∀ q, Isomorphic (componentProduct μ b hb q) (componentProduct ν c hc (e q))) :
    Isomorphic μ ν := by
  classical
  let : Fintype (WeakComponent μ b) := Fintype.ofFinite _
  let : Fintype (WeakComponent ν c) := Fintype.ofFinite _
  let f : ∀ q, componentSpace μ b q ≃ₗ[K] componentSpace ν c (e q) :=
    fun q => Classical.choose (h q)
  have hf (q) (x y : componentSpace μ b q) :
      f q (componentProduct μ b hb q x y) =
        componentProduct ν c hc (e q) (f q x) (f q y) := Classical.choose_spec (h q) x y
  let D := coordinateDecomposition b (componentIndex μ b)
  let E := coordinateDecomposition c (componentIndex ν c)
  let R := LinearEquiv.piCongrLeft K (fun q => componentSpace ν c q) e
  let g : V ≃ₗ[K] W := ((D.trans (LinearEquiv.piCongrRight f)).trans R).trans E.symm
  have hg (x : V) (q : WeakComponent μ b) : E (g x) (e q) = f q (D x q) := by
    have hr : (R (LinearEquiv.piCongrRight f (D x))) (e q) = f q (D x q) :=
      congr_fun (R.symm_apply_apply (LinearEquiv.piCongrRight f (D x))) q
    simpa only [g, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using hr
  refine ⟨g, ?_⟩
  intro x y
  apply E.injective
  funext r
  obtain ⟨q, rfl⟩ := e.surjective r
  rw [hg, coordinateDecomposition_mul ν c hc _
    (fun _ _ h => componentIndex_of_coefficient ν c h), hg, hg]
  exact (congrArg (f q) (coordinateDecomposition_mul μ b hb _
    (fun _ _ h => componentIndex_of_coefficient μ b h) x y q)).trans (hf q _ _)


private theorem eqvGen_map {I J : Type*} {R : I → I → Prop} {S : J → J → Prop}
    (f : I → J) (hf : ∀ i j, R i j → S (f i) (f j)) {i j : I}
    (h : Relation.EqvGen R i j) : Relation.EqvGen S (f i) (f j) := by
  induction h with
  | rel i j h => exact Relation.EqvGen.rel _ _ (hf i j h)
  | refl i => exact Relation.EqvGen.refl _
  | symm i j _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans i j k _ _ hij hjk => exact Relation.EqvGen.trans _ _ _ hij hjk

private def relationComponentEquiv {I J : Type*} (R : I → I → Prop) (S : J → J → Prop)
    (e : I ≃ J) (he : ∀ i j, R i j ↔ S (e i) (e j)) :
    Quotient (Relation.EqvGen.setoid R) ≃ Quotient (Relation.EqvGen.setoid S) :=
  Quotient.congr e (by
    intro i j
    change Relation.EqvGen R i j ↔ Relation.EqvGen S (e i) (e j)
    constructor
    · exact eqvGen_map e (fun i j h => (he i j).mp h)
    · intro h
      have hh := eqvGen_map (R := S) (S := R) e.symm (fun i j h =>
        (he (e.symm i) (e.symm j)).mpr (by simpa using h)) h
      simpa using hh)

private def supportComponentEquiv {n m : ℕ}
    (μ : Product K V) (ν : Product K W) (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (e : Fin n ≃ Fin m)
    (he : ∀ i j, structureCoefficient μ b i j ≠ 0 ↔
      structureCoefficient ν c (e i) (e j) ≠ 0) :
    WeakComponent μ b ≃ WeakComponent ν c :=
  relationComponentEquiv _ _ e he

private theorem monomial_support_iff {n m : ℕ}
    (μ : Product K V) (ν : Product K W) (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (e : Fin n ≃ Fin m) (d : Fin n → Kˣ)
    (heq : ∀ i j, structureCoefficient μ b i j * (d j : K) =
      (d i : K) ^ 2 * structureCoefficient ν c (e i) (e j)) (i j : Fin n) :
    structureCoefficient μ b i j ≠ 0 ↔ structureCoefficient ν c (e i) (e j) ≠ 0 := by
  apply not_congr
  constructor
  · intro hi
    have hh := heq i j
    rw [hi, zero_mul] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ (d i).ne_zero)
  · intro hi
    have hh := heq i j
    rw [hi, mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right (d j).ne_zero

private theorem monomial_component_map {n m : ℕ}
    (μ : Product K V) (ν : Product K W) (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (e : Fin n ≃ Fin m) (d : Fin n → Kˣ)
    (he : ∀ i j, structureCoefficient μ b i j ≠ 0 ↔
      structureCoefficient ν c (e i) (e j) ≠ 0)
    (f : V ≃ₗ[K] W) (hfb : ∀ i, f (b i) = (d i : K) • c (e i))
    (q : WeakComponent μ b) :
    (componentSpace μ b q).map f.toLinearMap =
      componentSpace ν c (supportComponentEquiv μ ν b c e he q) := by
  let E := supportComponentEquiv μ ν b c e he
  have hE (i : Fin n) : E (componentIndex μ b i) = componentIndex ν c (e i) := rfl
  have hmem (i : Fin n) (hi : componentIndex μ b i = q) :
      c (e i) ∈ componentSpace ν c (E q) := by
    rw [componentSpace_eq_span]
    exact Submodule.subset_span ⟨e i, (hE i).symm.trans (congrArg E hi), rfl⟩
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, componentSpace_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    change f (b i) ∈ componentSpace ν c (E q)
    rw [hfb]
    exact Submodule.smul_mem _ _ (hmem i hi)
  · rw [componentSpace_eq_span]
    apply Submodule.span_le.mpr
    rintro y ⟨j, hj, rfl⟩
    obtain ⟨i, rfl⟩ := e.surjective j
    have hi : componentIndex μ b i = q := E.injective ((hE i).trans hj)
    apply Submodule.mem_map.mpr
    refine ⟨(↑((d i)⁻¹) : K) • b i, ?_, ?_⟩
    · apply Submodule.smul_mem
      rw [componentSpace_eq_span]
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    · simp [hfb, smul_smul]

private theorem component_matching_of_monomial {n m : ℕ}
    (μ : Product K V) (ν : Product K W) (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (hb : Natural μ b) (hc : Natural ν c)
    (e : Fin n ≃ Fin m) (d : Fin n → Kˣ)
    (heq : ∀ i j, structureCoefficient μ b i j * (d j : K) =
      (d i : K) ^ 2 * structureCoefficient ν c (e i) (e j))
    (f : V ≃ₗ[K] W) (hfb : ∀ i, f (b i) = (d i : K) • c (e i))
    (hf : ∀ x y, f (μ x y) = ν (f x) (f y)) :
    ∃ E : WeakComponent μ b ≃ WeakComponent ν c,
      (∀ q, (componentSpace μ b q).map f.toLinearMap = componentSpace ν c (E q)) ∧
      ∀ q, Isomorphic (componentProduct μ b hb q) (componentProduct ν c hc (E q)) := by
  let he := monomial_support_iff μ ν b c e d heq
  let E := supportComponentEquiv μ ν b c e he
  have hmap := monomial_component_map μ ν b c e d he f hfb
  refine ⟨E, hmap, ?_⟩
  intro q
  refine ⟨f.ofSubmodules _ _ (hmap q), ?_⟩
  intro x y
  apply Subtype.ext
  exact hf x y

/-- Every unrestricted isomorphism of perfect-target evolution products matches
weak component ideals and restricts to unrestricted isomorphisms on them. -/
theorem isomorphism_matches_components {n m : ℕ}
    (μ : Product K V) (ν : Product K W) (b : Basis (Fin n) K V) (c : Basis (Fin m) K W)
    (hb : Natural μ b) (hc : Natural ν c) (hp : Perfect ν)
    (f : V ≃ₗ[K] W) (hf : ∀ x y, f (μ x y) = ν (f x) (f y)) :
    ∃ E : WeakComponent μ b ≃ WeakComponent ν c,
      (∀ q, (componentSpace μ b q).map f.toLinearMap = componentSpace ν c (E q)) ∧
      ∀ q, Isomorphic (componentProduct μ b hb q) (componentProduct ν c hc (E q)) := by
  obtain ⟨e, d, hfb, heq⟩ := isomorphism_basis_equations μ ν b c hb hc hp f hf
  exact component_matching_of_monomial μ ν b c hb hc e d heq f hfb hf


/-- The component multiplication inside the actual tensor-extended ambient product. -/
noncomputable def baseChangedComponentProduct (F : Type*) [Field F] [Algebra K F]
    {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b)
    (q : WeakComponent (LinearMap.BilinMap.baseChange F μ) (b.baseChange F)) :
    Product F (componentSpace (LinearMap.BilinMap.baseChange F μ) (b.baseChange F) q) :=
  componentProduct _ _ (by exact natural_baseChange F μ b hb) q

private noncomputable def componentScalarEquiv (F : Type*) [Field F] [Algebra K F]
    {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V) :
    WeakComponent μ b ≃ WeakComponent (LinearMap.BilinMap.baseChange F μ) (b.baseChange F) :=
  relationComponentEquiv (fun i j => structureCoefficient μ b i j ≠ 0)
    (fun i j => structureCoefficient (LinearMap.BilinMap.baseChange F μ) (b.baseChange F) i j ≠ 0)
    (Equiv.refl (Fin n)) (by
      intro i j
      change structureCoefficient μ b i j ≠ 0 ↔
        structureCoefficient (LinearMap.BilinMap.baseChange F μ) (b.baseChange F) i j ≠ 0
      rw [structureCoefficient_baseChange]
      simp only [ne_eq, map_eq_zero])

private theorem componentSpace_baseChange (F : Type*) [Field F] [Algebra K F]
    {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V) (q : WeakComponent μ b) :
    (componentSpace μ b q).baseChange F =
      componentSpace (LinearMap.BilinMap.baseChange F μ) (b.baseChange F)
        (componentScalarEquiv F μ b q) := by
  let E := componentScalarEquiv F μ b
  have hset : {i | componentIndex (LinearMap.BilinMap.baseChange F μ) (b.baseChange F) i = E q} =
      {i | componentIndex μ b i = q} := by
    ext i
    change E (componentIndex μ b i) = E q ↔ componentIndex μ b i = q
    exact E.injective.eq_iff
  rw [componentSpace_eq_span, Submodule.baseChange_span, componentSpace_eq_span, hset,
    Set.image_image]
  congr 1
  simp only [Basis.baseChange_apply]
  rfl

private theorem tensor_restricted_multiplicative (F : Type*) [Field F] [Algebra K F]
    (μ : Product K V) (S : Submodule K V) (hS : ∀ (x : S) (y : V), μ x y ∈ S)
    (x y : F ⊗[K] S) :
    S.subtype.baseChange F (LinearMap.BilinMap.baseChange F (restrictedProduct μ S hS) x y) =
      LinearMap.BilinMap.baseChange F μ (S.subtype.baseChange F x) (S.subtype.baseChange F y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul a' y => simp [restrictedProduct]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

private theorem component_tensor_isomorphic (F : Type*) [Field F] [Algebra K F]
    {n : ℕ} (μ : Product K V) (b : Basis (Fin n) K V) (hb : Natural μ b)
    (q : WeakComponent μ b) :
    Isomorphic (LinearMap.BilinMap.baseChange F (componentProduct μ b hb q))
      (baseChangedComponentProduct F μ b hb (componentScalarEquiv F μ b q)) := by
  let S := componentSpace μ b q
  let f := (Submodule.toBaseChange.toLinearEquiv F S).trans
    (LinearEquiv.ofEq _ _ (componentSpace_baseChange F μ b q))
  refine ⟨f, ?_⟩
  intro x y
  apply Subtype.ext
  exact tensor_restricted_multiplicative F μ S _ x y

end Components

/-- Rational weak components agree with the actual tensor components, including
isomorphisms from tensor-extended component carriers, and component matches characterize
unrestricted isomorphism over every rational field extension. -/
theorem scalar_extension_component_reconstruction (F : Type) [Field F] [Algebra ℚ F]
    (A B : RationalEvolutionAlgebra) {n m : ℕ}
    (b : Basis (Fin n) ℚ A.Carrier) (c : Basis (Fin m) ℚ B.Carrier)
    (hb : Natural A.multiplication b) (hc : Natural B.multiplication c)
    (hpA : Perfect A.multiplication) (hpB : Perfect B.multiplication) :
    ∃ EA : WeakComponent A.multiplication b ≃
        WeakComponent (LinearMap.BilinMap.baseChange F A.multiplication) (b.baseChange F),
    ∃ EB : WeakComponent B.multiplication c ≃
        WeakComponent (LinearMap.BilinMap.baseChange F B.multiplication) (c.baseChange F),
      (∀ i, EA (componentIndex A.multiplication b i) =
        componentIndex (LinearMap.BilinMap.baseChange F A.multiplication) (b.baseChange F) i) ∧
      (∀ i, EB (componentIndex B.multiplication c i) =
        componentIndex (LinearMap.BilinMap.baseChange F B.multiplication) (c.baseChange F) i) ∧
      (∀ q, (componentSpace A.multiplication b q).baseChange F =
        componentSpace (LinearMap.BilinMap.baseChange F A.multiplication) (b.baseChange F) (EA q)) ∧
      (∀ q, (componentSpace B.multiplication c q).baseChange F =
        componentSpace (LinearMap.BilinMap.baseChange F B.multiplication) (c.baseChange F) (EB q)) ∧
      (∀ q, Isomorphic (LinearMap.BilinMap.baseChange F (componentProduct A.multiplication b hb q))
        (baseChangedComponentProduct F A.multiplication b hb (EA q))) ∧
      (∀ q, Isomorphic (LinearMap.BilinMap.baseChange F (componentProduct B.multiplication c hc q))
        (baseChangedComponentProduct F B.multiplication c hc (EB q))) ∧
      (∀ q, Perfect (baseChangedComponentProduct F A.multiplication b hb (EA q))) ∧
      (∀ q, Perfect (baseChangedComponentProduct F B.multiplication c hc (EB q))) ∧
      (IsomorphicOver F A B ↔ ∃ e : WeakComponent A.multiplication b ≃ WeakComponent B.multiplication c,
        ∀ q, Isomorphic (baseChangedComponentProduct F A.multiplication b hb (EA q))
          (baseChangedComponentProduct F B.multiplication c hc (EB (e q)))) := by
  classical
  let μ := LinearMap.BilinMap.baseChange F A.multiplication
  let ν := LinearMap.BilinMap.baseChange F B.multiplication
  let bF := b.baseChange F
  let cF := c.baseChange F
  have hbF := natural_baseChange F A.multiplication b hb
  have hcF := natural_baseChange F B.multiplication c hc
  let EA := componentScalarEquiv F A.multiplication b
  let EB := componentScalarEquiv F B.multiplication c
  refine ⟨EA, EB, fun _ => rfl, fun _ => rfl,
    componentSpace_baseChange F A.multiplication b,
    componentSpace_baseChange F B.multiplication c,
    component_tensor_isomorphic F A.multiplication b hb,
    component_tensor_isomorphic F B.multiplication c hc, ?_, ?_, ?_⟩
  · intro q
    exact ((component_ideals_perfect μ bF hbF (perfect_baseChange F _ hpA)).1 (EA q)).2.2.2
  · intro q
    exact ((component_ideals_perfect ν cF hcF (perfect_baseChange F _ hpB)).1 (EB q)).2.2.2
  · constructor
    · intro h
      obtain ⟨e, d, heq⟩ := (isomorphic_over_iff_monomial_equations F A B b c hb hc hpB).mp h
      have heqF : ∀ i j, structureCoefficient μ bF i j * (d j : F) =
          (d i : F)^2 * structureCoefficient ν cF (e i) (e j) := by
        intro i j
        simpa only [μ, ν, bF, cF, structureCoefficient_baseChange] using heq i j
      obtain ⟨f, hfb, hf⟩ := monomial_equations_realize μ ν bF cF hbF hcF e d heqF
      obtain ⟨E, _, hE⟩ := component_matching_of_monomial μ ν bF cF hbF hcF e d heqF f hfb hf
      refine ⟨(EA.trans E).trans EB.symm, ?_⟩
      intro q
      change Isomorphic (baseChangedComponentProduct F A.multiplication b hb (EA q))
        (baseChangedComponentProduct F B.multiplication c hc (EB (EB.symm (E (EA q)))))
      rw [EB.apply_symm_apply]
      exact hE (EA q)
    · rintro ⟨e, he⟩
      apply isomorphic_of_component_matching μ ν bF cF hbF hcF ((EA.symm.trans e).trans EB)
      intro q
      have hq := he (EA.symm q)
      rw [EA.apply_symm_apply] at hq
      exact hq



end D5.S3.QuadraticForms.EvolutionAlgebras.RationalHassePrinciple
