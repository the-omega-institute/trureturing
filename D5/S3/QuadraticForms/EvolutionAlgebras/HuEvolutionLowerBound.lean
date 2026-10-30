/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square-zero subspaces force a sharp lower bound on evolution embedding dimension. -/

/-
The square-zero embedding bound is due to Wenlin Zhang and Haobo Ma in
Structure tests for stable derived terms. The proof uses a full-support
coordinate multiplier and rank-nullity. Commutativity is retained from the
source statement but is not used in its proof. No associativity or unit is
assumed. All square spans contain every pair product.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.CosetCover
import Mathlib.Algebra.CharZero.Infinite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound


abbrev Coord (d : ℕ) := Fin d → ℂ
abbrev Product (d : ℕ) := Coord d →ₗ[ℂ] Coord d →ₗ[ℂ] Coord d

def square {d : ℕ} (μ : Product d) (U : Submodule ℂ (Coord d)) :
    Submodule ℂ (Coord d) :=
  Submodule.span ℂ {z | ∃ x ∈ U, ∃ y ∈ U, μ x y = z}

def commutative {d : ℕ} (μ : Product d) : Prop :=
  ∀ x y, μ x y = μ y x

def perfect {d : ℕ} (μ : Product d) : Prop :=
  square μ ⊤ = ⊤

def hasNaturalBasis {d : ℕ} (μ : Product d) : Prop :=
  ∃ b : Module.Basis (Fin d) ℂ (Coord d),
    ∀ i j : Fin d, i ≠ j → μ (b i) (b j) = 0

def hasEvolutionEmbedding {d : ℕ} (μ : Product d) (n : ℕ) : Prop :=
  ∃ ν : Product n, ∃ f : Coord d →ₗ[ℂ] Coord n,
    hasNaturalBasis ν ∧ Function.Injective f ∧
    ∀ x y, f (μ x y) = ν (f x) (f y)


/-- A vector in a coordinate subspace can be chosen nonzero on its entire support. -/
private theorem exists_full_support {n : ℕ} (U : Submodule ℂ (Coord n)) :
    ∃ v : U, ∀ i : Fin n, (∃ x : U, (x : Coord n) i ≠ 0) →
      (v : Coord n) i ≠ 0 := by
  classical
  let I := {i : Fin n // ∃ x : U, (x : Coord n) i ≠ 0}
  let l : I → U →ₗ[ℂ] ℂ := fun i =>
    { toFun := fun x => (x : Coord n) i.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hproper : ∀ i : I, LinearMap.ker (l i) ≠ ⊤ := by
    intro i hi
    obtain ⟨x, hx⟩ := i.property
    have hxker : x ∈ LinearMap.ker (l i) := by rw [hi]; trivial
    exact hx hxker
  have hcover : (⋃ i : I, (LinearMap.ker (l i) : Set U)) ≠ Set.univ := by
    intro hc
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hc
    exact hproper i hi
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).mp hcover
  refine ⟨v, ?_⟩
  intro i hi he
  apply hv
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, he⟩

/-- Coordinate multiplication by a vector of full support embeds a square-zero
    coordinate subspace into the kernel of the linear structure map. -/
private theorem square_zero_coordinates_finrank_le_ker {n : ℕ}
    (M : Coord n →ₗ[ℂ] Coord n) (U : Submodule ℂ (Coord n))
    (hU : ∀ x y : U, M ((x : Coord n) * (y : Coord n)) = 0) :
    Module.finrank ℂ U ≤ Module.finrank ℂ (LinearMap.ker M) := by
  classical
  obtain ⟨v, hv⟩ := exists_full_support U
  let L : U →ₗ[ℂ] Coord n :=
    { toFun := fun x => (x : Coord n) * (v : Coord n)
      map_add' := by intro x y; ext i; exact add_mul _ _ _
      map_smul' := by intro c x; ext i; exact mul_assoc _ _ _ }
  have hL : Function.Injective L := by
    intro x y h
    apply Subtype.ext
    ext i
    by_cases hi : ∃ z : U, (z : Coord n) i ≠ 0
    · exact mul_right_cancel₀ (hv i hi) (congr_fun h i)
    · have hx : (x : Coord n) i = 0 := by
        by_contra hx; exact hi ⟨x, hx⟩
      have hy : (y : Coord n) i = 0 := by
        by_contra hy; exact hi ⟨y, hy⟩
      rw [hx, hy]
  let F : U →ₗ[ℂ] LinearMap.ker M := L.codRestrict (LinearMap.ker M) (fun x => hU x v)
  exact LinearMap.finrank_le_finrank_of_injective
    (f := F) (fun x y h => hL (congr_arg Subtype.val h))

/-- The dimension bound once an evolution multiplication is written using its
    linear structure map. No commutativity assumption is needed here. -/
private theorem structure_map_embedding_lower_bound {d n : ℕ}
    (μ : Product d) (hp : perfect μ)
    (W : Submodule ℂ (Coord d)) (hW : square μ W = ⊥)
    (g : Coord d →ₗ[ℂ] Coord n) (hg : Function.Injective g)
    (M : Coord n →ₗ[ℂ] Coord n)
    (hmul : ∀ x y, g (μ x y) = M (g x * g y)) :
    d + Module.finrank ℂ W ≤ n := by
  classical
  have hspan : square μ ⊤ ≤ (LinearMap.range M).comap g := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    exact ⟨g x * g y, (hmul x y).symm⟩
  have hrange : LinearMap.range g ≤ LinearMap.range M := by
    rintro z ⟨x, rfl⟩
    have hx : x ∈ square μ ⊤ := by rw [hp]; trivial
    exact hspan hx
  have hrank : d ≤ Module.finrank ℂ (LinearMap.range M) := by
    have h := Submodule.finrank_mono hrange
    simpa [LinearMap.finrank_range_of_inj hg, Coord] using h
  have hzero : ∀ x y : W.map g,
      M ((x : Coord n) * (y : Coord n)) = 0 := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨x, hxW, rfl⟩ := hx
    obtain ⟨y, hyW, rfl⟩ := hy
    have hxy : μ x y ∈ square μ W :=
      Submodule.subset_span ⟨x, hxW, y, hyW, rfl⟩
    have heq : μ x y = 0 := by simpa [hW] using hxy
    rw [← hmul, heq, map_zero]
  have hker := square_zero_coordinates_finrank_le_ker M (W.map g) hzero
  have hdim : Module.finrank ℂ (W.map g) = Module.finrank ℂ W :=
    (Submodule.equivMapOfInjective g hg W).finrank_eq.symm
  rw [hdim] at hker
  have hnull := M.finrank_range_add_finrank_ker
  have hsum := Nat.add_le_add hrank hker
  simpa [hnull, Coord] using hsum

/-- Expansion of a natural-basis product through the linear structure map. -/
theorem natural_basis_structure_map {n : ℕ} (ν : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → ν (b i) (b j) = 0) :
    ∃ M : Coord n →ₗ[ℂ] Coord n, ∀ x y,
      b.equivFun (ν x y) = M (b.equivFun x * b.equivFun y) := by
  classical
  let e := Pi.basisFun ℂ (Fin n)
  let M := e.constr ℂ (fun i => b.equivFun (ν (b i) (b i)))
  refine ⟨M, ?_⟩
  intro x y
  have hprod : ν x y = ∑ i : Fin n,
      (b.equivFun x i * b.equivFun y i) • ν (b i) (b i) := by
    calc
      ν x y = ν (∑ i, b.equivFun x i • b i) (∑ j, b.equivFun y j • b j) := by
        rw [b.sum_equivFun, b.sum_equivFun]
      _ = ∑ i, ∑ j, (b.equivFun x i * b.equivFun y j) • ν (b i) (b j) := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
          Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp only [mul_comm]
      _ = ∑ i, (b.equivFun x i * b.equivFun y i) • ν (b i) (b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_eq_single i
        · intro j hj hji
          rw [hb i j (Ne.symm hji), smul_zero]
        · intro hi; exact (hi (Finset.mem_univ i)).elim
  rw [hprod, map_sum]
  simp [M, e]

/-- A square-zero subspace increases the required evolution embedding dimension. -/
theorem square_zero_embedding_lower_bound {d n : ℕ}
    (μ : Product d) (_hc : commutative μ) (hp : perfect μ)
    (W : Submodule ℂ (Coord d)) (hW : square μ W = ⊥)
    (he : hasEvolutionEmbedding μ n) :
    d + Module.finrank ℂ W ≤ n := by
  obtain ⟨ν, f, ⟨b, hb⟩, hf, hmul⟩ := he
  obtain ⟨M, hM⟩ := natural_basis_structure_map ν b hb
  let g : Coord d →ₗ[ℂ] Coord n := b.equivFun.toLinearMap.comp f
  apply structure_map_embedding_lower_bound μ hp W hW g
    (b.equivFun.injective.comp hf) M
  intro x y
  change b.equivFun (f (μ x y)) = M (b.equivFun (f x) * b.equivFun (f y))
  rw [hmul, hM]


#print axioms square_zero_embedding_lower_bound
end D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
