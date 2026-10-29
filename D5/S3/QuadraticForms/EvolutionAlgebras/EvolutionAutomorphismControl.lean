/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Perfect evolution products force genuine monomial multiplication automorphisms and an exact diagonal arrow equation. -/

import D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Finite.Perm
import D5.S3.FiniteGroups.SuccessorPowerAssignments

/- Escape audit for the newly public owner lemmas is unfinished: https://github.com/the-omega-institute/trureturing/issues/22095 -/

/-! The definitions below retain the full bilinear, potentially nonassociative
    multiplication-preserving LinearEquiv group. No associative algebra or graph
    automorphism surrogate is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl

open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound

def preserves {A : Type*} [AddCommGroup A] [Module ℂ A]
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (f : A ≃ₗ[ℂ] A) : Prop :=
  ∀ x y, f (μ x y) = μ (f x) (f y)

noncomputable def squareVector {n : ℕ} (μ : Product n) (b : Module.Basis (Fin n) ℂ (Coord n))
    (i : Fin n) : Coord n := μ (b i) (b i)

noncomputable def structureCoefficient {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n)) (i j : Fin n) : ℂ :=
  b.equivFun (squareVector μ b i) j

def supportRelation {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n)) (i j : Fin n) : Prop :=
  structureCoefficient μ b i j ≠ 0

theorem structure_map_injective {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n)) (hp : perfect μ)
    (M : Coord n →ₗ[ℂ] Coord n)
    (hM : ∀ x y, b.equivFun (μ x y) = M (b.equivFun x * b.equivFun y)) :
    Function.Injective M := by
  have hspan : square μ ⊤ ≤ (LinearMap.range M).comap b.equivFun.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    exact ⟨b.equivFun x * b.equivFun y, (hM x y).symm⟩
  have hs : Function.Surjective M := by
    intro z
    have hz : b.equivFun.symm z ∈ square μ ⊤ := by rw [hp]; trivial
    have hh := hspan hz
    change b.equivFun (b.equivFun.symm z) ∈ LinearMap.range M at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact LinearMap.mem_range.mp hh
  exact (LinearMap.injective_iff_surjective).mpr hs

private theorem diagonal_coordinate_map {n : ℕ} (b : Module.Basis (Fin n) ℂ (Coord n))
    (f : Coord n ≃ₗ[ℂ] Coord n) (t : Fin n → ℂ)
    (hdiag : ∀ i, f (b i) = t i • b i) (x : Coord n) (j : Fin n) :
    b.equivFun (f x) j = b.equivFun x j * t j := by
  rw [← b.sum_equivFun x]
  simp only [map_sum, map_smul, hdiag, smul_smul, smul_eq_mul]
  simp only [Finset.sum_apply, Finset.smul_sum, Pi.smul_apply, smul_eq_mul,
    b.equivFun_self]
  classical
  simp [Finset.mul_sum, Finset.sum_mul, mul_comm]

private theorem row_nonzero {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (f : Coord n ≃ₗ[ℂ] Coord n) (i : Fin n) :
    ∃ j : Fin n, b.equivFun (f (b j)) i ≠ 0 := by
  obtain ⟨x, hx⟩ := f.surjective (b i)
  by_contra h
  push Not at h
  have hcoord : b.equivFun (f x) i =
      ∑ j : Fin n, b.equivFun x j * b.equivFun (f (b j)) i := by
    calc
      b.equivFun (f x) i =
          b.equivFun (f (∑ j : Fin n, b.equivFun x j • b j)) i := by
            rw [b.sum_equivFun x]
      _ = ∑ j : Fin n, b.equivFun x j * b.equivFun (f (b j)) i := by
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hx, b.equivFun_self] at hcoord
  simp [h] at hcoord

private theorem column_nonzero {n : ℕ} (b : Module.Basis (Fin n) ℂ (Coord n))
    (f : Coord n ≃ₗ[ℂ] Coord n) (j : Fin n) :
    ∃ i : Fin n, b.equivFun (f (b j)) i ≠ 0 := by
  by_contra h
  push Not at h
  have hz : b.equivFun (f (b j)) = 0 := by
    funext i
    exact h i
  have hz' : b.equivFun (f (b j)) = b.equivFun 0 := by simpa using hz
  have : f (b j) = 0 := b.equivFun.injective hz'
  have hbzero : b j = 0 := f.injective (by simpa using this)
  exact b.linearIndependent.ne_zero j hbzero

theorem automorphism_monomial {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0)
    (hp : perfect μ) (f : Coord n ≃ₗ[ℂ] Coord n) (hf : preserves μ f) :
    ∃ σ : Equiv.Perm (Fin n), ∃ t : Fin n → ℂ,
      (∀ i, t i ≠ 0) ∧
      (∀ i j, b.equivFun (f (b j)) i = if σ i = j then t i else 0) := by
  let p : Fin n → Fin n → ℂ := fun i j => b.equivFun (f (b j)) i
  obtain ⟨M, hM⟩ := natural_basis_structure_map μ b hb
  have hMi := structure_map_injective μ b hp M hM
  have hrow_zero (i : Fin n) (j k : Fin n) (hjk : j ≠ k) :
      p i j * p i k = 0 := by
    have hprod : μ (f (b j)) (f (b k)) = 0 := by
      rw [← hf, hb j k hjk, map_zero]
    have hzero : M (b.equivFun (f (b j)) * b.equivFun (f (b k))) = 0 := by
      rw [← hM, hprod, map_zero]
    have hz : b.equivFun (f (b j)) * b.equivFun (f (b k)) = 0 :=
      hMi (by simpa using hzero)
    exact congr_fun hz i
  have hrow_at_most (i : Fin n) {j k : Fin n} (hj : p i j ≠ 0) (hk : p i k ≠ 0) :
      j = k := by
    by_contra hne
    exact (mul_ne_zero hj hk) (hrow_zero i j k hne)
  have hrow : ∀ i : Fin n, ∃! j : Fin n, p i j ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := row_nonzero μ b f i
    exact ⟨j, by simpa [p] using hj, fun k hk =>
      (hrow_at_most i (j := j) (k := k) (by simpa [p] using hj)
        (by simpa [p] using hk)).symm⟩
  let s : Fin n → Fin n := fun i => Classical.choose (hrow i)
  have hs_ne (i : Fin n) : p i (s i) ≠ 0 :=
    (Classical.choose_spec (hrow i)).1
  have hs_unique (i : Fin n) {j : Fin n} (hj : p i j ≠ 0) : j = s i :=
    (Classical.choose_spec (hrow i)).2 j hj
  have hs_surj : Function.Surjective s := by
    intro j
    obtain ⟨i, hi⟩ := column_nonzero b f j
    exact ⟨i, (hs_unique i (by simpa [p] using hi)).symm⟩
  have hs_inj : Function.Injective s := Finite.injective_iff_surjective.mpr hs_surj
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective s ⟨hs_inj, hs_surj⟩
  have hσ (i : Fin n) : σ i = s i := rfl
  let t : Fin n → ℂ := fun i => p i (s i)
  refine ⟨σ, t, ?_, ?_⟩
  · intro i
    exact hs_ne i
  · intro i j
    by_cases h : σ i = j
    · have hs : s i = j := by rw [hσ i] at h; exact h
      change p i j = if s i = j then t i else 0
      simp [t, hs]
    · have hsj : j ≠ s i := by
        intro hjs
        apply h
        rw [hσ i]
        exact hjs.symm
      have hz : p i j = 0 := by
        by_contra hpj
        exact hsj (hs_unique i hpj)
      change p i j = if s i = j then t i else 0
      rw [ite_eq_right hsj.symm]
      exact hz

private theorem monomial_basis_image {n : ℕ} (b : Module.Basis (Fin n) ℂ (Coord n))
    (f : Coord n ≃ₗ[ℂ] Coord n) (σ : Equiv.Perm (Fin n)) (t : Fin n → ℂ)
    (ht : ∀ i, t i ≠ 0)
    (hm : ∀ i j, b.equivFun (f (b j)) i = if σ i = j then t i else 0) :
    ∀ j, f (b j) = t (σ.symm j) • b (σ.symm j) := by
  intro j
  apply b.equivFun.injective
  funext i
  rw [hm]
  by_cases h : σ i = j
  · have hi : i = σ.symm j := by
      apply σ.injective
      simpa using h
    subst i
    simp [b.equivFun_self]
  · have hi : i ≠ σ.symm j := by
      intro hi
      apply h
      simpa [hi]
    simp [b.equivFun_self, h, hi]

private theorem permuted_coordinate_map {n : ℕ} (b : Module.Basis (Fin n) ℂ (Coord n))
    (f : Coord n ≃ₗ[ℂ] Coord n) (σ : Equiv.Perm (Fin n)) (t : Fin n → ℂ)
    (hm : ∀ j, f (b j) = t (σ.symm j) • b (σ.symm j))
    (x : Coord n) (r : Fin n) :
    b.equivFun (f x) r = b.equivFun x (σ r) * t r := by
  calc
    b.equivFun (f x) r =
        b.equivFun (f (∑ j : Fin n, b.equivFun x j • b j)) r := by
          rw [b.sum_equivFun x]
    _ = ∑ j : Fin n, b.equivFun x j * b.equivFun (f (b j)) r := by
          simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = b.equivFun x (σ r) * t r := by
          classical
          simp only [hm, map_smul, Pi.smul_apply, smul_eq_mul, b.equivFun_self]
          have hh (j : Fin n) : (σ.symm j = r) ↔ j = σ r := by
            constructor
            · intro h
              rw [← h]
              simp
            · intro h
              rw [h]
              simp
          simp_rw [hh]
          simp

theorem automorphism_support_perm {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0)
    (hp : perfect μ) (f : Coord n ≃ₗ[ℂ] Coord n) (hf : preserves μ f) :
    ∃ σ : Equiv.Perm (Fin n), ∃ t : Fin n → ℂ,
      (∀ i, t i ≠ 0) ∧
      (∀ i j, b.equivFun (f (b j)) i = if σ i = j then t i else 0) ∧
      (∀ i j, supportRelation μ b i j ↔
        supportRelation μ b (σ.symm i) (σ.symm j)) := by
  obtain ⟨σ, t, ht, hm⟩ := automorphism_monomial μ b hb hp f hf
  have hbi : ∀ j, f (b j) = t (σ.symm j) • b (σ.symm j) :=
    monomial_basis_image b f σ t ht hm
  refine ⟨σ, t, ht, hm, ?_⟩
  intro i j
  let r := σ.symm j
  have hsquare := hf (b i) (b i)
  have hcoord := congr_fun (congrArg b.equivFun hsquare) r
  have hleft : b.equivFun (f (squareVector μ b i)) r =
      structureCoefficient μ b i j * t r := by
    rw [permuted_coordinate_map b f σ t hbi (squareVector μ b i) r]
    simp [r, structureCoefficient]
  have hright : b.equivFun (μ (f (b i)) (f (b i))) r =
      (t (σ.symm i) ^ 2) * structureCoefficient μ b (σ.symm i) r := by
    rw [hbi i]
    simp [structureCoefficient, squareVector, map_smul, smul_eq_mul, mul_assoc,
      mul_comm, mul_left_comm]
    ring
  change b.equivFun (f (squareVector μ b i)) r =
    b.equivFun (μ (f (b i)) (f (b i))) r at hcoord
  rw [hleft, hright] at hcoord
  constructor
  · intro h
    have hn : t r ≠ 0 := ht r
    have hprod : (t (σ.symm i) ^ 2) * structureCoefficient μ b (σ.symm i) r ≠ 0 := by
      rw [← hcoord]
      exact mul_ne_zero h hn
    exact (mul_ne_zero_iff.mp hprod).2
  · intro h
    have hn : t r ≠ 0 := ht r
    have hprod : structureCoefficient μ b i j * t r ≠ 0 := by
      rw [hcoord]
      exact mul_ne_zero (pow_ne_zero 2 (ht _)) h
    exact (mul_ne_zero_iff.mp hprod).1

theorem diagonal_arrow_equation {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0)
    (f : Coord n ≃ₗ[ℂ] Coord n) (hf : preserves μ f)
    (t : Fin n → ℂ) (hdiag : ∀ i, f (b i) = t i • b i) :
    ∀ i j, structureCoefficient μ b i j ≠ 0 → t j = t i ^ 2 := by
  intro i j hij
  have hsquare := hf (b i) (b i)
  have hcoord := congr_fun (congrArg b.equivFun hsquare) j
  have hleft : b.equivFun (f (squareVector μ b i)) j =
      structureCoefficient μ b i j * t j :=
    diagonal_coordinate_map b f t hdiag (squareVector μ b i) j
  have hright : b.equivFun (μ (t i • b i) (t i • b i)) j =
      (t i ^ 2) * structureCoefficient μ b i j := by
    simp [structureCoefficient, squareVector, map_smul, smul_eq_mul, mul_assoc,
      mul_comm, mul_left_comm]
    ring
  change b.equivFun (f (squareVector μ b i)) j =
    b.equivFun (μ (f (b i)) (f (b i))) j at hcoord
  rw [hleft, hdiag i, hright] at hcoord
  exact mul_left_cancel₀ hij (by simpa [mul_comm] using hcoord)

/-- The full group of complex linear multiplication automorphisms. -/
def Aut {A : Type*} [AddCommGroup A] [Module ℂ A]
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) : Subgroup (A ≃ₗ[ℂ] A) where
  carrier := {f | preserves μ f}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro f g hf hg x y
    change f (g (μ x y)) = μ (f (g x)) (f (g y))
    rw [hg, hf]
  inv_mem' := by
    intro f hf x y
    apply f.injective
    change f (f.symm (μ x y)) = f (μ (f.symm x) (f.symm y))
    rw [hf]
    simp only [LinearEquiv.apply_symm_apply]

private theorem basis_smul_index_eq {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (Coord n)) {a c : ℂ} {i j : Fin n}
    (ha : a ≠ 0) (h : a • b i = c • b j) : i = j := by
  by_contra hij
  have hh := congr_fun (congrArg b.equivFun h) i
  simp [hij, Ne.symm hij] at hh
  exact ha hh

structure MonomialData {n : ℕ} (μ : Product n) (b : Module.Basis (Fin n) ℂ (Coord n))
    (f : Coord n ≃ₗ[ℂ] Coord n) where
  perm : Equiv.Perm (Fin n)
  scalar : Fin n → ℂ
  nonzero : ∀ i, scalar i ≠ 0
  image : ∀ i, f (b i) = scalar i • b (perm i)
  support : ∀ i j, supportRelation μ b i j ↔
    supportRelation μ b (perm i) (perm j)

noncomputable def monomialData {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0)
    (hp : perfect μ) (f : Aut μ) : MonomialData μ b f.val := by
  let h := automorphism_support_perm μ b hb hp f.val f.property
  let σ := Classical.choose h
  let t := Classical.choose (Classical.choose_spec h)
  have ht := Classical.choose_spec (Classical.choose_spec h)
  exact ⟨σ.symm, fun i => t (σ.symm i), fun i => ht.1 _,
    monomial_basis_image b f.val σ t ht.1 ht.2.1, ht.2.2⟩

/-- The unique support permutation of each actual algebra automorphism. -/
noncomputable def rho {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0)
    (hp : perfect μ) : Aut μ →* Equiv.Perm (Fin n) where
  toFun f := (monomialData μ b hb hp f).perm
  map_one' := by
    apply Equiv.ext
    intro i
    apply basis_smul_index_eq b (c := 1) ((monomialData μ b hb hp 1).nonzero i)
    simpa using ((monomialData μ b hb hp 1).image i).symm
  map_mul' f g := by
    apply Equiv.ext
    intro i
    let df := monomialData μ b hb hp f
    let dg := monomialData μ b hb hp g
    let dfg := monomialData μ b hb hp (f * g)
    apply basis_smul_index_eq b (dfg.nonzero i)
    calc
      dfg.scalar i • b (dfg.perm i) = (f.val * g.val) (b i) := (dfg.image i).symm
      _ = f.val (g.val (b i)) := rfl
      _ = (dg.scalar i * df.scalar (dg.perm i)) • b (df.perm (dg.perm i)) := by
        rw [dg.image, map_smul, df.image, smul_smul]

/-- Its kernel consists precisely of the diagonal maps satisfying every arrow equation. -/
theorem rho_kernel_iff {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0)
    (hp : perfect μ) (f : Aut μ) :
    rho μ b hb hp f = 1 ↔ ∃ t : Fin n → ℂ,
      (∀ i, t i ≠ 0) ∧ (∀ i, f.val (b i) = t i • b i) ∧
      (∀ i j, supportRelation μ b i j → t j = t i ^ 2) := by
  constructor
  · intro h
    let d := monomialData μ b hb hp f
    have hd (i : Fin n) : d.perm i = i := congrArg (fun σ => σ i) h
    have hi (i : Fin n) : f.val (b i) = d.scalar i • b i := by rw [d.image, hd]
    exact ⟨d.scalar, d.nonzero, hi, diagonal_arrow_equation μ b hb f.val f.property _ hi⟩
  · rintro ⟨t, ht, hi, harrow⟩
    apply Equiv.ext
    intro i
    let d := monomialData μ b hb hp f
    apply basis_smul_index_eq b (d.nonzero i)
    exact (d.image i).symm.trans (hi i)

/-- The arrow equations are sufficient as well as necessary for an invertible diagonal map. -/
theorem preserves_diagonal_iff {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0)
    (f : Coord n ≃ₗ[ℂ] Coord n) (t : Fin n → ℂ)
    (hdiag : ∀ i, f (b i) = t i • b i) :
    preserves μ f ↔ ∀ i j, supportRelation μ b i j → t j = t i ^ 2 := by
  constructor
  · intro hf
    exact diagonal_arrow_equation μ b hb f hf t hdiag
  · intro ht
    have hsquare (i : Fin n) : f (μ (b i) (b i)) = μ (f (b i)) (f (b i)) := by
      apply b.equivFun.injective
      funext j
      rw [diagonal_coordinate_map b f t hdiag]
      rw [hdiag i]
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hij : supportRelation μ b i j
      · change structureCoefficient μ b i j * t j =
          t i * (t i * structureCoefficient μ b i j)
        rw [ht i j hij]
        ring
      · have hz : structureCoefficient μ b i j = 0 := not_not.mp hij
        change structureCoefficient μ b i j * t j =
          t i * (t i * structureCoefficient μ b i j)
        rw [hz]
        simp
    have heq : μ.compr₂ f.toLinearMap = μ.compl₁₂ f.toLinearMap f.toLinearMap := by
      apply b.ext
      intro i
      apply b.ext
      intro j
      change f (μ (b i) (b j)) = μ (f (b i)) (f (b j))
      by_cases hij : i = j
      · subst j
        exact hsquare i
      · rw [hb i j hij, map_zero, hdiag i, hdiag j]
        simp only [map_smul, LinearMap.smul_apply, hb i j hij, smul_zero]
    intro x y
    exact congrArg (fun F : Product n => F x y) heq

/-- Perfectness excludes zero columns and zero rows of the structure coefficients. -/
theorem support_positive_degrees {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ) :
    (∀ i, ∃ j, supportRelation μ b i j) ∧
    (∀ j, ∃ i, supportRelation μ b i j) := by
  classical
  obtain ⟨M, hM⟩ := natural_basis_structure_map μ b hb
  have hMi := structure_map_injective μ b hp M hM
  constructor
  · intro i
    by_contra h
    change ¬ ∃ j, structureCoefficient μ b i j ≠ 0 at h
    push Not at h
    have hz : M (b.equivFun (b i) * b.equivFun (b i)) = 0 := by
      rw [← hM]
      funext j
      exact h j
    have he : b.equivFun (b i) * b.equivFun (b i) = 0 := hMi (by simpa using hz)
    have hh := congr_fun he i
    simp at hh
  · intro j
    by_contra h
    change ¬ ∃ i, structureCoefficient μ b i j ≠ 0 at h
    push Not at h
    have hz : (LinearMap.proj j).comp M = 0 := by
      apply (Pi.basisFun ℂ (Fin n)).ext
      intro i
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.zero_apply,
        Pi.basisFun_apply]
      change M (Pi.single i 1) j = 0
      have he : b.equivFun (b i) * b.equivFun (b i) = Pi.single i 1 := by
        funext k
        simp [Pi.single_apply, Finsupp.single_apply, eq_comm]
      rw [← he, ← hM]
      exact h i
    obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hMi (Pi.single j 1)
    have hh := LinearMap.congr_fun hz x
    change M x j = 0 at hh
    rw [hx] at hh
    simp at hh

noncomputable def graphHom {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ) :
    Aut μ →* D5.S3.FiniteGroups.SuccessorQuotient.relationAut (supportRelation μ b) where
  toFun f := ⟨rho μ b hb hp f, fun i j => ((monomialData μ b hb hp f).support i j).symm⟩
  map_one' := Subtype.ext (map_one (rho μ b hb hp))
  map_mul' f g := Subtype.ext (map_mul (rho μ b hb hp) f g)

/-- Every actual diagonal-kernel automorphism descends to the canonical support quotient. -/
theorem kernel_assignment_descent {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ)
    (f : Aut μ) (hk : rho μ b hb hp f = 1) :
    ∃ v : D5.S3.FiniteGroups.SuccessorQuotient.QuotientAssignments
        (supportRelation μ b) (fun z : ℂ => z ^ 2)
        (support_positive_degrees μ b hb hp).1,
      ∀ i, f.val (b i) =
        v.val (D5.S3.FiniteGroups.SuccessorQuotient.project (supportRelation μ b) i) • b i := by
  obtain ⟨t, ht, hi, harrow⟩ := (rho_kernel_iff μ b hb hp f).mp hk
  let a : D5.S3.FiniteGroups.SuccessorQuotient.Assignments
      (supportRelation μ b) (fun z : ℂ => z ^ 2) := ⟨t, harrow⟩
  let v := D5.S3.FiniteGroups.SuccessorQuotient.assignmentEquiv
    (supportRelation μ b) (fun z : ℂ => z ^ 2)
    (support_positive_degrees μ b hb hp).1 a
  exact ⟨v, hi⟩


open D5.S3.FiniteGroups.SuccessorQuotient

/-- Coordinate multiplication by nonzero units, transported along the given basis. -/
noncomputable def diagonalEquiv {n : ℕ} (b : Module.Basis (Fin n) ℂ (Coord n))
    (t : Fin n → ℂˣ) : Coord n ≃ₗ[ℂ] Coord n :=
  b.equivFun.trans ((LinearEquiv.piCongrRight fun i =>
    LinearEquiv.smulOfUnit (M := ℂ) (t i)).trans b.equivFun.symm)

private theorem diagonalEquiv_basis {n : ℕ} (b : Module.Basis (Fin n) ℂ (Coord n))
    (t : Fin n → ℂˣ) (i : Fin n) :
    diagonalEquiv b t (b i) = (t i : ℂ) • b i := by
  classical
  apply b.equivFun.injective
  funext j
  simp [diagonalEquiv, LinearEquiv.piCongrRight_apply, LinearEquiv.smulOfUnit,
    b.equivFun_self, Finsupp.single_apply, Units.smul_def]

noncomputable def kernelAssignment {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ)
    (f : (rho μ b hb hp).ker) :
    Assignments (supportRelation μ b) (fun z : ℂˣ => z ^ 2) := by
  let h := kernel_assignment_descent μ b hb hp f.val f.property
  let v := Classical.choose h
  have hi := Classical.choose_spec h
  have hn (i : Fin n) : v.val (project (supportRelation μ b) i) ≠ 0 := by
    intro hz
    have hh := hi i
    rw [hz, zero_smul] at hh
    exact b.linearIndependent.ne_zero i (f.val.val.injective (by simpa using hh))
  refine ⟨fun i => Units.mk0 (v.val (project (supportRelation μ b) i)) (hn i), ?_⟩
  intro i j hij
  apply Units.ext
  change v.val (project (supportRelation μ b) j) =
    v.val (project (supportRelation μ b) i) ^ 2
  rw [← successor_project (supportRelation μ b) (support_positive_degrees μ b hb hp).1 hij]
  exact v.property _

private theorem kernel_basis_image {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ)
    (f : (rho μ b hb hp).ker) (i : Fin n) :
    f.val.val (b i) = ((kernelAssignment μ b hb hp f).val i : ℂ) • b i := by
  exact (Classical.choose_spec (kernel_assignment_descent μ b hb hp f.val f.property)) i

noncomputable def assignmentAutomorphism {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ)
    (t : Assignments (supportRelation μ b) (fun z : ℂˣ => z ^ 2)) :
    (rho μ b hb hp).ker := by
  let f := diagonalEquiv b t.val
  have hi (i : Fin n) : f (b i) = (t.val i : ℂ) • b i := diagonalEquiv_basis b t.val i
  have ht (i j : Fin n) (hij : supportRelation μ b i j) :
      (t.val j : ℂ) = (t.val i : ℂ) ^ 2 := congrArg Units.val (t.property i j hij)
  have hf : preserves μ f := (preserves_diagonal_iff μ b hb f _ hi).mpr ht
  exact ⟨⟨f, hf⟩, (rho_kernel_iff μ b hb hp ⟨f, hf⟩).mpr
    ⟨fun i => (t.val i : ℂ), fun i => (t.val i).ne_zero, hi, ht⟩⟩

/-- The entire permutation kernel is exactly the arrow-equation unit assignments. -/
noncomputable def kernelAssignmentEquiv {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ) :
    (rho μ b hb hp).ker ≃ Assignments (supportRelation μ b) (fun z : ℂˣ => z ^ 2) where
  toFun := kernelAssignment μ b hb hp
  invFun := assignmentAutomorphism μ b hb hp
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    change diagonalEquiv b (kernelAssignment μ b hb hp f).val (b i) = f.val.val (b i)
    rw [diagonalEquiv_basis, kernel_basis_image]
  right_inv t := by
    apply Subtype.ext
    funext i
    apply Units.ext
    have hh := kernel_basis_image μ b hb hp (assignmentAutomorphism μ b hb hp t) i
    change diagonalEquiv b t.val (b i) = _ at hh
    rw [diagonalEquiv_basis] at hh
    have hc := congr_fun (congrArg b.equivFun hh) i
    simpa using hc.symm

/-- The full diagonal kernel has exactly one independent root factor per quotient cycle. -/
theorem diagonal_kernel_card {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ) :
    Nat.card (rho μ b hb hp).ker =
      D5.S3.FiniteGroups.SuccessorPowerAssignments.cycleWeight
        (beta (supportRelation μ b) (support_positive_degrees μ b hb hp).1
          (support_positive_degrees μ b hb hp).2) := by
  rw [Nat.card_congr (kernelAssignmentEquiv μ b hb hp),
    Nat.card_congr (assignmentEquiv (supportRelation μ b) (fun z : ℂˣ => z ^ 2)
      (support_positive_degrees μ b hb hp).1)]
  exact D5.S3.FiniteGroups.SuccessorPowerAssignments.square_assignments_weight_card
    (beta (supportRelation μ b) (support_positive_degrees μ b hb hp).1
      (support_positive_degrees μ b hb hp).2)

/-- Actual finiteness of the full multiplication-preserving linear group. -/
theorem automorphism_finite {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ) :
    Finite (Aut μ) := by
  haveI : Finite (Assignments (supportRelation μ b) (fun z : ℂˣ => z ^ 2)) :=
    D5.S3.FiniteGroups.SuccessorPowerAssignments.relation_square_assignments_finite
      (supportRelation μ b) (support_positive_degrees μ b hb hp).1
      (support_positive_degrees μ b hb hp).2
  haveI : Finite (rho μ b hb hp).ker :=
    Finite.of_injective (kernelAssignmentEquiv μ b hb hp) (Equiv.injective _)
  exact (MonoidHom.finite_iff_finite_ker_range (rho μ b hb hp)).mpr
    ⟨inferInstance, inferInstance⟩

/-- The diagonal and block-action controls both bound the actual algebra group. -/
theorem automorphism_joint_control {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ) :
    Nat.card (Aut μ) ≤
      Nat.card (Assignments (supportRelation μ b) (fun z : ℂˣ => z ^ 2)) *
      (Nat.card (Subgroup.centralizer
        ({(beta (supportRelation μ b) (support_positive_degrees μ b hb hp).1
          (support_positive_degrees μ b hb hp).2)} :
            Set (Equiv.Perm (Blocks (supportRelation μ b))))) *
        Nat.card (∀ q : Blocks (supportRelation μ b),
          Equiv.Perm (Fiber (supportRelation μ b) q))) := by
  haveI : Finite (Aut μ) := automorphism_finite μ b hb hp
  have hk : Nat.card (rho μ b hb hp).ker =
      Nat.card (Assignments (supportRelation μ b) (fun z : ℂˣ => z ^ 2)) :=
    Nat.card_congr (kernelAssignmentEquiv μ b hb hp)
  have hr : Nat.card (rho μ b hb hp).range ≤ Nat.card (relationAut (supportRelation μ b)) := by
    let F : (rho μ b hb hp).range → relationAut (supportRelation μ b) :=
      fun σ => ⟨σ.val, by
        obtain ⟨f, hf⟩ := σ.property
        rw [← hf]
        exact (graphHom μ b hb hp f).property⟩
    exact Nat.card_le_card_of_injective F (fun x y h =>
      Subtype.ext (congrArg (fun z : relationAut (supportRelation μ b) => z.val) h))
  rw [← Subgroup.card_ker_mul_card_range (rho μ b hb hp), hk]
  exact Nat.mul_le_mul_left _ (hr.trans (relation_aut_joint_bound
    (supportRelation μ b) (support_positive_degrees μ b hb hp).1
    (support_positive_degrees μ b hb hp).2))


/-- The actual finite algebra automorphism group is bounded by successor-cycle roots,
its quotient centralizer, and the factorials of the actual quotient blocks. -/
theorem automorphism_quotient_bound {n : ℕ} (μ : Product n)
    (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ) :
    let R := supportRelation μ b
    let β := beta R (support_positive_degrees μ b hb hp).1
      (support_positive_degrees μ b hb hp).2
    letI := Fintype.ofFinite (Blocks R)
    Nat.card (Aut μ) ≤
      D5.S3.FiniteGroups.SuccessorPowerAssignments.cycleWeight β *
      Nat.card (Subgroup.centralizer ({β} : Set (Equiv.Perm (Blocks R)))) *
      ∏ q : Blocks R, (Nat.card (Fiber R q)).factorial := by
  classical
  dsimp only
  let R := supportRelation μ b
  let β := beta R (support_positive_degrees μ b hb hp).1
    (support_positive_degrees μ b hb hp).2
  letI := Fintype.ofFinite (Blocks R)
  have hd : Nat.card (Assignments R (fun z : ℂˣ => z ^ 2)) =
      D5.S3.FiniteGroups.SuccessorPowerAssignments.cycleWeight β :=
    (Nat.card_congr (kernelAssignmentEquiv μ b hb hp)).symm.trans
      (diagonal_kernel_card μ b hb hp)
  have hblocks : Nat.card (∀ q : Blocks R, Equiv.Perm (Fiber R q)) =
      ∏ q : Blocks R, (Nat.card (Fiber R q)).factorial := by
    simp only [Nat.card_pi, Nat.card_perm]
  have h := automorphism_joint_control μ b hb hp
  change Nat.card (Aut μ) ≤ Nat.card (Assignments R (fun z : ℂˣ => z ^ 2)) *
    (Nat.card (Subgroup.centralizer ({β} : Set (Equiv.Perm (Blocks R)))) *
      Nat.card (∀ q : Blocks R, Equiv.Perm (Fiber R q))) at h
  rw [hblocks] at h
  rw [hd] at h
  simpa only [Nat.mul_assoc] using h

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl

