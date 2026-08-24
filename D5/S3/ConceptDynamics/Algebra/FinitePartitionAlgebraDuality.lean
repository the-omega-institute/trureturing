/- GID: D5/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Algebra/FinitePartitionAlgebraDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Partition functions recover every relation without finiteness, while finite unital
     pointwise algebras recover exactly their indistinguishability blocks, including all six
     degenerate cases;
     named counterexamples show finiteness and all three closures are necessary. -/
/- Library-search audit trail (2026-08-25):
   * Repository search for `PullbackAlgebra`, `SemanticClosure`, and
     `RelationInvariantReadouts` found the Prop-valued factorization family in
     `DeterministicInterfaceEquivalence` and the definition-family Galois connection in
     `DefinitionKernelGalois`; neither carries the real subalgebra structure needed here.
   * Pinned Mathlib searches covered `Setoid.ker`, `Setoid.classes`, `Subalgebra`,
     `Algebra.adjoin`, `Finset.indicator`, `Function.FactorsThrough`,
     `Finset.sum_ite_eq`, and finite-dimensional commutative idempotent decompositions.
   * The available Lean skill has no LSP LeanSearch or Loogle endpoint. Its local
     `smart_search.sh` returned no theorem for finite function-subalgebra decomposition or
     finite products of fields. Direct source search likewise found no exact theorem.
   * The proof reuses `Subalgebra.prod_mem`, `Subalgebra.sum_mem`, `Quotient.fintype`,
     `Quotient.eq_iff_equiv`, `Finset.prod_eq_zero`, and pointwise big-operator lemmas.
   * `Algebra.adjoin`, `Finset.indicator`, `Function.FactorsThrough`, `Setoid.classes`, and
     the searched idempotent-decomposition material were adjacent but not used.
-/

import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Quotient
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Algebra.FinitePartitionAlgebraDuality

open scoped BigOperators

/-- Functions that are constant on a supplied binary relation. -/
def RelationInvariantFunctions {X : Type*} (relation : X → X → Prop) : Set (X → ℝ) :=
  {f | ∀ ⦃x y⦄, relation x y → f x = f y}

/-- Two points are indistinguishable by a family of real-valued functions. -/
def Indistinguishable {X : Type*} (A : Set (X → ℝ)) (x y : X) : Prop :=
  ∀ f ∈ A, f x = f y

/-- Indistinguishability by any function family is an equivalence relation. -/
def indistinguishabilitySetoid {X : Type*} (A : Set (X → ℝ)) : Setoid X where
  r := Indistinguishable A
  iseqv :=
    ⟨fun _ _ _ ↦ rfl,
      fun h f hf ↦ (h f hf).symm,
      fun hxy hyz f hf ↦ (hxy f hf).trans (hyz f hf)⟩

/-- The real partition algebra of functions constant on the classes of `R`. -/
def partitionAlgebra {X : Type*} (R : Setoid X) : Subalgebra ℝ (X → ℝ) where
  carrier := RelationInvariantFunctions R
  add_mem' {f} {g} hf hg left right hxy := by
    change f left + g left = f right + g right
    rw [hf hxy, hg hxy]
  mul_mem' {f} {g} hf hg left right hxy := by
    change f left * g left = f right * g right
    rw [hf hxy, hg hxy]
  algebraMap_mem' _ _ _ _ := rfl

/-- The family contains every constant real-valued function. -/
def ContainsConstants {X : Type*} (A : Set (X → ℝ)) : Prop :=
  ∀ c : ℝ, (fun _ ↦ c) ∈ A

/-- The family is closed under arbitrary binary real linear combinations. -/
def ClosedUnderLinearCombinations {X : Type*} (A : Set (X → ℝ)) : Prop :=
  ∀ (a b : ℝ) ⦃f g : X → ℝ⦄, f ∈ A → g ∈ A →
    (fun x ↦ a * f x + b * g x) ∈ A

/-- The family is closed under pointwise multiplication. -/
def ClosedUnderPointwiseMultiplication {X : Type*} (A : Set (X → ℝ)) : Prop :=
  ∀ ⦃f g : X → ℝ⦄, f ∈ A → g ∈ A → (fun x ↦ f x * g x) ∈ A

/-- Recovering a relation from its partition functions uses neither finiteness nor algebraic
closure. The indicator of one equivalence class separates every point outside that class. -/
theorem indistinguishability_partitionAlgebra {X : Type*} (R : Setoid X) :
    Indistinguishable (partitionAlgebra R : Set (X → ℝ)) = R := by
  classical
  funext x y
  apply propext
  constructor
  · intro hall
    by_contra hxy
    let indicator : X → ℝ := fun z ↦ if R x z then 1 else 0
    have hindicator : indicator ∈ partitionAlgebra R := by
      intro left right hlr
      by_cases hxl : R x left
      · have hxr : R x right := R.trans hxl hlr
        simp only [indicator, if_pos hxl, if_pos hxr]
      · have hxr : ¬R x right := by
          intro hxr
          exact hxl (R.trans hxr (R.symm hlr))
        simp only [indicator, if_neg hxl, if_neg hxr]
    have hequal := hall indicator hindicator
    simp only [indicator, if_pos (R.refl x), if_neg hxy] at hequal
    norm_num at hequal
  · intro hxy f hf
    exact hf hxy
#print axioms indistinguishability_partitionAlgebra

open scoped Classical in
private theorem blockIndicator_mem {X : Type*} [Fintype X]
    (A : Subalgebra ℝ (X → ℝ)) (x : X) :
    (fun z ↦ if Indistinguishable (A : Set (X → ℝ)) x z then 1 else 0) ∈ A := by
  classical
  have separator_exists (y : X)
      (hxy : ¬Indistinguishable (A : Set (X → ℝ)) x y) :
      ∃ g : X → ℝ, g ∈ A ∧ g x ≠ g y := by
    simp only [Indistinguishable] at hxy
    push Not at hxy
    exact hxy
  let separator : X → (X → ℝ) := fun y ↦
    if hxy : Indistinguishable (A : Set (X → ℝ)) x y then 0
    else Classical.choose (separator_exists y hxy)
  have separator_mem (y : X)
      (hxy : ¬Indistinguishable (A : Set (X → ℝ)) x y) : separator y ∈ A := by
    rw [show separator y = Classical.choose (separator_exists y hxy) by simp [separator, hxy]]
    exact (Classical.choose_spec (separator_exists y hxy)).1
  have separator_ne (y : X)
      (hxy : ¬Indistinguishable (A : Set (X → ℝ)) x y) :
      separator y x ≠ separator y y := by
    rw [show separator y = Classical.choose (separator_exists y hxy) by simp [separator, hxy]]
    exact (Classical.choose_spec (separator_exists y hxy)).2
  let normalized : X → (X → ℝ) := fun y ↦
    (separator y x - separator y y)⁻¹ • (separator y - fun _ ↦ separator y y)
  have normalized_mem (y : X)
      (hxy : ¬Indistinguishable (A : Set (X → ℝ)) x y) : normalized y ∈ A := by
    apply A.smul_mem
    apply A.sub_mem (separator_mem y hxy)
    have hconstant :
        (algebraMap ℝ (X → ℝ)) (separator y y) = fun _ ↦ separator y y := by
      funext z
      simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← hconstant]
    exact A.algebraMap_mem (separator y y)
  have normalized_at_x (y : X)
      (hxy : ¬Indistinguishable (A : Set (X → ℝ)) x y) : normalized y x = 1 := by
    simp only [normalized, Pi.smul_apply, Pi.sub_apply]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (separator_ne y hxy))
  have normalized_at_y (y : X) : normalized y y = 0 := by
    simp only [normalized, Pi.smul_apply, Pi.sub_apply, sub_self, smul_zero]
  let indicator : X → ℝ :=
    ∏ y ∈ Finset.univ.filter
      (fun y ↦ ¬Indistinguishable (A : Set (X → ℝ)) x y), normalized y
  have indicator_mem : indicator ∈ A := by
    apply A.prod_mem
    intro y hy
    exact normalized_mem y (Finset.mem_filter.mp hy).2
  have indicator_eq :
      indicator = fun z ↦
        if Indistinguishable (A : Set (X → ℝ)) x z then 1 else 0 := by
    funext z
    simp only [indicator, Finset.prod_apply]
    by_cases hxz : Indistinguishable (A : Set (X → ℝ)) x z
    · rw [if_pos hxz]
      apply Finset.prod_eq_one
      intro y hy
      have hxy := (Finset.mem_filter.mp hy).2
      rw [← normalized_at_x y hxy]
      exact (hxz (normalized y) (normalized_mem y hxy)).symm
    · rw [if_neg hxz]
      exact Finset.prod_eq_zero
        (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hxz⟩) (normalized_at_y z)
  rw [← indicator_eq]
  exact indicator_mem

/-- On a finite type, a real subalgebra of pointwise functions is exactly the partition algebra
of its indistinguishability relation. `Subalgebra` packages constants, real linear combinations,
and pointwise multiplication; no separate decidable-equality hypothesis is needed. -/
theorem partitionAlgebra_indistinguishability {X : Type*} [Fintype X]
    (A : Subalgebra ℝ (X → ℝ)) :
    partitionAlgebra (indistinguishabilitySetoid (A : Set (X → ℝ))) = A := by
  classical
  let R := indistinguishabilitySetoid (A : Set (X → ℝ))
  apply le_antisymm
  · intro f hf
    letI : Fintype (Quotient R) := Quotient.fintype R
    let reconstructed : X → ℝ :=
      ∑ block : Quotient R,
        f block.out •
          (fun z ↦ if Indistinguishable (A : Set (X → ℝ)) block.out z then 1 else 0)
    have reconstructed_mem : reconstructed ∈ A := by
      apply A.sum_mem
      intro block _
      apply A.smul_mem
      exact blockIndicator_mem A block.out
    have reconstructed_eq : reconstructed = f := by
      funext z
      simp only [reconstructed, Finset.sum_apply, Pi.smul_apply]
      have relation_iff (block : Quotient R) :
          Indistinguishable (A : Set (X → ℝ)) block.out z ↔
            block = Quotient.mk'' z := by
        change R block.out z ↔ block = Quotient.mk'' z
        constructor
        · intro hrelation
          rw [← Quotient.out_eq block]
          exact Quotient.sound hrelation
        · intro hblock
          apply Quotient.exact
          exact (Quotient.out_eq block).trans hblock
      simp_rw [relation_iff]
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      exact hf (@Quotient.mk_out X R z)
    rw [← reconstructed_eq]
    exact reconstructed_mem
  · intro f hf _ _ hxy
    exact hxy f hf
#print axioms partitionAlgebra_indistinguishability

/-- Eventually constant real sequences form a unital pointwise subalgebra. -/
def eventuallyConstantAlgebra : Subalgebra ℝ (ℕ → ℝ) where
  carrier := {f | ∃ N c, ∀ n, N ≤ n → f n = c}
  add_mem' := by
    rintro f g ⟨N, c, hf⟩ ⟨M, d, hg⟩
    refine ⟨max N M, c + d, fun n hn ↦ ?_⟩
    change f n + g n = c + d
    rw [hf n (le_trans (le_max_left N M) hn), hg n (le_trans (le_max_right N M) hn)]
  mul_mem' := by
    rintro f g ⟨N, c, hf⟩ ⟨M, d, hg⟩
    refine ⟨max N M, c * d, fun n hn ↦ ?_⟩
    change f n * g n = c * d
    rw [hf n (le_trans (le_max_left N M) hn), hg n (le_trans (le_max_right N M) hn)]
  algebraMap_mem' c := ⟨0, c, fun _ _ ↦ rfl⟩

/-- Finiteness is necessary: eventually constant sequences separate all natural numbers, but
the identity sequence is constant on their indistinguishability classes and is not eventually
constant. -/
theorem finiteness_is_necessary :
    partitionAlgebra
      (indistinguishabilitySetoid (eventuallyConstantAlgebra : Set (ℕ → ℝ))) ≠
        eventuallyConstantAlgebra := by
  intro hequal
  have relation_eq ⦃x y : ℕ⦄
      (hxy : Indistinguishable (eventuallyConstantAlgebra : Set (ℕ → ℝ)) x y) : x = y := by
    by_contra hne
    let delta : ℕ → ℝ := fun n ↦ if n = x then 1 else 0
    have delta_mem : delta ∈ eventuallyConstantAlgebra := by
      refine ⟨x + 1, 0, fun n hn ↦ ?_⟩
      have hnx : n ≠ x := by omega
      simp only [delta, if_neg hnx]
    have := hxy delta delta_mem
    simp only [delta, if_pos rfl, if_neg (Ne.symm hne)] at this
    norm_num at this
  have identity_mem : (fun n : ℕ ↦ (n : ℝ)) ∈
      partitionAlgebra
        (indistinguishabilitySetoid (eventuallyConstantAlgebra : Set (ℕ → ℝ))) := by
    intro x y hxy
    rw [relation_eq hxy]
  rw [hequal] at identity_mem
  rcases identity_mem with ⟨N, c, hc⟩
  have hN := hc N le_rfl
  have hNs := hc (N + 1) (Nat.le_add_right N 1)
  norm_num at hNs
  linarith
#print axioms finiteness_is_necessary

/-- Constants are necessary: the zero family is closed under linear combinations and products,
but its indistinguishability relation admits every constant function. -/
theorem constants_are_necessary :
    ∃ A : Set (Bool → ℝ),
      ClosedUnderLinearCombinations A ∧
      ClosedUnderPointwiseMultiplication A ∧
      RelationInvariantFunctions (Indistinguishable A) ≠ A := by
  refine ⟨{0}, ?_, ?_, ?_⟩
  · rintro a b f g (rfl : f = 0) (rfl : g = 0)
    simp only [Set.mem_singleton_iff]
    funext x
    simp
  · rintro f g (rfl : f = 0) (rfl : g = 0)
    simp only [Set.mem_singleton_iff]
    funext x
    simp
  · intro hequal
    have hone : (fun _ : Bool ↦ (1 : ℝ)) ∈
        RelationInvariantFunctions (Indistinguishable ({0} : Set (Bool → ℝ))) := by
      intro _ _ _
      rfl
    rw [hequal] at hone
    change (fun _ : Bool ↦ (1 : ℝ)) = (0 : Bool → ℝ) at hone
    have hfalse := congrFun hone false
    norm_num at hfalse
#print axioms constants_are_necessary

/-- Closure under linear combinations is necessary: constants together with scalar multiples
of one Boolean block indicator are multiplicatively closed and separating, but omit their sums. -/
theorem linear_combinations_are_necessary :
    ∃ A : Set (Bool → ℝ),
      ContainsConstants A ∧
      ClosedUnderPointwiseMultiplication A ∧
      RelationInvariantFunctions (Indistinguishable A) ≠ A := by
  let step : Bool → ℝ := fun b ↦ if b then 1 else 0
  let A : Set (Bool → ℝ) :=
    {f | (∃ c : ℝ, f = fun _ ↦ c) ∨ ∃ c : ℝ, f = fun b ↦ c * step b}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro c
    exact Or.inl ⟨c, rfl⟩
  · rintro f g (hf | hf) (hg | hg)
    · rcases hf with ⟨c, rfl⟩
      rcases hg with ⟨d, rfl⟩
      exact Or.inl ⟨c * d, by funext b; ring⟩
    · rcases hf with ⟨c, rfl⟩
      rcases hg with ⟨d, rfl⟩
      exact Or.inr ⟨c * d, by funext b; ring⟩
    · rcases hf with ⟨c, rfl⟩
      rcases hg with ⟨d, rfl⟩
      exact Or.inr ⟨c * d, by funext b; ring⟩
    · rcases hf with ⟨c, rfl⟩
      rcases hg with ⟨d, rfl⟩
      refine Or.inr ⟨c * d, ?_⟩
      funext b
      cases b <;> simp [step]
  · intro hequal
    let target : Bool → ℝ := fun b ↦ if b then 2 else 1
    have htarget : target ∈ RelationInvariantFunctions (Indistinguishable A) := by
      intro x y hxy
      have step_mem : step ∈ A := Or.inr ⟨1, by funext b; simp [step]⟩
      have hstep := hxy step step_mem
      cases x <;> cases y <;> simp [step] at hstep ⊢
    rw [hequal] at htarget
    rcases htarget with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hfalse := congrFun hc false
      have htrue := congrFun hc true
      norm_num [target] at hfalse htrue
      linarith
    · have hfalse := congrFun hc false
      norm_num [target, step] at hfalse
#print axioms linear_combinations_are_necessary

/-- Pointwise multiplication is necessary: affine functions on three points contain constants,
are closed under linear combinations, and separate points, but omit the square of the coordinate. -/
theorem pointwise_multiplication_is_necessary :
    ∃ A : Set (Fin 3 → ℝ),
      ContainsConstants A ∧
      ClosedUnderLinearCombinations A ∧
      RelationInvariantFunctions (Indistinguishable A) ≠ A := by
  let coordinate : Fin 3 → ℝ := fun i ↦ i.val
  let A : Set (Fin 3 → ℝ) :=
    {f | ∃ a b : ℝ, ∀ i, f i = a + b * coordinate i}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro c
    exact ⟨c, 0, fun i ↦ by simp⟩
  · rintro u v f g ⟨a, b, hf⟩ ⟨c, d, hg⟩
    refine ⟨u * a + v * c, u * b + v * d, fun i ↦ ?_⟩
    change u * f i + v * g i = _
    rw [hf i, hg i]
    ring
  · intro hequal
    let square : Fin 3 → ℝ := fun i ↦ coordinate i ^ 2
    have hsquare : square ∈ RelationInvariantFunctions (Indistinguishable A) := by
      intro x y hxy
      have coordinate_mem : coordinate ∈ A := ⟨0, 1, fun i ↦ by simp⟩
      have hcoordinate := hxy coordinate coordinate_mem
      have hcoordinate' : (x.val : ℝ) = y.val := by
        simpa only [coordinate] using hcoordinate
      have hval : x.val = y.val := by exact_mod_cast hcoordinate'
      have hxy' : x = y := Fin.ext hval
      rw [hxy']
    rw [hequal] at hsquare
    rcases hsquare with ⟨a, b, hsquare⟩
    have hzero := hsquare ⟨0, by omega⟩
    have hone := hsquare ⟨1, by omega⟩
    have htwo := hsquare ⟨2, by omega⟩
    norm_num [square, coordinate] at hzero hone htwo
    linarith
#print axioms pointwise_multiplication_is_necessary

-- The six requested degenerate cases all satisfy the corresponding half of the duality.
example (R : Setoid Empty) :
    Indistinguishable (partitionAlgebra R : Set (Empty → ℝ)) = R :=
  indistinguishability_partitionAlgebra R

example (A : Subalgebra ℝ (Unit → ℝ)) :
    partitionAlgebra (indistinguishabilitySetoid (A : Set (Unit → ℝ))) = A :=
  partitionAlgebra_indistinguishability A

example {X : Type*} :
    Indistinguishable (partitionAlgebra (⊤ : Setoid X) : Set (X → ℝ)) = (⊤ : Setoid X) :=
  indistinguishability_partitionAlgebra ⊤

example {X : Type*} :
    Indistinguishable (partitionAlgebra (⊥ : Setoid X) : Set (X → ℝ)) = (⊥ : Setoid X) :=
  indistinguishability_partitionAlgebra ⊥

example {X : Type*} [Fintype X] :
    partitionAlgebra
      (indistinguishabilitySetoid ((⊥ : Subalgebra ℝ (X → ℝ)) : Set (X → ℝ))) = ⊥ :=
  partitionAlgebra_indistinguishability ⊥

example {X : Type*} [Fintype X] :
    partitionAlgebra
      (indistinguishabilitySetoid ((⊤ : Subalgebra ℝ (X → ℝ)) : Set (X → ℝ))) = ⊤ :=
  partitionAlgebra_indistinguishability ⊤

end D5.S3.ConceptDynamics.Algebra.FinitePartitionAlgebraDuality
