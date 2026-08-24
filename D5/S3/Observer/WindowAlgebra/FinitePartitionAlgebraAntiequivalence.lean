/- GID: D5/S3/Observer/WindowAlgebra/FinitePartitionAlgebraAntiequivalence
   generality: G
   mirror-B: D5/B/S3/Observer/WindowAlgebra/FinitePartitionAlgebraAntiequivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite real partition algebras and relations reconstruct each other. -/

import Mathlib

/- Library-search audit trail (2026-08-25):
   * Repository searches in the Observer, Entropy, ObserverMemory, and QuantumStates
     families found no real-valued theorem proving both reconstruction equalities.
   * `ObservableAlgebraClosureDuality` contains a useful finite class-indicator proof,
     but its public carrier is the complex star algebra `StarSubalgebra ℂ (X -> ℂ)`;
     it is not an exact hit for the source's real function algebra.
   * Pinned Mathlib searches for finite function subalgebras, partition algebras,
     separating subalgebras, and relation reconstruction found no exact theorem.
     Standard `Subalgebra` closure operations and quotient induction are used below. -/

namespace D5.S3.Observer.WindowAlgebra.FinitePartitionAlgebraAntiequivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem class_indicator_mem
    {X : Type*} [Finite X] (A : Subalgebra ℝ (X -> ℝ)) (y : X) :
    (fun x => @ite ℝ (∀ f : X -> ℝ, f ∈ A -> f x = f y)
      (Classical.propDecidable _) 1 0) ∈ A := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let related : X -> X -> Prop :=
    fun x z => ∀ f : X -> ℝ, f ∈ A -> f x = f z
  let outside : Finset X := Finset.univ.filter (fun z => ¬ related z y)
  have witnesses : ∀ z, ∃ f : X -> ℝ, f ∈ A ∧
      (related z y ∨ f z ≠ f y) := by
    intro z
    by_cases hz : related z y
    · exact ⟨0, A.zero_mem, Or.inl hz⟩
    · have hseparates : ∃ f : X -> ℝ, f ∈ A ∧ f z ≠ f y := by
        by_contra hnone
        apply hz
        intro f hf
        by_contra hne
        exact hnone ⟨f, hf, hne⟩
      rcases hseparates with ⟨f, hf, hne⟩
      exact ⟨f, hf, Or.inr hne⟩
  choose g hg hproperty using witnesses
  have hdifferent : ∀ z ∈ outside, g z z ≠ g z y := by
    intro z hz
    exact (hproperty z).resolve_left (Finset.mem_filter.mp hz).2
  let factor (z : X) : X -> ℝ :=
    algebraMap ℝ (X -> ℝ) (g z z) - g z
  let normalized (z : X) : X -> ℝ :=
    (g z z - g z y)⁻¹ • factor z
  have hfactor : ∀ z ∈ outside, normalized z ∈ A := by
    intro z _
    exact A.smul_mem (A.sub_mem (A.algebraMap_mem _) (hg z)) _
  let product : X -> ℝ := ∏ z ∈ outside, normalized z
  have hproduct : product ∈ A := by
    exact A.prod_mem (by intro z hz; exact hfactor z hz)
  have hproduct_value : ∀ x,
      product x = if related x y then 1 else 0 := by
    intro x
    by_cases hxy : related x y
    · have hone : ∀ z ∈ outside, normalized z x = 1 := by
        intro z hz
        have hconstant : g z x = g z y := hxy (g z) (hg z)
        have hnonzero : g z z - g z y ≠ 0 := sub_ne_zero.mpr (hdifferent z hz)
        simp [normalized, factor, hconstant, hnonzero]
      rw [if_pos hxy]
      simp only [product, Finset.prod_apply]
      exact Finset.prod_eq_one hone
    · have hxmem : x ∈ outside :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
      have hzero : normalized x x = 0 := by
        simp [normalized, factor]
      rw [if_neg hxy]
      simp only [product, Finset.prod_apply]
      exact Finset.prod_eq_zero hxmem hzero
  have hequal : product =
      (fun x => if related x y then 1 else 0) := funext hproduct_value
  rw [← hequal]
  simpa [related] using hproduct

/-- On a finite real state space, an equivalence relation is recovered from
its fiber-constant algebra, and every real function subalgebra is recovered
from the relation of agreement under all its members. -/
theorem finite_partition_algebra_antiequivalence
    {X : Type*} [Finite X]
    (R : X -> X -> Prop) (hR : Equivalence R)
    (A : Subalgebra ℝ (X -> ℝ)) :
    (fun x y => ∀ f : X -> ℝ,
      (∀ ⦃a b⦄, R a b -> f a = f b) -> f x = f y) = R ∧
    ({f : X -> ℝ | ∀ ⦃x y⦄,
      (∀ g : X -> ℝ, g ∈ A -> g x = g y) -> f x = f y} : Set (X -> ℝ)) =
      (A : Set (X -> ℝ)) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  constructor
  · funext x y
    apply propext
    constructor
    · intro hagree
      by_contra hnot
      let indicator : X -> ℝ := fun z => if R z x then 1 else 0
      have hconstant : ∀ ⦃a b⦄, R a b -> indicator a = indicator b := by
        intro a b hab
        by_cases ha : R a x
        · have hb : R b x := hR.trans (hR.symm hab) ha
          simp [indicator, ha, hb]
        · have hb : ¬ R b x := by
            intro hb
            exact ha (hR.trans hab hb)
          simp [indicator, ha, hb]
      have hindicator := hagree indicator hconstant
      have hxx : R x x := hR.refl x
      have hyx : ¬ R y x := by
        intro hyx
        exact hnot (hR.symm hyx)
      norm_num [indicator, hxx, hyx] at hindicator
    · intro hxy f hf
      exact hf hxy
  · ext f
    constructor
    · intro hf
      let related : X -> X -> Prop :=
        fun x y => ∀ g : X -> ℝ, g ∈ A -> g x = g y
      have related_equivalence : Equivalence related := by
        refine ⟨?_, ?_, ?_⟩
        · intro x g _
          rfl
        · intro x y hxy g hg
          exact (hxy g hg).symm
        · intro x y z hxy hyz g hg
          exact (hxy g hg).trans (hyz g hg)
      let setoid : Setoid X :=
        { r := related
          iseqv := related_equivalence }
      let quotient := Quotient setoid
      let descended : quotient -> ℝ := Quotient.lift f (by
        intro x y hxy
        exact hf hxy)
      let indicator (q : quotient) : X -> ℝ := fun x =>
        if q = Quotient.mk setoid x then 1 else 0
      have hindicator : ∀ q, indicator q ∈ A := by
        intro q
        induction q using Quotient.inductionOn with
        | _ y =>
          have hiff : ∀ x,
              (Quotient.mk setoid y = Quotient.mk setoid x) ↔ related x y := by
            intro x
            constructor
            · intro h
              exact related_equivalence.symm (Quotient.exact h)
            · intro h
              exact Quotient.sound (related_equivalence.symm h)
          have hequal : indicator (Quotient.mk setoid y) =
              (fun x => if related x y then 1 else 0) := by
            funext x
            simp [indicator, hiff x]
          rw [hequal]
          simpa [related] using class_indicator_mem A y
      let expansion : X -> ℝ := ∑ q : quotient, descended q • indicator q
      have hexpansion : expansion ∈ A := by
        exact A.sum_mem (by
          intro q _
          exact A.smul_mem (hindicator q) (descended q))
      have hexpansion_eq : expansion = f := by
        funext x
        have hsum : (∑ q : quotient, descended q • indicator q x) =
            descended (Quotient.mk setoid x) •
              indicator (Quotient.mk setoid x) x := by
          apply Finset.sum_eq_single
          · intro q _ hq
            have hzero : indicator q x = 0 := by
              simp [indicator, hq]
            simp [hzero]
          · intro hmissing
            exact (hmissing (Finset.mem_univ _)).elim
        change (∑ q : quotient, descended q • indicator q) x = f x
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply]
        rw [hsum]
        simp [indicator, descended]
      rw [← hexpansion_eq]
      exact hexpansion
    · intro hf x y hxy
      exact hxy f hf

#print axioms finite_partition_algebra_antiequivalence

end D5.S3.Observer.WindowAlgebra.FinitePartitionAlgebraAntiequivalence
