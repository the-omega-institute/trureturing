/- GID: D5/S1/Eigenstructure/NilpotentJordanChains
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/NilpotentJordanChains
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Module.PID]
   utility: none
   digest: Nilpotent operators admit actual finite Jordan chains over any field. -/

import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/- The PID structure theorem supplies the primary decomposition and its induction.
   Polynomial linearity preserves the operator action, and the quotient power
   bases supply actual chains. No invariant complement or Jordan basis is assumed. -/

namespace D5.S1.Eigenstructure.NilpotentJordanChains

open Polynomial Module
open scoped DirectSum BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def blockBasis (K : Type*) [Field K] (s : ℕ) :
    Basis (Fin s) K (K[X] ⧸ Ideal.span {(X : K[X]) ^ s}) :=
  ((AdjoinRoot.powerBasis' (monic_X.pow s)).basis).reindex
    (finCongr (by change ((X : K[X]) ^ s).natDegree = s; simp only [natDegree_X_pow]))

private theorem blockBasis_apply (K : Type*) [Field K] (s : ℕ) (j : Fin s) :
    blockBasis K s j = AdjoinRoot.root ((X : K[X]) ^ s) ^ j.val := by
  change (((AdjoinRoot.powerBasis' (monic_X.pow s)).basis).reindex
    (finCongr (by change ((X : K[X]) ^ s).natDegree = s; simp only [natDegree_X_pow]))) j = _
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

private theorem blockBasis_smul (K : Type*) [Field K] (s m : ℕ) (j : Fin s) :
    (X ^ m : K[X]) • blockBasis K s j =
      if h : j.val + m < s then blockBasis K s ⟨j.val + m, h⟩ else 0 := by
  simp only [blockBasis_apply]
  change AdjoinRoot.mk ((X : K[X]) ^ s) (X ^ m) *
    AdjoinRoot.root ((X : K[X]) ^ s) ^ j.val =
      if h : j.val + m < s then AdjoinRoot.root ((X : K[X]) ^ s) ^ (j.val + m) else 0
  rw [map_pow, AdjoinRoot.mk_X, ← pow_add, Nat.add_comm m j.val]
  split_ifs with h
  · rfl
  · rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_eq_zero]
    exact pow_dvd_pow X (Nat.le_of_not_gt h)

private theorem sumBasis_apply {K : Type*} [Field K] {d : ℕ} (s : Fin d → ℕ)
    (j : Σ i, Fin (s i)) :
    (DFinsupp.basis fun i => blockBasis K (s i)) j =
      DirectSum.lof K (Fin d) (fun i => K[X] ⧸ Ideal.span {(X : K[X]) ^ s i}) j.1
        (blockBasis K (s j.1) j.2) := by
  simp [DFinsupp.basis, DirectSum.lof]
  rfl

private theorem exists_chain_basis {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ (d : ℕ) (s : Fin d → ℕ) (b : Basis (Σ i, Fin (s i)) K V),
      ∀ (m : ℕ) (i : Fin d) (j : Fin (s i)),
        (f ^ m) (b ⟨i, j⟩) =
          if h : j.val + m < s i then b ⟨i, ⟨j.val + m, h⟩⟩ else 0 := by
  classical
  have ht : Module.IsTorsion' (AEval' f) (Submonoid.powers (X : K[X])) := by
    rw [Submodule.isTorsion'_powers_iff]
    obtain ⟨n, hn⟩ := hf
    intro x
    refine ⟨n, ?_⟩
    apply (AEval'.of f).symm.injective
    simp [Module.AEval.of_symm_smul, hn]
  obtain ⟨d, s, ⟨e⟩⟩ :=
    Module.torsion_by_prime_power_decomposition (irreducible_X (R := K)) ht
  let E := (e.symm.restrictScalars K).trans (AEval'.of f).symm
  let b := (DFinsupp.basis fun i => blockBasis K (s i)).map E
  refine ⟨d, s, b, ?_⟩
  have hE (m : ℕ) (x) : (f ^ m) (E x) = E ((X ^ m : K[X]) • x) := by
    apply (AEval'.of f).injective
    change AEval'.of f ((f ^ m) • (AEval'.of f).symm (e.symm x)) =
      e.symm ((X ^ m : K[X]) • x)
    rw [← AEval'.X_pow_smul_of, LinearEquiv.apply_symm_apply, map_smul]
  intro m i j
  simp only [b, Basis.map_apply, hE, sumBasis_apply]
  change E ((X ^ m : K[X]) • DFinsupp.single i (blockBasis K (s i) j)) =
    if h : j.val + m < s i then E (DFinsupp.single i
      (blockBasis K (s i) ⟨j.val + m, h⟩)) else 0
  rw [← DFinsupp.single_smul, blockBasis_smul]
  split_ifs <;> simp

/-- Every nilpotent endomorphism of a finite-dimensional vector space admits
positive-length Jordan chains forming a basis, with the action of every iterate.
The scalar field is arbitrary; no algebraic-closure hypothesis is needed. -/
private theorem nilpotent_has_jordan_chains {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ+)
      (b : Basis (Σ i, Fin (s i)) K V),
      ∀ (m : ℕ) (i : ι) (j : Fin (s i)),
        (f ^ m) (b ⟨i, j⟩) =
          if h : j.val + m < s i then b ⟨i, ⟨j.val + m, h⟩⟩ else 0 := by
  classical
  obtain ⟨d, s, b, hb⟩ := exists_chain_basis f hf
  let ι := {i : Fin d // 0 < s i}
  let t : ι → ℕ+ := fun i => ⟨s i, i.prop⟩
  let e : (Σ i : Fin d, Fin (s i)) ≃ (Σ i : ι, Fin (t i)) :=
    { toFun := fun j => ⟨⟨j.1, Nat.zero_lt_of_lt j.2.isLt⟩, j.2⟩
      invFun := fun j => ⟨j.1.val, j.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨ι, inferInstance, t, b.reindex e, ?_⟩
  intro m i j
  simp only [Basis.reindex_apply]
  exact hb m i.val j

private theorem chain_basis_rank {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (f : Module.End K V) (s : ι → ℕ+)
    (b : Basis (Σ i, Fin (s i)) K V)
    (hb : ∀ (m : ℕ) (i : ι) (j : Fin (s i)),
      (f ^ m) (b ⟨i, j⟩) =
        if h : j.val + m < s i then b ⟨i, ⟨j.val + m, h⟩⟩ else 0)
    (m : ℕ) :
    Module.finrank K (LinearMap.range (f ^ m)) = ∑ i, ((s i : ℕ) - m) := by
  classical
  let tail : (Σ i, Fin ((s i : ℕ) - m)) → (Σ i, Fin (s i)) :=
    fun j => ⟨j.1, ⟨j.2.val + m, by have := j.2.isLt; omega⟩⟩
  have htail : Function.Injective tail := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hi : i = i' := congrArg Sigma.fst h
    subst i'
    have hj : j.val + m = j'.val + m := by
      exact congrArg (fun x : Σ i, Fin (s i) => x.2.val) h
    have : j = j' := Fin.ext (by omega)
    subst j'
    rfl
  have hrange : LinearMap.range (f ^ m) =
      Submodule.span K (Set.range (fun j => (f ^ m) (b j))) := by
    rw [← Submodule.map_top (f ^ m), ← b.span_eq, Submodule.map_span,
      ← Set.range_comp]
    rfl
  have hspan : LinearMap.range (f ^ m) =
      Submodule.span K (Set.range (fun j => b (tail j))) := by
    rw [hrange]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      dsimp only
      rw [hb]
      split_ifs with h
      · exact Submodule.subset_span ⟨⟨i, ⟨j.val, by omega⟩⟩, rfl⟩
      · exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨i, ⟨j.val, by have := j.isLt; omega⟩⟩, ?_⟩
      dsimp only
      rw [hb]
      split_ifs with h
      · rfl
      · have := j.isLt
        dsimp only at h
        omega
  rw [hspan]
  change finrank K (Submodule.span K (Set.range (b ∘ tail))) = _
  rw [finrank_span_eq_card (b.linearIndependent.comp tail htail)]
  simp

/-- The actual Jordan chains also compute the rank of every iterate. -/
theorem nilpotent_jordan_chains_rank {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ+)
      (b : Basis (Σ i, Fin (s i)) K V),
      (∀ (m : ℕ) (i : ι) (j : Fin (s i)),
        (f ^ m) (b ⟨i, j⟩) =
          if h : j.val + m < s i then b ⟨i, ⟨j.val + m, h⟩⟩ else 0) ∧
      ∀ m : ℕ, Module.finrank K (LinearMap.range (f ^ m)) =
        ∑ i, ((s i : ℕ) - m) := by
  obtain ⟨ι, hι, s, b, hb⟩ := nilpotent_has_jordan_chains f hf
  exact ⟨ι, hι, s, b, hb, chain_basis_rank f s b hb⟩

end

end D5.S1.Eigenstructure.NilpotentJordanChains
