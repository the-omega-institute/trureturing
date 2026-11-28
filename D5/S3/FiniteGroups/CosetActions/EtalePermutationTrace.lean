/- GID: D5/S3/FiniteGroups/CosetActions/EtalePermutationTrace
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/CosetActions/EtalePermutationTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The linear trace of a transitive finite étale action counts fixed cosets. -/

module

public import D5.S3.FiniteGroups.CosetActions.TransitiveEtaleAction
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.StdBasis
import OmegaBuild.Commands

/-!
The equivariant coset coordinates transport the delta basis to the algebra.
In this basis the linear operators are permutation matrices.
-/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.FiniteGroups.CosetActions.EtalePermutationTrace

/-- For a finite étale complex algebra with scalar invariants, the linear trace
at each group element counts the fixed points on a single left coset space. -/
theorem exists_coset_trace_eq_fixedPoints {G A : Type*} [Group G] [Finite G]
    [CommRing A] [Nontrivial A] [Algebra ℂ A] [Module.Finite ℂ A] [Algebra.Etale ℂ A]
    (ρ : G →* (A ≃ₐ[ℂ] A))
    (hfixed : ∀ a : A, (∀ g : G, ρ g a = a) → ∃ z : ℂ, a = algebraMap ℂ A z) :
    ∃ K : Subgroup G, ∀ g : G,
      LinearMap.trace ℂ A (ρ g).toLinearMap = ({q : G ⧸ K | g • q = q}.ncard : ℂ) := by
  classical
  obtain ⟨K, e, he⟩ := TransitiveEtaleAction.exists_coset_algEquiv ρ hfixed
  let : Fintype (G ⧸ K) := Fintype.ofFinite _
  let b := (Pi.basisFun ℂ (G ⧸ K)).map e.toLinearEquiv.symm
  have hb (j : G ⧸ K) : e (b j) = Pi.single j 1 := by
    change e (e.symm ((Pi.basisFun ℂ (G ⧸ K)) j)) = _
    rw [e.apply_symm_apply, Pi.basisFun_apply]
  refine ⟨K, fun g ↦ ?_⟩
  let σ : Equiv.Perm (G ⧸ K) := MulAction.toPerm g
  -- Row i reads the delta functions at the inverse translate of i.
  have hmatrix :
      LinearMap.toMatrix b b (ρ g).toLinearMap = Equiv.Perm.permMatrix ℂ σ.symm := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change (Pi.basisFun ℂ (G ⧸ K)).repr (e (ρ g (b j))) i = _
    rw [Pi.basisFun_repr, he, hb]
    change (Pi.single j 1 : (G ⧸ K) → ℂ) (σ.symm i) = _
    have hrow : Equiv.Perm.permMatrix ℂ σ.symm i = Pi.single (σ.symm i) 1 :=
      PEquiv.toMatrix_toPEquiv_apply σ.symm i
    rw [hrow]
    simp only [Pi.single_apply, eq_comm]
  change _ = ((Function.fixedPoints σ).ncard : ℂ)
  rw [LinearMap.trace_eq_matrix_trace ℂ b, hmatrix, Matrix.trace_permutation,
    Function.fixedPoints_symm]

/-- The same subgroup that computes the character also gives a nonvanishing
criterion. Each of its elements fixes the identity coset. -/
theorem exists_coset_trace_eq_fixedPoints_and_ne_zero {G A : Type*} [Group G] [Finite G]
    [CommRing A] [Nontrivial A] [Algebra ℂ A] [Module.Finite ℂ A] [Algebra.Etale ℂ A]
    (ρ : G →* (A ≃ₐ[ℂ] A))
    (hfixed : ∀ a : A, (∀ g : G, ρ g a = a) → ∃ z : ℂ, a = algebraMap ℂ A z) :
    ∃ K : Subgroup G, ∀ g : G,
      LinearMap.trace ℂ A (ρ g).toLinearMap = ({q : G ⧸ K | g • q = q}.ncard : ℂ) ∧
      (g ∈ K → LinearMap.trace ℂ A (ρ g).toLinearMap ≠ 0) := by
  obtain ⟨K, htrace⟩ := exists_coset_trace_eq_fixedPoints ρ hfixed
  refine ⟨K, fun g ↦ ⟨htrace g, ?_⟩⟩
  intro hg
  have hpoint : QuotientGroup.mk (1 : G) ∈ {q : G ⧸ K | g • q = q} := by
    change (QuotientGroup.mk (g * 1) : G ⧸ K) = QuotientGroup.mk 1
    simpa only [mul_one, one_mul] using QuotientGroup.mk_mul_of_mem (1 : G) hg
  rw [htrace g]
  exact Nat.cast_ne_zero.mpr (Set.ncard_ne_zero_of_mem hpoint)

#print axioms exists_coset_trace_eq_fixedPoints
#print axioms exists_coset_trace_eq_fixedPoints_and_ne_zero

end D5.S3.FiniteGroups.CosetActions.EtalePermutationTrace
