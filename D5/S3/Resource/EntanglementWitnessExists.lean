/- GID: D5/S3/Resource/EntanglementWitnessExists
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hilbert--Schmidt topology transfer yields entanglement witnesses. -/

import Mathlib
import D5.S3.Resource.CompositeCones
import D5.S3.Resource.CompositeConeDuality
import D5.S3.Resource.EntanglementWitness
import D5.S3.Resource.SeparableConeClosed

/- Provenance: Native proof over pinned mathlib. -/
/- Search receipt (2026-08-14): reused D5's frozen `separableCone`,
   `blockPositive`, `pairing`, cone closure laws, duality characterization, and
   `isClosed_separableCone`. In pinned mathlib, searches in
   Analysis/Convex/Cone/InnerDual.lean hit `ProperCone.hyperplane_separation'`;
   Analysis/InnerProductSpace/Defs.lean hit `InnerProductSpace.ofCore`; and
   Analysis/Normed/Module/FiniteDimension.lean plus
   Topology/Algebra/Module/FiniteDimension.lean hit the documented finite-
   dimensional norm-equivalence route
   `LinearMap.continuous_of_finiteDimensional` and
   `FiniteDimensional.complete`. No direct theorem comparing two norms on one
   type exists: mathlib explicitly prescribes putting the second norm on a copy
   and proving both identity maps continuous. That route is implemented below. -/

namespace D5.S3.Resource.EntanglementWitnessExists

open D5.S3.Resource.CompositeCones
open D5.S3.Resource.CompositeConeDuality
open D5.S3.Resource.EntanglementWitness
open D5.S3.Resource.SeparableConeClosed
open scoped RealInnerProductSpace ComplexOrder

noncomputable section

abbrev CompositeMatrix (m n : ℕ) := Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ

@[reducible] private def hsCore (m n : ℕ) : InnerProductSpace.Core ℝ (CompositeMatrix m n) := {
  definite := by
    intro S hS
    have ht : (0 : ℂ) ≤ Matrix.trace (Matrix.conjTranspose S * S) := by
      exact (Matrix.posSemidef_conjTranspose_mul_self S).trace_nonneg
    have hre : Complex.re (Matrix.trace (Matrix.conjTranspose S * S)) = 0 := hS
    have him : Complex.im (Matrix.trace (Matrix.conjTranspose S * S)) = 0 :=
      (Complex.nonneg_iff.mp ht).2.symm
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    exact Complex.ext hre him
  inner := fun S W => Complex.re (Matrix.trace (Matrix.conjTranspose S * W))
  conj_inner_symm := by
    intro S W
    change Complex.re (Matrix.trace (Matrix.conjTranspose W * S)) =
      Complex.re (Matrix.trace (Matrix.conjTranspose S * W))
    have htrace : Matrix.trace (Matrix.conjTranspose W * S) =
        star (Matrix.trace (Matrix.conjTranspose S * W)) := by
      calc
        Matrix.trace (Matrix.conjTranspose W * S) =
            Matrix.trace ((Matrix.conjTranspose W * S).conjTranspose).conjTranspose := by
              simp
        _ = star (Matrix.trace ((Matrix.conjTranspose W * S).conjTranspose)) :=
          Matrix.trace_conjTranspose _
        _ = star (Matrix.trace (Matrix.conjTranspose S * W)) := by
          congr 1
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [htrace]
    simp
  re_inner_nonneg := by
    intro S
    change 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose S * S))
    exact (Complex.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self S).trace_nonneg).1
  add_left := by
    intro S T W
    simp [Matrix.conjTranspose_add, add_mul, Matrix.trace_add]
  smul_left := by
    intro S W r
    simp [Matrix.conjTranspose_smul]
}

theorem pairing_eq_real_inner (m n : ℕ) (S W : CompositeMatrix m n) :
    pairing S W = Complex.re (Matrix.trace (Matrix.conjTranspose S * W)) := rfl

private def HilbertSchmidtCopy (E : Type*) := E

namespace HilbertSchmidtCopy

private instance {E : Type*} [h : AddCommGroup E] :
    AddCommGroup (HilbertSchmidtCopy E) := h

private instance {E : Type*} [AddCommGroup E] [h : Module ℝ E] :
    Module ℝ (HilbertSchmidtCopy E) := h

private def linearEquiv (E : Type*) [AddCommGroup E] [Module ℝ E] :
    E ≃ₗ[ℝ] HilbertSchmidtCopy E := LinearEquiv.refl ℝ E

@[reducible] private def core {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : InnerProductSpace.Core ℝ E) :
    InnerProductSpace.Core ℝ (HilbertSchmidtCopy E) := {
  inner := c.inner
  conj_inner_symm := c.conj_inner_symm
  re_inner_nonneg := c.re_inner_nonneg
  definite := c.definite
  add_left := c.add_left
  smul_left := c.smul_left
}

end HilbertSchmidtCopy

private theorem finiteDimensional_topology_bridge
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [FiniteDimensional ℝ E]
    (c : InnerProductSpace.Core ℝ E) :
    letI : InnerProductSpace.Core ℝ (HilbertSchmidtCopy E) :=
      HilbertSchmidtCopy.core c
    letI : NormedAddCommGroup (HilbertSchmidtCopy E) :=
      InnerProductSpace.Core.toNormedAddCommGroup
    letI : NormedSpace ℝ (HilbertSchmidtCopy E) :=
      InnerProductSpace.Core.toNormedSpace
    Continuous (HilbertSchmidtCopy.linearEquiv E) ∧
      Continuous (HilbertSchmidtCopy.linearEquiv E).symm := by
  let c' := HilbertSchmidtCopy.core c
  letI : InnerProductSpace.Core ℝ (HilbertSchmidtCopy E) := c'
  letI : NormedAddCommGroup (HilbertSchmidtCopy E) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ
      (HilbertSchmidtCopy E) _ _ _ c'
  let pc : PreInnerProductSpace.Core ℝ (HilbertSchmidtCopy E) := {
    inner := c'.inner
    conj_inner_symm := c'.conj_inner_symm
    re_inner_nonneg := c'.re_inner_nonneg
    add_left := c'.add_left
    smul_left := c'.smul_left
  }
  letI : InnerProductSpace ℝ (HilbertSchmidtCopy E) :=
    @InnerProductSpace.ofCore ℝ (HilbertSchmidtCopy E) _ _ _ pc
  constructor
  · exact (HilbertSchmidtCopy.linearEquiv E).toLinearMap.continuous_of_finiteDimensional
  · haveI : FiniteDimensional ℝ (HilbertSchmidtCopy E) :=
      FiniteDimensional.of_injective
        (HilbertSchmidtCopy.linearEquiv E).symm.toLinearMap
        (HilbertSchmidtCopy.linearEquiv E).symm.injective
    exact
      (HilbertSchmidtCopy.linearEquiv E).symm.toLinearMap.continuous_of_finiteDimensional

/-- The Hilbert--Schmidt norm induced by `hsCore` has exactly the matrix's
existing finite-dimensional topology. The homeomorphism is the identity map. -/
theorem hilbertSchmidtTopology_homeomorph (m n : ℕ) :
    let c' := HilbertSchmidtCopy.core (hsCore m n)
    letI : InnerProductSpace.Core ℝ
        (HilbertSchmidtCopy (CompositeMatrix m n)) := c'
    letI : NormedAddCommGroup
        (HilbertSchmidtCopy (CompositeMatrix m n)) :=
      InnerProductSpace.Core.toNormedAddCommGroup
    letI : NormedSpace ℝ (HilbertSchmidtCopy (CompositeMatrix m n)) :=
      InnerProductSpace.Core.toNormedSpace
    Nonempty (CompositeMatrix m n ≃ₜ
      HilbertSchmidtCopy (CompositeMatrix m n)) := by
  let c' := HilbertSchmidtCopy.core (hsCore m n)
  letI : InnerProductSpace.Core ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) := c'
  letI : NormedAddCommGroup
      (HilbertSchmidtCopy (CompositeMatrix m n)) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) _ _ _ c'
  let pc : PreInnerProductSpace.Core ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) := {
    inner := c'.inner
    conj_inner_symm := c'.conj_inner_symm
    re_inner_nonneg := c'.re_inner_nonneg
    add_left := c'.add_left
    smul_left := c'.smul_left
  }
  letI : InnerProductSpace ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) :=
    @InnerProductSpace.ofCore ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) _ _ _ pc
  have h := finiteDimensional_topology_bridge (hsCore m n)
  exact ⟨{
    HilbertSchmidtCopy.linearEquiv (CompositeMatrix m n) with
    continuous_toFun := h.1
    continuous_invFun := h.2
  }⟩

theorem exists_entanglementWitness {m n : ℕ} (R : CompositeMatrix m n) :
    R.PosSemidef → ¬separableCone R →
      ∃ W, blockPositive W ∧ pairing R W < 0 := by
  intro _hR hnot
  let c' := HilbertSchmidtCopy.core (hsCore m n)
  letI : InnerProductSpace.Core ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) := c'
  letI : NormedAddCommGroup
      (HilbertSchmidtCopy (CompositeMatrix m n)) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) _ _ _ c'
  let pc : PreInnerProductSpace.Core ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) := {
    inner := c'.inner
    conj_inner_symm := c'.conj_inner_symm
    re_inner_nonneg := c'.re_inner_nonneg
    add_left := c'.add_left
    smul_left := c'.smul_left
  }
  letI : InnerProductSpace ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) :=
    @InnerProductSpace.ofCore ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) _ _ _ pc
  have hcontinuous := finiteDimensional_topology_bridge (hsCore m n)
  let e : CompositeMatrix m n ≃ₜ
      HilbertSchmidtCopy (CompositeMatrix m n) := {
    HilbertSchmidtCopy.linearEquiv (CompositeMatrix m n) with
    continuous_toFun := hcontinuous.1
    continuous_invFun := hcontinuous.2
  }
  have hclosed : IsClosed
      {X : HilbertSchmidtCopy (CompositeMatrix m n) |
        separableCone (e.symm X)} :=
    isClosed_separableCone.preimage e.symm.continuous
  let C : ConvexCone ℝ (HilbertSchmidtCopy (CompositeMatrix m n)) :=
    ⟨{X | separableCone (e.symm X)},
      fun _c hc _S hS => by
        change separableCone (e.symm (_c • _S))
        change separableCone
          ((HilbertSchmidtCopy.linearEquiv (CompositeMatrix m n)).symm (_c • _S))
        rw [map_smul]
        exact separableCone_smul hc.le hS,
      fun _S hS _T hT => by
        change separableCone (e.symm (_S + _T))
        change separableCone
          ((HilbertSchmidtCopy.linearEquiv (CompositeMatrix m n)).symm (_S + _T))
        rw [map_add]
        exact separableCone_add hS hT⟩
  have hCclosed : IsClosed
      (C : Set (HilbertSchmidtCopy (CompositeMatrix m n))) := by
    simpa [C] using hclosed
  have hCnonempty :
      (C : Set (HilbertSchmidtCopy (CompositeMatrix m n))).Nonempty := by
    exact ⟨0, by
      change separableCone
        ((HilbertSchmidtCopy.linearEquiv (CompositeMatrix m n)).symm 0)
      rw [map_zero]
      exact separableCone_zero⟩
  lift C to ProperCone ℝ (HilbertSchmidtCopy (CompositeMatrix m n))
    using ⟨hCnonempty, hCclosed⟩ with K hK
  have hRnot : (e R : HilbertSchmidtCopy (CompositeMatrix m n)) ∉ K := by
    intro hmem
    have hmemC : e R ∈ C := by
      rw [← hK]
      exact hmem
    change separableCone (e.symm (e R)) at hmemC
    exact hnot (by simpa using hmemC)
  letI : FiniteDimensional ℝ
      (HilbertSchmidtCopy (CompositeMatrix m n)) :=
    FiniteDimensional.of_injective
      (HilbertSchmidtCopy.linearEquiv (CompositeMatrix m n)).symm.toLinearMap
      (HilbertSchmidtCopy.linearEquiv (CompositeMatrix m n)).symm.injective
  letI : CompleteSpace (HilbertSchmidtCopy (CompositeMatrix m n)) :=
    FiniteDimensional.complete ℝ _
  obtain ⟨W, hW, hRW⟩ := K.hyperplane_separation' hRnot
  refine ⟨e.symm W, ?_, ?_⟩
  · rw [blockPositive_iff_forall_separable_pairing_nonneg]
    intro S hS
    have hmem : e S ∈ K := by
      have hmemC : e S ∈ C := by
        change separableCone (e.symm (e S))
        simpa using hS
      change e S ∈ (K : ConvexCone ℝ
        (HilbertSchmidtCopy (CompositeMatrix m n)))
      rw [hK]
      exact hmemC
    have hnonneg := hW (e S) hmem
    change 0 ≤ (hsCore m n).inner S (e.symm W) at hnonneg
    exact hnonneg
  · change (hsCore m n).inner R (e.symm W) < 0 at hRW
    exact hRW

end
end D5.S3.Resource.EntanglementWitnessExists
