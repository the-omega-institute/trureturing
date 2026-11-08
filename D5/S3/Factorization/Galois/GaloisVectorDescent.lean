/- GID: D5/S3/Factorization/Galois/GaloisVectorDescent
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GaloisVectorDescent
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Invariant bases and canonical effective descent for semilinear Galois vector spaces. -/

import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RepresentationTheory.Invariants

/-!
Effective semilinear descent for an arbitrary-dimensional vector space. The finite
sum below is not divided by the order of the group. The group law on V and
`SMulDistribClass G L V` are essential: this is a genuine semilinear action,
not a projective action or a cocycle condition assumed to have a solution.

The new proof is invariant generation by twisted orbit sums and Artin
independence, followed by descent of the coordinates of an invariant basis.
Basis extraction, scalar restriction, and tensor base change reuse Mathlib.
-/

noncomputable section

open Module
open scoped TensorProduct

namespace D5.S3.Factorization.Galois.GaloisVectorDescent

universe uG uK uL uV

variable (G : Type uG) (K : Type uK) (L : Type uL) (V : Type uV)
  [Group G] [Finite G] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [IsGaloisGroup G K L]
  [AddCommGroup V] [Module L V] [DistribMulAction G V]
  [SMulDistribClass G L V]

section OrbitSums

variable [Fintype G]

/-- Twisted orbit sum; its scalar parameter avoids averaging by `|G|`. -/
private def orbitSum (a : L) (v : V) : V :=
  ∑ g : G, (g • a) • (g • v)

private theorem orbitSum_mem_fixedPoints (a : L) (v : V) :
    orbitSum G L V a v ∈ MulAction.fixedPoints G V := by
  intro h
  change h • (∑ g : G, (g • a) • (g • v)) = ∑ g : G, (g • a) • (g • v)
  simp_rw [Finset.smul_sum, smul_distrib_smul, ← mul_smul]
  exact Fintype.sum_bijective (fun g : G => h * g) (Group.mulLeft_bijective h)
    _ _ (fun _ => rfl)

end OrbitSums

/-- Artin independence, indexed by the given faithful field action. -/
private theorem fieldAction_linearIndependent :
    LinearIndependent L
      (fun g : G => (MulSemiringAction.toAlgHom K L g).toLinearMap) := by
  letI : FaithfulSMul G L := IsGaloisGroup.faithful K
  exact (linearIndependent_algHom_toLinearMap K L L).comp
    (MulSemiringAction.toAlgHom K L : G → L →ₐ[K] L)
    (MulSemiringAction.toAlgHom_injective K L)

include K in
/-- Invariant vectors span every semilinear Galois vector space over L.
No finite-dimensionality or restriction on the characteristic is assumed. -/
theorem span_fixedPoints :
    Submodule.span L (MulAction.fixedPoints G V) = ⊤ := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  by_contra hspan
  obtain ⟨ell, hell, hker⟩ :=
    (Submodule.span L (MulAction.fixedPoints G V)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hspan)
  have hli := fieldAction_linearIndependent G K L
  apply hell
  ext v
  have hsum :
      (∑ g : G, ell (g • v) • (MulSemiringAction.toAlgHom K L g).toLinearMap) = 0 := by
    ext a
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
    change (∑ g : G, ell (g • v) * (g • a)) = 0
    calc
      (∑ g : G, ell (g • v) * (g • a)) = ell (orbitSum G L V a v) := by
        simp only [orbitSum, map_sum, map_smul, smul_eq_mul]
        exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      _ = 0 := LinearMap.mem_ker.mp
        (hker (Submodule.subset_span (orbitSum_mem_fixedPoints G L V a v)))
  have hcoeff := (linearIndependent_iff'.mp hli) Finset.univ
    (fun g : G => ell (g • v)) hsum (1 : G) (Finset.mem_univ _)
  simpa only [one_smul, LinearMap.zero_apply] using hcoeff

include K in
/-- An arbitrary-dimensional semilinear Galois vector space has an L-basis
fixed pointwise by G. The index type lives in the universe of V. -/
theorem exists_invariant_basis :
    ∃ (ι : Type uV) (b : Basis ι L V), ∀ (g : G) (i : ι), g • b i = b i := by
  classical
  let hs : (⊤ : Submodule L V) ≤ Submodule.span L (MulAction.fixedPoints G V) :=
    (span_fixedPoints G K L V).ge
  refine ⟨_, Basis.ofSpan hs, ?_⟩
  intro g i
  exact (Basis.ofSpan_subset hs (Set.mem_range_self i)) g

/-- Coordinates in a fixed basis transform by the field action. The proof uses
only the finite support of each coordinate vector, not a finite basis. -/
private theorem repr_smul_of_fixed_basis {ι : Type*} (b : Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) (g : G) (v : V) (i : ι) :
    b.repr (g • v) i = g • (b.repr v i) := by
  classical
  let c : ι →₀ L := (b.repr v).mapRange (fun a : L => g • a) (smul_zero g)
  have hgv : g • v = Finsupp.linearCombination L b c := by
    calc
      g • v = g • Finsupp.linearCombination L b (b.repr v) := by
        rw [b.linearCombination_repr]
      _ = Finsupp.linearCombination L b c := by
        simp only [Finsupp.linearCombination_apply]
        dsimp only [c]
        rw [Finsupp.sum_mapRange_index (fun j => zero_smul L (b j))]
        simp only [Finsupp.sum, Finset.smul_sum, smul_distrib_smul, hb]
  rw [hgv, b.repr_linearCombination]
  rfl

section EffectiveDescent

/- Mathlib's preferred scalar-restriction convention. These structures are
available for every L-vector space, by `Module.restrictScalars K L V` and
`IsScalarTower.restrictScalars K L V`; they add no mathematical restriction. -/
variable [Module K V] [IsScalarTower K L V]

/-- Semilinearity and fixation of K imply K-linearity of the group action. -/
private def baseSMulCommClass : SMulCommClass G K V where
  smul_comm g k v := by
    rw [← algebraMap_smul L k v, smul_distrib_smul, smul_algebraMap, algebraMap_smul]

/-- The K-submodule V^G, using Mathlib's representation-invariant submodule. -/
abbrev fixedSubmodule : Submodule K V :=
  letI : SMulCommClass G K V := baseSMulCommClass G K L V
  Representation.invariants (DistribMulAction.toModuleEnd K V (S := G))

/-- An invariant vector has K-valued coordinates in any fixed L-basis;
conversely K-linear combinations of fixed basis vectors are invariant. -/
private theorem span_fixed_basis_eq_fixedSubmodule {ι : Type*} (b : Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) :
    Submodule.span K (Set.range b) = fixedSubmodule G K L V := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ∀ g : G, g • b i = b i
    exact fun g => hb g i
  · intro v hv
    change ∀ g : G, g • v = v at hv
    apply (b.mem_span_iff_repr_mem K v).mpr
    intro i
    have hfixed : b.repr v i ∈ FixedPoints.intermediateField (F := K) (E := L) G := by
      change ∀ g : G, g • (b.repr v i) = b.repr v i
      intro g
      rw [← repr_smul_of_fixed_basis G L V b hb g v i, hv g]
    rw [IsGaloisGroup.fixedPoints_eq_bot G K L] at hfixed
    exact IntermediateField.mem_bot.mp hfixed

/-- The fixed L-basis is a K-basis of V^G. Consumed by `descentEquiv`. -/
private def fixedBasis {ι : Type*} (b : Basis ι L V)
    (hb : ∀ (g : G) (i : ι), g • b i = b i) :
    Basis ι K (fixedSubmodule G K L V) :=
  (b.restrictScalars K).map
    (LinearEquiv.ofEq _ _ (span_fixed_basis_eq_fixedSubmodule G K L V b hb))

/-- Effective semilinear Galois vector-space descent: the canonical map
`L ⊗[K] V^G → V`, `a ⊗ w ↦ a • (w : V)`, is an L-linear equivalence.

The forward map is exactly `Submodule.subtype.liftBaseChange`, hence independent
of the basis used to prove bijectivity. This definition has arbitrary-dimensional
scope. Its mathematical dependency includes the proved invariant-generation
argument above, not an assumption that invariant vectors span. -/
def descentEquiv : L ⊗[K] (fixedSubmodule G K L V) ≃ₗ[L] V := by
  classical
  refine LinearEquiv.ofBijective ((fixedSubmodule G K L V).subtype.liftBaseChange L) ?_
  obtain ⟨ι, b, hb⟩ := exists_invariant_basis G K L V
  let c : Basis ι K (fixedSubmodule G K L V) := fixedBasis G K L V b hb
  let e : L ⊗[K] (fixedSubmodule G K L V) ≃ₗ[L] V :=
    (c.baseChange L).equiv b (Equiv.refl ι)
  have he : (fixedSubmodule G K L V).subtype.liftBaseChange L = e.toLinearMap := by
    apply (c.baseChange L).ext
    intro i
    change (fixedSubmodule G K L V).subtype.liftBaseChange L ((c.baseChange L) i) =
      ((c.baseChange L).equiv b (Equiv.refl ι)) ((c.baseChange L) i)
    rw [Basis.equiv_apply, Equiv.refl_apply, Basis.baseChange_apply,
      LinearMap.liftBaseChange_one_tmul]
    simp [c, fixedBasis]
  rw [he]
  exact e.bijective

end EffectiveDescent

end D5.S3.Factorization.Galois.GaloisVectorDescent
