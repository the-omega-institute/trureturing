/- GID: D5/S3/FiniteGroups/GroupAlgebra/Morita/SimpleRing
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/Morita/SimpleRing
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Attributed equality-of-dimension criterion for modules over a finite simple algebra. -/

/-
Classical algebra proofs used for the actual finite-group representation image.
Proof attribution: AxiomMath/Stacks contributors, Apache-2.0 (see upstream/LICENSE).
Pinned revision: 5ed82d14634e8d9576bb844c7bd4e3da66d450e7
Upstream: StacksCore/RingTheory/Morita/SimpleRing.lean
SHA-256: 5f5496b114b4852d86535beacd0db9ecc28eeff81fe9d68257627bdda66e6edf
Upstream: StacksCore/LinearAlgebra/Dimension/Finite.lean
SHA-256: c6579009c8e3296239dc55ad9e1c7892feab42e745755dbc24694c8a0cafbb66
The pinned source files contain no individual author or copyright notices.
Retirement: when the Mathlib revision pinned in this repository's lake-manifest.json
provides an equivalent of this namespace's `linearEquiv_iff_finrank_eq_over_simple_ring`,
for any field k, finite-dimensional simple k-algebra A and finite
A-modules M, N with compatible k-actions and scalar towers, replace that fragment
with direct Mathlib reuse and remove its unused transplanted helpers. Preserve
the equivalence between Nonempty (M ≃ₗ[A] N) and equality of k-finranks,
including zero modules, without centrality or algebraic-closure assumptions.
-/

import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.DivisionRing

namespace D5.S3.RingTheory.Morita.SimpleRing

open CategoryTheory DirectSum

universe w u v

open Module in
/-- If `M` is trivial and `N` has the same rank as `M` then `M` has a linear-equivalence to `N`. -/
private def equivOfSingleton {k A M N : Type*} [Ring k] [StrongRankCondition k] [Ring A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module k M] [Module A N] [Module k N]
    [Module.Finite k N] [NoZeroSMulDivisors k N] (h1 : finrank k M = finrank k N)
    (h2 : Subsingleton M) : M ≃ₗ[A] N :=
  have := nontrivial_of_invariantBasisNumber k
  have : Subsingleton N := subsingleton_of_forall_eq 0 fun x ↦ by
    obtain ⟨a, ha, hax⟩ := finrank_eq_zero_iff.1 (h1 ▸ finrank_zero_of_subsingleton) x
    exact (eq_zero_or_eq_zero_of_smul_eq_zero hax).resolve_left ha
  LinearEquiv.ofSubsingleton M N

section simple

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A]
    [IsSimpleRing A] [Module.Finite k A]

@[stacks 074E "(1)"]
private lemma linearEquiv_of_isSimpleModule_over_simple_ring [IsArtinianRing A] (M N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N] [IsSimpleModule A M]
    [IsSimpleModule A N] : Nonempty (M ≃ₗ[A] N) := by
  obtain ⟨n, hn, D, _, ⟨iso₁⟩⟩ := IsSimpleRing.exists_ringEquiv_matrix_divisionRing A
  let e₂ : ModuleCat A ≌ ModuleCat D :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv iso₁.symm).trans <|
    ModuleCat.matrixEquivalence D 0|>.symm
  have := IsSimpleModule.obj_of_isEquivalence e₂.functor (ModuleCat.of A M)
  have := IsSimpleModule.obj_of_isEquivalence e₂.functor (ModuleCat.of A N)
  have iso₂ := DivisionRing.nonempty_linearEquiv_of_isSimpleModule D
    (e₂.functor.obj (ModuleCat.of A M))|>.some.trans (DivisionRing.nonempty_linearEquiv_of_isSimpleModule D
    (e₂.functor.obj (ModuleCat.of A N))|>.some.symm)
  exact ⟨e₂.unitIso.app _ ≪≫ (e₂.inverse.mapIso <| iso₂.toModuleIso) ≪≫
    (e₂.unitIso.app _).symm|>.toLinearEquiv⟩

@[stacks 074E "(2)"]
private lemma directSum_simple_module_over_simple_ring [IsArtinianRing A] (M : Type v) [AddCommGroup M]
    [Module A M] : ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module A S) (_ : IsSimpleModule A S)
    (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  classical
  obtain ⟨n, hn, D, inst1, ⟨iso₁⟩⟩ := IsSimpleRing.exists_ringEquiv_matrix_divisionRing A
  let e₁ := ModuleCat.matrixEquivalence D (ι := Fin n) 0
  let e₂ : ModuleCat A ≌ ModuleCat (Matrix (Fin n) (Fin n) D) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv iso₁.symm
  let e := e₂.trans e₁.symm
  let S := e.inverse.obj (ModuleCat.of D D)
  have : IsSimpleModule A S := IsSimpleModule.obj_of_isEquivalence e.inverse (ModuleCat.of D D)
  obtain ⟨b, hb⟩ : Module.Free D (e.functor.obj (ModuleCat.of A M)) := inferInstance
  refine ⟨S, inferInstance, inferInstance, inferInstance, b, ⟨?_⟩⟩
  let iso₄ : ModuleCat.of A (b →₀ e.inverse.obj (ModuleCat.of D D)) ≅
      e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
    (finsuppLequivDFinsupp _).toModuleIso ≪≫ (ModuleCat.coprodIsoDirectSum _).symm ≪≫
    (Limits.PreservesCoproduct.iso _ _).symm ≪≫ e.inverse.mapIso
    ((ModuleCat.coprodIsoDirectSum _) ≪≫ (finsuppLequivDFinsupp _).symm.toModuleIso)
  exact e.unitIso.app (ModuleCat.of A M) ≪≫ (e.inverse.mapIso hb.repr.toModuleIso)
    ≪≫ iso₄.symm |>.toLinearEquiv


private lemma directSum_simple_module_over_simple_algebra' (A : Type v) [Ring A] [IsArtinianRing A]
    [IsSimpleRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (S : Type v) [AddCommGroup S] [Module A S] [IsSimpleModule A S] :
    ∃ (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  obtain ⟨T, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring A M
  obtain ⟨iso'⟩ := linearEquiv_of_isSimpleModule_over_simple_ring A S T
  exact ⟨ι, ⟨iso ≪≫ₗ Finsupp.mapRange.linearEquiv iso'.symm⟩⟩

/-- If a finite `k`-module `P` is `A`-isomorphic to `ι →₀ S` with `ι` nonempty and `S` nontrivial,
then `S` is finite over `k` and `ι` is finite. -/
private theorem finite_of_linearEquiv_finsupp (K : Type*) {R P S ι : Type*} [Field K] [Ring R]
    [Algebra K R] [AddCommGroup P] [AddCommGroup S] [Module R P] [Module R S] [Module K P]
    [Module K S] [IsScalarTower K R P] [IsScalarTower K R S] [Module.Finite K P] [Nonempty ι]
    [Nontrivial S] (e : P ≃ₗ[R] (ι →₀ S)) : Module.Finite K S ∧ Finite ι :=
  (Module.finite_finsupp_iff.1 <| Module.Finite.equiv (e.restrictScalars K)).resolve_left
    (not_isEmpty_of_nonempty ι) |>.resolve_left (not_subsingleton S)

attribute [local instance] Fintype.ofFinite in
@[stacks 074E "(3)"]
lemma linearEquiv_iff_finrank_eq_over_simple_ring
    (M N : Type v) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module k M]
    [Module k N] [IsScalarTower k A M] [IsScalarTower k A N] [Module.Finite A M]
    [Module.Finite A N] : Nonempty (M ≃ₗ[A] N) ↔ Module.finrank k M = Module.finrank k N := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : Module.Finite k M := Module.Finite.trans A M
  have : Module.Finite k N := Module.Finite.trans A N
  refine ⟨fun ⟨e⟩ ↦ (e.restrictScalars k).finrank_eq, fun h ↦ ?_⟩
  obtain ⟨S, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring A M
  obtain ⟨ι', ⟨iso'⟩⟩ := directSum_simple_module_over_simple_algebra' A N S
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨equivOfSingleton h iso.injective.subsingleton⟩
  obtain hι' | hι' := isEmpty_or_nonempty ι'
  · exact ⟨equivOfSingleton h.symm iso'.injective.subsingleton|>.symm⟩
  let : Module k S := Module.compHom S (algebraMap k A)
  have : IsScalarTower k A S := .of_algebraMap_smul fun _ _ ↦ rfl
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  obtain ⟨hS, hfι⟩ := finite_of_linearEquiv_finsupp k iso
  obtain ⟨-, hfι'⟩ := finite_of_linearEquiv_finsupp k iso'
  have EQ := (iso.restrictScalars k).finrank_eq.symm.trans <|
    h.trans (iso'.restrictScalars k).finrank_eq
  simp only [Module.finrank_finsupp, mul_eq_mul_right_iff] at EQ
  replace EQ := Fintype.card_eq.1 <| EQ.resolve_right <| ne_of_gt Module.finrank_pos
  exact ⟨iso ≪≫ₗ Finsupp.lcongr EQ.some (LinearEquiv.refl A S) ≪≫ₗ iso'.symm⟩

end simple

end D5.S3.RingTheory.Morita.SimpleRing
