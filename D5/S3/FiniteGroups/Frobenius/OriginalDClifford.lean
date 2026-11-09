/- GID: D5/S3/FiniteGroups/Frobenius/OriginalDClifford
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Frobenius/OriginalDClifford
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Clifford decomposition over the original Schur division ring with independent universes. -/

import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Dimension.Constructions
import D5.S3.FiniteGroups.CliffordConstituents

/-!
The restricted isotypic components carry the original Schur division-ring action.
Their actual inertia cosets index an equivariant product decomposition.
-/

namespace OriginalDCliffordCandidate

open scoped DirectSum
set_option backward.isDefEq.respectTransparency false

universe uR uD uM uI uk uG uV

-- These are proved Mathlib lemmas, deliberately not global instances upstream.
-- Both directions are needed by semilinear equivalence and composition.
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

section CommutingScalars

variable {R : Type uR} [Ring R]
variable (D : Type uD) [Semiring D]
variable {M : Type uM} [AddCommGroup M] [Module R M] [Module D M]
  [SMulCommClass D R M]

/-- Same carrier and additive structure, with the independent left D-action. -/
def fullyInvariantDSubmodule (P : Submodule R M) (hP : P.IsFullyInvariant) :
    Submodule D M where
  carrier := (P : Set M)
  zero_mem' := P.zero_mem
  add_mem' := P.add_mem
  smul_mem' d x hx := hP (Module.toModuleEnd R M d) hx

/-- Canonical D-linear summation. Bijectivity is inherited from the R-linear
summation equivalence, by equality on the direct-sum generators. Thus no
D-linearity of its inverse, nor an equality of endomorphism rings, is assumed. -/
noncomputable def commutingDirectSumEquiv
    {ι : Type uI} [DecidableEq ι]
    (A : ι → Submodule R M) (hA : ∀ i, (A i).IsFullyInvariant)
    (ind : iSupIndep A) (htop : (⨆ i, A i) = ⊤) :
    (⨁ i, fullyInvariantDSubmodule D (A i) (hA i)) ≃ₗ[D] M := by
  let f := DirectSum.coeLinearMap
    (fun i => fullyInvariantDSubmodule D (A i) (hA i))
  let e := ind.linearEquiv htop
  have hsum : ∀ x : (⨁ i, fullyInvariantDSubmodule D (A i) (hA i)), f x = e x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of i x =>
      dsimp only [f]
      rw [DirectSum.coeLinearMap_of]
      change (x : M) = e (DFinsupp.single i x)
      exact (LinearEquiv.apply_symm_apply e (x : M)).symm.trans
        (congrArg e (ind.linearEquiv_symm_apply htop x.2))
    | add x y hx hy =>
      simpa only [map_add, hx, hy]
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact e.injective ((hsum x).symm.trans (h.trans (hsum y)))
  · intro x
    obtain ⟨y, hy⟩ := e.surjective x
    exact ⟨y, (hsum y).trans hy⟩

end CommutingScalars

section SemilinearIsotypicTransport

variable {R : Type uR} [Ring R] {M : Type uM}
  [AddCommGroup M] [Module R M]

/-- Isotypic components are natural under a semilinear automorphism, provided
its scalar map is an automorphism of the SAME ring. No simplicity or
semisimplicity hypothesis is needed: transport the defining family of all
submodules linearly isomorphic to P, and use the inverse for surjectivity. -/
theorem map_isotypicComponent_semilinear
    (α : R ≃+* R) (e : M ≃ₛₗ[α] M) (P : Submodule R M) :
    (isotypicComponent R M P).map e.toLinearMap =
      isotypicComponent R M (P.map e.toLinearMap) := by
  have hle (β : R ≃+* R) (f : M ≃ₛₗ[β] M) (Q : Submodule R M) :
      (isotypicComponent R M Q).map f.toLinearMap ≤
        isotypicComponent R M (Q.map f.toLinearMap) := by
    apply Submodule.map_le_iff_le_comap.mpr
    change sSup {T : Submodule R M | Nonempty (T ≃ₗ[R] Q)} ≤ _
    refine sSup_le ?_
    rintro T ⟨i⟩
    apply Submodule.map_le_iff_le_comap.mp
    have j : T.map f.toLinearMap ≃ₗ[R] Q.map f.toLinearMap :=
      ((f.submoduleMap T).symm.trans i).trans (f.submoduleMap Q)
    exact le_sSup ⟨j⟩
  refine le_antisymm (hle α e P) ?_
  have hback := hle α.symm e.symm (P.map e.toLinearMap)
  have hcancel : (P.map e.toLinearMap).map e.symm.toLinearMap = P :=
    (Submodule.map_symm_eq_iff e).2 rfl
  rw [hcancel] at hback
  intro x hx
  have hpre : e.symm x ∈ isotypicComponent R M P :=
    hback (Submodule.mem_map_of_mem hx)
  exact ⟨e.symm x, hpre, e.apply_symm_apply x⟩

end SemilinearIsotypicTransport

section OriginalEndomorphisms

open scoped MonoidAlgebra
open D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation
open D5.S3.FiniteGroups.CliffordConstituents.Representation

variable {k : Type uk} [Field k] {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- The restriction type synonym carries the SAME original evaluation action.
The explicit change avoids relying on instance search unfolding asModule. -/
noncomputable instance originalDModuleRestriction (N : Subgroup G) :
    Module (Module.End k[G] ρ.asModule) (_root_.Representation.asModule (ρ.comp N.subtype)) := by
  change Module (Module.End k[G] ρ.asModule) ρ.asModule
  infer_instance

/-- End over k[G], acting on the LEFT, commutes with the restricted k[N]-action. -/
noncomputable instance originalDCommRestriction (N : Subgroup G) :
    SMulCommClass (Module.End k[G] ρ.asModule) k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype)) where
  smul_comm d a x := by
    change d (a • x : _root_.Representation.asModule (ρ.comp N.subtype)) =
      (a • (show _root_.Representation.asModule (ρ.comp N.subtype) from d x) :
        _root_.Representation.asModule (ρ.comp N.subtype))
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul, map_zero]
    | add a b ha hb => simp only [add_smul, map_add, ha, hb]
    | single n c =>
      have hd := d.map_smul (MonoidAlgebra.single (n : G) c) x
      simp only [Representation.single_smul] at hd ⊢
      change d (c • ρ (n : G) x) = c • ρ (n : G) (d x) at hd ⊢
      exact hd

/-- Translation is linear for the original D, not k[N]-linear. -/
noncomputable def originalDTranslate (g : G) :
    ρ.asModule ≃ₗ[Module.End k[G] ρ.asModule] ρ.asModule where
  toFun := ρ g
  invFun := ρ g⁻¹
  left_inv := Representation.inv_self_apply ρ g
  right_inv := Representation.self_inv_apply ρ g
  map_add' := (ρ g).map_add
  map_smul' d x := by
    change ρ g (d x) = d (ρ g x)
    have hd := (d.map_smul (MonoidAlgebra.single g (1 : k)) x).symm
    simp only [Representation.single_smul, one_smul] at hd
    change ρ g (d x) = d (ρ g x) at hd
    exact hd

/-- The SAME translation on the restriction, now semilinear over k[N]. Its
coefficient map sends single n c to single (g*n*g⁻¹) c. This is the missing
transport structure; no private constituents-file conjugation helper is used. -/
noncomputable def restrictionTranslate (N : Subgroup G) [N.Normal] (g : G) :
    (_root_.Representation.asModule (ρ.comp N.subtype)) ≃ₛₗ[
      ((MonoidAlgebra.domCongr k k (MulAut.conjNormal (H := N) g)).toRingEquiv :
        k[N] →+* k[N])]
      (_root_.Representation.asModule (ρ.comp N.subtype)) where
  toFun := ρ g
  invFun := ρ g⁻¹
  left_inv := Representation.inv_self_apply ρ g
  right_inv := Representation.self_inv_apply ρ g
  map_add' := (ρ g).map_add
  map_smul' a x := by
    have hconj (n : N) (v : V) :
        ρ g (ρ (n : G) v) = ρ (MulAut.conjNormal g n : G) (ρ g v) := by
      have hg : g * (n : G) = (MulAut.conjNormal g n : G) * g := by
        rw [MulAut.conjNormal_apply]
        group
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hg]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [map_zero, zero_smul]
    | add a b ha hb => simp only [map_add, add_smul, ha, hb]
    | single n c =>
      change ρ g (MonoidAlgebra.single n c • x :
          _root_.Representation.asModule (ρ.comp N.subtype)) =
        (MonoidAlgebra.domCongr k k (MulAut.conjNormal g)
          (MonoidAlgebra.single n c) •
            (show _root_.Representation.asModule (ρ.comp N.subtype) from ρ g x) :
          _root_.Representation.asModule (ρ.comp N.subtype))
      rw [MonoidAlgebra.domCongr_single, Representation.single_smul,
        Representation.single_smul]
      change ρ g (c • ρ (n : G) x) =
        c • ρ (MulAut.conjNormal g n : G) (ρ g x)
      rw [map_smul]
      exact congrArg (fun v : V => c • v) (hconj n x)

/-- Genuine base component as a D-submodule; full invariance is consumed
DIRECTLY from Mathlib, with simplicity installed from the chosen atom. -/
noncomputable def originalDBaseComponent {N : Subgroup G}
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    Submodule (Module.End k[G] ρ.asModule) (_root_.Representation.asModule (ρ.comp N.subtype)) := by
  letI : IsSimpleModule k[N] σ.asSubmodule :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hσ
  exact fullyInvariantDSubmodule (Module.End k[G] ρ.asModule)
    (isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) σ.asSubmodule)
    (Submodule.IsFullyInvariant.isotypicComponent k[N]
      (_root_.Representation.asModule (ρ.comp N.subtype)) σ.asSubmodule)

/-- The actual, unconditional component-image identity. Independent universes
for k, G and V are preserved here. No finite-dimension hypothesis is used. -/
theorem originalDTranslate_map_component {N : Subgroup G} [N.Normal]
    [ρ.IsIrreducible] (σ : Subrepresentation (ρ.comp N.subtype))
    (hσ : IsAtom σ) (g : G) :
    (originalDBaseComponent ρ σ hσ).map (originalDTranslate ρ g).toLinearMap =
      fullyInvariantDSubmodule (Module.End k[G] ρ.asModule)
        (conjSubrepIsotypicComponent ρ σ hσ g).1
        (Submodule.IsFullyInvariant.of_mem_isotypicComponents
          (conjSubrepIsotypicComponent ρ σ hσ g).2) := by
  let t := restrictionTranslate ρ N g
  have hσmap : σ.asSubmodule.map t.toLinearMap = (conjSubrep ρ g σ).asSubmodule := by
    ext x
    rfl
  have hR :
      (isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) σ.asSubmodule).map
          t.toLinearMap = (conjSubrepIsotypicComponent ρ σ hσ g).1 := by
    rw [map_isotypicComponent_semilinear, hσmap,
      coe_conjSubrepIsotypicComponent]
  ext x
  change (x ∈ (isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
      σ.asSubmodule).map t.toLinearMap) ↔
    x ∈ (conjSubrepIsotypicComponent ρ σ hσ g).1
  rw [hR]

end OriginalEndomorphisms

end OriginalDCliffordCandidate
/-!
The component index uses the actual original-D submodule stabilizer.
The scalar, group and representation carrier universes remain independent.
-/
namespace D5.S3.FiniteGroups.CliffordDecomposition.Representation

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped _root_.MonoidAlgebra
open _root_.OriginalDCliffordCandidate
open _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti
open _root_.D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation
open _root_.D5.S3.FiniteGroups.CliffordConstituents.Representation

universe uk uG uV
variable {k : Type uk} [Field k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : _root_.Representation k G V)
  [FiniteDimensional k V] [ρ.IsIrreducible]

private theorem originalDTranslate_mul (a b : G) :
    (originalDTranslate ρ (a * b)).toLinearMap =
      (originalDTranslate ρ a).toLinearMap.comp
        (originalDTranslate ρ b).toLinearMap := by
  ext x
  change ρ (a * b) x = ρ a (ρ b x)
  simp only [map_mul]
  rfl

private theorem originalDTranslate_inv (a : G) :
    originalDTranslate ρ a⁻¹ = (originalDTranslate ρ a).symm := by
  ext x
  rfl

/-- The actual original-D translate of the chosen component. -/
private noncomputable def originalDActualComponent
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    Submodule (Module.End k[G] ρ.asModule) (_root_.Representation.asModule (ρ.comp N.subtype)) :=
  (originalDBaseComponent ρ σ hσ).map (originalDTranslate ρ g).toLinearMap

/-- Actual inertia: the stabilizer of the genuine D-submodule component under
left evaluation by `D = End_{k[G]} ρ.asModule`. -/
noncomputable def originalDActualInertia
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) : Subgroup G where
  carrier := {g | originalDActualComponent ρ σ hσ g = originalDBaseComponent ρ σ hσ}
  one_mem' := by
    have ht : (originalDTranslate ρ (1 : G)).toLinearMap = LinearMap.id := by
      ext x
      change ρ 1 x = x
      simp only [map_one]
      rfl
    dsimp [originalDActualComponent]
    rw [ht, Submodule.map_id]
  mul_mem' := by
    intro a b ha hb
    have hmul := originalDTranslate_mul ρ a b
    dsimp [originalDActualComponent] at ha hb ⊢
    rw [hmul, Submodule.map_comp, hb, ha]
  inv_mem' := by
    intro a ha
    have hinv := originalDTranslate_inv ρ a
    dsimp [originalDActualComponent] at ha ⊢
    rw [hinv]
    exact (Submodule.map_symm_eq_iff (originalDTranslate ρ a)).2 ha

private theorem originalDActualComponent_eq_iff
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (a b : G) :
    originalDActualComponent ρ σ hσ a = originalDActualComponent ρ σ hσ b ↔
      a⁻¹ * b ∈ originalDActualInertia ρ σ hσ := by
  constructor
  · intro hab
    have hcancel :
        ((originalDBaseComponent ρ σ hσ).map (originalDTranslate ρ a).toLinearMap).map
            (originalDTranslate ρ a).symm.toLinearMap =
          originalDBaseComponent ρ σ hσ :=
      (Submodule.map_symm_eq_iff (originalDTranslate ρ a)).2 rfl
    have htransport := congrArg
      (fun P : Submodule (Module.End k[G] ρ.asModule)
          (_root_.Representation.asModule (ρ.comp N.subtype)) =>
        P.map (originalDTranslate ρ a).symm.toLinearMap) hab
    dsimp [originalDActualComponent] at htransport
    rw [hcancel] at htransport
    rw [← Submodule.map_comp] at htransport
    have hcomp :
        (originalDTranslate ρ a).symm.toLinearMap.comp
            (originalDTranslate ρ b).toLinearMap =
          (originalDTranslate ρ (a⁻¹ * b)).toLinearMap := by
      ext x
      change ρ a⁻¹ (ρ b x) = ρ (a⁻¹ * b) x
      simp only [map_mul]
      rfl
    rw [hcomp] at htransport
    change originalDActualComponent ρ σ hσ (a⁻¹ * b) =
      originalDBaseComponent ρ σ hσ
    exact htransport.symm
  · intro hab
    change originalDActualComponent ρ σ hσ (a⁻¹ * b) =
      originalDBaseComponent ρ σ hσ at hab
    dsimp only [originalDActualComponent] at hab
    have hmul := originalDTranslate_mul ρ a (a⁻¹ * b)
    calc
      originalDActualComponent ρ σ hσ a =
          (originalDBaseComponent ρ σ hσ).map
            (originalDTranslate ρ a).toLinearMap := rfl
      _ = ((originalDBaseComponent ρ σ hσ).map
            (originalDTranslate ρ (a⁻¹ * b)).toLinearMap).map
              (originalDTranslate ρ a).toLinearMap := by rw [hab]
      _ = (originalDBaseComponent ρ σ hσ).map
            ((originalDTranslate ρ a).toLinearMap.comp
              (originalDTranslate ρ (a⁻¹ * b)).toLinearMap) := by
        rw [Submodule.map_comp]
      _ = (originalDBaseComponent ρ σ hσ).map
            (originalDTranslate ρ (a * (a⁻¹ * b))).toLinearMap := by
        rw [hmul]
      _ = originalDActualComponent ρ σ hσ b := by
        dsimp [originalDActualComponent]
        simp only [← mul_assoc, mul_inv_cancel, one_mul]

private theorem originalDActualComponent_eq_iff_component
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (a b : G) :
    (conjSubrepIsotypicComponent ρ σ hσ a) =
        conjSubrepIsotypicComponent ρ σ hσ b ↔
      a⁻¹ * b ∈ originalDActualInertia ρ σ hσ := by
  let D := Module.End k[G] ρ.asModule
  let M := (_root_.Representation.asModule (ρ.comp N.subtype))
  let C (c : isotypicComponents k[N] M) :=
    fullyInvariantDSubmodule D c.1
      (Submodule.IsFullyInvariant.of_mem_isotypicComponents c.2)
  have hC : Function.Injective C := by
    intro c d h
    apply Subtype.ext
    ext x
    change x ∈ c.1 ↔ x ∈ d.1
    have hx : x ∈ C c ↔ x ∈ C d := by rw [h]
    exact hx
  have hA : originalDActualComponent ρ σ hσ a =
      C (conjSubrepIsotypicComponent ρ σ hσ a) := by
    simpa [originalDActualComponent, C] using
      (originalDTranslate_map_component ρ σ hσ a)
  have hB : originalDActualComponent ρ σ hσ b =
      C (conjSubrepIsotypicComponent ρ σ hσ b) := by
    simpa [originalDActualComponent, C] using
      (originalDTranslate_map_component ρ σ hσ b)
  calc
    _ ↔ originalDActualComponent ρ σ hσ a =
        originalDActualComponent ρ σ hσ b := by rw [hA, hB, hC.eq_iff]
    _ ↔ _ := originalDActualComponent_eq_iff ρ σ hσ a b

private noncomputable def originalDActualComponentQuotientMap
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    G ⧸ originalDActualInertia ρ σ hσ →
      isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) := by
  let H := originalDActualInertia ρ σ hσ
  let componentAt (g : G) := conjSubrepIsotypicComponent ρ σ hσ g
  exact @Quotient.lift G _ (QuotientGroup.leftRel H) componentAt (by
    intro a b hab
    exact (originalDActualComponent_eq_iff_component ρ σ hσ a b).2
      (QuotientGroup.leftRel_apply.mp hab))

private theorem originalDActualComponentQuotientMap_mk
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    originalDActualComponentQuotientMap ρ σ hσ (QuotientGroup.mk g) =
      conjSubrepIsotypicComponent ρ σ hσ g := by
  rfl

private theorem originalDActualComponentQuotientMap_bijective
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    Function.Bijective (originalDActualComponentQuotientMap ρ σ hσ) := by
  constructor
  · intro q₁ q₂
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro a b hq
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr
      ((originalDActualComponent_eq_iff_component ρ σ hσ a b).1 hq)
  · intro c
    rcases c.2 with ⟨S, hS, hc⟩
    letI : IsSimpleModule k[N] S := hS
    obtain ⟨g, ⟨e⟩⟩ :=
      exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ S
    refine ⟨QuotientGroup.mk g, ?_⟩
    apply Subtype.ext
    change isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
      (conjSubrep ρ g σ).asSubmodule = c.1
    rw [hc, e.isotypicComponent_eq]

private noncomputable def originalDActualComponentQuotientEquiv
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃
      G ⧸ originalDActualInertia ρ σ hσ :=
  (Equiv.ofBijective (originalDActualComponentQuotientMap ρ σ hσ)
    (originalDActualComponentQuotientMap_bijective ρ σ hσ)).symm

private theorem originalDActualComponentQuotientEquiv_apply
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (g : G) :
    originalDActualComponentQuotientEquiv ρ σ hσ
      (conjSubrepIsotypicComponent ρ σ hσ g) =
        QuotientGroup.mk g := by
  change (Equiv.ofBijective
    (originalDActualComponentQuotientMap ρ σ hσ)
    (originalDActualComponentQuotientMap_bijective ρ σ hσ)).symm
      (conjSubrepIsotypicComponent ρ σ hσ g) = QuotientGroup.mk g
  apply (Equiv.ofBijective
    (originalDActualComponentQuotientMap ρ σ hσ)
    (originalDActualComponentQuotientMap_bijective ρ σ hσ)).injective
  rw [Equiv.apply_symm_apply]
  exact (originalDActualComponentQuotientMap_mk ρ σ hσ g).symm

/-- Independent-universe D-linear product over the quotient by the actual
component inertia. Every factor identification is induced by the proved
original-D translation/component image identity. -/
private noncomputable def originalDRestrictEquivPiIndependent
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    ρ.asModule ≃ₗ[Module.End k[G] ρ.asModule]
      ((q : G ⧸ originalDActualInertia ρ σ hσ) →
        originalDBaseComponent ρ σ hσ) := by
  classical
  let M := (_root_.Representation.asModule (ρ.comp N.subtype))
  let D := Module.End k[G] ρ.asModule
  let U := originalDBaseComponent ρ σ hσ
  let H := originalDActualInertia ρ σ hσ
  let A (c : isotypicComponents k[N] M) : Submodule k[N] M := c.1
  let hA (c : isotypicComponents k[N] M) : (A c).IsFullyInvariant :=
    Submodule.IsFullyInvariant.of_mem_isotypicComponents c.2
  let C (c : isotypicComponents k[N] M) := fullyInvariantDSubmodule D (A c) (hA c)
  let eidx := originalDActualComponentQuotientEquiv ρ σ hσ
  letI : IsSemisimpleModule k[N] M :=
    (_root_.Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
      (isSemisimpleRepresentation_comp_subtype ρ)
  letI : IsNoetherian k[N] M := isNoetherian_of_tower k inferInstance
  letI : Fintype (isotypicComponents k[N] M) := Fintype.ofFinite _
  have hcomponent (q : G ⧸ H) : U ≃ₗ[D] C (eidx.symm q) := by
    let g : G := Quotient.out q
    have hq : (QuotientGroup.mk g : G ⧸ H) = q := Quotient.out_eq' q
    have hc : eidx.symm q = conjSubrepIsotypicComponent ρ σ hσ g := by
      apply eidx.injective
      rw [eidx.apply_symm_apply, ← hq]
      exact (originalDActualComponentQuotientEquiv_apply ρ σ hσ g).symm
    have hmap : U.map (originalDTranslate ρ g).toLinearMap = C (eidx.symm q) := by
      rw [hc]
      simpa only [C, A, U, D, M] using
        (originalDTranslate_map_component ρ σ hσ g)
    exact (originalDTranslate ρ g).ofSubmodules U (C (eidx.symm q)) hmap
  exact (commutingDirectSumEquiv D A hA
      ((sSupIndep_iff _).mp (sSupIndep_isotypicComponents k[N] M))
      ((sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents k[N] M))).symm ≪≫ₗ
    DFinsupp.linearEquivFunOnFintype ≪≫ₗ
    LinearEquiv.piCongrLeft' D (fun c => C c) eidx ≪≫ₗ
    LinearEquiv.piCongrRight (fun q => (hcomponent q).symm)

/-- Independent-universe original-D Clifford rank formula. -/
theorem originalD_finrank_independent_universes
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    Module.finrank (Module.End k[G] ρ.asModule) ρ.asModule =
      (originalDActualInertia ρ σ hσ).index *
        Module.finrank (Module.End k[G] ρ.asModule)
          (originalDBaseComponent ρ σ hσ) := by
  classical
  let D := Module.End k[G] ρ.asModule
  let M := (_root_.Representation.asModule (ρ.comp N.subtype))
  let U := originalDBaseComponent ρ σ hσ
  let H := originalDActualInertia ρ σ hσ
  letI : DivisionRing D := inferInstance
  letI : Algebra k D := inferInstance
  letI : IsScalarTower k D ρ.asModule := inferInstance
  letI : Module.Finite D ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k D ρ.asModule
  letI : Module.Finite D M := by
    change Module.Finite D ρ.asModule
    infer_instance
  letI : Module.Finite D U :=
    Module.Finite.of_injective U.subtype Subtype.val_injective
  letI : IsNoetherian k[N] M := isNoetherian_of_tower k inferInstance
  let eidx := originalDActualComponentQuotientEquiv ρ σ hσ
  letI : Finite (G ⧸ H) := .of_equiv _ eidx
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  rw [(originalDRestrictEquivPiIndependent ρ σ hσ).finrank_eq,
    Module.finrank_pi_fintype]
  simp [Subgroup.index, Nat.card_eq_fintype_card]

end D5.S3.FiniteGroups.CliffordDecomposition.Representation
