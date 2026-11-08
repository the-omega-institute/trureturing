/- GID: D5/S3/FiniteGroups/Frobenius/OriginalDProjective
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Frobenius/OriginalDProjective
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Projectivity from actual original-D regular coordinates and relative trace. -/

import D5.S3.FiniteGroups.Frobenius.OriginalDFrobenius
import Mathlib.Algebra.Module.Projective
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
Actual regular coordinates construct a complement-equivariant section without
division. A relative trace over left cosets then splits the original module
surjection after dividing only by the order of the Frobenius kernel.
-/

noncomputable section

namespace D5.S3.FiniteGroups.OriginalDFrobenius

open scoped MonoidAlgebra
open OriginalDCliffordCandidate

universe uk uG uV uP

set_option backward.isDefEq.respectTransparency false

variable {k : Type uk} [Field k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]

private theorem coordinate_section [Finite G] (ρ : Representation k G V)
    (C : Subgroup G) (S : Submodule (Module.End k[G] ρ.asModule) ρ.asModule)
    (E : ρ.asModule ≃ₗ[Module.End k[G] ρ.asModule] (C → S))
    (hE : ∀ (c : C) (v : ρ.asModule) (x : C),
      E (originalDTranslate ρ c v) x = E v (c⁻¹ * x))
    {P : Type uP} [AddCommGroup P] [Module k P] [Module k[G] P]
    [IsScalarTower k k[G] P]
    (f : P →ₗ[k[G]] ρ.asModule) (hf : Function.Surjective f) :
    ∃ s : ρ.asModule →ₗ[k] P, (∀ v, f (s v) = v) ∧
      ∀ (c : C) (v : ρ.asModule),
        s (MonoidAlgebra.single (c : G) (1 : k) • v) =
          MonoidAlgebra.single (c : G) (1 : k) • s v := by
  classical
  let : Fintype C := Fintype.ofFinite C
  let D := Module.End k[G] ρ.asModule
  let : Algebra k D := inferInstance
  let : IsScalarTower k D ρ.asModule := inferInstance
  let : Module k S := inferInstanceAs (Module k (S.restrictScalars k))
  let e : ρ.asModule ≃ₗ[k] (C → S) := E.restrictScalars k
  obtain ⟨t, ht⟩ := (f.restrictScalars k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  have ht' (v : ρ.asModule) : f (t v) = v := LinearMap.congr_fun ht v
  let j : S →ₗ[k] ρ.asModule :=
    e.symm.toLinearMap.comp (LinearMap.single k (fun _ : C => S) 1)
  let aW : G → (ρ.asModule →ₗ[k] ρ.asModule) :=
    MonoidAlgebra.GroupSMul.linearMap k ρ.asModule
  let aP : G → (P →ₗ[k] P) := MonoidAlgebra.GroupSMul.linearMap k P
  have he (c : C) (v : ρ.asModule) (x : C) :
      e (aW c v) x = e v (c⁻¹ * x) := by
    change E (MonoidAlgebra.single (c : G) (1 : k) • v) x = E v (c⁻¹ * x)
    rw [Representation.single_smul, one_smul]
    exact hE c v x
  have hj (c : C) (z : S) : e (aW c (j z)) = Pi.single c z := by
    funext x
    rw [he]
    change e (e.symm (Pi.single 1 z)) (c⁻¹ * x) = (Pi.single c z : C → S) x
    rw [e.apply_symm_apply]
    by_cases hx : x = c
    · subst x
      simp
    · have hx' : c⁻¹ * x ≠ 1 := by
        intro hh
        apply hx
        calc
          x = c * (c⁻¹ * x) := (mul_inv_cancel_left c x).symm
          _ = c := by rw [hh, mul_one]
      simp [hx, hx']
  let s : ρ.asModule →ₗ[k] P := ∑ c : C,
    (aP c).comp (t.comp (j.comp ((LinearMap.proj c).comp e.toLinearMap)))
  have hs (v : ρ.asModule) :
      s v = ∑ c : C, aP c (t (j (e v c))) := by
    simp [s, LinearMap.sum_apply]
  refine ⟨s, ?_, ?_⟩
  · intro v
    rw [hs, map_sum]
    have hterm (c : C) : f (aP c (t (j (e v c)))) = aW c (j (e v c)) := by
      change f (MonoidAlgebra.single (c : G) (1 : k) • _) = _
      rw [f.map_smul, ht']
      rfl
    simp_rw [hterm]
    apply e.injective
    rw [map_sum]
    simp_rw [hj]
    exact LinearMap.sum_single_apply (fun _ : C => S) (e v)
  · intro d v
    change s (aW d v) = aP d (s v)
    rw [hs, hs, map_sum]
    simp_rw [he]
    refine Fintype.sum_bijective (fun x : C => d⁻¹ * x) (Group.mulLeft_bijective d⁻¹)
      _ _ (fun x => ?_)
    simp only [aP, MonoidAlgebra.GroupSMul.linearMap_apply]
    rw [← mul_smul, MonoidAlgebra.single_mul_single, one_mul]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

private theorem coset_trace [Finite G] (ρ : Representation k G V) (C : Subgroup G)
    {P : Type uP} [AddCommGroup P] [Module k P] [Module k[G] P]
    [IsScalarTower k k[G] P]
    (f : P →ₗ[k[G]] ρ.asModule) (s : ρ.asModule →ₗ[k] P)
    (hs : ∀ v, f (s v) = v)
    (hc : ∀ (c : C) (v : ρ.asModule),
      s (MonoidAlgebra.single (c : G) (1 : k) • v) =
        MonoidAlgebra.single (c : G) (1 : k) • s v) :
    ∃ T : ρ.asModule →ₗ[k[G]] P, ∀ v, f (T v) = C.index • v := by
  classical
  let : Fintype (G ⧸ C) := Fintype.ofFinite (G ⧸ C)
  let aW : G → (ρ.asModule →ₗ[k] ρ.asModule) :=
    MonoidAlgebra.GroupSMul.linearMap k ρ.asModule
  let aP : G → (P →ₗ[k] P) := MonoidAlgebra.GroupSMul.linearMap k P
  let A (g : G) : ρ.asModule →ₗ[k] P := (aP g).comp (s.comp (aW g⁻¹))
  have hrep (g : G) (c : C) : A (g * c) = A g := by
    apply LinearMap.ext
    intro v
    change MonoidAlgebra.single (g * c) (1 : k) •
        s (MonoidAlgebra.single ((g * c)⁻¹) (1 : k) • v) =
      MonoidAlgebra.single g (1 : k) • s (MonoidAlgebra.single g⁻¹ (1 : k) • v)
    have hinner : MonoidAlgebra.single ((g * c)⁻¹) (1 : k) • v =
        MonoidAlgebra.single ((c⁻¹ : C) : G) (1 : k) •
          (MonoidAlgebra.single g⁻¹ (1 : k) • v) := by
      rw [← mul_smul, MonoidAlgebra.single_mul_single, one_mul]
      simp only [mul_inv_rev, Subgroup.coe_inv]
    rw [hinner, hc c⁻¹, ← mul_smul, MonoidAlgebra.single_mul_single, one_mul]
    simp only [Subgroup.coe_inv, mul_inv_cancel_right]
  let B : (G ⧸ C) → (ρ.asModule →ₗ[k] P) :=
    @Quotient.lift G _ (QuotientGroup.leftRel C) A (by
      intro a b hab
      simpa only [mul_inv_cancel_left] using
        (hrep a ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩).symm)
  have hcov (h : G) (q : G ⧸ C) (v : ρ.asModule) :
      B (h • q) (aW h v) = aP h (B q v) := by
    refine Quotient.inductionOn q ?_
    intro g
    change MonoidAlgebra.single (h * g) (1 : k) •
        s (MonoidAlgebra.single ((h * g)⁻¹) (1 : k) •
          (MonoidAlgebra.single h (1 : k) • v)) =
      MonoidAlgebra.single h (1 : k) •
        (MonoidAlgebra.single g (1 : k) • s (MonoidAlgebra.single g⁻¹ (1 : k) • v))
    simp only [← mul_smul, MonoidAlgebra.single_mul_single,
      mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hB (q : G ⧸ C) (v : ρ.asModule) : f (B q v) = v := by
    refine Quotient.inductionOn q ?_
    intro g
    change f (MonoidAlgebra.single g (1 : k) •
      s (MonoidAlgebra.single g⁻¹ (1 : k) • v)) = v
    rw [f.map_smul, hs]
    simp only [← mul_smul, MonoidAlgebra.single_mul_single, one_mul,
      mul_inv_cancel, ← MonoidAlgebra.one_def, one_smul]
  let T : ρ.asModule →ₗ[k] P := ∑ q : G ⧸ C, B q
  have hT (h : G) (v : ρ.asModule) : T (aW h v) = aP h (T v) := by
    simp only [T, LinearMap.sum_apply, map_sum]
    symm
    exact Fintype.sum_bijective (fun q : G ⧸ C => h • q) (MulAction.bijective h)
      _ _ (fun q => (hcov h q v).symm)
  refine ⟨MonoidAlgebra.equivariantOfLinearOfComm T hT, ?_⟩
  intro v
  change f (T v) = C.index • v
  simp only [T, LinearMap.sum_apply, map_sum, hB, Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, ← C.index_eq_card]

/-- The actual original-D Frobenius module is projective when the kernel order
is invertible in the coefficient field. Only the kernel order is divided out. -/
theorem projective_originalD [Finite G]
    (N : Subgroup G) [N.Normal] (ρ : Representation k G V)
    [FiniteDimensional k V] [ρ.IsIrreducible]
    (hfix : ∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (hnt : ¬ Representation.IsTrivial (ρ.comp N.subtype))
    (hunit : IsUnit (Nat.card N : k)) :
    Module.Projective k[G] ρ.asModule := by
  classical
  obtain ⟨C, hC, S, E, hE⟩ := exists_complement_originalD_regular N ρ hfix hnt
  apply Module.Projective.of_lifting_property''
  intro f hf
  obtain ⟨s, hs, hc⟩ := coordinate_section ρ C S E hE f hf
  obtain ⟨T, hT⟩ := coset_trace ρ C f s hs hc
  refine ⟨(Nat.card N : k)⁻¹ • T, ?_⟩
  apply LinearMap.ext
  intro v
  change f ((Nat.card N : k)⁻¹ • T v) = v
  rw [f.map_smul_of_tower, hT, hC.index_eq_card, ← Nat.cast_smul_eq_nsmul k,
    smul_smul, inv_mul_cancel₀ hunit.ne_zero, one_smul]

end D5.S3.FiniteGroups.OriginalDFrobenius
