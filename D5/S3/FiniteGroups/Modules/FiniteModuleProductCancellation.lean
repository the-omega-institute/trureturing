/- GID: D5/S3/FiniteGroups/Modules/FiniteModuleProductCancellation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Modules/FiniteModuleProductCancellation
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Finite module products admit cancellation by counting linear maps and their kernels. -/

module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

/-! Cancellation for finite modules, using the decomposition of linear maps by kernel. -/

@[expose] public section

namespace D5.S3.FiniteGroups.FiniteModuleProductCancellation

open Function
open scoped BigOperators

set_option autoImplicit false

universe u v w x y

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {A : Type w} {B : Type x} {C : Type y} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

private def injectiveMaps (R : Type u) [Ring R] (M : Type v) (A : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup A] [Module R A] :=
  {f : M →ₗ[R] A // Injective f}

private instance finiteLinearMaps [Finite M] [Finite A] : Finite (M →ₗ[R] A) :=
  Finite.of_injective (fun f : M →ₗ[R] A => (f : M → A)) LinearMap.coe_injective

private instance finiteSubmodules [Finite M] : Finite (Submodule R M) :=
  Finite.of_injective (fun P : Submodule R M => (P : Set M)) SetLike.coe_injective

private instance finiteQuotient [Finite M] (P : Submodule R M) : Finite (M ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

private instance finiteInjectiveMaps [Finite M] [Finite A] : Finite (injectiveMaps R M A) := by
  unfold injectiveMaps
  infer_instance

private def byKernel : (Σ P : Submodule R M, injectiveMaps R (M ⧸ P) A) → M →ₗ[R] A :=
  fun f => (f.2.val).comp f.1.mkQ

private noncomputable def kernelDecomposition :
    (Σ P : Submodule R M, injectiveMaps R (M ⧸ P) A) ≃ (M →ₗ[R] A) :=
  Equiv.ofBijective byKernel ⟨by
    rintro ⟨P, f⟩ ⟨Q, g⟩ h
    have kernel_eq (S : Submodule R M) (k : injectiveMaps R (M ⧸ S) A) :
        LinearMap.ker (byKernel ⟨S, k⟩) = S := by
      change LinearMap.ker (k.val.comp S.mkQ) = S
      rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr k.prop), Submodule.ker_mkQ]
    have hPQ := congrArg LinearMap.ker h
    rw [kernel_eq, kernel_eq] at hPQ
    subst Q
    have hfg : f = g := by
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := P.mkQ_surjective x
      exact congrArg (fun l : M →ₗ[R] A => l y) h
    rw [hfg], by
    intro f
    let P := LinearMap.ker f
    let g := P.liftQ f le_rfl
    have hg : Injective g := LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' P f rfl)
    exact ⟨⟨P, g, hg⟩, Submodule.liftQ_mkQ P f le_rfl⟩⟩

private theorem card_maps_eq_sum [Finite M] [Finite A] [Fintype (Submodule R M)] :
    Nat.card (M →ₗ[R] A) = ∑ P : Submodule R M, Nat.card (injectiveMaps R (M ⧸ P) A) :=
  (Nat.card_congr (kernelDecomposition (R := R) (M := M) (A := A)).symm).trans Nat.card_sigma

private theorem card_quotient_lt [Finite M] (P : Submodule R M) (hP : P ≠ ⊥) :
    Nat.card (M ⧸ P) < Nat.card M := by
  let _ := Fintype.ofFinite M
  let _ := Fintype.ofFinite (M ⧸ P)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_surjective_not_injective P.mkQ P.mkQ_surjective
  intro hinj
  exact hP (P.ker_mkQ.symm.trans (LinearMap.ker_eq_bot.mpr hinj))

private def injectiveMapsCongr (e : M ≃ₗ[R] C) : injectiveMaps R M A ≃ injectiveMaps R C A where
  toFun f := ⟨f.val.comp e.symm.toLinearMap, f.prop.comp e.symm.injective⟩
  invFun f := ⟨f.val.comp e.toLinearMap, f.prop.comp e.injective⟩
  left_inv f := Subtype.ext (LinearMap.ext fun x => by simp)
  right_inv f := Subtype.ext (LinearMap.ext fun x => by simp)

private theorem card_injectiveMaps_eq [Finite A] [Finite B]
    (h : ∀ (X : Type w) [AddCommGroup X] [Module R X] [Finite X],
      Nat.card (X →ₗ[R] A) = Nat.card (X →ₗ[R] B)) (n : ℕ) :
    ∀ (X : Type w) [AddCommGroup X] [Module R X] [Finite X], Nat.card X = n →
      Nat.card (injectiveMaps R X A) = Nat.card (injectiveMaps R X B) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ _ _ hX
    classical
    let _ := Fintype.ofFinite (Submodule R X)
    have hsum := h X
    rw [card_maps_eq_sum, card_maps_eq_sum] at hsum
    let S := (Finset.univ : Finset (Submodule R X)).erase ⊥
    have htail : (∑ P ∈ S, Nat.card (injectiveMaps R (X ⧸ P) A)) =
        ∑ P ∈ S, Nat.card (injectiveMaps R (X ⧸ P) B) := by
      apply Finset.sum_congr rfl
      intro P hp
      have hP : P ≠ ⊥ := (Finset.mem_erase.mp hp).1
      exact ih _ (hX ▸ card_quotient_lt P hP) (X ⧸ P) rfl
    have hbot : Nat.card (injectiveMaps R (X ⧸ (⊥ : Submodule R X)) A) =
        Nat.card (injectiveMaps R (X ⧸ (⊥ : Submodule R X)) B) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⊥ : Submodule R X)),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ (⊥ : Submodule R X))] at hsum
      exact Nat.add_left_cancel (htail ▸ hsum)
    let bot : (X ⧸ (⊥ : Submodule R X)) ≃ₗ[R] X := Submodule.quotEquivOfEqBot _ rfl
    exact (Nat.card_congr (injectiveMapsCongr (A := A) bot)).symm.trans
      (hbot.trans (Nat.card_congr (injectiveMapsCongr (A := B) bot)))

/-- Cancelling a common finite factor in a linear equivalence of products.
Linear maps from a finite source are enumerated by their kernel and an
injection from the quotient. The equality of map counts determines the
injection counts by induction on the size of the source. -/
theorem finite_prod_cancel [Finite A] [Finite B] [Finite C]
    (e : (A × C) ≃ₗ[R] (B × C)) : Nonempty (A ≃ₗ[R] B) := by
  have hcard := Nat.card_congr e.toEquiv
  rw [Nat.card_prod, Nat.card_prod] at hcard
  have hAB : Nat.card A = Nat.card B := Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard
  have hMaps (X : Type w) [AddCommGroup X] [Module R X] [Finite X] :
      Nat.card (X →ₗ[R] A) = Nat.card (X →ₗ[R] B) := by
    let equiv : (X →ₗ[R] (A × C)) ≃+ (X →ₗ[R] (B × C)) :=
      (LinearEquiv.refl R X).arrowCongrAddEquiv e
    have h := Nat.card_congr equiv.toEquiv
    rw [← Nat.card_congr (LinearEquiv.toEquiv (σ := RingHom.id ℤ)
          (LinearMap.prodEquiv (S := ℤ) (M := X) (M₂ := A) (M₃ := C))),
      ← Nat.card_congr (LinearEquiv.toEquiv (σ := RingHom.id ℤ)
          (LinearMap.prodEquiv (S := ℤ) (M := X) (M₂ := B) (M₃ := C))),
      Nat.card_prod, Nat.card_prod] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hinj := card_injectiveMaps_eq hMaps (Nat.card A) A rfl
  have hpos : 0 < Nat.card (injectiveMaps R A A) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨LinearMap.id, Function.injective_id⟩⟩, inferInstance⟩
  obtain ⟨⟨f, hf⟩⟩ := (Nat.card_pos_iff.mp (hinj ▸ hpos)).1
  exact ⟨LinearEquiv.ofBijective f (hf.bijective_of_nat_card_le hAB.ge)⟩

end D5.S3.FiniteGroups.FiniteModuleProductCancellation
