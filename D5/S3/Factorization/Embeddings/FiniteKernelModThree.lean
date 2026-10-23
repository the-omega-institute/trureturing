/- GID: D5/S3/Factorization/Embeddings/FiniteKernelModThree
   generality: G
   mirror-B: D5/B/S3/Factorization/Embeddings/FiniteKernelModThree
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Finite-kernel descent bounds original unit cube quotients by Dirichlet rank. -/
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.Abel
import D5.S3.Factorization.Embeddings.DirichletUnitCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The pinned ModN supplier itself uses this elaboration option at quotient bridges.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Factorization.Embeddings.FiniteKernelModThree

open Function

section Descent

variable {A L : Type*} [AddCommGroup A] [AddCommGroup L]
variable (f : A →+ L) (hf : Surjective f) [Finite f.ker]
variable (h3 : ∀ a : A, (3 : ℕ) • a = 0 → a = 0)

include hf h3

/-- The substantive preimage calculation, before taking any quotient.
The correction term is solved inside the finite kernel, hence inside A. -/
private theorem preimage_triples (a : A) :
    f a ∈ LinearMap.range (LinearMap.lsmul ℤ L (3 : ℤ)) ↔
      a ∈ LinearMap.range (LinearMap.lsmul ℤ A (3 : ℤ)) := by
  have h3z (x : A) (hx : (3 : ℤ) • x = 0) : x = 0 := by
    apply h3 x
    simpa only [ofNat_zsmul] using hx
  constructor
  · rintro ⟨l, hl⟩
    change (3 : ℤ) • l = f a at hl
    obtain ⟨v, hv⟩ := hf l
    let k : f.ker := ⟨a - (3 : ℤ) • v, by
      change f (a - (3 : ℤ) • v) = 0
      rw [map_sub, map_zsmul, hv, hl, sub_self]⟩
    have hmul : Injective (fun t : f.ker => (3 : ℤ) • t) := by
      intro x y hxy
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply h3z
      have hxy' : (3 : ℤ) • (x : A) = (3 : ℤ) • (y : A) :=
        congrArg (fun t : f.ker => (t : A)) hxy
      rw [smul_sub, hxy', sub_self]
    obtain ⟨t, ht⟩ := Finite.surjective_of_injective hmul k
    have ht' : (3 : ℤ) • (t : A) = a - (3 : ℤ) • v :=
      congrArg (fun t : f.ker => (t : A)) ht
    refine ⟨v + (t : A), ?_⟩
    change (3 : ℤ) • (v + (t : A)) = a
    rw [smul_add, ht']
    abel
  · rintro ⟨v, hv⟩
    change (3 : ℤ) • v = a at hv
    refine ⟨f v, ?_⟩
    change (3 : ℤ) • f v = f a
    simpa only [map_zsmul] using congrArg f hv

/-- The map induced by f is a ZMod 3 linear equivalence.
No finite-generation or freeness of A or L is needed for this descent. -/
noncomputable def modThreeEquiv : ModN A 3 ≃ₗ[ZMod 3] ModN L 3 := by
  let φ : A →+ ModN L 3 := (ModN.mkQ (G := L) 3).comp f
  have hφ : Surjective φ :=
    (LinearMap.range (LinearMap.lsmul ℤ L (3 : ℤ))).mkQ_surjective.comp hf
  have hker :
      (LinearMap.range (LinearMap.lsmul ℤ A (3 : ℤ))).toAddSubgroup = φ.ker := by
    ext a
    change a ∈ LinearMap.range (LinearMap.lsmul ℤ A (3 : ℤ)) ↔
      (Submodule.Quotient.mk (f a) : ModN L 3) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (preimage_triples f hf h3 a).symm
  let e : ModN A 3 ≃+ ModN L 3 :=
    QuotientAddGroup.liftEquiv
      (LinearMap.range (LinearMap.lsmul ℤ A (3 : ℤ))).toAddSubgroup hφ hker
  exact LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap 3) e.bijective

variable [Module.Free ℤ L] [Module.Finite ℤ L]

/-- Finite-kernel descent and the existing reduced integral basis
give actual finite dimensionality and the exact dimension. -/
theorem modThree_finite_finrank :
    Module.Finite (ZMod 3) (ModN A 3) ∧
      Module.finrank (ZMod 3) (ModN A 3) = Module.finrank ℤ L := by
  let e := modThreeEquiv f hf h3
  constructor
  · exact Module.Finite.equiv e.symm
  · calc
      Module.finrank (ZMod 3) (ModN A 3) =
          Module.finrank (ZMod 3) (ModN L 3) := e.finrank_eq
      _ = Fintype.card (Fin (Module.finrank ℤ L)) :=
        Module.finrank_eq_card_basis
          (ModN.basis (n := 3) (Module.finBasis ℤ L))
      _ = Module.finrank ℤ L := Fintype.card_fin _

end Descent

section OrderUnitConsumer

open NumberField
open D5.S3.Factorization.Embeddings.DirichletUnitCompletion

variable {K U : Type*} [Field K] [NumberField K] [CommGroup U]

/-- Apply to the actual original order units U, embedded into integer
units of K. The free-coordinate codomain is restricted to its actual range.
The only arithmetic premises are the unit embedding and absence of 3-torsion.
In particular, no quotient embedding or pre-existing rank bound is a premise. -/
theorem embedded_units_modThree
    (i : U →* (𝓞 K)ˣ) (hi : Injective i)
    (h3 : ∀ u : U, u ^ (3 : ℕ) = 1 → u = 1) :
    Module.Finite (ZMod 3) (ModN (Additive U) 3) ∧
      Module.finrank (ZMod 3) (ModN (Additive U) 3) ≤ NumberField.Units.rank K := by
  let s : U →* NumberField.Units.torsion K ×
      Multiplicative (Fin (NumberField.Units.rank K) → ℤ) :=
    (unitCompletionMulEquiv K).toMonoidHom.comp i
  have hs : Injective s := (unitCompletionMulEquiv K).injective.comp hi
  let c : U →* Multiplicative (Fin (NumberField.Units.rank K) → ℤ) :=
    (MonoidHom.snd _ _).comp s
  let l : Additive U →ₗ[ℤ] (Fin (NumberField.Units.rank K) → ℤ) :=
    c.toAdditiveLeft.toIntLinearMap
  let L : Submodule ℤ (Fin (NumberField.Units.rank K) → ℤ) := LinearMap.range l
  let f : Additive U →+ L := l.rangeRestrict.toAddMonoidHom
  have hf : Surjective f := LinearMap.surjective_rangeRestrict l
  -- Finite generation of L comes from its inclusion in the finite free lattice.
  letI : Module.Finite ℤ L := Module.Finite.of_injective L.subtype Subtype.val_injective
  -- Submodule.instIsTorsionFree and the PID instance give freeness of L.
  letI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  -- On ker f the free coordinate vanishes. The torsion coordinate alone is injective.
  let τ : f.ker → NumberField.Units.torsion K := fun a => (s a.val.toMul).1
  have hτ : Injective τ := by
    intro a b hab
    have ha : l a.val = 0 := by
      have ha' : f a.val = 0 := a.property
      exact congrArg (fun x : L => (x : Fin (NumberField.Units.rank K) → ℤ)) ha'
    have hb : l b.val = 0 := by
      have hb' : f b.val = 0 := b.property
      exact congrArg (fun x : L => (x : Fin (NumberField.Units.rank K) → ℤ)) hb'
    have hsecond : (s a.val.toMul).2 = (s b.val.toMul).2 := by
      apply Multiplicative.toAdd.injective
      change l a.val = l b.val
      exact ha.trans hb.symm
    have hpair : s a.val.toMul = s b.val.toMul :=
      Prod.ext hab hsecond
    apply Subtype.ext
    exact Additive.toMul.injective (hs hpair)
  letI : Finite f.ker := Finite.of_injective τ hτ
  have h3add : ∀ a : Additive U, (3 : ℕ) • a = 0 → a = 0 := by
    intro a ha
    apply Additive.toMul.injective
    apply h3 a.toMul
    have hp := congrArg (fun x : Additive U => x.toMul) ha
    change a.toMul ^ (3 : ℕ) = 1 at hp
    exact hp
  obtain ⟨hfinite, hdim⟩ := modThree_finite_finrank f hf h3add
  refine ⟨hfinite, ?_⟩
  calc
    Module.finrank (ZMod 3) (ModN (Additive U) 3) = Module.finrank ℤ L := hdim
    _ ≤ Module.finrank ℤ (Fin (NumberField.Units.rank K) → ℤ) := Submodule.finrank_le L
    _ = NumberField.Units.rank K := by
      rw [Module.finrank_pi, Fintype.card_fin]

/-- A quotient equality produces a cube root in the original U.
This is the final witness extraction consumed by the q4 character/basis argument. -/
theorem exists_original_cube_of_quotient_eq (u v : U)
    (h : ModN.mkQ (G := Additive U) 3 (Additive.ofMul u) =
      ModN.mkQ (G := Additive U) 3 (Additive.ofMul v)) :
    ∃ w : U, u = v * w ^ (3 : ℕ) := by
  have hz : ModN.mkQ (G := Additive U) 3
      (Additive.ofMul u - Additive.ofMul v) = 0 := by
    rw [map_sub, h, sub_self]
  have hmem : Additive.ofMul u - Additive.ofMul v ∈
      LinearMap.range (LinearMap.lsmul ℤ (Additive U) (3 : ℤ)) :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨w, hw⟩ := hmem
  change (3 : ℤ) • w = Additive.ofMul u - Additive.ofMul v at hw
  have hw' : (3 : ℕ) • w = Additive.ofMul u - Additive.ofMul v := by
    simpa only [ofNat_zsmul] using hw
  have hp := congrArg (fun x : Additive U => x.toMul) hw'
  change w.toMul ^ (3 : ℕ) = u / v at hp
  refine ⟨w.toMul, ?_⟩
  calc
    u = (u / v) * v := (div_mul_cancel u v).symm
    _ = w.toMul ^ (3 : ℕ) * v := by rw [hp]
    _ = v * w.toMul ^ (3 : ℕ) := mul_comm _ _

end OrderUnitConsumer

end D5.S3.Factorization.Embeddings.FiniteKernelModThree
