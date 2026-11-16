/- GID: D5/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/Operations
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/Operations
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Needed two-sided-ideal operations for the attributed tensor simplicity proof. -/

/-
Classical algebra proofs used for the actual finite-group representation image.
Proof attribution: AxiomMath/Stacks contributors, Apache-2.0 (see upstream/LICENSE).
Pinned revision: 5ed82d14634e8d9576bb844c7bd4e3da66d450e7
Upstream: StacksCore/RingTheory/TwoSidedIdeal/Operations.lean
SHA-256: 46be68d41f8ac60c28a7391b92e845b00bde919b3b9e2244282293ce5b50fe61
The pinned source files contain no individual author or copyright notices.
Retirement: when the Mathlib revision pinned in this repository's lake-manifest.json
provides equivalent required declarations, replace the corresponding fragments
with direct Mathlib reuse and remove unused transplants. In this namespace these
are `map_le_iff_le_comap` for nonunital nonassociative rings and any FunLike
NonUnitalRingHomClass, `map_bot` with only ZeroHomClass on that FunLike family,
and `mem_map_of_mem` with no homomorphism-class assumption. For arbitrary unital
rings and FunLike families they are `map_eq_bot_iff_le_ker`,
`mem_map_iff_of_surjective` (surjective RingHomClass map with kernel contained in
I.asIdeal), `toTwoSided_le_iff` (I.IsTwoSided), `map_le_twoSided` (no homomorphism
class required), and `asIdeal_comap`; `map_eq_bot_iff_le_ker` and `asIdeal_comap`
require RingHomClass, without commutativity or finiteness assumptions.
-/

import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.TwoSidedIdeal.Operations

namespace D5.S3.RingTheory.TwoSidedIdeal.Operations

open _root_.TwoSidedIdeal

section NonUnitalNonAssoc

variable {R S F : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [FunLike F R S]

private lemma mem_image_of_mem_map_of_surjective [NonUnitalRingHomClass F R S] {f : F}
    (hf : Function.Surjective f) {I : TwoSidedIdeal R} {y} (H : y ∈ I.map f) :
    y ∈ f '' I :=
  span_induction (hx := H) (fun _ ↦ id) ⟨0, by simp⟩
    (fun _ _ _ _ ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩ ↦ ⟨a + b, I.add_mem ha hb, ha' ▸ hb' ▸ map_add ..⟩)
    (fun _ _ ⟨a, ha, ha'⟩ ↦ ⟨-a, I.neg_mem ha, ha' ▸ map_neg ..⟩)
    (fun c _ _ ⟨a, ha, ha'⟩ ↦
      let ⟨d, hd⟩ := hf c
      ⟨d * a, I.mul_mem_left _ _ ha, hd ▸ ha' ▸ map_mul ..⟩) <|
    fun b _ _ ⟨a, ha, ha'⟩ ↦
      let ⟨d, hd⟩ := hf b
      ⟨a * d, I.mul_mem_right _ _ ha, ha' ▸ hd ▸ map_mul ..⟩

private lemma comap_coe {f : F} [NonUnitalRingHomClass F R S] (I : TwoSidedIdeal S) :
    I.comap f = f ⁻¹' I := by ext; simp [mem_comap]

lemma map_le_iff_le_comap {f : F} [NonUnitalRingHomClass F R S] (I : TwoSidedIdeal R)
    (J : TwoSidedIdeal S) : I.map f ≤ J ↔ I ≤ J.comap f :=
  span_le.trans <| Set.image_subset_iff.trans <|
    (comap_coe (f := f) J).symm ▸ SetLike.coe_subset_coe

@[simp]
private lemma span_eq_bot {s : Set R} :
    span s = ⊥ ↔ ∀ x ∈ s, x = 0 := _root_.eq_bot_iff.trans
  ⟨fun H _ h => (mem_bot R).mp <| H <| subset_span h,
   fun H => span_le.mpr fun x h => (mem_bot R).mpr <| H x h⟩

private lemma span_singleton_eq_bot {x : R} :
    span ({x} : Set R) = ⊥ ↔ x = 0 := by simp

@[simp]
lemma map_bot [ZeroHomClass F R S] {f : F} :
    (⊥ : TwoSidedIdeal R).map f = ⊥ := by
  ext x
  simp [map, span_singleton_eq_bot.2]

theorem mem_map_of_mem {f : F} {I : TwoSidedIdeal R}
    {x : R} (hx : x ∈ I) : f x ∈ I.map f :=
  TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩

end NonUnitalNonAssoc

variable {R S F : Type*} [Ring R] [Ring S] [FunLike F R S]

@[simp]
private lemma bot_toTwoSided : (⊥ : Ideal R).toTwoSided = ⊥ := by ext; simp

private lemma comap_toTwoSided (f : F) (I : Ideal S) [RingHomClass F R S] [I.IsTwoSided] :
    (I.comap f).toTwoSided = (I.toTwoSided).comap f := by
  ext; simp [mem_comap]

lemma map_eq_bot_iff_le_ker {f : F} [RingHomClass F R S] (I : TwoSidedIdeal R) :
    I.map f = ⊥ ↔ I ≤ (RingHom.ker f).toTwoSided := by
  unfold RingHom.ker
  rw [comap_toTwoSided, bot_toTwoSided, ← map_le_iff_le_comap, le_bot_iff]

lemma mem_map_iff_of_surjective [RingHomClass F R S] {f : F} (hf : Function.Surjective f)
    {I : TwoSidedIdeal R} (hker : RingHom.ker f ≤ I.asIdeal) {x : R} :
    f x ∈ I.map f ↔ x ∈ I := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_map_of_mem h⟩
  obtain ⟨z, hz, hzx⟩ := mem_image_of_mem_map_of_surjective hf h
  have hxz : x - z ∈ RingHom.ker f := by rw [RingHom.mem_ker, map_sub, hzx, sub_self]
  simpa using I.add_mem (mem_asIdeal.1 (hker hxz)) hz

lemma toTwoSided_le_iff {I : Ideal R} [I.IsTwoSided] {J : TwoSidedIdeal R} :
    I.toTwoSided ≤ J ↔ I ≤ J.asIdeal :=
  ⟨fun h _ hx ↦ mem_asIdeal.2 <| h <| Ideal.mem_toTwoSided.2 hx,
   fun h _ hx ↦ mem_asIdeal.1 <| h <| Ideal.mem_toTwoSided.1 hx⟩

private lemma span_le_twoSided (s : Set R) :
    Ideal.span s ≤ (span s).asIdeal := fun x hx ↦ by
  simp only [Ideal.mem_span, mem_asIdeal, mem_span_iff] at hx ⊢
  exact fun I hI ↦ by simpa using hx I.asIdeal (by simpa using hI)

lemma map_le_twoSided {f : F} (I : TwoSidedIdeal R) :
    I.asIdeal.map f ≤ (I.map f).asIdeal := span_le_twoSided _

@[simp]
lemma asIdeal_comap {f : F} [RingHomClass F R S] (I : TwoSidedIdeal S) :
    (I.comap f).asIdeal = I.asIdeal.comap f := by
  ext
  simp [mem_comap]

end D5.S3.RingTheory.TwoSidedIdeal.Operations
