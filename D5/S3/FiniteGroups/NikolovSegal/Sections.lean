/- GID: D5/S3/FiniteGroups/NikolovSegal/Sections
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Sections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary subgroup sections and the simple-section image/kernel dichotomy. -/

import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

set_option autoImplicit false

namespace NikolovSegal

universe u v w

/-- A section is a quotient of an arbitrary subgroup. -/
def Involves (A : Type u) (G : Type v) [Group A] [Group G] : Prop :=
  ∃ H : Subgroup G, ∃ f : H →* A, Function.Surjective f

variable {A : Type u} {G : Type v} {Q : Type w}
  [Group A] [Group G] [Group Q]

theorem involves_of_surjective (f : G →* A) (hf : Function.Surjective f) :
    Involves A G := by
  refine ⟨⊤, f.comp (⊤ : Subgroup G).subtype, ?_⟩
  intro a
  obtain ⟨g, hg⟩ := hf a
  exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩

theorem involves_of_injective (i : G →* Q) (hi : Function.Injective i)
    (h : Involves A G) : Involves A Q := by
  obtain ⟨H, f, hf⟩ := h
  let e := H.equivMapOfInjective i hi
  exact ⟨H.map i, f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective⟩

/-- A simple section of an extension occurs in its kernel or in its image.
The codomain need not equal the image, and the section subgroup is arbitrary. -/
theorem simple_involves_map_or_kernel [IsSimpleGroup A]
    (q : G →* Q) (h : Involves A G) :
    Involves A Q ∨ Involves A q.ker := by
  classical
  obtain ⟨H, f, hf⟩ := h
  let K : Subgroup H := q.ker.comap H.subtype
  have : K.Normal := Subgroup.normal_comap _
  have : (K.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases Subgroup.Normal.eq_bot_or_eq_top (inferInstance : (K.map f).Normal) with hbot | htop
  · left
    let r := q.subgroupMap H
    have hr : Function.Surjective r := q.subgroupMap_surjective H
    have hker : r.ker ≤ f.ker := by
      intro x hx
      have hxK : x ∈ K := by
        change q (x : G) = 1
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      have hfx : f x ∈ K.map f := Subgroup.mem_map.mpr ⟨x, hxK, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hfx
      exact MonoidHom.mem_ker.mpr hfx
    let t : H.map q →* A := r.liftOfSurjective hr ⟨f, hker⟩
    refine ⟨H.map q, t, ?_⟩
    intro a
    obtain ⟨x, hx⟩ := hf a
    refine ⟨r x, ?_⟩
    change (r.liftOfRightInverse (Function.surjInv hr)
      (Function.rightInverse_surjInv hr) ⟨f, hker⟩) (r x) = a
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    exact hx
  · right
    have hs : Function.Surjective (f.comp K.subtype) := by
      intro a
      have ha : a ∈ K.map f := htop ▸ Subgroup.mem_top a
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
      exact ⟨⟨x, hx⟩, hxa⟩
    let i : K →* q.ker :=
      (H.subtype.comp K.subtype).codRestrict q.ker (fun x => x.property)
    have hi : Function.Injective i := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : q.ker => (z : G)) hxy
    exact involves_of_injective i hi (involves_of_surjective _ hs)

theorem involves_card_dvd [Finite G] (h : Involves A G) :
    Nat.card A ∣ Nat.card G := by
  obtain ⟨H, f, hf⟩ := h
  exact (Subgroup.card_dvd_of_surjective f hf).trans H.card_subgroup_dvd_card

theorem not_involves_of_prime_dvd {p : ℕ} [Finite G]
    (hA : p ∣ Nat.card A) (hG : ¬p ∣ Nat.card G) : ¬Involves A G := by
  intro h
  exact hG (hA.trans (involves_card_dvd h))

theorem not_involves_pGroup {p : ℕ} (hG : IsPGroup p G)
    (hA : ¬IsPGroup p A) : ¬Involves A G := by
  rintro ⟨H, f, hf⟩
  exact hA ((hG.to_subgroup H).of_surjective f hf)

end NikolovSegal
