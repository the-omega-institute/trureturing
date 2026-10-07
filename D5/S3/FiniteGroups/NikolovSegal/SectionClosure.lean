/- GID: D5/S3/FiniteGroups/NikolovSegal/SectionClosure
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/SectionClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Alternating-section bounds are preserved by subgroups, quotients, and extensions. -/

import D5.S3.FiniteGroups.NikolovSegal.NikolovSegalLemma2

set_option autoImplicit false

/-!
Closure properties for the class in Nikolov--Segal (2011), Proposition 3.
`Involves` always means a quotient of an arbitrary subgroup. The extension
argument uses simplicity only in alternating degrees at least five.
-/

namespace NikolovSegal

universe u v w
variable {G : Type u} {Q : Type v} {A : Type w}
  [Group G] [Group Q] [Group A]

/-- Every section of a surjective image lifts to a section of the source. -/
theorem involves_of_surjective_image (q : G →* Q) (hq : Function.Surjective q)
    (h : Involves A Q) : Involves A G := by
  obtain ⟨H, f, hf⟩ := h
  let r : H.comap q →* H :=
    (q.comp (H.comap q).subtype).codRestrict H (fun x => x.property)
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨g, hg⟩ := hq x
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change q g ∈ H
      rw [hg]
      exact x.property
    · exact Subtype.ext hg
  exact ⟨H.comap q, f.comp r, hf.comp hr⟩

/-- A bound on alpha is exactly a bound on every alternating section degree. -/
theorem alpha_le_iff_sections [Finite G] (k : ℕ) :
    alpha G ≤ k ↔ ∀ n, Involves (alternatingGroup (Fin n)) G → n ≤ k := by
  constructor
  · intro h n hn
    exact ((alpha_spec (G := G)).2 n hn).trans h
  · intro h
    exact h _ (alpha_spec (G := G)).1

/-- The trivial group belongs to the class for every threshold at least four. -/
theorem alpha_le_four_of_subsingleton [Finite G] [Subsingleton G] : alpha G ≤ 4 := by
  have hc : Nat.card G = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  have hb := alternating_degree_card_bound (alpha_spec (G := G)).1
  rw [hc] at hb
  omega

/-- The bounded-section class is closed under subgroups and faithful maps. -/
theorem alpha_le_of_injective [Finite G] [Finite Q]
    (i : G →* Q) (hi : Function.Injective i) : alpha G ≤ alpha Q := by
  apply (alpha_le_iff_sections _).2
  intro n hn
  exact (alpha_spec (G := Q)).2 n (involves_of_injective i hi hn)

/-- Inclusion of actual subgroups preserves the bound. -/
theorem alpha_le_of_subgroup_le [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    alpha H ≤ alpha K :=
  alpha_le_of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

/-- The bounded-section class is closed under arbitrary surjective images. -/
theorem alpha_le_of_surjective [Finite G] [Finite Q]
    (q : G →* Q) (hq : Function.Surjective q) : alpha Q ≤ alpha G := by
  apply (alpha_le_iff_sections _).2
  intro n hn
  exact (alpha_spec (G := G)).2 n (involves_of_surjective_image q hq hn)

/-- Kernel and codomain bounds give the extension bound required in Case 2.
The homomorphism need not be surjective. -/
theorem alpha_le_of_kernel_codomain [Finite G] [Finite Q]
    (q : G →* Q) {k : ℕ} (hk : 4 ≤ k)
    (hker : alpha q.ker ≤ k) (hQ : alpha Q ≤ k) : alpha G ≤ k := by
  apply (alpha_le_iff_sections _).2
  intro n hn
  by_cases hsmall : n ≤ 4
  · exact hsmall.trans hk
  · have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using (show 5 ≤ n by omega))
    rcases simple_involves_map_or_kernel q hn with h | h
    · exact (alpha_le_iff_sections k).1 hQ n h
    · exact (alpha_le_iff_sections k).1 hker n h

/-- In particular the class is closed under extensions by normal subgroups. -/
theorem alpha_le_of_normal_extension [Finite G]
    (N : Subgroup G) [N.Normal] {k : ℕ} (hk : 4 ≤ k)
    (hN : alpha N ≤ k) (hquot : alpha (G ⧸ N) ≤ k) : alpha G ≤ k := by
  apply alpha_le_of_kernel_codomain (QuotientGroup.mk' N) hk ?_ hquot
  apply (alpha_le_of_subgroup_le ?_).trans hN
  intro g hg
  exact (QuotientGroup.eq_one_iff g).mp (MonoidHom.mem_ker.mp hg)

/-- First isomorphism gives the bound on the quotient used by Lemma 2. -/
theorem alpha_quotient_kernel_le [Finite G] [Finite Q] (q : G →* Q) :
    alpha (G ⧸ q.ker) ≤ alpha Q :=
  alpha_le_of_injective (QuotientGroup.kerLift q) (QuotientGroup.kerLift_injective q)

/-- The preimage of a bounded subgroup remains bounded if the kernel is bounded.
This is the precise extension/subgroup step used for the corrected Y tuple. -/
theorem alpha_preimage_le [Finite G] [Finite Q] (q : G →* Q) (H : Subgroup Q)
    {k : ℕ} (hk : 4 ≤ k) (hker : alpha q.ker ≤ k) (hH : alpha H ≤ k) :
    alpha (H.comap q) ≤ k := by
  let T := H.comap q
  let r : T →* H := (q.comp T.subtype).codRestrict H (fun x => x.property)
  let i : r.ker →* q.ker :=
    (T.subtype.comp r.ker.subtype).codRestrict q.ker (fun x => by
      apply MonoidHom.mem_ker.mpr
      exact congrArg (fun z : H => (z : Q)) (MonoidHom.mem_ker.mp x.property))
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : q.ker => (z : G)) hxy
  exact alpha_le_of_kernel_codomain r hk
    ((alpha_le_of_injective i hi).trans hker) hH

end NikolovSegal
