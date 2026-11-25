/- GID: D5/S3/TotalVariation/FairBiasCycleFactorization
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasCycleFactorization
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Signed circuit products in the augmented fair-bias boundary matrix. -/

import D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
import D5.S3.TotalVariation.FairBiasChainContraction

/-! The native ordered-matroid formula in signed augmented-face coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.TotalVariation.FairBiasCycleFactorization

open D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
open D5.S3.TotalVariation.FairBiasMatching
open D5.S3.TotalVariation.FairBiasRestriction
open D5.S3.TotalVariation.FairBiasShelling
open D5.S3.TotalVariation.FairBiasChainContraction

variable {A L : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
  [Fintype L] [LinearOrder (L × Bool)]

/-- The augmented top facets include the empty face when there are no nonempty facets. -/
def TopFacet (c : L → A) (F : Finset (L × Bool)) : Prop :=
  F ∈ facets c ∨ F = ∅ ∧ ¬ (facets c).Nonempty

private lemma topFacet_iff_base (c : L → A) (F : Finset (L × Bool)) :
    TopFacet c F ↔ (signedMatroid c).IsBase (F : Set (L × Bool)) := by
  classical
  constructor
  · rintro (hF | ⟨rfl, he⟩)
    · exact ((facet_iff_base c F).1 (mem_facets.1 hF)).2
    · obtain ⟨J, hJ⟩ := (signedMatroid c).exists_isBase
      let G := J.toFinite.toFinset
      have hcoe : (G : Set (L × Bool)) = J := Set.Finite.coe_toFinset _
      by_cases hG : G.Nonempty
      · exact (he ⟨G, mem_facets.2 ((facet_iff_base c G).2 ⟨hG, hcoe.symm ▸ hJ⟩)⟩).elim
      · rwa [← hcoe, not_nonempty_iff_eq_empty.1 hG] at hJ
  · intro hF
    by_cases h : F.Nonempty
    · exact .inl (mem_facets.2 ((facet_iff_base c F).2 ⟨h, hF⟩))
    · have hEmpty := not_nonempty_iff_eq_empty.1 h
      refine .inr ⟨hEmpty, ?_⟩
      rintro ⟨G, hG⟩
      obtain ⟨hne, hb⟩ := (facet_iff_base c G).1 (mem_facets.1 hG)
      have heq := Finset.coe_injective (hF.eq_of_subset_indep hb.indep
        (by simp [hEmpty] : (F : Set (L × Bool)) ⊆ G))
      exact h (heq.symm ▸ hne)

private lemma base_mem_augmented (c : L → A) {F : Finset (L × Bool)}
    (hF : (signedMatroid c).IsBase (F : Set (L × Bool))) : F ∈ augmentedFaces c := by
  rcases (topFacet_iff_base c F).2 hF with h | ⟨rfl, _⟩
  · exact augmented_of_subset_facet c h Subset.rfl
  · simp [augmentedFaces]

private lemma passive_iff_full_restriction (c : L → A) {F : Finset (L × Bool)} :
    PassiveBase (signedMatroid c) F ↔ TopFacet c F ∧ restrictionFace c F = F := by
  classical
  have hdec : (LinearOrder.toDecidableEq : DecidableEq (L × Bool)) =
      (inferInstance : DecidableEq (L × Bool)) :=
    Subsingleton.elim _ _
  constructor
  · intro hp
    refine ⟨(topFacet_iff_base c F).2 hp.1, Subset.antisymm (filter_subset _ _) ?_⟩
    intro a ha
    obtain ⟨x, hx, hxa, hX⟩ := hp.2 a ha
    rw [hdec] at hX
    have hXF : insert x (F.erase a) ∈ facets c :=
      mem_facets.2 ((facet_iff_base c _).2 ⟨⟨x, mem_insert_self _ _⟩, hX⟩)
    apply mem_filter.mpr
    refine ⟨ha, _, hXF, lexBefore_iff.mpr ⟨x, mem_insert_self _ _, hx, ?_⟩,
      subset_insert _ _⟩
    intro y hy hyX
    have hyEq : y = a := by
      by_contra hn
      exact hyX (mem_insert_of_mem (mem_erase.mpr ⟨hn, hy⟩))
    rwa [hyEq]
  · rintro ⟨hf, hr⟩
    have hF := (topFacet_iff_base c F).1 hf
    refine ⟨hF, fun a ha => ?_⟩
    obtain ⟨_, X, hX, hlex, hsubset⟩ := mem_filter.mp (hr.symm ▸ ha)
    obtain ⟨x, hxX, hxF, hxLt⟩ := lexBefore_iff.mp hlex
    have hb := ((facet_iff_base c X).1 (mem_facets.1 hX)).2
    have hcard : F.card = X.card := by simpa using hF.ncard_eq_ncard_of_isBase hb
    have hinsert : insert x (F.erase a) = X := by
      apply eq_of_subset_of_card_le (insert_subset hxX hsubset)
      rw [card_insert_of_notMem (fun h => hxF (mem_of_mem_erase h)),
        card_erase_add_one ha, hcard]
    have haX : a ∉ X := by
      rw [← hinsert]
      simp [ne_of_mem_of_not_mem ha hxF]
    refine ⟨x, hxF, hxLt a ha haX, ?_⟩
    rwa [hdec, hinsert]

noncomputable section

local instance (c : L → A) : Fintype (Face c) := by
  classical
  unfold Face
  infer_instance

/-- Normalization on the full restriction faces in the signed augmented boundary matrix. -/
structure SignedNormalized (c : L → A) (B : Face c) (z : Face c → ℤ) : Prop where
  vanishes : ∀ F : Face c, ¬ TopFacet c F.val → z F = 0
  cycle : ∀ R : Face c, ∑ T : Face c, boundary c R T * z T = 0
  coordinate : ∀ F : Face c, TopFacet c F.val → restrictionFace c F.val = F.val →
    z F = if F = B then 1 else 0

private abbrev ambient {c : L → A} (z : Face c → ℤ) : Chain (L × Bool) :=
  Function.extend Subtype.val z (fun _ => 0)

omit [Module (ZMod 2) A] [Finite A] [LinearOrder (L × Bool)] in
private lemma ambient_on_face {c : L → A} (z : Face c → ℤ) (F : Face c) :
    ambient z F.val = z F :=
  Subtype.val_injective.extend_apply z _ F

omit [Module (ZMod 2) A] [Finite A] [LinearOrder (L × Bool)] in
private lemma ambient_off_face {c : L → A} (z : Face c → ℤ) {F : Finset (L × Bool)}
    (hF : F ∉ augmentedFaces c) : ambient z F = 0 :=
  Function.extend_apply' z _ _ (by rintro ⟨s, rfl⟩; exact hF s.property)

section MatrixOrientation

local instance : DecidableEq (L × Bool) := LinearOrder.toDecidableEq

omit [Module (ZMod 2) A] [Finite A] in
private lemma entry_eq_insertions (c : L → A) (R T : Face c) :
    boundary c R T =
      ∑ x ∈ univ \ R.val, if insert x R.val = T.val then insertionSign R.val x else 0 := by
  classical
  change (∑ x ∈ T.val, if R.val = T.val.erase x then insertionSign T.val x else 0) = _
  have hfilter : univ.filter (· ∈ T.val) = T.val := by ext x; simp
  have hfilter' : univ.filter (· ∉ R.val) = univ \ R.val := by ext x; simp
  nth_rw 1 [← hfilter]
  rw [← hfilter', sum_filter, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases h : x ∈ T.val ∧ R.val = T.val.erase x
  · rcases h with ⟨hx, hr⟩
    simp only [hx, hr, ite_true, notMem_erase, not_false_eq_true, insert_erase hx]
    unfold insertionSign
    rw [filter_erase, erase_eq_of_notMem]
    simp
  · have hinvalid : ¬ (x ∉ R.val ∧ insert x R.val = T.val) := by
      rintro ⟨hx, heq⟩
      apply h
      rw [← heq, erase_insert hx]
      exact ⟨mem_insert_self _ _, rfl⟩
    have hleft : (if x ∈ T.val then if R.val = T.val.erase x then
        insertionSign T.val x else 0 else 0) = 0 := by
      by_cases hx : x ∈ T.val
      · rw [ite_eq_left hx, ite_eq_right (fun hr => h ⟨hx, hr⟩)]
      · rw [ite_eq_right hx]
    rw [hleft]
    by_cases hx : x ∈ R.val
    · simp [hx]
    · have hne : insert x R.val ≠ T.val := fun he => hinvalid ⟨hx, he⟩
      simp [hx, hne]

private lemma boundary_on_face {c : L → A} (z : Face c → ℤ) (R : Face c) :
    (∑ T : Face c, boundary c R T * z T) = boundaryOn univ (ambient z) R.val := by
  classical
  simp only [entry_eq_insertions, sum_mul, boundaryOn]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases hf : insert x R.val ∈ augmentedFaces c
  · let T : Face c := ⟨insert x R.val, hf⟩
    rw [sum_eq_single T]
    · change (if insert x R.val = T.val then _ else _) * z T = _ * ambient z T.val
      rw [ite_eq_left rfl, ambient_on_face z T]
    · intro T' _ hne
      have hneq : insert x R.val ≠ T'.val := fun h => hne (Subtype.ext h.symm)
      rw [ite_eq_right hneq, zero_mul]
    · simp
  · rw [ambient_off_face z (F := insert x R.val) hf, mul_zero]
    apply sum_eq_zero
    intro T _
    have hneq : insert x R.val ≠ T.val := fun h => hf (h.symm ▸ T.property)
    rw [ite_eq_right hneq, zero_mul]

end MatrixOrientation

private lemma ambient_normalized {c : L → A} {B : Face c} {z : Face c → ℤ}
    (hz : SignedNormalized c B z) : Normalized (signedMatroid c) B.val (ambient z) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro F hF
    by_cases hf : F ∈ augmentedFaces c
    · let s : Face c := ⟨F, hf⟩
      rw [ambient_on_face z s]
      exact hz.vanishes s (fun h => hF ((topFacet_iff_base c F).1 h))
    · exact ambient_off_face z hf
  · intro R
    by_cases hr : R ∈ augmentedFaces c
    · rw [← boundary_on_face z (⟨R, hr⟩ : Face c)]
      exact hz.cycle _
    · let _ : DecidableEq (L × Bool) := LinearOrder.toDecidableEq
      apply sum_eq_zero
      intro x _
      by_cases hp : insert x R ∈ augmentedFaces c
      · let s : Face c := ⟨insert x R, hp⟩
        change insertionSign R x * ambient z s.val = 0
        rw [ambient_on_face z s, hz.vanishes s ?_, mul_zero]
        rintro (hF | ⟨he, _⟩)
        · exact hr (augmented_of_subset_facet c hF (subset_insert _ _))
        · exact notMem_empty x (he ▸ mem_insert_self _ _)
      · rw [ambient_off_face z (F := insert x R) hp, mul_zero]
  · intro F hF
    let s : Face c := ⟨F, base_mem_augmented c hF.1⟩
    obtain ⟨hf, hr⟩ := passive_iff_full_restriction c |>.mp hF
    rw [ambient_on_face z s, hz.coordinate s hf hr]
    by_cases h : s = B
    · have hv : F = B.val := congrArg Subtype.val h
      simp [h, hv]
    · simp [h, show F ≠ B.val from fun he => h (Subtype.ext he)]

private lemma restrict_normalized {c : L → A} {B : Face c} {z : Chain (L × Bool)}
    (hz : Normalized (signedMatroid c) B.val z) :
    SignedNormalized c B (fun F => z F.val) := by
  classical
  have hext : ambient (fun F : Face c => z F.val) = z := by
    funext F
    by_cases hF : F ∈ augmentedFaces c
    · exact ambient_on_face _ ⟨F, hF⟩
    · rw [ambient_off_face _ hF, hz.vanishes _ (fun hb => hF (base_mem_augmented c hb))]
  constructor
  · intro F hF
    exact hz.vanishes _ (fun h => hF ((topFacet_iff_base c F.val).2 h))
  · intro R
    rw [boundary_on_face, hext]
    exact hz.cycle _
  · intro F hf hr
    rw [hz.coordinate _ ((passive_iff_full_restriction c).2 ⟨hf, hr⟩)]
    by_cases h : F = B
    · simp [h]
    · simp [h, show F.val ≠ B.val from fun he => h (Subtype.ext he)]

omit [Module (ZMod 2) A] [Finite A] [LinearOrder (L × Bool)] in
private lemma signed_support_card {c : L → A} (z : Face c → ℤ) :
    (univ.filter fun F : Face c => z F ≠ 0).card = (cycleSupport (ambient z)).card := by
  classical
  refine card_bij (fun F _ => F.val) ?_ ?_ ?_
  · intro F hF
    simpa [cycleSupport, ambient_on_face] using (mem_filter.mp hF).2
  · intro F _ G _ h
    exact Subtype.ext h
  · intro F hF
    have hn : ambient z F ≠ 0 := (mem_filter.mp hF).2
    have hf : F ∈ augmentedFaces c := by
      by_contra h
      exact hn (ambient_off_face z h)
    let s : Face c := ⟨F, hf⟩
    change ambient z s.val ≠ 0 at hn
    rw [ambient_on_face z s] at hn
    exact ⟨s, mem_filter.mpr ⟨mem_univ _, hn⟩, rfl⟩

/-- The signed fair-bias complex has a unique normalized integral cycle at each
full-restriction top facet. In positive rank its signed circuit product determines
each oriented coefficient and partitions its support by the omitted circuit vertex. -/
theorem signed_cycle_factorization (c : L → A) (B : Face c)
    (hB : TopFacet c B.val) (hR : restrictionFace c B.val = B.val) :
    (∃! z, SignedNormalized c B z) ∧
    (∀ z, SignedNormalized c B z → B.val = ∅ → ∀ F : Face c, z F = simplex ∅ F.val) ∧
    ∀ e, LeastNonloop (signedMatroid c) e →
      let C := circuitAt (signedMatroid c) B.val e
      let D := B.val \ C
      PassiveBase (signedMatroid c ／ (C : Set (L × Bool))) D ∧
      ∀ z w, SignedNormalized c B z →
        Normalized (signedMatroid c ／ (C : Set (L × Bool))) D w →
        (∀ F : Face c, z F = circuitLift C e B.val w F.val) ∧
        (∀ F : Face c, z F ≠ 0 ↔ ∃ x ∈ C, F.val ∩ C = C.erase x ∧ F.val \ C ∈ cycleSupport w) ∧
        (univ.filter fun F : Face c => z F ≠ 0).card = C.card * (cycleSupport w).card := by
  classical
  have hp := (passive_iff_full_restriction c).2 ⟨hB, hR⟩
  obtain ⟨hex, hzero, hfactor⟩ := normalized_factorization (signedMatroid c) B.val hp
  obtain ⟨v, hv, hu⟩ := hex
  refine ⟨⟨fun F => v F.val, restrict_normalized hv, ?_⟩, ?_, ?_⟩
  · intro z hz
    have heq := hu _ (ambient_normalized hz)
    funext F
    rw [← ambient_on_face z F, heq]
  · intro z hz hempty F
    rw [← ambient_on_face z F, hzero _ (ambient_normalized hz) hempty]
  · intro e he
    obtain ⟨hD, hf⟩ := hfactor e he
    refine ⟨hD, fun z w hz hw => ?_⟩
    obtain ⟨heq, hs, hc⟩ := hf _ _ (ambient_normalized hz) hw
    refine ⟨fun F => ?_, fun F => ?_, ?_⟩
    · rw [← ambient_on_face z F, heq]
    · simpa [cycleSupport, ambient_on_face] using hs F.val
    · rw [signed_support_card, hc]

end
end D5.S3.TotalVariation.FairBiasCycleFactorization
