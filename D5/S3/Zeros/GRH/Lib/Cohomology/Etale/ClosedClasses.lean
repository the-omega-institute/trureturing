/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/Etale/ClosedClasses
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/Etale/ClosedClasses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.Etale.ClosedClasses. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/Etale/ClosedClasses.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.Partitions
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Closed classes of functors: stable under bijections, finite unions and exact functors. -/

open CategoryTheory ShortComplex Subfunctor Splitting Equiv


variable {C D} [Category C] [Category D] {P : AbFunctor C → _} {E Y : C ⥤ Type 1}

lemma IsClosedClass.of_bijective (hP : IsClosedClass P) (g : E ⟶ Y) (h : AllBijective (g ·)) :
  P (freeAb E) → P (freeAb Y) := (hP.iff_of_isIso (freeAb.map (isoOfAppBijective g h).1)).1

/-- Let P satisfy `IsClosedClass` and S be a set of subfunctors of Y closed under intersection,
with ℤ[V] in P for all V in S. Then ℤ[⋃ U_i] is in P for every finite family U_i in S. -/
lemma IsClosedClass.freeAb_iSup (c : IsClosedClass P) (S : Set (Subfunctor Y)) (h : ∀ V ∈ S,
  P (freeAb V.toFunctor) ∧ ∀ W ∈ S, V
  ⊓ W ∈ S) {ι} [Finite.{1} ι] {U : ι → _} (H : ∀ i, U i ∈ S) : P (freeAb (iSup U).toFunctor) := by
  induction ι using Finite.induction_empty_option
  exacts [by simp_all [← iSup_comp ‹_›],
    c.1 _ (freeAb.hom_ext nofun), by rw [iSup_option, sup_comm, ← c.2 _ mayer_vietoris_shortExact.2,
    c.2 _ (ofHasBinaryBiproduct ..).shortExact] <;> simp_all [iSup_min]]

/-- If a property P of functors C → Ab holds for 0 and, in short exact sequences whose first
term has P, holds for the middle term iff for the last, then N ↦ P(ΦN) has the same two
features, for Φ exact. -/
lemma IsClosedClass.comap (h : IsClosedClass P) (Φ : AbFunctor D ⥤ _) [IsExactFunctor Φ] :
  IsClosedClass (P <| Φ ·) :=
  ⟨by simp_all [← Φ.3, IsClosedClass], fun _ e ↦ h.2 _ (e.map_of_exact Φ)⟩
