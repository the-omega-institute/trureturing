/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2Cofinite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2Cofinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Difference-one words give a finite spanning family in the Leech relative C₂ quotient. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOne.ActualLeech
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechRelativeOddAction
import Mathlib.Data.Fintype.List

/-! C₂-cofiniteness of the actual Leech extension via the negative twisted relative quotient. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2

open ActualLeechHyperbolic (leechData leech_spec)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeGeneratingFieldLocality (LatticeData)
open OddDifferenceOne (leech_odd_difference_one)
open OddDifferenceOneSpanning (Homogeneous Word strictSpan wordMap)
open private lettersIn increasing sorted_truncate tail_cutoff wordMap_cons from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOneSpanning

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    AddCommGroup (paritySpace D hu (-1)) :=
  (paritySpace D hu (-1)).addCommGroup

/-- In the relative quotient, the surviving strict words have indices in a finite interval.
Their letters lie in a finite alphabet, and strictness makes each word duplicate-free. -/
private theorem relativeOddC2_finite_of_strictSpan {D : LatticeData} {hu : IsUnit D.G.det}
    (X : Finset (Homogeneous D)) (u : paritySpace D hu (-1)) (hspan : strictSpan X u = ⊤) :
    FiniteDimensional ℂ (paritySpace D hu (-1) ⧸ relativeOddC2 D hu) := by
  classical
  obtain ⟨L, hL⟩ := tail_cutoff X u
  let C := relativeOddC2 D hu
  let A := X ×ˢ Finset.Ico (-1 : ℤ) L
  let represent : {l : List ↥A // l.Nodup} → (paritySpace D hu (-1) ⧸ C) :=
    fun l => C.mkQ (wordMap (l.val.map Subtype.val) u)
  let S := Submodule.span ℂ (Set.range represent)
  have hle : strictSpan X u ≤ S.comap C.mkQ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, hletters, hinc, rfl⟩
    change C.mkQ (wordMap t u) ∈ S
    by_cases low : ∃ a ∈ t, a.2 ≤ -2
    · obtain ⟨a, ha, ha'⟩ := low
      cases t with
      | nil => simp at ha
      | cons b s =>
        have hb : b.2 ≤ -2 := by
          rcases List.mem_cons.mp ha with rfl | hb
          · exact ha'
          · exact (le_of_lt ((List.pairwise_cons.mp hinc).1 a hb)).trans ha'
        have hz : wordMap (b :: s) u ∈ C := by
          rw [wordMap_cons]
          exact fixed_odd_mode_mem_relativeOddC2 D hu b.1.state (wordMap s u) hb
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero C).mpr hz]
        exact S.zero_mem
    by_cases high : ∃ a ∈ t, L ≤ a.2
    · rw [sorted_truncate X u L hL t (List.Pairwise.imp le_of_lt hinc) hletters high, map_zero]
      exact S.zero_mem
    have hA : ∀ a ∈ t, a ∈ A := by
      intro a ha
      have hlow : ¬ a.2 ≤ -2 := fun h => low ⟨a, ha, h⟩
      exact Finset.mem_product.mpr ⟨hletters a ha,
        Finset.mem_Ico.mpr ⟨by omega, lt_of_not_ge fun h => high ⟨a, ha, h⟩⟩⟩
    have ht : t.Nodup :=
      List.Pairwise.imp (fun h eq => (ne_of_lt h) (congrArg Prod.snd eq)) hinc
    let l := t.attachWith (fun a => a ∈ A) hA
    have hl : l.map Subtype.val = t := List.attachWith_map_subtype_val hA
    have hnodup : l.Nodup := List.Nodup.of_map Subtype.val (hl.symm ▸ ht)
    exact Submodule.subset_span ⟨⟨l, hnodup⟩, by simp only [represent, hl]⟩
  have hS : S = ⊤ := by
    refine top_unique fun q _ => ?_
    obtain ⟨v, rfl⟩ := C.mkQ_surjective q
    exact hle (hspan.symm ▸ Submodule.mem_top)
  change Module.Finite ℂ (paritySpace D hu (-1) ⧸ C)
  rw [Module.finite_def, Submodule.fg_def]
  exact ⟨Set.range represent, Set.finite_range represent, hS⟩

/-- The actual negative twisted sector modulo the fixed-source C₂ subspace is finite-dimensional. -/
theorem leech_relative_odd_c2_finite :
    FiniteDimensional ℂ LeechRelativeOddQuotient := by
  rcases subsingleton_or_nontrivial (paritySpace leechData leech_spec.2.1 (-1)) with h | h
  · let : Subsingleton (paritySpace leechData leech_spec.2.1 (-1)) := h
    let C := relativeOddC2 leechData leech_spec.2.1
    exact FiniteDimensional.of_surjective C.mkQ C.mkQ_surjective
  · let : Nontrivial (paritySpace leechData leech_spec.2.1 (-1)) := h
    obtain ⟨u, hu⟩ := exists_ne (0 : paritySpace leechData leech_spec.2.1 (-1))
    obtain ⟨X, hspan, _⟩ := leech_odd_difference_one u hu
    exact relativeOddC2_finite_of_strictSpan X u hspan

/-- The actual Leech extension is C₂-cofinite. -/
theorem leech_extension_c2_cofinite :
    FiniteDimensional ℂ LeechExtensionQuotient :=
  leech_extension_c2_cofinite_of_relative_odd_finite leech_relative_odd_c2_finite

#print axioms leech_relative_odd_c2_finite
#print axioms leech_extension_c2_cofinite

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2
