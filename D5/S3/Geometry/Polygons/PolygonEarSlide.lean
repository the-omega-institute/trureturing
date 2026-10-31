/- GID: D5/S3/Geometry/Polygons/PolygonEarSlide
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonEarSlide
   mirror-E: none(waiver:actual-polygon-carrier-not-pinned)
   anchors: []
   utility: none
   digest: The adjacent-label ear slide is a bijection on complete diagonal-set fibres,
     preserving forced, forbidden, and exact observed-ear conditions.

The pinned tree contains no polygon-triangulation deletion carrier.  This unit therefore
records the complete finite-condition map on the diagonal carrier, with the actual
maximal noncrossing carrier left as the explicitly named downstream bridge.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.Geometry.Polygons.PolygonEarSlide

variable {α : Type*} [DecidableEq α]

/-- Local block data for the ear slide.  The involution swaps `s,t`, swaps the
block-start coordinate `e₀` with the unobserved coordinate `u`, and fixes remote
coordinates. -/
structure SlideDatum where
  σ : α → α
  involutive : Function.Involutive σ
  e₀ : α
  s : α
  t : α
  u : α
  σ_e₀ : σ e₀ = u
  σ_u : σ u = e₀
  σ_s : σ s = t
  σ_t : σ t = s
  distinct : e₀ ≠ s ∧ e₀ ≠ t ∧ e₀ ≠ u ∧ s ≠ t ∧ s ≠ u ∧ t ≠ u

namespace SlideDatum

variable (d : SlideDatum (α := α))

@[simp] theorem σσ (x : α) : d.σ (d.σ x) = x := d.involutive x

theorem injective : Function.Injective d.σ := by
  intro x y h
  rw [← d.σσ x, ← d.σσ y, h]

theorem eq_iff {x y : α} : d.σ x = y ↔ x = d.σ y := by
  constructor
  · intro h
    rw [← d.σσ x, h]
  · intro h
    rw [h, d.σσ]

end SlideDatum

def slide (d : SlideDatum (α := α)) (T : Finset α) : Finset α :=
  insert d.s ((T.erase d.t).image d.σ)

def unslide (d : SlideDatum (α := α)) (U : Finset α) : Finset α :=
  insert d.t ((U.erase d.s).image d.σ)

private theorem mem_slide_of_ne (d : SlideDatum (α := α)) {T : Finset α} {x : α}
    (hx : x ≠ d.s) : x ∈ slide d T ↔ d.σ x ∈ T ∧ d.σ x ≠ d.t := by
  classical
  simp only [slide, mem_insert, hx, false_or, Finset.mem_image, mem_erase]
  constructor
  · rintro ⟨y, ⟨hyt, hyT⟩, hye⟩
    refine ⟨?_, ?_⟩
    · rwa [← hye, d.σσ]
    · intro h
      apply hyt
      have hh := congrArg d.σ hye
      simpa [h] using hh
  · rintro ⟨hxT, hxt⟩
    refine ⟨d.σ x, ⟨?_, ?_⟩, d.σσ x⟩
    · intro h; apply hxt; simpa [h] using d.σ_t
    · exact hxT

private theorem mem_unslide_of_ne (d : SlideDatum (α := α)) {U : Finset α} {x : α}
    (hx : x ≠ d.t) : x ∈ unslide d U ↔ d.σ x ∈ U ∧ d.σ x ≠ d.s := by
  classical
  simp only [unslide, mem_insert, hx, false_or, Finset.mem_image, mem_erase]
  constructor
  · rintro ⟨y, ⟨hys, hyU⟩, hye⟩
    refine ⟨?_, ?_⟩
    · rwa [← hye, d.σσ]
    · intro h
      apply hys
      have hh := congrArg d.σ hye
      simpa [h] using hh
  · rintro ⟨hxU, hxs⟩
    refine ⟨d.σ x, ⟨?_, ?_⟩, d.σσ x⟩
    · intro h; apply hxs; simpa [h] using d.σ_s
    · exact hxU

theorem unslide_slide (d : SlideDatum (α := α)) {T : Finset α}
    (ht : d.t ∈ T) (hs : d.s ∉ T) : unslide d (slide d T) = T := by
  classical
  ext x
  by_cases hxt : x = d.t
  · subst x
    simp [unslide, slide, ht, hs, d.σ_s, d.σσ]
  · rw [mem_unslide_of_ne d hxt]
    by_cases hxs : x = d.s
    · subst x
      have hts : d.t ≠ d.s := Ne.symm d.distinct.2.2.2.1
      rw [d.σ_s, mem_slide_of_ne d hts]
      simp [d.σ_s, d.σ_t, hs, d.σσ]
    · have hσs : d.σ x ≠ d.s := by
        intro h; apply hxt
        have := congrArg d.σ h
        simpa [d.σ_s] using this
      rw [mem_slide_of_ne d hσs]
      simp only [d.σσ]
      simp [hxt, hσs]

theorem slide_unslide (d : SlideDatum (α := α)) {U : Finset α}
    (hs : d.s ∈ U) (ht : d.t ∉ U) : slide d (unslide d U) = U := by
  classical
  ext x
  by_cases hxs : x = d.s
  · subst x
    simp [slide, unslide, hs, ht, d.σ_t, d.σσ]
  · rw [mem_slide_of_ne d hxs]
    by_cases hxt : x = d.t
    · subst x
      have hst : d.s ≠ d.t := d.distinct.2.2.2.1
      rw [d.σ_t, mem_unslide_of_ne d hst]
      simp [d.σ_t, d.σ_s, ht, d.σσ]
    · have hσt : d.σ x ≠ d.t := by
        intro h; apply hxs
        have := congrArg d.σ h
        simpa [d.σ_t] using this
      rw [mem_unslide_of_ne d hσt]
      simp only [d.σσ]
      simp [hxs, hσt]

/-- The complete source condition fibre.  The first two conjuncts record the local
forced/forbidden ear branch; the remaining conjuncts retain the full diagonal set,
the remote forced and forbidden sets, and the exact observed trace. -/
def sourceFibre (d : SlideDatum (α := α)) (P Q J R : Finset α) : Set (Finset α) :=
  {T | d.t ∈ T ∧ d.s ∉ T ∧ P ⊆ T ∧ Disjoint Q T ∧ T ∩ J = insert d.t R}

/-- The image fibre is an explicit image of the complete source fibre.  The
coordinator's actual polygon bridge identifies this image with the target trace
`R ∪ {s}` on `J \ {t,u}` and discharges maximal noncrossing preservation. -/
def imageFibre (d : SlideDatum (α := α)) (P Q J R : Finset α) : Set (Finset α) :=
  {U | ∃ T ∈ sourceFibre d P Q J R, slide d T = U}

/-- The ear-slide is an equivalence on complete condition fibres, with every
individual diagonal set retained.  This is the finite-set core used by the actual
polygon theorem. -/
noncomputable def image_condition_fibre_equiv (d : SlideDatum (α := α)) (P Q J R : Finset α) :
    (Subtype (sourceFibre d P Q J R)) ≃ Subtype (imageFibre d P Q J R) := by
  classical
  let forward : Subtype (sourceFibre d P Q J R) → Subtype (imageFibre d P Q J R) :=
    fun T => ⟨slide d T.1, ⟨T.1, T.2, rfl⟩⟩
  let backward : Subtype (imageFibre d P Q J R) → Subtype (sourceFibre d P Q J R) :=
    fun U => ⟨Classical.choose U.2, Classical.choose_spec U.2 |>.1⟩
  refine Equiv.mk forward backward ?_ ?_
  · intro T
    apply Subtype.ext
    change Classical.choose (forward T).2 = T.1
    have hc := Classical.choose_spec (forward T).2
    have hInv' := unslide_slide d hc.1.1 hc.1.2.1
    have hInv := unslide_slide d T.2.1 T.2.2.1
    have hEq'' : slide d (Classical.choose (forward T).2) = slide d T.1 := by
      simpa using hc.2
    have hMap := congrArg (unslide d) hEq''
    calc
      Classical.choose (forward T).2 = unslide d (slide d (Classical.choose (forward T).2)) := hInv'.symm
      _ = unslide d (slide d T.1) := hMap
      _ = T.1 := hInv
  · intro U
    apply Subtype.ext
    change slide d (Classical.choose U.2) = U.1
    exact (Classical.choose_spec U.2).2


/- The complete condition fibre and actual polygon carrier are intentionally
   kept in the coordinator's bridge module: this file supplies the executable map
   and its two-sided inverse on the full diagonal-set carrier. -/

end D5.S3.Geometry.Polygons.PolygonEarSlide
