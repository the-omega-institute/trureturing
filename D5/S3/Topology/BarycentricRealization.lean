/- GID: D5/S3/Topology/BarycentricRealization
   generality: G
   mirror-B: D5/B/S3/Topology/BarycentricRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Lemmas]
   utility: none
   digest: The finite barycentric realization homeomorphism preserves subcomplexes. -/

import D5.S3.Geometry.FiniteSimplicialOpenCover
import D5.S3.Geometry.FiniteSimplicialJoin
import D5.S3.Geometry.FiniteSubcomplexCylinder
import D5.S3.Topology.BarycentricBaseRigidity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Coordinate realization of ordinary barycentric subdivision

The old positive support is the union of the positively weighted faces.
For a flag this is its greatest face, so it detects membership in any
ambient face subcomplex.

The inverse construction subtracts one positive layer at a time.
Working with unnormalized weights makes the all-equal layer end at zero.
For uniqueness, the greatest face is recovered from the old support.
A vertex outside the next smaller face recovers the greatest face's
weight from the least positive coordinate.
-/

namespace D5.S3.Topology.BarycentricRealization

open D5.S3.Geometry
open FiniteConeCollapse (faceSimplex realization realization_mem_iff)
open FiniteSimplicialJoin (Space realizationCompactSpace)
open BarycentricGraphDistance (Face)
open BarycentricBaseRigidity (sd)
open BarycentricNeighborhoodIteration (subdivision)
open scoped BigOperators ContinuousMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable {K P : PreAbstractSimplicialComplex V}

local instance faceFintype (K : PreAbstractSimplicialComplex V) : Fintype (Face K) :=
  Fintype.ofFinite _

-- The existing formula is presented with a linear order on the vertex labels.
-- Its values depend only on membership and cardinality.
private abbrev labelOrder (V : Type) [Fintype V] : LinearOrder V :=
  LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective

private def faceBarycenter (s : Finset V) : V → ℝ :=
  letI : LinearOrder V := labelOrder V
  FiniteSimplicialOpenCover.barycenterCoords s

private theorem faceBarycenter_apply (s : Finset V) (v : V) :
    faceBarycenter s v = if v ∈ s then 1 / (s.card : ℝ) else 0 := by
  by_cases hv : v ∈ s <;> simp [faceBarycenter, FiniteSimplicialOpenCover.barycenterCoords, hv]

private theorem faceBarycenter_mem {s : Finset V} (hs : s.Nonempty) :
    faceBarycenter s ∈ faceSimplex s := by
  let : LinearOrder V := labelOrder V
  exact FiniteSimplicialOpenCover.barycenterCoords_mem_faceSimplex hs

private def positiveSupport {U : Type} [Fintype U] (x : U → ℝ) : Finset U := by
  classical
  exact Finset.univ.filter fun u => 0 < x u

@[simp] private theorem mem_positiveSupport {U : Type} [Fintype U]
    {x : U → ℝ} {u : U} : u ∈ positiveSupport x ↔ 0 < x u := by
  simp [positiveSupport]

private theorem zero_off_support {U : Type} [Fintype U] {x : U → ℝ}
    (hx : ∀ u, 0 ≤ x u) {u : U} (hu : u ∉ positiveSupport x) : x u = 0 :=
  le_antisymm (le_of_not_gt fun h => hu (mem_positiveSupport.mpr h)) (hx u)

private theorem support_nonempty {U : Type} [Fintype U] {x : U → ℝ}
    (hx : ∀ u, 0 ≤ x u) (hsum : ∑ u, x u = 1) : (positiveSupport x).Nonempty := by
  by_contra h
  have hz : ∀ u, x u = 0 := fun u =>
    zero_off_support hx (fun hu => h ⟨u, hu⟩)
  simp [hz] at hsum

private theorem mem_realization_iff_support {U : Type} [Fintype U] [DecidableEq U]
    (L : PreAbstractSimplicialComplex U) {x : U → ℝ}
    (hx : ∀ u, 0 ≤ x u) (hsum : ∑ u, x u = 1) :
    x ∈ realization L ↔ positiveSupport x ∈ L := by
  constructor
  · intro hm
    obtain ⟨s, hs, hsx⟩ := (realization_mem_iff L x).mp hm
    refine (L.isRelLowerSet_faces hs).2 ?_ (support_nonempty hx hsum)
    intro u hu
    by_contra h
    exact (ne_of_gt (mem_positiveSupport.mp hu)) (hsx.2.2 u h)
  · intro hm
    exact (realization_mem_iff L x).mpr
      ⟨_, hm, hx, hsum, fun _ hu => zero_off_support hx hu⟩

private theorem coordinate_data {U : Type} [Fintype U] [DecidableEq U]
    {L : PreAbstractSimplicialComplex U} (x : Space L) :
    (∀ u, 0 ≤ x.val u) ∧ (∑ u, x.val u) = 1 := by
  obtain ⟨_, _, hx⟩ := (realization_mem_iff L x.val).mp x.property
  exact ⟨hx.1, hx.2.1⟩

/-- The old coordinates are the weighted sum of the barycentres of ambient faces. -/
def barycentricCoords (w : Face K → ℝ) (v : V) : ℝ :=
  ∑ f, w f * faceBarycenter f.val v

private theorem barycentricCoords_add_weight (w : Face K → ℝ) (top : Face K)
    (c : ℝ) (v : V) :
    barycentricCoords (fun f => w f + if f = top then c else 0) v =
      barycentricCoords w v + c * faceBarycenter top.val v := by
  simp [barycentricCoords, add_mul, Finset.sum_add_distrib, ite_mul]

private theorem barycentricCoords_nonneg {w : Face K → ℝ} (hw : ∀ f, 0 ≤ w f) (v : V) :
    0 ≤ barycentricCoords w v :=
  Finset.sum_nonneg fun f _ =>
    mul_nonneg (hw f) ((faceBarycenter_mem (K.isRelLowerSet_faces f.property).1).1 v)

private theorem sum_barycentricCoords (w : Face K → ℝ) :
    (∑ v, barycentricCoords w v) = ∑ f, w f := by
  unfold barycentricCoords
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [← Finset.mul_sum, (faceBarycenter_mem (K.isRelLowerSet_faces f.property).1).2.1, mul_one]

private theorem support_barycentricCoords {w : Face K → ℝ} (hw : ∀ f, 0 ≤ w f) :
    positiveSupport (barycentricCoords w) = (positiveSupport w).biUnion Subtype.val := by
  ext v
  rw [mem_positiveSupport, Finset.mem_biUnion]
  have hterm (f : Face K) : 0 ≤ w f * faceBarycenter f.val v :=
    mul_nonneg (hw f) ((faceBarycenter_mem (K.isRelLowerSet_faces f.property).1).1 v)
  constructor
  · intro hv
    by_contra h
    have hz (f : Face K) : w f * faceBarycenter f.val v = 0 := by
      by_cases hf : f ∈ positiveSupport w
      · have hfv : v ∉ f.val := fun hfv => h ⟨f, hf, hfv⟩
        simp [faceBarycenter_apply, hfv]
      · simp [zero_off_support hw hf]
    simp [barycentricCoords, hz] at hv
  · rintro ⟨f, hf, hv⟩
    change 0 < ∑ g, w g * faceBarycenter g.val v
    apply Finset.sum_pos' (fun g _ => hterm g)
    refine ⟨f, Finset.mem_univ _, mul_pos (mem_positiveSupport.mp hf) ?_⟩
    rw [faceBarycenter_apply, if_pos hv]
    exact one_div_pos.mpr (by exact_mod_cast (K.isRelLowerSet_faces f.property).1.card_pos)

private theorem chain_has_top {s : Finset (Face K)} (hne : s.Nonempty)
    (hs : IsChain (· < ·) (s : Set (Face K))) :
    ∃ top ∈ s, ∀ f ∈ s, f ≤ top := by
  obtain ⟨top, htop, hcard⟩ := Finset.exists_max_image s (fun f : Face K => f.val.card) hne
  refine ⟨top, htop, fun f hf => ?_⟩
  by_cases he : f = top
  · exact he.le
  rcases hs hf htop he with h | h
  · exact h.le
  · exact (not_lt_of_ge (hcard f hf) (Finset.card_lt_card h)).elim

private theorem support_barycentricCoords_of_top {w : Face K → ℝ} (hw : ∀ f, 0 ≤ w f)
    {top : Face K} (ht : top ∈ positiveSupport w) (hle : ∀ f ∈ positiveSupport w, f ≤ top) :
    positiveSupport (barycentricCoords w) = top.val := by
  rw [support_barycentricCoords hw]
  exact le_antisymm (Finset.biUnion_subset.mpr hle)
    (Finset.subset_biUnion_of_mem Subtype.val ht)

private theorem subdivided_support (w : Space (sd K)) :
    positiveSupport w.val ∈ sd K := by
  obtain ⟨hw, hsum⟩ := coordinate_data w
  exact (mem_realization_iff_support (sd K) hw hsum).mp w.property

/-- The barycentre map preserves and reflects every ambient face subcomplex. -/
theorem barycentricCoords_mem_subcomplex_iff (w : Space (sd K)) :
    barycentricCoords w.val ∈ realization P ↔ w.val ∈ realization (subdivision K P) := by
  obtain ⟨hw, hsum⟩ := coordinate_data w
  have hs := subdivided_support w
  obtain ⟨top, htop, hle⟩ := chain_has_top hs.1 hs.2.1
  rw [mem_realization_iff_support P (barycentricCoords_nonneg hw)
      ((sum_barycentricCoords w.val).trans hsum),
    mem_realization_iff_support (subdivision K P) hw hsum,
    support_barycentricCoords_of_top hw htop hle]
  refine ⟨fun h => ⟨hs.1, hs.2.1, ?_⟩, fun h => h.2.2 top htop⟩
  intro f hf
  exact (P.isRelLowerSet_faces h).2 (hle f hf) (K.isRelLowerSet_faces f.property).1

/-- The continuous map from the ordinary subdivision to the original realization. -/
def toOriginal (K : PreAbstractSimplicialComplex V) : C(Space (sd K), Space K) where
  toFun w := ⟨barycentricCoords w.val, (barycentricCoords_mem_subcomplex_iff w).mpr w.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    change Continuous (fun w : Space (sd K) => ∑ f : Face K, w.val f * faceBarycenter f.val v)
    exact continuous_finsetSum _ fun f _ =>
      ((continuous_apply f).comp continuous_subtype_val).mul continuous_const

/-- A nonnegative coordinate vector supported inside a face is a nonnegative
sum of face barycentres along a chain. -/
private theorem exists_chain_weights (T : Face K) (s : Finset V) :
    ∀ (x : V → ℝ), positiveSupport x = s → (∀ v, 0 ≤ x v) → s ⊆ T.val →
      ∃ w : Face K → ℝ, (∀ f, 0 ≤ w f) ∧
        IsChain (· < ·) (positiveSupport w : Set (Face K)) ∧
        (∀ f ∈ positiveSupport w, f.val ⊆ s) ∧ barycentricCoords w = x := by
  refine Finset.strongInductionOn s ?_
  intro s ih x hs hx hT
  by_cases hne : s.Nonempty
  · let top : Face K := ⟨s, (K.isRelLowerSet_faces T.property).2 hT hne⟩
    obtain ⟨v₀, hv₀, hmin⟩ := Finset.exists_min_image s x hne
    have hm : 0 < x v₀ := mem_positiveSupport.mp (by rw [hs]; exact hv₀)
    have hcard : (0 : ℝ) < s.card := by exact_mod_cast hne.card_pos
    let c : ℝ := (s.card : ℝ) * x v₀
    have hc : 0 < c := mul_pos hcard hm
    have hterm (v : V) (hv : v ∈ s) : c * faceBarycenter top.val v = x v₀ := by
      rw [faceBarycenter_apply, if_pos hv]
      dsimp [c, top]
      field_simp [hcard.ne'] <;> ring
    let y : V → ℝ := fun v => x v - c * faceBarycenter top.val v
    have hy (v : V) : 0 ≤ y v := by
      by_cases hv : v ∈ s
      · exact sub_nonneg.mpr (by rw [hterm v hv]; exact hmin v hv)
      · simpa [y, faceBarycenter_apply, top, hv] using hx v
    have hys : positiveSupport y ⊆ s := by
      intro v hv
      by_contra hvs
      have hz := zero_off_support hx (fun h => hvs (hs ▸ h))
      have hpos := mem_positiveSupport.mp hv
      simp [y, faceBarycenter_apply, top, hvs, hz] at hpos
    have hyv : v₀ ∉ positiveSupport y := by
      simp [y, hterm v₀ hv₀]
    have hylt : positiveSupport y ⊂ s :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hys, fun h => hyv (h.symm ▸ hv₀)⟩
    obtain ⟨u, hu, hchain, hsub, heq⟩ :=
      ih (positiveSupport y) hylt y rfl hy (hys.trans hT)
    have hlt (f : Face K) (hf : f ∈ positiveSupport u) : f < top := by
      change f.val ⊂ s
      exact lt_of_le_of_lt (hsub f hf) hylt
    have htop : top ∉ positiveSupport u := fun h => (lt_irrefl top) (hlt _ h)
    let w : Face K → ℝ := fun f => if f = top then c else u f
    have hsupport : positiveSupport w = insert top (positiveSupport u) := by
      ext f
      by_cases hf : f = top <;> simp [w, hf, hc, mem_positiveSupport]
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · intro f
      by_cases hf : f = top <;> simp [w, hf, hc.le, hu]
    · rw [hsupport, Finset.coe_insert]
      intro f hf g hg hfg
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · have hg' : g ∈ positiveSupport u :=
          (Set.mem_insert_iff.mp hg).resolve_left (Ne.symm hfg)
        exact Or.inr (hlt g hg')
      · rcases Set.mem_insert_iff.mp hg with rfl | hg
        · exact Or.inl (hlt f hf)
        · exact hchain hf hg hfg
    · intro f hf
      rw [hsupport] at hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact Finset.Subset.rfl
      · exact (hsub f hf).trans hys
    · funext v
      have huw : u top = 0 := zero_off_support hu htop
      have hw : w = fun f => u f + if f = top then c else 0 := by
        funext f
        by_cases hf : f = top
        · subst f
          simp [w, huw]
        · simp [w, hf]
      calc
        barycentricCoords w v = barycentricCoords u v + c * faceBarycenter top.val v := by
          rw [hw, barycentricCoords_add_weight]
        _ = x v := by
          rw [congrFun heq v]
          dsimp [y]
          ring
  · have hs0 := Finset.not_nonempty_iff_eq_empty.mp hne
    have hz (v : V) : x v = 0 :=
      zero_off_support hx (by simp [hs, hs0])
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_, ?_, ?_⟩
    · intro f hf
      exact ((lt_irrefl (0 : ℝ))
        ((mem_positiveSupport (x := fun _ : Face K => 0) (u := f)).mp hf)).elim
    · intro f hf
      exact ((lt_irrefl (0 : ℝ))
        ((mem_positiveSupport (x := fun _ : Face K => 0) (u := f)).mp hf)).elim
    · funext v
      simp [barycentricCoords, hz]

/-- Every point of the original realization has barycentric coordinates on a flag. -/
theorem toOriginal_surjective (K : PreAbstractSimplicialComplex V) :
    Function.Surjective (toOriginal K) := by
  intro x
  obtain ⟨hx, hsum⟩ := coordinate_data x
  have hface := (mem_realization_iff_support K hx hsum).mp x.property
  let T : Face K := ⟨positiveSupport x.val, hface⟩
  obtain ⟨w, hw, hchain, _, heq⟩ :=
    exists_chain_weights T (positiveSupport x.val) x.val rfl hx Finset.Subset.rfl
  have hwsum : (∑ f, w f) = 1 := by
    rw [← sum_barycentricCoords, heq, hsum]
  have hws : positiveSupport w ∈ sd K :=
    ⟨support_nonempty hw hwsum, hchain, fun f _ => f.property⟩
  exact ⟨⟨w, (mem_realization_iff_support (sd K) hw hwsum).mpr hws⟩, Subtype.ext heq⟩

private def eraseWeight (w : Face K → ℝ) (top : Face K) : Face K → ℝ :=
  fun f => if f = top then 0 else w f

private theorem eraseWeight_nonneg {w : Face K → ℝ} (hw : ∀ f, 0 ≤ w f) (top : Face K) :
    ∀ f, 0 ≤ eraseWeight w top f := by
  intro f
  by_cases hf : f = top <;> simp [eraseWeight, hf, hw]

private theorem support_eraseWeight (w : Face K → ℝ) (top : Face K) :
    positiveSupport (eraseWeight w top) = (positiveSupport w).erase top := by
  ext f
  by_cases hf : f = top <;> simp [eraseWeight, hf, Finset.mem_erase]

private theorem barycentricCoords_eraseWeight (w : Face K → ℝ) (top : Face K) (v : V) :
    barycentricCoords w v =
      barycentricCoords (eraseWeight w top) v + w top * faceBarycenter top.val v := by
  have heq : w = fun f => eraseWeight w top f + if f = top then w top else 0 := by
    funext f
    by_cases hf : f = top
    · subst f
      simp [eraseWeight]
    · simp [eraseWeight, hf]
  calc
    barycentricCoords w v =
        barycentricCoords (fun f => eraseWeight w top f + if f = top then w top else 0) v :=
      congrArg (fun u => barycentricCoords u v) heq
    _ = _ := barycentricCoords_add_weight (eraseWeight w top) top (w top) v

-- A vertex outside the penultimate face receives precisely the top contribution.
private theorem top_contribution_is_minimum {w : Face K → ℝ} (hw : ∀ f, 0 ≤ w f)
    (hchain : IsChain (· < ·) (positiveSupport w : Set (Face K))) {top : Face K}
    (hle : ∀ f ∈ positiveSupport w, f ≤ top) :
    (∀ v ∈ top.val, w top * (1 / (top.val.card : ℝ)) ≤ barycentricCoords w v) ∧
    ∃ v ∈ top.val, barycentricCoords w v = w top * (1 / (top.val.card : ℝ)) := by
  let u := eraseWeight w top
  have hu := eraseWeight_nonneg hw top
  have hus : positiveSupport u = (positiveSupport w).erase top :=
    support_eraseWeight w top
  have hlt (f : Face K) (hf : f ∈ positiveSupport u) : f < top := by
    rw [hus] at hf
    exact lt_of_le_of_ne (hle f (Finset.mem_of_mem_erase hf)) (Finset.ne_of_mem_erase hf)
  have hdecomp (v : V) (hv : v ∈ top.val) :
      barycentricCoords w v = barycentricCoords u v + w top * (1 / (top.val.card : ℝ)) := by
    rw [barycentricCoords_eraseWeight w top v, faceBarycenter_apply, if_pos hv]
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [hdecomp v hv]
    linarith [barycentricCoords_nonneg hu v]
  have hmiss : ∃ v ∈ top.val, ∀ f ∈ positiveSupport u, v ∉ f.val := by
    by_cases hne : (positiveSupport u).Nonempty
    · have hchain' : IsChain (· < ·) (positiveSupport u : Set (Face K)) := by
        exact IsChain.mono (by
          rw [hus]
          exact Finset.coe_subset.mpr (Finset.erase_subset _ _)) hchain
      obtain ⟨next, hn, hnext⟩ := chain_has_top hne hchain'
      obtain ⟨v, hv, hvn⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (Finset.card_lt_card (hlt next hn))
      exact ⟨v, hv, fun f hf hvf => hvn (hnext f hf hvf)⟩
    · obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces top.property).1
      exact ⟨v, hv, fun f hf => (hne ⟨f, hf⟩).elim⟩
  obtain ⟨v, hv, hvmiss⟩ := hmiss
  have hvzero : barycentricCoords u v = 0 := by
    apply zero_off_support (barycentricCoords_nonneg hu)
    rw [support_barycentricCoords hu, Finset.mem_biUnion]
    rintro ⟨f, hf, hvf⟩
    exact hvmiss f hf hvf
  exact ⟨v, hv, by rw [hdecomp v hv, hvzero, zero_add]⟩

private theorem chain_weights_injective (s : Finset (Face K)) :
    ∀ (w z : Face K → ℝ), positiveSupport w = s →
      (∀ f, 0 ≤ w f) → (∀ f, 0 ≤ z f) →
      IsChain (· < ·) (positiveSupport w : Set (Face K)) →
      IsChain (· < ·) (positiveSupport z : Set (Face K)) →
      barycentricCoords w = barycentricCoords z → w = z := by
  refine Finset.strongInductionOn s ?_
  intro s ih w z hs hw hz hchainw hchainz heq
  by_cases hne : s.Nonempty
  · obtain ⟨top, htop, hle⟩ := chain_has_top (hs.symm ▸ hne) hchainw
    have hsupport := support_barycentricCoords_of_top hw htop hle
    have hzne : (positiveSupport z).Nonempty := by
      by_contra h
      rw [heq, support_barycentricCoords hz, Finset.not_nonempty_iff_eq_empty.mp h,
        Finset.biUnion_empty] at hsupport
      exact (K.isRelLowerSet_faces top.property).1.ne_empty hsupport.symm
    obtain ⟨top', htop', hle'⟩ := chain_has_top hzne hchainz
    have htop_eq : top = top' := Subtype.ext (hsupport.symm.trans
      ((congrArg positiveSupport heq).trans (support_barycentricCoords_of_top hz htop' hle')))
    subst top'
    obtain ⟨hwmin, v, hv, hvmin⟩ := top_contribution_is_minimum hw hchainw hle
    obtain ⟨hzmin, u, hu, humin⟩ := top_contribution_is_minimum hz hchainz hle'
    have hcoeff : w top = z top := by
      have h₁ := hwmin u hu
      have h₂ := hzmin v hv
      rw [heq, humin] at h₁
      rw [← heq, hvmin] at h₂
      have hpos : 0 < 1 / (top.val.card : ℝ) :=
        one_div_pos.mpr (by exact_mod_cast (K.isRelLowerSet_faces top.property).1.card_pos)
      exact le_antisymm ((mul_le_mul_iff_of_pos_right hpos).mp h₁)
        ((mul_le_mul_iff_of_pos_right hpos).mp h₂)
    have herase : barycentricCoords (eraseWeight w top) = barycentricCoords (eraseWeight z top) := by
      funext v
      have h₁ := barycentricCoords_eraseWeight w top v
      have h₂ := barycentricCoords_eraseWeight z top v
      rw [heq, hcoeff, h₂] at h₁
      exact add_right_cancel h₁.symm
    have ht : top ∈ s := hs ▸ htop
    have hss : s.erase top ⊂ s :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.erase_subset _ _, fun h =>
        (Finset.notMem_erase top s) (h.symm ▸ ht)⟩
    have erase_chain (u : Face K → ℝ)
        (hc : IsChain (· < ·) (positiveSupport u : Set (Face K))) :
        IsChain (· < ·) (positiveSupport (eraseWeight u top) : Set (Face K)) := by
      exact IsChain.mono (by
        rw [support_eraseWeight]
        exact Finset.coe_subset.mpr (Finset.erase_subset _ _)) hc
    have hrec := ih (s.erase top) hss (eraseWeight w top) (eraseWeight z top)
      ((support_eraseWeight w top).trans (congrArg (fun t => t.erase top) hs))
      (eraseWeight_nonneg hw top) (eraseWeight_nonneg hz top)
      (erase_chain w hchainw) (erase_chain z hchainz) herase
    funext f
    by_cases hf : f = top
    · exact hf ▸ hcoeff
    · simpa [eraseWeight, hf] using congrFun hrec f
  · have hs0 := Finset.not_nonempty_iff_eq_empty.mp hne
    have hw0 (f : Face K) : w f = 0 := zero_off_support hw (by rw [hs, hs0]; simp)
    have hsum : (∑ f, z f) = 0 := by
      rw [← sum_barycentricCoords, ← heq, sum_barycentricCoords]
      simp [hw0]
    have hz0 := (Finset.sum_eq_zero_iff_of_nonneg (fun f _ => hz f)).mp hsum
    funext f
    exact (hw0 f).trans (hz0 f (Finset.mem_univ f)).symm

/-- Positive weights along a flag are determined by their old coordinates. -/
theorem toOriginal_injective (K : PreAbstractSimplicialComplex V) :
    Function.Injective (toOriginal K) := by
  intro w z heq
  apply Subtype.ext
  exact chain_weights_injective (positiveSupport w.val) w.val z.val rfl
    (coordinate_data w).1 (coordinate_data z).1
    (subdivided_support w).2.1 (subdivided_support z).2.1 (congrArg Subtype.val heq)

/-- Ordinary barycentric subdivision preserves the actual finite coordinate space. -/
def realizationHomeomorph (K : PreAbstractSimplicialComplex V) : Space (sd K) ≃ₜ Space K := by
  letI : CompactSpace (Space (sd K)) := realizationCompactSpace (sd K)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (toOriginal K) ⟨toOriginal_injective K, toOriginal_surjective K⟩)
    (toOriginal K).continuous

@[simp] theorem realizationHomeomorph_apply (w : Space (sd K)) :
    realizationHomeomorph K w = toOriginal K w := rfl

/-- The homeomorphism restricts to each face subcomplex in the same ambient coordinates. -/
def subcomplexHomeomorph (K P : PreAbstractSimplicialComplex V) :
    FiniteSubcomplexCylinder.Subspace (sd K) (subdivision K P) ≃ₜ
      FiniteSubcomplexCylinder.Subspace K P :=
  (realizationHomeomorph K).subtype fun w => by
    change w.val ∈ realization (subdivision K P) ↔
      (realizationHomeomorph K w).val ∈ realization P
    rw [realizationHomeomorph_apply]
    exact (barycentricCoords_mem_subcomplex_iff w).symm

/-- The relative inclusion is nullhomotopic exactly when its subdivided inclusion is. -/
theorem subcomplex_nullhomotopic_iff (K P : PreAbstractSimplicialComplex V) :
    (ContinuousMap.subtypeVal (FiniteSubcomplexCylinder.Subspace (sd K) (subdivision K P))).Nullhomotopic ↔
      (ContinuousMap.subtypeVal (FiniteSubcomplexCylinder.Subspace K P)).Nullhomotopic := by
  let e := realizationHomeomorph K
  let d := subcomplexHomeomorph K P
  let i := ContinuousMap.subtypeVal (FiniteSubcomplexCylinder.Subspace (sd K) (subdivision K P))
  let j := ContinuousMap.subtypeVal (FiniteSubcomplexCylinder.Subspace K P)
  have hcomm : (toContinuousMap e).comp i = j.comp (toContinuousMap d) := by
    apply ContinuousMap.ext
    intro x
    rfl
  have hforward : ((toContinuousMap e).comp i).comp (toContinuousMap d.symm) = j := by
    rw [hcomm]
    apply ContinuousMap.ext
    intro x
    exact congrArg j (d.apply_symm_apply x)
  have hback : (toContinuousMap e.symm).comp (j.comp (toContinuousMap d)) = i := by
    rw [← hcomm]
    apply ContinuousMap.ext
    intro x
    exact e.symm_apply_apply (i x)
  change i.Nullhomotopic ↔ j.Nullhomotopic
  constructor
  · intro h
    rw [← hforward]
    exact (h.comp_right (toContinuousMap e)).comp_left (toContinuousMap d.symm)
  · intro h
    rw [← hback]
    exact (h.comp_left (toContinuousMap d)).comp_right (toContinuousMap e.symm)

end

end D5.S3.Topology.BarycentricRealization
