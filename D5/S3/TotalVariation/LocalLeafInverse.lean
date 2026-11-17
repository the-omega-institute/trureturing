/- GID: D5/S3/TotalVariation/LocalLeafInverse
   generality: G
   mirror-B: D5/B/S3/TotalVariation/LocalLeafInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local opposite-channel leaves give the sharp three-halves signed inverse bound. -/

import D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope
import D5.S3.TotalVariation.Metric

/-! Finite observation fibres with opposite-channel singleton partners admit
a uniform signed inverse estimate. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.TotalVariation.LocalLeafInverse

open D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope (pushMass)
open D5.S3.TotalVariation.Pinsker (totalVariation)

variable {X U V : Type*} [Fintype X]

/-- The actual observation fibre of x consists only of x. -/
def IsLeaf (f : X → U) (x : X) : Prop := ∀ y, f y = f x → y = x

/-- Every other member of a two-channel ambiguous source's first fibre is
identified by its second observation. This is a combinatorial condition on the
actual maps, independent of the signed mass or an inverse inequality. -/
def OppositeLeaves (f : X → U) (g : X → V) : Prop :=
  ∀ x, ¬ IsLeaf f x → ¬ IsLeaf g x →
    ∀ y, f y = f x → y ≠ x → IsLeaf g y

private def leaves (f : X → U) : Finset X := by
  classical exact Finset.univ.filter (IsLeaf f)

private def centres (f : X → U) (g : X → V) : Finset X := by
  classical exact Finset.univ.filter (fun x => ¬ IsLeaf f x ∧ ¬ IsLeaf g x)

private def partners (f : X → U) (x : X) : Finset X := by
  classical exact (Finset.univ.filter (fun y => f y = f x)).erase x

private lemma mem_leaves (f : X → U) (x : X) : x ∈ leaves f ↔ IsLeaf f x := by
  classical simp [leaves]

private lemma mem_centres (f : X → U) (g : X → V) (x : X) :
    x ∈ centres f g ↔ ¬ IsLeaf f x ∧ ¬ IsLeaf g x := by
  classical simp [centres]

private lemma mem_partners (f : X → U) (x y : X) :
    y ∈ partners f x ↔ y ≠ x ∧ f y = f x := by
  classical simp [partners]

private lemma centres_swap (f : X → U) (g : X → V) : centres f g = centres g f := by
  classical ext x; simp only [mem_centres, and_comm]

private lemma centre_inj (f : X → U) (g : X → V) (hg : OppositeLeaves f g) :
    Set.InjOn f (↑(centres f g) : Set X) := by
  intro x hx y hy he
  by_contra hxy
  have hx' := (mem_centres f g x).mp hx
  have hy' := (mem_centres f g y).mp hy
  exact hy'.2 (hg x hx'.1 hx'.2 y he.symm (Ne.symm hxy))

/-- At most one ambiguous centre uses each first-channel output. Its partners
therefore occupy disjoint opposite-channel singleton fibres. -/
private lemma partner_sum_le (f : X → U) (g : X → V)
    (hg : OppositeLeaves f g) (h : X → ℝ) :
    (∑ x ∈ centres f g, ∑ y ∈ partners f x, |h y|) ≤ ∑ y ∈ leaves g, |h y| := by
  classical
  have hinj := centre_inj f g hg
  have hd : Set.PairwiseDisjoint (↑(centres f g) : Set X) (partners f) := by
    intro x hx z hz hxz
    apply Finset.disjoint_left.mpr
    intro y hyx hyz
    have hyx' := (mem_partners f x y).mp hyx
    have hyz' := (mem_partners f z y).mp hyz
    exact hxz (hinj hx hz (hyx'.2.symm.trans hyz'.2))
  have hs : (centres f g).biUnion (partners f) ⊆ leaves g := by
    intro y hy
    obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
    have hx' := (mem_centres f g x).mp hx
    have hy' := (mem_partners f x y).mp hy
    exact (mem_leaves g y).mpr (hg x hx'.1 hx'.2 y hy'.2 hy'.1)
  rw [← Finset.sum_biUnion hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun y _ _ => abs_nonneg (h y))

variable [Fintype U]

private lemma leaf_mass (f : X → U) (h : X → ℝ) (x : X) (hx : IsLeaf f x) :
    pushMass f h (f x) = h x := by
  classical
  change (∑ y, if f y = f x then h y else 0) = h x
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    exact ite_eq_right (fun he => hy (hx y he))
  · simp

private lemma fibre_triangle (f : X → U) (h : X → ℝ) (x : X) :
    |h x| ≤ |pushMass f h (f x)| + ∑ y ∈ partners f x, |h y| := by
  classical
  let s := Finset.univ.filter (fun y => f y = f x)
  have hx : x ∈ s := by simp [s]
  have decomp : (∑ y ∈ partners f x, h y) + h x = pushMass f h (f x) := by
    have he := Finset.sum_erase_add (s := s) h hx
    change (∑ y ∈ s.erase x, h y) + h x = _
    rw [he]
    change (∑ y ∈ Finset.univ.filter (fun y => f y = f x), h y) =
      ∑ y, if f y = f x then h y else 0
    exact Finset.sum_filter _ _
  calc
    |h x| = |pushMass f h (f x) - ∑ y ∈ partners f x, h y| := by
      congr 1; linarith [decomp]
    _ ≤ |pushMass f h (f x)| + |∑ y ∈ partners f x, h y| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (pushMass f h (f x)) (-(∑ y ∈ partners f x, h y)))
    _ ≤ |pushMass f h (f x)| + ∑ y ∈ partners f x, |h y| :=
      add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs h (partners f x))

/-- Singleton outputs and centre outputs form disjoint subsets of the actual
channel's output coordinates. No output norm is paid for twice. -/
private lemma leaf_centre_mass_le (f : X → U) (g : X → V)
    (hg : OppositeLeaves f g) (h : X → ℝ) :
    (∑ x ∈ leaves f, |h x|) +
      (∑ x ∈ centres f g, |pushMass f h (f x)|) ≤ ∑ u, |pushMass f h u| := by
  classical
  have hiL : Set.InjOn f (↑(leaves f) : Set X) := by
    intro x hx y hy he
    exact (mem_leaves f y).mp hy x he
  have hiC := centre_inj f g hg
  have hleaf : (∑ x ∈ leaves f, |h x|) =
      ∑ u ∈ (leaves f).image f, |pushMass f h u| := by
    rw [Finset.sum_image hiL]
    apply Finset.sum_congr rfl
    intro x hx
    rw [leaf_mass f h x ((mem_leaves f x).mp hx)]
  have hcentre : (∑ x ∈ centres f g, |pushMass f h (f x)|) =
      ∑ u ∈ (centres f g).image f, |pushMass f h u| := by
    rw [Finset.sum_image hiC]
  have hd : Disjoint ((leaves f).image f) ((centres f g).image f) := by
    apply Finset.disjoint_left.mpr
    intro u huL huC
    obtain ⟨x,hx,hxu⟩ := Finset.mem_image.mp huL
    obtain ⟨y,hy,hyu⟩ := Finset.mem_image.mp huC
    have hxy : y = x := (mem_leaves f x).mp hx y (hyu.trans hxu.symm)
    subst y
    exact ((mem_centres f g x).mp hy).1 ((mem_leaves f x).mp hx)
  rw [hleaf,hcentre,← Finset.sum_union hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun u _ _ => abs_nonneg (pushMass f h u))

variable [Fintype V]

/-- A local, weight-independent geometric condition gives a uniform signed
inverse estimate. The conclusion holds for arbitrary real weights, without
nonnegativity or a zero-total-mass premise. -/
theorem signed_l1_le (f : X → U) (g : X → V)
    (hfg : OppositeLeaves f g) (hgf : OppositeLeaves g f) (h : X → ℝ) :
    (∑ x, |h x|) ≤ (3 / 2 : ℝ) *
      ((∑ u, |pushMass f h u|) + ∑ v, |pushMass g h v|) := by
  classical
  let Lf := ∑ x ∈ leaves f, |h x|
  let Lg := ∑ x ∈ leaves g, |h x|
  let B := centres f g
  let C := ∑ x ∈ B, |h x|
  let N := ∑ x ∈ Finset.univ \ B, |h x|
  let Mf := ∑ x ∈ B, |pushMass f h (f x)|
  let Mg := ∑ x ∈ B, |pushMass g h (g x)|
  have split : (∑ x, |h x|) = C + N := by
    exact (Finset.sum_add_sum_compl B (fun x => |h x|)).symm
  have hend : N ≤ Lf + Lg := by
    calc
      N ≤ ∑ x ∈ Finset.univ \ B,
          ((if x ∈ leaves f then |h x| else 0) +
            (if x ∈ leaves g then |h x| else 0)) := by
        apply Finset.sum_le_sum
        intro x hx
        have hn : x ∉ centres f g := (Finset.mem_sdiff.mp hx).2
        have hl : IsLeaf f x ∨ IsLeaf g x := by
          by_contra hs
          push Not at hs
          exact hn ((mem_centres f g x).mpr hs)
        rcases hl with hl | hl
        · simp only [ite_eq_left ((mem_leaves f x).mpr hl)]
          split_ifs <;> linarith [abs_nonneg (h x)]
        · simp only [ite_eq_left ((mem_leaves g x).mpr hl)]
          split_ifs <;> linarith [abs_nonneg (h x)]
      _ ≤ ∑ x, ((if x ∈ leaves f then |h x| else 0) +
            (if x ∈ leaves g then |h x| else 0)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro x _ _
        split_ifs <;> positivity
      _ = Lf + Lg := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Lf, Lg]
  have hmiddle : 2*C ≤ Mf + Mg + Lf + Lg := by
    have hpF := partner_sum_le f g hfg h
    have hpG := partner_sum_le g f hgf h
    rw [← centres_swap f g] at hpG
    have hpoint := Finset.sum_le_sum (s := B) (fun x _ =>
      add_le_add (fibre_triangle f h x) (fibre_triangle g h x))
    simp only [Finset.sum_add_distrib] at hpoint
    dsimp only [C,Mf,Mg,B,Lf,Lg] at *
    linarith
  have hf := leaf_centre_mass_le f g hfg h
  have hg := leaf_centre_mass_le g f hgf h
  rw [← centres_swap f g] at hg
  have hm0 : 0 ≤ Mf + Mg := by
    dsimp [Mf,Mg]; positivity
  change Lf + Mf ≤ _ at hf
  change Lg + Mg ≤ _ at hg
  rw [split]
  linarith

/-- Half-L1 TV inherits the inverse constant; the laws may be arbitrary real
coordinates, with probability laws as a specialization. -/
theorem total_variation_le_sum (f : X → U) (g : X → V)
    (hfg : OppositeLeaves f g) (hgf : OppositeLeaves g f) (p q : X → ℝ) :
    totalVariation p q ≤ (3 / 2 : ℝ) *
      (totalVariation (pushMass f p) (pushMass f q) +
        totalVariation (pushMass g p) (pushMass g q)) := by
  have h := signed_l1_le f g hfg hgf (p-q)
  rw [map_sub,map_sub] at h
  simp only [Pi.sub_apply] at h
  unfold totalVariation
  linarith

/-- Both separate observed errors bounded by epsilon imply an original error
bounded by three epsilon. -/
theorem total_variation_le_max (f : X → U) (g : X → V)
    (hfg : OppositeLeaves f g) (hgf : OppositeLeaves g f) (p q : X → ℝ) :
    totalVariation p q ≤ 3 *
      max (totalVariation (pushMass f p) (pushMass f q))
        (totalVariation (pushMass g p) (pushMass g q)) := by
  have h := total_variation_le_sum f g hfg hgf p q
  have hf := le_max_left (totalVariation (pushMass f p) (pushMass f q))
    (totalVariation (pushMass g p) (pushMass g q))
  have hg := le_max_right (totalVariation (pushMass f p) (pushMass f q))
    (totalVariation (pushMass g p) (pushMass g q))
  linarith

end D5.S3.TotalVariation.LocalLeafInverse
