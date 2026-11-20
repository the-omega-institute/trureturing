/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FiveCoverExclusion
   generality: I
   mirror-B: none(waiver:standalone-research-source)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Huang sign classes and distance sums exclude five eightfold covers in Q9. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverRigidity
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CoverDistanceSum
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8ParallelCenterPacking
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverPacking
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

/-! The two Huang sign classes at an eightfold cover constrain its distance-four
neighbors. The mixed-axis distance sum forces five putative covers to be parallel,
where the projected centers violate the eight-dimensional packing bound. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FiveCoverExclusion

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsSwitching IsBalanced)
open Q9EightfoldCoverSeparation (EightfoldCover eightfold_cover_distance_ge_four)
open Q9EightfoldCoverRigidity (distance_four_sign_rigidity)
open Q9EightfoldCoverLocal (transverseSign)
open Q9EightfoldCoverPacking (eightfoldCoverEdges mem_eightfoldCoverEdges)
open Q9CoverDistanceSum (coverEndpoint same_axis_of_five_covers)
open private diff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private cover_at_endpoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverSeparation
open private flip_at_other from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
open private sign_transport transverseSign_unit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal
open private chooseEndpointBits fixedMismatch from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CoverDistanceSum
open private huangMatrix cubeParity from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

local notation "edge" x:arg a:arg => ({x, flip x a} : Finset (Q 9))

attribute [local instance] Classical.propDecidable
attribute [local irreducible] eightfoldCoverEdges

variable {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
variable {x y z : Q 9} {a b c : Fin 9}

private def fixedDisagreements (x : Q 9) (a : Fin 9) (y : Q 9) (b : Fin 9) :
    Finset (Fin 9) :=
  ((diff x y).erase a).erase b

/-- The minimum endpoint distance counts disagreements at coordinates fixed by both edges. -/
def coverDistance (x : Q 9) (a : Fin 9) (y : Q 9) (b : Fin 9) : ℕ :=
  (fixedDisagreements x a y b).card

private theorem coverDistance_symm (x y : Q 9) (a b : Fin 9) :
    coverDistance x a y b = coverDistance y b x a := by
  unfold coverDistance
  apply congrArg Finset.card
  ext i
  simp [fixedDisagreements, diff, ne_comm, and_left_comm]

private theorem endpoint_at_fixed {u : Q 9} (hu : u ∈ edge x a) {i : Fin 9}
    (hi : i ≠ a) : u i = x i := by
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl
  · rfl
  · exact flip_at_other x hi.symm

private theorem coverEndpoint_mem (x : Q 9) (a : Fin 9) (s : Bool) :
    coverEndpoint x a s ∈ edge x a := by
  rw [mem_insert, mem_singleton]
  by_cases hs : s = x a
  · left
    ext i
    by_cases h : i = a
    · subst i
      simp [coverEndpoint, hs]
    · simp [coverEndpoint, h]
  · right
    ext i
    by_cases h : i = a
    · subst i
      have he : s = !x a := by cases hxa : x a <;> cases s <;> simp_all
      simp [coverEndpoint, BalancedCriticalSpectrum.flip, he]
    · rw [flip_at_other x (Ne.symm h)]
      simp [coverEndpoint, h]

private theorem fixedDisagreements_eq {u v : Q 9}
    (hu : u ∈ edge x a) (hv : v ∈ edge y b) :
    fixedDisagreements x a y b = fixedDisagreements u a v b := by
  ext i
  by_cases ha : i = a
  · simp [fixedDisagreements, ha]
  by_cases hb : i = b
  · simp [fixedDisagreements, hb]
  simp [fixedDisagreements, diff, ha, hb, endpoint_at_fixed hu ha, endpoint_at_fixed hv hb]

private theorem coverDistance_le {u v : Q 9} (hu : u ∈ edge x a) (hv : v ∈ edge y b) :
    coverDistance x a y b ≤ hammingDist u v := by
  unfold coverDistance
  rw [fixedDisagreements_eq hu hv]
  exact card_le_card (fun i hi => mem_of_mem_erase (mem_of_mem_erase hi))

private theorem closest_endpoints (x y : Q 9) (a b : Fin 9) :
    ∃ u ∈ edge x a, ∃ v ∈ edge y b, diff u v = fixedDisagreements x a y b := by
  obtain ⟨s, t, hbits⟩ := chooseEndpointBits x y a b
  refine ⟨_, coverEndpoint_mem x a s, _, coverEndpoint_mem y b t, ?_⟩
  ext i
  specialize hbits i
  by_cases ha : i = a <;> by_cases hb : i = b <;>
    by_cases hd : coverEndpoint x a s i = coverEndpoint y b t i <;>
    by_cases he : x i = y i <;>
    simp_all [diff, fixedDisagreements, fixedMismatch]

private theorem coverDistance_ge_four
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x a) (hy : EightfoldCover C y b)
    (hxy : edge x a ≠ edge y b) : 4 ≤ coverDistance x a y b := by
  obtain ⟨u, hu, v, hv, hdiff⟩ := closest_endpoints x y a b
  have h := eightfold_cover_distance_ge_four hr hs hx hy hxy hu hv
  change 4 ≤ (diff u v).card at h
  rwa [hdiff] at h

private noncomputable def signClass (sigma : Q 9 → ℝ) (x : Q 9) (a : Fin 9) (s : ℝ) :
    Finset (Fin 9) := by
  classical
  exact (univ.erase a).filter (fun i => transverseSign sigma x i = s)

private theorem distance_four_class
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x a) (hy : EightfoldCover C y b)
    (hxy : edge x a ≠ edge y b) (hd : coverDistance x a y b = 4) :
    fixedDisagreements x a y b = signClass sigma x a 1 ∨
      fixedDisagreements x a y b = signClass sigma x a (-1) := by
  classical
  obtain ⟨u, hu, v, hv, hdiff⟩ := closest_endpoints x y a b
  obtain ⟨huCover, huEdge⟩ := cover_at_endpoint hx hu
  obtain ⟨hvCover, hvEdge⟩ := cover_at_endpoint hy hv
  have huv : hammingDist u v = 4 := by
    change (diff u v).card = 4
    rwa [hdiff]
  obtain ⟨s, _, hsUnit, _, hclass, _⟩ := distance_four_sign_rigidity
    hr hs huCover hvCover (by rwa [huEdge, hvEdge]) huv
  have hc : fixedDisagreements x a y b = signClass sigma u a s := hdiff.symm.trans hclass
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl
  · rcases hsUnit with rfl | rfl
    · exact Or.inl hc
    · exact Or.inr hc
  · let factor := huangMatrix 9 x (flip x a)
    have hfactor : factor = 1 ∨ factor = -1 :=
      sq_eq_one_iff.mp (SupportedEigenSaturation.matrix_sq_of_adj (flip_adj x a))
    have hs' : -(factor * s) = 1 ∨ -(factor * s) = -1 := by
      rcases hfactor with h | h <;> rcases hsUnit with h' | h' <;> simp [h, h']
    have htransport : signClass sigma (flip x a) a s = signClass sigma x a (-(factor * s)) := by
      ext i
      by_cases hi : i = a
      · simp [signClass, hi]
      have ht := sign_transport hs hi (hx.2.2 i hi).1 (hx.2.2 i hi).2
      change transverseSign sigma x i = -(factor * transverseSign sigma (flip x a) i) at ht
      simp only [signClass, mem_filter, mem_erase, mem_univ, and_true, ht, neg_inj]
      rcases hfactor with h | h <;> simp [h]
    rw [htransport] at hc
    rcases hs' with h | h
    · exact Or.inl (hc.trans (congrArg (signClass sigma x a) h))
    · exact Or.inr (hc.trans (congrArg (signClass sigma x a) h))

private theorem distinct_distance_four_classes
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hy : EightfoldCover C y b) (hz : EightfoldCover C z c)
    (hyz : edge y b ≠ edge z c) :
    fixedDisagreements x a y b ≠ fixedDisagreements x a z c := by
  intro he
  obtain ⟨u, hu, v, hv, hdv⟩ := closest_endpoints x y a b
  obtain ⟨u', hu', w, hw, hdw⟩ := closest_endpoints x z a c
  have hsame : ∀ i ≠ a, v i = w i := by
    intro i hi
    have huEq := (endpoint_at_fixed hu hi).trans (endpoint_at_fixed hu' hi).symm
    have hmem : i ∈ diff u v ↔ i ∈ diff u' w := by rw [hdv, hdw, he]
    simp only [diff, mem_filter, mem_univ, true_and, huEq] at hmem
    cases h : u' i <;> cases h' : v i <;> cases h'' : w i <;>
      simp [h, h', h''] at hmem ⊢
  have hsub : diff v w ⊆ {a} := by
    intro i hi
    simp only [diff, mem_filter, mem_univ, true_and] at hi
    exact mem_singleton.mpr (by by_contra h; exact hi (hsame i h))
  have hupper := card_le_card hsub
  have hlower := eightfold_cover_distance_ge_four hr hs hy hz hyz hv hw
  change 4 ≤ (diff v w).card at hlower
  simp at hupper
  omega

/-- Two distinct distance-four neighbors of one eightfold cover are at distance
at least six from each other. If the three axes coincide, their distance is eight. -/
theorem distance_four_neighbors_separate
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma)
    (hx : EightfoldCover C x a) (hy : EightfoldCover C y b) (hz : EightfoldCover C z c)
    (hxy : edge x a ≠ edge y b) (hxz : edge x a ≠ edge z c) (hyz : edge y b ≠ edge z c)
    (h4y : coverDistance x a y b = 4) (h4z : coverDistance x a z c = 4) :
    6 ≤ coverDistance y b z c ∧ (a = b → a = c → coverDistance y b z c = 8) := by
  have hdistinct := distinct_distance_four_classes (x := x) (a := a) hr hs hy hz hyz
  have hclasses : ∀ i ≠ a, (i ∈ fixedDisagreements x a y b) ↔
      i ∉ fixedDisagreements x a z c := by
    intro i hi
    have hunit := transverseSign_unit hs (hx.2.2 i hi).1
    rcases distance_four_class hr hs hx hy hxy h4y with h | h <;>
      rcases distance_four_class hr hs hx hz hxz h4z with h' | h'
    · exact (hdistinct (h.trans h'.symm)).elim
    · rw [h, h']
      rcases hunit with hu | hu <;> norm_num [signClass, hi, hu]
    · rw [h, h']
      rcases hunit with hu | hu <;> norm_num [signClass, hi, hu]
    · exact (hdistinct (h.trans h'.symm)).elim
  obtain ⟨u, hu, v, hv, hdv⟩ := closest_endpoints x y a b
  obtain ⟨u', hu', w, hw, hdw⟩ := closest_endpoints x z a c
  have hsub : univ.erase a ⊆ diff v w := by
    intro i hi
    have hia := (mem_erase.mp hi).1
    have huEq := (endpoint_at_fixed hu hia).trans (endpoint_at_fixed hu' hia).symm
    have hmem := hclasses i hia
    rw [← hdv, ← hdw] at hmem
    simp only [diff, mem_filter, mem_univ, true_and, huEq] at hmem ⊢
    intro he
    rw [he] at hmem
    exact iff_not_self hmem
  have hcard : (univ.erase a).card = 8 := by simp
  have hbound : (((univ.erase a).erase b).erase c).card ≤ coverDistance y b z c := by
    unfold coverDistance
    rw [fixedDisagreements_eq hv hw]
    exact card_le_card (erase_subset_erase c (erase_subset_erase b hsub))
  constructor
  · have h₁ := pred_card_le_card_erase (s := univ.erase a) (a := b)
    have h₂ := pred_card_le_card_erase (s := (univ.erase a).erase b) (a := c)
    omega
  · rintro rfl rfl
    have hupper : coverDistance y a z a ≤ 8 := by
      unfold coverDistance
      exact (card_le_card (show fixedDisagreements y a z a ⊆ univ.erase a by
        intro i hi
        exact mem_erase.mpr ⟨(mem_erase.mp hi).1, mem_univ _⟩)).trans_eq hcard
    simp only [erase_idem, hcard] at hbound
    exact le_antisymm hupper hbound

/-- In any family of distinct eightfold cover edges, each cover has at most two
neighbors at minimum endpoint distance four. -/
theorem card_distance_four_neighbors_le_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (word : ι → Q 9) (axis : ι → Fin 9)
    (hcover : ∀ i, EightfoldCover C (word i) (axis i))
    (hdistinct : ∀ i j, i ≠ j →
      ({word i, flip (word i) (axis i)} : Finset (Q 9)) ≠ {word j, flip (word j) (axis j)})
    (i : ι) :
    (univ.filter fun j => i ≠ j ∧ coverDistance (word i) (axis i) (word j) (axis j) = 4).card
      ≤ 2 := by
  classical
  let label j := fixedDisagreements (word i) (axis i) (word j) (axis j)
  let classes : Finset (Finset (Fin 9)) :=
    {signClass sigma (word i) (axis i) 1, signClass sigma (word i) (axis i) (-1)}
  refine (card_le_card_of_injOn label (t := classes) ?_ ?_).trans card_le_two
  · intro j hj
    have ⟨hne, hd⟩ := (mem_filter.mp hj).2
    rw [mem_coe, mem_insert, mem_singleton]
    exact distance_four_class hr hs (hcover i) (hcover j) (hdistinct i j hne) hd
  · intro j _ k _ he
    by_contra hjk
    exact distinct_distance_four_classes hr hs (hcover j) (hcover k) (hdistinct j k hjk) he

private theorem projected_distance (x y : Q 9) (a : Fin 9) :
    hammingDist (fun i : Fin 8 => x (a.succAbove i)) (fun i : Fin 8 => y (a.succAbove i)) =
      coverDistance x a y a := by
  unfold hammingDist coverDistance fixedDisagreements
  rw [erase_idem]
  refine card_bij (fun i _ => a.succAbove i) ?_ ?_ ?_
  · intro i hi
    exact mem_erase.mpr ⟨a.succAbove_ne i, by simpa [diff] using hi⟩
  · intro i _ j _ hij
    exact Fin.succAbove_right_inj.mp hij
  · intro j hj
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (mem_erase.mp hj).1
    exact ⟨i, by simpa [diff] using (mem_erase.mp hj).2, rfl⟩

private theorem normalized_distance (x y : Q 9) (a : Fin 9) :
    hammingDist (coverEndpoint x a false) (coverEndpoint y a false) = coverDistance x a y a := by
  change (diff (coverEndpoint x a false) (coverEndpoint y a false)).card =
    (fixedDisagreements x a y a).card
  apply congrArg Finset.card
  ext i
  by_cases hi : i = a <;> simp [diff, fixedDisagreements, coverEndpoint, hi]

private theorem no_five_eightfold_covers
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (word : Fin 5 → Q 9) (axis : Fin 5 → Fin 9)
    (hcover : ∀ i, EightfoldCover C (word i) (axis i))
    (hdistinct : ∀ i j, i ≠ j →
      ({word i, flip (word i) (axis i)} : Finset (Q 9)) ≠ {word j, flip (word j) (axis j)}) :
    False := by
  let D i j := coverDistance (word i) (axis i) (word j) (axis j)
  have hmin (i j : Fin 5) (hij : i ≠ j) : 4 ≤ D i j :=
    coverDistance_ge_four hr hs (hcover i) (hcover j) (hdistinct i j hij)
  have hsep (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hj : D i j = 4) (hk : D i k = 4) :
      6 ≤ D j k ∧ (axis i = axis j → axis i = axis k → D j k = 8) :=
    distance_four_neighbors_separate hr hs (hcover i) (hcover j) (hcover k)
      (hdistinct i j hij) (hdistinct i k hik) (hdistinct j k hjk) hj hk
  have hsymm (i j : Fin 5) : D i j = D j i :=
    coverDistance_symm (word i) (word j) (axis i) (axis j)
  have hparallel := same_axis_of_five_covers word axis D
    (fun i j s t => coverDistance_le (coverEndpoint_mem (word i) (axis i) s)
      (coverEndpoint_mem (word j) (axis j) t))
    hsymm hmin (card_distance_four_neighbors_le_two hr hs word axis hcover hdistinct)
    (fun i j k hij hik hjk hi hj =>
      (hsep k i j hik.symm hjk.symm hij ((hsymm k i).trans hi) ((hsymm k j).trans hj)).1)
  let projected (i : Fin 5) (t : Fin 8) := word i ((axis 0).succAbove t)
  let normalized (i : Fin 5) := coverEndpoint (word i) (axis 0) false
  have hprojected (i j : Fin 5) : hammingDist (projected i) (projected j) = D i j := by
    dsimp only [projected, D]
    rw [hparallel i 0, hparallel j 0, projected_distance]
  have hnormalized (i j : Fin 5) : hammingDist (normalized i) (normalized j) = D i j := by
    dsimp only [normalized, D]
    rw [hparallel i 0, hparallel j 0, normalized_distance]
  have hparity (i j : Fin 5) :
      D i j % 2 = 0 ↔ cubeParity (normalized i) = cubeParity (normalized j) := by
    rw [← hnormalized]
    exact distance_parity _ _
  apply Q8ParallelCenterPacking.no_five_parallel_centers projected
    (fun i => cubeParity (normalized i))
  · intro i j hij
    rw [hprojected]
    exact hmin i j hij
  · intro i j h
    rw [hprojected]
    have heven := (hparity i j).mpr h
    omega
  · intro i j h
    rw [hprojected]
    have hij : i ≠ j := fun he => h (congrArg (fun k => cubeParity (normalized k)) he)
    have hge := hmin i j hij
    have hodd := mt (hparity i j).mp h
    omega
  · intro i j k hjk hj hk
    rw [hprojected] at hj hk ⊢
    have hij : i ≠ j := by
      rintro rfl
      simp [D, coverDistance, fixedDisagreements, diff] at hj
    have hik : i ≠ k := by
      rintro rfl
      simp [D, coverDistance, fixedDisagreements, diff] at hk
    exact le_of_eq ((hsep i j k hij hik hjk hj hk).2 (hparallel i j) (hparallel i k)).symm

/-- A balanced induced cubic support in Q9 has at most four eightfold exterior edges. -/
theorem card_eightfoldCoverEdges_le_four (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : (eightfoldCoverEdges C).card ≤ 4 := by
  classical
  by_contra h
  obtain ⟨sigma, hs⟩ := hb
  have hcard : Fintype.card (Fin 5) ≤ Fintype.card ↥(eightfoldCoverEdges C) := by
    simp only [Fintype.card_fin, Fintype.card_coe]
    omega
  obtain ⟨select⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hwitness (i : Fin 5) :
      ∃ x a, EightfoldCover C x a ∧ edge x a = (select i).val :=
    (mem_eightfoldCoverEdges (C := C) (e := (select i).val)).mp (select i).property
  choose word axis hcover he using hwitness
  apply no_five_eightfold_covers hr hs word axis hcover
  intro i j hij heq
  rw [he i, he j] at heq
  exact hij (select.injective (Subtype.ext heq))

#check coverDistance
#check distance_four_neighbors_separate
#check card_distance_four_neighbors_le_two
#check card_eightfoldCoverEdges_le_four
#print axioms coverDistance
#print axioms distance_four_neighbors_separate
#print axioms card_distance_four_neighbors_le_two
#print axioms card_eightfoldCoverEdges_le_four

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FiveCoverExclusion
