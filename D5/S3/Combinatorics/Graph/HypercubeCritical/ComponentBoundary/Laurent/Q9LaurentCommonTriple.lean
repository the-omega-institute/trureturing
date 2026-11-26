/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonTriple
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonTriple
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: A shared Laurent direction triple forces three-point fibers and descends the complementary integer height. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LaurentGainPartition

/-! A shared direction triple gives three-point fibers in the complementary
six axes and preserves the complementary height on each fiber. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9LaurentCommonTriple

open Finset
open BalancedCriticalSpectrum (Q)
local notation "cubeFlip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (directions mem_directions flip_injective)
open Q9IsotropicHuang (parity)
open Q9LaurentGainPartition (Side Exponent axis LaurentIdentity)
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private flip_parity mem_twoStepPaths from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LaurentGainPartition

abbrev Axes := Fin 3 ⊕ Fin 6 ≃ Fin 9

def inside (e : Axes) (x : Q 9) : Q 3 := fun i => x (e (.inl i))
def outside (e : Axes) (x : Q 9) : Q 6 := fun i => x (e (.inr i))

def commonAxes (e : Axes) : Finset (Fin 9) := univ.image fun i : Fin 3 => e (.inl i)

private theorem outside_flip (e : Axes) (x : Q 9) (i : Fin 3) :
    outside e (cubeFlip x (e (.inl i))) = outside e x := by
  funext j
  have h : e (.inr j) ≠ e (.inl i) := fun h => Sum.inr_ne_inl (e.injective h)
  simp only [outside, BalancedCriticalSpectrum.flip, Function.update_of_ne h]

private theorem parity_split (e : Axes) (x : Q 9) :
    parity x = cubeParity (inside e x) + cubeParity (outside e x) := by
  change (∑ i : Fin 9, x i) = (∑ i : Fin 3, x (e (.inl i))) + ∑ j : Fin 6, x (e (.inr j))
  rw [← Equiv.sum_comp e x, Fintype.sum_sum_type]

private theorem card_Q3_parity : ∀ b : Bool,
    ((univ : Finset (Q 3)).filter fun x => cubeParity x = b).card = 4 := by
  decide +kernel

noncomputable def fiber (C : Finset (Q 9)) (b : Bool) (e : Axes) (u : Q 6) :
    Finset (Q 9) := C.filter fun x => parity x = b ∧ outside e x = u

private theorem fiber_card_le_four (C : Finset (Q 9)) (b : Bool) (e : Axes) (u : Q 6) :
    (fiber C b e u).card ≤ 4 := by
  classical
  rw [← card_Q3_parity (b - cubeParity u)]
  apply card_le_card_of_injOn (inside e)
  · intro x hx
    change x ∈ fiber C b e u at hx
    obtain ⟨_, hb, hu⟩ := mem_filter.mp hx
    have he := parity_split e x
    rw [hb, hu] at he
    exact mem_filter.mpr ⟨mem_univ _, eq_sub_of_add_eq he.symm⟩
  · intro x hx y hy hxy
    change x ∈ fiber C b e u at hx
    change y ∈ fiber C b e u at hy
    have hx' := (mem_filter.mp hx).2.2
    have hy' := (mem_filter.mp hy).2.2
    funext k
    obtain ⟨i, rfl⟩ := e.surjective k
    cases i with
    | inl i => exact congrFun hxy i
    | inr i => exact congrFun (hx'.trans hy'.symm) i

/-- A type-S center has three neighbors, one along each axis in `S`. -/
noncomputable def star (e : Axes) (c : Q 9) : Finset (Q 9) :=
  univ.image fun i : Fin 3 => cubeFlip c (e (.inl i))

private theorem mem_star {e : Axes} {c x : Q 9} :
    x ∈ star e c ↔ ∃ i : Fin 3, cubeFlip c (e (.inl i)) = x := by
  simp [star]

private theorem star_card (e : Axes) (c : Q 9) : (star e c).card = 3 := by
  rw [star, card_image_of_injective, card_univ, Fintype.card_fin]
  exact (flip_injective c).comp (e.injective.comp Sum.inl_injective)

/-- Every selected-parity vertex has a unique internal neighbor of the common type. -/
def UniqueCommonNeighbor (C : Finset (Q 9)) (b : Bool) (e : Axes) : Prop :=
  ∀ x : Side C b, ∃! i : Fin 3,
    cubeFlip x.val (e (.inl i)) ∈ C ∧ directions C (cubeFlip x.val (e (.inl i))) = commonAxes e

open scoped Classical in
/-- Membership of the common triple in every Laurent partition gives
uniqueness of the corresponding internal neighbor. -/
theorem uniqueCommonNeighbor_of_laurent {C : Finset (Q 9)} {b : Bool} {e : Axes}
    {a : Side C b → Exponent}
    (hC : ((D5.S3.Combinatorics.Graph.Hypercube.hypercube 9).induce
      (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a)
    (hcover : ∀ x : Side C b, ∃ i ∈ directions C x.val,
      directions C (cubeFlip x.val i) = commonAxes e) : UniqueCommonNeighbor C b e := by
  intro x
  obtain ⟨i, hi, heq⟩ := hcover x
  have hiS : i ∈ commonAxes e := by
    rw [← heq]
    exact (mem_directions C _ _).mpr (by rw [BalancedCriticalSpectrum.flip_flip]; exact x.property.1)
  obtain ⟨j, _, rfl⟩ := mem_image.mp hiS
  refine ⟨j, ⟨(mem_directions C _ _).mp hi, heq⟩, ?_⟩
  intro l hl
  obtain ⟨_, _, huniq⟩ := Q9LaurentGainPartition.neighbor_triples_partition hC h x
  let k := e (.inl (0 : Fin 3))
  have hk : k ∈ commonAxes e := mem_image.mpr ⟨0, mem_univ _, rfl⟩
  obtain ⟨m, _, hm⟩ := huniq k
  have hjm := hm ⟨e (.inl j), hi⟩ (by
    change k ∈ directions C (cubeFlip x.val (e (.inl j)))
    rwa [heq])
  have hlm := hm ⟨e (.inl l), (mem_directions C _ _).mpr hl.1⟩ (by
    change k ∈ directions C (cubeFlip x.val (e (.inl l)))
    rwa [hl.2])
  exact Sum.inl.inj (e.injective (congrArg Subtype.val (hlm.trans hjm.symm)))

private theorem star_subset_fiber {C : Finset (Q 9)} {b : Bool} {e : Axes} {c : Q 9} {u : Q 6}
    (hdir : directions C c = commonAxes e) (hb : parity c = !b) (hu : outside e c = u) :
    star e c ⊆ fiber C b e u := by
  intro x hx
  obtain ⟨i, rfl⟩ := mem_star.mp hx
  refine mem_filter.mpr ⟨(mem_directions C c _).mp ?_, ?_, (outside_flip e c i).trans hu⟩
  · rw [hdir, commonAxes]
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
  · rw [flip_parity, hb, Bool.not_not]

/-- The three vertices over a projected point all belong to the same common
star. Two different stars in one fiber would require six vertices of a
single parity in a three-cube. -/
theorem exists_star_over_projection {C : Finset (Q 9)} {b : Bool} {e : Axes}
    (hcommon : UniqueCommonNeighbor C b e) (x : Side C b) :
    ∃ (c : Q 9), c ∈ C ∧ directions C c = commonAxes e ∧
      fiber C b e (outside e x.val) = star e c := by
  classical
  obtain ⟨i, ⟨hc, hdir⟩, _⟩ := hcommon x
  let c := cubeFlip x.val (e (.inl i))
  have hsub := star_subset_fiber hdir (by rw [flip_parity, x.property.2])
    (outside_flip e x.val i)
  refine ⟨c, hc, hdir, Subset.antisymm ?_ hsub⟩
  intro y hy
  obtain ⟨hyC, hyb, hyOut⟩ := mem_filter.mp hy
  obtain ⟨j, ⟨hd, hdDir⟩, _⟩ := hcommon ⟨y, hyC, hyb⟩
  let d := cubeFlip y (e (.inl j))
  have hdSub := star_subset_fiber hdDir (by rw [flip_parity, hyb])
    ((outside_flip e y j).trans hyOut)
  have hcd : c = d := by
    by_contra hne
    have hdisj : Disjoint (star e c) (star e d) := by
      refine disjoint_left.mpr ?_
      intro z hzC hzD
      obtain ⟨k, hk⟩ := mem_star.mp hzC
      obtain ⟨l, hl⟩ := mem_star.mp hzD
      have hk' : cubeFlip z (e (.inl k)) = c := by rw [← hk, BalancedCriticalSpectrum.flip_flip]
      have hl' : cubeFlip z (e (.inl l)) = d := by rw [← hl, BalancedCriticalSpectrum.flip_flip]
      obtain ⟨hzmem, hzb, _⟩ := mem_filter.mp (hsub hzC)
      obtain ⟨a, _, ha⟩ := hcommon ⟨z, hzmem, hzb⟩
      have hka : k = a := ha k (by
        change cubeFlip z (e (.inl k)) ∈ C ∧ _
        rw [hk']
        exact ⟨hc, hdir⟩)
      have hla : l = a := ha l (by
        change cubeFlip z (e (.inl l)) ∈ C ∧ _
        rw [hl']
        exact ⟨hd, hdDir⟩)
      exact hne (hk'.symm.trans ((congrArg (fun i => cubeFlip z (e (.inl i)))
        (hka.trans hla.symm)).trans hl'))
    have hcard := card_le_card (union_subset hsub hdSub)
    rw [card_union_of_disjoint hdisj, star_card, star_card] at hcard
    have hfour := fiber_card_le_four C b e (outside e x.val)
    omega
  rw [hcd]
  exact mem_star.mpr ⟨j, BalancedCriticalSpectrum.flip_flip _ _⟩

/-- The Laurent exponent descends to the six-axis projection. -/
theorem exponent_eq_outside {C : Finset (Q 9)} {b : Bool} {e : Axes} {a : Side C b → Exponent}
    (h : LaurentIdentity a) (hcommon : UniqueCommonNeighbor C b e) (x y : Side C b)
    (hout : outside e x.val = outside e y.val) (r : Fin 6) :
    a x (e (.inr r)) = a y (e (.inr r)) := by
  classical
  obtain ⟨c, hc, _, hf⟩ := exists_star_over_projection hcommon x
  have hx : x.val ∈ star e c := hf ▸ mem_filter.mpr ⟨x.property.1, x.property.2, rfl⟩
  have hy : y.val ∈ star e c := hf ▸ mem_filter.mpr ⟨y.property.1, y.property.2, hout.symm⟩
  obtain ⟨i, hi⟩ := mem_star.mp hx
  obtain ⟨j, hj⟩ := mem_star.mp hy
  by_cases hij : i = j
  · subst j
    rw [show x = y from Subtype.ext (hi.symm.trans hj)]
  have hb : cubeFlip x.val (e (.inl i)) = c := by rw [← hi, BalancedCriticalSpectrum.flip_flip]
  have hne : e (.inl i) ≠ e (.inl j) := fun h => hij (Sum.inl.inj (e.injective h))
  let p : Q9LaurentGainPartition.PathAt C x.val := ⟨(e (.inl i), e (.inl j)),
    mem_twoStepPaths.mpr ⟨(mem_directions C _ _).mpr (hb.symm ▸ hc),
      (mem_directions C _ _).mpr (by rw [hb, hj]; exact y.property.1), hne⟩⟩
  have hend : Q9LaurentGainPartition.pathEnd x p = y := by
    apply Subtype.ext
    change cubeFlip (cubeFlip x.val (e (.inl i))) (e (.inl j)) = y.val
    rw [hb, hj]
  have hgain := congrFun (Q9LaurentGainPartition.path_exponent_and_gain h x p).2.2 (e (.inr r))
  rw [hend] at hgain
  have hne' (k : Fin 3) : e (.inr r) ≠ e (.inl k) := fun h => Sum.inr_ne_inl (e.injective h)
  change a y (e (.inr r)) - a x (e (.inr r)) =
    axis (e (.inl j)) (e (.inr r)) - axis (e (.inl i)) (e (.inr r)) at hgain
  simp only [axis, hne', ite_false, sub_zero] at hgain
  omega

#print axioms uniqueCommonNeighbor_of_laurent
#print axioms exists_star_over_projection
#print axioms exponent_eq_outside

end Q9LaurentCommonTriple
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
