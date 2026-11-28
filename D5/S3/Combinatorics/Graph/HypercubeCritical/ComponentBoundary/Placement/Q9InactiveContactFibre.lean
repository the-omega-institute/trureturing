import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFibreCapacity
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap

/-! A shared midpoint keeps both contact rows inside one inactive-coordinate fibre. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre

open Finset
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open private differingAxes differingAxes_foldl_flip mem_minimumDisplacements parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

/-- The fibre of a midpoint obtained by freezing all coordinates outside `A`. -/
def sameFibre (A : Finset (Fin 9)) (z u : Q 9) : Prop :=
  ∀ k, k ∉ A → u k = z k

open Classical in
/-- Restrict a support to the fibre through `z` with active coordinates `A`. -/
noncomputable def restrictToFibre (S : Finset (Q 9)) (A : Finset (Fin 9)) (z : Q 9) : Finset (Q 9) :=
  S.filter (sameFibre A z)

private theorem diff_pair (u : Q 9) {i j : Fin 9} (hij : i ≠ j) :
    differingAxes u (flip (flip u i) j) = {i, j} := by
  simpa using differingAxes_foldl_flip [i, j] (by simp [hij]) u

private theorem cross_pair_axes_active
    {C D : Finset (Q 9)} {A : Finset (Fin 9)} {b : Bool} {z : Q 9}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hpar : ∀ x ∈ C, parity x = b)
    (hmask : ∀ T ∈ minimumDisplacements C D b 2, T ⊆ A)
    {i j : Fin 9} (hi : flip z i ∈ C) (hj : flip z j ∈ D) :
    i ∈ A ∧ j ∈ A := by
  have hij : i ≠ j := by
    intro he
    subst j
    have h := hsep _ hi _ hj
    simp at h
  have hpair : ({i, j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
    have he : differingAxes (flip z i) (flip z j) = {i, j} := by
      simpa only [BalancedCriticalSpectrum.flip_flip] using diff_pair (flip z i) hij
    have hd : hammingDist (flip z i) (flip z j) = 2 := by
      change (differingAxes (flip z i) (flip z j)).card = 2
      rw [he, Finset.card_pair hij]
    exact mem_minimumDisplacements.mpr ⟨_, hi, _, hj, hpar _ hi, hd, he⟩
  have hsub := hmask _ hpair
  exact ⟨hsub (by simp), hsub (by simp)⟩

private theorem flip_same_fibre {A : Finset (Fin 9)} {z : Q 9} {i : Fin 9}
    (hi : i ∈ A) : sameFibre A z (flip z i) := by
  intro k hk
  have hki : k ≠ i := by
    intro h
    exact hk (h ▸ hi)
  simp [sameFibre, BalancedCriticalSpectrum.flip, hki]

private theorem directions_restrictToFibre_eq
    {S : Finset (Q 9)} {A : Finset (Fin 9)} {z : Q 9}
    (hactive : directions S z ⊆ A) :
    directions S z = directions (restrictToFibre S A z) z := by
  classical
  ext i
  constructor
  · intro hi
    apply (mem_directions _ _ _).mpr
    refine mem_filter.mpr ⟨(mem_directions S z i).mp hi, ?_⟩
    exact flip_same_fibre (hactive hi)
  · intro hi
    exact (mem_directions S z i).mpr (mem_filter.mp ((mem_directions _ _ _).mp hi)).1

/-- If every realized two-axis contact mask is active, both banks retain all
their neighbors at a shared midpoint after freezing the inactive coordinates. -/
theorem shared_midpoint_neighbors_preserved
    {C D : Finset (Q 9)} {A : Finset (Fin 9)} {b : Bool} {z : Q 9}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hparC : ∀ x ∈ C, parity x = b)
    (hmask : ∀ T ∈ minimumDisplacements C D b 2, T ⊆ A)
    {i j : Fin 9} (hi : flip z i ∈ C) (hj : flip z j ∈ D) :
    directions C z = directions (restrictToFibre C A z) z ∧
      directions D z = directions (restrictToFibre D A z) z := by
  have hCactive : directions C z ⊆ A := by
    intro k hk
    exact (cross_pair_axes_active hsep hparC hmask
      ((mem_directions C z k).mp hk) hj).1
  have hDactive : directions D z ⊆ A := by
    intro k hk
    exact (cross_pair_axes_active hsep hparC hmask hi
      ((mem_directions D z k).mp hk)).2
  exact ⟨directions_restrictToFibre_eq hCactive,
    directions_restrictToFibre_eq hDactive⟩

open private even_diff_of_parity_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap

open Classical in
/-- A five-axis fibre containing no realized distance-two contact mask has room
for at most six selected vertices of a fixed parity if both components occur. -/
theorem mixed_five_axis_fibre_capacity {C D : Finset (Q 9)} (b : Bool) (z : Q 9)
    (e : Fin 5 ↪ Fin 9)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hmask : ∀ T ∈ minimumDisplacements C D b 2, ¬ T ⊆ univ.map e) :
    let A := univ.map e
    let L := (restrictToFibre C A z).filter (fun x => parity x = b)
    let R := (restrictToFibre D A z).filter (fun x => parity x = b)
    L.Nonempty → R.Nonempty → L.card + R.card ≤ 6 := by
  intro A L R hL hR
  let project (x : Q 9) : Fin 5 → Bool := fun i => x (e i)
  have hmem {S : Finset (Q 9)} {x : Q 9}
      (h : x ∈ (restrictToFibre S A z).filter (fun x => parity x = b)) :
      x ∈ S ∧ sameFibre A z x ∧ parity x = b := by
    obtain ⟨hx, hp⟩ := mem_filter.mp h
    obtain ⟨hs, hf⟩ := mem_filter.mp hx
    exact ⟨hs, hf, hp⟩
  have hdist {x y : Q 9} (hx : sameFibre A z x) (hy : sameFibre A z y) :
      hammingDist (project x) (project y) = hammingDist x y := by
    unfold hammingDist
    apply card_bij (fun i _ => e i)
    · intro i hi
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
    · intro i _ j _ hij
      exact e.injective hij
    · intro j hj
      have hd := (mem_filter.mp hj).2
      have hA : j ∈ A := by
        by_contra hn
        exact hd ((hx j hn).trans (hy j hn).symm)
      obtain ⟨i, _, rfl⟩ := mem_map.mp hA
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, hd⟩, rfl⟩
  have hcard (S : Finset (Q 9))
      (hS : ∀ x ∈ S, sameFibre A z x) : (S.image project).card = S.card := by
    apply card_image_of_injOn
    intro x hx y hy he
    funext j
    by_cases hj : j ∈ A
    · obtain ⟨i, _, rfl⟩ := mem_map.mp hj
      exact congrFun he i
    · exact (hS x hx j hj).trans (hS y hy j hj).symm
  have hcross : ∀ u ∈ L.image project, ∀ v ∈ R.image project, hammingDist u v = 4 := by
    intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hv
    obtain ⟨hxC, hxA, hxb⟩ := hmem hx
    obtain ⟨hyD, hyA, hyb⟩ := hmem hy
    rw [hdist hxA hyA]
    have hle : hammingDist x y ≤ 5 := by
      rw [← hdist hxA hyA]
      simpa using (hammingDist_le_card_fintype
        (x := project x) (y := project y))
    have hge := hsep x hxC y hyD
    have heven : hammingDist x y % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd (even_diff_of_parity_eq x y (hxb.trans hyb.symm)).two_dvd
    have hne : hammingDist x y ≠ 2 := by
      intro he
      have hm : differingAxes x y ∈ minimumDisplacements C D b 2 :=
        mem_minimumDisplacements.mpr ⟨x, hxC, y, hyD, hxb, he, rfl⟩
      apply hmask _ hm
      intro j hj
      by_contra hn
      exact (mem_filter.mp hj).2 ((hxA j hn).trans (hyA j hn).symm)
    omega
  have hbound := Q9FiveAxisFibreCapacity.cross_distance_four_card_bound
    (L.image project) (R.image project) (hL.image _) (hR.image _) hcross
  rw [hcard L (fun x hx => (hmem hx).2.1), hcard R (fun x hx => (hmem hx).2.1)] at hbound
  exact hbound.2.2.1

open Classical in
/-- A forbidden pair of flips gives a packing inequality between adjacent
fibres on the chosen parity. One flip moves between the fibres and the other
corrects the parity. -/
theorem adjacent_fibre_capacity {C D : Finset (Q 9)} (b : Bool) (z : Q 9)
    (e : Fin 5 ↪ Fin 9) {i j : Fin 9} (hi : i ∉ univ.map e) (hj : j ∈ univ.map e)
    (hmask : ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2) :
    let A := univ.map e
    let L := (restrictToFibre C A z).filter (fun x => parity x = b)
    let R := (restrictToFibre D A (flip z i)).filter (fun x => parity x = b)
    L.card + R.card ≤ 16 := by
  intro A L R
  have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
  let T := restrictToFibre univ A (flip z i)
  let F := T.filter (fun x => parity x = b)
  let tau := fun x : Q 9 => flip (flip x i) j
  have hinj : Function.Injective tau := by
    intro x y he
    have h := congrArg (fun z : Q 9 => flip (flip z j) i) he
    simpa [tau] using h
  have hL : L.image tau ⊆ F := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    obtain ⟨hx, hp⟩ := mem_filter.mp hx
    have hf := (mem_filter.mp hx).2
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · intro k hk
      have hkn : k ≠ j := fun h => hk (h.symm ▸ hj)
      by_cases hki : k = i
      · subst k
        simp [tau, BalancedCriticalSpectrum.flip, hkn, hf i hi]
      · simp [tau, BalancedCriticalSpectrum.flip, hkn, hki, hf k hk]
    · simp only [tau, parity_flip, Bool.not_not, hp]
  have hR : R ⊆ F := by
    intro x hx
    obtain ⟨hx, hp⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩, hp⟩
  have hdisj : Disjoint (L.image tau) R := disjoint_left.mpr (by
    intro y hyL hyR
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hyL
    obtain ⟨hx, hp⟩ := mem_filter.mp hx
    have hxC := (mem_filter.mp hx).1
    have hyD := (mem_filter.mp (mem_filter.mp hyR).1).1
    have hd := diff_pair x hij
    have hdist : hammingDist x (tau x) = 2 := by
      change (differingAxes x (tau x)).card = 2
      rw [show differingAxes x (tau x) = {i, j} from hd, card_pair hij]
    exact hmask (mem_minimumDisplacements.mpr ⟨x, hxC, tau x, hyD, hp, hdist, hd⟩))
  have hpacked : L.card + R.card ≤ F.card := by
    rw [← card_image_of_injective L hinj, ← card_union_of_disjoint hdisj]
    exact card_le_card (union_subset hL hR)
  have hT : T.card ≤ 32 := by
    let project := fun x : Q 9 => fun k : Fin 5 => x (e k)
    have hc : (T.image project).card = T.card := by
      apply card_image_of_injOn
      intro x hx y hy hxy
      have hxF := (mem_filter.mp hx).2
      have hyF := (mem_filter.mp hy).2
      funext k
      by_cases hk : k ∈ A
      · obtain ⟨a, _, rfl⟩ := mem_map.mp hk
        exact congrFun hxy a
      · exact (hxF k hk).trans (hyF k hk).symm
    rw [← hc]
    exact (card_le_univ _).trans (by decide)
  let G := T.filter (fun x => parity x ≠ b)
  have hFG : F.card = G.card := by
    apply card_bij' (fun x _ => flip x j) (fun x _ => flip x j)
    · intro x hx
      obtain ⟨hx, hp⟩ := mem_filter.mp hx
      have hf := (mem_filter.mp hx).2
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
      · intro k hk
        have hkn : k ≠ j := fun h => hk (h.symm ▸ hj)
        simp [BalancedCriticalSpectrum.flip, hkn, hf k hk]
      · rw [parity_flip, hp]
        cases b <;> decide
    · intro x hx
      obtain ⟨hx, hp⟩ := mem_filter.mp hx
      have hf := (mem_filter.mp hx).2
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
      · intro k hk
        have hkn : k ≠ j := fun h => hk (h.symm ▸ hj)
        simp [BalancedCriticalSpectrum.flip, hkn, hf k hk]
      · exact (parity_flip x j).trans (Bool.not_eq_iff.mpr hp)
    · intro x _
      exact BalancedCriticalSpectrum.flip_flip x j
    · intro x _
      exact BalancedCriticalSpectrum.flip_flip x j
  have hsum : F.card + G.card = T.card :=
    card_filter_add_card_filter_not (s := T) (fun x => parity x = b)
  omega

#print axioms shared_midpoint_neighbors_preserved
#print axioms mixed_five_axis_fibre_capacity
#print axioms adjacent_fibre_capacity

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre
