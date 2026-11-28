import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFibreCapacity
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
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
open private minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

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
/-- The union of the images under all forbidden parity corrections packs
disjointly from the other component in the adjacent fibre. Two corrections
give an image saturated under the involution that flips their two axes. -/
theorem adjacent_fibre_capacity {C D : Finset (Q 9)} (b : Bool) (z : Q 9)
    (e : Fin 5 ↪ Fin 9) {i : Fin 9} (hi : i ∉ univ.map e)
    (B : Finset (Fin 9)) (hB : B ⊆ univ.map e)
    (hmask : ∀ j ∈ B, ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2) :
    let A := univ.map e
    let L := (restrictToFibre C A z).filter (fun x => parity x = b)
    let R := (restrictToFibre D A (flip z i)).filter (fun x => parity x = b)
    (B.biUnion fun j => L.image (fun x : Q 9 => flip (flip x i) j)).card + R.card ≤ 16 := by
  intro A L R
  let T := restrictToFibre univ A (flip z i)
  let F := T.filter (fun x => parity x = b)
  let tau := fun (j : Fin 9) (x : Q 9) => flip (flip x i) j
  let transported := B.biUnion (fun j => L.image (tau j))
  have hL : transported ⊆ F := by
    intro y hy
    obtain ⟨j, hjB, hy⟩ := mem_biUnion.mp hy
    have hj : j ∈ A := hB hjB
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
  have hdisj : Disjoint transported R := disjoint_left.mpr (by
    intro y hyL hyR
    obtain ⟨j, hjB, hyL⟩ := mem_biUnion.mp hyL
    have hij : i ≠ j := fun h => hi (h.symm ▸ hB hjB)
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hyL
    obtain ⟨hx, hp⟩ := mem_filter.mp hx
    have hxC := (mem_filter.mp hx).1
    have hyD := (mem_filter.mp (mem_filter.mp hyR).1).1
    have hd := diff_pair x hij
    have hdist : hammingDist x (tau j x) = 2 := by
      change (differingAxes x (tau j x)).card = 2
      rw [show differingAxes x (tau j x) = {i, j} from hd, card_pair hij]
    exact hmask j hjB (mem_minimumDisplacements.mpr ⟨x, hxC, tau j x, hyD, hp, hdist, hd⟩))
  have hpacked : transported.card + R.card ≤ F.card := by
    rw [← card_union_of_disjoint hdisj]
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
  let j := e 0
  have hj : j ∈ A := mem_map.mpr ⟨0, mem_univ _, rfl⟩
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
  change transported.card + R.card ≤ 16
  omega

open Classical in
/-- A selected vertex in one fibre forces two holes for the other component
in the adjacent fibre when both parity corrections are forbidden. -/
theorem adjacent_fibre_two_holes {C D : Finset (Q 9)} (b : Bool) (z : Q 9)
    (e : Fin 5 ↪ Fin 9) {i j k : Fin 9} (hi : i ∉ univ.map e)
    (hj : j ∈ univ.map e) (hk : k ∈ univ.map e) (hjk : j ≠ k)
    (hmj : ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hmk : ({i, k} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (hne : ((restrictToFibre C (univ.map e) z).filter (fun x => parity x = b)).Nonempty) :
    ((restrictToFibre D (univ.map e) (flip z i)).filter (fun x => parity x = b)).card ≤ 14 := by
  let L := (restrictToFibre C (univ.map e) z).filter (fun x => parity x = b)
  let B : Finset (Fin 9) := {j, k}
  let moved (l : Fin 9) := L.image (fun x : Q 9 => flip (flip x i) l)
  have hB : B ⊆ univ.map e := by
    intro l hl
    rcases mem_insert.mp hl with rfl | hl
    · exact hj
    · obtain rfl := mem_singleton.mp hl
      exact hk
  have hm (l : Fin 9) (hl : l ∈ B) :
      ({i, l} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2 := by
    rcases mem_insert.mp hl with rfl | hl
    · exact hmj
    · obtain rfl := mem_singleton.mp hl
      exact hmk
  have hbound := adjacent_fibre_capacity (C := C) (D := D) b z e hi B hB hm
  obtain ⟨x, hx⟩ := hne
  let y := flip x i
  have hne : flip y j ≠ flip y k := by
    intro he
    have h := congrFun he j
    simpa [BalancedCriticalSpectrum.flip, hjk] using h
  have hsub : ({flip y j, flip y k} : Finset (Q 9)) ⊆ B.biUnion moved := by
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact mem_biUnion.mpr ⟨j, by simp [B], mem_image.mpr ⟨x, hx, rfl⟩⟩
    · obtain rfl := mem_singleton.mp ha
      exact mem_biUnion.mpr ⟨k, by simp [B], mem_image.mpr ⟨x, hx, rfl⟩⟩
  have htwo := card_le_card hsub
  rw [card_pair hne] at htwo
  change (B.biUnion moved).card + _ ≤ 16 at hbound
  omega

private def closedPattern (p : Q 4) : Finset (Q 4) :=
  insert p (univ.image (fun i : Fin 4 => BalancedCriticalSpectrum.flip p i))

private theorem closedPattern_card : ∀ p, (closedPattern p).card = 5 := by decide

private theorem closedPattern_union_large :
    ∀ p q, p ≠ q → 6 ≤ (closedPattern p ∪ closedPattern q).card := by decide

open scoped BigOperators in
private theorem count_pure_patterns (a d : Q 4 → ℕ)
    (htotal : 129 ≤ ∑ p, (a p + d p))
    (hcap : ∀ p, a p + d p ≤ 16)
    (hmixed : ∀ p, 0 < a p → 0 < d p → a p + d p ≤ 6)
    (hholes : ∀ (p : Q 4) (i : Fin 4),
      0 < a (flip p i) → 0 < d (flip p i) → a p + d p ≤ 14) :
    let M := univ.filter (fun p => 0 < a p ∧ 0 < d p)
    let P := univ.filter (fun p => (0 < a p ∧ d p = 0) ∨ (a p = 0 ∧ 0 < d p))
    M.card ≤ 11 ∧ 5 ≤ P.card := by
  intro M P
  let H := P.filter (fun p => 14 < a p + d p)
  have hdis : Disjoint M P := disjoint_left.mpr (by
    intro p hm hp
    have hm' := (mem_filter.mp hm).2
    have hp' := (mem_filter.mp hp).2
    rcases hp' with hp' | hp' <;> omega)
  have hcount : M.card + P.card ≤ 16 := by
    rw [← card_union_of_disjoint hdis]
    exact (card_le_univ _).trans (by decide)
  have hH : H.card ≤ P.card := card_le_card (filter_subset _ _)
  have hweighted : 129 ≤ 6 * M.card + 14 * P.card + 2 * H.card := by
    apply htotal.trans
    calc
      _ ≤ ∑ p, ((if p ∈ M then 6 else 0) + (if p ∈ P then 14 else 0) +
          (if p ∈ H then 2 else 0)) := by
        apply sum_le_sum
        intro p _
        by_cases hm : p ∈ M
        · have h := (mem_filter.mp hm).2
          have hp : p ∉ P := fun hp => disjoint_left.mp hdis hm hp
          have hh : p ∉ H := fun hh => hp (mem_filter.mp hh).1
          simpa [hm, hp, hh] using hmixed p h.1 h.2
        · by_cases hp : p ∈ P
          · by_cases hh : p ∈ H
            · simpa [hm, hp, hh] using hcap p
            · have hle : a p + d p ≤ 14 := by
                exact Nat.le_of_not_gt (fun h => hh (mem_filter.mpr ⟨hp, h⟩))
              simpa [hm, hp, hh] using hle
          · have hh : p ∉ H := fun hh => hp (mem_filter.mp hh).1
            simp only [hm, hp, hh, if_false, Nat.add_zero]
            simp only [M, P, mem_filter, mem_univ, true_and] at hm hp
            omega
      _ = _ := by simp [sum_add_distrib, mul_comm]
  have hclosed (p : Q 4) (hp : p ∈ H) : closedPattern p ⊆ univ \ M := by
    intro q hq
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hm
    rcases mem_insert.mp hq with rfl | hq
    · exact disjoint_left.mp hdis hm (mem_filter.mp hp).1
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hq
      have h := (mem_filter.mp hm).2
      exact (Nat.not_lt_of_ge (hholes p i h.1 h.2)) (mem_filter.mp hp).2
  have hcomp : (univ \ M).card + M.card = 16 := by
    rw [card_sdiff_add_card_eq_card (subset_univ M)]
    decide
  have hM : M.card ≤ 11 := by
    by_contra! h
    have hzero : H.card = 0 := by
      apply card_eq_zero.mpr
      apply not_nonempty_iff_eq_empty.mp
      intro ⟨p, hp⟩
      have he := card_le_card (hclosed p hp)
      rw [closedPattern_card] at he
      omega
    omega
  refine ⟨hM, ?_⟩
  by_contra! hp
  have hone : H.card ≤ 1 := by
    by_contra! hh
    obtain ⟨p, q, hp, hq, hne⟩ := one_lt_card_iff.mp hh
    have hsub := union_subset (hclosed p hp) (hclosed q hq)
    have he := (closedPattern_union_large p q hne).trans (card_le_card hsub)
    omega
  omega

open Classical in
open scoped BigOperators in
/-- Two inactive correction axes give enough holes in the four-coordinate
quotient to rule out twelve mixed fibres and force five nonempty pure fibres. -/
theorem five_axis_fibre_counts {C D : Finset (Q 9)} (b : Bool)
    (e : Fin 5 ↪ Fin 9) (g : Fin 4 ↪ Fin 9)
    (hcover : ∀ k, k ∉ univ.map e ↔ ∃ i, g i = k)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hinside : ∀ T ∈ minimumDisplacements C D b 2, ¬ T ⊆ univ.map e)
    {j k : Fin 9} (hj : j ∈ univ.map e) (hk : k ∈ univ.map e) (hjk : j ≠ k)
    (hmissing : ∀ i ∉ univ.map e,
      ({i, j} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2 ∧
      ({i, k} : Finset (Fin 9)) ∉ minimumDisplacements C D b 2)
    (htotal : 129 ≤ (C.filter (fun x => parity x = b)).card +
      (D.filter (fun x => parity x = b)).card) :
    let bank (S : Finset (Q 9)) (p : Q 4) :=
      (S.filter (fun x => parity x = b)).filter (fun x => (fun i => x (g i)) = p)
    let M := univ.filter (fun p => (bank C p).Nonempty ∧ (bank D p).Nonempty)
    let P := univ.filter (fun p => ((bank C p).Nonempty ∧ bank D p = ∅) ∨
      (bank C p = ∅ ∧ (bank D p).Nonempty))
    M.card ≤ 11 ∧ 5 ≤ P.card := by
  intro bank M P
  let A := univ.map e
  let project (x : Q 9) : Q 4 := fun i => x (g i)
  let lift (p : Q 4) (l : Fin 9) : Bool :=
    if h : ∃ i, g i = l then p (Classical.choose h) else false
  have hproj (p : Q 4) : project (lift p) = p := by
    funext i
    have hi : ∃ j, g j = g i := ⟨i, rfl⟩
    change (if h : ∃ j, g j = g i then p (Classical.choose h) else false) = p i
    rw [dif_pos hi, g.injective (Classical.choose_spec hi)]
  have hbank (S : Finset (Q 9)) (x : Q 9) :
      bank S (project x) = (restrictToFibre S A x).filter (fun y => parity y = b) := by
    ext y
    have h : project y = project x ↔ sameFibre A x y := by
      constructor
      · intro he l hl
        obtain ⟨i, rfl⟩ := (hcover l).mp hl
        exact congrFun he i
      · intro he
        funext i
        exact he (g i) ((hcover (g i)).mpr ⟨i, rfl⟩)
    simp only [bank, restrictToFibre, mem_filter]
    change (_ ∧ project y = project x) ↔ _
    rw [h]
    tauto
  have hflip (p : Q 4) (i : Fin 4) :
      project (flip (lift p) (g i)) = flip p i := by
    funext l
    have he : lift p (g l) = p l := congrFun (hproj p) l
    by_cases hl : l = i
    · subst l
      simp [project, he]
    · simp [project, BalancedCriticalSpectrum.flip, hl, g.injective.ne hl, he]
  have hsum (S : Finset (Q 9)) :
      (S.filter (fun x => parity x = b)).card = ∑ p, (bank S p).card := by
    exact card_eq_sum_card_fiberwise (f := project) (fun _ _ => mem_univ _)
  rw [hsum C, hsum D, ← sum_add_distrib] at htotal
  have hmixed (p : Q 4) (ha : (bank C p).Nonempty) (hd : (bank D p).Nonempty) :
      (bank C p).card + (bank D p).card ≤ 6 := by
    rw [← hproj p, hbank C] at ha
    rw [← hproj p, hbank D] at hd
    rw [← hproj p, hbank C, hbank D]
    exact mixed_five_axis_fibre_capacity b (lift p) e hsep hinside ha hd
  have hcap (S : Finset (Q 9)) (p : Q 4) : (bank S p).card ≤ 16 := by
    let i := g 0
    have hi : i ∉ A := (hcover i).mpr ⟨0, rfl⟩
    have hc := adjacent_fibre_capacity (C := ∅) (D := S) b (flip (lift p) i) e
      hi ∅ (empty_subset _) (by simp)
    rw [← hproj p, hbank S]
    simpa using hc
  have htwo (S T : Finset (Q 9)) (p : Q 4) (i : Fin 4)
      (hmj : ({g i, j} : Finset (Fin 9)) ∉ minimumDisplacements S T b 2)
      (hmk : ({g i, k} : Finset (Fin 9)) ∉ minimumDisplacements S T b 2)
      (hs : (bank S (flip p i)).Nonempty) : (bank T p).card ≤ 14 := by
    have hi : g i ∉ A := (hcover (g i)).mpr ⟨i, rfl⟩
    rw [← hflip p i, hbank S] at hs
    have hc := adjacent_fibre_two_holes b (flip (lift p) (g i)) e hi hj hk hjk hmj hmk hs
    rw [← hproj p, hbank T]
    simpa using hc
  have hb (p : Q 4) : (bank C p).card + (bank D p).card ≤ 16 := by
    by_cases ha : (bank C p).Nonempty
    · by_cases hd : (bank D p).Nonempty
      · exact (hmixed p ha hd).trans (by decide)
      · simpa [not_nonempty_iff_eq_empty.mp hd] using hcap C p
    · simpa [not_nonempty_iff_eq_empty.mp ha] using hcap D p
  have hh (p : Q 4) (i : Fin 4) (ha : (bank C (flip p i)).Nonempty)
      (hd : (bank D (flip p i)).Nonempty) : (bank C p).card + (bank D p).card ≤ 14 := by
    have hmask := hmissing (g i) ((hcover (g i)).mpr ⟨i, rfl⟩)
    by_cases hC : (bank C p).Nonempty
    · by_cases hD : (bank D p).Nonempty
      · exact (hmixed p hC hD).trans (by decide)
      · rw [minimumDisplacements_swap_two C D b] at hmask
        simpa [not_nonempty_iff_eq_empty.mp hD] using htwo D C p i hmask.1 hmask.2 hd
    · simpa [not_nonempty_iff_eq_empty.mp hC] using htwo C D p i hmask.1 hmask.2 ha
  simpa only [M, P, card_pos, card_eq_zero] using
    count_pure_patterns (fun p => (bank C p).card) (fun p => (bank D p).card) htotal hb
      (fun p ha hd => hmixed p (card_pos.mp ha) (card_pos.mp hd))
      (fun p i ha hd => hh p i (card_pos.mp ha) (card_pos.mp hd))

#print axioms shared_midpoint_neighbors_preserved
#print axioms mixed_five_axis_fibre_capacity
#print axioms adjacent_fibre_capacity
#print axioms adjacent_fibre_two_holes
#print axioms five_axis_fibre_counts

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre
