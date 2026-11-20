/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9MissingPairFourStarShape
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9MissingPairFourStarShape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The opposite fiber at missing-pair equality consists of four separated cubical stars. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairProjectionRefinement
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairSignedFibers

/-! The cubical components in the opposite fiber of Hong–Wu–Xia,
arXiv:2610.09483, §7 Problem 2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairFourStarShape

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeComponentBoundary (directions)
open Q9MissingPairSignedFibers (prefixBits)
open Q9PairProjectionRefinement (missing_pair_halves_eq_twenty_eight)
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private flip_append_prefix flip_append_suffix from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairSignedFibers

local notation "flip" => BalancedCriticalSpectrum.flip

/-- The center and its neighbors obtained by flipping the specified axes. -/
def starVertices (center : Q 7) (axes : Finset (Fin 7)) : Finset (Q 7) :=
  insert center (axes.image (flip center))

/-- Four cubical 3-stars partition the fiber, with no edges between stars. -/
structure FourStarShape (fiber : Q 7 → Prop) (center : Fin 4 → Q 7)
    (axes : Fin 4 → Finset (Fin 7)) : Prop where
  centers_injective : Function.Injective center
  axes_card : ∀ i, (axes i).card = 3
  mem_iff : ∀ x, fiber x ↔ ∃! i, x ∈ starVertices (center i) (axes i)
  separated : ∀ ⦃i j⦄, i ≠ j → ∀ ⦃x y⦄,
    x ∈ starVertices (center i) (axes i) → y ∈ starVertices (center j) (axes j) →
    x ≠ y ∧ ∀ d : Fin 7, flip x d ≠ y

private theorem append_prefix_iff (a b : Bool) (v : Q 9) :
    (∃ x : Q 7, Fin.append (prefixBits a b) x = v) ↔ v 0 = a ∧ v 1 = b := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun d => v (d.natAdd 2), ?_⟩
    funext d
    refine Fin.addCases (m := 2) (n := 7) ?_ ?_ d
    · intro i
      fin_cases i
      · exact h0.symm
      · exact h1.symm
    · exact fun _ => Fin.append_right _ _ _

open Classical in
/-- If prefix `11` is absent and both TRUE halves have size at least 28,
the `00` fiber consists of four separated cubical 3-stars in the seven suffix coordinates. -/
theorem missing_pair_four_star_shape {S : Finset (Q 9)} (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (hmissing : ∀ x : Q 7, Fin.append (prefixBits true true) x ∉ S)
    (h0 : 28 ≤ (S.filter fun v => v 0 = true).card)
    (h1 : 28 ≤ (S.filter fun v => v 1 = true).card) :
    ∃ (center : Fin 4 → Q 7) (axes : Fin 4 → Finset (Fin 7)),
      FourStarShape (fun x => Fin.append (prefixBits false false) x ∈ S) center axes := by
  let join (x : Q 7) := Fin.append (prefixBits false false) x
  let A := S.filter (fun v => v 0 ≠ true ∧ v 1 ≠ true)
  let E (i : Fin 9) := S.filter (fun v => v i ≠ true ∧ flip v i ∈ S)
  let D := E 0 ∩ E 1
  let N := A \ (E 0 ∪ E 1)
  have hmissing' : ¬ ∃ v ∈ S, v 0 = true ∧ v 1 = true := by
    rintro ⟨v, hv, hp⟩
    obtain ⟨x, rfl⟩ := (append_prefix_iff true true v).mpr hp
    exact hmissing x hv
  obtain ⟨_, _, _, hN, hdisjoint, hpartition, hleaf, hcenter⟩ :=
    missing_pair_halves_eq_twenty_eight hsize hreg hb (by decide : (0 : Fin 9) ≠ 1)
      hmissing' h0 h1
  change N.card = 4 at hN
  change Disjoint D N at hdisjoint
  change D ∪ N = A at hpartition
  have hD_A : D ⊆ A := hpartition ▸ Finset.subset_union_left
  have hN_A : N ⊆ A := hpartition ▸ Finset.subset_union_right
  have hDN {v : Q 9} (hd : v ∈ D) (hn : v ∈ N) : False :=
    Finset.disjoint_left.mp hdisjoint hd hn
  have hjoin_mem (x : Q 7) : join x ∈ A ↔ join x ∈ S := by
    simp [A, show join x 0 = false from rfl, show join x 1 = false from rfl]
  have happend {v : Q 9} (hv : v ∈ A) : join (fun d => v (d.natAdd 2)) = v := by
    obtain ⟨_, h0', h1'⟩ := Finset.mem_filter.mp hv
    obtain ⟨x, rfl⟩ := (append_prefix_iff false false v).mpr
      ⟨Bool.eq_false_of_not_eq_true h0', Bool.eq_false_of_not_eq_true h1'⟩
    simp only [join, Fin.append_right]
  have hjoin : Function.Injective join := by
    intro x y h
    funext d
    simpa only [join, Fin.append_right] using congrFun h (d.natAdd 2)
  let e := (Finset.equivFinOfCardEq hN).symm
  let center (i : Fin 4) (d : Fin 7) := (e i : Q 9) (d.natAdd 2)
  have hcenter_join (i : Fin 4) : join (center i) = e i := happend (hN_A (e i).property)
  have hcenter_N (i : Fin 4) : join (center i) ∈ N := by
    rw [hcenter_join]
    exact (e i).property
  have hcenter_inj : Function.Injective center := by
    intro i j h
    apply e.injective
    apply Subtype.ext
    rw [← hcenter_join i, ← hcenter_join j, h]
  have hcenter_all {x : Q 7} (hx : join x ∈ N) : ∃ i, x = center i := by
    obtain ⟨i, hi⟩ := e.surjective ⟨join x, hx⟩
    exact ⟨i, hjoin ((congrArg Subtype.val hi).symm.trans (hcenter_join i).symm)⟩
  have hstep (x : Q 7) (d : Fin 7) : flip (join x) (d.natAdd 2) = join (flip x d) :=
    flip_append_suffix _ _ _
  have haxis_inj : Function.Injective (Fin.natAdd 2 : Fin 7 → Fin 9) := by
    intro i j h
    simpa only [Fin.natAdd_inj] using h
  have haxis {x : Q 7} {k : Fin 9} (hk : k ∈ directions A (join x)) :
      ∃ d : Fin 7, d.natAdd 2 = k := by
    revert hk
    refine Fin.addCases (m := 2) (n := 7) ?_ (fun d _ => ⟨d, rfl⟩) k
    intro i hi
    have hm := (mem_directions A (join x) _).mp hi
    change flip (Fin.append (prefixBits false false) x) (i.castAdd 7) ∈ A at hm
    rw [flip_append_prefix] at hm
    have hbit := Finset.mem_filter.mp hm
    fin_cases i
    · exact (hbit.2.1 rfl).elim
    · exact (hbit.2.2 rfl).elim
  have hleaf_neighbor {x : Q 7} (hx : join x ∈ D) :
      ∃ d : Fin 7, join (flip x d) ∈ N ∧
        ∀ k : Fin 7, join (flip x k) ∈ A → k = d := by
    obtain ⟨k, hk, hn⟩ := hleaf (join x) hx
    obtain ⟨d, rfl⟩ := haxis (hk.symm ▸ Finset.mem_singleton_self _)
    refine ⟨d, (hstep x d) ▸ hn, fun j hj => haxis_inj ?_⟩
    apply Finset.mem_singleton.mp
    rw [← hk]
    exact (mem_directions A (join x) _).mpr ((hstep x j).symm ▸ hj)
  let axes (i : Fin 4) := Finset.univ.filter (fun d : Fin 7 => join (flip (center i) d) ∈ A)
  have haxes (i : Fin 4) (d : Fin 7) :
      d ∈ axes i ↔ d.natAdd 2 ∈ directions A (join (center i)) := by
    simp [axes, mem_directions, hstep]
  have haxes_card (i : Fin 4) : (axes i).card = 3 := by
    rw [← (hcenter (join (center i)) (hcenter_N i)).1]
    apply Finset.card_bij (fun d _ => d.natAdd 2)
    · exact fun d hd => (haxes i d).mp hd
    · exact fun _ _ _ _ h => haxis_inj h
    · intro k hk
      obtain ⟨d, rfl⟩ := haxis hk
      exact ⟨d, (haxes i d).mpr hk, rfl⟩
  have hstar (i : Fin 4) (x : Q 7) :
      x ∈ starVertices (center i) (axes i) ↔
        x = center i ∨ (join x ∈ D ∧ ∃ d : Fin 7, flip x d = center i) := by
    simp only [starVertices, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (rfl | ⟨d, hd, rfl⟩)
      · exact Or.inl rfl
      · have hD := (hcenter (join (center i)) (hcenter_N i)).2 _ ((haxes i d).mp hd)
        exact Or.inr ⟨(hstep _ d) ▸ hD, d, BalancedCriticalSpectrum.flip_flip _ _⟩
    · rintro (rfl | ⟨hx, d, hd⟩)
      · exact Or.inl rfl
      · have he : flip (center i) d = x := by
          rw [← hd, BalancedCriticalSpectrum.flip_flip]
        exact Or.inr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm ▸ hD_A hx⟩, he⟩
  have hstar_A {i : Fin 4} {x : Q 7} (hx : x ∈ starVertices (center i) (axes i)) :
      join x ∈ A := by
    rcases (hstar i x).mp hx with rfl | ⟨hxD, _⟩
    · exact hN_A (hcenter_N i)
    · exact hD_A hxD
  have hunique {i j : Fin 4} {x : Q 7}
      (hi : x ∈ starVertices (center i) (axes i))
      (hj : x ∈ starVertices (center j) (axes j)) : i = j := by
    rcases (hstar i x).mp hi with hi | ⟨hxD, d, hd⟩ <;>
      rcases (hstar j x).mp hj with hj | ⟨hyD, k, hk⟩
    · exact hcenter_inj (hi.symm.trans hj)
    · exact (hDN hyD (hi.symm ▸ hcenter_N i)).elim
    · exact (hDN hxD (hj.symm ▸ hcenter_N j)).elim
    · obtain ⟨l, _, hl⟩ := hleaf_neighbor hxD
      have hdl := hl d (hd.symm ▸ hN_A (hcenter_N i))
      have hkl := hl k (hk.symm ▸ hN_A (hcenter_N j))
      exact hcenter_inj (hd.symm.trans (by rw [hdl, ← hkl, hk]))
  have hclosed {i : Fin 4} {x : Q 7} (hx : x ∈ starVertices (center i) (axes i))
      (d : Fin 7) (hd : join (flip x d) ∈ A) :
      flip x d ∈ starVertices (center i) (axes i) := by
    rcases (hstar i x).mp hx with rfl | ⟨hxD, k, hk⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩))
    · obtain ⟨l, _, hl⟩ := hleaf_neighbor hxD
      have hkl := hl k (hk.symm ▸ hN_A (hcenter_N i))
      exact (hstar i _).mpr (Or.inl (by rw [hl d hd, ← hkl, hk]))
  refine ⟨center, axes, hcenter_inj, haxes_card, ?_, ?_⟩
  · intro x
    change join x ∈ S ↔ _
    rw [← hjoin_mem x]
    constructor
    · intro hx
      have hx' : join x ∈ D ∪ N := hpartition.symm ▸ hx
      obtain ⟨i, hi⟩ : ∃ i, x ∈ starVertices (center i) (axes i) := by
        rcases Finset.mem_union.mp hx' with hxD | hxN
        · obtain ⟨d, hd, _⟩ := hleaf_neighbor hxD
          obtain ⟨i, hi⟩ := hcenter_all hd
          exact ⟨i, (hstar i x).mpr (Or.inr ⟨hxD, d, hi⟩)⟩
        · obtain ⟨i, hi⟩ := hcenter_all hxN
          exact ⟨i, (hstar i x).mpr (Or.inl hi)⟩
      exact ⟨i, hi, fun _ hj => hunique hj hi⟩
    · rintro ⟨i, hi, _⟩
      exact hstar_A hi
  · intro i j hij x y hx hy
    refine ⟨fun he => hij (hunique hx (he.symm ▸ hy)), fun d he => hij ?_⟩
    exact hunique (hclosed hx d (he.symm ▸ hstar_A hy)) (he.symm ▸ hy)

/-- Relabel suffix coordinates by `p` and translate `origin` to the all-false vertex. -/
def suffixAction (p : Equiv.Perm (Fin 7)) (origin : Q 7) : Equiv.Perm (Q 7) where
  toFun x d := x (p.symm d) != origin (p.symm d)
  invFun x d := x (p d) != origin d
  left_inv x := by
    funext d
    simp only [Equiv.symm_apply_apply]
    cases x d <;> cases origin d <;> rfl
  right_inv x := by
    funext d
    simp only [Equiv.apply_symm_apply]
    cases x d <;> cases origin (p.symm d) <;> rfl

/-- The suffix action sends edges in direction `d` to edges in direction `p d`. -/
theorem suffixAction_flip (p : Equiv.Perm (Fin 7)) (origin x : Q 7) (d : Fin 7) :
    suffixAction p origin (flip x d) = flip (suffixAction p origin x) (p d) := by
  funext j
  by_cases hj : j = p d
  · subst j
    simp only [BalancedCriticalSpectrum.flip_apply_same]
    change (flip x d (p.symm (p d)) != origin (p.symm (p d))) =
      !(x (p.symm (p d)) != origin (p.symm (p d)))
    simp only [Equiv.symm_apply_apply, BalancedCriticalSpectrum.flip_apply_same]
    cases x d <;> cases origin d <;> rfl
  · have hd : p.symm j ≠ d := fun he => hj (p.symm_apply_eq.mp he)
    simp [suffixAction, BalancedCriticalSpectrum.flip, hj, hd]

/-- Extend the suffix action to the nine-cube by retaining the two prefix bits. -/
def coordinateAction (p : Equiv.Perm (Fin 7)) (origin : Q 7) : Equiv.Perm (Q 9) :=
  (Fin.appendEquiv 2 7).symm.trans
    ((Equiv.prodCongr (Equiv.refl (Q 2)) (suffixAction p origin)).trans (Fin.appendEquiv 2 7))

theorem coordinateAction_append (p : Equiv.Perm (Fin 7)) (origin : Q 7) (u : Q 2) (x : Q 7) :
    coordinateAction p origin (Fin.append u x) = Fin.append u (suffixAction p origin x) := by
  change coordinateAction p origin (Fin.appendEquiv 2 7 (u, x)) =
    Fin.appendEquiv 2 7 (u, suffixAction p origin x)
  simp [coordinateAction]

open Classical in
/-- A prefix-preserving cube action puts the first center at zero and its axes
at the first three suffix coordinates. All four stars retain their separation. -/
theorem FourStarShape.normalize {S : Finset (Q 9)} {center : Fin 4 → Q 7}
    {axes : Fin 4 → Finset (Fin 7)}
    (h : FourStarShape (fun x => Fin.append (prefixBits false false) x ∈ S) center axes) :
    ∃ p : Equiv.Perm (Fin 7),
      let g := suffixAction p (center 0)
      let T := S.map (coordinateAction p (center 0)).toEmbedding
      FourStarShape (fun x => Fin.append (prefixBits false false) x ∈ T)
        (g ∘ center) (fun i => (axes i).map p.toEmbedding) ∧
      g (center 0) = (fun _ => false) ∧
      (axes 0).map p.toEmbedding = {0, 1, 2} := by
  let rootAxes : Finset (Fin 7) := {0, 1, 2}
  have hrootAxes : rootAxes.card = 3 := by decide
  let e := (Finset.equivFinOfCardEq (h.axes_card 0)).trans
    (Finset.equivFinOfCardEq hrootAxes).symm
  let f (d : Fin 7) := if hd : d ∈ axes 0 then (e ⟨d, hd⟩ : Fin 7) else d
  have hf : Set.InjOn f (axes 0 : Set (Fin 7)) := by
    intro d hd j hj he
    change d ∈ axes 0 at hd
    change j ∈ axes 0 at hj
    simp only [f, dite_eq_left hd, dite_eq_left hj] at he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  obtain ⟨q, hq⟩ := Finset.exists_equiv_extend_of_card_eq
    (t := Finset.univ) (by simp) (Finset.subset_univ ((axes 0).image f)) hf
  let p := q.trans (Equiv.subtypeUnivEquiv Finset.mem_univ)
  have hp : (axes 0).map p.toEmbedding = rootAxes := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hj
      change (q d : Fin 7) ∈ rootAxes
      rw [hq d hd]
      simpa only [f, dite_eq_left hd] using (e ⟨d, hd⟩).property
    · rw [Finset.card_map, h.axes_card, hrootAxes]
  let g := suffixAction p (center 0)
  have hstar (i : Fin 4) (x : Q 7) :
      g x ∈ starVertices (g (center i)) ((axes i).map p.toEmbedding) ↔
        x ∈ starVertices (center i) (axes i) := by
    simp only [starVertices, Finset.mem_insert, Finset.mem_image, Finset.mem_map]
    constructor
    · rintro (he | ⟨_, ⟨d, hd, rfl⟩, he⟩)
      · exact Or.inl (g.injective he)
      · exact Or.inr ⟨d, hd, g.injective ((suffixAction_flip p _ _ d).trans he)⟩
    · rintro (rfl | ⟨d, hd, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨p d, ⟨d, hd, rfl⟩, (suffixAction_flip p _ _ d).symm⟩
  refine ⟨p, ?_, ?_, hp⟩
  · refine ⟨g.injective.comp h.centers_injective, ?_, ?_, ?_⟩
    · intro i
      rw [Finset.card_map, h.axes_card]
    · intro y
      obtain ⟨x, rfl⟩ := g.surjective y
      change (Fin.append (prefixBits false false) (suffixAction p (center 0) x) ∈
        S.map (coordinateAction p (center 0)).toEmbedding) ↔ _
      rw [← coordinateAction_append, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      change _ ↔ ∃! i, g x ∈ starVertices (g (center i)) ((axes i).map p.toEmbedding)
      simp_rw [hstar]
      exact h.mem_iff x
    · intro i j hij x y hx hy
      obtain ⟨x, rfl⟩ := g.surjective x
      obtain ⟨y, rfl⟩ := g.surjective y
      obtain ⟨hne, hsep⟩ := h.separated hij ((hstar i x).mp hx) ((hstar j y).mp hy)
      refine ⟨g.injective.ne hne, fun d he => hsep (p.symm d) (g.injective ?_)⟩
      calc
        g (flip x (p.symm d)) = flip (g x) (p (p.symm d)) := suffixAction_flip p _ x _
        _ = g y := by simpa only [Equiv.apply_symm_apply] using he
  · funext d
    change (center 0 (p.symm d) != center 0 (p.symm d)) = false
    cases center 0 (p.symm d) <;> rfl

#check starVertices
#check FourStarShape
#check FourStarShape.centers_injective
#check FourStarShape.axes_card
#check FourStarShape.mem_iff
#check FourStarShape.separated
#check missing_pair_four_star_shape
#check suffixAction
#check suffixAction_flip
#check coordinateAction
#check coordinateAction_append
#check FourStarShape.normalize

#print axioms starVertices
#print axioms FourStarShape
#print axioms missing_pair_four_star_shape
#print axioms suffixAction
#print axioms suffixAction_flip
#print axioms coordinateAction
#print axioms coordinateAction_append
#print axioms FourStarShape.normalize

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairFourStarShape
