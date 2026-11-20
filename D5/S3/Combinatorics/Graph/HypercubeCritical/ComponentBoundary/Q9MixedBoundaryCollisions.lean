/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Mixed boundary collisions count distance-two pairs with a shared internal direction. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryEdgeTranslations

/-! Mixed collisions between two separated supports in the nine-dimensional cube. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj IsBalanced IsSwitching)
open Q9BoundaryEdgeTranslations
open private flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private mem_internalEdges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryEdgeTranslations

local notation "flip" => BalancedCriticalSpectrum.flip
local notation "multiplicity" => Q9BoundaryEdgeTranslations.multiplicity

attribute [local instance] Classical.propDecidable

/-- Disjoint ambient supports with no cube edge between them. -/
def Separated (C D : Finset (Q 9)) : Prop :=
  Disjoint C D ∧ ∀ c ∈ C, ∀ d ∈ D, ¬ (hypercube 9).Adj c d

private theorem Separated.symm {C D : Finset (Q 9)} (h : Separated C D) :
    Separated D C :=
  ⟨h.1.symm, fun d hd c hc hadj => h.2 c hc d hd hadj.symm⟩

private theorem outside_other {C D : Finset (Q 9)} (h : Separated C D)
    {x : Q 9} {i : Fin 9} (hx : flip x i ∈ C) : x ∉ D :=
  fun hxD => h.2 _ hx _ hxD (flip_adj x i).symm

private theorem flip_at_other (x : Q 9) {i t : Fin 9} (hit : i ≠ t) :
    flip x i t = x t := by
  simp [BalancedCriticalSpectrum.flip, Function.update_of_ne hit.symm]

private theorem mem_witness {S : Finset (Q 9)} {x : Q 9} {t i : Fin 9} :
    ((x, t), i) ∈ witnesses S ↔
      x ∈ S ∧ flip x t ∈ S ∧ x t = false ∧ i ≠ t ∧
        flip x i ∉ S ∧ flip (flip x t) i ∉ S := by
  simp [witnesses, transverseExterior, and_assoc]

private theorem witnesses_union {C D : Finset (Q 9)} (h : Separated C D) :
    witnesses (C ∪ D) = witnesses C ∪ witnesses D := by
  ext ⟨⟨x, t⟩, i⟩
  simp only [Finset.mem_union, mem_witness, not_or]
  constructor
  · rintro ⟨hxC | hxD, hyC | hyD, hb, hit, hx, hy⟩
    · exact Or.inl ⟨hxC, hyC, hb, hit, hx.1, hy.1⟩
    · exact (h.2 _ hxC _ hyD (flip_adj x t)).elim
    · exact (h.2 _ hyC _ hxD (flip_adj x t).symm).elim
    · exact Or.inr ⟨hxD, hyD, hb, hit, hx.2, hy.2⟩
  · rintro (⟨hx, hy, hb, hit, houx, houy⟩ | ⟨hx, hy, hb, hit, houx, houy⟩)
    · exact ⟨Or.inl hx, Or.inl hy, hb, hit,
        ⟨houx,
          outside_other h (i := i) (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx)⟩,
        ⟨houy,
          outside_other h (i := i) (by simpa only [BalancedCriticalSpectrum.flip_flip] using hy)⟩⟩
    · exact ⟨Or.inr hx, Or.inr hy, hb, hit,
        ⟨outside_other h.symm (i := i)
          (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx), houx⟩,
        ⟨outside_other h.symm (i := i)
          (by simpa only [BalancedCriticalSpectrum.flip_flip] using hy), houy⟩⟩

/-- Each image edge has exactly the sum of the two separate witness multiplicities. -/
theorem multiplicity_union {C D : Finset (Q 9)} (h : Separated C D) (e : Edge) :
    multiplicity (C ∪ D) e = multiplicity C e + multiplicity D e := by
  unfold Q9BoundaryEdgeTranslations.multiplicity
  rw [witnesses_union h, Finset.filter_union, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  rintro ⟨⟨x, t⟩, i⟩ hx hy
  exact Finset.disjoint_left.mp h.1 (mem_witness.mp (Finset.mem_filter.mp hx).1).1
    (mem_witness.mp (Finset.mem_filter.mp hy).1).1

private theorem collisionCount_eq_sum (S : Finset (Q 9)) :
    collisionCount S = ∑ e : Edge, (multiplicity S e).choose 2 := by
  unfold collisionCount
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  have hz : multiplicity S e = 0 := by
    unfold Q9BoundaryEdgeTranslations.multiplicity
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hw, heq⟩ := Finset.mem_filter.mp hw
    exact he (heq ▸ translatedEdges_subset_boundaryEdges S (Finset.mem_image_of_mem _ hw))
  simp [hz]

private theorem choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have step (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ n 1
    rw [Nat.add_succ, step (a + b), step b, ih, Nat.mul_succ]
    omega

/-- The mixed term in the union's collision count counts one witness from each support. -/
theorem collisionCount_union {C D : Finset (Q 9)} (h : Separated C D) :
    collisionCount (C ∪ D) = collisionCount C + collisionCount D +
      ∑ e : Edge, multiplicity C e * multiplicity D e := by
  simp only [collisionCount_eq_sum, multiplicity_union h, choose_two_add, Finset.sum_add_distrib]

private def imageAxes (S : Finset (Q 9)) (e : Edge) : Finset (Fin 9) :=
  Finset.univ.filter fun i =>
    e.1 e.2 = false ∧ i ≠ e.2 ∧
      flip e.1 i ∈ S ∧ flip (flip e.1 i) e.2 ∈ S ∧
      e.1 ∉ S ∧ flip e.1 e.2 ∉ S

private theorem mem_imageAxes {S : Finset (Q 9)} {x : Q 9} {t i : Fin 9} :
    i ∈ imageAxes S (x, t) ↔ x t = false ∧ i ≠ t ∧
      flip x i ∈ S ∧ flip (flip x i) t ∈ S ∧ x ∉ S ∧ flip x t ∉ S := by
  simp [imageAxes]

private theorem card_imageAxes (S : Finset (Q 9)) (e : Edge) :
    (imageAxes S e).card = multiplicity S e := by
  obtain ⟨x, t⟩ := e
  unfold Q9BoundaryEdgeTranslations.multiplicity
  refine Finset.card_nbij' (fun i => ((flip x i, t), i)) Prod.snd ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨hb, hit, hx, hy, hox, hoy⟩ := mem_imageAxes.mp hi
    exact Finset.mem_filter.mpr ⟨mem_witness.mpr
      ⟨hx, hy, (flip_at_other x hit).trans hb, hit, by simpa using hox,
        by simpa only [flip_comm (flip x i) t i, BalancedCriticalSpectrum.flip_flip] using hoy⟩,
      by simp [translate]⟩
  · rintro ⟨⟨y, u⟩, i⟩ hw
    change ((y, u), i) ∈ (witnesses S).filter (fun w => translate w = (x, t)) at hw
    obtain ⟨hwitness, he⟩ := Finset.mem_filter.mp hw
    change (flip y i, u) = (x, t) at he
    cases he
    obtain ⟨hy, hy', hb, hi, hox, hoy⟩ := mem_witness.mp hwitness
    exact mem_imageAxes.mpr ⟨(flip_at_other y hi).trans hb, hi, by simpa using hy,
      by simpa using hy', hox, by simpa only [flip_comm y t i] using hoy⟩
  · intro i _
    rfl
  · rintro ⟨⟨y, u⟩, i⟩ hw
    obtain ⟨_, he⟩ := Finset.mem_filter.mp hw
    change (flip y i, u) = (x, t) at he
    cases he
    simp

/-- The triples counted by the mixed term, with a direction internal at both vertices. -/
def mixedTriples (C D : Finset (Q 9)) : Finset (Q 9 × Q 9 × Fin 9) :=
  (C.product (D.product Finset.univ)).filter fun (c, d, t) =>
    hammingDist c d = 2 ∧ flip c t ∈ C ∧ flip d t ∈ D

private theorem mem_mixedTriples {C D : Finset (Q 9)} {c d : Q 9} {t : Fin 9} :
    (c, d, t) ∈ mixedTriples C D ↔
      c ∈ C ∧ d ∈ D ∧ hammingDist c d = 2 ∧ flip c t ∈ C ∧ flip d t ∈ D := by
  simp [mixedTriples, and_assoc]

private abbrev MixedPair := Edge × (Fin 9 × Fin 9)

private def mixedFiber (C D : Finset (Q 9)) (e : Edge) : Finset MixedPair :=
  ({e} : Finset Edge).product ((imageAxes C e).product (imageAxes D e))

private def mixedPairs (C D : Finset (Q 9)) : Finset MixedPair :=
  Finset.univ.biUnion (mixedFiber C D)

private theorem mem_mixedPairs (C D : Finset (Q 9)) (x : Q 9) (t i j : Fin 9) :
    ((x, t), (i, j)) ∈ mixedPairs C D ↔
      i ∈ imageAxes C (x, t) ∧ j ∈ imageAxes D (x, t) := by
  simp [mixedPairs, mixedFiber]

private theorem card_mixedPairs (C D : Finset (Q 9)) :
    (mixedPairs C D).card = ∑ e : Edge, multiplicity C e * multiplicity D e := by
  unfold mixedPairs
  rw [Finset.card_biUnion]
  · simp [mixedFiber, Finset.card_product, card_imageAxes]
  · intro e _ f _ hef
    apply Finset.disjoint_left.mpr
    intro pair hp hq
    have he : pair.1 = e := Finset.mem_singleton.mp (Finset.mem_product.mp hp).1
    have hf : pair.1 = f := Finset.mem_singleton.mp (Finset.mem_product.mp hq).1
    exact hef (he.symm.trans hf)

-- Use the membership and cardinality lemmas without reducing the ambient enumeration.
attribute [local irreducible] mixedPairs

private theorem two_flip_disagreements (c : Q 9) {i j : Fin 9} (hij : i ≠ j) :
    (Finset.univ.filter fun k => c k ≠ flip (flip c i) j k) = {i, j} := by
  ext k
  by_cases hi : k = i
  · subst k
    simp [flip_at_other (flip c i) hij.symm]
  by_cases hj : k = j
  · subst k
    simp [flip_at_other c hij]
  · simp [flip_at_other (flip c i) (Ne.symm hj), flip_at_other c (Ne.symm hi), hi, hj]

private theorem distinct_flip_disagreements (x : Q 9) {i j : Fin 9} (hij : i ≠ j) :
    (Finset.univ.filter fun k => flip x i k ≠ flip x j k) = {i, j} := by
  simpa only [BalancedCriticalSpectrum.flip_flip] using two_flip_disagreements (flip x i) hij

private theorem ordered_two_flips {c d : Q 9} (hd : hammingDist c d = 2) :
    ∃ i j : Fin 9, i < j ∧ d = flip (flip c i) j := by
  obtain ⟨i, j, hij, hset⟩ := Finset.card_eq_two.mp hd
  have rebuild {i j : Fin 9} (hne : i ≠ j)
      (hs : (Finset.univ.filter fun k => c k ≠ d k) = {i, j}) :
      d = flip (flip c i) j := by
    funext k
    have heq := Finset.ext_iff.mp (hs.trans (two_flip_disagreements c hne).symm) k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heq
    cases hc : c k <;> simpa [hc] using heq
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, rebuild hij hset⟩
  · exact ⟨j, i, h, rebuild hij.symm (by simpa only [Finset.pair_comm] using hset)⟩

private theorem ordered_axes_unique {i j k l : Fin 9} (hij : i < j) (hkl : k < l)
    (he : ({i, j} : Finset (Fin 9)) = {k, l}) : i = k ∧ j = l := by
  have hi : i = k ∨ i = l := by
    have : i ∈ ({k, l} : Finset (Fin 9)) := he ▸ Finset.mem_insert_self _ _
    simpa using this
  have hk : k = i ∨ k = j := by
    have : k ∈ ({i, j} : Finset (Fin 9)) := he.symm ▸ Finset.mem_insert_self _ _
    simpa using this
  have h_ik : i = k := by
    rcases hi with hi | hi
    · exact hi
    rcases hk with hk | hk <;> omega
  subst k
  have hj : j ∈ ({i, l} : Finset (Fin 9)) := he ▸ Finset.mem_insert_of_mem (by simp)
  exact ⟨rfl, (show j = i ∨ j = l by simpa using hj).resolve_left hij.ne.symm⟩

-- Axis order selects one of the two endpoints of the normalized exterior edge.
private def chosenEndpoint (x : Q 9) (t i j : Fin 9) : Q 9 :=
  if i < j then x else flip x t

private def mixedPairToTriple (p : MixedPair) : Q 9 × Q 9 × Fin 9 :=
  let ⟨(x, t), (i, j)⟩ := p
  let z := chosenEndpoint x t i j
  (flip z i, flip z j, t)

private theorem mixedPair_geometry {C D : Finset (Q 9)} (h : Separated C D)
    {x : Q 9} {t i j : Fin 9} (hp : ((x, t), (i, j)) ∈ mixedPairs C D) :
    x t = false ∧ i ≠ j ∧ i ≠ t ∧ j ≠ t ∧
      (flip x i ∈ C ∧ flip (flip x i) t ∈ C) ∧
      (flip x j ∈ D ∧ flip (flip x j) t ∈ D) := by
  rw [mem_mixedPairs C D x t i j] at hp
  obtain ⟨hi, hj⟩ := hp
  obtain ⟨hb, hit, hc, hc', _, _⟩ := mem_imageAxes.mp hi
  obtain ⟨_, hjt, hd, hd', _, _⟩ := mem_imageAxes.mp hj
  exact ⟨hb, fun he => Finset.disjoint_left.mp h.1 hc (he ▸ hd), hit, hjt, ⟨hc, hc'⟩, ⟨hd, hd'⟩⟩

private theorem mixedPair_mem_of_neighbors {C D : Finset (Q 9)} (h : Separated C D)
    {x : Q 9} {t i j : Fin 9} (hb : x t = false) (hit : i ≠ t) (hjt : j ≠ t)
    (hc : flip x i ∈ C) (hc' : flip (flip x i) t ∈ C)
    (hd : flip x j ∈ D) (hd' : flip (flip x j) t ∈ D) :
    ((x, t), (i, j)) ∈ mixedPairs C D := by
  rw [mem_mixedPairs C D x t i j]
  exact ⟨
    mem_imageAxes.mpr ⟨hb, hit, hc, hc', outside_other h.symm hd,
      outside_other h.symm (by rwa [flip_comm x t j])⟩,
    mem_imageAxes.mpr ⟨hb, hjt, hd, hd', outside_other h hc,
      outside_other h (by rwa [flip_comm x t i])⟩⟩

private theorem mixedPairToTriple_mem {C D : Finset (Q 9)} (h : Separated C D) :
    Set.MapsTo mixedPairToTriple (mixedPairs C D) (mixedTriples C D) := by
  rintro ⟨⟨x, t⟩, i, j⟩ hp
  change ((x, t), (i, j)) ∈ mixedPairs C D at hp
  obtain ⟨_, hij, _, _, ⟨hc, hc'⟩, ⟨hd, hd'⟩⟩ := mixedPair_geometry h hp
  apply mem_mixedTriples.mpr
  let z := chosenEndpoint x t i j
  have hdist : hammingDist (flip z i) (flip z j) = 2 := by
    unfold hammingDist
    rw [distinct_flip_disagreements z hij]
    simp [hij]
  refine ⟨?_, ?_, hdist, ?_, ?_⟩
  · by_cases ho : i < j
    · simpa [z, chosenEndpoint, ho] using hc
    · simpa [z, chosenEndpoint, ho, flip_comm x t i] using hc'
  · by_cases ho : i < j
    · simpa [z, chosenEndpoint, ho] using hd
    · simpa [z, chosenEndpoint, ho, flip_comm x t j] using hd'
  · by_cases ho : i < j
    · simpa [z, chosenEndpoint, ho] using hc'
    · simpa [z, chosenEndpoint, ho, flip_comm x t i] using hc
  · by_cases ho : i < j
    · simpa [z, chosenEndpoint, ho] using hd'
    · simpa [z, chosenEndpoint, ho, flip_comm x t j] using hd

private theorem mixedPairToTriple_inj {C D : Finset (Q 9)} (h : Separated C D) :
    Set.InjOn mixedPairToTriple (mixedPairs C D) := by
  rintro ⟨⟨x, t⟩, i, j⟩ hp ⟨⟨y, u⟩, k, l⟩ hq he
  change (flip (chosenEndpoint x t i j) i, flip (chosenEndpoint x t i j) j, t) =
    (flip (chosenEndpoint y u k l) k, flip (chosenEndpoint y u k l) l, u) at he
  obtain ⟨hc, hdt⟩ := Prod.mk.inj he
  obtain ⟨hd, rfl⟩ := Prod.mk.inj hdt
  change ((x, t), (i, j)) ∈ mixedPairs C D at hp
  change ((y, t), (k, l)) ∈ mixedPairs C D at hq
  obtain ⟨hx, hij, hit, _, _⟩ := mixedPair_geometry h (x := x) (t := t) (i := i) (j := j) hp
  obtain ⟨hy, hkl, hkt, _, _⟩ := mixedPair_geometry h (x := y) (t := t) (i := k) (j := l) hq
  have hpair : ({i, j} : Finset (Fin 9)) = {k, l} := by
    rw [← distinct_flip_disagreements (chosenEndpoint x t i j) hij,
      ← distinct_flip_disagreements (chosenEndpoint y t k l) hkl, hc, hd]
  have horder : i < j ↔ k < l := by
    have hb := congrFun hc t
    rw [flip_at_other _ hit, flip_at_other _ hkt] at hb
    by_cases hi : i < j <;> by_cases hk : k < l <;>
      simp [chosenEndpoint, hi, hk, hx, hy] at hb ⊢
  have haxes : i = k ∧ j = l := by
    by_cases hi : i < j
    · exact ordered_axes_unique hi (horder.mp hi) hpair
    · have hji := lt_of_le_of_ne (le_of_not_gt hi) hij.symm
      have hlk := lt_of_le_of_ne (le_of_not_gt (mt horder.mpr hi)) hkl.symm
      obtain ⟨hj, hi⟩ := ordered_axes_unique hji hlk
        (by simpa only [Finset.pair_comm] using hpair)
      exact ⟨hi, hj⟩
  obtain ⟨rfl, rfl⟩ := haxes
  have hz := congrArg (fun z => flip z i) hc
  simp only [BalancedCriticalSpectrum.flip_flip] at hz
  have hxy : x = y := by
    by_cases hi : i < j
    · simpa [chosenEndpoint, hi] using hz
    · simpa [chosenEndpoint, hi] using congrArg (fun z => flip z t) hz
  subst y
  rfl

private theorem mixedPairToTriple_surj {C D : Finset (Q 9)} (h : Separated C D) :
    Set.SurjOn mixedPairToTriple (mixedPairs C D) (mixedTriples C D) := by
  rintro ⟨c, d, t⟩ hp
  obtain ⟨hc, hd, hdist, hc', hd'⟩ := mem_mixedTriples.mp hp
  obtain ⟨i, j, hij, rfl⟩ := ordered_two_flips hdist
  have hit : i ≠ t := by
    rintro rfl
    exact h.2 _ hc' _ hd (flip_adj _ _)
  have hjt : j ≠ t := by
    rintro rfl
    rw [flip_comm c i j] at hd
    exact h.2 _ hc' _ hd (flip_adj _ _)
  cases hb : c t
  · let x := flip c i
    have hx : x t = false := (flip_at_other c hit).trans hb
    refine ⟨((x, t), (i, j)), ?_, ?_⟩
    · change ((x, t), (i, j)) ∈ mixedPairs C D
      exact mixedPair_mem_of_neighbors h (x := x) hx hit hjt
        (by simpa [x] using hc) (by simpa [x] using hc') hd hd'
    · simp [mixedPairToTriple, chosenEndpoint, hij, x]
  · let z := flip c j
    let x := flip z t
    have hz : z t = true := (flip_at_other c hjt).trans hb
    have hx : x t = false := by simp [x, hz]
    have hci : flip z j = c := BalancedCriticalSpectrum.flip_flip c j
    have hdj : flip z i = flip (flip c i) j := flip_comm c j i
    refine ⟨((x, t), (j, i)), ?_, ?_⟩
    · change ((x, t), (j, i)) ∈ mixedPairs C D
      refine mixedPair_mem_of_neighbors h (x := x) hx hjt hit ?_ ?_ ?_ ?_
      · simpa [x, flip_comm z t j, hci] using hc'
      · simpa [x, flip_comm z t j, hci] using hc
      · simpa [x, flip_comm z t i, hdj] using hd'
      · simpa [x, flip_comm z t i, hdj] using hd
    · simp [mixedPairToTriple, chosenEndpoint, not_lt_of_gt hij, x, hci, hdj]

/-- The ambient mixed multiplicity is exactly the number of distance-two triples
    with a common internal direction. Edges without both witnesses contribute zero. -/
theorem sum_mixed_multiplicity {C D : Finset (Q 9)} (h : Separated C D) :
    (∑ e : Edge, multiplicity C e * multiplicity D e) = (mixedTriples C D).card := by
  rw [← card_mixedPairs]
  exact Finset.card_nbij mixedPairToTriple
    (mixedPairToTriple_mem h) (mixedPairToTriple_inj h) (mixedPairToTriple_surj h)

#print axioms multiplicity_union
#print axioms collisionCount_union
#print axioms sum_mixed_multiplicity

open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

private theorem separated_union_degree {C D : Finset (Q 9)} (h : Separated C D)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    {x : Q 9} (hx : x ∈ C) (hu : x ∈ C ∪ D) :
    ((hypercube 9).induce ((C ∪ D : Finset (Q 9)) : Set (Q 9))).degree ⟨x, hu⟩ = 3 := by
  rw [← selected_neighbor_card hu, ← hr.degree_eq ⟨x, hx⟩, ← selected_neighbor_card hx]
  congr 1
  ext y
  simp only [Finset.mem_inter, Finset.mem_union, SimpleGraph.mem_neighborFinset]
  exact ⟨fun ⟨ha, hm⟩ => ⟨ha, hm.resolve_right (fun hy => h.2 x hx y hy ha)⟩,
    fun ⟨ha, hm⟩ => ⟨ha, Or.inl hm⟩⟩

private theorem separated_union_regular {C D : Finset (Q 9)} (h : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3) :
    ((hypercube 9).induce ((C ∪ D : Finset (Q 9)) : Set (Q 9))).IsRegularOfDegree 3 := by
  intro ⟨x, hx⟩
  rcases Finset.mem_union.mp hx with hxC | hxD
  · exact separated_union_degree h hrC hxC hx
  · have hx' : x ∈ D ∪ C := Finset.mem_union_left _ hxD
    have hdeg := separated_union_degree h.symm hrD hxD hx'
    rw [← selected_neighbor_card hx', Finset.union_comm] at hdeg
    rwa [← selected_neighbor_card hx]

private theorem separated_union_balanced {C D : Finset (Q 9)} (h : Separated C D)
    (hbC : IsBalanced C) (hbD : IsBalanced D) : IsBalanced (C ∪ D) := by
  obtain ⟨sC, hC⟩ := hbC
  obtain ⟨sD, hD⟩ := hbD
  let s := fun x => if x ∈ C then sC x else sD x
  have other {x : Q 9} (hx : x ∈ D) : x ∉ C :=
    fun hxC => Finset.disjoint_left.mp h.1 hxC hx
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hxC | hxD
    · simpa [s, hxC] using hC.1 x hxC
    · simpa [s, other hxD] using hD.1 x hxD
  · intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hxC | hxD
    · have hyC := (Finset.mem_union.mp hy).resolve_right (fun hyD => h.2 x hxC y hyD hxy)
      simpa [s, hxC, hyC] using hC.2 x hxC y hyC hxy
    · have hyD := (Finset.mem_union.mp hy).resolve_left (fun hyC => h.2 y hyC x hxD hxy.symm)
      simpa [s, other hxD, other hyD] using hD.2 x hxD y hyD hxy

/-- Two separated balanced cubic components of a 258-vertex subcubic support must
    supply the indicated total of within-component and mixed boundary collisions. -/
theorem mixed_collision_bound {C D U : Finset (Q 9)} (h : Separated C D)
    (hCU : C ⊆ U) (hDU : D ⊆ U)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hCclosed : ∀ x ∈ C, ∀ y ∈ U \ C, ¬ (hypercube 9).Adj x y)
    (hDclosed : ∀ x ∈ D, ∀ y ∈ U \ D, ¬ (hypercube 9).Adj x y)
    (hU : ((hypercube 9).induce (U : Set (Q 9))).maxDegree ≤ 3)
    (hcard : U.card = 258) :
    6 * (C.card + D.card) - 369 ≤
      collisionCount C + collisionCount D + (mixedTriples C D).card := by
  have hclosed : ∀ x ∈ C ∪ D, ∀ y ∈ U \ (C ∪ D), ¬ (hypercube 9).Adj x y := by
    intro x hx y hy
    obtain ⟨hyU, hyout⟩ := Finset.mem_sdiff.mp hy
    rcases Finset.mem_union.mp hx with hxC | hxD
    · exact hCclosed x hxC y
        (Finset.mem_sdiff.mpr ⟨hyU, fun hc => hyout (Finset.mem_union_left _ hc)⟩)
    · exact hDclosed x hxD y
        (Finset.mem_sdiff.mpr ⟨hyU, fun hd => hyout (Finset.mem_union_right _ hd)⟩)
  have hbound := boundary_edge_bound (C ∪ D) U (Finset.union_subset hCU hDU)
    (separated_union_regular h hrC hrD) (separated_union_balanced h hbC hbD) hclosed hU
  rw [hcard, Finset.card_union_of_disjoint h.1, collisionCount_union h,
    sum_mixed_multiplicity h] at hbound
  omega

#print axioms mixed_collision_bound

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
