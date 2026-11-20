/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelCoverFibreBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelCoverFibreBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Projected fibre counts bound a balanced cubic support with distant parallel covers. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverSeparation
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary

/-! Delete the common cover direction and count occupied fibres by projected
parity. The transverse degree contributions cancel between the two parities. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParallelCoverFibreBound

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum
  (Q IsBalanced IsSwitching directionEndpoints directionEdges
    direction_edge_count)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9EightfoldCoverLocal (transverseSign card_transverse_signs eightfold_corner_rule)
open Q9EightfoldCoverSeparation (EightfoldCover)
open Q9ParityFoldedBoundary (dropCoordinate parity parityPart parityFold)
open private dropCoordinate_flip_drop dropCoordinate_flip_keep parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary
open private endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

local notation "flip" => BalancedCriticalSpectrum.flip

attribute [local instance] Classical.propDecidable

private abbrev liftVertex (a : Fin 9) (t : Bool) (z : Q 8) : Q 9 :=
  Fin.insertNth (α := fun _ => Bool) a t z

private theorem drop_insert (a : Fin 9) (t : Bool) (z : Q 8) :
    dropCoordinate a (liftVertex a t z) = z :=
  funext (Fin.insertNth_apply_succAbove (α := fun _ => Bool) a t z)

private theorem insert_drop (a : Fin 9) (x : Q 9) :
    liftVertex a (x a) (dropCoordinate a x) = x := by
  funext i
  by_cases hi : i = a
  · subst i
    simp [liftVertex]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    exact Fin.insertNth_apply_succAbove (α := fun _ => Bool) a (x a) _ j

private theorem flip_insert (a : Fin 9) (t : Bool) (z : Q 8) :
    flip (liftVertex a t z) a = liftVertex a (!t) z := by
  funext i
  by_cases hi : i = a
  · subst i
    simp [BalancedCriticalSpectrum.flip, liftVertex]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    simp [BalancedCriticalSpectrum.flip, liftVertex, Fin.succAbove_ne]

private theorem mem_lifts (S : Finset (Q 9)) (a : Fin 9) (x : Q 9) :
    (liftVertex a false (dropCoordinate a x) ∈ S ∧
      liftVertex a true (dropCoordinate a x) ∈ S) ↔ x ∈ S ∧ flip x a ∈ S := by
  have hx := insert_drop a x
  have hf := (flip_insert a (x a) (dropCoordinate a x)).symm
  rw [hx] at hf
  cases h : x a <;> simp only [h, Bool.not_false, Bool.not_true] at hx hf <;>
    simp only [hx, hf, and_comm]

private def projectedVertices (S : Finset (Q 9)) (a : Fin 9) (b : Bool) : Finset (Q 9) :=
  S.filter (fun x => parity (dropCoordinate a x) = b)

/-- Projected fibres of parity `b` with at least one selected endpoint. -/
def occupiedFibres (S : Finset (Q 9)) (a : Fin 9) (b : Bool) : Finset (Q 8) :=
  parityPart (S.image (dropCoordinate a)) b

/-- Projected fibres of parity `b` with both endpoints selected. -/
def doubleFibres (S : Finset (Q 9)) (a : Fin 9) (b : Bool) : Finset (Q 8) :=
  parityPart (univ.filter fun z => liftVertex a false z ∈ S ∧ liftVertex a true z ∈ S) b

private theorem card_layer (S : Finset (Q 9)) (a : Fin 9) (t : Bool)
    (p : Q 8 → Prop) [DecidablePred p] :
    (univ.filter fun z => liftVertex a t z ∈ S ∧ p z).card =
      (S.filter fun x => x a = t ∧ p (dropCoordinate a x)).card := by
  apply card_bij (fun z _ => liftVertex a t z)
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    exact mem_filter.mpr
      ⟨hz.1, Fin.insertNth_apply_same (α := fun _ => Bool) a t z,
        by simpa only [drop_insert] using hz.2⟩
  · intro z _ w _ h
    simpa only [drop_insert] using congrArg (dropCoordinate a) h
  · intro x hx
    obtain ⟨hx, ht, hp⟩ := mem_filter.mp hx
    have he : liftVertex a t (dropCoordinate a x) = x := by simpa only [ht] using insert_drop a x
    exact ⟨dropCoordinate a x, by simp [he, hx, hp], he⟩

private theorem card_projectedVertices (S : Finset (Q 9)) (a : Fin 9) (b : Bool) :
    (projectedVertices S a b).card =
      (occupiedFibres S a b).card + (doubleFibres S a b).card := by
  let layer (t : Bool) := univ.filter
    (fun z => liftVertex a t z ∈ S ∧ parity z = b)
  have hu : layer false ∪ layer true = occupiedFibres S a b := by
    ext z
    simp only [layer, occupiedFibres, parityPart, mem_union, mem_filter, mem_univ,
      true_and, mem_image]
    constructor
    · rintro (⟨h, hp⟩ | ⟨h, hp⟩)
      · exact ⟨⟨_, h, drop_insert a false z⟩, hp⟩
      · exact ⟨⟨_, h, drop_insert a true z⟩, hp⟩
    · rintro ⟨⟨x, hx, rfl⟩, hp⟩
      have he := insert_drop a x
      cases ht : x a
      · exact Or.inl ⟨by rw [ht] at he; exact he.symm ▸ hx, hp⟩
      · exact Or.inr ⟨by rw [ht] at he; exact he.symm ▸ hx, hp⟩
  have hi : layer false ∩ layer true = doubleFibres S a b := by
    ext z
    simp only [layer, doubleFibres, parityPart, mem_inter, mem_filter, mem_univ, true_and]
    tauto
  have hc (t : Bool) : (layer t).card =
      ((projectedVertices S a b).filter fun x => x a = t).card := by
    dsimp only [layer]
    rw [card_layer S a t (fun z => parity z = b)]
    congr 1
    ext x
    simp only [projectedVertices, mem_filter]
    tauto
  have hnot : ((projectedVertices S a b).filter fun x => ¬ x a = false) =
      (projectedVertices S a b).filter (fun x => x a = true) := by
    ext x
    cases h : x a <;> simp [h]
  rw [← hu, ← hi, card_union_add_card_inter, hc, hc, ← hnot]
  exact (card_filter_add_card_filter_not _).symm

private theorem card_both_layers (S : Finset (Q 9)) (a : Fin 9) :
    (univ.filter fun z => liftVertex a false z ∈ S ∧ liftVertex a true z ∈ S).card =
      directionEdges S a := by
  rw [card_layer S a false (fun z => liftVertex a true z ∈ S)]
  unfold directionEdges
  congr 1
  ext x
  simp only [mem_filter]
  have he := flip_insert a (x a) (dropCoordinate a x)
  rw [insert_drop] at he
  by_cases ht : x a = false
  · simp [ht, show flip x a = liftVertex a true (dropCoordinate a x) by simpa [ht] using he]
  · simp [ht]

private theorem card_doubleFibres (S : Finset (Q 9)) (a : Fin 9) (b : Bool) :
    (doubleFibres S a b).card = directionEdges (projectedVertices S a b) a := by
  let V := projectedVertices S a b
  have hl : doubleFibres S a b = univ.filter
      (fun z => liftVertex a false z ∈ V ∧ liftVertex a true z ∈ V) := by
    ext z
    simp only [doubleFibres, parityPart, V, projectedVertices, mem_filter, mem_univ,
      true_and, drop_insert]
    tauto
  rw [hl, card_both_layers]

private theorem card_parity_partition {n : ℕ} (A : Finset (Q n)) (p : Q n → Bool) (b : Bool) :
    (A.filter fun x => p x = b).card + (A.filter fun x => p x = !b).card = A.card := by
  have h : (A.filter fun x => p x = !b) = A.filter (fun x => ¬ p x = b) := by
    ext x
    cases b <;> cases hpx : p x <;> simp [hpx]
  rw [h, card_filter_add_card_filter_not]

private theorem doubleFibres_partition (S : Finset (Q 9)) (a : Fin 9) (b : Bool) :
    (doubleFibres S a b).card + (doubleFibres S a (!b)).card = directionEdges S a := by
  unfold doubleFibres parityPart
  rw [card_parity_partition, card_both_layers]

private theorem direction_degree_sum {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (V : Finset (Q 9)) (hV : V ⊆ S) :
    (∑ i : Fin 9, (V.filter fun x => flip x i ∈ S).card) = 3 * V.card := by
  calc
    _ = ∑ i : Fin 9, ∑ x ∈ V, if flip x i ∈ S then 1 else 0 := by
      simp
    _ = ∑ x ∈ V, (directions S x).card := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      simp [directions]
    _ = 3 * V.card := by
      rw [sum_congr rfl (fun x hx => regular_directions S hr (hV hx))]
      simp [Nat.mul_comm]

private theorem transverse_count (S : Finset (Q 9)) (a : Fin 9) (b : Bool)
    (j : Fin 9) (hj : j ≠ a) :
    ((projectedVertices S a b).filter fun x => flip x j ∈ S).card =
      ((projectedVertices S a (!b)).filter fun x => flip x j ∈ S).card := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  let f := fun x : Q 9 => flip x (a.succAbove k)
  have hp (x : Q 9) : parity (dropCoordinate a (f x)) = !parity (dropCoordinate a x) := by
    simp only [f, dropCoordinate_flip_keep, parity_flip]
  have hf (x : Q 9) : f (f x) = x := BalancedCriticalSpectrum.flip_flip _ _
  apply card_bij' (fun x _ => f x) (fun x _ => f x)
  · intro x hx
    simp only [projectedVertices, mem_filter] at hx ⊢
    exact ⟨⟨hx.2, (hp x).trans (congrArg Bool.not hx.1.2)⟩,
      by simpa only [f, BalancedCriticalSpectrum.flip_flip] using hx.1.1⟩
  · intro x hx
    simp only [projectedVertices, mem_filter] at hx ⊢
    exact ⟨⟨hx.2, by rw [hp, hx.1.2, Bool.not_not]⟩,
      by simpa only [f, BalancedCriticalSpectrum.flip_flip] using hx.1.1⟩
  · intro x _
    exact hf x
  · intro x _
    exact hf x

private theorem axial_count (S : Finset (Q 9)) (a : Fin 9) (b : Bool) :
    ((projectedVertices S a b).filter fun x => flip x a ∈ S).card =
      2 * (doubleFibres S a b).card := by
  rw [card_doubleFibres, ← endpoint_card_twice]
  congr 1
  ext x
  simp only [directionEndpoints, projectedVertices, mem_filter, dropCoordinate_flip_drop]
  tauto

/-- In a balanced induced cubic support, the occupied count of projected
parity `b` is determined by the total axial edge count and the number of
double fibres of the opposite parity. -/
theorem occupied_fibre_identity {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (a : Fin 9) (b : Bool) :
    3 * (occupiedFibres S a b).card =
      7 * directionEdges S a + (doubleFibres S a (!b)).card := by
  have hdeg (p : Bool) :=
    direction_degree_sum hr (projectedVertices S a p) (filter_subset _ _)
  have hsplit (p : Bool) :=
    sum_erase_add (univ : Finset (Fin 9))
      (fun i => ((projectedVertices S a p).filter fun x => flip x i ∈ S).card)
      (mem_univ a)
  have htrans :
      (∑ i ∈ univ.erase a, ((projectedVertices S a b).filter fun x => flip x i ∈ S).card) =
      (∑ i ∈ univ.erase a, ((projectedVertices S a (!b)).filter fun x => flip x i ∈ S).card) :=
    sum_congr rfl fun i hi => transverse_count S a b i (mem_erase.mp hi).1
  have hax (p : Bool) := axial_count S a p
  have hv (p : Bool) := card_projectedVertices S a p
  have hpart := card_parity_partition S (fun x => parity (dropCoordinate a x)) b
  change (projectedVertices S a b).card + (projectedVertices S a (!b)).card = S.card at hpart
  have hm := doubleFibres_partition S a b
  have hsize : 6 * directionEdges S a = S.card := direction_edge_count (d := 3) S hr hb a
  have h₀ := hsplit b
  have h₁ := hsplit (!b)
  rw [hdeg b, hax b, htrans] at h₀
  rw [hdeg (!b), hax (!b)] at h₁
  have hv₀ := hv b
  omega

#print axioms occupied_fibre_identity

private theorem drop_eq_or_flip {a : Fin 9} {x y : Q 9}
    (h : dropCoordinate a y = dropCoordinate a x) : y = x ∨ y = flip x a := by
  have hx := insert_drop a x
  have hy := insert_drop a y
  rw [h] at hy
  have hf := flip_insert a (x a) (dropCoordinate a x)
  rw [hx] at hf
  cases hxa : x a <;> cases hya : y a <;> simp_all

private theorem empty_projected {S : Finset (Q 9)} {a : Fin 9} {x : Q 9}
    (hx : x ∉ S) (hf : flip x a ∉ S) (b : Bool) :
    dropCoordinate a x ∉ occupiedFibres S a b := by
  intro hm
  obtain ⟨y, hy, he⟩ := mem_image.mp (mem_filter.mp hm).1
  rcases drop_eq_or_flip he with rfl | rfl
  · exact hx hy
  · exact hf hy

private def toggle (z : Q 8) (I : Finset (Fin 8)) : Q 8 :=
  fun i => if i ∈ I then !z i else z i

private theorem diff_toggle (z : Q 8) (I : Finset (Fin 8)) :
    diff (toggle z I) z = I := by
  ext i
  by_cases hi : i ∈ I <;> simp [diff, toggle, hi]

private theorem toggle_diff (z w : Q 8) : toggle z (diff w z) = w := by
  funext i
  cases hz : z i <;> cases hw : w i <;> simp [diff, toggle, hz, hw]

private theorem diff_single_flip (z : Q 8) (i : Fin 8) : diff (flip z i) z = {i} := by
  rw [diff_flip]
  simp [diff]

private theorem diff_double_flip (z : Q 8) {i j : Fin 8} (hij : i ≠ j) :
    diff (flip (flip z i) j) z = {i, j} := by
  rw [diff_flip, diff_single_flip]
  simp [hij.symm, Finset.pair_comm]

private def signAxes (sigma : Q 9 → ℝ) (x : Q 9) (a : Fin 9) (s : ℝ) :
    Finset (Fin 8) :=
  univ.filter fun i => transverseSign sigma x (a.succAbove i) = s

private theorem card_signAxes (sigma : Q 9 → ℝ) (x : Q 9) (a : Fin 9) (s : ℝ) :
    (signAxes sigma x a s).card =
      ((univ.erase a).filter fun i => transverseSign sigma x i = s).card := by
  apply card_bij (fun i _ => a.succAbove i)
  · intro i hi
    have hs := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨Fin.succAbove_ne a i, mem_univ _⟩, hs⟩
  · intro i _ j _ h
    exact Fin.succAbove_right_injective h
  · intro j hj
    obtain ⟨ha, hs⟩ := mem_filter.mp hj
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (mem_erase.mp ha).1
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hs⟩, rfl⟩

private theorem empty_corner {S : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching S sigma) {a : Fin 9} {x : Q 9} (hx : EightfoldCover S x a)
    (b : Bool) {i j : Fin 8}
    (he : transverseSign sigma x (a.succAbove i) = transverseSign sigma x (a.succAbove j)) :
    flip (flip (dropCoordinate a x) i) j ∉ occupiedFibres S a b := by
  obtain ⟨hp, hq⟩ := (eightfold_corner_rule hr hs hx.1 hx.2.1 hx.2.2
    (Fin.succAbove_ne a i) (Fin.succAbove_ne a j)).1.mp he
  simpa only [dropCoordinate_flip_keep] using empty_projected hp hq b

private theorem cover_fibres {S : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching S sigma) {a : Fin 9} {x : Q 9} (hx : EightfoldCover S x a) :
    let z := dropCoordinate a x
    let b := parity z
    ∃ E D : Finset (Q 8),
      E.card = 13 ∧ D.card = 8 ∧
      (∀ w ∈ E, parity w = b ∧ w ∉ occupiedFibres S a b ∧ hammingDist w z ≤ 2) ∧
      (∀ w ∈ D, w ∈ doubleFibres S a (!b) ∧ hammingDist w z ≤ 1) := by
  let z := dropCoordinate a x
  let b := parity z
  let A := signAxes sigma x a 1
  let B := signAxes sigma x a (-1)
  let pairs := A.powersetCard 2 ∪ B.powersetCard 2
  let E := insert z (pairs.image (toggle z))
  let D := (univ : Finset (Fin 8)).image (flip z)
  have hsign := card_transverse_signs hr hs hx.1 hx.2.1 (fun i hi => (hx.2.2 i hi).1)
  have hA : A.card = 4 := (card_signAxes _ _ _ _).trans hsign.1
  have hB : B.card = 4 := (card_signAxes _ _ _ _).trans hsign.2
  have hpair_card {I : Finset (Fin 8)} (hI : I ∈ pairs) : I.card = 2 :=
    (mem_union.mp hI).elim (fun h => (mem_powersetCard.mp h).2)
      (fun h => (mem_powersetCard.mp h).2)
  have hpair_disjoint : Disjoint (A.powersetCard 2) (B.powersetCard 2) := by
    apply disjoint_left.mpr
    intro I hI hJ
    obtain ⟨i, hi⟩ := card_pos.mp (by rw [(mem_powersetCard.mp hI).2]; exact Nat.zero_lt_succ 1)
    have hp := (mem_filter.mp ((mem_powersetCard.mp hI).1 hi)).2
    have hn := (mem_filter.mp ((mem_powersetCard.mp hJ).1 hi)).2
    change transverseSign sigma x (a.succAbove i) = 1 at hp
    change transverseSign sigma x (a.succAbove i) = -1 at hn
    linarith
  have hpairs : pairs.card = 12 := by
    rw [show pairs = _ from rfl, card_union_of_disjoint hpair_disjoint,
      card_powersetCard, card_powersetCard, hA, hB]
    decide
  have hz : z ∉ pairs.image (toggle z) := by
    rintro hz
    obtain ⟨I, hI, he⟩ := mem_image.mp hz
    have hd := congrArg (fun w => diff w z) he
    rw [diff_toggle] at hd
    have hc := hpair_card hI
    rw [hd] at hc
    simp [diff] at hc
  refine ⟨E, D, ?_, ?_, ?_, ?_⟩
  · rw [show E = _ from rfl, card_insert_of_notMem hz, card_image_of_injective _ ?_, hpairs]
    intro I J h
    simpa only [diff_toggle] using congrArg (fun w => diff w z) h
  · rw [show D = _ from rfl, card_image_of_injective, card_univ, Fintype.card_fin]
    intro i j he
    have hd : ({i} : Finset (Fin 8)) = {j} := by
      simpa only [diff_single_flip] using congrArg (fun w => diff w z) he
    exact singleton_inj.mp hd
  · intro w hw
    rcases mem_insert.mp hw with he | hw
    · subst w
      refine ⟨rfl, empty_projected hx.1 hx.2.1 b, ?_⟩
      change hammingDist z z ≤ 2
      rw [hammingDist_self]
      exact Nat.zero_le _
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hw
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp (hpair_card hI)
    have hsigns : ∃ s : ℝ, i ∈ signAxes sigma x a s ∧ j ∈ signAxes sigma x a s := by
      rcases mem_union.mp hI with hp | hn
      · exact ⟨1, (mem_powersetCard.mp hp).1 (by simp), (mem_powersetCard.mp hp).1 (by simp)⟩
      · exact ⟨-1, (mem_powersetCard.mp hn).1 (by simp), (mem_powersetCard.mp hn).1 (by simp)⟩
    obtain ⟨s, hi, hj⟩ := hsigns
    have he := ((mem_filter.mp hi).2).trans ((mem_filter.mp hj).2).symm
    have hcorner : toggle z {i, j} = flip (flip z i) j := by
      rw [← diff_double_flip z hij, toggle_diff]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcorner, parity_flip, parity_flip, Bool.not_not]
    · rw [hcorner]
      exact empty_corner hr hs hx b he
    · change (diff (toggle z {i, j}) z).card ≤ 2
      simp [diff_toggle, hij]
  · intro w hw
    obtain ⟨i, _, rfl⟩ := mem_image.mp hw
    have hf := hx.2.2 (a.succAbove i) (Fin.succAbove_ne a i)
    rw [← flip_comm x (a.succAbove i) a] at hf
    have hm := (mem_lifts S a (flip x (a.succAbove i))).mpr hf
    rw [dropCoordinate_flip_keep] at hm
    refine ⟨?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hm⟩, parity_flip z i⟩
    · exact le_of_eq (by change (diff (flip z i) z).card = 1; simp [diff_single_flip])

private theorem card_parity_eight (b : Bool) : (parityPart (univ : Finset (Q 8)) b).card = 128 := by
  let U := parityPart (univ : Finset (Q 8)) b
  let e : ↥U ≃ {z : Q 8 // parity z = b} :=
    Equiv.subtypeEquivRight (fun z => by simp [U, parityPart])
  calc
    U.card = Fintype.card ↥U := (Fintype.card_coe U).symm
    _ = Fintype.card (Q 7) := Fintype.card_congr (e.trans (parityFold (0 : Fin 8) b))
    _ = 128 := by
      change Fintype.card (Fin 7 → Bool) = 128
      simp

private theorem disjoint_of_distances {z w : Q 8} {U V : Finset (Q 8)} {r s : ℕ}
    (hd : r + s < hammingDist z w)
    (hU : ∀ u ∈ U, hammingDist u z ≤ r) (hV : ∀ u ∈ V, hammingDist u w ≤ s) :
    Disjoint U V := by
  apply disjoint_left.mpr
  intro u hu hv
  have ht := hammingDist_triangle z u w
  rw [hammingDist_comm z u] at ht
  exact (not_lt_of_ge (ht.trans (Nat.add_le_add (hU u hu) (hV u hv)))) hd

/-- Two parallel eightfold exterior cover edges with projected centers of the
same parity at Hamming distance at least six force at most 246 selected vertices. -/
theorem card_le_246_of_parallel_eightfold_covers {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) {a : Fin 9} {x y : Q 9}
    (hx : EightfoldCover S x a) (hy : EightfoldCover S y a)
    (hp : parity (dropCoordinate a x) = parity (dropCoordinate a y))
    (hd : 6 ≤ hammingDist (dropCoordinate a x) (dropCoordinate a y)) :
    S.card ≤ 246 := by
  obtain ⟨sigma, hs⟩ := hb
  let b := parity (dropCoordinate a x)
  have hcx := cover_fibres hr hs hx
  have hcy := cover_fibres hr hs hy
  dsimp only at hcx hcy
  rw [← hp] at hcy
  obtain ⟨Ex, Dx, hEx, hDx, hxE, hxD⟩ := hcx
  obtain ⟨Ey, Dy, hEy, hDy, hyE, hyD⟩ := hcy
  have hE : Disjoint Ex Ey :=
    disjoint_of_distances (by omega) (fun u hu => (hxE u hu).2.2) (fun u hu => (hyE u hu).2.2)
  have hD : Disjoint Dx Dy :=
    disjoint_of_distances (by omega) (fun u hu => (hxD u hu).2) (fun u hu => (hyD u hu).2)
  have hEcard : (Ex ∪ Ey).card = 26 := by rw [card_union_of_disjoint hE, hEx, hEy]
  have hDcard : (Dx ∪ Dy).card = 16 := by rw [card_union_of_disjoint hD, hDx, hDy]
  have hdouble : 16 ≤ (doubleFibres S a (!b)).card := by
    rw [← hDcard]
    exact card_le_card (union_subset (fun u hu => (hxD u hu).1) (fun u hu => (hyD u hu).1))
  have hEO : Disjoint (Ex ∪ Ey) (occupiedFibres S a b) := by
    apply disjoint_left.mpr
    intro u hu ho
    exact (mem_union.mp hu).elim (fun hx => (hxE u hx).2.1 ho) (fun hy => (hyE u hy).2.1 ho)
  have hsubset : (Ex ∪ Ey) ∪ occupiedFibres S a b ⊆ parityPart univ b := by
    intro u hu
    have h : parity u = b := (mem_union.mp hu).elim
      (fun he => (mem_union.mp he).elim (fun hx => (hxE u hx).1) (fun hy => (hyE u hy).1))
      (fun ho => (mem_filter.mp ho).2)
    exact mem_filter.mpr ⟨mem_univ _, h⟩
  have hoccupied := card_le_card hsubset
  rw [card_union_of_disjoint hEO, hEcard, card_parity_eight] at hoccupied
  have hid := occupied_fibre_identity hr ⟨sigma, hs⟩ a b
  have hsize : 6 * directionEdges S a = S.card :=
    direction_edge_count (d := 3) S hr ⟨sigma, hs⟩ a
  omega

#print axioms card_le_246_of_parallel_eightfold_covers

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParallelCoverFibreBound
