/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverLocal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverLocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The exact signed rule for the two layers of corners at an eightfold exterior edge. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-! The signed corner rule at a Q9 exterior edge covered in all eight transverse axes. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q gamma gamma_apply flip_adj
  IsSwitching switchingVector ambient_eigenvector)
open BalancedCubeGirth (gamma_anticommute no_selected_square)
open BalancedCubeComponentBoundary (directions regular_directions)
open SupportedEigenSaturation (matrix_sq_of_adj)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private switching_sq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private flip_comm from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private matrix_row from D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private flip_at_other two_flip_disagreements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions

local notation "flip" => BalancedCriticalSpectrum.flip

/-- The contribution of the selected neighbor in direction i to the exterior Huang row. -/
def transverseSign (sigma : Q 9 → ℝ) (v : Q 9) (i : Fin 9) : ℝ :=
  huangMatrix 9 v (flip v i) * sigma (flip v i)

variable {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
variable {v : Q 9} {k : Fin 9}

private theorem transverseSign_unit (hs : IsSwitching C sigma) {i : Fin 9}
    (hi : flip v i ∈ C) :
    transverseSign sigma v i = 1 ∨ transverseSign sigma v i = -1 := by
  apply sq_eq_one_iff.mp
  rw [transverseSign, mul_pow, matrix_sq_of_adj (flip_adj v i), switching_sq hs hi, mul_one]

private theorem gamma_selected (hs : IsSwitching C sigma) {x : Q 9} {i : Fin 9}
    (hx : x ∈ C) (hxi : flip x i ∈ C) : gamma i sigma x = sigma x := by
  rw [gamma_apply, hs.2 x hx (flip x i) hxi (flip_adj x i), mul_assoc, ← pow_two,
    switching_sq hs hxi, mul_one]

private theorem sign_neg_of_corner (hs : IsSwitching C sigma) {i j : Fin 9}
    (hij : i ≠ j) (hi : flip v i ∈ C) (hj : flip v j ∈ C)
    (hc : flip (flip v i) j ∈ C) :
    transverseSign sigma v i = -transverseSign sigma v j := by
  have hc' : flip (flip v j) i ∈ C := by simpa only [flip_comm v j i] using hc
  have h := congrFun (gamma_anticommute hij sigma) v
  rw [Pi.neg_apply, gamma_apply i (gamma j sigma), gamma_apply j (gamma i sigma),
    gamma_selected hs hi hc, gamma_selected hs hj hc'] at h
  exact h

private theorem sign_transport (hs : IsSwitching C sigma) {i : Fin 9}
    (hik : i ≠ k) (hi : flip v i ∈ C) (hi' : flip (flip v k) i ∈ C) :
    transverseSign sigma v i =
      -(huangMatrix 9 v (flip v k) * transverseSign sigma (flip v k) i) := by
  have hmate : flip (flip v i) k ∈ C := by simpa only [flip_comm v i k] using hi'
  have h := congrFun (gamma_anticommute hik sigma) v
  rw [Pi.neg_apply, gamma_apply i (gamma k sigma), gamma_selected hs hi hmate,
    gamma_apply k (gamma i sigma), gamma_apply i sigma] at h
  exact h

open Classical in
/-- An exterior endpoint with all eight transverse neighbors selected has four of each sign. -/
theorem card_transverse_signs
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hv : v ∉ C) (hvk : flip v k ∉ C)
    (hcover : ∀ i ≠ k, flip v i ∈ C) :
    ((Finset.univ.erase k).filter fun i => transverseSign sigma v i = 1).card = 4 ∧
    ((Finset.univ.erase k).filter fun i => transverseSign sigma v i = -1).card = 4 := by
  let axes := Finset.univ.erase k
  let a := transverseSign sigma v
  have haxes : axes.card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hunit (i : Fin 9) (hi : i ∈ axes) : a i = 1 ∨ a i = -1 :=
    transverseSign_unit hs (hcover i (Finset.mem_erase.mp hi).1)
  let z := switchingVector C sigma
  have hrow : ∑ i, huangMatrix 9 v (flip v i) * z (flip v i) = 0 := by
    rw [← matrix_row, ambient_eigenvector (d := 3) C sigma hr hs]
    simp [switchingVector, hv]
  have hsum : ∑ i ∈ axes, a i = 0 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun i => huangMatrix 9 v (flip v i) * z (flip v i)) (Finset.mem_univ k)
    rw [hrow] at h
    simp only [z, switchingVector, ite_eq_right hvk, mul_zero, add_zero] at h
    calc
      ∑ i ∈ axes, a i =
          ∑ i ∈ axes, huangMatrix 9 v (flip v i) * z (flip v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [a, transverseSign, z, switchingVector, hcover i (Finset.mem_erase.mp hi).1]
      _ = 0 := h
  let positive := axes.filter fun i => a i = 1
  let negative := axes.filter fun i => a i = -1
  have hin : ∀ i ∈ axes, a i = (if a i = 1 then (2 : ℝ) else 0) - 1 := by
    intro i hi
    rcases hunit i hi with h | h <;> norm_num [h]
  have hcount : ∑ i ∈ axes, a i = 2 * (positive.card : ℝ) - (axes.card : ℝ) := by
    rw [Finset.sum_congr rfl hin]
    simp [Finset.sum_sub_distrib, Finset.sum_ite, positive, mul_comm]
  rw [hsum, haxes] at hcount
  norm_num at hcount
  have hpositive : positive.card = 4 := by
    exact_mod_cast (show (positive.card : ℝ) = 4 by linarith only [hcount])
  have hnegative : negative = axes.filter fun i => a i ≠ 1 := by
    ext i
    simp only [negative, Finset.mem_filter]
    constructor
    · rintro ⟨hi, h⟩
      exact ⟨hi, by norm_num [h]⟩
    · rintro ⟨hi, h⟩
      exact ⟨hi, (hunit i hi).resolve_left h⟩
  have hpartition := Finset.card_filter_add_card_filter_not (s := axes) (fun i => a i = 1)
  change positive.card + (axes.filter fun i => a i ≠ 1).card = axes.card at hpartition
  rw [← hnegative, haxes, hpositive] at hpartition
  refine ⟨hpositive, ?_⟩
  change negative.card = 4
  omega

set_option maxHeartbeats 500000 in
-- Constructing and comparing the two filtered sets of directions exceeds the default limit.
open Classical in
/-- For two transverse axes at an eightfold exterior edge, equal Huang signs
give no selected corner and opposite signs give exactly one selected corner. -/
theorem eightfold_corner_rule
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hv : v ∉ C) (hvk : flip v k ∉ C)
    (hcover : ∀ i ≠ k, flip v i ∈ C ∧ flip (flip v k) i ∈ C)
    {i j : Fin 9} (hik : i ≠ k) (hjk : j ≠ k) :
    let p := flip (flip v i) j
    let q := flip p k
    (transverseSign sigma v i = transverseSign sigma v j ↔ p ∉ C ∧ q ∉ C) ∧
    (transverseSign sigma v i = -transverseSign sigma v j ↔
      (p ∈ C ∧ q ∉ C) ∨ (p ∉ C ∧ q ∈ C)) := by
  classical
  let a := transverseSign sigma v
  let b := transverseSign sigma (flip v k)
  let lower := (directions C (flip v i)).erase k
  let upper := (directions C (flip (flip v k) i)).erase k
  let opposite := (Finset.univ.erase k).filter fun t => a t = -a i
  have hi := hcover i hik
  have hmate (t : Fin 9) :
      flip (flip (flip v k) i) t = flip (flip (flip v i) t) k := by
    rw [flip_comm v k i, flip_comm (flip v i) k t]
  have hdisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨htk, hl⟩ := Finset.mem_erase.mp ht
    have hp := (mem_directions _ _ _).mp hl
    have hq := (mem_directions _ _ _).mp (Finset.mem_erase.mp ht').2
    have hi' : flip (flip v i) k ∈ C := by simpa only [flip_comm v i k] using hi.2
    apply no_selected_square ⟨sigma, hs⟩ htk.symm hi.1 hi' hp
    rwa [← flip_comm v k i]
  have hcardLower : lower.card = 2 := by
    have hk : k ∈ directions C (flip v i) := by
      rw [mem_directions, flip_comm v i k]
      exact hi.2
    rw [Finset.card_erase_of_mem hk, regular_directions C hr hi.1]
  have hcardUpper : upper.card = 2 := by
    have hk : k ∈ directions C (flip (flip v k) i) := by
      rw [mem_directions, flip_comm (flip v k) i k, BalancedCriticalSpectrum.flip_flip]
      exact hi.1
    rw [Finset.card_erase_of_mem hk, regular_directions C hr hi.2]
  have hsubset : lower ∪ upper ⊆ opposite := by
    intro t ht
    obtain hl | hu := Finset.mem_union.mp ht
    · obtain ⟨htk, hl⟩ := Finset.mem_erase.mp hl
      have hp := (mem_directions _ _ _).mp hl
      have hti : t ≠ i := by
        rintro rfl
        exact hv (by simpa only [BalancedCriticalSpectrum.flip_flip] using hp)
      have hneg : a i = -a t := sign_neg_of_corner hs hti.symm hi.1 (hcover t htk).1 hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨htk, Finset.mem_univ _⟩,
        by rw [hneg, neg_neg]⟩
    · obtain ⟨htk, hu⟩ := Finset.mem_erase.mp hu
      have hq := (mem_directions _ _ _).mp hu
      have hti : t ≠ i := by
        rintro rfl
        exact hvk (by simpa only [BalancedCriticalSpectrum.flip_flip] using hq)
      have hneg : b i = -b t := sign_neg_of_corner hs hti.symm hi.2 (hcover t htk).2 hq
      have hiSign := sign_transport hs hik hi.1 hi.2
      have htSign := sign_transport hs htk (hcover t htk).1 (hcover t htk).2
      have hop : a t = -a i := by
        change transverseSign sigma v t = -transverseSign sigma v i
        rw [hiSign, htSign]
        change -(huangMatrix 9 v (flip v k) * b t) =
          -(-(huangMatrix 9 v (flip v k) * b i))
        rw [hneg, mul_neg, neg_neg]
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨htk, Finset.mem_univ _⟩, hop⟩
  have hcounts := card_transverse_signs hr hs hv hvk (fun t ht => (hcover t ht).1)
  have hopCard : opposite.card = 4 := by
    rcases transverseSign_unit hs hi.1 with h | h
    · simpa only [opposite, a, h] using hcounts.2
    · simpa only [opposite, a, h, neg_neg] using hcounts.1
  have hfull : lower ∪ upper = opposite := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [Finset.card_union_of_disjoint hdisjoint, hcardLower, hcardUpper, hopCard]
  have hl : j ∈ lower ↔ flip (flip v i) j ∈ C := by
    constructor
    · intro h
      exact (mem_directions _ _ _).mp (Finset.mem_erase.mp h).2
    · intro h
      exact Finset.mem_erase.mpr ⟨hjk, (mem_directions _ _ _).mpr h⟩
  have hu : j ∈ upper ↔ flip (flip (flip v i) j) k ∈ C := by
    rw [← hmate j]
    constructor
    · intro h
      exact (mem_directions _ _ _).mp (Finset.mem_erase.mp h).2
    · intro h
      exact Finset.mem_erase.mpr ⟨hjk, (mem_directions _ _ _).mpr h⟩
  have hneg : a i = -a j ↔ j ∈ lower ∨ j ∈ upper := by
    rw [← Finset.mem_union, hfull, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩, by rw [h, neg_neg]⟩
    · rintro ⟨_, h⟩
      change a j = -a i at h
      rw [h, neg_neg]
  have hsign : a i = a j ↔ ¬ a i = -a j := by
    have hiUnit : a i = 1 ∨ a i = -1 := transverseSign_unit hs hi.1
    have hjUnit : a j = 1 ∨ a j = -1 := transverseSign_unit hs (hcover j hjk).1
    rcases hiUnit with h | h <;> rcases hjUnit with h' | h' <;> norm_num [h, h']
  have hnotBoth : ¬ (j ∈ lower ∧ j ∈ upper) :=
    fun h => Finset.disjoint_left.mp hdisjoint h.1 h.2
  change (a i = a j ↔ flip (flip v i) j ∉ C ∧ flip (flip (flip v i) j) k ∉ C) ∧
    (a i = -a j ↔ (flip (flip v i) j ∈ C ∧ flip (flip (flip v i) j) k ∉ C) ∨
      (flip (flip v i) j ∉ C ∧ flip (flip (flip v i) j) k ∈ C))
  refine ⟨by rw [hsign, hneg, not_or, hl, hu], ?_⟩
  rw [hneg, ← hl, ← hu]
  exact ⟨fun h => h.elim
    (fun hp => Or.inl ⟨hp, fun hq => hnotBoth ⟨hp, hq⟩⟩)
    (fun hq => Or.inr ⟨fun hp => hnotBoth ⟨hp, hq⟩, hq⟩),
    fun h => h.elim (fun hp => Or.inl hp.1) (fun hq => Or.inr hq.2)⟩

open Classical in
/-- The selected corners reached by two transverse flips from either exterior endpoint. -/
def selectedCorners (C : Finset (Q 9)) (v : Q 9) (k : Fin 9) : Finset (Q 9) :=
  C.filter fun p => ∃ i j : Fin 9, i ≠ k ∧ j ≠ k ∧ i ≠ j ∧
    (p = flip (flip v i) j ∨ p = flip (flip (flip v i) j) k)

open Classical in
private theorem corner_disagreements {i j : Fin 9} (hik : i ≠ k) (hjk : j ≠ k) (hij : i ≠ j)
    {p : Q 9} (hp : p = flip (flip v i) j ∨ p = flip (flip (flip v i) j) k) :
    ((Finset.univ.erase k).filter fun t => v t ≠ p t) = {i, j} := by
  rw [← two_flip_disagreements v hij]
  ext t
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
  constructor
  · rintro ⟨ht, h⟩
    rcases hp with rfl | rfl
    · exact h
    · simpa only [flip_at_other _ ht.symm] using h
  · intro h
    have ht : t ≠ k := by
      rintro rfl
      exact h (by rw [flip_at_other _ hjk, flip_at_other _ hik])
    refine ⟨ht, ?_⟩
    rcases hp with rfl | rfl
    · exact h
    · simpa only [flip_at_other _ ht.symm] using h

set_option maxHeartbeats 500000 in
-- Elaborating the finite bijection requires reducing several local finset definitions.
open Classical in
/-- Each positive-negative pair of transverse axes gives a different selected corner. -/
theorem card_selected_corners
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hv : v ∉ C) (hvk : flip v k ∉ C)
    (hcover : ∀ i ≠ k, flip v i ∈ C ∧ flip (flip v k) i ∈ C) :
    (selectedCorners C v k).card = 16 := by
  let a := transverseSign sigma v
  let positive := (Finset.univ.erase k).filter fun i => a i = 1
  let negative := (Finset.univ.erase k).filter fun i => a i = -1
  let pairs := positive.product negative
  let corner (i j : Fin 9) := flip (flip v i) j
  let chooseCorner (ij : Fin 9 × Fin 9) :=
    if corner ij.1 ij.2 ∈ C then corner ij.1 ij.2 else flip (corner ij.1 ij.2) k
  have hcounts := card_transverse_signs hr hs hv hvk (fun t ht => (hcover t ht).1)
  have hcard : pairs.card = 16 := by
    change (positive ×ˢ negative).card = 16
    rw [Finset.card_product, show positive.card = 4 from hcounts.1,
      show negative.card = 4 from hcounts.2]
  have pair_spec {ij : Fin 9 × Fin 9} (h : ij ∈ pairs) :
      ij.1 ≠ k ∧ ij.2 ≠ k ∧ a ij.1 = 1 ∧ a ij.2 = -1 ∧ ij.1 ≠ ij.2 := by
    obtain ⟨hp, hn⟩ := Finset.mem_product.mp h
    obtain ⟨hi, hpos⟩ := Finset.mem_filter.mp hp
    obtain ⟨hj, hneg⟩ := Finset.mem_filter.mp hn
    refine ⟨(Finset.mem_erase.mp hi).1, (Finset.mem_erase.mp hj).1, hpos, hneg, ?_⟩
    intro he
    change a ij.1 = 1 at hpos
    change a ij.2 = -1 at hneg
    rw [he, hneg] at hpos
    norm_num at hpos
  have choice_spec (ij : Fin 9 × Fin 9) :
      chooseCorner ij = corner ij.1 ij.2 ∨
        chooseCorner ij = flip (corner ij.1 ij.2) k := by
    by_cases h : corner ij.1 ij.2 ∈ C <;> simp [chooseCorner, h]
  have choice_eq {i j : Fin 9} (hik : i ≠ k) (hjk : j ≠ k)
      (hi : a i = 1) (hj : a j = -1) {p : Q 9} (hpC : p ∈ C)
      (hp : p = corner i j ∨ p = flip (corner i j) k) :
      chooseCorner (i, j) = p := by
    have hopp : a i = -a j := by rw [hi, hj, neg_neg]
    have hsingle := (eightfold_corner_rule hr hs hv hvk hcover hik hjk).2.mp hopp
    change (corner i j ∈ C ∧ flip (corner i j) k ∉ C) ∨
      (corner i j ∉ C ∧ flip (corner i j) k ∈ C) at hsingle
    rcases hp with rfl | rfl
    · simp [chooseCorner, hpC]
    · rcases hsingle with h | h
      · exact (h.2 hpC).elim
      · simp [chooseCorner, h.1]
  rw [← hcard]
  symm
  apply Finset.card_bij (fun ij _ => chooseCorner ij)
  · intro ij h
    obtain ⟨hik, hjk, hi, hj, hij⟩ := pair_spec h
    have hopp : a ij.1 = -a ij.2 := by rw [hi, hj, neg_neg]
    have hsingle := (eightfold_corner_rule hr hs hv hvk hcover hik hjk).2.mp hopp
    change (corner ij.1 ij.2 ∈ C ∧ flip (corner ij.1 ij.2) k ∉ C) ∨
      (corner ij.1 ij.2 ∉ C ∧ flip (corner ij.1 ij.2) k ∈ C) at hsingle
    refine Finset.mem_filter.mpr ⟨?_, ij.1, ij.2, hik, hjk, hij, choice_spec ij⟩
    rcases hsingle with h | h
    · simpa only [chooseCorner, ite_eq_left h.1] using h.1
    · simpa only [chooseCorner, ite_eq_right h.1] using h.2
  · intro ij hij ab hab he
    change chooseCorner ij = chooseCorner ab at he
    obtain ⟨hik, hjk, hi, hj, hne⟩ := pair_spec hij
    obtain ⟨hak, hbk, ha, hb, hne'⟩ := pair_spec hab
    have hpair : ({ij.1, ij.2} : Finset (Fin 9)) = {ab.1, ab.2} := by
      rw [← corner_disagreements hik hjk hne (choice_spec ij), he,
        corner_disagreements hak hbk hne' (choice_spec ab)]
    have hfirst : ij.1 ∈ ({ab.1, ab.2} : Finset (Fin 9)) := by
      rw [← hpair]
      exact Finset.mem_insert_self _ _
    have hsecond : ij.2 ∈ ({ab.1, ab.2} : Finset (Fin 9)) := by
      rw [← hpair]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
    refine Prod.ext (hfirst.resolve_right ?_) (hsecond.resolve_left ?_)
    · intro h
      rw [h, hb] at hi
      norm_num at hi
    · intro h
      rw [h, ha] at hj
      norm_num at hj
  · intro p hp
    obtain ⟨hpC, i, j, hik, hjk, hij, hpCorner⟩ :=
      Finset.mem_filter.mp (show p ∈ selectedCorners C v k from hp)
    have hne : a i ≠ a j := by
      intro he
      obtain ⟨hl, hu⟩ := (eightfold_corner_rule hr hs hv hvk hcover hik hjk).1.mp he
      rcases hpCorner with rfl | rfl
      · exact hl hpC
      · exact hu hpC
    have usePair (i j : Fin 9) (hik : i ≠ k) (hjk : j ≠ k)
        (hi : a i = 1) (hj : a j = -1)
        (hpCorner : p = corner i j ∨ p = flip (corner i j) k) :
        ∃ ij, ∃ _ : ij ∈ pairs, chooseCorner ij = p := by
      refine ⟨(i, j), Finset.mem_product.mpr ⟨?_, ?_⟩, choice_eq hik hjk hi hj hpC hpCorner⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hik, Finset.mem_univ _⟩, hi⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩, hj⟩
    rcases transverseSign_unit hs (hcover i hik).1 with hi | hi
    · exact usePair i j hik hjk hi ((transverseSign_unit hs (hcover j hjk).1).resolve_left
        (fun hj => hne (hi.trans hj.symm))) hpCorner
    · exact usePair j i hjk hik ((transverseSign_unit hs (hcover j hjk).1).resolve_right
        (fun hj => hne (hi.trans hj.symm))) hi
        (by simpa only [corner, flip_comm v j i] using hpCorner)

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal
