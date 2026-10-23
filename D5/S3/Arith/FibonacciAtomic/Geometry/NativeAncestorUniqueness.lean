/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordered leaf words and ancestor coordinates uniquely determine native labelled trees. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval
import D5.S3.Combinatorics.Partitions.WordPartitionInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestorUniqueness
open GenealogicalFiberTransport (Source)
open D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)
open AncestorAreaInterval (coordinates area offset CompleteSubtree ancestor_area_interval)
open ActualTreeReadoutAcquisition (Address)
open ActualLeafHistoryRigidity (subtree)

set_option maxHeartbeats 1600000 in
-- Address navigation and the native tree induction share the proof budget.
/-- Equality of the complete ordered leaf words and actual inorder ancestor
coordinates forces literal equality of the native labelled trees. -/
theorem native_ancestor_uniqueness (s t : Source)
    (word_eq : wd s = wd t) (area_eq : coordinates s = coordinates t) : s = t := by
  have wordLength (u : Source) : (wd u).length = u.length := by
    simpa only [wd, List.length_cons, FreeSemigroup.length] using
      FreeMagma.length_toFreeSemigroup u
  have coordLength : ∀ u : Source, (coordinates u).length = u.length-1 := by
    intro u
    induction u with
    | of b => rfl
    | mul l r hl hr =>
      have hp := FreeMagma.length_pos l
      have hq := FreeMagma.length_pos r
      simp only [coordinates, List.length_append, List.length_singleton, hl, hr, FreeMagma.length]
      omega
  have occurrenceBound : ∀ (u : Address) (v q : Source), subtree u v = some q →
      offset v u + q.length ≤ v.length := by
    intro u
    induction u with
    | nil =>
      intro v q h
      have he : v = q := Option.some.inj h
      subst q
      simp [offset]
    | cons d u ih =>
      intro v q h
      cases v with
      | of b => simp [subtree] at h
      | mul l r =>
        cases d with
        | false =>
          have hh := ih l q h
          simp only [offset, FreeMagma.length]
          omega
        | true =>
          have hh := ih r q h
          simp only [offset, FreeMagma.length]
          omega
  have prefixBound (l r : Source) (n : ℕ) (hn : n < (.mul l r : Source).length)
      (hc : CompleteSubtree (.mul l r) 1 n) : n ≤ l.length := by
    obtain ⟨u,q,hu,ha,hb,_⟩ := hc
    cases u with
    | nil =>
      have he : (.mul l r : Source) = q := Option.some.inj hu
      subst q
      simp only [offset, Nat.zero_add] at hb
      omega
    | cons d u =>
      cases d with
      | false =>
        have hh := occurrenceBound u l q hu
        simp only [offset] at hb
        omega
      | true =>
        have hp := FreeMagma.length_pos l
        simp only [offset] at ha
        omega
  have leafLength (u : Source) : (ActualTreeReadoutAcquisition.leaves u).length = u.length := by
    rw [← List.toFinset_card_of_nodup (ActualJointResponseCostCore.cost_foundation.1 u).1]
    exact (ActualImageSevenLeafSeparation.seven_leaf_separation.1 u).1
  have leftComplete (l r : Source) : CompleteSubtree (.mul l r) 1 l.length := by
    refine ⟨[false], l, rfl, by simp [offset], by simp [offset], ?_⟩
    have hp := FreeMagma.length_pos l
    have hk : l.length-1+1 = l.length := by omega
    simp only [Nat.sub_self,List.drop_zero,hk,ActualTreeReadoutAcquisition.leaves]
    rw [List.take_append_of_le_length (by simp only [List.length_map,leafLength]; omega),
      List.take_of_length_le (by simp only [List.length_map,leafLength]; omega)]
    rfl
  have coordTake (u v : Source) : (coordinates (.mul u v)).take (u.length-1) =
      coordinates u := by
    rw [coordinates,List.append_assoc,
      List.take_append_of_le_length (by rw [coordLength]),
      List.take_of_length_le (by rw [coordLength])]
  have coordDrop (u v : Source) : (coordinates (.mul u v)).drop u.length =
      coordinates v := by
    have hp := FreeMagma.length_pos u
    rw [coordinates,List.drop_append,
      List.drop_eq_nil_of_le (by
        simp only [List.length_append,List.length_singleton,coordLength]; omega),
      List.nil_append]
    have hn : u.length-((coordinates u ++ [u.length*v.length]).length) = 0 := by
      simp only [List.length_append,List.length_singleton,coordLength]; omega
    rw [hn,List.drop_zero]
  have wordTake (u v : Source) : (wd (.mul u v)).take u.length = wd u := by
    change List.take u.length (wd (u*v)) = _
    rw [show wd (u*v) = wd u ++ wd v by simp [wd,map_mul],
      List.take_append_of_le_length (by rw [wordLength]),
      List.take_of_length_le (by rw [wordLength])]
  have wordDrop (u v : Source) : (wd (.mul u v)).drop u.length = wd v := by
    change List.drop u.length (wd (u*v)) = _
    rw [show wd (u*v) = wd u ++ wd v by simp [wd,map_mul],List.drop_append,
      List.drop_eq_nil_of_le (by rw [wordLength]),List.nil_append,wordLength,
      Nat.sub_self,List.drop_zero]
  induction s generalizing t with
  | of a =>
    cases t with
    | of b =>
      have hab : a = b := by simpa [wd] using word_eq
      subst b
      rfl
    | mul l r =>
      have hlen := congrArg List.length word_eq
      rw [wordLength,wordLength] at hlen
      have hp := FreeMagma.length_pos l
      have hq := FreeMagma.length_pos r
      simp only [FreeMagma.length] at hlen
      omega
  | mul l r hl hr =>
    cases t with
    | of b =>
      have hlen := congrArg List.length word_eq
      rw [wordLength,wordLength] at hlen
      have hp := FreeMagma.length_pos l
      have hq := FreeMagma.length_pos r
      simp only [FreeMagma.length] at hlen
      omega
    | mul p q =>
      have hp := FreeMagma.length_pos l
      have hq := FreeMagma.length_pos r
      have hpp := FreeMagma.length_pos p
      have hqq := FreeMagma.length_pos q
      have hlen := congrArg List.length word_eq
      rw [wordLength,wordLength] at hlen
      simp only [FreeMagma.length] at hlen
      have transfer (n : ℕ) (hn : 1 ≤ n) (hb : n ≤ l.length+r.length) :
          CompleteSubtree (.mul l r) 1 n ↔ CompleteSubtree (.mul p q) 1 n := by
        have hs := (ancestor_area_interval (.mul l r) 1 n (by omega) hn hb).2
        have ht := (ancestor_area_interval (.mul p q) 1 n (by omega) hn (by
          simp only [FreeMagma.length]; omega)).2
        have he : area (.mul l r) 1 n = area (.mul p q) 1 n := by
          simp only [area,area_eq]
        rw [← hs, ← ht, he]
      have leftLe : l.length ≤ p.length :=
        prefixBound p q l.length (by simp only [FreeMagma.length]; omega)
          ((transfer l.length hp (by omega)).mp (leftComplete l r))
      have rightLe : p.length ≤ l.length :=
        prefixBound l r p.length (by simp only [FreeMagma.length]; omega)
          ((transfer p.length hpp (by omega)).mpr (leftComplete p q))
      have split : l.length = p.length := Nat.le_antisymm leftLe rightLe
      have leftCoords : coordinates l = coordinates p := by
        have he := congrArg (List.take (l.length-1)) area_eq
        rw [coordTake,split,coordTake] at he
        exact he
      have rightCoords : coordinates r = coordinates q := by
        have he := congrArg (List.drop l.length) area_eq
        rw [coordDrop,split,coordDrop] at he
        exact he
      have leftWord : wd l = wd p := by
        have he := congrArg (List.take l.length) word_eq
        rw [wordTake,split,wordTake] at he
        exact he
      have rightWord : wd r = wd q := by
        have he := congrArg (List.drop l.length) word_eq
        rw [wordDrop,split,wordDrop] at he
        exact he
      exact congrArg₂ FreeMagma.mul (hl p leftWord leftCoords) (hr q rightWord rightCoords)

#print axioms native_ancestor_uniqueness

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestorUniqueness
