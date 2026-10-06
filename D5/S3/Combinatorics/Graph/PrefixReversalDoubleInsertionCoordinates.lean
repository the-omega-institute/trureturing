/- GID: D5/S3/Combinatorics/Graph/PrefixReversalDoubleInsertionCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversalDoubleInsertionCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: Two insertion gaps classify the actual complete conversion domain. -/

import D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversalDoubleInsertionCoordinates

open PrefixReversalTripleOddNonGeneration
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open Fin.NatCast

/-- The two marked labels are deleted before any walk is specified. -/
def DoubleStar {m : ℕ} (t s : Fin (m + 2)) (P : Cycle (Fin (m + 2)))
    (v : Configuration (m + 1)) : Prop :=
  delete t (delete s (configurationCycle v)) = P ∨
    delete t (delete s (configurationCycle v)) = P.reverse

/-- The first `q` entries of an actual configuration. -/
private def blockList {N : ℕ} (q : ℕ) (hq : q ≤ N) (v : Equiv.Perm (Fin N)) :
    List (Fin N) := List.ofFn (fun i : Fin q => v (Fin.castLE hq i))

/-- This permutation is only a coordinate operation, not a fourth graph generator. -/
private def blockTurn {N : ℕ} (q : ℕ) (hq : q ≤ N) : Equiv.Perm (Fin N) :=
  prefixReversal q hq * prefixReversal (q - 1) (by omega)

private theorem blockTurn_apply {N q : ℕ} (hq : q ≤ N) (hqp : 2 ≤ q)
    (i : Fin N) :
    blockTurn q hq i =
      if hi : i.val < q then
        (⟨(i.val + 1) % q, (Nat.mod_lt _ (by omega)).trans_le hq⟩ : Fin N)
      else i := by
  apply Fin.ext
  simp only [blockTurn, Equiv.Perm.mul_apply]
  change (reverseIndex q hq (reverseIndex (q - 1) (by omega) i)).val = _
  by_cases hs : i.val < q - 1
  · have ht : q - 1 - 1 - i.val < q := by omega
    simp [reverseIndex, hs, ht, show i.val < q by omega,
      Nat.mod_eq_of_lt (show i.val + 1 < q by omega)]
    omega
  · by_cases ht : i.val < q
    · have he : i.val = q - 1 := by omega
      simp [reverseIndex, he, show 0 < q by omega, Nat.sub_add_cancel (show 1 ≤ q by omega)]
    · simp [reverseIndex, hs, ht]

private theorem blockTurn_cast {N q : ℕ} (hq : q ≤ N) (hqp : 2 ≤ q)
    (i : Fin q) :
    blockTurn q hq (Fin.castLE hq i) = Fin.castLE hq (finRotate q i) := by
  apply Fin.ext
  rw [blockTurn_apply hq hqp]
  simp [i.isLt, finRotate_apply, Fin.add_def]

private theorem blockTurn_pow_cast {N q : ℕ} (hq : q ≤ N) (hqp : 2 ≤ q)
    (r : ℕ) (i : Fin q) :
    (blockTurn q hq ^ r) (Fin.castLE hq i) = Fin.castLE hq ((finRotate q ^ r) i) := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, blockTurn_cast hq hqp, ih,
      pow_succ, Equiv.Perm.mul_apply]

private theorem blockTurn_pow_fixed {N q : ℕ} (hq : q ≤ N) (hqp : 2 ≤ q)
    (r : ℕ) (i : Fin N) (hi : q ≤ i.val) : (blockTurn q hq ^ r) i = i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, blockTurn_apply hq hqp,
      dif_neg (by omega), ih]

private theorem blockTurn_list {N q : ℕ} (hq : q ≤ N) (hqp : 2 ≤ q)
    (v : Equiv.Perm (Fin N)) :
    blockList q hq (v * blockTurn q hq) = (blockList q hq v).rotate 1 := by
  apply List.ext_getElem
  · simp [blockList]
  · intro i hi hj
    simp only [blockList, List.getElem_ofFn, List.getElem_rotate, List.length_ofFn,
      Equiv.Perm.mul_apply]
    rw [blockTurn_cast hq hqp]
    congr 1
    apply Fin.ext
    simp [finRotate_apply, Fin.add_def]

private theorem blockTurn_pow_list {N q : ℕ} (hq : q ≤ N) (hqp : 2 ≤ q)
    (v : Equiv.Perm (Fin N)) (r : ℕ) :
    blockList q hq (v * blockTurn q hq ^ r) = (blockList q hq v).rotate r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, blockTurn_list hq hqp, ih, List.rotate_rotate]

private theorem blockList_nodup {N q : ℕ} (hq : q ≤ N)
    (v : Equiv.Perm (Fin N)) : (blockList q hq v).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin N => i.val) (v.injective h)

private theorem residual_split {m : ℕ} (z : Configuration (m + 1)) :
    residualList z = blockList m (by omega) z ++ [z ((Fin.last m).castSucc)] := by
  simp only [residualList, List.ofFn_succ', List.concat_eq_append]
  rfl

private theorem double_delete {m : ℕ} (z : Configuration (m + 1)) :
    delete (z ((Fin.last m).castSucc))
        (delete (z (Fin.last (m + 1))) (configurationCycle z)) =
      (blockList m (by omega) z : Cycle (Fin (m + 2))) := by
  rw [configurationCycle_delete_last, residual_split]
  change (((blockList m (by omega) z ++ [z ((Fin.last m).castSucc)]).filter
    (fun y => decide (y ≠ z ((Fin.last m).castSucc)))) : Cycle (Fin (m + 2))) = _
  rw [List.filter_append]
  have hf : (blockList m (by omega) z).filter
      (fun y => decide (y ≠ z ((Fin.last m).castSucc))) = blockList m (by omega) z := by
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp only [decide_eq_true_eq, ne_eq, z.injective.eq_iff]
    intro he
    have hv := congrArg Fin.val he
    dsimp at hv
    omega
  rw [hf]
  simp

private theorem delete_reverse {α : Type*} [DecidableEq α] (t : α) (C : Cycle α) :
    delete t C.reverse = (delete t C).reverse := by
  induction C using Quotient.inductionOn with
  | _ l =>
    change ((l.reverse.filter (fun y => decide (y ≠ t))) : Cycle α) = _
    rw [List.filter_reverse]
    rfl

private theorem full_cycle_list {m : ℕ} (v : Configuration m) (r : Fin (m + 1)) :
    List.ofFn (v * finCycle r) = (List.ofFn v).rotate r.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_rotate, List.length_ofFn,
      Equiv.Perm.mul_apply]
    congr 1

private theorem configuration_cycle_rotate {m : ℕ} (v : Configuration m)
    (r : Fin (m + 1)) : configurationCycle (v * finCycle r) = configurationCycle v := by
  apply Cycle.coe_eq_coe.mpr
  rw [full_cycle_list]
  exact List.IsRotated.symm ⟨r.val, rfl⟩

private theorem block_reverse_list {N q : ℕ} (hq : q ≤ N)
    (v : Equiv.Perm (Fin N)) :
    blockList q hq (v * prefixReversal q hq) = (blockList q hq v).reverse := by
  apply List.ext_getElem
  · simp [blockList]
  · intro i hi hj
    simp only [blockList, List.getElem_ofFn, List.getElem_reverse, List.length_ofFn,
      Equiv.Perm.mul_apply]
    congr 1
    apply Fin.ext
    simp [prefixReversal, reverseIndex, show i < q by simpa [blockList] using hi]

private theorem prefix_fixed {N q : ℕ} (hq : q ≤ N) (i : Fin N) (hi : q ≤ i.val) :
    prefixReversal q hq i = i := by
  change reverseIndex q hq i = i
  simp [reverseIndex, show ¬i.val < q by omega]

private theorem configuration_eq_of_block_last_two {m : ℕ}
    {u v : Configuration (m + 1)}
    (hr : blockList m (by omega) u = blockList m (by omega) v)
    (ht : u ((Fin.last m).castSucc) = v ((Fin.last m).castSucc))
    (hs : u (Fin.last (m + 1)) = v (Fin.last (m + 1))) : u = v := by
  have hf := List.ofFn_injective hr
  apply Equiv.ext
  intro i
  refine Fin.lastCases hs (fun j => ?_) i
  refine Fin.lastCases ht (fun k => ?_) j
  exact congrFun hf k

/-- Rotate only the residual labels, leaving the two marked labels at the end. -/
def outerAnchor {m : ℕ} (z : Configuration (m + 1)) (k : Fin m) : Configuration (m + 1) :=
  z * blockTurn m (by omega) ^ k.val

/-- The independent current circle corresponding to a t insertion gap. -/
def outerCircle {m : ℕ} (z : Configuration (m + 1)) (k : Fin m) : Cycle (Fin (m + 2)) :=
  (residualList (outerAnchor z k) : Cycle (Fin (m + 2)))

private theorem outer_last {m : ℕ} (hm : 2 ≤ m) (z : Configuration (m + 1)) (k : Fin m) :
    outerAnchor z k (Fin.last (m + 1)) = z (Fin.last (m + 1)) := by
  simp only [outerAnchor, Equiv.Perm.mul_apply]
  rw [blockTurn_pow_fixed (by omega) hm _ _ (by simp)]

private theorem outer_penult {m : ℕ} (hm : 2 ≤ m) (z : Configuration (m + 1)) (k : Fin m) :
    outerAnchor z k ((Fin.last m).castSucc) = z ((Fin.last m).castSucc) := by
  simp only [outerAnchor, Equiv.Perm.mul_apply]
  rw [blockTurn_pow_fixed (by omega) hm _ _ (by simp)]

private theorem outer_block {m : ℕ} (hm : 2 ≤ m) (z : Configuration (m + 1)) (k : Fin m) :
    blockList m (by omega) (outerAnchor z k) = (blockList m (by omega) z).rotate k.val :=
  blockTurn_pow_list (by omega) hm z k.val

private theorem outer_double_delete {m : ℕ} (hm : 2 ≤ m) (z : Configuration (m + 1))
    (k : Fin m) :
    delete (z ((Fin.last m).castSucc)) (outerCircle z k) =
      (blockList m (by omega) z : Cycle (Fin (m + 2))) := by
  rw [← outer_penult hm z k, outerCircle, ← configurationCycle_delete_last,
    double_delete, outer_block hm]
  exact Cycle.coe_eq_coe.mpr (List.IsRotated.symm ⟨k.val, rfl⟩)

private theorem block_not_reverse {m : ℕ} (hm : 3 ≤ m) (z : Configuration (m + 1)) :
    (blockList m (by omega) z : Cycle (Fin (m + 2))) ≠
      (blockList m (by omega) z : Cycle (Fin (m + 2))).reverse := by
  intro he
  have hn := Cycle.nodup_coe_iff.mpr (blockList_nodup (show m ≤ m + 2 by omega) z)
  have hw : DeleteWalk [] (blockList m (by omega) z : Cycle (Fin (m + 2)))
      (blockList m (by omega) z : Cycle (Fin (m + 2))).reverse := by
    rw [← he]
    exact DeleteWalk.nil _
  have hb := negative_walk_support_bound hw hn
  change (blockList m (by omega) z).toFinset.card ≤ 2 at hb
  rw [List.toFinset_card_of_nodup (blockList_nodup _ z)] at hb
  simp only [blockList, List.length_ofFn] at hb
  omega

private theorem positive_last_two_anchor {m : ℕ} (hm : 2 ≤ m)
    (z w : Configuration (m + 1))
    (hs : w (Fin.last (m + 1)) = z (Fin.last (m + 1)))
    (ht : w ((Fin.last m).castSucc) = z ((Fin.last m).castSucc))
    (hd : delete (z ((Fin.last m).castSucc))
      (delete (z (Fin.last (m + 1))) (configurationCycle w)) =
        (blockList m (by omega) z : Cycle (Fin (m + 2)))) :
    ∃ k : Fin m, w = outerAnchor z k := by
  rw [← hs, ← ht, double_delete] at hd
  obtain ⟨r, hr⟩ := (Cycle.coe_eq_coe.mp hd).symm
  let k : Fin m := ⟨r % m, Nat.mod_lt _ (by omega)⟩
  refine ⟨k, configuration_eq_of_block_last_two ?_ ?_ ?_⟩
  · rw [outer_block hm]
    have he := (List.rotate_mod (blockList m (by omega) z) r).trans hr
    simpa only [blockList, List.length_ofFn, k] using he.symm
  · rw [outer_penult hm]
    exact ht
  · rw [outer_last hm]
    exact hs

private theorem outer_first {m : ℕ} (hm : 2 ≤ m) (z : Configuration (m + 1)) (k : Fin m) :
    outerAnchor z k (⟨0, by omega⟩ : Fin (m + 2)) = z (Fin.castLE (by omega) k) := by
  have he := congrArg (fun l : List (Fin (m + 2)) => l[0]?) (outer_block hm z k)
  rw [List.getElem?_rotate (by simp [blockList]; omega)] at he
  simpa [blockList, show 0 < m by omega, Nat.mod_eq_of_lt k.isLt] using he

private theorem outer_next {m : ℕ} (hm : 2 ≤ m) (z : Configuration (m + 1)) (k : Fin m)
    (hn : (outerCircle z k).Nodup)
    (ht : z ((Fin.last m).castSucc) ∈ outerCircle z k) :
    (outerCircle z k).next hn (z ((Fin.last m).castSucc)) ht =
      z (Fin.castLE (by omega) k) := by
  have hnd : (residualList (outerAnchor z k)).Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j h
    exact Fin.castSucc_injective _ ((outerAnchor z k).injective h)
  have hx : (residualList (outerAnchor z k))[m]'(by simp [residualList]) =
      z ((Fin.last m).castSucc) := by
    simp only [residualList, List.getElem_ofFn]
    exact outer_penult hm z k
  change List.next (residualList (outerAnchor z k)) (z ((Fin.last m).castSucc))
    (Cycle.mem_coe_iff.mp ht) = _
  calc
    _ = (residualList (outerAnchor z k))[(m + 1) %
        (residualList (outerAnchor z k)).length]'(by simp [residualList]) := by
      simpa only [hx] using
        List.next_getElem (residualList (outerAnchor z k)) hnd m (by simp [residualList])
    _ = _ := by
      simp only [residualList, List.length_ofFn, Nat.mod_self, List.getElem_ofFn]
      exact outer_first hm z k

private theorem outerCircle_injective {m : ℕ} (hm : 3 ≤ m) (z : Configuration (m + 1)) :
    Function.Injective (outerCircle z) := by
  intro k l he
  have hnk : (outerCircle z k).Nodup := by
    apply Cycle.nodup_coe_iff.mpr
    apply List.nodup_ofFn.mpr
    intro i j h
    exact Fin.castSucc_injective _ ((outerAnchor z k).injective h)
  have hnl : (outerCircle z l).Nodup := he ▸ hnk
  have htk : z ((Fin.last m).castSucc) ∈ outerCircle z k := by
    change z ((Fin.last m).castSucc) ∈ (residualList (outerAnchor z k) : Cycle (Fin (m + 2)))
    rw [Cycle.mem_coe_iff]
    apply List.mem_ofFn.mpr
    exact ⟨Fin.last m, outer_penult (by omega) z k⟩
  have htl : z ((Fin.last m).castSucc) ∈ outerCircle z l := he ▸ htk
  have hn : (outerCircle z k).next hnk (z ((Fin.last m).castSucc)) htk =
      (outerCircle z l).next hnl (z ((Fin.last m).castSucc)) htl := by
    have hc : ∀ (C D : Cycle (Fin (m + 2))) (h : C = D)
        (hC : C.Nodup) (hD : D.Nodup)
        (htC : z ((Fin.last m).castSucc) ∈ C) (htD : z ((Fin.last m).castSucc) ∈ D),
        C.next hC (z ((Fin.last m).castSucc)) htC =
          D.next hD (z ((Fin.last m).castSucc)) htD := by
      intro C D h
      cases h
      intro hC hD htC htD
      rfl
    exact hc _ _ he _ _ _ _
  rw [outer_next (by omega), outer_next (by omega)] at hn
  apply Fin.ext
  exact congrArg (fun i : Fin (m + 2) => i.val) (z.injective hn)

private theorem outer_not_reverse {m : ℕ} (hm : 3 ≤ m) (z : Configuration (m + 1))
    (k l : Fin m) : outerCircle z k ≠ (outerCircle z l).reverse := by
  intro he
  have hd := congrArg (delete (z ((Fin.last m).castSucc))) he
  rw [outer_double_delete (by omega), delete_reverse,
    outer_double_delete (by omega)] at hd
  exact block_not_reverse hm z hd

private theorem prefix_current_rotate {m : ℕ} (hm : 2 ≤ m)
    (v : Configuration (m + 1)) (r : ℕ) :
    delete (v (Fin.last (m + 1)))
      (configurationCycle (v * blockTurn (m + 1) (by omega) ^ r)) =
        delete (v (Fin.last (m + 1))) (configurationCycle v) := by
  have hl : ((v * blockTurn (m + 1) (by omega) ^ r) : Configuration (m + 1)) (Fin.last (m + 1)) =
      v (Fin.last (m + 1)) := by
    simp only [Equiv.Perm.mul_apply]
    rw [blockTurn_pow_fixed (by omega) (by omega) _ _ (by simp)]
  calc
    delete (v (Fin.last (m + 1)))
        (configurationCycle (v * blockTurn (m + 1) (by omega) ^ r)) =
        (residualList (v * blockTurn (m + 1) (by omega) ^ r) : Cycle (Fin (m + 2))) := by
      rw [← hl, configurationCycle_delete_last]
    _ = (residualList v : Cycle (Fin (m + 2))) := by
      change (blockList (m + 1) (by omega) (v * blockTurn (m + 1) (by omega) ^ r) : Cycle (Fin (m + 2))) =
        (blockList (m + 1) (by omega) v : Cycle (Fin (m + 2)))
      rw [blockTurn_pow_list (by omega) (by omega)]
      exact Cycle.coe_eq_coe.mpr (List.IsRotated.symm ⟨r, rfl⟩)
    _ = delete (v (Fin.last (m + 1))) (configurationCycle v) :=
      (configurationCycle_delete_last v).symm

private theorem residual_block_reverse {m : ℕ} (v : Configuration (m + 1)) :
    delete (v (Fin.last (m + 1)))
      (configurationCycle (v * prefixReversal m (by omega))) =
        (delete (v (Fin.last (m + 1))) (configurationCycle v)).reverse := by
  have hl : ((v * prefixReversal m (by omega)) : Configuration (m + 1)) (Fin.last (m + 1)) =
      v (Fin.last (m + 1)) := by
    rw [Equiv.Perm.mul_apply, prefix_fixed (by omega) _ (by simp)]
  calc
    delete (v (Fin.last (m + 1)))
        (configurationCycle (v * prefixReversal m (by omega))) =
        (residualList (v * prefixReversal m (by omega)) : Cycle (Fin (m + 2))) := by
      rw [← hl, configurationCycle_delete_last]
    _ = (residualList v : Cycle (Fin (m + 2))).reverse := by
      rw [residual_split, block_reverse_list, Equiv.Perm.mul_apply,
        prefix_fixed (by omega) _ (by simp), residual_split, Cycle.reverse_coe,
        List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append]
      exact Cycle.coe_cons_eq_coe_append _ _ |>.symm
    _ = (delete (v (Fin.last (m + 1))) (configurationCycle v)).reverse :=
      congrArg Cycle.reverse (configurationCycle_delete_last v).symm

private theorem outer_classification {m : ℕ} (hm : 3 ≤ m)
    (z v : Configuration (m + 1))
    (hv : DoubleStar (z ((Fin.last m).castSucc)) (z (Fin.last (m + 1)))
      (blockList m (by omega) z : Cycle (Fin (m + 2))) v) :
    ∃ k : Fin m, Star (z (Fin.last (m + 1))) (outerCircle z k) v := by
  let s := z (Fin.last (m + 1))
  let t := z ((Fin.last m).castSucc)
  let d : Fin (m + 2) := v.symm s + 1
  let w := v * finCycle d
  have hs : w (Fin.last (m + 1)) = s := by
    change v (Fin.last (m + 1) + d) = s
    have hi : Fin.last (m + 1) + d = v.symm s := by
      dsimp [d]
      have ht : Fin.last (m + 1) + (1 : Fin (m + 2)) = 0 := by
        rw [← Fin.neg_last (m + 1)]
        exact add_neg_cancel _
      calc
        Fin.last (m + 1) + (v.symm s + 1) =
            (Fin.last (m + 1) + 1) + v.symm s := by abel
        _ = v.symm s := by rw [ht, zero_add]
    rw [hi, v.apply_symm_apply]
  have hst : s ≠ t := by
    dsimp [s, t]
    intro he
    have hh := congrArg Fin.val (z.injective he)
    simp at hh
  have hip : (w.symm t).val < m + 1 := by
    have hne : w.symm t ≠ Fin.last (m + 1) := by
      intro he
      have hh := congrArg w he
      simp only [Equiv.apply_symm_apply, hs] at hh
      exact hst hh.symm
    have hh := (w.symm t).isLt
    have hn : (w.symm t).val ≠ m + 1 := fun h => hne (Fin.ext h)
    omega
  let i : Fin (m + 1) := ⟨(w.symm t).val, hip⟩
  let e : Fin (m + 1) := i + 1
  let q := w * blockTurn (m + 1) (by omega) ^ e.val
  have hqs : q (Fin.last (m + 1)) = s := by
    change w ((blockTurn (m + 1) (by omega) ^ e.val) (Fin.last (m + 1))) = s
    rw [blockTurn_pow_fixed (by omega) (by omega) _ _ (by simp)]
    exact hs
  have hqt : q ((Fin.last m).castSucc) = t := by
    dsimp [q]
    rw [Equiv.Perm.mul_apply]
    change w ((blockTurn (m + 1) (by omega) ^ e.val) (Fin.castLE (by omega) (Fin.last m))) = t
    rw [blockTurn_pow_cast (by omega) (by omega)]
    have hfe : (finRotate (m + 1) ^ e.val) (Fin.last m) = finCycle e (Fin.last m) := by
      simpa only [Equiv.Perm.coe_pow] using
        congrFun (finCycle_eq_finRotate_iterate (k := e)).symm (Fin.last m)
    rw [hfe]
    have hei : finCycle e (Fin.last m) = i := by
      simp only [finCycle_apply]
      dsimp [e]
      have hlast : Fin.last m + (1 : Fin (m + 1)) = 0 := by
        rw [← Fin.neg_last m]
        exact add_neg_cancel _
      calc
        Fin.last m + (i + 1) = (Fin.last m + 1) + i := by abel
        _ = i := by rw [hlast, zero_add]
    rw [hei]
    have hic : Fin.castLE (show m + 1 ≤ m + 2 by omega) i = w.symm t := Fin.ext rfl
    rw [hic, w.apply_symm_apply]
  have hcurrent : delete s (configurationCycle q) = delete s (configurationCycle v) := by
    calc
      delete s (configurationCycle q) = delete s (configurationCycle w) := by
        dsimp [q]
        rw [← hs]
        exact prefix_current_rotate (by omega) w e.val
      _ = delete s (configurationCycle v) := congrArg (delete s) (configuration_cycle_rotate v d)
  have hqd : DoubleStar t s (blockList m (by omega) z : Cycle (Fin (m + 2))) q := by
    simpa only [DoubleStar, hcurrent] using hv
  rcases hqd with hd | hd
  · obtain ⟨k, hk⟩ := positive_last_two_anchor (by omega) z q hqs hqt hd
    refine ⟨k, Or.inl ?_⟩
    rw [← hcurrent, hk]
    change delete (z (Fin.last (m + 1))) (configurationCycle (outerAnchor z k)) = outerCircle z k
    rw [← outer_last (by omega) z k, configurationCycle_delete_last]
    rfl
  · let q' := q * prefixReversal m (by omega)
    have hq's : q' (Fin.last (m + 1)) = s := by
      change q (prefixReversal m (by omega) (Fin.last (m + 1))) = s
      rw [prefix_fixed (by omega) _ (by simp)]
      exact hqs
    have hq't : q' ((Fin.last m).castSucc) = t := by
      change q (prefixReversal m (by omega) ((Fin.last m).castSucc)) = t
      rw [prefix_fixed (by omega) _ (by simp)]
      exact hqt
    have hq'c : delete s (configurationCycle q') = (delete s (configurationCycle q)).reverse := by
      dsimp [q']
      rw [← hqs]
      exact residual_block_reverse q
    have hq'd : delete t (delete s (configurationCycle q')) =
        (blockList m (by omega) z : Cycle (Fin (m + 2))) := by
      rw [hq'c, delete_reverse, hd, Cycle.reverse_reverse]
    obtain ⟨k, hk⟩ := positive_last_two_anchor (by omega) z q' hq's hq't hq'd
    refine ⟨k, Or.inr ?_⟩
    have hcc : (delete s (configurationCycle v)).reverse = outerCircle z k := by
      rw [← hcurrent, ← hq'c, hk]
      change delete (z (Fin.last (m + 1))) (configurationCycle (outerAnchor z k)) = outerCircle z k
      rw [← outer_last (by omega) z k, configurationCycle_delete_last]
      rfl
    simpa only [Cycle.reverse_reverse] using congrArg Cycle.reverse hcc

/-- Literal two-gap coordinates; the inner native-circle coordinates are reused. -/
def doubleCoordinate {m : ℕ} (z : Configuration (m + 1))
    (p : Fin m × Fin (m + 1) × Fin (m + 2) × Bool) : Configuration (m + 1) :=
  coordinate (outerAnchor z p.1) p.2

private theorem doubleCoordinate_star {m : ℕ} (hm : 3 ≤ m)
    (z : Configuration (m + 1)) (p : Fin m × Fin (m + 1) × Fin (m + 2) × Bool) :
    DoubleStar (z ((Fin.last m).castSucc)) (z (Fin.last (m + 1)))
      (blockList m (by omega) z : Cycle (Fin (m + 2))) (doubleCoordinate z p) := by
  have hv := ((coordinateEquiv (show 3 ≤ m + 1 by omega) (outerAnchor z p.1)) p.2).property
  change Star ((outerAnchor z p.1) (Fin.last (m + 1)))
    (outerCircle z p.1) (doubleCoordinate z p) at hv
  rw [outer_last (by omega)] at hv
  rcases hv with hd | hd
  · left
    rw [hd, outer_double_delete (by omega)]
  · right
    rw [hd, delete_reverse, outer_double_delete (by omega)]

private theorem doubleCoordinate_injective {m : ℕ} (hm : 3 ≤ m)
    (z : Configuration (m + 1)) : Function.Injective (doubleCoordinate z) := by
  rintro ⟨k, p⟩ ⟨l, q⟩ he
  have hpk := ((coordinateEquiv (show 3 ≤ m + 1 by omega) (outerAnchor z k)) p).property
  have hql := ((coordinateEquiv (show 3 ≤ m + 1 by omega) (outerAnchor z l)) q).property
  change Star ((outerAnchor z k) (Fin.last (m + 1))) (outerCircle z k) (doubleCoordinate z (k, p)) at hpk
  change Star ((outerAnchor z l) (Fin.last (m + 1))) (outerCircle z l) (doubleCoordinate z (l, q)) at hql
  rw [outer_last (by omega)] at hpk hql
  rw [← he] at hql
  have hk : k = l := by
    rcases hpk with hp | hp <;> rcases hql with hq | hq
    · exact outerCircle_injective hm z (hp.symm.trans hq)
    · exact (outer_not_reverse hm z k l (hp.symm.trans hq)).elim
    · exact (outer_not_reverse hm z l k (hq.symm.trans hp)).elim
    · apply outerCircle_injective hm z
      simpa only [Cycle.reverse_reverse] using congrArg Cycle.reverse (hp.symm.trans hq)
  subst l
  have hpq : p = q := (coordinateEquiv (show 3 ≤ m + 1 by omega) (outerAnchor z k)).injective
    (Subtype.ext he)
  subst q
  rfl

/-- The actual coordinate map takes values in the independently specified double-deletion domain. -/
def doubleInsertionMap {m : ℕ} (hm : 3 ≤ m) (z : Configuration (m + 1))
    (p : Fin m × Fin (m + 1) × Fin (m + 2) × Bool) :
    {v : Configuration (m + 1) //
      DoubleStar (z ((Fin.last m).castSucc)) (z (Fin.last (m + 1)))
        (delete (z ((Fin.last m).castSucc))
          (delete (z (Fin.last (m + 1))) (configurationCycle z))) v} :=
  ⟨doubleCoordinate z p, by
    rw [double_delete]
    exact doubleCoordinate_star hm z p⟩

/-- Every independent double-deletion configuration has exactly one actual two-gap coordinate. -/
theorem doubleInsertion_coordinates_bijective {m : ℕ} (hm : 3 ≤ m)
    (z : Configuration (m + 1)) : Function.Bijective (doubleInsertionMap hm z) := by
  constructor
  · intro p q he
    exact doubleCoordinate_injective hm z (congrArg Subtype.val he)
  · intro v
    have hv : DoubleStar (z ((Fin.last m).castSucc)) (z (Fin.last (m + 1)))
        (blockList m (by omega) z : Cycle (Fin (m + 2))) v.val := by
      simpa only [double_delete] using v.property
    obtain ⟨k, hk⟩ := outer_classification hm z v.val hv
    have hk' : Star ((outerAnchor z k) (Fin.last (m + 1))) (outerCircle z k) v.val := by
      simpa only [outer_last (by omega) z k] using hk
    let w : {v : Configuration (m + 1) //
      Star ((outerAnchor z k) (Fin.last (m + 1))) (outerCircle z k) v} := ⟨v.val, hk'⟩
    let p := (coordinateEquiv (show 3 ≤ m + 1 by omega) (outerAnchor z k)).symm w
    refine ⟨(k, p), Subtype.ext ?_⟩
    change coordinate (outerAnchor z k) p = v.val
    exact congrArg (fun u : {u : Configuration (m + 1) //
      Star ((outerAnchor z k) (Fin.last (m + 1))) (outerCircle z k) u} => u.val)
      ((coordinateEquiv (show 3 ≤ m + 1 by omega) (outerAnchor z k)).apply_symm_apply w)

/-- The proved actual coordinate map, packaged as an equivalence for transport. -/
noncomputable def doubleInsertionCoordinateEquiv {m : ℕ} (hm : 3 ≤ m)
    (z : Configuration (m + 1)) :
    (Fin m × Fin (m + 1) × Fin (m + 2) × Bool) ≃
      {v : Configuration (m + 1) //
        DoubleStar (z ((Fin.last m).castSucc)) (z (Fin.last (m + 1)))
          (delete (z ((Fin.last m).castSucc))
            (delete (z (Fin.last (m + 1))) (configurationCycle z))) v} :=
  Equiv.ofBijective (doubleInsertionMap hm z) (doubleInsertion_coordinates_bijective hm z)

#print axioms doubleInsertion_coordinates_bijective
#print axioms doubleInsertionCoordinateEquiv

end D5.S3.Combinatorics.Graph.PrefixReversalDoubleInsertionCoordinates
