/- GID: D5/S3/Combinatorics/Graph/PrefixReversalZeroStarComplement
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversalZeroStarComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: Native zero-star complements exhaust the independently defined insertion domain. -/

import D5.S0.CayleyGrowth.PrefixReversalTripleOddNonGeneration
import D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement

open PrefixReversalTripleOddNonGeneration
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open Fin.NatCast

/-- A configuration assigns every label to exactly one position. -/
abbrev Configuration (m : ℕ) := Equiv.Perm (Fin (m + 1))

/-- The actual circular tuple of a configuration, modulo oriented rotation only. -/
def configurationCycle {m : ℕ} (v : Configuration m) : Cycle (Fin (m + 1)) :=
  (List.ofFn v : Cycle (Fin (m + 1)))

/-- The insertion star is specified by its deletion residual, independently of any walk. -/
def Star {m : ℕ} (t : Fin (m + 1)) (W : Cycle (Fin (m + 1)))
    (v : Configuration m) : Prop :=
  delete t (configurationCycle v) = W ∨
    delete t (configurationCycle v) = W.reverse

/-- The three literal prefix reversals acting on positions. -/
def a (m : ℕ) : Configuration m := prefixReversal (m + 1) le_rfl

def b (m : ℕ) : Configuration m := prefixReversal m (by omega)

def c (m : ℕ) : Configuration m := prefixReversal (m - 1) (by omega)

private theorem a_apply {m : ℕ} (i : Fin (m + 1)) :
    a m i = i.rev := by
  apply Fin.ext
  simp [a, prefixReversal, reverseIndex, i.isLt, Fin.rev]

private theorem b_apply {m : ℕ} (i : Fin (m + 1)) :
    (b m i).val = if i.val < m then m - 1 - i.val else i.val := by
  by_cases hi : i.val < m <;> simp [b, prefixReversal, reverseIndex, hi]

private theorem c_apply {m : ℕ} (i : Fin (m + 1)) :
    (c m i).val = if i.val < m - 1 then m - 2 - i.val else i.val := by
  by_cases hi : i.val < m - 1 <;>
    simp [c, prefixReversal, reverseIndex, hi] <;> omega

private theorem ab_eq_rotate (m : ℕ) : a m * b m = finRotate (m + 1) := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [Equiv.Perm.mul_apply, a_apply]
  simp only [Fin.val_rev, b_apply]
  rw [coe_finRotate]
  by_cases hi : i.val < m
  · have hn : i ≠ Fin.last m := by intro h; subst i; simp at hi
    simp [hi, hn, Fin.val_last]
    omega
  · have he : i = Fin.last m := Fin.ext (by simpa using (show i.val = m by omega))
    subst i
    simp

private theorem bc_apply {m : ℕ} (hm : 2 ≤ m) (i : Fin (m + 1)) :
    (b m * c m) i =
      if hi : i.val < m then
        (⟨(i.val + 1) % m, (Nat.mod_lt _ (by omega)).trans_le (by omega)⟩ :
          Fin (m + 1))
      else i := by
  apply Fin.ext
  rw [Equiv.Perm.mul_apply]
  simp only [b_apply, c_apply]
  by_cases hsmall : i.val < m - 1
  · have hnext : i.val + 1 < m := by omega
    simp [hsmall, show m - 2 - i.val < m by omega,
      show i.val < m by omega, Nat.mod_eq_of_lt hnext]
    omega
  · by_cases hmid : i.val < m
    · have he : i.val = m - 1 := by omega
      simp [hsmall, hmid, he, show 0 < m by omega,
        Nat.sub_add_cancel (show 1 ≤ m by omega)]
    · simp [hsmall, hmid]

private theorem full_reverse_list {m : ℕ} (v : Configuration m) :
    List.ofFn (v * a m) = (List.ofFn v).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn,
      Equiv.Perm.mul_apply, a_apply]
    congr 1
    apply Fin.ext
    simp [Fin.val_rev]

private theorem rotate_list {m : ℕ} (v : Configuration m) :
    List.ofFn (v * finRotate (m + 1)) = (List.ofFn v).rotate 1 := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_rotate, List.length_ofFn,
      Equiv.Perm.mul_apply]
    congr 1
    apply Fin.ext
    simp [finRotate_apply, Fin.add_def]

private theorem rotate_pow_list {m : ℕ} (v : Configuration m) (k : ℕ) :
    List.ofFn (v * finRotate (m + 1) ^ k) = (List.ofFn v).rotate k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, rotate_list, ih, List.rotate_rotate]

/-- The residual linear tuple at a configuration with the marked label last. -/
def residualList {m : ℕ} (z : Configuration m) : List (Fin (m + 1)) :=
  List.ofFn (fun i : Fin m => z i.castSucc)

private theorem residual_nodup {m : ℕ} (z : Configuration m) :
    (residualList z).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  exact (Fin.castSucc_injective m) (z.injective h)

private theorem residual_delete {m : ℕ} (z : Configuration m) :
    delete (z (Fin.last m)) (configurationCycle z) =
      (residualList z : Cycle (Fin (m + 1))) := by
  change ((List.ofFn z).filter (fun y => decide (y ≠ z (Fin.last m))) :
    Cycle (Fin (m + 1))) = _
  rw [List.ofFn_succ', List.concat_eq_append, List.filter_append]
  have hf : (residualList z).filter (fun y => decide (y ≠ z (Fin.last m))) =
      residualList z := by
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp only [decide_eq_true_eq, ne_eq, z.injective.eq_iff]
    exact Fin.castSucc_ne_last i
  simpa [residualList] using congrArg
    (fun l : List (Fin (m + 1)) => (l : Cycle (Fin (m + 1)))) hf

private theorem delete_rotate {m : ℕ} (v : Configuration m) (t : Fin (m + 1))
    (k : ℕ) :
    delete t (configurationCycle (v * finRotate (m + 1) ^ k)) =
      delete t (configurationCycle v) := by
  apply congrArg (delete t)
  apply Cycle.coe_eq_coe.mpr
  rw [rotate_pow_list]
  exact List.IsRotated.symm ⟨k, rfl⟩

private theorem delete_reverse {m : ℕ} (v : Configuration m) (t : Fin (m + 1)) :
    delete t (configurationCycle (v * a m)) =
      (delete t (configurationCycle v)).reverse := by
  change ((List.ofFn (v * a m)).filter (fun y => decide (y ≠ t)) :
    Cycle (Fin (m + 1))) = _
  rw [full_reverse_list, List.filter_reverse]
  rfl

private theorem residual_not_reverse {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    (residualList z : Cycle (Fin (m + 1))) ≠
      (residualList z : Cycle (Fin (m + 1))).reverse := by
  intro he
  have hn : (residualList z : Cycle (Fin (m + 1))).Nodup :=
    Cycle.nodup_coe_iff.mpr (residual_nodup z)
  have hw : DeleteWalk [] (residualList z : Cycle (Fin (m + 1)))
      (residualList z : Cycle (Fin (m + 1))).reverse := by
    rw [← he]
    exact DeleteWalk.nil _
  have hb := negative_walk_support_bound hw hn
  change (residualList z).toFinset.card ≤ 2 at hb
  rw [List.toFinset_card_of_nodup (residual_nodup z)] at hb
  simp only [residualList, List.length_ofFn] at hb
  omega

private theorem bc_last {m : ℕ} (hm : 2 ≤ m) :
    (b m * c m) (Fin.last m) = Fin.last m := by
  rw [bc_apply hm]
  simp

private theorem prefix_bc_list {m : ℕ} (hm : 2 ≤ m) (v : Configuration m) :
    residualList (v * (b m * c m)) = (residualList v).rotate 1 := by
  apply List.ext_getElem
  · simp [residualList]
  · intro i hi hj
    simp only [residualList, List.getElem_ofFn, List.getElem_rotate, List.length_ofFn,
      Equiv.Perm.mul_apply]
    change v ((b m * c m) (⟨i, by simpa [residualList] using hi⟩ : Fin m).castSucc) = _
    rw [bc_apply hm]
    simp only [Fin.val_castSucc, dif_pos (show i < m by simpa [residualList] using hi)]
    congr 1

/-- Consecutive marked-label insertion gaps, based at an actual tuple. -/
def gapAnchor {m : ℕ} (z : Configuration m) (k : Fin m) : Configuration m :=
  z * (b m * c m) ^ k.val

private theorem anchor_last {m : ℕ} (hm : 2 ≤ m) (z : Configuration m) (k : Fin m) :
    gapAnchor z k (Fin.last m) = z (Fin.last m) := by
  have hp (r : ℕ) : ((b m * c m) ^ r) (Fin.last m) = Fin.last m := by
    induction r with
    | zero => simp
    | succ r ih => simp [pow_succ, Equiv.Perm.mul_apply, bc_last hm, ih]
  simp [gapAnchor, Equiv.Perm.mul_apply, hp]

private theorem anchor_residual {m : ℕ} (hm : 2 ≤ m) (z : Configuration m) (k : Fin m) :
    residualList (gapAnchor z k) = (residualList z).rotate k.val := by
  have hp (r : ℕ) : residualList (z * (b m * c m) ^ r) =
      (residualList z).rotate r := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, ← mul_assoc, prefix_bc_list hm, ih, List.rotate_rotate]
  exact hp k.val

private theorem anchor_delete {m : ℕ} (hm : 2 ≤ m) (z : Configuration m) (k : Fin m) :
    delete (z (Fin.last m)) (configurationCycle (gapAnchor z k)) =
      (residualList z : Cycle (Fin (m + 1))) := by
  rw [← anchor_last hm z k, residual_delete, anchor_residual hm]
  exact Cycle.coe_eq_coe.mpr (List.IsRotated.symm ⟨k.val, rfl⟩)

/-- A native-circle coordinate records the gap, cyclic position, and reflection direction. -/
def coordinate {m : ℕ} (z : Configuration m)
    (p : Fin m × Fin (m + 1) × Bool) : Configuration m :=
  gapAnchor z p.1 * finCycle p.2.1 *
    (if p.2.2 then a m else 1)

private theorem rotate_pow_eq_cycle {m : ℕ} (k : ℕ) :
    finRotate (m + 1) ^ k = finCycle (k : Fin (m + 1)) := by
  induction k with
  | zero =>
    apply Equiv.ext
    intro i
    simp
  | succ k ih =>
    apply Equiv.ext
    intro i
    simp [pow_succ, Equiv.Perm.mul_apply, ih, finRotate_apply]
    abel

private theorem delete_finCycle {m : ℕ} (v : Configuration m) (t : Fin (m + 1))
    (r : Fin (m + 1)) :
    delete t (configurationCycle (v * finCycle r)) = delete t (configurationCycle v) := by
  have he : finRotate (m + 1) ^ r.val = finCycle r := by
    simpa using rotate_pow_eq_cycle (m := m) r.val
  rw [← he, delete_rotate]

private theorem coordinate_star {m : ℕ} (hm : 2 ≤ m) (z : Configuration m)
    (p : Fin m × Fin (m + 1) × Bool) :
    Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) (coordinate z p) := by
  rcases p with ⟨k, r, s⟩
  cases s
  · left
    simp only [coordinate, Bool.false_eq_true, ↓reduceIte, mul_one]
    rw [delete_finCycle, anchor_delete hm]
  · right
    simp only [coordinate, ↓reduceIte]
    rw [delete_reverse, delete_finCycle, anchor_delete hm]

private theorem coordinate_residual {m : ℕ} (hm : 2 ≤ m) (z : Configuration m)
    (p : Fin m × Fin (m + 1) × Bool) :
    delete (z (Fin.last m)) (configurationCycle (coordinate z p)) =
      if p.2.2 then (residualList z : Cycle (Fin (m + 1))).reverse else
        (residualList z : Cycle (Fin (m + 1))) := by
  rcases p with ⟨k, r, s⟩
  cases s <;> simp only [coordinate, Bool.false_eq_true, ↓reduceIte, mul_one]
  · rw [delete_finCycle, anchor_delete hm]
  · rw [delete_reverse, delete_finCycle, anchor_delete hm]

private theorem anchor_injective {m : ℕ} (hm : 2 ≤ m) (z : Configuration m) :
    Function.Injective (gapAnchor z) := by
  intro k l he
  have hr := congrArg residualList he
  rw [anchor_residual hm, anchor_residual hm] at hr
  have hn : residualList z ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp [residualList] at hl
    omega
  have hv := (residual_nodup z).rotate_congr hn k.val l.val hr
  simp only [residualList, List.length_ofFn, Nat.mod_eq_of_lt k.isLt,
    Nat.mod_eq_of_lt l.isLt] at hv
  exact Fin.ext hv

private theorem coordinate_injective {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    Function.Injective (coordinate z) := by
  rintro ⟨k, r, s⟩ ⟨l, u, q⟩ he
  have hres := congrArg (fun v => delete (z (Fin.last m)) (configurationCycle v)) he
  rw [coordinate_residual (by omega), coordinate_residual (by omega)] at hres
  have hs : s = q := by
    cases s <;> cases q <;> simp only [↓reduceIte] at hres ⊢
    · exact (residual_not_reverse hm z hres).elim
    · exact (residual_not_reverse hm z hres.symm).elim
  subst q
  have he' : gapAnchor z k * finCycle r = gapAnchor z l * finCycle u :=
    mul_right_cancel he
  have hlast := anchor_last (by omega) z l
  have hv := congrArg (fun v : Configuration m => v (Fin.last m - r)) he'
  simp only [Equiv.Perm.mul_apply, finCycle_apply, sub_add_cancel] at hv
  rw [anchor_last (by omega)] at hv
  have hi : Fin.last m - r + u = Fin.last m :=
    (gapAnchor z l).injective (hv.symm.trans hlast.symm)
  have hu : r = u := by
    have hi' : u = r := by simpa only [sub_add_eq_add_sub, sub_eq_iff_eq_add,
      add_assoc, add_right_inj] using hi
    exact hi'.symm
  subst u
  have hk := anchor_injective (by omega) z (mul_right_cancel he')
  subst l
  rfl

private theorem cycle_mul {m : ℕ} (r s : Fin (m + 1)) :
    finCycle r * finCycle s = finCycle (r + s) := by
  apply Equiv.ext
  intro i
  simp only [Equiv.Perm.mul_apply, finCycle_apply]
  abel

private theorem cycle_zero (m : ℕ) : finCycle (0 : Fin (m + 1)) = 1 := by
  apply Equiv.ext
  intro i
  simp

private theorem a_sq (m : ℕ) : a m * a m = 1 := by
  apply Equiv.ext
  intro i
  simp [Equiv.Perm.mul_apply, a_apply]

private theorem b_sq (m : ℕ) : b m * b m = 1 := by
  apply Equiv.ext
  intro i
  exact reverseIndex_involutive (L := m) (by omega) i

private theorem a_cycle {m : ℕ} (r : Fin (m + 1)) :
    a m * finCycle r = finCycle (-r) * a m := by
  apply Equiv.ext
  intro i
  simp [Equiv.Perm.mul_apply, a_apply, Fin.rev_add, sub_eq_add_neg]

private theorem b_eq_cycle_a (m : ℕ) :
    b m = finCycle (-1 : Fin (m + 1)) * a m := by
  have hr : finRotate (m + 1) = finCycle (1 : Fin (m + 1)) := by
    simpa using rotate_pow_eq_cycle (m := m) 1
  calc
    b m = a m * (a m * b m) := by rw [← mul_assoc, a_sq, one_mul]
    _ = a m * finCycle (1 : Fin (m + 1)) := by rw [ab_eq_rotate, hr]
    _ = finCycle (-1 : Fin (m + 1)) * a m := a_cycle _

private theorem b_last (m : ℕ) : b m (Fin.last m) = Fin.last m := by
  apply Fin.ext
  simp [b_apply]

private theorem residual_b {m : ℕ} (v : Configuration m) :
    residualList (v * b m) = (residualList v).reverse := by
  apply List.ext_getElem
  · simp [residualList]
  · intro i hi hj
    simp only [residualList, List.getElem_ofFn, List.getElem_reverse, List.length_ofFn,
      Equiv.Perm.mul_apply]
    apply congrArg v
    apply Fin.ext
    rw [b_apply]
    simp only [Fin.val_castSucc, if_pos (show i < m by simpa [residualList] using hi)]

private theorem configuration_eq_of_residual_last {m : ℕ} {u v : Configuration m}
    (hr : residualList u = residualList v) (hl : u (Fin.last m) = v (Fin.last m)) :
    u = v := by
  have hf : (fun i : Fin m => u i.castSucc) = (fun i : Fin m => v i.castSucc) :=
    List.ofFn_injective hr
  apply Equiv.ext
  intro i
  exact Fin.lastCases hl (fun j => congrFun hf j) i

private theorem positive_last_anchor {m : ℕ} (hm : 2 ≤ m) (z w : Configuration m)
    (hl : w (Fin.last m) = z (Fin.last m))
    (hd : delete (z (Fin.last m)) (configurationCycle w) =
      (residualList z : Cycle (Fin (m + 1)))) :
    ∃ k : Fin m, w = gapAnchor z k := by
  rw [← hl, residual_delete] at hd
  obtain ⟨k, hk⟩ := (Cycle.coe_eq_coe.mp hd).symm
  let j : Fin m := ⟨k % m, Nat.mod_lt _ (by omega)⟩
  refine ⟨j, configuration_eq_of_residual_last ?_ ?_⟩
  · rw [anchor_residual hm]
    have he := (List.rotate_mod (residualList z) k).trans hk
    simpa only [residualList, List.length_ofFn, j] using he.symm
  · rw [anchor_last hm]
    exact hl

private theorem coordinate_surjective {m : ℕ} (hm : 3 ≤ m) (z v : Configuration m)
    (hv : Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v) :
    ∃ p : Fin m × Fin (m + 1) × Bool, coordinate z p = v := by
  let d : Fin (m + 1) := v.symm (z (Fin.last m)) + 1
  let w : Configuration m := v * finCycle d
  have hwlast : w (Fin.last m) = z (Fin.last m) := by
    change v (Fin.last m + d) = z (Fin.last m)
    have he : Fin.last m + d = v.symm (z (Fin.last m)) := by
      dsimp [d]
      have ht : Fin.last m + (1 : Fin (m + 1)) = 0 := by
        rw [← Fin.neg_last m]
        exact add_neg_cancel _
      calc
        Fin.last m + (v.symm (z (Fin.last m)) + 1) =
            (Fin.last m + 1) + v.symm (z (Fin.last m)) := by abel
        _ = v.symm (z (Fin.last m)) := by rw [ht, zero_add]
    rw [he, v.apply_symm_apply]
  have hwdelete : delete (z (Fin.last m)) (configurationCycle w) =
      delete (z (Fin.last m)) (configurationCycle v) := delete_finCycle v _ d
  have hwrecover : w * finCycle (-d) = v := by
    dsimp [w]
    rw [mul_assoc, cycle_mul, add_neg_cancel, cycle_zero, mul_one]
  rcases hv with hv | hv
  · obtain ⟨k, hk⟩ := positive_last_anchor (by omega) z w hwlast (hwdelete.trans hv)
    refine ⟨⟨k, -d, false⟩, ?_⟩
    simpa only [coordinate, Bool.false_eq_true, ↓reduceIte, mul_one, hk] using hwrecover
  · have hwb : (w * b m) (Fin.last m) = z (Fin.last m) := by
      rw [Equiv.Perm.mul_apply, b_last, hwlast]
    have hwbd : delete (z (Fin.last m)) (configurationCycle (w * b m)) =
        (residualList z : Cycle (Fin (m + 1))) := by
      rw [← hwb, residual_delete, residual_b]
      have hwd : (residualList w : Cycle (Fin (m + 1))) =
          (residualList z : Cycle (Fin (m + 1))).reverse := by
        rw [← residual_delete, hwlast]
        exact hwdelete.trans hv
      rw [← Cycle.reverse_coe, hwd, Cycle.reverse_reverse]
    obtain ⟨k, hk⟩ := positive_last_anchor (by omega) z (w * b m) hwb hwbd
    have hkw : gapAnchor z k * b m = w := by
      rw [← hk, mul_assoc, b_sq, mul_one]
    refine ⟨⟨k, -1 + d, true⟩, ?_⟩
    have hcb : b m * finCycle (-d) = finCycle (-1 + d) * a m := by
      rw [b_eq_cycle_a, mul_assoc, a_cycle, neg_neg, ← mul_assoc, cycle_mul]
    calc
      coordinate z (k, -1 + d, true) =
          gapAnchor z k * (finCycle (-1 + d) * a m) := by simp [coordinate, mul_assoc]
      _ = (gapAnchor z k * b m) * finCycle (-d) := by rw [← hcb, mul_assoc]
      _ = v := by rw [hkw, hwrecover]

/-- The explicit gap and native-circle coordinates form a bijection onto the deletion star. -/
noncomputable def coordinateEquiv {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    (Fin m × Fin (m + 1) × Bool) ≃
      {v : Configuration m //
        Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v} :=
  Equiv.ofBijective
    (fun p => ⟨coordinate z p, coordinate_star (by omega) z p⟩)
    ⟨fun p q he => coordinate_injective hm z (congrArg Subtype.val he),
      fun v => by
        obtain ⟨p, hp⟩ := coordinate_surjective hm z v.val v.property
        exact ⟨p, Subtype.ext hp⟩⟩

/-- The zero-layer switch selects a-edges throughout, b-edges off the marked last position,
and c-edges at that position, inside the native Cayley graph. -/
def factor (m : ℕ) (t : Fin (m + 1)) : SimpleGraph (Configuration m) :=
  SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) ⊓
    SimpleGraph.fromRel (fun u v =>
      v = u * a m ∨
        (u (Fin.last m) ≠ t ∧ v = u * b m) ∨
        (u (Fin.last m) = t ∧ v = u * c m))

/-- The factor restricted to a residual bracelet, retaining its independently specified vertices. -/
def starFactor {m : ℕ} (t : Fin (m + 1)) (W : Cycle (Fin (m + 1))) :
    SimpleGraph {v : Configuration m // Star t W v} :=
  (factor m t).induce {v | Star t W v}

/-- The literal alternating word (ab)^k a. -/
def uWord (m : ℕ) : ℕ → List (Configuration m)
  | 0 => [a m]
  | k + 1 => a m :: b m :: uWord m k

/-- The literal complementary word around a complete zero star. -/
def zWord (m j : ℕ) : List (Configuration m) :=
  uWord m j ++ (List.replicate (m - 1) (c m :: uWord m m)).flatten ++
    c m :: uWord m (m - j - 1)

private theorem uWord_length (m k : ℕ) : (uWord m k).length = 2 * k + 1 := by
  induction k with
  | zero => simp [uWord]
  | succ k ih => simp [uWord, ih]; omega

private theorem uWord_product (m k : ℕ) :
    (uWord m k).prod = finRotate (m + 1) ^ k * a m := by
  induction k with
  | zero => simp [uWord]
  | succ k ih =>
    simp only [uWord, List.prod_cons, ih]
    rw [← mul_assoc, ab_eq_rotate, ← mul_assoc, ← pow_succ']

private theorem uWord_snoc (m k : ℕ) :
    uWord m (k + 1) = uWord m k ++ [b m, a m] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change a m :: b m :: uWord m (k + 1) =
      a m :: b m :: (uWord m k ++ [b m, a m])
    rw [ih]

private theorem uWord_reverse (m k : ℕ) : (uWord m k).reverse = uWord m k := by
  induction k with
  | zero => simp [uWord]
  | succ k ih =>
    simp only [uWord, List.reverse_cons, List.reverse_cons, ih]
    rw [List.append_assoc]
    exact (uWord_snoc m k).symm

private theorem uWord_split (m p q : ℕ) :
    uWord m (p + q + 1) = uWord m p ++ b m :: uWord m q := by
  induction p with
  | zero => simp [uWord]
  | succ p ih =>
    rw [show p + 1 + q + 1 = (p + q + 1) + 1 by omega, uWord, ih]
    simp only [uWord, List.cons_append]

private theorem uWord_ofFn (m k : ℕ) : uWord m k =
    List.ofFn (fun i : Fin (2 * k + 1) => if i.val % 2 = 0 then a m else b m) := by
  induction k with
  | zero => simp [uWord, List.ofFn_succ]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega]
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [Fin.val_zero, Nat.zero_mod, ↓reduceIte,
      Fin.val_succ, Nat.one_mod, Nat.one_ne_zero]
    rw [uWord, ih]
    congr 2
    congr 1
    funext i
    have hp : (i.val + 1 + 1) % 2 = i.val % 2 := by omega
    simp only [hp]

/-- Native ranks put the two reflection directions consecutively within each gap. -/
def rankEquiv (m : ℕ) : Fin (m * ((m + 1) * 2)) ≃
    (Fin m × Fin (m + 1) × Bool) :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin m))
      (finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)))

/-- The actual configuration at a native rank of the (Hc)^m circle. -/
def nativeVertex {m : ℕ} (z : Configuration m) (i : Fin (m * ((m + 1) * 2))) :
    Configuration m := coordinate z (rankEquiv m i)

private theorem nativeVertex_injective {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    Function.Injective (nativeVertex z) :=
  (coordinate_injective hm z).comp (rankEquiv m).injective

private theorem nativeVertex_surjective {m : ℕ} (hm : 3 ≤ m) (z v : Configuration m)
    (hv : Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v) :
    ∃ i : Fin (m * ((m + 1) * 2)), nativeVertex z i = v := by
  obtain ⟨p, hp⟩ := coordinate_surjective hm z v hv
  exact ⟨(rankEquiv m).symm p, by simpa [nativeVertex] using hp⟩

private theorem anchor_next {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) (k : Fin m) :
    gapAnchor z ⟨(k.val + 1) % m, Nat.mod_lt _ (by omega)⟩ =
      gapAnchor z k * (b m * c m) := by
  apply configuration_eq_of_residual_last
  · rw [anchor_residual (by omega), prefix_bc_list (by omega),
      anchor_residual (by omega), List.rotate_rotate]
    simpa only [residualList, List.length_ofFn] using
      List.rotate_mod (residualList z) (k.val + 1)
  · change gapAnchor z ⟨(k.val + 1) % m, _⟩ (Fin.last m) =
      gapAnchor z k ((b m * c m) (Fin.last m))
    rw [bc_last (show 2 ≤ m by omega), anchor_last (show 2 ≤ m by omega),
      anchor_last (show 2 ≤ m by omega)]

private theorem coordinate_a {m : ℕ} (z : Configuration m) (k : Fin m)
    (r : Fin (m + 1)) :
    coordinate z (k, r, false) * a m = coordinate z (k, r, true) := by
  simp [coordinate]

private theorem coordinate_b {m : ℕ} (z : Configuration m) (k : Fin m)
    (r : Fin (m + 1)) :
    coordinate z (k, r, true) * b m = coordinate z (k, r + 1, false) := by
  have hr : a m * b m = finCycle (1 : Fin (m + 1)) := by
    rw [ab_eq_rotate]
    simpa using rotate_pow_eq_cycle (m := m) 1
  simp only [coordinate, Bool.false_eq_true, ↓reduceIte, mul_one]
  rw [mul_assoc, hr, mul_assoc, cycle_mul]

private theorem coordinate_c {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) (k : Fin m) :
    coordinate z (k, Fin.last m, true) * c m =
      coordinate z (⟨(k.val + 1) % m, Nat.mod_lt _ (by omega)⟩, 0, false) := by
  have he : (-1 : Fin (m + 1)) = Fin.last m := by
    rw [← Fin.neg_last m, neg_neg]
  simp only [coordinate, Bool.false_eq_true, ↓reduceIte, mul_one, cycle_zero]
  rw [anchor_next hm z k, b_eq_cycle_a, he]
  simp only [mul_assoc]

private theorem coordinate_true_last {m : ℕ} (hm : 3 ≤ m) (z : Configuration m)
    (k : Fin m) (r : Fin (m + 1)) :
    coordinate z (k, r, true) (Fin.last m) = z (Fin.last m) ↔ r = Fin.last m := by
  simp only [coordinate, ↓reduceIte, Equiv.Perm.mul_apply, a_apply,
    Fin.rev_last, finCycle_apply, zero_add]
  rw [← anchor_last (by omega) z k, (gapAnchor z k).injective.eq_iff]

private theorem native_size_three {m : ℕ} (hm : 3 ≤ m) :
    3 ≤ m * ((m + 1) * 2) := by nlinarith

private theorem rank_val {m : ℕ} (k : Fin m) (r : Fin (m + 1)) (s : Bool) :
    ((rankEquiv m).symm (k, r, s)).val =
      (if s then 1 else 0) + 2 * r.val + ((m + 1) * 2) * k.val := by
  cases s <;> simp [rankEquiv, finProdFinEquiv, finTwoEquiv, Nat.mul_comm]

private theorem rank_next_false {m : ℕ} [NeZero (m * ((m + 1) * 2))]
    (hm : 3 ≤ m) (k : Fin m)
    (r : Fin (m + 1)) :
    (rankEquiv m).symm (k, r, false) + 1 = (rankEquiv m).symm (k, r, true) := by
  have hN := native_size_three hm
  have he : ((rankEquiv m).symm (k, r, false)).val + 1 =
      ((rankEquiv m).symm (k, r, true)).val := by
    simp only [rank_val, Bool.false_eq_true, ↓reduceIte]
    omega
  apply Fin.ext
  change (((rankEquiv m).symm (k, r, false)).val +
    1 % (m * ((m + 1) * 2))) % (m * ((m + 1) * 2)) = _
  rw [Nat.mod_eq_of_lt (show 1 < m * ((m + 1) * 2) by omega), he,
    Nat.mod_eq_of_lt ((rankEquiv m).symm (k, r, true)).isLt]

private theorem rank_next_true {m : ℕ} [NeZero (m * ((m + 1) * 2))]
    (hm : 3 ≤ m) (k : Fin m)
    (r : Fin (m + 1)) (hr : r.val < m) :
    (rankEquiv m).symm (k, r, true) + 1 = (rankEquiv m).symm (k, r + 1, false) := by
  have hN := native_size_three hm
  have he : ((rankEquiv m).symm (k, r, true)).val + 1 =
      ((rankEquiv m).symm (k, r + 1, false)).val := by
    simp only [rank_val, Bool.false_eq_true, ↓reduceIte,
      Fin.val_add_one_of_lt hr]
    omega
  apply Fin.ext
  change (((rankEquiv m).symm (k, r, true)).val +
    1 % (m * ((m + 1) * 2))) % (m * ((m + 1) * 2)) = _
  rw [Nat.mod_eq_of_lt (show 1 < m * ((m + 1) * 2) by omega), he,
    Nat.mod_eq_of_lt ((rankEquiv m).symm (k, r + 1, false)).isLt]

private theorem rank_next_last {m : ℕ} [NeZero (m * ((m + 1) * 2))]
    (hm : 3 ≤ m) (k : Fin m) :
    (rankEquiv m).symm (k, Fin.last m, true) + 1 =
      (rankEquiv m).symm
        (⟨(k.val + 1) % m, Nat.mod_lt _ (by omega)⟩, 0, false) := by
  have hN := native_size_three hm
  apply Fin.ext
  change (((rankEquiv m).symm (k, Fin.last m, true)).val +
    1 % (m * ((m + 1) * 2))) % (m * ((m + 1) * 2)) = _
  rw [Nat.mod_eq_of_lt (show 1 < m * ((m + 1) * 2) by omega)]
  simp only [rank_val, Bool.false_eq_true, ↓reduceIte, Fin.val_last, Fin.val_zero, mul_zero, add_zero,
    zero_add]
  rw [show 1 + 2 * m + ((m + 1) * 2) * k.val + 1 =
      ((m + 1) * 2) * (k.val + 1) by ring,
    show m * ((m + 1) * 2) = ((m + 1) * 2) * m by ring,
    Nat.mul_mod_mul_left]

/-- The edge leaving a native rank; the final edge in each H-block is its c-connector. -/
def nativeGenerator {m : ℕ} (i : Fin (m * ((m + 1) * 2))) : Configuration m :=
  let p := rankEquiv m i
  if p.2.2 then (if p.2.1 = Fin.last m then c m else b m) else a m

private theorem native_step {m : ℕ} [NeZero (m * ((m + 1) * 2))]
    (hm : 3 ≤ m) (z : Configuration m)
    (i : Fin (m * ((m + 1) * 2))) :
    nativeVertex z i * nativeGenerator i = nativeVertex z (i + 1) := by
  let p := rankEquiv m i
  have hi : i = (rankEquiv m).symm p := ((rankEquiv m).symm_apply_apply i).symm
  rcases p with ⟨k, r, s⟩
  rw [hi]
  cases s
  · rw [rank_next_false hm]
    simpa [nativeVertex, nativeGenerator] using coordinate_a z k r
  · by_cases hr : r = Fin.last m
    · subst r
      rw [rank_next_last hm]
      simpa [nativeVertex, nativeGenerator] using coordinate_c hm z k
    · have hv : r.val < m := by
        have hn : r.val ≠ m := by simpa only [Fin.ext_iff, Fin.val_last] using hr
        omega
      rw [rank_next_true hm k r hv]
      simpa [nativeVertex, nativeGenerator, hr] using coordinate_b z k r

private theorem c_sq (m : ℕ) : c m * c m = 1 := by
  apply Equiv.ext
  intro i
  exact reverseIndex_involutive (L := m - 1) (by omega) i

private theorem nativeGenerator_sq {m : ℕ} (i : Fin (m * ((m + 1) * 2))) :
    nativeGenerator i * nativeGenerator i = 1 := by
  dsimp [nativeGenerator]
  split
  · split
    · exact c_sq m
    · exact b_sq m
  · exact a_sq m

private theorem factor_direction {m : ℕ} {t : Fin (m + 1)} {u v : Configuration m}
    (hn : u ≠ v)
    (he : v = u * a m ∨ (u (Fin.last m) ≠ t ∧ v = u * b m) ∨
      (u (Fin.last m) = t ∧ v = u * c m)) : (factor m t).Adj u v := by
  constructor
  · rw [SimpleGraph.mulCayley_adj']
    refine ⟨hn, ?_⟩
    rcases he with ha | hb | hc
    · exact ⟨a m, by simp, Or.inl ha.symm⟩
    · exact ⟨b m, by simp, Or.inl hb.2.symm⟩
    · exact ⟨c m, by simp, Or.inl hc.2.symm⟩
  · exact ⟨hn, Or.inl he⟩

private theorem native_adj {m : ℕ} [NeZero (m * ((m + 1) * 2))]
    (hm : 3 ≤ m) (z : Configuration m)
    (i : Fin (m * ((m + 1) * 2))) :
    (factor m (z (Fin.last m))).Adj (nativeVertex z i) (nativeVertex z (i + 1)) := by
  have hN := native_size_three hm
  have hi : i ≠ i + 1 := by
    intro he
    have hone : (1 : Fin (m * ((m + 1) * 2))) = 0 := by
      exact add_left_cancel (show i + 1 = i + 0 by simpa using he.symm)
    have hv := congrArg Fin.val hone
    simp [Fin.val_one', Nat.mod_eq_of_lt (show 1 < m * ((m + 1) * 2) by omega)] at hv
  apply factor_direction ((nativeVertex_injective hm z).ne hi)
  rw [← native_step hm]
  let p := rankEquiv m i
  have hi2 : i = (rankEquiv m).symm p := ((rankEquiv m).symm_apply_apply i).symm
  rcases p with ⟨k, r, s⟩
  rw [hi2]
  simp only [nativeVertex, Equiv.apply_symm_apply]
  cases s
  · left
    simp [nativeGenerator]
  · by_cases hr : r = Fin.last m
    · right; right
      refine ⟨(coordinate_true_last hm z k r).mpr hr, ?_⟩
      simp [nativeGenerator, hr]
    · right; left
      refine ⟨fun he => hr ((coordinate_true_last hm z k r).mp he), ?_⟩
      simp [nativeGenerator, hr]

/-- The literal word (Hc)^m, before cutting an internal b-edge. -/
def cycleWord (m : ℕ) : List (Configuration m) :=
  (List.replicate m (uWord m m ++ [c m])).flatten

private def blockWord (m : ℕ) : List (Configuration m) :=
  List.ofFn (fun q : Fin ((m + 1) * 2) =>
    if q.val = 2 * m + 1 then c m else if q.val % 2 = 0 then a m else b m)

private theorem blockWord_eq (m : ℕ) : blockWord m = uWord m m ++ [c m] := by
  unfold blockWord
  rw [show (m + 1) * 2 = (2 * m + 1) + 1 by omega, List.ofFn_succ']
  have hf : (fun i : Fin (2 * m + 1) =>
      if i.castSucc.val = 2 * m + 1 then c m
      else if i.castSucc.val % 2 = 0 then a m else b m) =
      (fun i : Fin (2 * m + 1) => if i.val % 2 = 0 then a m else b m) := by
    funext i
    simp only [Fin.val_castSucc, if_neg (show i.val ≠ 2 * m + 1 by omega)]
  simp only [hf, Fin.val_last, ↓reduceIte, List.concat_eq_append]
  rw [← uWord_ofFn]

private theorem generator_finProd {m : ℕ} (k : Fin m) (q : Fin ((m + 1) * 2)) :
    nativeGenerator (finProdFinEquiv (k, q)) =
      if q.val = 2 * m + 1 then c m else if q.val % 2 = 0 then a m else b m := by
  simp only [nativeGenerator, rankEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  change (if finTwoEquiv q.modNat then
    if q.divNat = Fin.last m then c m else b m else a m) = _
  have hb : finTwoEquiv q.modNat = true ↔ q.val % 2 = 1 := by
    change (q.modNat == (1 : Fin 2)) = true ↔ _
    simp [beq_iff_eq, Fin.ext_iff, Fin.modNat]
  simp only [hb, Fin.ext_iff, Fin.divNat, Fin.val_last]
  split
  · rename_i hodd
    by_cases hlast : q.val / 2 = m
    · have he : q.val = 2 * m + 1 := by omega
      rw [if_pos hlast, if_pos he]
    · have he : q.val ≠ 2 * m + 1 := by omega
      have hn : q.val % 2 ≠ 0 := by omega
      rw [if_neg hlast, if_neg he, if_neg hn]
  · rename_i heven
    have hn : q.val % 2 = 0 := by omega
    have he : q.val ≠ 2 * m + 1 := by omega
    rw [if_neg he, if_pos hn]

private theorem rank_bound {m : ℕ} (k : Fin m) (q : Fin ((m + 1) * 2)) :
    k.val * ((m + 1) * 2) + q.val < m * ((m + 1) * 2) := by
  calc
    _ < k.val * ((m + 1) * 2) + ((m + 1) * 2) := Nat.add_lt_add_left q.isLt _
    _ = (k.val + 1) * ((m + 1) * 2) := by ring
    _ ≤ m * ((m + 1) * 2) := Nat.mul_le_mul_right _ k.isLt

private theorem cycleWord_ofFn (m : ℕ) : cycleWord m =
    List.ofFn (fun i : Fin (m * ((m + 1) * 2)) => nativeGenerator i) := by
  rw [List.ofFn_mul]
  have hf : (fun k : Fin m =>
      List.ofFn (fun q : Fin ((m + 1) * 2) =>
        nativeGenerator ⟨k.val * ((m + 1) * 2) + q.val, rank_bound k q⟩)) =
      (fun _ : Fin m => blockWord m) := by
    funext k
    congr 1
    funext q
    have he : (⟨k.val * ((m + 1) * 2) + q.val, rank_bound k q⟩ :
        Fin (m * ((m + 1) * 2))) = finProdFinEquiv (k, q) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
    rw [he, generator_finProd]
  rw [hf, List.ofFn_const]
  simp only [cycleWord, blockWord_eq]

private theorem cycleWord_length (m : ℕ) : (cycleWord m).length = m * ((m + 1) * 2) := by
  rw [cycleWord_ofFn]
  simp

private theorem complement_word (m : ℕ) (hm : 3 ≤ m) (j : Fin m) :
    ((cycleWord m).rotate (2 * j.val + 1)).tail.reverse = zWord m j.val := by
  have hsplit : uWord m m = uWord m j.val ++ b m :: uWord m (m - j.val - 1) := by
    have hn : j.val + (m - j.val - 1) + 1 = m := by omega
    simpa only [hn] using uWord_split m j.val (m - j.val - 1)
  have hrep : List.replicate m (uWord m m ++ [c m]) =
      (uWord m m ++ [c m]) :: List.replicate (m - 1) (uWord m m ++ [c m]) := by
    calc
      _ = List.replicate ((m - 1) + 1) (uWord m m ++ [c m]) := by congr 1; omega
      _ = _ := List.replicate_succ
  have hS : cycleWord m = uWord m j.val ++ b m ::
      (uWord m (m - j.val - 1) ++ [c m] ++
       (List.replicate (m - 1) (uWord m m ++ [c m])).flatten) := by
    rw [cycleWord, hrep, List.flatten_cons]
    simp only [hsplit, List.cons_append, List.append_assoc]
  rw [hS, ← uWord_length m j.val, List.rotate_append_length_eq]
  simp only [List.cons_append, List.tail_cons, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.reverse_flatten,
    List.map_replicate, List.reverse_replicate, uWord_reverse, List.nil_append,
    List.append_nil]
  simp only [zWord, List.cons_append, List.append_assoc]

private theorem zWord_length {m : ℕ} (hm : 3 ≤ m) (j : Fin m) :
    (zWord m j.val).length = m * ((m + 1) * 2) - 1 := by
  rw [← complement_word m hm j, List.length_reverse, List.length_tail,
    List.length_rotate, cycleWord_length]

private theorem star_base_iff {m : ℕ} (z : Configuration m) (t : Fin (m + 1))
    (W : Cycle (Fin (m + 1))) (hzt : z (Fin.last m) = t)
    (hW : (residualList z : Cycle (Fin (m + 1))) = W ∨
      (residualList z : Cycle (Fin (m + 1))) = W.reverse) (v : Configuration m) :
    Star t W v ↔ Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v := by
  rcases hW with hW | hW
  · rw [hzt, hW]
  · rw [hzt, hW]
    simp only [Star, Cycle.reverse_reverse, or_comm]

private def nativeStarVertex {m : ℕ} (hm : 3 ≤ m) (z : Configuration m)
    (t : Fin (m + 1)) (W : Cycle (Fin (m + 1))) (hzt : z (Fin.last m) = t)
    (hW : (residualList z : Cycle (Fin (m + 1))) = W ∨
      (residualList z : Cycle (Fin (m + 1))) = W.reverse)
    (i : Fin (m * ((m + 1) * 2))) : {v : Configuration m // Star t W v} :=
  ⟨nativeVertex z i, (star_base_iff z t W hzt hW _).mpr
    (coordinate_star (by omega) z (rankEquiv m i))⟩

private theorem nativeStarVertex_bijective {m : ℕ} (hm : 3 ≤ m) (z : Configuration m)
    (t : Fin (m + 1)) (W : Cycle (Fin (m + 1))) (hzt : z (Fin.last m) = t)
    (hW : (residualList z : Cycle (Fin (m + 1))) = W ∨
      (residualList z : Cycle (Fin (m + 1))) = W.reverse) :
    Function.Bijective (nativeStarVertex hm z t W hzt hW) := by
  constructor
  · intro i k he
    exact nativeVertex_injective hm z (congrArg Subtype.val he)
  · intro v
    obtain ⟨i, hi⟩ := nativeVertex_surjective hm z v.val
      ((star_base_iff z t W hzt hW v.val).mp v.property)
    exact ⟨i, Subtype.ext hi⟩

/-- The odd native rank of the retained b-edge with marked-label position j. -/
def cutStart {m : ℕ} (j : Fin m) : Fin (m * ((m + 1) * 2)) :=
  (rankEquiv m).symm ((⟨0, j.pos⟩ : Fin m), j.castSucc, true)

private theorem cutStart_val {m : ℕ} (j : Fin m) : (cutStart j).val = 2 * j.val + 1 := by
  simp only [cutStart, rank_val, ↓reduceIte, Fin.val_castSucc, mul_zero, add_zero]
  omega

private theorem zWord_letter {m : ℕ} (hm : 3 ≤ m) (j : Fin m) (i : ℕ)
    (hi : i < m * ((m + 1) * 2) - 1) :
    (zWord m j.val)[i]'(by rwa [zWord_length hm]) =
      nativeGenerator (cutStart j -
        (⟨i + 1, by omega⟩ : Fin (m * ((m + 1) * 2)))) := by
  have hN := native_size_three hm
  letI : NeZero (m * ((m + 1) * 2)) := ⟨by omega⟩
  simp only [← complement_word m hm j, List.getElem_reverse, List.getElem_tail,
    List.getElem_rotate, cycleWord_ofFn]
  simp only [List.length_tail, List.length_rotate, cycleWord_length, List.length_ofFn,
    List.getElem_ofFn]
  congr 1
  apply Fin.ext
  simp only [Fin.val_sub, cutStart_val]
  congr 1
  omega

private theorem backwards_trace {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) (j : Fin m) :
    List.ofFn (fun i : Fin (m * ((m + 1) * 2)) =>
      nativeVertex z (cutStart j - i)) =
      List.scanl (fun v g => v * g) (nativeVertex z (cutStart j)) (zWord m j.val) := by
  have hN := native_size_three hm
  letI : NeZero (m * ((m + 1) * 2)) := ⟨by omega⟩
  let xs := List.ofFn (fun i : Fin (m * ((m + 1) * 2)) =>
    nativeVertex z (cutStart j - i))
  let ys := List.scanl (fun v g => v * g)
    (nativeVertex z (cutStart j)) (zWord m j.val)
  have hlen : xs.length = ys.length := by
    simp only [xs, ys, List.length_ofFn, List.length_scanl, zWord_length hm]
    omega
  have hget : ∀ i (hi : i < xs.length) (hj : i < ys.length), xs[i] = ys[i] := by
    intro i
    induction i with
    | zero =>
      intro hi hj
      simp only [xs, ys, List.getElem_ofFn, List.getElem_scanl_zero, Fin.mk_zero',
        sub_zero]
    | succ i ih =>
      intro hi hj
      have hi0 : i < xs.length := by omega
      have hj0 : i < ys.length := by omega
      rw [show ys[i + 1] = ys[i] * (zWord m j.val)[i]'(by
        simp only [ys, List.length_scanl] at hj; omega) from
        List.getElem_succ_scanl hj, ← ih hi0 hj0,
        zWord_letter hm j i (by
          have hilen : i + 1 < m * ((m + 1) * 2) := by
            simpa only [xs, List.length_ofFn] using hi
          omega)]
      simp only [xs, List.getElem_ofFn]
      have he : cutStart j - (⟨i + 1, by simpa only [xs, List.length_ofFn] using hi⟩ :
          Fin (m * ((m + 1) * 2))) + 1 =
          cutStart j - (⟨i, by simpa only [xs, List.length_ofFn] using hi0⟩ :
            Fin (m * ((m + 1) * 2))) := by
        have hc : (⟨i + 1, by simpa only [xs, List.length_ofFn] using hi⟩ :
            Fin (m * ((m + 1) * 2))) =
            (⟨i, by simpa only [xs, List.length_ofFn] using hi0⟩ :
              Fin (m * ((m + 1) * 2))) + 1 := by
          apply Fin.ext
          simp [Fin.add_def, Nat.mod_eq_of_lt (show i + 1 < m * ((m + 1) * 2) by
            simpa only [xs, List.length_ofFn] using hi),
            Nat.mod_eq_of_lt (show 1 < m * ((m + 1) * 2) by omega)]
        rw [hc]
        abel
      have hs := native_step hm z (cutStart j -
        (⟨i + 1, by simpa only [xs, List.length_ofFn] using hi⟩ :
          Fin (m * ((m + 1) * 2))))
      rw [he] at hs
      rw [← hs, mul_assoc, nativeGenerator_sq, mul_one]
  exact List.ext_getElem hlen hget

private theorem native_complement {m : ℕ} (hm : 3 ≤ m) (z : Configuration m)
    (t : Fin (m + 1)) (W : Cycle (Fin (m + 1))) (hzt : z (Fin.last m) = t)
    (hW : (residualList z : Cycle (Fin (m + 1))) = W ∨
      (residualList z : Cycle (Fin (m + 1))) = W.reverse) (j : Fin m) :
    let u := nativeStarVertex hm z t W hzt hW (cutStart j)
    let v := nativeStarVertex hm z t W hzt hW
      (finRotate (m * ((m + 1) * 2)) (cutStart j))
    ∃ w : ((starFactor t W).deleteEdges ({s(u, v)} : Set _)).Walk u v,
      w.IsHamiltonian ∧ w.length = m * ((m + 1) * 2) - 1 ∧
        w.support.map Subtype.val = List.scanl (fun x g => x * g) u.val (zWord m j.val) := by
  classical
  have hN := native_size_three hm
  letI : NeZero (m * ((m + 1) * 2)) := ⟨by omega⟩
  let u := nativeStarVertex hm z t W hzt hW (cutStart j)
  let v := nativeStarVertex hm z t W hzt hW
    (finRotate (m * ((m + 1) * 2)) (cutStart j))
  let f (i : Fin (m * ((m + 1) * 2))) :=
    nativeStarVertex hm z t W hzt hW (cutStart j - i)
  let last : Fin (m * ((m + 1) * 2)) := ⟨m * ((m + 1) * 2) - 1, by omega⟩
  have hone : (1 : Fin (m * ((m + 1) * 2))) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_one', Fin.val_zero,
      Nat.mod_eq_of_lt (show 1 < m * ((m + 1) * 2) by omega)] at hv
    omega
  have hlastIndex : last = -(1 : Fin (m * ((m + 1) * 2))) := by
    apply Fin.ext
    simp only [last, Fin.val_neg, if_neg hone, Fin.val_one',
      Nat.mod_eq_of_lt (show 1 < m * ((m + 1) * 2) by omega)]
  have hf0 : f 0 = u := by simp [f, u]
  have hflast : f last = v := by
    simp only [f, v, hlastIndex, sub_neg_eq_add, finRotate_apply]
  have hf : Function.Bijective f := by
    have hb := nativeStarVertex_bijective hm z t W hzt hW
    constructor
    · intro i k he
      exact sub_right_inj.mp (hb.1 he)
    · intro x
      obtain ⟨k, hk⟩ := hb.2 x
      refine ⟨cutStart j - k, ?_⟩
      have he : cutStart j - (cutStart j - k) = k := by abel
      simpa only [f, he] using hk
  let xs := List.ofFn f
  have hne : xs ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [xs, List.length_ofFn, List.length_nil] at hl
    omega
  have hhead : xs.head hne = u := by
    rw [List.head_ofFn]
    exact hf0
  have hlast : xs.getLast hne = v := by
    rw [List.getLast_ofFn]
    exact hflast
  have hchain : xs.IsChain (((starFactor t W).deleteEdges ({s(u, v)} : Set _)).Adj) := by
    apply List.isChain_ofFn.mpr
    intro i hi
    let x : Fin (m * ((m + 1) * 2)) := ⟨i, by omega⟩
    let y : Fin (m * ((m + 1) * 2)) := ⟨i + 1, hi⟩
    change ((starFactor t W).deleteEdges ({s(u, v)} : Set _)).Adj (f x) (f y)
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · have he : cutStart j - y + 1 = cutStart j - x := by
        have hy : y = x + 1 := by
          apply Fin.ext
          simp only [x, y, Fin.add_def, Fin.val_one',
            Nat.mod_eq_of_lt (show 1 < m * ((m + 1) * 2) by omega)]
          rw [Nat.mod_eq_of_lt hi]
        rw [hy]
        abel
      have ha := (native_adj hm z (cutStart j - y)).symm
      rw [he, hzt] at ha
      exact ha
    · intro he
      simp only [Set.mem_singleton_iff] at he
      rcases Sym2.eq_iff.mp he with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [← hf0] at hx
        rw [← hflast] at hy
        have hxv := congrArg Fin.val (hf.1 hx)
        have hyv := congrArg Fin.val (hf.1 hy)
        simp only [x, y, last, Fin.val_zero] at hxv hyv
        omega
      · rw [← hflast] at hx
        have hxv := congrArg Fin.val (hf.1 hx)
        simp only [x, last] at hxv
        omega
  let raw := SimpleGraph.Walk.ofSupport xs hne hchain
  let w := raw.copy hhead hlast
  have hs : w.support = xs := by
    simp only [w, raw, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]
  have hp : w.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [hs]
    exact List.nodup_ofFn.mpr hf.1)
  refine ⟨w, hp.isHamiltonian_of_mem ?_, ?_, ?_⟩
  · intro x
    rw [hs]
    exact List.mem_ofFn.mpr (hf.2 x)
  · simp only [w, raw, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_ofSupport,
      xs, List.length_ofFn]
  · rw [hs, List.map_ofFn]
    exact backwards_trace hm z j

private theorem uWord_sq (m k : ℕ) : (uWord m k).prod * (uWord m k).prod = 1 := by
  rw [uWord_product, rotate_pow_eq_cycle]
  calc
    (finCycle (k : Fin (m + 1)) * a m) * (finCycle (k : Fin (m + 1)) * a m) =
        finCycle (k : Fin (m + 1)) * (a m * finCycle (k : Fin (m + 1))) * a m := by
          simp only [mul_assoc]
    _ = finCycle (k : Fin (m + 1)) * (finCycle (- (k : Fin (m + 1))) * a m) * a m := by
      rw [a_cycle]
    _ = 1 := by
      rw [← mul_assoc, cycle_mul, add_neg_cancel, cycle_zero, one_mul, a_sq]

private theorem cast_j {m : ℕ} (j : Fin m) : (j.val : Fin (m + 1)) = j.castSucc := by
  apply Fin.ext
  simp only [Fin.val_natCast, Fin.val_castSucc]
  exact Nat.mod_eq_of_lt (by omega)

private theorem native_start {m : ℕ} (z : Configuration m) (j : Fin m) :
    nativeVertex z (cutStart j) = z * (uWord m j.val).prod := by
  simp only [nativeVertex, cutStart, Equiv.apply_symm_apply, coordinate, gapAnchor,
    Fin.val_zero, pow_zero, mul_one, ↓reduceIte, uWord_product, rotate_pow_eq_cycle, cast_j,
    mul_assoc]

private theorem native_end {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) (j : Fin m) :
    nativeVertex z (finRotate (m * ((m + 1) * 2)) (cutStart j)) =
      nativeVertex z (cutStart j) * b m := by
  have hN := native_size_three hm
  letI : NeZero (m * ((m + 1) * 2)) := ⟨by omega⟩
  have hg : nativeGenerator (cutStart j) = b m := by
    simp only [nativeGenerator, cutStart, Equiv.apply_symm_apply, ↓reduceIte,
      if_neg (Fin.castSucc_ne_last j)]
  rw [finRotate_apply, ← native_step hm, hg]

/-- Cutting any retained b-edge in a zero star gives the specified literal Z_j path.
The vertex domain is defined by deletion residuals, and every one of its vertices occurs
exactly once in the actual path. -/
theorem zeroStar_b_complement_hamiltonian {m : ℕ} (hm : 6 ≤ m)
    (t : Fin (m + 1)) (W : Cycle (Fin (m + 1))) (v : Configuration m)
    (hv : Star t W v) (j : Fin m) (hj : v j.castSucc = t) :
    ∃ hvb : Star t W (v * b m),
      ∃ w : ((starFactor t W).deleteEdges
          ({s((⟨v, hv⟩ : {x : Configuration m // Star t W x}),
            (⟨v * b m, hvb⟩ : {x : Configuration m // Star t W x}))} : Set _)).Walk
          ⟨v, hv⟩ ⟨v * b m, hvb⟩,
        w.IsHamiltonian ∧ w.length = 2 * m * (m + 1) - 1 ∧
          w.support.map Subtype.val = List.scanl (fun x g => x * g) v (zWord m j.val) := by
  classical
  let z := v * (uWord m j.val).prod
  have hzt : z (Fin.last m) = t := by
    simpa only [z, uWord_product, rotate_pow_eq_cycle, Equiv.Perm.mul_apply,
      a_apply, Fin.rev_last, finCycle_apply, zero_add, cast_j] using hj
  have hdel : delete t (configurationCycle z) =
      (delete t (configurationCycle v)).reverse := by
    dsimp [z]
    rw [uWord_product, ← mul_assoc, delete_reverse, delete_rotate]
  have hres : (residualList z : Cycle (Fin (m + 1))) =
      (delete t (configurationCycle v)).reverse := by
    rw [← residual_delete, hzt]
    exact hdel
  have hW : (residualList z : Cycle (Fin (m + 1))) = W ∨
      (residualList z : Cycle (Fin (m + 1))) = W.reverse := by
    rcases hv with hd | hd
    · right
      rw [hres, hd]
    · left
      rw [hres, hd, Cycle.reverse_reverse]
  let u := nativeStarVertex (show 3 ≤ m by omega) z t W hzt hW (cutStart j)
  let e := nativeStarVertex (show 3 ≤ m by omega) z t W hzt hW
    (finRotate (m * ((m + 1) * 2)) (cutStart j))
  have hu : u.val = v := by
    change nativeVertex z (cutStart j) = v
    rw [native_start]
    dsimp [z]
    rw [mul_assoc, uWord_sq, mul_one]
  have he : e.val = v * b m := by
    change nativeVertex z (finRotate (m * ((m + 1) * 2)) (cutStart j)) = _
    rw [native_end (show 3 ≤ m by omega)]
    exact congrArg (fun x => x * b m) hu
  have hvb : Star t W (v * b m) := he ▸ e.property
  have hu' : u = (⟨v, hv⟩ : {x : Configuration m // Star t W x}) := Subtype.ext hu
  have he' : e = (⟨v * b m, hvb⟩ : {x : Configuration m // Star t W x}) := Subtype.ext he
  refine ⟨hvb, ?_⟩
  have hc := native_complement (show 3 ≤ m by omega) z t W hzt hW j
  change ∃ w : ((starFactor t W).deleteEdges ({s(u, e)} : Set _)).Walk u e,
      w.IsHamiltonian ∧ w.length = m * ((m + 1) * 2) - 1 ∧
        w.support.map Subtype.val = List.scanl (fun x g => x * g) u.val (zWord m j.val) at hc
  rw [hu', he'] at hc
  simpa only [show m * ((m + 1) * 2) = 2 * m * (m + 1) by ring] using hc

#print axioms coordinateEquiv
#print axioms zeroStar_b_complement_hamiltonian

end D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
