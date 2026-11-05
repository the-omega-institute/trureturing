/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse differing columns control equal-height tiling windows by finite phases. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.EqualLengthTiling
import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedWords
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Finite phase estimates for actual marked tilings. The good-phase theorem
allows a window to cross arbitrarily many seams. It assumes neither invariant
measures nor a chosen point or representative in each phase fibre.
The public theorem escape registrations remain unfinished under the linked
same-problem audit issue https://github.com/the-omega-institute/trureturing/issues/24726.
-/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.SparseDisagreement

/-- A phase is bad when one of the finitely many signed window coordinates
lands in the specified differing-column set. -/
def badPhases {L : ℕ} [NeZero L] (D : Finset (ZMod L)) (t : ℤ) (r : ℕ) :
    Finset (ZMod L) :=
  (Finset.range r).biUnion fun k => D.image fun d => d - ((t + (k : ℤ) : ℤ) : ZMod L)

/-- A union of translates has at most one copy of the disagreement set per
window coordinate; overlap can only reduce its size. -/
theorem badPhases_card_le {L : ℕ} [NeZero L] (D : Finset (ZMod L)) (t : ℤ) (r : ℕ) :
    (badPhases D t r).card ≤ r * D.card := by
  calc
    (badPhases D t r).card ≤
        ∑ k ∈ Finset.range r,
          (D.image fun d => d - ((t + (k : ℤ) : ℤ) : ZMod L)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range r, D.card :=
      Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = r * D.card := by simp

/-- The literal differing columns of two words of one positive common height. -/
def wordDisagreements (W : Bool → List Bool) (L : ℕ) [NeZero L]
    (hW : ∀ a, (W a).length = L) : Finset (ZMod L) :=
  Finset.univ.filter fun j =>
    (W false)[j.val]'(by rw [hW]; exact j.val_lt) ≠
      (W true)[j.val]'(by rw [hW]; exact j.val_lt)

/-- Physical offsets evolve by addition in the common finite cyclic phase group. -/
theorem offset_cast (W : Bool → List Bool) (L : ℕ) [NeZero L]
    (hW : ∀ a, (W a).length = L) (x : MarkedTiling W) (i : ℤ) :
    (((x.1 i).2.val : ℕ) : ZMod L) =
      (i : ZMod L) + (((x.1 0).2.val : ℕ) : ZMod L) := by
  have hp := tiled_offset_phase W L hW (NeZero.pos L) x i
  have hc := congrArg (fun j : ℤ => (j : ZMod L)) hp
  simpa only [Int.cast_natCast, ZMod.intCast_mod, Int.cast_add] using hc

private theorem read_at_offset (W : Bool → List Bool) (L : ℕ)
    (hW : ∀ a, (W a).length = L) (x : MarkedTiling W) (i : ℤ)
    (j : ℕ) (hj : j < L) (hoff : (x.1 i).2.val = j) :
    readTiling W x i = (W (x.1 i).1)[j]'(by rw [hW]; exact hj) := by
  simp only [readTiling, readTile, List.get_eq_getElem, hoff]

/-- Two actual tilings at the same physical phase write the same entire
window outside the finite translated disagreement set, including all seams. -/
theorem same_phase_window (W : Bool → List Bool) (L : ℕ) [NeZero L]
    (hW : ∀ a, (W a).length = L) (x y : MarkedTiling W)
    (hphase : (x.1 0).2.val = (y.1 0).2.val) (t : ℤ) (r : ℕ)
    (hgood : (((x.1 0).2.val : ℕ) : ZMod L) ∉
      badPhases (wordDisagreements W L hW) t r) :
    ∀ k : ℕ, k < r → readTiling W x (t + (k : ℤ)) =
      readTiling W y (t + (k : ℤ)) := by
  intro k hk
  let i : ℤ := t + (k : ℤ)
  let j : ℕ := (x.1 i).2.val
  have hj : j < L := by simpa only [hW] using (x.1 i).2.isLt
  have hoff : (y.1 i).2.val = j := by
    have hx := tiled_offset_phase W L hW (NeZero.pos L) x i
    have hy := tiled_offset_phase W L hW (NeZero.pos L) y i
    rw [hphase] at hx
    dsimp [j]
    omega
  have hnot : (j : ZMod L) ∉ wordDisagreements W L hW := by
    intro hbad
    apply hgood
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_range.mpr hk, Finset.mem_image.mpr ⟨(j : ZMod L), hbad, ?_⟩⟩
    change (((x.1 i).2.val : ℕ) : ZMod L) - (i : ZMod L) = _
    rw [offset_cast W L hW x i]
    exact add_sub_cancel_left _ _
  have hcolumn : (W false)[j]'(by rw [hW]; exact hj) =
      (W true)[j]'(by rw [hW]; exact hj) := by
    simpa only [wordDisagreements, Finset.mem_filter, Finset.mem_univ, true_and,
      ZMod.val_natCast_of_lt hj, not_not] using hnot
  change readTiling W x i = readTiling W y i
  rw [read_at_offset W L hW x i j hj rfl, read_at_offset W L hW y i j hj hoff]
  cases (x.1 i).1 <;> cases (y.1 i).1 <;> simp_all

private theorem mismatchCount_ofFn (L : ℕ) (f g : Fin L → Bool) :
    Balanced.mismatchCount (List.ofFn f) (List.ofFn g) =
      ∑ j : Fin L, if f j = g j then 0 else 1 := by
  induction L with
  | zero => simp [Balanced.mismatchCount]
  | succ L ih =>
      have ht := ih (fun j => f j.succ) (fun j => g j.succ)
      simp only [Balanced.mismatchCount] at ht ⊢
      rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, List.count_cons,
        Fin.sum_univ_succ, ht]
      cases f 0 <;> cases g 0 <;> simp [Nat.add_comm]

/-- The finite residue disagreement set has exactly the aligned list mismatch
count. This bridges physical columns to the existing word recurrence. -/
theorem wordDisagreements_card (W : Bool → List Bool) (L : ℕ) [NeZero L]
    (hW : ∀ a, (W a).length = L) :
    (wordDisagreements W L hW).card = Balanced.mismatchCount (W false) (W true) := by
  let f (a : Bool) (j : Fin L) : Bool :=
    (W a)[j.val]'(by rw [hW]; exact j.isLt)
  have hlist (a : Bool) : List.ofFn (f a) = W a := by
    apply List.ext_getElem
    · simp [hW]
    · intro j hj hj'
      simp only [List.getElem_ofFn, f]
  have hc := mismatchCount_ofFn L (f false) (f true)
  rw [hlist false, hlist true] at hc
  rw [hc]
  cases L with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ L =>
      unfold wordDisagreements
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      simp only [ZMod.val, f]
      split_ifs <;> simp_all

local instance (n : ℕ) : NeZero (Balanced.height n) :=
  ⟨Nat.ne_of_gt (Balanced.height_pos n)⟩

/-- For the actual balanced words, the proportion of exceptional phases for
any signed length-r window is at most r times the exact 3^(-n) disagreement
fraction. This integral form avoids division and rounding altogether. -/
theorem balanced_badPhases_card_scaled (n : ℕ) (t : ℤ) (r : ℕ) :
    3 ^ n * (badPhases
      (wordDisagreements (Balanced.balancedWord n) (Balanced.height n)
        (Balanced.balancedWord_length n)) t r).card ≤ r * Balanced.height n := by
  have hc := badPhases_card_le
    (wordDisagreements (Balanced.balancedWord n) (Balanced.height n)
      (Balanced.balancedWord_length n)) t r
  have hm := wordDisagreements_card (Balanced.balancedWord n) (Balanced.height n)
    (Balanced.balancedWord_length n)
  change _ = Balanced.disagreementCount n at hm
  rw [hm] at hc
  have hs := Balanced.disagreementCount_scaled n
  calc
    _ ≤ 3 ^ n * (r * Balanced.disagreementCount n) := Nat.mul_le_mul_left _ hc
    _ = r * Balanced.height n := by rw [Nat.mul_left_comm, hs]

end D5.S1.Dynamics.Symbolic.PermutativeLifts.SparseDisagreement
