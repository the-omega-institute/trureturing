/- Unconditional all-k strong-state induction candidate. Not kernel checked.
   This source requires the full third-order base, not its temporary helper check. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ThirdOrderState
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStrongStateStep
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeFramePredecessor

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateExistence

open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ThirdOrderState
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeFramePredecessor
open private parent_from_state_suppliers from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
open private current_joint_from_same_state_parent from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateJointPromotion
open private strong_state_from_same_parent from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStrongStateStep

/-- Every native frame of order at least three has one actual Hamilton
cycle with its complete joint and both restored partitions, literal
ports, correct orientation flags and all three retained-edge invariants. -/
theorem native_actual_state_exists {m k : ℕ} (hk : 3 ≤ k)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) :
    ∃ S : StateFor F (by omega) hB,
      S.primaryOdd = decide (k % 2 = 1) ∧
      S.oppositeOdd = !decide (k % 2 = 1) ∧
      S.distinguishedOpposite = decide (k % 2 = 0) := by
  induction k, hk using Nat.le_induction generalizing F with
  | base =>
    simpa only [show 3 % 2 = 1 from rfl, decide_true, Bool.not_true,
      Nat.one_ne_zero, decide_false] using native_third_order_state_exists F hB
  | succ k hk ih =>
    have hprefix := F.prefix_length
    simp only [List.length_append, F.selected_length] at hprefix
    have hm : 3 ≤ m := by omega
    obtain ⟨P, u, hbase, hnext, _, _, _, _⟩ := native_frame_predecessor F
    let B := oppositeSelectedFrame P (by omega)
    obtain ⟨W⟩ := parent_from_state_suppliers hm (by omega) ih B F.base u hbase hB
    obtain ⟨J⟩ := current_joint_from_same_state_parent hm hk B F.base u hbase hB W
    have hnew := strong_state_from_same_parent hm hk B F.base u hbase hB W J
    have hrev : oppositeSelectedFrame B (by omega) = P :=
      native_opposite_selected_involutive P (by omega)
    have hstate : ∃ S : StateFor F (by omega) hB,
        S.primaryOdd = W.P.oppositeOdd ∧ S.oppositeOdd = W.P.primaryOdd ∧
          S.distinguishedOpposite = !W.P.distinguishedOpposite := by
      simpa only [hrev, hnext] using hnew
    obtain ⟨S, h₀, h₁, hd⟩ := hstate
    have hp : decide ((k + 1) % 2 = 1) = !decide (k % 2 = 1) := by
      by_cases he : k % 2 = 0
      · have hn : (k + 1) % 2 = 1 := by omega
        simp only [he, hn, Nat.zero_ne_one, decide_false, decide_true, Bool.not_false]
      · have ho : k % 2 = 1 := by omega
        have hn : (k + 1) % 2 = 0 := by omega
        simp only [ho, hn, Nat.zero_ne_one, decide_false, decide_true, Bool.not_true]
    have hdp : decide ((k + 1) % 2 = 0) = !decide (k % 2 = 0) := by
      by_cases he : k % 2 = 0
      · have hn : (k + 1) % 2 = 1 := by omega
        simp only [he, hn, Nat.one_ne_zero, decide_false, decide_true, Bool.not_true]
      · have ho : k % 2 = 1 := by omega
        have hn : (k + 1) % 2 = 0 := by omega
        simp only [ho, hn, Nat.one_ne_zero, decide_false, decide_true, Bool.not_false]
    refine ⟨S, ?_, ?_, ?_⟩
    · rw [h₀, W.pFlags.2.1, hp]
    · rw [h₁, W.pFlags.1, hp, Bool.not_not]
    · rw [hd, W.pFlags.2.2, hdp]

#print axioms native_actual_state_exists

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateExistence
