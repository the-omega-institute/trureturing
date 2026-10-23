/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeFramePredecessor
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeFramePredecessor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every supplied next frame has a literal predecessor preserving both protected selected labels. -/
/- predecessor for the all-frame induction.
   Move exactly the newly prepended selected label to the end of the
   predecessor base. Reapplying the native constructor returns the
   supplied frame, so induction is not restricted to generated frames. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeFramePredecessor

open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open private next_full_perm from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates

/-- Every supplied next frame has an actual prior frame. The prior base
adds exactly the first selected label, without rotating its old base or
changing its terminal. The protected pair stays the same for k at least two. -/
theorem native_frame_predecessor {m k : ℕ} (F : SupplyFrame m (k + 1)) :
    ∃ (P : SupplyFrame m k) (u : Fin (m + 1)),
      ∃ hbase : P.base = F.base ++ [u],
        nextFrame P F.base u hbase = F ∧
        P.base.length = F.base.length + 1 ∧
        P.terminal = F.terminal ∧ F.selected = u :: P.selected ∧
        (∀ hk : 2 ≤ k,
          protectedP F (by omega) = protectedP P hk ∧
            protectedQ F (by omega) = protectedQ P hk) := by
  cases F with
  | mk S B v hlen hprefix hnodup hlabels =>
    cases S with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons u S =>
      let P : SupplyFrame m k := {
        selected := S
        base := B ++ [u]
        terminal := v
        selected_length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen
        prefix_length := by
          simp only [List.length_append, List.length_cons, List.length_singleton,
            List.length_nil] at hprefix ⊢
          omega
        full_nodup := (next_full_perm S B u v).nodup_iff.mp hnodup
        full_labels := fun x => (next_full_perm S B u v).mem_iff.mp (hlabels x) }
      refine ⟨P, u, rfl, ?_, ?_, rfl, rfl, ?_⟩
      · rfl
      · simp only [P, List.length_append, List.length_singleton]
      · intro hk
        exact native_protected_labels_prepend P _ hk u rfl

#print axioms native_frame_predecessor

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeFramePredecessor
