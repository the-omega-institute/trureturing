/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.finite_certificate
   digest: Four-row local-to-transfer counting bridge. -/
/-
admission_basis: open-problem-resolution (#28807; Proved)
escape_witness: none
count_transfer: proof_shape=bind-only; consumers=HardinA233259PairTransferBase.initial_values, HardinA233259PairTransferRecurrence.shifted
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferInitial
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCount
open HardinA233259PairTransferCore
open HardinA233259PairTransferRep (quotient_rows)
open HardinA233259PairTransferInitial (initial_weights)

theorem count_transfer (n : ℕ) :
    (L (n+2) : ℤ) = dotProduct weights ((Q^n).mulVec (1 : Fin 14 → ℤ)) := by
  classical
  let he : {P : Fin 4 × Fin (n+2) → Fin 3 // Proper P} ≃
      {f : Fin (n+2) → Col //
        TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} :=
    Equiv.subtypeEquiv (gridEquiv (n+2)) (fun P => grid_good (n+2) P)
  have hc : L (n+2) = Nat.card {f : Fin (n+2) → Col //
      TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} := by
    rw [← Nat.card_congr he]
    simp [L, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  refine TransferMatrix.cardMatrix compatible (fun _ _ _ => True) (fun _ b => cls b)
    Q weights ?_ ?_ n
  · intro a b _ s
    rw [← quotient_rows b s]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : compatible b c <;> by_cases hs : cls c = s <;> simp [h, hs]
  · intro s
    rw [← initial_weights s]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : compatible a b ∧ cls b = s <;> simp [h]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCount
