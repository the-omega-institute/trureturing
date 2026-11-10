/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferBase
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferBase
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferBase.initial_values; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCount.count_transfer,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.powers_table
   digest: Four-row transfer initial scalar values. -/
/-
admission_basis: escape-witness
escape_witness: Rep.representative_rows, Initial.initial_weights and Powers.table_steps (via count_transfer and powers_table)
initial_values: proof_shape=content; consumers=HardinA233259PairTransferRecurrence.recurrence, Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip.Bridge.actual_dependence
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCount
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
open HardinA233259PairTransferCore
open HardinA233259PairTransferCount (count_transfer)
open HardinA233259PairTransferPowers (powers_table)

theorem initial_values : ∀ k : Fin 8, (L (k.val + 2) : ℤ) =
    ![384, 2592, 17496, 121176, 842616, 5871528, 40931568, 285366888] k := by
  intro k
  rw [count_transfer, powers_table ⟨k.val, by omega⟩]
  fin_cases k <;> rfl

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
