/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep.quotient_rows; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep.representative_rows
   digest: Four-row representative orbit continuation certificate. -/
/-
admission_basis: escape-witness
escape_witness: representative_rows (kernel checks every entry for the one-sided graph; used by quotient_rows)
representative_rows: proof_shape=content; consumers=quotient_rows
quotient_rows: proof_shape=content; consumers=HardinA233259PairTransferCount.count_transfer
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer (Col cls representatives relabel class_rep class_relabel)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem representative_rows : ∀ i s : Fin 14,
    (∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0) =
      Q i s := by
  have h : List.ofFn (fun i : Fin 14 => List.ofFn (fun s : Fin 14 =>
      ∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0)) =
      List.ofFn (fun i : Fin 14 => List.ofFn (fun s : Fin 14 => Q i s)) := by
    decide +kernel
  intro i s
  exact congrFun (List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp h) i)) s

theorem quotient_rows (b : Col) (s : Fin 14) :
    (∑ c : Col, if compatible b c ∧ cls c = s then (1 : ℤ) else 0) = Q (cls b) s := by
  obtain ⟨e, he⟩ :=
    class_rep b
  calc
    _ = ∑ c : Col, if compatible (relabel e b) (relabel e c) ∧
        cls (relabel e c) = s then (1 : ℤ) else 0 := by
      simp only [compatible_relabel,
        class_relabel]
    _ = ∑ c : Col, if compatible (representatives (cls b)) c ∧
        cls c = s then (1 : ℤ) else 0 := by
      rw [he]
      exact (relabel e).sum_comp (fun c =>
        if compatible (representatives (cls b)) c ∧ cls c = s then (1 : ℤ) else 0)
    _ = _ := representative_rows _ _

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRep
