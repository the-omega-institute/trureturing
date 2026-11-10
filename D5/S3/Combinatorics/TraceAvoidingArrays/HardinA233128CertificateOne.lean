/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOne
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.finite_certificate
   digest: Single-row class counts by the first boundary label. -/

/-
admission_basis: open-problem-resolution (#28672; Proved)
escape_witness: none; all-height class reduction is semiconjugacy iteration.
After normalizing finite one-step premises, v_eq_w is an instance of
Function.Semiconj.iterate_right. It and its downstream chain are bind-only.
Declaration namespace: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
Direct frozen dependencies (declaration GIDs and statement_ids):
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.PairRow
statement_id: sha256:e97b1a06b78d944d101465bdc94301416cfe964a1e9cbf900093e9cd04d04132
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowProper
statement_id: sha256:be16a774dbabce7949eb6e2bfc0026252c129abfda8a7377875535297a177b53
row_counts_one: proof_shape=bind-only; consumers=row_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneA
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneB
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneC
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneD
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneE
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import Mathlib.Tactic.FinCases

set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open HardinA233255PairTransfer (rowProper)

open private
  completed_1010101 completed_1010102 completed_1010120
  completed_1010121 completed_1010201 completed_1010202
  completed_1010210 completed_1010212 completed_1012010
  completed_1012012 completed_1012020 completed_1012021
  completed_1012101 completed_1012102 completed_1012120
  completed_1012121
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneA

open private
  completed_1020101 completed_1020102 completed_1020120
  completed_1020121 completed_1020201 completed_1020202
  completed_1020210 completed_1020212 completed_1021010
  completed_1021012 completed_1021020 completed_1021021
  completed_1021201 completed_1021202 completed_1021210
  completed_1021212
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneB

open private
  completed_1201010 completed_1201012 completed_1201020
  completed_1201021 completed_1201201 completed_1201202
  completed_1201210 completed_1201212 completed_1202010
  completed_1202012 completed_1202020 completed_1202021
  completed_1202101 completed_1202102 completed_1202120
  completed_1202121
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneC

open private
  completed_1210101 completed_1210102 completed_1210120
  completed_1210121 completed_1210201 completed_1210202
  completed_1210210 completed_1210212 completed_1212010
  completed_1212012 completed_1212020 completed_1212021
  completed_1212101 completed_1212102 completed_1212120
  completed_1212121
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneD

open private
  unseen_1010101
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOneE

section
attribute [local irreducible] classCount

set_option maxHeartbeats 4000000 in
private theorem row_counts_one : ∀ s p, Valid s p → p 0 = 1 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 p6 hp hfirst k
  change p0 = (1 : Fin 3) at hfirst
  subst p0
  cases b1
  · cases hp.1
  · cases b2 <;> fin_cases p1 <;> simp [Valid, rowProper, Fin.forall_fin_succ] at hp
    all_goals fin_cases p2 <;> simp at hp
    all_goals fin_cases p3 <;> simp at hp
    all_goals fin_cases p4 <;> simp at hp
    all_goals fin_cases p5 <;> simp at hp
    all_goals fin_cases p6 <;> simp at hp
    all_goals first
      | exact completed_1010101 k
      | exact completed_1010102 k
      | exact completed_1010120 k
      | exact completed_1010121 k
      | exact completed_1010201 k
      | exact completed_1010202 k
      | exact completed_1010210 k
      | exact completed_1010212 k
      | exact completed_1012010 k
      | exact completed_1012012 k
      | exact completed_1012020 k
      | exact completed_1012021 k
      | exact completed_1012101 k
      | exact completed_1012102 k
      | exact completed_1012120 k
      | exact completed_1012121 k
      | exact completed_1020101 k
      | exact completed_1020102 k
      | exact completed_1020120 k
      | exact completed_1020121 k
      | exact completed_1020201 k
      | exact completed_1020202 k
      | exact completed_1020210 k
      | exact completed_1020212 k
      | exact completed_1021010 k
      | exact completed_1021012 k
      | exact completed_1021020 k
      | exact completed_1021021 k
      | exact completed_1021201 k
      | exact completed_1021202 k
      | exact completed_1021210 k
      | exact completed_1021212 k
      | exact completed_1201010 k
      | exact completed_1201012 k
      | exact completed_1201020 k
      | exact completed_1201021 k
      | exact completed_1201201 k
      | exact completed_1201202 k
      | exact completed_1201210 k
      | exact completed_1201212 k
      | exact completed_1202010 k
      | exact completed_1202012 k
      | exact completed_1202020 k
      | exact completed_1202021 k
      | exact completed_1202101 k
      | exact completed_1202102 k
      | exact completed_1202120 k
      | exact completed_1202121 k
      | exact completed_1210101 k
      | exact completed_1210102 k
      | exact completed_1210120 k
      | exact completed_1210121 k
      | exact completed_1210201 k
      | exact completed_1210202 k
      | exact completed_1210210 k
      | exact completed_1210212 k
      | exact completed_1212010 k
      | exact completed_1212012 k
      | exact completed_1212020 k
      | exact completed_1212021 k
      | exact completed_1212101 k
      | exact completed_1212102 k
      | exact completed_1212120 k
      | exact completed_1212121 k
      | exact unseen_1010101 k
end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
