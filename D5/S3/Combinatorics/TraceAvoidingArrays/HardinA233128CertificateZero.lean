/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateZero
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128CertificateZero
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
DIRECT_FROZEN_DEPENDENCIES
DECLARATION_CONSUMERS
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroA
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroB
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroC
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroD
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroE
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import Mathlib.Tactic.FinCases

set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open HardinA233255PairTransfer (rowProper)

open private
  completed_0101010 completed_0101012 completed_0101020
  completed_0101021 completed_0101201 completed_0101202
  completed_0101210 completed_0101212 completed_0102010
  completed_0102012 completed_0102020 completed_0102021
  completed_0102101 completed_0102102 completed_0102120
  completed_0102121
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroA

open private
  completed_0120101 completed_0120102 completed_0120120
  completed_0120121 completed_0120201 completed_0120202
  completed_0120210 completed_0120212 completed_0121010
  completed_0121012 completed_0121020 completed_0121021
  completed_0121201 completed_0121202 completed_0121210
  completed_0121212
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroB

open private
  completed_0201010 completed_0201012 completed_0201020
  completed_0201021 completed_0201201 completed_0201202
  completed_0201210 completed_0201212 completed_0202010
  completed_0202012 completed_0202020 completed_0202021
  completed_0202101 completed_0202102 completed_0202120
  completed_0202121
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroC

open private
  completed_0210101 completed_0210102 completed_0210120
  completed_0210121 completed_0210201 completed_0210202
  completed_0210210 completed_0210212 completed_0212010
  completed_0212012 completed_0212020 completed_0212021
  completed_0212101 completed_0212102 completed_0212120
  completed_0212121
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroD

open private
  unseen_0101010
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroE

section
attribute [local irreducible] classCount

set_option maxHeartbeats 4000000 in
private theorem row_counts_zero : ∀ s p, Valid s p → p 0 = 0 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 p6 hp hfirst k
  change p0 = (0 : Fin 3) at hfirst
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
      | exact completed_0101010 k
      | exact completed_0101012 k
      | exact completed_0101020 k
      | exact completed_0101021 k
      | exact completed_0101201 k
      | exact completed_0101202 k
      | exact completed_0101210 k
      | exact completed_0101212 k
      | exact completed_0102010 k
      | exact completed_0102012 k
      | exact completed_0102020 k
      | exact completed_0102021 k
      | exact completed_0102101 k
      | exact completed_0102102 k
      | exact completed_0102120 k
      | exact completed_0102121 k
      | exact completed_0120101 k
      | exact completed_0120102 k
      | exact completed_0120120 k
      | exact completed_0120121 k
      | exact completed_0120201 k
      | exact completed_0120202 k
      | exact completed_0120210 k
      | exact completed_0120212 k
      | exact completed_0121010 k
      | exact completed_0121012 k
      | exact completed_0121020 k
      | exact completed_0121021 k
      | exact completed_0121201 k
      | exact completed_0121202 k
      | exact completed_0121210 k
      | exact completed_0121212 k
      | exact completed_0201010 k
      | exact completed_0201012 k
      | exact completed_0201020 k
      | exact completed_0201021 k
      | exact completed_0201201 k
      | exact completed_0201202 k
      | exact completed_0201210 k
      | exact completed_0201212 k
      | exact completed_0202010 k
      | exact completed_0202012 k
      | exact completed_0202020 k
      | exact completed_0202021 k
      | exact completed_0202101 k
      | exact completed_0202102 k
      | exact completed_0202120 k
      | exact completed_0202121 k
      | exact completed_0210101 k
      | exact completed_0210102 k
      | exact completed_0210120 k
      | exact completed_0210121 k
      | exact completed_0210201 k
      | exact completed_0210202 k
      | exact completed_0210210 k
      | exact completed_0210212 k
      | exact completed_0212010 k
      | exact completed_0212012 k
      | exact completed_0212020 k
      | exact completed_0212021 k
      | exact completed_0212101 k
      | exact completed_0212102 k
      | exact completed_0212120 k
      | exact completed_0212121 k
      | exact unseen_0101010 k
end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
