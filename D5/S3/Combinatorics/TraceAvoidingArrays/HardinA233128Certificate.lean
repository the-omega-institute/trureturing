/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Certificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Certificate
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

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateA
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateB
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateC
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateD
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZero
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOne
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import Mathlib.Tactic.FinCases

set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open HardinA233255PairTransfer (rowProper)

open private
  completed_2010101 completed_2010102 completed_2010120
  completed_2010121 completed_2010201 completed_2010202
  completed_2010210 completed_2010212 completed_2012010
  completed_2012012 completed_2012020 completed_2012021
  completed_2012101 completed_2012102 completed_2012120
  completed_2012121
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateA

open private
  completed_2020101 completed_2020102 completed_2020120
  completed_2020121 completed_2020201 completed_2020202
  completed_2020210 completed_2020212 completed_2021010
  completed_2021012 completed_2021020 completed_2021021
  completed_2021201 completed_2021202 completed_2021210
  completed_2021212
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateB

open private
  completed_2101010 completed_2101012 completed_2101020
  completed_2101021 completed_2101201 completed_2101202
  completed_2101210 completed_2101212 completed_2102010
  completed_2102012 completed_2102020 completed_2102021
  completed_2102101 completed_2102102 completed_2102120
  completed_2102121
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateC

open private
  completed_2120101 completed_2120102 completed_2120120
  completed_2120121 completed_2120201 completed_2120202
  completed_2120210 completed_2120212 completed_2121010
  completed_2121012 completed_2121020 completed_2121021
  completed_2121201 completed_2121202 completed_2121210
  completed_2121212
  from D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateD

section
attribute [local irreducible] classCount

set_option maxHeartbeats 4000000 in
private theorem row_counts_two : ∀ s p, Valid s p → p 0 = 2 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 p6 hp hfirst k
  change p0 = (2 : Fin 3) at hfirst
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
      | exact completed_2010101 k
      | exact completed_2010102 k
      | exact completed_2010120 k
      | exact completed_2010121 k
      | exact completed_2010201 k
      | exact completed_2010202 k
      | exact completed_2010210 k
      | exact completed_2010212 k
      | exact completed_2012010 k
      | exact completed_2012012 k
      | exact completed_2012020 k
      | exact completed_2012021 k
      | exact completed_2012101 k
      | exact completed_2012102 k
      | exact completed_2012120 k
      | exact completed_2012121 k
      | exact completed_2020101 k
      | exact completed_2020102 k
      | exact completed_2020120 k
      | exact completed_2020121 k
      | exact completed_2020201 k
      | exact completed_2020202 k
      | exact completed_2020210 k
      | exact completed_2020212 k
      | exact completed_2021010 k
      | exact completed_2021012 k
      | exact completed_2021020 k
      | exact completed_2021021 k
      | exact completed_2021201 k
      | exact completed_2021202 k
      | exact completed_2021210 k
      | exact completed_2021212 k
      | exact completed_2101010 k
      | exact completed_2101012 k
      | exact completed_2101020 k
      | exact completed_2101021 k
      | exact completed_2101201 k
      | exact completed_2101202 k
      | exact completed_2101210 k
      | exact completed_2101212 k
      | exact completed_2102010 k
      | exact completed_2102012 k
      | exact completed_2102020 k
      | exact completed_2102021 k
      | exact completed_2102101 k
      | exact completed_2102102 k
      | exact completed_2102120 k
      | exact completed_2102121 k
      | exact completed_2120101 k
      | exact completed_2120102 k
      | exact completed_2120120 k
      | exact completed_2120121 k
      | exact completed_2120201 k
      | exact completed_2120202 k
      | exact completed_2120210 k
      | exact completed_2120212 k
      | exact completed_2121010 k
      | exact completed_2121012 k
      | exact completed_2121020 k
      | exact completed_2121021 k
      | exact completed_2121201 k
      | exact completed_2121202 k
      | exact completed_2121210 k
      | exact completed_2121212 k
end

open private row_counts_zero from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZero
open private row_counts_one from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateOne

private theorem row_counts (s : Seen) (p : PairRow) (hp : Valid s p) (k : Fin 21) :
    classCount s p k = transfer (boundaryClass s p) k := by
  have h : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide +kernel
  rcases h (p 0) with hzero | hone | htwo
  · exact row_counts_zero s p hp hzero k
  · exact row_counts_one s p hp hone k
  · exact row_counts_two s p hp htwo k

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
