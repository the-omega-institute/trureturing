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
Direct frozen dependencies (declaration GIDs and statement_ids):
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.colour_bond_iff
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableGood
statement_id: sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowFinish
statement_id: sha256:ded50bd8c5de69b5b2324e575fee135f275ae05b5bb30b328b0e5c0313d86b07
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowWeight
statement_id: sha256:076a03b0e19556ba67d0faed8d8d552fb3d55e6c40992d9c52c88faad85e373a
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.scanner_fibres
statement_id: sha256:63a356389be3d9bf756c53fb12271299a7668c1123562d84a2e34e78a341fc90
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.PairRow
statement_id: sha256:e97b1a06b78d944d101465bdc94301416cfe964a1e9cbf900093e9cd04d04132
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Row
statement_id: sha256:bfdef18389c25a4e0e0289ec0c41644aaf42d71c7a4d540ac5103952779dfd2c
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.decidableRowLegal
statement_id: sha256:566fa77bfdf47796ff0524d5a78f68b96413ca55006aa1429a767aad72408b70
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowLegal
statement_id: sha256:ad59d456a8f5b2710481be3ed4a9d79e276a0e4319f7b6918310d350fc440508
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowProper
statement_id: sha256:be16a774dbabce7949eb6e2bfc0026252c129abfda8a7377875535297a177b53
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.full_row
statement_id: sha256:f81e65c6e42bf750ca73737a7ace4b7b696a7b7a57684908ba1ce134acfcf88c
GID: D5/S3/Observer/Separation/BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
row_counts_01: proof_shape=bind-only; consumers=row_counts_zero
row_counts_02: proof_shape=bind-only; consumers=row_counts_zero
row_counts_zero: proof_shape=bind-only; consumers=row_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroA
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroB
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroC
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroD
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128CertificateZeroE
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import Mathlib.Tactic.FinCases

/-! Single-row class counts by the first boundary label. -/

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
-- The finite branching retains each legal label row explicitly.
private theorem row_counts_01 : ∀ s p, Valid s p → p 0 = 0 → p 1 = 1 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 p6 hp hfirst hsecond k
  change p0 = (0 : Fin 3) at hfirst
  change p1 = (1 : Fin 3) at hsecond
  subst p0
  subst p1
  cases b1
  · cases hp.1
  · change (_ ∧ _ ∧ _) at hp
    cases b2 <;> simp [rowProper, Fin.forall_fin_succ] at hp
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
      | exact unseen_0101010 k

set_option maxHeartbeats 4000000 in
-- The finite branching retains each legal label row explicitly.
private theorem row_counts_02 : ∀ s p, Valid s p → p 0 = 0 → p 1 = 2 → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 p6 hp hfirst hsecond k
  change p0 = (0 : Fin 3) at hfirst
  change p1 = (2 : Fin 3) at hsecond
  subst p0
  subst p1
  cases b1
  · cases hp.1
  · change (_ ∧ _ ∧ _) at hp
    cases b2 <;> simp [rowProper, Fin.forall_fin_succ] at hp
    all_goals fin_cases p2 <;> simp at hp
    all_goals fin_cases p3 <;> simp at hp
    all_goals fin_cases p4 <;> simp at hp
    all_goals fin_cases p5 <;> simp at hp
    all_goals fin_cases p6 <;> simp at hp
    all_goals first
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

private theorem row_counts_zero (s : HardinA233175PairStrip.Seen)
    (p : HardinA233255PairTransfer.PairRow) (hp : Valid s p) (hfirst : p 0 = 0)
    (k : Fin 21) : classCount s p k = transfer (boundaryClass s p) k := by
  have hne : p 0 ≠ p 1 := hp.2.1 0
  have h : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide +kernel
  rcases h (p 1) with hbad | hb | hc
  · exact (hne (hfirst.trans hbad.symm)).elim
  · exact row_counts_01 s p hp hfirst hb k
  · exact row_counts_02 s p hp hfirst hc k

end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
