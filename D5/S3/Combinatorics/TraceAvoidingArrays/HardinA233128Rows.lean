/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Rows
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.finite_certificate
   digest: Literal seven-column square strips and their boundary classes. -/

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
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableGood
statement_id: sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableLegal
statement_id: sha256:6c1f0ba304e14673a1966eca92d67e12ccf8925c940c5ba2391b4b478ac39547
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthLegal
statement_id: sha256:989eff70ea57c1a27e750e36536ea11ddb8f9aa5a27d74dce459fc2432ec52e8
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
GID: D5/S3/Observer/Separation/BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
bonds: proof_shape=bind-only; consumers=a, bonds_iff, counting_bridge
decidableBonds: proof_shape=bind-only; consumers=a, counting_bridge
a: proof_shape=bind-only; consumers=counting_bridge, a_eq_w, shifted_count, result
labels: proof_shape=bind-only; consumers=classCount, firstCount, bonds_iff, valid_next
compatible: proof_shape=bind-only; consumers=classCount
decidableCompatible: proof_shape=bind-only; consumers=classCount, counting_bridge
Valid: proof_shape=bind-only; consumers=valid_next, initial_valid, row_counts
boundaryClass: proof_shape=bind-only; consumers=classCount, firstCount, row_counts, v_eq_w
transfer: proof_shape=bind-only; consumers=row_counts, w, distribution_step
classCount: proof_shape=bind-only; consumers=class_fibres, row_counts, finite_certificate
firstCount: proof_shape=bind-only; consumers=initial_fibres, finite_certificate, a_eq_w
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Observer.Separation.BooleanRankThreeK4

/-! Literal seven-column square strips and their boundary classes. -/

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip (widthLegal colour_bond_iff)
open HardinA233255PairTransfer (Row rowLegal PairRow rowProper)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 7, c j ≠ d j ∧ (c j).val + (d j).val ≠ 5

private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

/-- The literal filtered count, with the owner's normalization predicate. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 7 → Fin 6 => widthLegal rowLegal bonds A)).card

def labels (c : Row) : PairRow := fun j => beta (c j)
def compatible (p : PairRow) (c : Row) : Prop := ∀ j, p j ≠ beta (c j)
private instance decidableCompatible (p : PairRow) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))

def Valid (s : Seen) (p : PairRow) : Prop :=
  s.1 = true ∧ rowProper p ∧ (s.2 = false → ∀ j, p j ≠ 2)

def boundaryClass (s : Seen) (p : PairRow) : Fin 21 :=
  if s.2 then
    if p 2 = p 0 then
      if p 3 = p 1 then
        if p 4 = p 2 then
          if p 5 = p 3 then if p 6 = p 4 then 1 else 2 else if p 6 = p 4 then 3 else 4
        else if p 5 = p 3 then if p 6 = p 4 then 5 else 6 else if p 6 = p 4 then 7 else 8
      else if p 4 = p 2 then
          if p 5 = p 3 then if p 6 = p 4 then 3 else 9 else if p 6 = p 4 then 10 else 11
        else if p 5 = p 3 then if p 6 = p 4 then 7 else 12 else if p 6 = p 4 then 13 else 14
    else if p 3 = p 1 then
        if p 4 = p 2 then
          if p 5 = p 3 then if p 6 = p 4 then 2 else 15 else if p 6 = p 4 then 9 else 16
        else if p 5 = p 3 then if p 6 = p 4 then 6 else 17 else if p 6 = p 4 then 12 else 18
      else if p 4 = p 2 then
          if p 5 = p 3 then if p 6 = p 4 then 4 else 16 else if p 6 = p 4 then 11 else 19
        else if p 5 = p 3 then if p 6 = p 4 then 8 else 18 else if p 6 = p 4 then 14 else 20
  else 0

def transfer (i k : Fin 21) : ℤ :=
  ![![128, 128, 256, 256, 128, 128, 256, 128, 0, 128, 128, 128, 128, 0, 0, 128, 0, 128, 0,
      64, 0]
    , ![0, 384, 512, 512, 256, 256, 512, 256, 0, 256, 256, 256, 256, 0, 0, 256, 0, 256, 0, 128,
      0]
    , ![0, 256, 384, 512, 256, 128, 256, 128, 128, 256, 256, 256, 256, 0, 0, 128, 256, 128,
      128, 0, 0]
    , ![0, 256, 512, 384, 128, 256, 512, 256, 0, 256, 128, 256, 256, 128, 0, 256, 0, 256, 0,
      128, 0]
    , ![0, 128, 256, 128, 256, 128, 256, 256, 128, 256, 0, 128, 128, 128, 128, 128, 128, 128,
      128, 128, 0]
    , ![0, 256, 256, 512, 256, 256, 256, 256, 256, 256, 256, 256, 256, 0, 0, 0, 256, 0, 256, 0,
      0]
    , ![0, 256, 256, 512, 256, 128, 384, 128, 0, 256, 256, 256, 256, 0, 0, 128, 0, 128, 128,
      128, 0]
    , ![0, 128, 128, 256, 256, 128, 128, 384, 256, 256, 128, 128, 256, 128, 128, 0, 256, 0,
      256, 0, 0]
    , ![0, 0, 128, 0, 128, 128, 0, 256, 384, 128, 0, 128, 0, 128, 256, 0, 256, 0, 128, 0, 128]
    , ![0, 128, 256, 256, 256, 128, 256, 256, 128, 384, 128, 128, 128, 128, 128, 128, 256, 128,
      128, 0, 0]
    , ![0, 256, 512, 256, 0, 256, 512, 256, 0, 256, 256, 256, 256, 0, 0, 256, 0, 256, 0, 128, 0]
    , ![0, 128, 256, 256, 128, 128, 256, 128, 128, 128, 128, 256, 256, 0, 0, 128, 128, 128,
      128, 128, 0]
    , ![0, 128, 256, 256, 128, 128, 256, 256, 0, 128, 128, 256, 384, 128, 0, 128, 0, 128, 128,
      128, 0]
    , ![0, 0, 0, 256, 256, 0, 0, 256, 256, 256, 0, 0, 256, 256, 256, 0, 256, 0, 256, 0, 0]
    , ![0, 0, 0, 0, 128, 0, 0, 128, 256, 128, 0, 0, 0, 128, 384, 0, 256, 0, 128, 0, 128]
    , ![0, 256, 256, 512, 256, 0, 256, 0, 0, 256, 256, 256, 256, 0, 0, 256, 0, 0, 256, 128, 0]
    , ![0, 0, 256, 0, 128, 128, 0, 256, 256, 256, 0, 128, 0, 128, 256, 0, 384, 128, 0, 0, 128]
    , ![0, 256, 256, 512, 256, 0, 256, 0, 0, 256, 256, 256, 256, 0, 0, 0, 256, 256, 0, 0, 0]
    , ![0, 0, 128, 0, 128, 128, 128, 256, 128, 128, 0, 128, 128, 128, 128, 128, 0, 0, 256, 128,
      0]
    , ![0, 128, 0, 256, 256, 0, 256, 0, 0, 0, 128, 256, 256, 0, 0, 128, 0, 0, 256, 256, 0]
    , ![0, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0, 0, 256, 0, 256, 0, 0, 0, 256]] i k

def classCount (s : Seen) (p : PairRow) (k : Fin 21) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (labels c) = k then 1 else 0

def firstCount (k : Fin 21) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    boundaryClass (finish (false, false) c) (labels c) = k then 1 else 0

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
