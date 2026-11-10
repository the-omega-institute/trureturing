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
DIRECT_FROZEN_DEPENDENCIES
DECLARATION_CONSUMERS
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Observer.Separation.BooleanRankThreeK4

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
