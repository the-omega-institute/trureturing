/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.finite_certificate
   digest: Literal six-column square-strip definitions and boundary data. -/

/-
admission_basis: open-problem-resolution (#28649; Proved)
escape_witness: none; every declaration is bind-only.
Declaration names use the D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip namespace.
Cross-module consumers retain that namespace.
bonds: proof_shape=bind-only; consumers=a
decidableBonds: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=counting_bridge
labels: proof_shape=bind-only; consumers=class_fibres
compatible: proof_shape=bind-only; consumers=class_fibres
decidableCompatible: proof_shape=bind-only; consumers=classCount
Valid: proof_shape=bind-only; consumers=valid_next
boundaryClass: proof_shape=bind-only; consumers=row_counts
transfer: proof_shape=bind-only; consumers=w
classCount: proof_shape=bind-only; consumers=class_fibres
firstCount: proof_shape=bind-only; consumers=first_fibres
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Observer.Separation.BooleanRankThreeK4

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip
  (widthLegal)
open HardinA233254TriangleStrip (Row rowLegal)
open HardinA233255PairTransfer (Boundary)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype
def bonds (c d : Row) : Prop :=
  ∀ j : Fin 6, c j ≠ d j ∧ (c j).val + (d j).val ≠ 5

private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

/-- Literal filtered array count. The first-cell condition sets the convention `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 6 → Fin 6 => widthLegal rowLegal bonds A)).card

def labels (c : Row) : Boundary := fun j => beta (c j)
def compatible (p : Boundary) (c : Row) : Prop := ∀ j, p j ≠ beta (c j)
private instance decidableCompatible (p : Boundary) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))

def Valid (s : Seen) (p : Boundary) : Prop :=
  s.1 = true ∧ (∀ j : Fin 5, p j.castSucc ≠ p j.succ) ∧
    (s.2 = false → ∀ j, p j ≠ 2)

def boundaryClass (s : Seen) (p : Boundary) : Fin 11 :=
  if s.2 then
    if p 2 = p 0 then
      if p 3 = p 1 then
        if p 4 = p 2 then (if p 5 = p 3 then 1 else 2)
        else (if p 5 = p 3 then 4 else 3)
      else if p 4 = p 2 then (if p 5 = p 3 then 4 else 5)
        else (if p 5 = p 3 then 7 else 6)
    else if p 3 = p 1 then
      if p 4 = p 2 then (if p 5 = p 3 then 2 else 10)
      else (if p 5 = p 3 then 5 else 9)
    else if p 4 = p 2 then (if p 5 = p 3 then 3 else 9)
      else (if p 5 = p 3 then 6 else 8)
  else 0

def transfer (i k : Fin 11) : ℤ :=
  ![![64, 64, 128, 64, 128, 128, 0, 32, 0, 64, 32]
    , ![0, 192, 256, 128, 256, 256, 0, 64, 0, 128, 64]
    , ![0, 128, 256, 64, 192, 192, 64, 64, 0, 128, 64]
    , ![0, 64, 64, 192, 128, 64, 128, 64, 64, 64, 64]
    , ![0, 128, 192, 128, 256, 192, 64, 64, 0, 128, 64]
    , ![0, 128, 192, 64, 192, 256, 0, 64, 0, 128, 64]
    , ![0, 0, 64, 128, 64, 0, 192, 64, 64, 64, 64]
    , ![0, 64, 128, 128, 128, 128, 128, 128, 0, 128, 64]
    , ![0, 0, 0, 128, 0, 0, 128, 0, 128, 0, 64]
    , ![0, 64, 128, 64, 128, 128, 64, 64, 0, 192, 0]
    , ![0, 64, 128, 128, 128, 128, 128, 64, 64, 0, 128]] i k

def classCount (s : Seen) (p : Boundary) (k : Fin 11) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (labels c) = k then 1 else 0

def firstCount (k : Fin 11) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    boundaryClass (finish (false, false) c) (labels c) = k then 1 else 0


end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
