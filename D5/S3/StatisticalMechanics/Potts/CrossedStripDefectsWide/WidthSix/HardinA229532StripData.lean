/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.finite_certificate
   digest: Exact width-six one-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229532Strip.result)
between: proof_shape=bind-only; consumers=HardinA229532Strip.result
Valid: proof_shape=bind-only; consumers=HardinA229532Strip.result
decidableValid: proof_shape=bind-only; consumers=HardinA229532Strip.result
cl: proof_shape=bind-only; consumers=HardinA229532Strip.result
T: proof_shape=bind-only; consumers=HardinA229532Strip.result
initial: proof_shape=bind-only; consumers=HardinA229532Strip.result
terminal: proof_shape=bind-only; consumers=HardinA229532Strip.result
W: proof_shape=bind-only; consumers=HardinA229532Strip.result
raw_successors: proof_shape=bind-only; consumers=HardinA229532Strip.result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233172DiagonalStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

/-! Exact width-six HDA residual-budget transfer. -/
open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
open DefectTransfer (bondDefects)
open HardinA229584StripData (Row horizontal antidiagonal)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
def between : Finset (Fin 6 × Fin 6) :=
  antidiagonal ∪ antidiagonal.image Prod.swap
def Valid (p : Row) (d : ℕ) : Prop :=
  d ≤ 1 ∧ bondDefects horizontal p p ≤ 1 - d
private instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Row) (d : ℕ) : Fin 31 :=
  if bondDefects horizontal p p = 0 then
    ⟨(HardinA233172DiagonalStrip.boundaryClass (true, true) p).val - 1 +
      (if 0 < d then 0 else 10), by
      have := (HardinA233172DiagonalStrip.boundaryClass (true, true) p).isLt
      split_ifs <;> omega⟩ else
  let code : ℕ := (if p 0 = p 1 then 1 else 0) + (if p 0 = p 2 then 2 else 0) + (if p 0 = p 3 then 4 else 0) + (if p 0 = p 4 then 8 else 0) + (if p 0 = p 5 then 16 else 0) + (if p 1 = p 2 then 32 else 0) + (if p 1 = p 3 then 64 else 0) + (if p 1 = p 4 then 128 else 0) + (if p 1 = p 5 then 256 else 0) + (if p 2 = p 3 then 512 else 0) + (if p 2 = p 4 then 1024 else 0) + (if p 2 = p 5 then 2048 else 0) + (if p 3 = p 4 then 4096 else 0) + (if p 3 = p 5 then 8192 else 0) + (if p 4 = p 5 then 16384 else 0)
  if code ∈ ({10902, 646, 6354, 6162, 9396, 1188, 8244, 2340, 6156, 6336, 656, 10880} : Finset ℕ) then 20 else
  if code ∈ ({2344, 4364} : Finset ℕ) then 21 else
  if code ∈ ({4354, 8232} : Finset ℕ) then 22 else
  if code ∈ ({10774, 774, 776, 10760} : Finset ℕ) then 23 else
  if code ∈ ({1093, 1297, 16472, 19520} : Finset ℕ) then 24 else
  if code ∈ ({9217, 16450} : Finset ℕ) then 25 else
  if code ∈ ({9557, 19546} : Finset ℕ) then 26 else
  if code ∈ ({2185, 1200, 16772, 4304} : Finset ℕ) then 27 else
  if code ∈ ({8329, 4290, 16770, 9376} : Finset ℕ) then 28 else
  if code ∈ ({2117, 19460} : Finset ℕ) then 29 else
  30
def T : Matrix (Fin 31) (Fin 31) ℤ :=
  ![![HardinA233172DiagonalStrip.transfer 1 1 / 64, HardinA233172DiagonalStrip.transfer 1 2 / 64, HardinA233172DiagonalStrip.transfer 1 3 / 64, HardinA233172DiagonalStrip.transfer 1 4 / 64, HardinA233172DiagonalStrip.transfer 1 5 / 64, HardinA233172DiagonalStrip.transfer 1 6 / 64, HardinA233172DiagonalStrip.transfer 1 7 / 64, HardinA233172DiagonalStrip.transfer 1 8 / 64, HardinA233172DiagonalStrip.transfer 1 9 / 64, HardinA233172DiagonalStrip.transfer 1 10 / 64, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![HardinA233172DiagonalStrip.transfer 2 1 / 64, HardinA233172DiagonalStrip.transfer 2 2 / 64, HardinA233172DiagonalStrip.transfer 2 3 / 64, HardinA233172DiagonalStrip.transfer 2 4 / 64, HardinA233172DiagonalStrip.transfer 2 5 / 64, HardinA233172DiagonalStrip.transfer 2 6 / 64, HardinA233172DiagonalStrip.transfer 2 7 / 64, HardinA233172DiagonalStrip.transfer 2 8 / 64, HardinA233172DiagonalStrip.transfer 2 9 / 64, HardinA233172DiagonalStrip.transfer 2 10 / 64, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![HardinA233172DiagonalStrip.transfer 3 1 / 64, HardinA233172DiagonalStrip.transfer 3 2 / 64, HardinA233172DiagonalStrip.transfer 3 3 / 64, HardinA233172DiagonalStrip.transfer 3 4 / 64, HardinA233172DiagonalStrip.transfer 3 5 / 64, HardinA233172DiagonalStrip.transfer 3 6 / 64, HardinA233172DiagonalStrip.transfer 3 7 / 64, HardinA233172DiagonalStrip.transfer 3 8 / 64, HardinA233172DiagonalStrip.transfer 3 9 / 64, HardinA233172DiagonalStrip.transfer 3 10 / 64, 0, 1, 1, 1, 3, 0, 1, 1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![HardinA233172DiagonalStrip.transfer 4 1 / 64, HardinA233172DiagonalStrip.transfer 4 2 / 64, HardinA233172DiagonalStrip.transfer 4 3 / 64, HardinA233172DiagonalStrip.transfer 4 4 / 64, HardinA233172DiagonalStrip.transfer 4 5 / 64, HardinA233172DiagonalStrip.transfer 4 6 / 64, HardinA233172DiagonalStrip.transfer 4 7 / 64, HardinA233172DiagonalStrip.transfer 4 8 / 64, HardinA233172DiagonalStrip.transfer 4 9 / 64, HardinA233172DiagonalStrip.transfer 4 10 / 64, 1, 1, 1, 1, 2, 0, 1, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0],
    ![HardinA233172DiagonalStrip.transfer 5 1 / 64, HardinA233172DiagonalStrip.transfer 5 2 / 64, HardinA233172DiagonalStrip.transfer 5 3 / 64, HardinA233172DiagonalStrip.transfer 5 4 / 64, HardinA233172DiagonalStrip.transfer 5 5 / 64, HardinA233172DiagonalStrip.transfer 5 6 / 64, HardinA233172DiagonalStrip.transfer 5 7 / 64, HardinA233172DiagonalStrip.transfer 5 8 / 64, HardinA233172DiagonalStrip.transfer 5 9 / 64, HardinA233172DiagonalStrip.transfer 5 10 / 64, 0, 1, 3, 2, 3, 1, 1, 2, 3, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0],
    ![HardinA233172DiagonalStrip.transfer 6 1 / 64, HardinA233172DiagonalStrip.transfer 6 2 / 64, HardinA233172DiagonalStrip.transfer 6 3 / 64, HardinA233172DiagonalStrip.transfer 6 4 / 64, HardinA233172DiagonalStrip.transfer 6 5 / 64, HardinA233172DiagonalStrip.transfer 6 6 / 64, HardinA233172DiagonalStrip.transfer 6 7 / 64, HardinA233172DiagonalStrip.transfer 6 8 / 64, HardinA233172DiagonalStrip.transfer 6 9 / 64, HardinA233172DiagonalStrip.transfer 6 10 / 64, 0, 2, 0, 0, 2, 0, 2, 2, 2, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
    ![HardinA233172DiagonalStrip.transfer 7 1 / 64, HardinA233172DiagonalStrip.transfer 7 2 / 64, HardinA233172DiagonalStrip.transfer 7 3 / 64, HardinA233172DiagonalStrip.transfer 7 4 / 64, HardinA233172DiagonalStrip.transfer 7 5 / 64, HardinA233172DiagonalStrip.transfer 7 6 / 64, HardinA233172DiagonalStrip.transfer 7 7 / 64, HardinA233172DiagonalStrip.transfer 7 8 / 64, HardinA233172DiagonalStrip.transfer 7 9 / 64, HardinA233172DiagonalStrip.transfer 7 10 / 64, 0, 1, 1, 1, 1, 1, 2, 2, 2, 1, 0, 1, 1, 4, 2, 1, 1, 0, 0, 0, 0],
    ![HardinA233172DiagonalStrip.transfer 8 1 / 64, HardinA233172DiagonalStrip.transfer 8 2 / 64, HardinA233172DiagonalStrip.transfer 8 3 / 64, HardinA233172DiagonalStrip.transfer 8 4 / 64, HardinA233172DiagonalStrip.transfer 8 5 / 64, HardinA233172DiagonalStrip.transfer 8 6 / 64, HardinA233172DiagonalStrip.transfer 8 7 / 64, HardinA233172DiagonalStrip.transfer 8 8 / 64, HardinA233172DiagonalStrip.transfer 8 9 / 64, HardinA233172DiagonalStrip.transfer 8 10 / 64, 0, 0, 2, 0, 4, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2],
    ![HardinA233172DiagonalStrip.transfer 9 1 / 64, HardinA233172DiagonalStrip.transfer 9 2 / 64, HardinA233172DiagonalStrip.transfer 9 3 / 64, HardinA233172DiagonalStrip.transfer 9 4 / 64, HardinA233172DiagonalStrip.transfer 9 5 / 64, HardinA233172DiagonalStrip.transfer 9 6 / 64, HardinA233172DiagonalStrip.transfer 9 7 / 64, HardinA233172DiagonalStrip.transfer 9 8 / 64, HardinA233172DiagonalStrip.transfer 9 9 / 64, HardinA233172DiagonalStrip.transfer 9 10 / 64, 1, 1, 3, 3, 3, 1, 2, 0, 1, 0, 0, 0, 1, 0, 2, 2, 1, 2, 2, 0, 1],
    ![HardinA233172DiagonalStrip.transfer 10 1 / 64, HardinA233172DiagonalStrip.transfer 10 2 / 64, HardinA233172DiagonalStrip.transfer 10 3 / 64, HardinA233172DiagonalStrip.transfer 10 4 / 64, HardinA233172DiagonalStrip.transfer 10 5 / 64, HardinA233172DiagonalStrip.transfer 10 6 / 64, HardinA233172DiagonalStrip.transfer 10 7 / 64, HardinA233172DiagonalStrip.transfer 10 8 / 64, HardinA233172DiagonalStrip.transfer 10 9 / 64, HardinA233172DiagonalStrip.transfer 10 10 / 64, 0, 2, 2, 2, 0, 2, 2, 0, 0, 0, 0, 2, 2, 4, 4, 2, 2, 0, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 1 1 / 64, HardinA233172DiagonalStrip.transfer 1 2 / 64, HardinA233172DiagonalStrip.transfer 1 3 / 64, HardinA233172DiagonalStrip.transfer 1 4 / 64, HardinA233172DiagonalStrip.transfer 1 5 / 64, HardinA233172DiagonalStrip.transfer 1 6 / 64, HardinA233172DiagonalStrip.transfer 1 7 / 64, HardinA233172DiagonalStrip.transfer 1 8 / 64, HardinA233172DiagonalStrip.transfer 1 9 / 64, HardinA233172DiagonalStrip.transfer 1 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 2 1 / 64, HardinA233172DiagonalStrip.transfer 2 2 / 64, HardinA233172DiagonalStrip.transfer 2 3 / 64, HardinA233172DiagonalStrip.transfer 2 4 / 64, HardinA233172DiagonalStrip.transfer 2 5 / 64, HardinA233172DiagonalStrip.transfer 2 6 / 64, HardinA233172DiagonalStrip.transfer 2 7 / 64, HardinA233172DiagonalStrip.transfer 2 8 / 64, HardinA233172DiagonalStrip.transfer 2 9 / 64, HardinA233172DiagonalStrip.transfer 2 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 3 1 / 64, HardinA233172DiagonalStrip.transfer 3 2 / 64, HardinA233172DiagonalStrip.transfer 3 3 / 64, HardinA233172DiagonalStrip.transfer 3 4 / 64, HardinA233172DiagonalStrip.transfer 3 5 / 64, HardinA233172DiagonalStrip.transfer 3 6 / 64, HardinA233172DiagonalStrip.transfer 3 7 / 64, HardinA233172DiagonalStrip.transfer 3 8 / 64, HardinA233172DiagonalStrip.transfer 3 9 / 64, HardinA233172DiagonalStrip.transfer 3 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 4 1 / 64, HardinA233172DiagonalStrip.transfer 4 2 / 64, HardinA233172DiagonalStrip.transfer 4 3 / 64, HardinA233172DiagonalStrip.transfer 4 4 / 64, HardinA233172DiagonalStrip.transfer 4 5 / 64, HardinA233172DiagonalStrip.transfer 4 6 / 64, HardinA233172DiagonalStrip.transfer 4 7 / 64, HardinA233172DiagonalStrip.transfer 4 8 / 64, HardinA233172DiagonalStrip.transfer 4 9 / 64, HardinA233172DiagonalStrip.transfer 4 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 5 1 / 64, HardinA233172DiagonalStrip.transfer 5 2 / 64, HardinA233172DiagonalStrip.transfer 5 3 / 64, HardinA233172DiagonalStrip.transfer 5 4 / 64, HardinA233172DiagonalStrip.transfer 5 5 / 64, HardinA233172DiagonalStrip.transfer 5 6 / 64, HardinA233172DiagonalStrip.transfer 5 7 / 64, HardinA233172DiagonalStrip.transfer 5 8 / 64, HardinA233172DiagonalStrip.transfer 5 9 / 64, HardinA233172DiagonalStrip.transfer 5 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 6 1 / 64, HardinA233172DiagonalStrip.transfer 6 2 / 64, HardinA233172DiagonalStrip.transfer 6 3 / 64, HardinA233172DiagonalStrip.transfer 6 4 / 64, HardinA233172DiagonalStrip.transfer 6 5 / 64, HardinA233172DiagonalStrip.transfer 6 6 / 64, HardinA233172DiagonalStrip.transfer 6 7 / 64, HardinA233172DiagonalStrip.transfer 6 8 / 64, HardinA233172DiagonalStrip.transfer 6 9 / 64, HardinA233172DiagonalStrip.transfer 6 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 7 1 / 64, HardinA233172DiagonalStrip.transfer 7 2 / 64, HardinA233172DiagonalStrip.transfer 7 3 / 64, HardinA233172DiagonalStrip.transfer 7 4 / 64, HardinA233172DiagonalStrip.transfer 7 5 / 64, HardinA233172DiagonalStrip.transfer 7 6 / 64, HardinA233172DiagonalStrip.transfer 7 7 / 64, HardinA233172DiagonalStrip.transfer 7 8 / 64, HardinA233172DiagonalStrip.transfer 7 9 / 64, HardinA233172DiagonalStrip.transfer 7 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 8 1 / 64, HardinA233172DiagonalStrip.transfer 8 2 / 64, HardinA233172DiagonalStrip.transfer 8 3 / 64, HardinA233172DiagonalStrip.transfer 8 4 / 64, HardinA233172DiagonalStrip.transfer 8 5 / 64, HardinA233172DiagonalStrip.transfer 8 6 / 64, HardinA233172DiagonalStrip.transfer 8 7 / 64, HardinA233172DiagonalStrip.transfer 8 8 / 64, HardinA233172DiagonalStrip.transfer 8 9 / 64, HardinA233172DiagonalStrip.transfer 8 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 9 1 / 64, HardinA233172DiagonalStrip.transfer 9 2 / 64, HardinA233172DiagonalStrip.transfer 9 3 / 64, HardinA233172DiagonalStrip.transfer 9 4 / 64, HardinA233172DiagonalStrip.transfer 9 5 / 64, HardinA233172DiagonalStrip.transfer 9 6 / 64, HardinA233172DiagonalStrip.transfer 9 7 / 64, HardinA233172DiagonalStrip.transfer 9 8 / 64, HardinA233172DiagonalStrip.transfer 9 9 / 64, HardinA233172DiagonalStrip.transfer 9 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, HardinA233172DiagonalStrip.transfer 10 1 / 64, HardinA233172DiagonalStrip.transfer 10 2 / 64, HardinA233172DiagonalStrip.transfer 10 3 / 64, HardinA233172DiagonalStrip.transfer 10 4 / 64, HardinA233172DiagonalStrip.transfer 10 5 / 64, HardinA233172DiagonalStrip.transfer 10 6 / 64, HardinA233172DiagonalStrip.transfer 10 7 / 64, HardinA233172DiagonalStrip.transfer 10 8 / 64, HardinA233172DiagonalStrip.transfer 10 9 / 64, HardinA233172DiagonalStrip.transfer 10 10 / 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def initial : Fin 31 → ℤ := ![6, 12, 12, 12, 12, 6, 12, 6, 12, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 12, 12, 24, 24, 12, 12, 24, 24, 12, 12]
def terminal : Fin 31 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 21 → Fin 31 → ℤ :=
  ![![6, 12, 12, 12, 12, 6, 12, 6, 12, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 12, 12, 24, 24, 12, 12, 24, 24, 12, 12],
    ![24, 72, 96, 120, 144, 72, 192, 54, 180, 126, 24, 108, 144, 180, 240, 96, 264, 108, 312, 180, 0, 24, 36, 96, 96, 60, 60, 48, 72, 24, 36],
    ![150, 600, 1320, 1500, 2088, 930, 2628, 576, 2448, 1752, 540, 2160, 3768, 4008, 5472, 2460, 6264, 1944, 6144, 3768, 0, 444, 624, 1560, 1536, 948, 876, 600, 1104, 180, 360],
    ![1326, 6600, 17976, 19728, 28644, 12666, 36000, 7026, 32844, 23910, 8592, 35328, 68688, 73500, 101112, 45864, 120060, 32592, 114168, 74244, 0, 6132, 8580, 21240, 21336, 13116, 11820, 7896, 14904, 1752, 4200],
    ![14952, 82476, 244344, 264996, 389652, 171768, 488844, 91434, 443148, 324102, 129084, 554988, 1164444, 1247712, 1741788, 784836, 2094456, 528792, 1969752, 1316820, 0, 83820, 116664, 290304, 290616, 178152, 159360, 105144, 200784, 20652, 53496],
    ![188862, 1085868, 3311568, 3576912, 5281416, 2326854, 6623556, 1221108, 5989908, 4388136, 1921008, 8540064, 18926052, 20301936, 28625700, 12845304, 34691400, 8325528, 32393976, 22032132, 0, 1137048, 1580196, 3938856, 3939696, 2412996, 2152716, 1416288, 2712696, 265344, 708492],
    ![2495838, 14558496, 44836896, 48364980, 71508048, 31498350, 89667852, 16450794, 81026040, 59390610, 28353420, 129456288, 299015700, 320989896, 455816148, 203954592, 555305808, 128416416, 515945856, 355043184, 0, 15399828, 21389736, 53354184, 53342304, 32661060, 29113368, 19133640, 36686184, 3528084, 9517992],
    ![33505128, 196401276, 606849588, 654309672, 967832748, 426292776, 1213568712, 222286758, 1096318872, 803726730, 415617144, 1939615812, 4627088064, 4969779048, 7094514816, 3167868612, 8676148512, 1950549900, 8031307656, 5574013368, 0, 208449072, 289475112, 722227248, 721966320, 442009200, 393884748, 258782040, 496344480, 47460084, 128486124],
    ![452193162, 2655014868, 8212487316, 8853462108, 13097661108, 5768899098, 16422971988, 3006548436, 14834954772, 10876359648, 6056411400, 28787517228, 70474361652, 75724807776, 108539934096, 48389095908, 133126031316, 29272951944, 122880158184, 85839338676, 0, 2821022172, 3917341044, 9774352872, 9770347584, 5981492664, 5329747308, 3501257088, 6716164008, 640974792, 1737293664],
    ![6113756466, 35915929812, 111135026772, 119803138512, 177243333936, 78066796038, 222241899240, 40678532994, 200746400448, 147181651638, 87805297452, 423929050344, 1060035793596, 1139380264152, 1638418794612, 729524499384, 2014192102836, 435060752676, 1854970639512, 1302463682628, 0, 38175691284, 53010646056, 132272922936, 132216614328, 80943261936, 72121404036, 47376833760, 90882272352, 8668111740, 23503066512],
    ![82708219272, 485965977504, 1503908593500, 1621181589300, 2398503530400, 1056418246584, 3007431430068, 550439409870, 2716522926648, 1991691716478, 1267344639432, 6201778977120, 15783951628320, 16969888403136, 24466942357680, 10883126632356, 30134778974904, 6414141354252, 27701745251316, 19531407830952, 0, 516605202516, 717351602964, 1789961387664, 1789189873800, 1095341337348, 975952002888, 641099077920, 1229825684472, 117272995800, 318019396248],
    ![1119113606646, 6575931729240, 20351199426108, 21938044223352, 32457040746180, 14295658032978, 40697157386028, 7448509839072, 36760408470072, 26951938762920, 18220969486752, 90217223984148, 233068983731088, 250636004267508, 362155079847180, 160954488583644, 446739773167716, 93926165858748, 410047749848208, 290097815853912, 0, 6990814863024, 9707337789672, 24222165572520, 24211682640144, 14822364246720, 13206720139812, 8675409031896, 16642175897808, 1586844797244, 4303367723892],
    ![15143555174958, 88985563043340, 275396201229564, 296869152636948, 439214685357684, 193451447047638, 550721378223396, 100793946631302, 497448045235140, 364718441014830, 261062812023072, 1306001729139684, 3417507550521996, 3675778857942312, 5321111453413428, 2363213496407280, 6572447856779016, 1367493773716704, 6024937986179508, 4274721205709316, 0, 94601034911868, 131361443381940, 327779016727704, 327636968256240, 200578892598192, 178715503806264, 117396905386848, 225204660438528, 21472951407384, 58233359877456],
    ![204923064849600, 1204163327571288, 3726710617031064, 4017284073337008, 5943531607876944, 2617819350745200, 7452459692336280, 1363958703736518, 6731553109418028, 4935434288222382, 3728875512751548, 18825529023973248, 49813086228052452, 53586161602180548, 77694672760928028, 34484891870832384, 96072148409940960, 19810589402288700, 87973181049578364, 62569904597809404, 0, 1280158260253056, 1777606305488196, 4435565065143456, 4433641981691760, 2714269036081020, 2418408884108484, 1588634395744176, 3047508159803496, 290573456305944, 788021501541084],
    ![2773045096157406, 16294927375069848, 50430506070270768, 54362586805315092, 80428919056346784, 35424792738966906, 100847998464009828, 18457316567134824, 91092552900809136, 66787164428779440, 53113831121768532, 270345971865567420, 722345649243983244, 777166896742430784, 1128355173401848476, 500560105305585936, 1396585176374826024, 285745576949485236, 1277651750540225820, 910627861442012508, 0, 17323328268781044, 24054881378199072, 60022853325215448, 59996825972152032, 36729966095494044, 32726330393549052, 21497674365510072, 41239411518399600, 3932080735044324, 10663633844462352],
    ![37525289038362078, 220505717782848384, 682434476096254128, 735644036605593624, 1088378275374978756, 479374520464497954, 1364692840207720536, 249767593173265746, 1232680388785127388, 903775636310357406, 754660519642945416, 3869411599368049956, 10428055152751299084, 11220831902401445028, 16310769587113920756, 7232468826164192364, 20204961310702029468, 4105807860223463832, 18469186334012231772, 13187765214345713004, 0, 234422327321568708, 325514880222377844, 812239822527024696, 811887598557449256, 497036352179533764, 442858432412994276, 290910279412248456, 558058937127366216, 53209560509339496, 144302113410148632],
    ![507798599994476208, 2983921625379673428, 9234823170827105688, 9954864074956485564, 14728125947815647180, 6486980173844529792, 18467263124677601076, 3379898661695554626, 16680847240730154444, 12230050544006337030, 10698204404625180216, 55217420199421468488, 149952773200842747720, 161369906853552553920, 234816249187965247488, 104079621831135777540, 291091803201337388640, 58795359284516980032, 265893241708770852348, 190164338310203630652, 0, 3172244112828435348, 4404924501613562736, 10991371987930303584, 10986605553977082984, 6725983165773668880, 5992837963335072984, 3936648850781442024, 7551751396022871648, 720040904129379876, 1952721292914507264],
    ![6871618887069704262, 40378949089826048532, 124967248119386328672, 134710967068157111352, 199303585520622405432, 87782954276857860774, 249902245954951798308, 45737380746762681300, 225728151710123342556, 165499190339789492160, 151346695204250268744, 785857863531203278476, 2148791387609367049080, 2312615600553408987288, 3368324952010611815424, 1492439362631745361332, 4178282790211763951544, 839403632584972287564, 3814154796966324660540, 2731733815321816851624, 0, 42927364212690275136, 59608211453420429580, 148737175370113871592, 148672674802472153520, 91017184641966231204, 81096134724627186012, 53271422631373280016, 102191624807398628136, 9743718948770782680, 26424566189500937124],
    ![92987948723658434094, 546415016225597322096, 1691078733561487490496, 1822932444144838901628, 2697011097426764021112, 1187894342989888339254, 3381721049845053209124, 618926257841728380162, 3054592959720238774800, 2239564087601927551170, 2137047310098706288692, 11157331552905392729388, 30696326437568027719080, 33039419504467939121328, 48162030354244019289096, 21332865955123780490172, 59777846858366303109840, 11951321643649125697752, 54537313914025102217172, 39109752196521070878744, 0, 580900626634530782628, 806628778344654125184, 2012737562286396604968, 2011864727730553061232, 1231660515575399873172, 1097407125358801893216, 720878237556560907816, 1382874998915718876456, 131853710583351411132, 357581862293474753688],
    ![1258329222790984136352, 7394183849447045949132, 22883974195727067387132, 24668241727636121469552, 36496427477922978494508, 16074794715290198287584, 45762042712776307682544, 8375418714257989363950, 41335287969552271351728, 30306174255327837775122, 30123225910518302392260, 158059823150558331112992, 437289960336432694477932, 470704800697445714473848, 686667191162502207898260, 304065013596707604620196, 852722430061566601974504, 169743360533987863620588, 777569842750046580685332, 558245582648245743715488, 0, 7860849225048908311464, 10915442184769147086264, 27236717921747476398192, 27224906564391822214752, 16667046241916149882176, 14850305797879367867700, 9755050807730155352856, 18713307158137865557536, 1784267531909054082420, 4838860491629292857220],
    ![17027931786496019449434, 100059393270180431720148, 309669954737627126193420, 333814976015590150870452, 493876061408534359272444, 217526943054232782448170, 619259992779372797975364, 113337635739012250045836, 559356370656049655301204, 410108468439398004891144, 423929939292252889947120, 2234658502686010454861376, 6213864622326651044460960, 6689148918050196134775816, 9764781778668976218411300, 4322852667123564881999808, 12131873359047659922789012, 2405470573519926287124252, 11057562564611597365452396, 7946785418067599565836832, 0, 106374391223431983232788, 147709679192984254584516, 368572046733577374981000, 368412213341814466158048, 225541394640459504430752, 200956944099423211806924, 132007059394376785642560, 253231756415688136743048, 24145021277963024677032, 65480309247515296028760]]

/-- Saturated individual-colour fibres supply the original proper HDA block. -/
theorem raw_successors (p : Row) (hp : HardinThinGraphTransport.proper p) (j : Fin 11) :
    64 * (∑ r : Row, if HardinThinGraphTransport.proper r ∧
      HardinThinGraphTransport.compatible true p r ∧
      HardinA233172DiagonalStrip.boundaryClass (true, true) r = j then (1 : ℤ) else 0) =
      HardinA233172DiagonalStrip.transfer
        (HardinA233172DiagonalStrip.boundaryClass (true, true) p) j := by
  have ha : HardinA233172DiagonalStrip.Valid (true, true) p := ⟨rfl, hp, by simp⟩
  have ht := HardinA233172DiagonalStrip.finite_certificate (true, true) p ha j
  have h := HardinA233172DiagonalStrip.class_fibres (true, true) p j
  have hs (r : Row) : HardinA233255LiteralBridge.rowWeight (true, true) r = 64 ∧
      HardinA233255LiteralBridge.rowFinish (true, true) r = (true, true) := by
    simpa using HardinA233255ShapeSymmetry.full_row 6 r
  simp_rw [(hs _).1, (hs _).2] at h
  rw [← Finset.mul_sum] at h
  exact h.symm.trans ht
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
