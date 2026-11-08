/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185764Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA185764Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The literal binary array counts satisfy the published recurrence and series. -/

/-
admission_basis: open-problem-resolution (#21316; Proved)
proof_shape: content: result, via the literal-array cardinality bridge and continuation induction
escape_witness: none (the settling result uses the external open-problem basis)
Direct frozen dependencies: none. Pinned Mathlib supplies matrices, finite sums and cardinalities.
All auxiliary theorems are consumed; arithmetic certificates and normalization helpers are bind-only.
The source arrays use Matrix directly; their encoded-row traces apply Matrix.trace to block. Row predicates use pairOK and tripleOK.
The finite decision procedures transport diagonal-entry sums to Matrix.trace through checked equivalences.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21914
The source is OEIS A185761--A185764; literature-search completeness is ASSUMED-UNVERIFIED.
Declaration classifications (name | proof_shape | consumer):
CertA185764.trace | bind-only | decidableRowPredicate1
CertA185764.decidableRowPredicate1 | bind-only | step_0
CertA185764.decidableRowPredicate2 | bind-only | step_0
CertA185764.classify | bind-only | step_0
CertA185764.T | bind-only | step_0
CertA185764.initial | bind-only | initial_distribution
CertA185764.W | bind-only | vector_0
CertA185764.step_0 | bind-only | transitions
CertA185764.step_1 | bind-only | transitions
CertA185764.step_2 | bind-only | transitions
CertA185764.step_3 | bind-only | transitions
CertA185764.step_4 | bind-only | transitions
CertA185764.step_5 | bind-only | transitions
CertA185764.step_6 | bind-only | transitions
CertA185764.step_7 | bind-only | transitions
CertA185764.step_8 | bind-only | transitions
CertA185764.step_9 | bind-only | transitions
CertA185764.step_10 | bind-only | transitions
CertA185764.step_11 | bind-only | transitions
CertA185764.step_12 | bind-only | transitions
CertA185764.step_13 | bind-only | transitions
CertA185764.step_14 | bind-only | transitions
CertA185764.step_15 | bind-only | transitions
CertA185764.step_16 | bind-only | transitions
CertA185764.step_17 | bind-only | transitions
CertA185764.step_18 | bind-only | transitions
CertA185764.step_19 | bind-only | transitions
CertA185764.step_20 | bind-only | transitions
CertA185764.step_21 | bind-only | transitions
CertA185764.step_22 | bind-only | transitions
CertA185764.step_23 | bind-only | transitions
CertA185764.step_24 | bind-only | transitions
CertA185764.step_25 | bind-only | transitions
CertA185764.step_26 | bind-only | transitions
CertA185764.step_27 | bind-only | transitions
CertA185764.step_28 | bind-only | transitions
CertA185764.step_29 | bind-only | transitions
CertA185764.step_30 | bind-only | transitions
CertA185764.step_31 | bind-only | transitions
CertA185764.vector_0 | bind-only | powers_table
CertA185764.vector_1 | bind-only | powers_table
CertA185764.vector_2 | bind-only | powers_table
CertA185764.vector_3 | bind-only | powers_table
CertA185764.vector_4 | bind-only | powers_table
CertA185764.vector_5 | bind-only | powers_table
CertA185764.vector_6 | bind-only | powers_table
CertA185764.vector_7 | bind-only | powers_table
CertA185764.vector_8 | bind-only | powers_table
CertA185764.vector_9 | bind-only | powers_table
CertA185764.polynomial | bind-only | power_polynomial
CertA185764.initial_distribution | bind-only | count_transfer
CertA185764.vector_zero | bind-only | powers_table
TraceSeries.ogf_A185764 | bind-only | result
block | bind-only | valid
valid | bind-only | count
count | bind-only | generatingSeries
generatingSeries | bind-only | claim
claim | bind-only | result
transitions | bind-only | count_transfer
trace_decode | bind-only | source_card
source_card | content | count_transfer
count_transfer | content | count_1
powers_table | bind-only | power_polynomial
coefficients | bind-only | power_polynomial
power_polynomial | bind-only | recurrence
count_1 | bind-only | recurrence
count_2 | bind-only | recurrence
count_3 | bind-only | recurrence
count_4 | bind-only | recurrence
count_5 | bind-only | recurrence
count_6 | bind-only | recurrence
count_7 | bind-only | recurrence
count_8 | bind-only | recurrence
count_9 | bind-only | recurrence
count_10 | bind-only | recurrence
recurrence | content | result
result | content | none (settling result)
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.IntervalCases
import Mathlib.LinearAlgebra.Matrix.Trace
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence

/-- The contiguous 2-by-2 block with upper-left corner (i,j), in integers. -/
def block {n : ℕ} (a : (Matrix (Fin (n + 1)) (Fin 5) (Fin 2))) (i : Fin n) (j : Fin 4) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun u v => ((a (if u = 0 then i.castSucc else i.succ)
    (if v = 0 then j.castSucc else j.succ)).val : ℤ)


open D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
section

open scoped BigOperators
namespace CertA185764
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private def trace (a b : Fin 32) (j : Fin 4) : ℤ :=
 Matrix.trace (block (n := 1)
  (fun i => if i.val = 0 then (finFunctionFinEquiv.symm a : Fin 5 → Fin 2)
   else (finFunctionFinEquiv.symm b : Fin 5 → Fin 2)) 0 j)
private instance decidableRowPredicate1 : DecidableRel (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) := fun a b =>
 decidable_of_iff (∀ j j' : Fin 4, j'.val = j.val + 1 →
   ((((finFunctionFinEquiv.symm a : Fin 5 → Fin 2) j.castSucc).val : ℤ) + (((finFunctionFinEquiv.symm b : Fin 5 → Fin 2) j.succ).val : ℤ)) ≠ ((((finFunctionFinEquiv.symm a : Fin 5 → Fin 2) j'.castSucc).val : ℤ) + (((finFunctionFinEquiv.symm b : Fin 5 → Fin 2) j'.succ).val : ℤ)))
   (by simp [pairOK, trace, block, Matrix.trace, Matrix.diag, Fin.sum_univ_two])
private instance decidableRowPredicate2 (a b c : Fin 32) : Decidable ((tripleOK trace) a b c) :=
 decidable_of_iff (∀ j : Fin 4,
   ((((finFunctionFinEquiv.symm a : Fin 5 → Fin 2) j.castSucc).val : ℤ) + (((finFunctionFinEquiv.symm b : Fin 5 → Fin 2) j.succ).val : ℤ)) ≠ ((((finFunctionFinEquiv.symm b : Fin 5 → Fin 2) j.castSucc).val : ℤ) + (((finFunctionFinEquiv.symm c : Fin 5 → Fin 2) j.succ).val : ℤ)))
   (by simp [tripleOK, trace, block, Matrix.trace, Matrix.diag, Fin.sum_univ_two])
private def classify (a b : (Fin 32)) : (Fin 52) :=
 (![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 19, 0, 0, 0, 0, 0, 0, 0, 0, 10, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 6, 45, 36, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 5, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 29, 48, 3, 0, 51, 0, 0, 12, 39, 42, 9, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 27, 0, 0, 0, 0, 30, 21, 16, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 26, 25, 0, 0, 0, 0, 0, 0, 34, 17, 20, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 16, 21, 30, 0, 0],
 ![2, 49, 28, 23, 0, 0, 0, 0, 8, 43, 38, 13, 0, 0, 50, 1, 0, 0, 0, 0, 0, 0, 0, 0, 9, 42, 39, 12, 0, 0, 51, 0],
 ![0, 0, 0, 0, 14, 37, 44, 7, 4, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 46, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 18, 33, 0, 0, 0, 0, 40, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 10, 0, 0, 0, 0],
 ![0, 0, 0, 0, 10, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 40, 0, 0, 0, 0, 33, 18, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 46, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 4, 7, 44, 37, 14, 0, 0, 0, 0],
 ![0, 51, 0, 0, 12, 39, 42, 9, 0, 0, 0, 0, 0, 0, 0, 0, 1, 50, 0, 0, 13, 38, 43, 8, 0, 0, 0, 0, 23, 28, 49, 2],
 ![0, 0, 30, 21, 16, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 20, 17, 34, 0, 0, 0, 0, 0, 0, 25, 26, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 16, 21, 30, 0, 0, 0, 0, 27, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 9, 42, 39, 12, 0, 0, 51, 0, 3, 48, 29, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 5, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 36, 45, 6, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 10, 0, 0, 0, 0, 0, 0, 0, 0, 19, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 19, 0, 0, 0, 0, 0, 0, 0, 0, 10, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 6, 45, 36, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 5, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 29, 48, 3, 0, 51, 0, 0, 12, 39, 42, 9, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 27, 0, 0, 0, 0, 30, 21, 16, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 26, 25, 0, 0, 0, 0, 0, 0, 34, 17, 20, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 16, 21, 30, 0, 0],
 ![2, 49, 28, 23, 0, 0, 0, 0, 8, 43, 38, 13, 0, 0, 50, 1, 0, 0, 0, 0, 0, 0, 0, 0, 9, 42, 39, 12, 0, 0, 51, 0],
 ![0, 0, 0, 0, 14, 37, 44, 7, 4, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 46, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 18, 33, 0, 0, 0, 0, 40, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 10, 0, 0, 0, 0],
 ![0, 0, 0, 0, 10, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 40, 0, 0, 0, 0, 33, 18, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 46, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 4, 7, 44, 37, 14, 0, 0, 0, 0],
 ![0, 51, 0, 0, 12, 39, 42, 9, 0, 0, 0, 0, 0, 0, 0, 0, 1, 50, 0, 0, 13, 38, 43, 8, 0, 0, 0, 0, 23, 28, 49, 2],
 ![0, 0, 30, 21, 16, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 20, 17, 34, 0, 0, 0, 0, 0, 0, 25, 26, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 16, 21, 30, 0, 0, 0, 0, 27, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 9, 42, 39, 12, 0, 0, 51, 0, 3, 48, 29, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 5, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 36, 45, 6, 0, 0, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 10, 0, 0, 0, 0, 0, 0, 0, 0, 19, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : (Fin 32) → (Fin 32) → (Fin 52)) a b
private def T : Matrix (Fin 52) (Fin 52) ℤ :=
 !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1;
 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1;
 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0;
 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0;
 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0;
 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
private def initial : (Fin 52) → ℤ := ![8, 4, 4, 4, 4, 8, 4, 4, 4, 8, 8, 4, 8, 4, 4, 4, 8, 4, 4, 4, 4, 8, 4, 4, 4, 4, 4, 4, 4, 4, 8, 4, 4, 4, 4, 8, 4, 4, 4, 8, 4, 8, 8, 4, 4, 4, 8, 4, 4, 4, 4, 8]
private def W : Fin 11 → (Fin 52) → ℤ :=
 ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
 ![2, 2, 2, 2, 2, 2, 4, 2, 4, 2, 4, 6, 4, 6, 2, 4, 2, 4, 2, 4, 2, 2, 2, 2, 2, 2, 4, 4, 6, 6, 4, 4, 8, 4, 10, 6, 12, 6, 16, 10, 12, 8, 2, 4, 2, 4, 4, 4, 2, 2, 4, 4],
 ![12, 12, 12, 12, 6, 6, 30, 12, 30, 18, 20, 28, 20, 28, 8, 22, 6, 12, 6, 12, 6, 6, 8, 8, 6, 6, 20, 20, 24, 24, 12, 12, 48, 20, 56, 36, 60, 24, 72, 48, 60, 42, 6, 12, 6, 12, 12, 12, 6, 6, 24, 24],
 ![60, 60, 62, 62, 26, 26, 150, 62, 150, 88, 94, 136, 94, 136, 42, 110, 18, 36, 18, 36, 26, 26, 42, 42, 18, 18, 104, 104, 128, 128, 50, 50, 240, 104, 272, 168, 306, 128, 356, 228, 284, 192, 18, 36, 18, 36, 50, 50, 18, 18, 124, 124],
 ![276, 276, 286, 286, 122, 122, 706, 286, 706, 420, 430, 616, 430, 616, 186, 494, 76, 152, 76, 152, 122, 122, 186, 186, 76, 76, 506, 506, 612, 612, 250, 250, 1182, 506, 1352, 846, 1474, 612, 1724, 1112, 1356, 928, 76, 152, 76, 152, 250, 250, 76, 76, 602, 602],
 ![1334, 1334, 1358, 1358, 582, 582, 3330, 1358, 3330, 1972, 2086, 3008, 2086, 3008, 922, 2426, 372, 744, 372, 744, 582, 582, 922, 922, 372, 372, 2420, 2420, 2916, 2916, 1160, 1160, 5638, 2420, 6436, 4016, 6992, 2916, 8152, 5236, 6396, 4358, 372, 744, 372, 744, 1160, 1160, 372, 372, 2826, 2826],
 ![6382, 6382, 6444, 6444, 2792, 2792, 15848, 6444, 15848, 9404, 9972, 14360, 9972, 14360, 4388, 11568, 1742, 3484, 1742, 3484, 2792, 2792, 4388, 4388, 1742, 1742, 11482, 11482, 13826, 13826, 5568, 5568, 26802, 11482, 30640, 19158, 33220, 13826, 38788, 24962, 30468, 20802, 1742, 3484, 1742, 3484, 5568, 5568, 1742, 1742, 13492, 13492],
 ![30286, 30286, 30774, 30774, 13224, 13224, 75602, 30774, 75602, 44828, 47348, 68248, 47348, 68248, 20900, 55024, 8360, 16720, 8360, 16720, 13224, 13224, 20900, 20900, 8360, 8360, 54808, 54808, 65954, 65954, 26400, 26400, 127830, 54808, 146044, 91236, 158308, 65954, 184708, 118754, 144960, 98880, 8360, 16720, 8360, 16720, 26400, 26400, 8360, 8360, 64120, 64120],
 ![144550, 144550, 146228, 146228, 63168, 63168, 359436, 146228, 359436, 213208, 225932, 325528, 225932, 325528, 99596, 262360, 39624, 79248, 39624, 79248, 63168, 63168, 99596, 99596, 39624, 39624, 260508, 260508, 313696, 313696, 125988, 125988, 607870, 260508, 694724, 434216, 753380, 313696, 879368, 565672, 690556, 471266, 39624, 79248, 39624, 79248, 125988, 125988, 39624, 39624, 305654, 305654],
 ![687118, 687118, 697198, 697198, 300132, 300132, 1713282, 697198, 1713282, 1016084, 1074104, 1547944, 1074104, 1547944, 473840, 1247812, 189156, 378312, 189156, 378312, 300132, 300132, 473840, 473840, 189156, 189156, 1241808, 1241808, 1494640, 1494640, 599144, 599144, 2896908, 1241808, 3310200, 2068392, 3588424, 1494640, 4187568, 2692928, 3287160, 2242724, 189156, 378312, 189156, 378312, 599144, 599144, 189156, 189156, 1454424, 1454424],
 ![3275220, 3275220, 3316828, 3316828, 1430964, 1430964, 8151932, 3316828, 8151932, 4835104, 5119476, 7377024, 5119476, 7377024, 2257548, 5946060, 899276, 1798552, 899276, 1798552, 1430964, 1430964, 2257548, 2257548, 899276, 899276, 5908574, 5908574, 7113814, 7113814, 2854834, 2854834, 13785628, 5908574, 15754108, 9845534, 17082462, 7113814, 19937296, 12823482, 15654212, 10681940, 899276, 1798552, 899276, 1798552, 2854834, 2854834, 899276, 899276, 6927830, 6927830]]

private theorem step_0 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 0 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 0 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 0 b) k := by decide +kernel
private theorem step_1 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 1 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 1 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 1 b) k := by decide +kernel
private theorem step_2 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 2 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 2 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 2 b) k := by decide +kernel
private theorem step_3 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 3 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 3 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 3 b) k := by decide +kernel
private theorem step_4 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 4 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 4 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 4 b) k := by decide +kernel
private theorem step_5 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 5 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 5 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 5 b) k := by decide +kernel
private theorem step_6 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 6 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 6 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 6 b) k := by decide +kernel
private theorem step_7 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 7 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 7 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 7 b) k := by decide +kernel
private theorem step_8 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 8 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 8 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 8 b) k := by decide +kernel
private theorem step_9 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 9 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 9 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 9 b) k := by decide +kernel
private theorem step_10 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 10 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 10 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 10 b) k := by decide +kernel
private theorem step_11 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 11 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 11 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 11 b) k := by decide +kernel
private theorem step_12 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 12 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 12 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 12 b) k := by decide +kernel
private theorem step_13 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 13 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 13 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 13 b) k := by decide +kernel
private theorem step_14 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 14 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 14 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 14 b) k := by decide +kernel
private theorem step_15 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 15 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 15 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 15 b) k := by decide +kernel
private theorem step_16 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 16 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 16 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 16 b) k := by decide +kernel
private theorem step_17 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 17 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 17 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 17 b) k := by decide +kernel
private theorem step_18 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 18 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 18 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 18 b) k := by decide +kernel
private theorem step_19 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 19 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 19 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 19 b) k := by decide +kernel
private theorem step_20 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 20 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 20 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 20 b) k := by decide +kernel
private theorem step_21 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 21 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 21 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 21 b) k := by decide +kernel
private theorem step_22 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 22 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 22 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 22 b) k := by decide +kernel
private theorem step_23 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 23 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 23 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 23 b) k := by decide +kernel
private theorem step_24 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 24 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 24 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 24 b) k := by decide +kernel
private theorem step_25 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 25 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 25 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 25 b) k := by decide +kernel
private theorem step_26 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 26 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 26 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 26 b) k := by decide +kernel
private theorem step_27 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 27 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 27 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 27 b) k := by decide +kernel
private theorem step_28 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 28 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 28 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 28 b) k := by decide +kernel
private theorem step_29 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 29 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 29 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 29 b) k := by decide +kernel
private theorem step_30 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 30 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 30 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 30 b) k := by decide +kernel
private theorem step_31 : ∀ b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) 31 b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 31 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 31 b) k := by decide +kernel

private theorem vector_0 : W 1 = T.mulVec (W 0) := by decide +kernel
private theorem vector_1 : W 2 = T.mulVec (W 1) := by decide +kernel
private theorem vector_2 : W 3 = T.mulVec (W 2) := by decide +kernel
private theorem vector_3 : W 4 = T.mulVec (W 3) := by decide +kernel
private theorem vector_4 : W 5 = T.mulVec (W 4) := by decide +kernel
private theorem vector_5 : W 6 = T.mulVec (W 5) := by decide +kernel
private theorem vector_6 : W 7 = T.mulVec (W 6) := by decide +kernel
private theorem vector_7 : W 8 = T.mulVec (W 7) := by decide +kernel
private theorem vector_8 : W 9 = T.mulVec (W 8) := by decide +kernel
private theorem vector_9 : W 10 = T.mulVec (W 9) := by decide +kernel
private theorem polynomial : ∀ k : (Fin 52), W 10 k = (1:ℤ) * W 9 k + (17:ℤ) * W 8 k + (9:ℤ) * W 7 k + (-22:ℤ) * W 6 k + (-1:ℤ) * W 5 k + (1:ℤ) * W 4 k + (-6:ℤ) * W 3 k := by decide +kernel
private theorem initial_distribution : ∀ k : (Fin 52),
 (∑ a : (Fin 32), ∑ b : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) a b ∧ classify a b = k then (1:ℤ) else 0) = initial k := by decide +kernel

private theorem vector_zero : W 0 = (1 : Fin 52 → ℤ) := by decide +kernel

end CertA185764
end

section
namespace TraceSeries
private theorem ogf_A185764 (a : ℕ → ℕ) (h1 : a 1 = 264) (h2 : a 2 = 1128) (h3 : a 3 = 5272) (h4 : a 4 = 24832) (h5 : a 5 = 118248) (h6 : a 6 = 562800) (h7 : a 7 = 2680000) (h8 : a 8 = 12760448) (h9 : a 9 = 60758008)
 (hr : ∀ n : ℕ, 10 ≤ n → (a n : ℤ) = (a (n - 1) : ℤ) + 17 * (a (n - 2) : ℤ) + 9 * (a (n - 3) : ℤ) - 22 * (a (n - 4) : ℤ) - (a (n - 5) : ℤ) + (a (n - 6) : ℤ) - 6 * (a (n - 7) : ℤ)) :
 (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (a n : ℚ))) = (let X : PowerSeries ℚ := PowerSeries.X; (264 * X ^ 1 + 864 * X ^ 2 - 344 * X ^ 3 - 1992 * X ^ 4 - 552 * X ^ 5 + 40 * X ^ 6 + 344 * X ^ 7 + 648 * X ^ 8 + 144 * X ^ 9) * (1 - X ^ 1 - 17 * X ^ 2 - 9 * X ^ 3 + 22 * X ^ 4 + X ^ 5 - X ^ 6 + 6 * X ^ 7)⁻¹) := by
 let X : PowerSeries ℚ := PowerSeries.X
 let F := (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (a n : ℚ)))
 have hp : F * (1 - X ^ 1 - 17 * X ^ 2 - 9 * X ^ 3 + 22 * X ^ 4 + X ^ 5 - X ^ 6 + 6 * X ^ 7) = (264 * X ^ 1 + 864 * X ^ 2 - 344 * X ^ 3 - 1992 * X ^ 4 - 552 * X ^ 5 + 40 * X ^ 6 + 344 * X ^ 7 + 648 * X ^ 8 + 144 * X ^ 9) := by
   have he : F * (1 - X ^ 1 - 17 * X ^ 2 - 9 * X ^ 3 + 22 * X ^ 4 + X ^ 5 - X ^ 6 + 6 * X ^ 7) = F - (F * X ^ 1) - 17 * (F * X ^ 2) - 9 * (F * X ^ 3) + 22 * (F * X ^ 4) + (F * X ^ 5) - (F * X ^ 6) + 6 * (F * X ^ 7) := by ring
   rw [he]
   apply PowerSeries.ext
   intro n
   simp only [X,map_sub,map_add,PowerSeries.coeff_ofNat_mul,
     PowerSeries.coeff_mul_X_pow',PowerSeries.coeff_X_pow,PowerSeries.coeff_X,
     F,PowerSeries.coeff_mk]
   by_cases hn : n < 10
   · interval_cases n <;> norm_num [h1,h2,h3,h4,h5,h6,h7,h8,h9,X]
   · have hnr : 10 ≤ n := by exact Nat.le_of_not_lt hn
     have hq : (a n : ℚ) = (a (n - 1) : ℚ) + 17 * (a (n - 2) : ℚ) + 9 * (a (n - 3) : ℚ) - 22 * (a (n - 4) : ℚ) - (a (n - 5) : ℚ) + (a (n - 6) : ℚ) - 6 * (a (n - 7) : ℚ) := by exact_mod_cast hr n hnr
     simp only [ite_eq_left (show 1 ≤ n by omega),
       ite_eq_left (show 2 ≤ n by omega),
       ite_eq_left (show 3 ≤ n by omega),
       ite_eq_left (show 4 ≤ n by omega),
       ite_eq_left (show 5 ≤ n by omega),
       ite_eq_left (show 6 ≤ n by omega),
       ite_eq_left (show 7 ≤ n by omega),
       ite_eq_left (show 8 ≤ n by omega),
       ite_eq_left (show 9 ≤ n by omega),
       ite_eq_right (show ¬ n = 0 by omega),
       ite_eq_right (show ¬ n = 1 by omega),
       ite_eq_right (show ¬ n - 1 = 0 by omega),
       ite_eq_right (show ¬ n = 2 by omega),
       ite_eq_right (show ¬ n - 2 = 0 by omega),
       ite_eq_right (show ¬ n = 3 by omega),
       ite_eq_right (show ¬ n - 3 = 0 by omega),
       ite_eq_right (show ¬ n = 4 by omega),
       ite_eq_right (show ¬ n - 4 = 0 by omega),
       ite_eq_right (show ¬ n = 5 by omega),
       ite_eq_right (show ¬ n - 5 = 0 by omega),
       ite_eq_right (show ¬ n = 6 by omega),
       ite_eq_right (show ¬ n - 6 = 0 by omega),
       ite_eq_right (show ¬ n = 7 by omega),
       ite_eq_right (show ¬ n - 7 = 0 by omega),
       ite_eq_right (show ¬ n = 8 by omega),
       ite_eq_right (show ¬ n - 8 = 0 by omega),
       ite_eq_right (show ¬ n = 9 by omega),
       ite_eq_right (show ¬ n - 9 = 0 by omega)]
     linarith [hq]
 change F = (264 * X ^ 1 + 864 * X ^ 2 - 344 * X ^ 3 - 1992 * X ^ 4 - 552 * X ^ 5 + 40 * X ^ 6 + 344 * X ^ 7 + 648 * X ^ 8 + 144 * X ^ 9) * (1 - X ^ 1 - 17 * X ^ 2 - 9 * X ^ 3 + 22 * X ^ 4 + X ^ 5 - X ^ 6 + 6 * X ^ 7)⁻¹
 calc
  F = (F * (1 - X ^ 1 - 17 * X ^ 2 - 9 * X ^ 3 + 22 * X ^ 4 + X ^ 5 - X ^ 6 + 6 * X ^ 7)) * (1 - X ^ 1 - 17 * X ^ 2 - 9 * X ^ 3 + 22 * X ^ 4 + X ^ 5 - X ^ 6 + 6 * X ^ 7)⁻¹ := by
    rw [mul_assoc,PowerSeries.mul_inv_cancel _ (by norm_num [X]),mul_one]
  _ = (264 * X ^ 1 + 864 * X ^ 2 - 344 * X ^ 3 - 1992 * X ^ 4 - 552 * X ^ 5 + 40 * X ^ 6 + 344 * X ^ 7 + 648 * X ^ 8 + 144 * X ^ 9) * (1 - X ^ 1 - 17 * X ^ 2 - 9 * X ^ 3 + 22 * X ^ 4 + X ^ 5 - X ^ 6 + 6 * X ^ 7)⁻¹ := by rw [hp]

end TraceSeries
end

section


/-- Exactly vertical and horizontal neighbors of contiguous blocks. -/
def valid {n : ℕ} (a : (Matrix (Fin (n + 1)) (Fin 5) (Fin 2))) : Prop :=
  (∀ (i i' : Fin n) (j : Fin 4),
    i'.val = i.val + 1 → Matrix.trace (block a i j) ≠ Matrix.trace (block a i' j)) ∧
  (∀ (i : Fin n) (j j' : Fin 4),
    j'.val = j.val + 1 → Matrix.trace (block a i j) ≠ Matrix.trace (block a i j'))

/-- The OEIS count, directly on the source arrays. -/
noncomputable def count (n : ℕ) : ℕ := Nat.card {a : (Matrix (Fin (n + 1)) (Fin 5) (Fin 2)) // valid a}

/-- The source OGF starts at n=1; its constant coefficient is zero. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (count n : ℚ))

/-- The published recurrence, initial terms and conjectural OGF. -/
def claim : Prop :=
  count 1 = 264 ∧ count 2 = 1128 ∧ count 3 = 5272 ∧
  count 4 = 24832 ∧ count 5 = 118248 ∧ count 6 = 562800 ∧
  count 7 = 2680000 ∧ count 8 = 12760448 ∧ count 9 = 60758008 ∧
  (∀ n : ℕ, 10 ≤ n →
    (count n : ℤ) = (count (n - 1) : ℤ) + 17 * (count (n - 2) : ℤ) +
      9 * (count (n - 3) : ℤ) - 22 * (count (n - 4) : ℤ) -
      (count (n - 5) : ℤ) + (count (n - 6) : ℤ) - 6 * (count (n - 7) : ℤ)) ∧
  (let X : PowerSeries ℚ := PowerSeries.X
   generatingSeries = (8 * X * (33 + 108 * X - 43 * X ^ 2 - 249 * X ^ 3 - 69 * X ^ 4 +
      5 * X ^ 5 + 43 * X ^ 6 + 81 * X ^ 7 + 18 * X ^ 8)) *
     (1 - X - 17 * X ^ 2 - 9 * X ^ 3 + 22 * X ^ 4 + X ^ 5 - X ^ 6 + 6 * X ^ 7)⁻¹)


open scoped BigOperators
open CertA185764
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem transitions : ∀ a b : (Fin 32), (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) a b → ∀ k : (Fin 52),
 (∑ c : (Fin 32), if (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) a b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify a b) k := by
 intro a
 fin_cases a <;> first
 | exact step_0
 | exact step_1
 | exact step_2
 | exact step_3
 | exact step_4
 | exact step_5
 | exact step_6
 | exact step_7
 | exact step_8
 | exact step_9
 | exact step_10
 | exact step_11
 | exact step_12
 | exact step_13
 | exact step_14
 | exact step_15
 | exact step_16
 | exact step_17
 | exact step_18
 | exact step_19
 | exact step_20
 | exact step_21
 | exact step_22
 | exact step_23
 | exact step_24
 | exact step_25
 | exact step_26
 | exact step_27
 | exact step_28
 | exact step_29
 | exact step_30
 | exact step_31

private theorem trace_decode (n : ℕ) (a : (Matrix (Fin (n + 1)) (Fin 5) (Fin 2))) :
 valid a ↔ arrayOK trace (fun j j' : Fin 4 => j'.val = j.val+1) n
    (fun i => (finFunctionFinEquiv (a i) : (Fin 32))) := by
 simp [valid,block,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
   arrayOK,trace]

private theorem source_card (n : ℕ) :
 count n = Nat.card {a : Fin (n+1) → (Fin 32) // good (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) (tripleOK trace) (List.ofFn a)} := by
 let e : ((Matrix (Fin (n + 1)) (Fin 5) (Fin 2))) ≃ (Fin (n+1) → (Fin 32)) := Equiv.piCongrRight (fun _ => finFunctionFinEquiv)
 unfold count
 apply Nat.card_congr
 apply e.subtypeEquiv
 intro a
 rw [trace_decode,arrayOKIffGood]
 rfl

private theorem count_transfer (n : ℕ) :
 (count (n+1) : ℤ) = dotProduct initial ((T^n).mulVec (1 : Fin 52 → ℤ)) := by
 rw [source_card]
 refine cardMatrix (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) (tripleOK trace) classify T initial ?_ ?_ n
 · intro a b hab k
   convert transitions a b hab k using 1
   apply Finset.sum_congr rfl
   intro c _
   by_cases h : (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) a b c ∧ classify b c = k <;> simp [h]
 · intro k
   convert initial_distribution k using 1
   apply Finset.sum_congr rfl
   intro a _
   apply Finset.sum_congr rfl
   intro b _
   by_cases h : (pairOK trace (fun j j' : Fin 4 => j'.val = j.val + 1)) a b ∧ classify a b = k <;> simp [h]

private theorem powers_table : ∀ k : Fin 11, (T^k.val).mulVec (1 : Fin 52 → ℤ) = W k := by
 apply tabulatedPowers T 10 W vector_zero
 intro k
 fin_cases k <;> first
 | exact vector_0
 | exact vector_1
 | exact vector_2
 | exact vector_3
 | exact vector_4
 | exact vector_5
 | exact vector_6
 | exact vector_7
 | exact vector_8
 | exact vector_9

private def coefficients : Fin 7 → ℤ := ![-6, 1, -1, -22, 9, 17, 1]

private theorem power_polynomial : (T^10).mulVec (1 : Fin 52 → ℤ) =
 ∑ j : Fin 7, coefficients j • (T^(3+j.val)).mulVec (1 : Fin 52 → ℤ) := by
 calc
  _ = W 10 := powers_table 10
  _ = ∑ j : Fin 7, coefficients j • W ⟨3+j.val,by omega⟩ := by
   ext k
   have hp := polynomial k
   norm_num [coefficients,Fin.sum_univ_succ,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
   linear_combination hp
  _ = _ := by
   apply Finset.sum_congr rfl
   intro j _
   rw [powers_table ⟨3+j.val,by omega⟩]

private theorem count_1 : count 1 = 264 := by
 have h := count_transfer 0
 rw [powers_table ⟨0,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_2 : count 2 = 1128 := by
 have h := count_transfer 1
 rw [powers_table ⟨1,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_3 : count 3 = 5272 := by
 have h := count_transfer 2
 rw [powers_table ⟨2,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_4 : count 4 = 24832 := by
 have h := count_transfer 3
 rw [powers_table ⟨3,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_5 : count 5 = 118248 := by
 have h := count_transfer 4
 rw [powers_table ⟨4,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_6 : count 6 = 562800 := by
 have h := count_transfer 5
 rw [powers_table ⟨5,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_7 : count 7 = 2680000 := by
 have h := count_transfer 6
 rw [powers_table ⟨6,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_8 : count 8 = 12760448 := by
 have h := count_transfer 7
 rw [powers_table ⟨7,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_9 : count 9 = 60758008 := by
 have h := count_transfer 8
 rw [powers_table ⟨8,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_10 : count 10 = 289298976 := by
 have h := count_transfer 9
 rw [powers_table ⟨9,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem recurrence : ∀ n : ℕ, 10 ≤ n → (count n : ℤ) = (count (n - 1) : ℤ) + 17 * (count (n - 2) : ℤ) + 9 * (count (n - 3) : ℤ) - 22 * (count (n - 4) : ℤ) - (count (n - 5) : ℤ) + (count (n - 6) : ℤ) - 6 * (count (n - 7) : ℤ) := by
 intro n hn
 by_cases hsmall : n < 11
 · interval_cases n <;> norm_num [count_1,count_2,count_3,count_4,count_5,count_6,count_7,count_8,count_9,count_10] at *
 · have hn' : 11 ≤ n := by exact Nat.le_of_not_lt hsmall
   have hr := scalarRelationShift T initial 7 3 coefficients power_polynomial (n-11)
   have hh (j : Fin 7) :
      dotProduct initial ((T^(n-11+3+j.val)).mulVec (1 : Fin 52 → ℤ)) =
       (count (n-11+3+j.val+1) : ℤ) := (count_transfer _).symm
   have he : n-11+3+7+1 = n := by omega
   rw [← count_transfer,he] at hr
   simp_rw [hh] at hr
   have hidx (j : Fin 7) : n-11+3+j.val+1 = n-(7-j.val) := by omega
   simp_rw [hidx] at hr
   norm_num [coefficients,Fin.sum_univ_succ] at hr
   linear_combination hr


theorem result : claim := by
 unfold claim
 refine ⟨count_1, count_2, count_3, count_4, count_5, count_6, count_7, count_8, count_9, recurrence, ?_⟩
 have h := TraceSeries.ogf_A185764 count count_1 count_2 count_3 count_4 count_5 count_6 count_7 count_8 count_9 recurrence
 change (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (count n : ℚ))) = _
 simp only [pow_one] at h
 convert h using 1 <;> ring

end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence
