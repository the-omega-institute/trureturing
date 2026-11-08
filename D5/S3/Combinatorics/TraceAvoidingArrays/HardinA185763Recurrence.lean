/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The literal binary array counts satisfy the published recurrence and series. -/

/-
admission_basis: open-problem-resolution (#21315; Proved)
proof_shape: content: result, via the literal-array cardinality bridge and continuation induction
escape_witness: none (the settling result uses the external open-problem basis)
Direct frozen dependencies: none. Pinned Mathlib supplies matrices, finite sums and cardinalities.
All auxiliary theorems are consumed; arithmetic certificates and normalization helpers are bind-only.
The source arrays use Matrix directly; their encoded-row traces apply Matrix.trace to block. Row predicates use pairOK and tripleOK.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21914
The source is OEIS A185761--A185764; literature-search completeness is ASSUMED-UNVERIFIED.
Declaration classifications (name | proof_shape | consumer):
CertA185763.trace | bind-only | decidableRowPredicate1
CertA185763.decidableRowPredicate1 | bind-only | step_0
CertA185763.decidableRowPredicate2 | bind-only | step_0
CertA185763.classify | bind-only | step_0
CertA185763.T | bind-only | step_0
CertA185763.initial | bind-only | initial_distribution
CertA185763.W | bind-only | vector_0
CertA185763.step_0 | bind-only | transitions
CertA185763.step_1 | bind-only | transitions
CertA185763.step_2 | bind-only | transitions
CertA185763.step_3 | bind-only | transitions
CertA185763.step_4 | bind-only | transitions
CertA185763.step_5 | bind-only | transitions
CertA185763.step_6 | bind-only | transitions
CertA185763.step_7 | bind-only | transitions
CertA185763.step_8 | bind-only | transitions
CertA185763.step_9 | bind-only | transitions
CertA185763.step_10 | bind-only | transitions
CertA185763.step_11 | bind-only | transitions
CertA185763.step_12 | bind-only | transitions
CertA185763.step_13 | bind-only | transitions
CertA185763.step_14 | bind-only | transitions
CertA185763.step_15 | bind-only | transitions
CertA185763.vector_0 | bind-only | powers_table
CertA185763.vector_1 | bind-only | powers_table
CertA185763.vector_2 | bind-only | powers_table
CertA185763.vector_3 | bind-only | powers_table
CertA185763.vector_4 | bind-only | powers_table
CertA185763.vector_5 | bind-only | powers_table
CertA185763.vector_6 | bind-only | powers_table
CertA185763.vector_7 | bind-only | powers_table
CertA185763.polynomial | bind-only | power_polynomial
CertA185763.initial_distribution | bind-only | count_transfer
CertA185763.vector_zero | bind-only | powers_table
TraceSeries.ogf_A185763 | bind-only | result
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
recurrence | content | result
result | content | none (settling result)
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.IntervalCases
import Mathlib.LinearAlgebra.Matrix.Trace
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence

/-- The contiguous 2-by-2 block with upper-left corner (i,j), in integers. -/
def block {n : ℕ} (a : (Matrix (Fin (n + 1)) (Fin 4) (Fin 2))) (i : Fin n) (j : Fin 3) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun u v => ((a (if u = 0 then i.castSucc else i.succ)
    (if v = 0 then j.castSucc else j.succ)).val : ℤ)


open D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
section

open scoped BigOperators
namespace CertA185763
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private def trace (a b : Fin 16) (j : Fin 3) : ℤ :=
 Matrix.trace (block (n := 1)
  (fun i => if i.val = 0 then (finFunctionFinEquiv.symm a : Fin 4 → Fin 2)
   else (finFunctionFinEquiv.symm b : Fin 4 → Fin 2)) 0 j)
private instance decidableRowPredicate1 : DecidableRel (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) := fun _ _ => inferInstanceAs (Decidable (∀ j j' : Fin 3, _))
private instance decidableRowPredicate2 (a b c : (Fin 16)) : Decidable ((tripleOK trace) a b c) := inferInstanceAs (Decidable (∀ j : Fin 3, trace a b j ≠ trace b c j))
private def classify (a b : (Fin 16)) : (Fin 20) :=
 (![![0, 0, 0, 0, 4, 15, 0, 0, 0, 0, 10, 9, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 18, 1, 2, 17, 12, 7, 0, 0, 0, 0],
 ![0, 19, 0, 0, 6, 13, 16, 3, 0, 0, 0, 0, 7, 12, 17, 2],
 ![0, 0, 14, 5, 8, 11, 0, 0, 0, 0, 0, 0, 9, 10, 0, 0],
 ![0, 0, 10, 9, 0, 0, 0, 0, 0, 0, 11, 8, 5, 14, 0, 0],
 ![2, 17, 12, 7, 0, 0, 0, 0, 3, 16, 13, 6, 0, 0, 19, 0],
 ![0, 0, 0, 0, 7, 12, 17, 2, 1, 18, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 9, 10, 0, 0, 0, 0, 15, 4, 0, 0, 0, 0],
 ![0, 0, 0, 0, 4, 15, 0, 0, 0, 0, 10, 9, 0, 0, 0, 0],
 ![0, 0, 0, 0, 0, 0, 18, 1, 2, 17, 12, 7, 0, 0, 0, 0],
 ![0, 19, 0, 0, 6, 13, 16, 3, 0, 0, 0, 0, 7, 12, 17, 2],
 ![0, 0, 14, 5, 8, 11, 0, 0, 0, 0, 0, 0, 9, 10, 0, 0],
 ![0, 0, 10, 9, 0, 0, 0, 0, 0, 0, 11, 8, 5, 14, 0, 0],
 ![2, 17, 12, 7, 0, 0, 0, 0, 3, 16, 13, 6, 0, 0, 19, 0],
 ![0, 0, 0, 0, 7, 12, 17, 2, 1, 18, 0, 0, 0, 0, 0, 0],
 ![0, 0, 0, 0, 9, 10, 0, 0, 0, 0, 15, 4, 0, 0, 0, 0]] : (Fin 16) → (Fin 16) → (Fin 20)) a b
private def T : Matrix (Fin 20) (Fin 20) ℤ :=
 !![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1;
 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1;
 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1;
 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1;
 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0;
 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
private def initial : (Fin 20) → ℤ := ![4, 4, 8, 4, 4, 4, 4, 8, 4, 8, 8, 4, 8, 4, 4, 4, 4, 8, 4, 4]
private def W : Fin 9 → (Fin 20) → ℤ :=
 ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
 ![2, 2, 2, 2, 4, 2, 4, 2, 2, 2, 4, 6, 6, 10, 4, 8, 2, 2, 4, 4],
 ![6, 6, 12, 12, 14, 6, 14, 8, 6, 6, 20, 28, 24, 36, 12, 30, 6, 6, 12, 12],
 ![26, 26, 44, 44, 60, 26, 60, 34, 18, 18, 68, 100, 86, 136, 50, 118, 18, 18, 50, 50],
 ![86, 86, 178, 178, 204, 86, 204, 118, 76, 76, 272, 392, 334, 516, 182, 440, 76, 76, 182, 182],
 ![348, 348, 644, 644, 816, 348, 816, 468, 268, 268, 988, 1440, 1242, 1948, 706, 1680, 268, 268, 706, 706],
 ![1256, 1256, 2496, 2496, 2964, 1256, 2964, 1708, 1054, 1054, 3818, 5528, 4730, 7352, 2622, 6298, 1054, 1054, 2622, 2622],
 ![4872, 4872, 9262, 9262, 11454, 4872, 11454, 6582, 3878, 3878, 14194, 20632, 17744, 27732, 9988, 23854, 3878, 3878, 9988, 9988],
 ![18072, 18072, 35308, 35308, 42582, 18072, 42582, 24510, 14860, 14860, 54046, 78372, 67186, 104652, 37466, 89792, 14860, 14860, 37466, 37466]]

private theorem step_0 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 0 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 0 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 0 b) k := by decide
private theorem step_1 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 1 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 1 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 1 b) k := by decide
private theorem step_2 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 2 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 2 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 2 b) k := by decide
private theorem step_3 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 3 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 3 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 3 b) k := by decide
private theorem step_4 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 4 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 4 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 4 b) k := by decide
private theorem step_5 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 5 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 5 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 5 b) k := by decide
private theorem step_6 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 6 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 6 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 6 b) k := by decide
private theorem step_7 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 7 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 7 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 7 b) k := by decide
private theorem step_8 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 8 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 8 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 8 b) k := by decide
private theorem step_9 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 9 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 9 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 9 b) k := by decide
private theorem step_10 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 10 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 10 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 10 b) k := by decide
private theorem step_11 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 11 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 11 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 11 b) k := by decide
private theorem step_12 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 12 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 12 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 12 b) k := by decide
private theorem step_13 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 13 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 13 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 13 b) k := by decide
private theorem step_14 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 14 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 14 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 14 b) k := by decide
private theorem step_15 : ∀ b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) 15 b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 15 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 15 b) k := by decide

private theorem vector_0 : W 1 = T.mulVec (W 0) := by decide
private theorem vector_1 : W 2 = T.mulVec (W 1) := by decide
private theorem vector_2 : W 3 = T.mulVec (W 2) := by decide
private theorem vector_3 : W 4 = T.mulVec (W 3) := by decide
private theorem vector_4 : W 5 = T.mulVec (W 4) := by decide
private theorem vector_5 : W 6 = T.mulVec (W 5) := by decide
private theorem vector_6 : W 7 = T.mulVec (W 6) := by decide
private theorem vector_7 : W 8 = T.mulVec (W 7) := by decide
private theorem polynomial : ∀ k : (Fin 20), W 8 k = (1:ℤ) * W 7 k + (10:ℤ) * W 6 k + (3:ℤ) * W 5 k + (-5:ℤ) * W 4 k + (1:ℤ) * W 3 k := by decide
private theorem initial_distribution : ∀ k : (Fin 20),
 (∑ a : (Fin 16), ∑ b : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) a b ∧ classify a b = k then (1:ℤ) else 0) = initial k := by decide

private theorem vector_zero : W 0 = (1 : Fin 20 → ℤ) := by decide

end CertA185763
end

section
namespace TraceSeries
private theorem ogf_A185763 (a : ℕ → ℕ) (h1 : a 1 = 104) (h2 : a 2 = 368) (h3 : a 3 = 1408) (h4 : a 4 = 5272) (h5 : a 5 = 19992) (h6 : a 6 = 75192)
 (hr : ∀ n : ℕ, 7 ≤ n → (a n : ℤ) = (a (n - 1) : ℤ) + 10 * (a (n - 2) : ℤ) + 3 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ)) :
 (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (a n : ℚ))) = (let X : PowerSeries ℚ := PowerSeries.X; (104 * X ^ 1 + 264 * X ^ 2 - 128 * X ^ 4 + 56 * X ^ 5 - 8 * X ^ 6) * (1 - X ^ 1 - 10 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - X ^ 5)⁻¹) := by
 let X : PowerSeries ℚ := PowerSeries.X
 let F := (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (a n : ℚ)))
 have hp : F * (1 - X ^ 1 - 10 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - X ^ 5) = (104 * X ^ 1 + 264 * X ^ 2 - 128 * X ^ 4 + 56 * X ^ 5 - 8 * X ^ 6) := by
   have he : F * (1 - X ^ 1 - 10 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - X ^ 5) = F - (F * X ^ 1) - 10 * (F * X ^ 2) - 3 * (F * X ^ 3) + 5 * (F * X ^ 4) - (F * X ^ 5) := by ring
   rw [he]
   apply PowerSeries.ext
   intro n
   simp only [X,map_sub,map_add,PowerSeries.coeff_ofNat_mul,
     PowerSeries.coeff_mul_X_pow',PowerSeries.coeff_X_pow,PowerSeries.coeff_X,
     F,PowerSeries.coeff_mk]
   by_cases hn : n < 7
   · interval_cases n <;> norm_num [h1,h2,h3,h4,h5,h6,X]
   · have hnr : 7 ≤ n := by exact Nat.le_of_not_lt hn
     have hq : (a n : ℚ) = (a (n - 1) : ℚ) + 10 * (a (n - 2) : ℚ) + 3 * (a (n - 3) : ℚ) - 5 * (a (n - 4) : ℚ) + (a (n - 5) : ℚ) := by exact_mod_cast hr n hnr
     simp only [ite_eq_left (show 1 ≤ n by omega),
       ite_eq_left (show 2 ≤ n by omega),
       ite_eq_left (show 3 ≤ n by omega),
       ite_eq_left (show 4 ≤ n by omega),
       ite_eq_left (show 5 ≤ n by omega),
       ite_eq_left (show 6 ≤ n by omega),
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
       ite_eq_right (show ¬ n - 6 = 0 by omega)]
     linarith [hq]
 change F = (104 * X ^ 1 + 264 * X ^ 2 - 128 * X ^ 4 + 56 * X ^ 5 - 8 * X ^ 6) * (1 - X ^ 1 - 10 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - X ^ 5)⁻¹
 calc
  F = (F * (1 - X ^ 1 - 10 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - X ^ 5)) * (1 - X ^ 1 - 10 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - X ^ 5)⁻¹ := by
    rw [mul_assoc,PowerSeries.mul_inv_cancel _ (by norm_num [X]),mul_one]
  _ = (104 * X ^ 1 + 264 * X ^ 2 - 128 * X ^ 4 + 56 * X ^ 5 - 8 * X ^ 6) * (1 - X ^ 1 - 10 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - X ^ 5)⁻¹ := by rw [hp]

end TraceSeries
end

section


/-- Exactly vertical and horizontal neighbors of contiguous blocks. -/
def valid {n : ℕ} (a : (Matrix (Fin (n + 1)) (Fin 4) (Fin 2))) : Prop :=
  (∀ (i i' : Fin n) (j : Fin 3),
    i'.val = i.val + 1 → Matrix.trace (block a i j) ≠ Matrix.trace (block a i' j)) ∧
  (∀ (i : Fin n) (j j' : Fin 3),
    j'.val = j.val + 1 → Matrix.trace (block a i j) ≠ Matrix.trace (block a i j'))

/-- The OEIS count, directly on the source arrays. -/
noncomputable def count (n : ℕ) : ℕ := Nat.card {a : (Matrix (Fin (n + 1)) (Fin 4) (Fin 2)) // valid a}

/-- The source OGF starts at n=1; its constant coefficient is zero. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (count n : ℚ))

/-- The published recurrence, initial terms and conjectural OGF. -/
def claim : Prop :=
  count 1 = 104 ∧ count 2 = 368 ∧ count 3 = 1408 ∧
  count 4 = 5272 ∧ count 5 = 19992 ∧ count 6 = 75192 ∧
  (∀ n : ℕ, 7 ≤ n →
    (count n : ℤ) = (count (n - 1) : ℤ) + 10 * (count (n - 2) : ℤ) +
      3 * (count (n - 3) : ℤ) - 5 * (count (n - 4) : ℤ) + (count (n - 5) : ℤ)) ∧
  (let X : PowerSeries ℚ := PowerSeries.X
   generatingSeries = (8 * X * (13 + 33 * X - 16 * X ^ 3 + 7 * X ^ 4 - X ^ 5)) *
     (1 - X - 10 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - X ^ 5)⁻¹)


open scoped BigOperators
open CertA185763
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem transitions : ∀ a b : (Fin 16), (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) a b → ∀ k : (Fin 20),
 (∑ c : (Fin 16), if (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) a b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify a b) k := by
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

private theorem trace_decode (n : ℕ) (a : (Matrix (Fin (n + 1)) (Fin 4) (Fin 2))) :
 valid a ↔ arrayOK trace (fun j j' : Fin 3 => j'.val = j.val+1) n
    (fun i => (finFunctionFinEquiv (a i) : (Fin 16))) := by
 simp [valid,block,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
   arrayOK,trace]

private theorem source_card (n : ℕ) :
 count n = Nat.card {a : Fin (n+1) → (Fin 16) // good (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) (tripleOK trace) (List.ofFn a)} := by
 let e : ((Matrix (Fin (n + 1)) (Fin 4) (Fin 2))) ≃ (Fin (n+1) → (Fin 16)) := Equiv.piCongrRight (fun _ => finFunctionFinEquiv)
 unfold count
 apply Nat.card_congr
 apply e.subtypeEquiv
 intro a
 rw [trace_decode,arrayOKIffGood]
 rfl

private theorem count_transfer (n : ℕ) :
 (count (n+1) : ℤ) = dotProduct initial ((T^n).mulVec (1 : Fin 20 → ℤ)) := by
 rw [source_card]
 refine cardMatrix (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) (tripleOK trace) classify T initial ?_ ?_ n
 · intro a b hab k
   convert transitions a b hab k using 1
   apply Finset.sum_congr rfl
   intro c _
   by_cases h : (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) a b c ∧ classify b c = k <;> simp [h]
 · intro k
   convert initial_distribution k using 1
   apply Finset.sum_congr rfl
   intro a _
   apply Finset.sum_congr rfl
   intro b _
   by_cases h : (pairOK trace (fun j j' : Fin 3 => j'.val = j.val + 1)) a b ∧ classify a b = k <;> simp [h]

private theorem powers_table : ∀ k : Fin 9, (T^k.val).mulVec (1 : Fin 20 → ℤ) = W k := by
 apply tabulatedPowers T 8 W vector_zero
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

private def coefficients : Fin 5 → ℤ := ![1, -5, 3, 10, 1]

private theorem power_polynomial : (T^8).mulVec (1 : Fin 20 → ℤ) =
 ∑ j : Fin 5, coefficients j • (T^(3+j.val)).mulVec (1 : Fin 20 → ℤ) := by
 calc
  _ = W 8 := powers_table 8
  _ = ∑ j : Fin 5, coefficients j • W ⟨3+j.val,by omega⟩ := by
   ext k
   have hp := polynomial k
   norm_num [coefficients,Fin.sum_univ_succ,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
   linear_combination hp
  _ = _ := by
   apply Finset.sum_congr rfl
   intro j _
   rw [powers_table ⟨3+j.val,by omega⟩]

private theorem count_1 : count 1 = 104 := by
 have h := count_transfer 0
 rw [powers_table ⟨0,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_2 : count 2 = 368 := by
 have h := count_transfer 1
 rw [powers_table ⟨1,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_3 : count 3 = 1408 := by
 have h := count_transfer 2
 rw [powers_table ⟨2,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_4 : count 4 = 5272 := by
 have h := count_transfer 3
 rw [powers_table ⟨3,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_5 : count 5 = 19992 := by
 have h := count_transfer 4
 rw [powers_table ⟨4,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_6 : count 6 = 75192 := by
 have h := count_transfer 5
 rw [powers_table ⟨5,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_7 : count 7 = 284256 := by
 have h := count_transfer 6
 rw [powers_table ⟨6,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_8 : count 8 = 1071200 := by
 have h := count_transfer 7
 rw [powers_table ⟨7,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem recurrence : ∀ n : ℕ, 7 ≤ n → (count n : ℤ) = (count (n - 1) : ℤ) + 10 * (count (n - 2) : ℤ) + 3 * (count (n - 3) : ℤ) - 5 * (count (n - 4) : ℤ) + (count (n - 5) : ℤ) := by
 intro n hn
 by_cases hsmall : n < 9
 · interval_cases n <;> norm_num [count_1,count_2,count_3,count_4,count_5,count_6,count_7,count_8] at *
 · have hn' : 9 ≤ n := by exact Nat.le_of_not_lt hsmall
   have hr := scalarRelationShift T initial 5 3 coefficients power_polynomial (n-9)
   have hh (j : Fin 5) :
      dotProduct initial ((T^(n-9+3+j.val)).mulVec (1 : Fin 20 → ℤ)) =
       (count (n-9+3+j.val+1) : ℤ) := (count_transfer _).symm
   have he : n-9+3+5+1 = n := by omega
   rw [← count_transfer,he] at hr
   simp_rw [hh] at hr
   have hidx (j : Fin 5) : n-9+3+j.val+1 = n-(5-j.val) := by omega
   simp_rw [hidx] at hr
   norm_num [coefficients,Fin.sum_univ_succ] at hr
   linear_combination hr


theorem result : claim := by
 unfold claim
 refine ⟨count_1, count_2, count_3, count_4, count_5, count_6, recurrence, ?_⟩
 have h := TraceSeries.ogf_A185763 count count_1 count_2 count_3 count_4 count_5 count_6 recurrence
 change (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (count n : ℚ))) = _
 simp only [pow_one] at h
 convert h using 1 <;> ring

end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence
