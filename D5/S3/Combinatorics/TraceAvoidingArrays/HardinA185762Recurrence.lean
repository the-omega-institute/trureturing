/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185762Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA185762Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The literal binary array counts satisfy the published recurrence and series. -/

/-
admission_basis: open-problem-resolution (#21314; Proved)
proof_shape: content: result, via the literal-array cardinality bridge and continuation induction
escape_witness: none (the settling result uses the external open-problem basis)
Direct frozen dependencies: none. Pinned Mathlib supplies matrices, finite sums and cardinalities.
All auxiliary theorems are consumed; arithmetic certificates and normalization helpers are bind-only.
The source arrays use Matrix directly; their encoded-row traces apply Matrix.trace to block. Row predicates use pairOK and tripleOK.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21914
The source is OEIS A185761--A185764; literature-search completeness is ASSUMED-UNVERIFIED.
Declaration classifications (name | proof_shape | consumer):
CertA185762.trace | bind-only | decidableRowPredicate1
CertA185762.decidableRowPredicate1 | bind-only | step_0
CertA185762.decidableRowPredicate2 | bind-only | step_0
CertA185762.classify | bind-only | step_0
CertA185762.T | bind-only | step_0
CertA185762.initial | bind-only | initial_distribution
CertA185762.W | bind-only | vector_0
CertA185762.step_0 | bind-only | transitions
CertA185762.step_1 | bind-only | transitions
CertA185762.step_2 | bind-only | transitions
CertA185762.step_3 | bind-only | transitions
CertA185762.step_4 | bind-only | transitions
CertA185762.step_5 | bind-only | transitions
CertA185762.step_6 | bind-only | transitions
CertA185762.step_7 | bind-only | transitions
CertA185762.vector_0 | bind-only | powers_table
CertA185762.vector_1 | bind-only | powers_table
CertA185762.vector_2 | bind-only | powers_table
CertA185762.vector_3 | bind-only | powers_table
CertA185762.vector_4 | bind-only | powers_table
CertA185762.initial_distribution | bind-only | count_transfer
CertA185762.vector_zero | bind-only | powers_table
TraceSeries.ogf_A185762 | bind-only | result
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
recurrence | content | result
result | content | none (settling result)
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.IntervalCases
import Mathlib.LinearAlgebra.Matrix.Trace
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence

/-- The contiguous 2-by-2 block with upper-left corner (i,j), in integers. -/
def block {n : ℕ} (a : (Matrix (Fin (n + 1)) (Fin 3) (Fin 2))) (i : Fin n) (j : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun u v => ((a (if u = 0 then i.castSucc else i.succ)
    (if v = 0 then j.castSucc else j.succ)).val : ℤ)


open D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
section

open scoped BigOperators
namespace CertA185762
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private def trace (a b : Fin 8) (j : Fin 2) : ℤ :=
 Matrix.trace (block (n := 1)
  (fun i => if i.val = 0 then (finFunctionFinEquiv.symm a : Fin 3 → Fin 2)
   else (finFunctionFinEquiv.symm b : Fin 3 → Fin 2)) 0 j)
private instance decidableRowPredicate1 : DecidableRel (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) := fun _ _ => inferInstanceAs (Decidable (∀ j j' : Fin 2, _))
private instance decidableRowPredicate2 (a b c : (Fin 8)) : Decidable ((tripleOK trace) a b c) := inferInstanceAs (Decidable (∀ j : Fin 2, trace a b j ≠ trace b c j))
private def classify (a b : (Fin 8)) : (Fin 8) :=
 (![![0, 0, 4, 3, 0, 7, 0, 0],
 ![2, 5, 6, 1, 0, 0, 7, 0],
 ![0, 7, 0, 0, 1, 6, 5, 2],
 ![0, 0, 7, 0, 3, 4, 0, 0],
 ![0, 0, 4, 3, 0, 7, 0, 0],
 ![2, 5, 6, 1, 0, 0, 7, 0],
 ![0, 7, 0, 0, 1, 6, 5, 2],
 ![0, 0, 7, 0, 3, 4, 0, 0]] : (Fin 8) → (Fin 8) → (Fin 8)) a b
private def T : Matrix (Fin 8) (Fin 8) ℤ :=
 !![0, 0, 0, 1, 1, 0, 0, 0;
 0, 0, 0, 1, 1, 0, 0, 0;
 1, 0, 0, 0, 0, 0, 0, 1;
 1, 0, 0, 0, 0, 0, 0, 1;
 1, 1, 0, 0, 0, 0, 1, 1;
 1, 0, 0, 0, 0, 0, 0, 1;
 1, 1, 1, 0, 0, 1, 1, 1;
 0, 1, 1, 0, 0, 1, 1, 0]
private def initial : (Fin 8) → ℤ := ![8, 4, 4, 4, 4, 4, 4, 8]
private def W : Fin 6 → (Fin 8) → ℤ :=
 ![![1, 1, 1, 1, 1, 1, 1, 1],
 ![2, 2, 2, 2, 4, 2, 6, 4],
 ![6, 6, 6, 6, 14, 6, 18, 12],
 ![20, 20, 18, 18, 42, 18, 54, 36],
 ![60, 60, 56, 56, 130, 56, 166, 110],
 ![186, 186, 170, 170, 396, 170, 508, 338]]

private theorem step_0 : ∀ b : (Fin 8), (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) 0 b → ∀ k : (Fin 8),
 (∑ c : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 0 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 0 b) k := by decide
private theorem step_1 : ∀ b : (Fin 8), (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) 1 b → ∀ k : (Fin 8),
 (∑ c : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 1 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 1 b) k := by decide
private theorem step_2 : ∀ b : (Fin 8), (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) 2 b → ∀ k : (Fin 8),
 (∑ c : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 2 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 2 b) k := by decide
private theorem step_3 : ∀ b : (Fin 8), (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) 3 b → ∀ k : (Fin 8),
 (∑ c : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 3 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 3 b) k := by decide
private theorem step_4 : ∀ b : (Fin 8), (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) 4 b → ∀ k : (Fin 8),
 (∑ c : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 4 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 4 b) k := by decide
private theorem step_5 : ∀ b : (Fin 8), (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) 5 b → ∀ k : (Fin 8),
 (∑ c : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 5 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 5 b) k := by decide
private theorem step_6 : ∀ b : (Fin 8), (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) 6 b → ∀ k : (Fin 8),
 (∑ c : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 6 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 6 b) k := by decide
private theorem step_7 : ∀ b : (Fin 8), (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) 7 b → ∀ k : (Fin 8),
 (∑ c : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 7 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 7 b) k := by decide

private theorem vector_0 : W 1 = T.mulVec (W 0) := by exact List.ofFn_inj.mp rfl
private theorem vector_1 : W 2 = T.mulVec (W 1) := by exact List.ofFn_inj.mp rfl
private theorem vector_2 : W 3 = T.mulVec (W 2) := by exact List.ofFn_inj.mp rfl
private theorem vector_3 : W 4 = T.mulVec (W 3) := by exact List.ofFn_inj.mp rfl
private theorem vector_4 : W 5 = T.mulVec (W 4) := by exact List.ofFn_inj.mp rfl
private theorem initial_distribution : ∀ k : (Fin 8),
 (∑ a : (Fin 8), ∑ b : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) a b ∧ classify a b = k then (1:ℤ) else 0) = initial k := by decide

private theorem vector_zero : W 0 = (1 : Fin 8 → ℤ) := by exact List.ofFn_inj.mp rfl

end CertA185762
end

section
namespace TraceSeries
private theorem ogf_A185762 (a : ℕ → ℕ) (h1 : a 1 = 40) (h2 : a 2 = 120) (h3 : a 3 = 368)
 (hr : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = (a (n - 1) : ℤ) + 6 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ)) :
 (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (a n : ℚ))) = (let X : PowerSeries ℚ := PowerSeries.X; (40 * X ^ 1 + 80 * X ^ 2 + 8 * X ^ 3) * (1 - X ^ 1 - 6 * X ^ 2 - X ^ 3)⁻¹) := by
 let X : PowerSeries ℚ := PowerSeries.X
 let F := (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (a n : ℚ)))
 have hp : F * (1 - X ^ 1 - 6 * X ^ 2 - X ^ 3) = (40 * X ^ 1 + 80 * X ^ 2 + 8 * X ^ 3) := by
   have he : F * (1 - X ^ 1 - 6 * X ^ 2 - X ^ 3) = F - (F * X ^ 1) - 6 * (F * X ^ 2) - (F * X ^ 3) := by ring
   rw [he]
   apply PowerSeries.ext
   intro n
   simp only [X,map_sub,map_add,PowerSeries.coeff_ofNat_mul,
     PowerSeries.coeff_mul_X_pow',PowerSeries.coeff_X_pow,PowerSeries.coeff_X,
     F,PowerSeries.coeff_mk]
   by_cases hn : n < 4
   · interval_cases n <;> norm_num [h1,h2,h3,X]
   · have hnr : 4 ≤ n := by exact Nat.le_of_not_lt hn
     have hq : (a n : ℚ) = (a (n - 1) : ℚ) + 6 * (a (n - 2) : ℚ) + (a (n - 3) : ℚ) := by exact_mod_cast hr n hnr
     simp only [ite_eq_left (show 1 ≤ n by omega),
       ite_eq_left (show 2 ≤ n by omega),
       ite_eq_left (show 3 ≤ n by omega),
       ite_eq_right (show ¬ n = 0 by omega),
       ite_eq_right (show ¬ n = 1 by omega),
       ite_eq_right (show ¬ n - 1 = 0 by omega),
       ite_eq_right (show ¬ n = 2 by omega),
       ite_eq_right (show ¬ n - 2 = 0 by omega),
       ite_eq_right (show ¬ n = 3 by omega),
       ite_eq_right (show ¬ n - 3 = 0 by omega)]
     linarith [hq]
 change F = (40 * X ^ 1 + 80 * X ^ 2 + 8 * X ^ 3) * (1 - X ^ 1 - 6 * X ^ 2 - X ^ 3)⁻¹
 calc
  F = (F * (1 - X ^ 1 - 6 * X ^ 2 - X ^ 3)) * (1 - X ^ 1 - 6 * X ^ 2 - X ^ 3)⁻¹ := by
    rw [mul_assoc,PowerSeries.mul_inv_cancel _ (by norm_num [X]),mul_one]
  _ = (40 * X ^ 1 + 80 * X ^ 2 + 8 * X ^ 3) * (1 - X ^ 1 - 6 * X ^ 2 - X ^ 3)⁻¹ := by rw [hp]

end TraceSeries
end

section


/-- Exactly vertical and horizontal neighbors of contiguous blocks. -/
def valid {n : ℕ} (a : (Matrix (Fin (n + 1)) (Fin 3) (Fin 2))) : Prop :=
  (∀ (i i' : Fin n) (j : Fin 2),
    i'.val = i.val + 1 → Matrix.trace (block a i j) ≠ Matrix.trace (block a i' j)) ∧
  (∀ (i : Fin n) (j j' : Fin 2),
    j'.val = j.val + 1 → Matrix.trace (block a i j) ≠ Matrix.trace (block a i j'))

/-- The OEIS count, directly on the source arrays. -/
noncomputable def count (n : ℕ) : ℕ := Nat.card {a : (Matrix (Fin (n + 1)) (Fin 3) (Fin 2)) // valid a}

/-- The source OGF starts at n=1; its constant coefficient is zero. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (count n : ℚ))

/-- The published recurrence, initial terms and conjectural OGF. -/
def claim : Prop :=
  count 1 = 40 ∧ count 2 = 120 ∧ count 3 = 368 ∧
  (∀ n : ℕ, 4 ≤ n →
    (count n : ℤ) = (count (n - 1) : ℤ) + 6 * (count (n - 2) : ℤ) + (count (n - 3) : ℤ)) ∧
  (let X : PowerSeries ℚ := PowerSeries.X
   generatingSeries = (8 * X * (5 + 10 * X + X ^ 2)) *
     (1 - X - 6 * X ^ 2 - X ^ 3)⁻¹)


open scoped BigOperators
open CertA185762
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem transitions : ∀ a b : (Fin 8), (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) a b → ∀ k : (Fin 8),
 (∑ c : (Fin 8), if (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) a b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify a b) k := by
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

private theorem trace_decode (n : ℕ) (a : (Matrix (Fin (n + 1)) (Fin 3) (Fin 2))) :
 valid a ↔ arrayOK trace (fun j j' : Fin 2 => j'.val = j.val+1) n
    (fun i => (finFunctionFinEquiv (a i) : (Fin 8))) := by
 simp [valid,block,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
   arrayOK,trace]

private theorem source_card (n : ℕ) :
 count n = Nat.card {a : Fin (n+1) → (Fin 8) // good (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) (tripleOK trace) (List.ofFn a)} := by
 let e : ((Matrix (Fin (n + 1)) (Fin 3) (Fin 2))) ≃ (Fin (n+1) → (Fin 8)) := Equiv.piCongrRight (fun _ => finFunctionFinEquiv)
 unfold count
 apply Nat.card_congr
 apply e.subtypeEquiv
 intro a
 rw [trace_decode,arrayOKIffGood]
 rfl

private theorem count_transfer (n : ℕ) :
 (count (n+1) : ℤ) = dotProduct initial ((T^n).mulVec (1 : Fin 8 → ℤ)) := by
 rw [source_card]
 refine cardMatrix (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) (tripleOK trace) classify T initial ?_ ?_ n
 · intro a b hab k
   convert transitions a b hab k using 1
   apply Finset.sum_congr rfl
   intro c _
   by_cases h : (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) a b c ∧ classify b c = k <;> simp [h]
 · intro k
   convert initial_distribution k using 1
   apply Finset.sum_congr rfl
   intro a _
   apply Finset.sum_congr rfl
   intro b _
   by_cases h : (pairOK trace (fun j j' : Fin 2 => j'.val = j.val + 1)) a b ∧ classify a b = k <;> simp [h]

private theorem powers_table : ∀ k : Fin 6, (T^k.val).mulVec (1 : Fin 8 → ℤ) = W k := by
 apply tabulatedPowers T 5 W vector_zero
 intro k
 fin_cases k <;> first
 | exact vector_0
 | exact vector_1
 | exact vector_2
 | exact vector_3
 | exact vector_4

private def coefficients : Fin 3 → ℤ := ![1, 6, 1]

private theorem power_polynomial : (T^5).mulVec (1 : Fin 8 → ℤ) =
 ∑ j : Fin 3, coefficients j • (T^(2+j.val)).mulVec (1 : Fin 8 → ℤ)  := by
 calc
  _ = W 5 := powers_table 5
  _ = ∑ j : Fin 3, coefficients j • W ⟨2+j.val,by omega⟩ := by
   exact List.ofFn_inj.mp rfl
  _ = _ := by
   apply Finset.sum_congr rfl
   intro j _
   rw [powers_table ⟨2+j.val,by omega⟩]


private theorem count_1 : count 1 = 40 := by
 have h := count_transfer 0
 rw [powers_table ⟨0,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_2 : count 2 = 120 := by
 have h := count_transfer 1
 rw [powers_table ⟨1,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_3 : count 3 = 368 := by
 have h := count_transfer 2
 rw [powers_table ⟨2,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_4 : count 4 = 1128 := by
 have h := count_transfer 3
 rw [powers_table ⟨3,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_5 : count 5 = 3456 := by
 have h := count_transfer 4
 rw [powers_table ⟨4,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem recurrence : ∀ n : ℕ, 4 ≤ n → (count n : ℤ) = (count (n - 1) : ℤ) + 6 * (count (n - 2) : ℤ) + (count (n - 3) : ℤ) := by
 intro n hn
 by_cases hsmall : n < 6
 · interval_cases n <;> norm_num [count_1,count_2,count_3,count_4,count_5] at *
 · have hn' : 6 ≤ n := by exact Nat.le_of_not_lt hsmall
   have hr := scalarRelationShift T initial 3 2 coefficients power_polynomial (n-6)
   have hh (j : Fin 3) :
      dotProduct initial ((T^(n-6+2+j.val)).mulVec (1 : Fin 8 → ℤ)) =
       (count (n-6+2+j.val+1) : ℤ) := (count_transfer _).symm
   have he : n-6+2+3+1 = n := by omega
   rw [← count_transfer,he] at hr
   simp_rw [hh] at hr
   have hidx (j : Fin 3) : n-6+2+j.val+1 = n-(3-j.val) := by omega
   simp_rw [hidx] at hr
   norm_num [coefficients,Fin.sum_univ_succ] at hr
   linear_combination hr


theorem result : claim := by
 unfold claim
 refine ⟨count_1, count_2, count_3, recurrence, ?_⟩
 have h := TraceSeries.ogf_A185762 count count_1 count_2 count_3 recurrence
 change (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (count n : ℚ))) = _
 simp only [pow_one] at h
 convert h using 1 <;> ring

end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence
