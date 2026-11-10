/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185761Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA185761Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The literal binary array counts satisfy the published recurrence and series. -/

/-
admission_basis: open-problem-resolution (#21313; Proved)
proof_shape: content: result, via the literal-array cardinality bridge and continuation induction
escape_witness: none (the settling result uses the external open-problem basis)
Direct frozen dependencies: none. Pinned Mathlib supplies matrices, finite sums and cardinalities.
All auxiliary theorems are consumed; arithmetic certificates and normalization helpers are bind-only.
The source arrays use Matrix directly; their encoded-row traces apply Matrix.trace to block. Row predicates use pairOK and tripleOK.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21914
The source is OEIS A185761--A185764; literature-search completeness is ASSUMED-UNVERIFIED.
Declaration classifications (name | proof_shape | consumer):
CertA185761.trace | bind-only | decidableRowPredicate1
CertA185761.decidableRowPredicate1 | bind-only | step_0
CertA185761.decidableRowPredicate2 | bind-only | step_0
CertA185761.classify | bind-only | step_0
CertA185761.T | bind-only | step_0
CertA185761.initial | bind-only | initial_distribution
CertA185761.W | bind-only | vector_0
CertA185761.step_0 | bind-only | transitions
CertA185761.step_1 | bind-only | transitions
CertA185761.step_2 | bind-only | transitions
CertA185761.step_3 | bind-only | transitions
CertA185761.vector_0 | bind-only | powers_table
CertA185761.vector_1 | bind-only | powers_table
CertA185761.vector_2 | bind-only | powers_table
CertA185761.initial_distribution | bind-only | count_transfer
CertA185761.vector_zero | bind-only | powers_table
TraceSeries.ogf_A185761 | bind-only | result
HardinClosed.rootPlus | bind-only | closed
HardinClosed.rootMinus | bind-only | closed
HardinClosed.closed | bind-only | closed_step
HardinClosed.root_plus_sq | bind-only | closed_step
HardinClosed.root_minus_sq | bind-only | closed_step
HardinClosed.closed_step | bind-only | solution_eq
HardinClosed.closed_one | bind-only | solution_eq
HardinClosed.closed_two | bind-only | solution_eq
HardinClosed.closed_eq_source | bind-only | result
HardinClosed.solution_eq | bind-only | result
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
recurrence | content | result
result | content | none (settling result)
-/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.IntervalCases
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence

/-- The contiguous 2-by-2 block with upper-left corner (i,j), in integers. -/
def block {n : ℕ} (a : (Matrix (Fin (n + 1)) (Fin 2) (Fin 2))) (i : Fin n) (j : Fin 1) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun u v => ((a (if u = 0 then i.castSucc else i.succ)
    (if v = 0 then j.castSucc else j.succ)).val : ℤ)


open D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
section

open scoped BigOperators
namespace CertA185761
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private def trace (a b : Fin 4) (j : Fin 1) : ℤ :=
 Matrix.trace (block (n := 1)
  (fun i => if i.val = 0 then (finFunctionFinEquiv.symm a : Fin 2 → Fin 2)
   else (finFunctionFinEquiv.symm b : Fin 2 → Fin 2)) 0 j)
private instance decidableRowPredicate1 : DecidableRel (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) := fun _ _ => inferInstanceAs (Decidable (∀ j j' : Fin 1, _))
private instance decidableRowPredicate2 (a b c : (Fin 4)) : Decidable ((tripleOK trace) a b c) := inferInstanceAs (Decidable (∀ j : Fin 1, trace a b j ≠ trace b c j))
private def classify (a b : (Fin 4)) : (Fin 3) :=
 (![![0, 2, 1, 1],
 ![1, 1, 2, 0],
 ![0, 2, 1, 1],
 ![1, 1, 2, 0]] : (Fin 4) → (Fin 4) → (Fin 3)) a b
private def T : Matrix (Fin 3) (Fin 3) ℤ :=
 !![0, 2, 0;
 1, 0, 1;
 1, 2, 1]
private def initial : (Fin 3) → ℤ := ![4, 8, 4]
private def W : Fin 4 → (Fin 3) → ℤ :=
 ![![1, 1, 1],
 ![2, 2, 4],
 ![4, 6, 10],
 ![12, 14, 26]]

private theorem step_0 : ∀ b : (Fin 4), (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) 0 b → ∀ k : (Fin 3),
 (∑ c : (Fin 4), if (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 0 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 0 b) k := by decide
private theorem step_1 : ∀ b : (Fin 4), (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) 1 b → ∀ k : (Fin 3),
 (∑ c : (Fin 4), if (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 1 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 1 b) k := by decide
private theorem step_2 : ∀ b : (Fin 4), (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) 2 b → ∀ k : (Fin 3),
 (∑ c : (Fin 4), if (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 2 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 2 b) k := by
 simpa [pairOK, tripleOK, trace, block, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
   Fin.forall_fin_one, classify,
   show (finFunctionFinEquiv (m := 2) (n := 2)).symm (2 : Fin 4) (0 : Fin 2) =
     (finFunctionFinEquiv (m := 2) (n := 2)).symm (0 : Fin 4) (0 : Fin 2) from rfl]
   using step_0
private theorem step_3 : ∀ b : (Fin 4), (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) 3 b → ∀ k : (Fin 3),
 (∑ c : (Fin 4), if (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) 3 b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify 3 b) k := by
 simpa [pairOK, tripleOK, trace, block, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
   Fin.forall_fin_one, classify,
   show (finFunctionFinEquiv (m := 2) (n := 2)).symm (3 : Fin 4) (0 : Fin 2) =
     (finFunctionFinEquiv (m := 2) (n := 2)).symm (1 : Fin 4) (0 : Fin 2) from rfl]
   using step_1

private theorem vector_0 : W 1 = T.mulVec (W 0) := by exact List.ofFn_inj.mp rfl
private theorem vector_1 : W 2 = T.mulVec (W 1) := by exact List.ofFn_inj.mp rfl
private theorem vector_2 : W 3 = T.mulVec (W 2) := by exact List.ofFn_inj.mp rfl
private theorem initial_distribution : ∀ k : (Fin 3),
 (∑ a : (Fin 4), ∑ b : (Fin 4), if (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) a b ∧ classify a b = k then (1:ℤ) else 0) = initial k := by decide

private theorem vector_zero : W 0 = (1 : Fin 3 → ℤ) := by exact List.ofFn_inj.mp rfl

end CertA185761
end

section
namespace TraceSeries
private theorem ogf_A185761 (a : ℕ → ℕ) (h1 : a 1 = 16) (h2 : a 2 = 40)
 (hr : ∀ n : ℕ, 3 ≤ n → (a n : ℤ) = (a (n - 1) : ℤ) + 4 * (a (n - 2) : ℤ)) :
 (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (a n : ℚ))) = (let X : PowerSeries ℚ := PowerSeries.X; (16 * X ^ 1 + 24 * X ^ 2) * (1 - X ^ 1 - 4 * X ^ 2)⁻¹) := by
 let X : PowerSeries ℚ := PowerSeries.X
 let F := (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (a n : ℚ)))
 have hp : F * (1 - X ^ 1 - 4 * X ^ 2) = (16 * X ^ 1 + 24 * X ^ 2) := by
   have he : F * (1 - X ^ 1 - 4 * X ^ 2) = F - (F * X ^ 1) - 4 * (F * X ^ 2) := by ring
   rw [he]
   apply PowerSeries.ext
   intro n
   simp only [X,map_sub,map_add,PowerSeries.coeff_ofNat_mul,
     PowerSeries.coeff_mul_X_pow',PowerSeries.coeff_X_pow,PowerSeries.coeff_X,
     F,PowerSeries.coeff_mk]
   by_cases hn : n < 3
   · interval_cases n <;> norm_num [h1,h2,X]
   · have hnr : 3 ≤ n := by exact Nat.le_of_not_lt hn
     have hq : (a n : ℚ) = (a (n - 1) : ℚ) + 4 * (a (n - 2) : ℚ) := by exact_mod_cast hr n hnr
     simp only [ite_eq_left (show 1 ≤ n by omega),
       ite_eq_left (show 2 ≤ n by omega),
       ite_eq_right (show ¬ n = 0 by omega),
       ite_eq_right (show ¬ n = 1 by omega),
       ite_eq_right (show ¬ n - 1 = 0 by omega),
       ite_eq_right (show ¬ n = 2 by omega),
       ite_eq_right (show ¬ n - 2 = 0 by omega)]
     linarith [hq]
 change F = (16 * X ^ 1 + 24 * X ^ 2) * (1 - X ^ 1 - 4 * X ^ 2)⁻¹
 calc
  F = (F * (1 - X ^ 1 - 4 * X ^ 2)) * (1 - X ^ 1 - 4 * X ^ 2)⁻¹ := by
    rw [mul_assoc,PowerSeries.mul_inv_cancel _ (by norm_num [X]),mul_one]
  _ = (16 * X ^ 1 + 24 * X ^ 2) * (1 - X ^ 1 - 4 * X ^ 2)⁻¹ := by rw [hp]

end TraceSeries
end

section

namespace HardinClosed
open scoped BigOperators
private noncomputable def rootPlus : ℝ := (1 + Real.sqrt 17) / 2
private noncomputable def rootMinus : ℝ := (1 - Real.sqrt 17) / 2
private noncomputable def closed (n : ℕ) : ℝ :=
 ((13+3*Real.sqrt 17)*rootPlus^n+(-13+3*Real.sqrt 17)*rootMinus^n)/Real.sqrt 17

private theorem root_plus_sq : rootPlus^2 = rootPlus + 4 := by
 have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
 dsimp [rootPlus]
 nlinarith

private theorem root_minus_sq : rootMinus^2 = rootMinus + 4 := by
 have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
 dsimp [rootMinus]
 nlinarith

private theorem closed_step (n : ℕ) : closed (n+2) = closed (n+1)+4*closed n := by
 simp only [closed, pow_add, pow_one, root_plus_sq, root_minus_sq]
 ring

private theorem closed_one : closed 1 = 16 := by
 have ht : Real.sqrt 17 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
 have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
 dsimp [closed,rootPlus,rootMinus]
 field_simp [ht]
 nlinarith

private theorem closed_two : closed 2 = 40 := by
 have ht : Real.sqrt 17 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
 have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
 have h3 : Real.sqrt 17 ^ 3 = 17*Real.sqrt 17 := by rw [pow_succ, h]
 dsimp [closed,rootPlus,rootMinus]
 field_simp [ht]
 nlinarith [h3]

private theorem closed_eq_source (n : ℕ) : closed n =
 ((2 : ℝ)⁻¹ ^ n *
        ((1 - Real.sqrt 17) ^ n * (-13 + 3 * Real.sqrt 17) +
         (1 + Real.sqrt 17) ^ n * (13 + 3 * Real.sqrt 17))) / Real.sqrt 17 := by
 simp only [closed,rootPlus,rootMinus]
 simp only [div_pow]
 simp only [div_eq_mul_inv,inv_pow]
 ring

private theorem solution_eq (a : ℕ → ℝ) (h1 : a 1 = 16) (h2 : a 2 = 40)
 (hrec : ∀ n : ℕ, 3 ≤ n → a n = a (n-1)+4*a (n-2)) :
 ∀ n : ℕ, 1 ≤ n → a n = closed n := by
 let E : LinearRecurrence ℝ := ⟨2, ![4,1]⟩
 have hu : E.IsSolution (fun k => a (k+1)) := by
   intro k
   change a (k+2+1) = ∑ j : Fin 2, (![4,1] : Fin 2 → ℝ) j * a (k+j.val+1)
   norm_num [Fin.sum_univ_two, Nat.add_assoc]
   have h := hrec (k+3) (by omega)
   have he1 : k+3-1 = k+2 := by exact Nat.add_succ_sub_one k 2
   have he2 : k+3-2 = k+1 := by exact Eq.symm (Nat.add_succ k 0)
   rw [he1,he2] at h
   linear_combination h
 have hv : E.IsSolution (fun k => closed (k+1)) := by
   intro k
   change closed (k+2+1) = ∑ j : Fin 2, (![4,1] : Fin 2 → ℝ) j * closed (k+j.val+1)
   norm_num [Fin.sum_univ_two, Nat.add_assoc]
   have h := closed_step (k+1)
   simp only [Nat.add_assoc] at h
   linear_combination h
 have heq : (fun k => a (k+1)) = (fun k => closed (k+1)) := by
   apply (E.eq_iff_eqOn_range_order _ _ hu hv).mpr
   intro k hk
   have hk' : k < 2 := by exact List.mem_range.mp hk
   interval_cases k <;> simp [h1,h2,closed_one,closed_two]
 intro n hn
 have h := congrFun heq (n-1)
 simpa only [Nat.sub_add_cancel hn] using h
end HardinClosed
end

section


/-- Exactly vertical and horizontal neighbors of contiguous blocks. -/
def valid {n : ℕ} (a : (Matrix (Fin (n + 1)) (Fin 2) (Fin 2))) : Prop :=
  (∀ (i i' : Fin n) (j : Fin 1),
    i'.val = i.val + 1 → Matrix.trace (block a i j) ≠ Matrix.trace (block a i' j)) ∧
  (∀ (i : Fin n) (j j' : Fin 1),
    j'.val = j.val + 1 → Matrix.trace (block a i j) ≠ Matrix.trace (block a i j'))

/-- The OEIS count, directly on the source arrays. -/
noncomputable def count (n : ℕ) : ℕ := Nat.card {a : (Matrix (Fin (n + 1)) (Fin 2) (Fin 2)) // valid a}

/-- The source OGF starts at n=1; its constant coefficient is zero. -/
noncomputable def generatingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (count n : ℚ))

/-- The published recurrence, initial terms and conjectural OGF and closed form. -/
def claim : Prop :=
  count 1 = 16 ∧ count 2 = 40 ∧
  (∀ n : ℕ, 3 ≤ n →
    (count n : ℤ) = (count (n - 1) : ℤ) + 4 * (count (n - 2) : ℤ)) ∧
  (let X : PowerSeries ℚ := PowerSeries.X
   generatingSeries = (8 * X * (2 + 3 * X)) *
     (1 - X - 4 * X ^ 2)⁻¹) ∧
  (∀ n : ℕ, 1 ≤ n →
    (count n : ℝ) =
      ((2 : ℝ)⁻¹ ^ n *
        ((1 - Real.sqrt 17) ^ n * (-13 + 3 * Real.sqrt 17) +
         (1 + Real.sqrt 17) ^ n * (13 + 3 * Real.sqrt 17))) / Real.sqrt 17)


open scoped BigOperators
open CertA185761
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem transitions : ∀ a b : (Fin 4), (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) a b → ∀ k : (Fin 3),
 (∑ c : (Fin 4), if (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) a b c ∧ classify b c = k then (1:ℤ) else 0) = T (classify a b) k := by
 intro a
 fin_cases a <;> first
 | exact step_0
 | exact step_1
 | exact step_2
 | exact step_3

private theorem trace_decode (n : ℕ) (a : (Matrix (Fin (n + 1)) (Fin 2) (Fin 2))) :
 valid a ↔ arrayOK trace (fun j j' : Fin 1 => j'.val = j.val+1) n
    (fun i => (finFunctionFinEquiv (a i) : (Fin 4))) := by
 simp [valid,block,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
   arrayOK,trace]

private theorem source_card (n : ℕ) :
 count n = Nat.card {a : Fin (n+1) → (Fin 4) // good (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) (tripleOK trace) (List.ofFn a)} := by
 let e : ((Matrix (Fin (n + 1)) (Fin 2) (Fin 2))) ≃ (Fin (n+1) → (Fin 4)) := Equiv.piCongrRight (fun _ => finFunctionFinEquiv)
 unfold count
 apply Nat.card_congr
 apply e.subtypeEquiv
 intro a
 rw [trace_decode,arrayOKIffGood]
 rfl

private theorem count_transfer (n : ℕ) :
 (count (n+1) : ℤ) = dotProduct initial ((T^n).mulVec (1 : Fin 3 → ℤ)) := by
 rw [source_card]
 refine cardMatrix (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) (tripleOK trace) classify T initial ?_ ?_ n
 · intro a b hab k
   convert transitions a b hab k using 1
   apply Finset.sum_congr rfl
   intro c _
   by_cases h : (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) b c ∧ (tripleOK trace) a b c ∧ classify b c = k <;> simp [h]
 · intro k
   convert initial_distribution k using 1
   apply Finset.sum_congr rfl
   intro a _
   apply Finset.sum_congr rfl
   intro b _
   by_cases h : (pairOK trace (fun j j' : Fin 1 => j'.val = j.val + 1)) a b ∧ classify a b = k <;> simp [h]

private theorem powers_table : ∀ k : Fin 4, (T^k.val).mulVec (1 : Fin 3 → ℤ) = W k := by
 apply tabulatedPowers T 3 W vector_zero
 intro k
 fin_cases k <;> first
 | exact vector_0
 | exact vector_1
 | exact vector_2

private def coefficients : Fin 2 → ℤ := ![4, 1]

private theorem power_polynomial : (T^3).mulVec (1 : Fin 3 → ℤ) =
 ∑ j : Fin 2, coefficients j • (T^(1+j.val)).mulVec (1 : Fin 3 → ℤ)  := by
 calc
  _ = W 3 := powers_table 3
  _ = ∑ j : Fin 2, coefficients j • W ⟨1+j.val,by omega⟩ := by
   exact List.ofFn_inj.mp rfl
  _ = _ := by
   apply Finset.sum_congr rfl
   intro j _
   rw [powers_table ⟨1+j.val,by omega⟩]


private theorem count_1 : count 1 = 16 := by
 have h := count_transfer 0
 rw [powers_table ⟨0,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_2 : count 2 = 40 := by
 have h := count_transfer 1
 rw [powers_table ⟨1,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem count_3 : count 3 = 104 := by
 have h := count_transfer 2
 rw [powers_table ⟨2,by decide⟩] at h
 norm_num [dotProduct,initial,W,Fin.sum_univ_succ] at h
 exact_mod_cast h

private theorem recurrence : ∀ n : ℕ, 3 ≤ n → (count n : ℤ) = (count (n - 1) : ℤ) + 4 * (count (n - 2) : ℤ) := by
 intro n hn
 by_cases hsmall : n < 4
 · interval_cases n <;> norm_num [count_1,count_2,count_3] at *
 · have hn' : 4 ≤ n := by exact Nat.le_of_not_lt hsmall
   have hr := scalarRelationShift T initial 2 1 coefficients power_polynomial (n-4)
   have hh (j : Fin 2) :
      dotProduct initial ((T^(n-4+1+j.val)).mulVec (1 : Fin 3 → ℤ)) =
       (count (n-4+1+j.val+1) : ℤ) := (count_transfer _).symm
   have he : n-4+1+2+1 = n := by omega
   rw [← count_transfer,he] at hr
   simp_rw [hh] at hr
   have hidx (j : Fin 2) : n-4+1+j.val+1 = n-(2-j.val) := by omega
   simp_rw [hidx] at hr
   norm_num [coefficients,Fin.sum_univ_succ] at hr
   linear_combination hr


theorem result : claim := by
 unfold claim
 refine ⟨count_1, count_2, recurrence, ?_, ?_⟩
 · have h := TraceSeries.ogf_A185761 count count_1 count_2 recurrence
   change (PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (count n : ℚ))) = _
   simp only [pow_one] at h
   convert h using 1 <;> ring
 · intro n hn
   have hrec : ∀ m : ℕ, 3 ≤ m → (count m : ℝ) = (count (m-1) : ℝ)+4*(count (m-2) : ℝ) := by
     intro m hm
     exact_mod_cast recurrence m hm
   have h := HardinClosed.solution_eq (fun m => (count m : ℝ))
     (by exact_mod_cast count_1) (by exact_mod_cast count_2) hrec n hn
   exact h.trans (HardinClosed.closed_eq_source n)

end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence
