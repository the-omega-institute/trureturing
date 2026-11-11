/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite words with local constraints admit a weighted transfer count. -/

/-
admission_basis: escape-witness
proof_shape: content: cardMatrix; structural induction in cont_matrix
escape_witness: cont_matrix (induction transporting admissible continuations)
Direct frozen dependencies: none. Pinned Mathlib supplies matrices, finite sums and cardinalities.
The remaining public owners are used by the four recurrence modules.
The continuation count records pair and triple admissibility before weighted lumping.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21914
The source is OEIS A185761--A185764; literature-search completeness is ASSUMED-UNVERIFIED.
Declaration classifications (name | proof_shape | consumer):
tailGood | bind-only | good
good | bind-only | good_cons
card_subtype_sum | bind-only | cont_succ
cont | bind-only | cont_zero
cont_zero | bind-only | cont_matrix
cont_succ | bind-only | cont_matrix
cont_matrix | content | cardMatrix
good_cons | bind-only | good_iff_local
good_iff_local | content | arrayOKIffGood
pairOK | bind-only | arrayOKIffGood
tripleOK | bind-only | arrayOKIffGood
arrayOK | bind-only | arrayOKIffGood
arrayOKIffGood | content | HardinA185761Recurrence.source_card
card_good | bind-only | cardMatrix
cardMatrix | content | HardinA185761Recurrence.count_transfer
vector_relation_shift | bind-only | scalarRelationShift
scalarRelationShift | bind-only | HardinA185761Recurrence.recurrence
tabulatedPowers | bind-only | HardinA185761Recurrence.powers_table
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum
import Mathlib.Data.List.GetD

namespace D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

section

open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R S : Type*} [Fintype R] [Fintype S] [DecidableEq S]

def tailGood (P : R → R → Prop) (Q : R → R → R → Prop) : R → R → List R → Prop
 | _, _, [] => True
 | a, b, c :: cs => P b c ∧ Q a b c ∧ tailGood P Q b c cs

def good (P : R → R → Prop) (Q : R → R → R → Prop) : List R → Prop
 | [] => True
 | [_] => True
 | a :: b :: cs => P a b ∧ tailGood P Q a b cs

private theorem card_subtype_sum {A : Type*} [Fintype A] (p : A → Prop) :
 (Nat.card {a : A // p a} : ℤ) = ∑ a : A, if p a then 1 else 0 := by
 classical
 rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
 push_cast
 rfl

private noncomputable def cont (P : R → R → Prop) (Q : R → R → R → Prop)
    (n : ℕ) (a b : R) : ℤ := by
 classical
 exact (Nat.card {cs : Fin n → R // tailGood P Q a b (List.ofFn cs)} : ℤ)

private theorem cont_zero (P : R → R → Prop) (Q : R → R → R → Prop) (a b : R) :
    cont P Q 0 a b = 1 := by
 classical
 simp [cont, tailGood, Nat.card_eq_fintype_card]

private theorem cont_succ (P : R → R → Prop) (Q : R → R → R → Prop) (n : ℕ) (a b : R) :
    cont P Q (n+1) a b = ∑ c : R, if P b c ∧ Q a b c then cont P Q n b c else 0 := by
 classical
 simp_rw [cont, card_subtype_sum]
 rw [← (Fin.consEquiv fun _ : Fin (n+1) => R).sum_comp]
 simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_cons, tailGood]
 apply Finset.sum_congr rfl
 intro c _
 by_cases h : P b c ∧ Q a b c
 · simp [h.1, h.2]
 · simp only [ite_and]
   rcases not_and_or.mp h with h | h <;> simp [h]

private theorem cont_matrix (P : R → R → Prop) (Q : R → R → R → Prop)
    (cl : R → R → S) (T : Matrix S S ℤ)
    (hT : ∀ a b, P a b → ∀ s,
      (∑ c : R, if P b c ∧ Q a b c ∧ cl b c = s then (1:ℤ) else 0) = T (cl a b) s)
    (n : ℕ) (a b : R) (hab : P a b) :
    cont P Q n a b = (T ^ n).mulVec (1 : S → ℤ) (cl a b) := by
 classical
 induction n generalizing a b with
 | zero => simp [cont_zero, Matrix.one_mulVec]
 | succ n ih =>
   rw [cont_succ, pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec]
   simp only [dotProduct]
   simp_rw [← hT a b hab, Finset.sum_mul]
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro c _
   by_cases h : P b c ∧ Q a b c
   · simp only [h.1, h.2, true_and, ite_true, ite_mul, one_mul, zero_mul]
     simp [ih b c h.1]
   · simp only [show ¬ (P b c ∧ Q a b c) from h, ite_false]
     simp [show ∀ s, ¬ (P b c ∧ Q a b c ∧ cl b c = s) from fun _ hh => h ⟨hh.1, hh.2.1⟩]
end

section

variable {R : Type*}
private theorem good_cons (P : R → R → Prop) (Q : R → R → R → Prop) (a b : R) (cs : List R) :
 good P Q (a :: b :: cs) ↔ P a b ∧
   (match cs with | [] => True | c :: _ => Q a b c) ∧ good P Q (b :: cs) := by
 cases cs <;> simp only [good, tailGood, and_true, and_comm, and_left_comm]

theorem good_iff_local [Inhabited R] (P : R → R → Prop) (Q : R → R → R → Prop) (xs : List R) :
 good P Q xs ↔
   (∀ i, i+1 < xs.length → P (xs.getD i default) (xs.getD (i+1) default)) ∧
   (∀ i, i+2 < xs.length → Q (xs.getD i default) (xs.getD (i+1) default) (xs.getD (i+2) default)) := by
 induction xs with
 | nil => simp [good]
 | cons a xs ih =>
   cases xs with
   | nil => simp [good]
   | cons b cs =>
     rw [good_cons]
     rw [ih]
     constructor
     · rintro ⟨hp,hq,ht⟩
       constructor
       · intro i hi
         cases i with
         | zero => simpa using hp
         | succ i =>
           have h := ht.1 i (by simp only [List.length_cons] at hi ⊢; omega)
           simpa [List.getD_cons_succ] using h
       · intro i hi
         cases i with
         | zero =>
           cases cs with
           | nil => simp at hi
           | cons c cs => simpa [List.getD_cons_succ] using hq
         | succ i =>
           have h := ht.2 i (by simp only [List.length_cons] at hi ⊢; omega)
           simpa [List.getD_cons_succ] using h
     · intro h
       refine ⟨?_,?_,?_,?_⟩
       · simpa [List.getD_cons_succ] using h.1 0 (by simp)
       · cases cs with
         | nil => trivial
         | cons c cs => simpa [List.getD_cons_succ] using h.2 0 (by simp)
       · intro i hi
         have hh := h.1 (i+1) (by simp only [List.length_cons] at hi ⊢; omega)
         simpa [List.getD_cons_succ] using hh
       · intro i hi
         have hh := h.2 (i+1) (by simp only [List.length_cons] at hi ⊢; omega)
         simpa [List.getD_cons_succ] using hh
end

section

variable {R J K : Type*} [Inhabited R]

def pairOK (tr : R → R → J → K) (adj : J → J → Prop) (a b : R) : Prop :=
 ∀ j j', adj j j' → tr a b j ≠ tr a b j'
def tripleOK (tr : R → R → J → K) (a b c : R) : Prop :=
 ∀ j, tr a b j ≠ tr b c j

def arrayOK (tr : R → R → J → K) (adj : J → J → Prop) (n : ℕ)
    (a : Fin (n+1) → R) : Prop :=
 (∀ i i' : Fin n, ∀ j : J, i'.val = i.val + 1 →
   tr (a i.castSucc) (a i.succ) j ≠ tr (a i'.castSucc) (a i'.succ) j) ∧
 (∀ i : Fin n, ∀ j j' : J, adj j j' →
   tr (a i.castSucc) (a i.succ) j ≠ tr (a i.castSucc) (a i.succ) j')

theorem arrayOKIffGood (tr : R → R → J → K) (adj : J → J → Prop) (n : ℕ)
    (a : Fin (n+1) → R) :
 arrayOK tr adj n a ↔ good (pairOK tr adj) (tripleOK tr) (List.ofFn a) := by
 rw [good_iff_local]
 have get (k : ℕ) (hk : k < n+1) :
     (List.ofFn a).getD k default = a ⟨k,hk⟩ := by
   rw [List.getD_eq_getElem (List.ofFn a) default (by simpa using hk), List.getElem_ofFn]
 constructor
 · intro h
   constructor
   · intro i hi
     simp only [List.length_ofFn] at hi
     have hn : i < n := by exact Nat.succ_lt_succ_iff.mp hi
     simpa only [get i (by omega), get (i+1) hi, pairOK, Fin.castSucc_mk,Fin.succ_mk] using h.2 (⟨i,hn⟩ : Fin n)
   · intro i hi
     simp only [List.length_ofFn] at hi
     have hn : i < n := by omega
     have hn' : i+1 < n := by exact Nat.succ_lt_succ_iff.mp hi
     intro j
     have h' := h.1 (⟨i,hn⟩ : Fin n) (⟨i+1,hn'⟩ : Fin n) j rfl
     simpa only [get i (by omega), get (i+1) (by omega), get (i+2) hi,Fin.castSucc_mk,Fin.succ_mk] using h'
 · intro h
   constructor
   · rintro ⟨i,hi⟩ ⟨i',hi'⟩ j hij
     dsimp at hij
     subst i'
     have hn : i+2 < n+1 := by exact Nat.succ_lt_succ hi'
     have h' := h.2 i (by simpa using hn) j
     simpa only [get i (by omega), get (i+1) (by omega), get (i+2) hn,
       Fin.castSucc_mk,Fin.succ_mk] using h'
   · rintro ⟨i,hi⟩ j j' hj
     have hn : i+1 < n+1 := by exact Nat.add_lt_add_right hi 1
     have h' := h.1 i (by simpa using hn) j j' hj
     simpa only [get i (by omega), get (i+1) hn,Fin.castSucc_mk,Fin.succ_mk] using h'

end

section

open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R S : Type*} [Fintype R] [Fintype S] [DecidableEq S]

private theorem card_good (P : R → R → Prop) (Q : R → R → R → Prop) (n : ℕ) :
 (Nat.card {a : Fin (n+2) → R // good P Q (List.ofFn a)} : ℤ) =
  ∑ a : R, ∑ b : R, if P a b then cont P Q n a b else 0 := by
 classical
 rw [card_subtype_sum]
 rw [← (Fin.consEquiv fun _ : Fin (n+2) => R).sum_comp]
 simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_cons]
 apply Finset.sum_congr rfl
 intro a _
 rw [← (Fin.consEquiv fun _ : Fin (n+1) => R).sum_comp]
 simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_cons, good]
 apply Finset.sum_congr rfl
 intro b _
 by_cases hab : P a b <;> simp [hab,cont,Fintype.card_subtype]

theorem cardMatrix (P : R → R → Prop) (Q : R → R → R → Prop)
    (cl : R → R → S) (T : Matrix S S ℤ) (v : S → ℤ)
    (hT : ∀ a b, P a b → ∀ s,
      (∑ c : R, if P b c ∧ Q a b c ∧ cl b c = s then (1:ℤ) else 0) = T (cl a b) s)
    (hv : ∀ s, (∑ a : R, ∑ b : R, if P a b ∧ cl a b = s then (1:ℤ) else 0) = v s)
    (n : ℕ) :
 (Nat.card {a : Fin (n+2) → R // good P Q (List.ofFn a)} : ℤ) =
   dotProduct v ((T ^ n).mulVec (1 : S → ℤ)) := by
 classical
 rw [card_good]
 unfold dotProduct
 simp_rw [← hv, Finset.sum_mul]
 conv_rhs => rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro a _
 conv_rhs => rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro b _
 by_cases hab : P a b
 · simp [hab,cont_matrix P Q cl T hT n a b hab]
 · simp [hab]

private theorem vector_relation_shift (T : Matrix S S ℤ) (d b : ℕ) (c : Fin d → ℤ)
    (h : (T ^ (b+d)).mulVec (1 : S → ℤ) =
      ∑ j : Fin d, c j • (T ^ (b+j.val)).mulVec (1 : S → ℤ)) (n : ℕ) :
    (T ^ (n+b+d)).mulVec (1 : S → ℤ) =
      ∑ j : Fin d, c j • (T ^ (n+b+j.val)).mulVec (1 : S → ℤ) := by
 have hh := congrArg (fun w => (T^n).mulVec w) h
 simpa only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
   ← pow_add, Nat.add_assoc] using hh

theorem scalarRelationShift (T : Matrix S S ℤ) (v : S → ℤ) (d b : ℕ) (c : Fin d → ℤ)
    (h : (T ^ (b+d)).mulVec (1 : S → ℤ) =
      ∑ j : Fin d, c j • (T ^ (b+j.val)).mulVec (1 : S → ℤ)) (n : ℕ) :
    dotProduct v ((T ^ (n+b+d)).mulVec (1 : S → ℤ)) =
      ∑ j : Fin d, c j * dotProduct v ((T ^ (n+b+j.val)).mulVec (1 : S → ℤ)) := by
 rw [vector_relation_shift T d b c h n,dotProduct_sum]
 simp only [dotProduct_smul,smul_eq_mul]

theorem tabulatedPowers (T : Matrix S S ℤ) (N : ℕ) (W : Fin (N+1) → S → ℤ)
 (h0 : W 0 = (1 : S → ℤ))
 (hstep : ∀ k : Fin N, W k.succ = T.mulVec (W k.castSucc)) :
 ∀ k : Fin (N+1), (T ^ k.val).mulVec (1 : S → ℤ) = W k := by
 intro k
 induction k using Fin.induction with
 | zero =>
   simp only [Fin.val_zero,pow_zero,Matrix.one_mulVec]
   exact h0.symm
 | succ k ih =>
   change (T ^ (k.val+1)).mulVec (1 : S → ℤ) = W k.succ
   simp only [Fin.val_castSucc] at ih
   rw [pow_succ', ← Matrix.mulVec_mulVec,ih,← hstep k]

end

end D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
