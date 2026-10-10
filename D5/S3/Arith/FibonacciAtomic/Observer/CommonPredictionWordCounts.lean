/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact generating functions and parity balance for priority-teacher word classes. -/

import D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Basic


/-!
The common two-layer priority-teacher problem on independent complete windows.
All prefix lengths and all rare-count classes are included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CommonPrediction

attribute [local instance] Classical.propDecidable


section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open scoped BigOperators Polynomial
namespace WordCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
/-- Indicator of a rare window: low, ends or high. -/
def rb : W → ℕ | .low | .ends | .high => 1 | _ => 0
/-- Indicator of the high endpoint bit. -/
def hb (a : W) : ℕ := if last a then 1 else 0
/-- Number of rare windows in a complete word. -/
def rareN {n : ℕ} (p : Fin n → W) : ℕ := ∑ i, rb (p i)
/-- Number of high endpoints in a prefix. -/
def highN {n : ℕ} (p : Fin n → W) : ℕ := ∑ i, hb (p i)
private def bw {n : ℕ} (p : Fin n → W) : Polynomial P := Polynomial.C (X ^ rareN p) * Y ^ highN p
private lemma bw_product {n : ℕ} (p : Fin n → W) :
    bw p = ∏ i, Polynomial.C (X ^ rb (p i)) * Y ^ hb (p i) := by
  unfold bw rareN highN
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, map_prod]
  rw [Finset.prod_mul_distrib]
private lemma bivariate_generating (n : ℕ) :
    (∑ p : Fin n → W, bw p) = (Polynomial.C (2+X) + Polynomial.C (2*X)*Y)^n := by
  classical
  simp_rw [bw_product]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (a : W) => Polynomial.C (X^rb a)*Y^hb a)]
  have hpoint : (∑ a : W, Polynomial.C (X ^ rb a) * Y ^ hb a) =
      Polynomial.C (2+X) + Polynomial.C (2*X)*Y := by
    simp [rb, hb, last, Finset.univ, Fintype.elems, map_add, map_mul, Polynomial.C_ofNat]
    ring
  simp_rw [hpoint]
  simp

/-- Rare-count generating polynomial at a fixed high-endpoint count. -/
def slice (n k : ℕ) : P := ∑ p : Fin n → W, if highN p = k then X ^ rareN p else 0
private lemma slice_as_coefficient (n k : ℕ) :
    slice n k = ((Polynomial.C (2+X)+Polynomial.C (2*X)*Y)^n).coeff k := by
  have h := congrArg (fun p : Polynomial P => p.coeff k) (bivariate_generating n)
  rw [Polynomial.finsetSum_coeff] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [bw, Polynomial.coeff_C_mul_X_pow]
  by_cases hk : highN p = k
  · simp [hk]
  · simp [hk, Ne.symm hk]
/-- Exact polynomial for all prefixes with a prescribed number of high endpoints. -/
lemma slice_formula (n k : ℕ) :
    slice n k = (n.choose k : P)*(2*X)^k*(2+X)^(n-k) := by
  rw [slice_as_coefficient]
  have hc : (Polynomial.C (2+X)+Polynomial.C (2*X)*Y)^n =
      ((Y+Polynomial.C (2+X))^n).comp (Polynomial.C (2*X)*Y) := by
    simp only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp,
      Polynomial.C_comp]
    rw [add_comm]
  rw [hc]
  simp only [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_X_add_C_pow]
  ring
end
end WordCounts

namespace WordCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open scoped BigOperators Polynomial
/-- Indicator of the joint-endpoint window ends. -/
def eb (a : W) : ℕ := if a = .ends then 1 else 0
/-- Number of joint-endpoint windows in a prefix. -/
def endsN {n : ℕ} (p : Fin n → W) : ℕ := ∑ i, eb (p i)
private def sw (a : W) : P := (-1)^eb a * X^rb a
private def signedWeight {n : ℕ} (p : Fin n → W) : P := ∏ i, sw (p i)
private def sbw {n : ℕ} (p : Fin n → W) : Polynomial P := Polynomial.C (signedWeight p)*Y^highN p
private lemma signed_weight_formula {n : ℕ} (p : Fin n → W) :
    signedWeight p = (-1)^endsN p * X^rareN p := by
  simp only [signedWeight, sw, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    endsN, rareN]
private lemma sbw_product {n : ℕ} (p : Fin n → W) :
    sbw p = ∏ i, Polynomial.C (sw (p i))*Y^hb (p i) := by
  unfold sbw signedWeight highN
  rw [← Finset.prod_pow_eq_pow_sum, map_prod, Finset.prod_mul_distrib]
private lemma signed_local : (∑ a : W, Polynomial.C (sw a)*Y^hb a) = Polynomial.C (2+X) := by
  simp [sw, rb, hb, eb, last, Finset.univ, Fintype.elems, map_add, map_ofNat]
  ring
private lemma signed_local_low : (∑ a : W, if last a=false then Polynomial.C (sw a)*Y^hb a else 0) =
    Polynomial.C (2+X) := by
  simp [sw, rb, hb, eb, last, Finset.univ, Fintype.elems, map_add, map_ofNat]
  ring
private lemma signed_local_high : (∑ a : W, if last a=true then Polynomial.C (sw a)*Y^hb a else 0) = 0 := by
  simp [sw, rb, hb, eb, last, Finset.univ, Fintype.elems] <;> ring
private def fw {n : ℕ} (i j : Fin n) (h : Bool) (a : W) : Polynomial P :=
  if j=i then if last a=h then Polynomial.C (sw a)*Y^hb a else 0
  else Polynomial.C (sw a)*Y^hb a
private lemma forced_point {n : ℕ} (i : Fin n) (h : Bool) (p : Fin n → W) :
    (if last (p i)=h then sbw p else 0) = ∏ j, fw i j h (p j) := by
  classical
  by_cases hi : last (p i)=h
  · rw [if_pos hi, sbw_product]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases he : j=i
    · subst j; simp [fw, hi]
    · simp [fw, he]
  · rw [if_neg hi]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [fw, hi]
private lemma forced_signed_generating {n : ℕ} (i : Fin n) (h : Bool) :
    (∑ p : Fin n → W, if last (p i)=h then sbw p else 0) =
      if h then 0 else Polynomial.C ((2+X)^n) := by
  classical
  simp_rw [forced_point]
  rw [← Fintype.prod_sum]
  cases h
  · have hh (j : Fin n) : (∑ a : W, fw i j false a) = Polynomial.C (2+X) := by
      by_cases he : j=i
      · simpa [fw, he] using signed_local_low
      · simpa [fw, he] using signed_local
    simp_rw [hh]
    simp
  · simp only [Bool.true_eq, ↓reduceIte]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa [fw] using signed_local_high

private lemma forced_signed_slice_zero {n : ℕ} (i : Fin n) (h : Bool) (k : ℕ) (hk : 0 < k) :
    (∑ p : Fin n → W, if highN p=k ∧ last (p i)=h then signedWeight p else 0) = 0 := by
  have eqn := congrArg (fun p : Polynomial P => p.coeff k) (forced_signed_generating i h)
  rw [Polynomial.finsetSum_coeff] at eqn
  have rhs : (if h then (0 : Polynomial P) else Polynomial.C ((2+X)^n)).coeff k = 0 := by
    cases h <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Polynomial.coeff_zero, Polynomial.coeff_C_of_ne_zero (Nat.ne_of_gt hk)]
  rw [rhs] at eqn
  calc
    (∑ p : Fin n → W, if highN p=k ∧ last (p i)=h then signedWeight p else 0) =
        ∑ p : Fin n → W, (if last (p i)=h then sbw p else 0).coeff k := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hh : last (p i)=h <;> by_cases hnk : highN p=k <;>
        simp only [hh, hnk, and_self, and_true, and_false, true_and, false_and, ↓reduceIte, sbw, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero, eq_comm] <;> split_ifs <;> simp_all
    _ = 0 := eqn

/-- The parity of the number of joint-endpoint windows. -/
def prefixCoin {n : ℕ} (p : Fin n → W) : Bool := decide (endsN p % 2 = 1)
private lemma signed_weight_coin {n : ℕ} (p : Fin n → W) :
    signedWeight p = if prefixCoin p then -X^rareN p else X^rareN p := by
  rw [signed_weight_formula, neg_one_pow_eq_pow_mod_two]
  have hmod : endsN p % 2 = 0 ∨ endsN p % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [prefixCoin, hmod]
/-- Positive high-endpoint fibers have equal weights at both coin values, even after fixing one bit. -/
lemma forced_coin_balance {n : ℕ} (i : Fin n) (h : Bool) (k : ℕ) (hk : 0 < k) :
    (∑ p : Fin n → W, if highN p=k ∧ last (p i)=h ∧ prefixCoin p=false then X^rareN p else 0) =
    (∑ p : Fin n → W, if highN p=k ∧ last (p i)=h ∧ prefixCoin p=true then X^rareN p else 0) := by
  have hs := forced_signed_slice_zero i h k hk
  have hp (p : Fin n → W) :
      (if highN p=k ∧ last (p i)=h then signedWeight p else 0) =
      (if highN p=k ∧ last (p i)=h ∧ prefixCoin p=false then X^rareN p else 0) -
      (if highN p=k ∧ last (p i)=h ∧ prefixCoin p=true then X^rareN p else 0) := by
    rw [signed_weight_coin]
    by_cases hnk : highN p=k <;> by_cases hh : last (p i)=h <;> cases hc : prefixCoin p <;>
      simp [hnk, hh, hc]
  rw [Finset.sum_congr rfl (fun p _ => hp p), Finset.sum_sub_distrib] at hs
  exact sub_eq_zero.mp hs
end
end WordCounts

namespace WordCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open scoped BigOperators Polynomial
private lemma positive_local : (∑ a : W, Polynomial.C (X^rb a)*Y^hb a) =
    Polynomial.C (2+X)+Polynomial.C (2*X)*Y := by
  simp [rb, hb, last, Finset.univ, Fintype.elems, map_add, map_mul, Polynomial.C_ofNat]
  ring
private lemma positive_local_low : (∑ a : W, if last a=false then Polynomial.C (X^rb a)*Y^hb a else 0) =
    Polynomial.C (2+X) := by
  simp [rb, hb, last, Finset.univ, Fintype.elems, map_add, map_ofNat]
  ring
private def pfw {n : ℕ} (i j : Fin n) (a : W) : Polynomial P :=
  if j=i then if last a=false then Polynomial.C (X^rb a)*Y^hb a else 0
  else Polynomial.C (X^rb a)*Y^hb a
private lemma positive_forced_point {n : ℕ} (i : Fin n) (p : Fin n → W) :
    (if last (p i)=false then bw p else 0) = ∏ j, pfw i j (p j) := by
  classical
  by_cases hi : last (p i)=false
  · rw [if_pos hi, bw_product]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases he : j=i
    · subst j; simp [pfw, hi]
    · simp [pfw, he]
  · rw [if_neg hi]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [pfw, hi]
private lemma forced_positive_generating {n : ℕ} (i : Fin n) :
    (∑ p : Fin n → W, if last (p i)=false then bw p else 0) =
      Polynomial.C (2+X)*(Polynomial.C (2+X)+Polynomial.C (2*X)*Y)^(n-1) := by
  classical
  simp_rw [positive_forced_point]
  rw [← Fintype.prod_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hhead : (∑ a : W, pfw i i a) = Polynomial.C (2+X) := by
    simpa [pfw] using positive_local_low
  rw [hhead]
  congr 1
  have hrest (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      (∑ a : W, pfw i j a) = Polynomial.C (2+X)+Polynomial.C (2*X)*Y := by
    simpa [pfw, (Finset.mem_erase.mp hj).1] using positive_local
  rw [Finset.prod_congr rfl hrest]
  simp
/-- A prefix fiber with a fixed low high-endpoint bit has an explicit generating polynomial. -/
lemma forced_positive_slice {n : ℕ} (i : Fin n) (k : ℕ) :
    (∑ p : Fin n → W, if highN p=k ∧ last (p i)=false then X^rareN p else 0) =
      (2+X)*slice (n-1) k := by
  have eqn := congrArg (fun p : Polynomial P => p.coeff k) (forced_positive_generating i)
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, ← slice_as_coefficient] at eqn
  rw [← eqn]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hh : last (p i)=false <;> by_cases hnk : highN p=k <;>
    simp only [hh, hnk, and_self, and_true, and_false, true_and, false_and, ↓reduceIte, bw, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero, eq_comm] <;> split_ifs <;> simp_all
end
end WordCounts

namespace WordCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open scoped BigOperators Polynomial
private lemma hb_le (a : W) : hb a ≤ 1 := by cases a <;> decide
/-- The high-endpoint count is bounded by the prefix length. -/
lemma high_n_le {n : ℕ} (p : Fin n → W) : highN p ≤ n := by
  calc
    highN p ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => hb_le (p i))
    _ = n := by simp
/-- A prefix with no high endpoints has a false high bit at every position. -/
lemma high_n_zero_last {n : ℕ} (p : Fin n → W) (i : Fin n) (h : highN p=0) : last (p i)=false := by
  have hi := Finset.single_le_sum (s := Finset.univ) (f := fun j => hb (p j))
    (fun j _ => Nat.zero_le (hb (p j))) (Finset.mem_univ i)
  change hb (p i) ≤ highN p at hi
  rw [h] at hi
  cases hl : last (p i) <;> simp_all [hb]
/-- One false high bit excludes the all-high prefix class. -/
lemma high_n_last_false {n : ℕ} (p : Fin n → W) (i : Fin n) (h : last (p i)=false) : highN p < n := by
  classical
  have he : highN p=∑ j ∈ Finset.univ.erase i, hb (p j) := by
    rw [highN, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp [hb, h]
  have hbnd := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hb_le (p j))
  rw [← he] at hbnd
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin] at hbnd
  have hn := i.isLt
  omega
end
end WordCounts
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open scoped BigOperators Polynomial
namespace ReservoirWords
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "X" => (Polynomial.X : Polynomial ℕ)
private lemma prefix_generating (m : ℕ) :
    (∑ x : Fin m → W, X ^ WordCounts.rareN x) = (2 + 3 * X) ^ m := by
  classical
  have hp := Fintype.prod_sum (fun (_ : Fin m) (a : W) => X ^ WordCounts.rb a)
  have hpoint (p : Fin m → W) : X ^ WordCounts.rareN p = ∏ i, X ^ WordCounts.rb (p i) := by
    simp [WordCounts.rareN, Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_congr rfl (fun p _ => hpoint p), ← hp]
  have hw : (∑ a : W, X ^ WordCounts.rb a) = 2+3*X := by
    simp [WordCounts.rb,Finset.univ,Fintype.elems]; ring
  rw [hw]
  simp [Finset.prod_const, Fintype.card_fin]
/-- The three allowed first-anchor windows of the fixed-label reservoir. -/
def qok (a : W) : Prop := a ∈ ({.zero,.middle,.high} : Finset W)
/-- The two allowed last-anchor windows of the fixed-label reservoir. -/
def vok (a : W) : Prop := a ∈ ({.low,.ends} : Finset W)
private noncomputable def aw (q r v : W) : Polynomial ℕ := by
  classical exact if qok q ∧ r=.high ∧ vok v then X^(WordCounts.rb q + WordCounts.rb r + WordCounts.rb v) else 0
private lemma anchor_generating :
    (∑ q : W, ∑ r : W, ∑ v : W, aw q r v) = 2 * X^2 * (2+X) := by
  classical
  simp [aw,qok,vok,WordCounts.rb,Finset.univ,Fintype.elems]
  ring

/-- Reduced words on which all left teachers are zero and all right teachers are two. -/
def isReservoir {m : ℕ} (x : LegalPriorityTeacher.Input (m+3)) : Prop :=
  qok (x ⟨m, by omega⟩) ∧ x ⟨m+1, by omega⟩ = .high ∧ vok (x ⟨m+2, by omega⟩)
private def fullWeight {m : ℕ} (x : LegalPriorityTeacher.Input (m+3)) : Polynomial ℕ := by
  classical exact if isReservoir x then X ^ WordCounts.rareN x else 0
private lemma append_res (m : ℕ) (p : Fin m → W) (a : Fin 3 → W) :
    isReservoir (Fin.append p a) ↔ qok (a 0) ∧ a 1 = .high ∧ vok (a 2) := by
  change qok (Fin.append p a (Fin.natAdd m 0)) ∧
    Fin.append p a (Fin.natAdd m 1) = .high ∧
    vok (Fin.append p a (Fin.natAdd m 2)) ↔ _
  simp
/-- Rare count splits between the prefix and its three anchors. -/
lemma append_rare (m : ℕ) (p : Fin m → W) (a : Fin 3 → W) :
    WordCounts.rareN (Fin.append p a) = WordCounts.rareN p + (WordCounts.rb (a 0) + WordCounts.rb (a 1) + WordCounts.rb (a 2)) := by
  simp [WordCounts.rareN, Fin.sum_univ_add, Fin.sum_univ_three, add_assoc]
private lemma full_append (m : ℕ) (p : Fin m → W) (a : Fin 3 → W) :
    fullWeight (Fin.append p a) = X ^ WordCounts.rareN p * aw (a 0) (a 1) (a 2) := by
  classical
  rw [fullWeight, append_res, append_rare]
  by_cases h : qok (a 0) ∧ a 1 = .high ∧ vok (a 2)
  · simp [aw, h, pow_add]
  · simp [aw, h]
/-- The three actual anchor windows as an ordered triple. -/
def anchorEquiv : (Fin 3 → W) ≃ W × W × W where
  toFun a := (a 0, a 1, a 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv t := by rcases t with ⟨q,r,v⟩; rfl
private lemma anchor_function_sum :
    (∑ a : Fin 3 → W, aw (a 0) (a 1) (a 2)) = 2 * X^2*(2+X) := by
  have hs := Equiv.sum_comp anchorEquiv (fun t : W × W × W => aw t.1 t.2.1 t.2.2)
  change (∑ a : Fin 3 → W, aw (anchorEquiv a).1 (anchorEquiv a).2.1
    (anchorEquiv a).2.2) = _
  rw [hs, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  exact anchor_generating
private lemma actual_reservoir_generating (m : ℕ) :
    (∑ x : LegalPriorityTeacher.Input (m+3), fullWeight x) = 2*X^2*(2+X)*(2+3*X)^m := by
  classical
  rw [← Equiv.sum_comp (Fin.appendEquiv m 3)]
  change (∑ pa : (Fin m → W) × (Fin 3 → W), fullWeight (Fin.append pa.1 pa.2)) = _
  simp_rw [full_append]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, anchor_function_sum]
  rw [← Finset.sum_mul, prefix_generating]
  ring

local notation "Reservoir" m => ({x : LegalPriorityTeacher.Input (m+3) // isReservoir x})
attribute [local instance] Classical.propDecidable
private lemma reservoir_subtype_generating (m : ℕ) :
    (∑ x : Reservoir m, X ^ WordCounts.rareN x.val) = 2*X^2*(2+X)*(2+3*X)^m := by
  classical
  have hs := Finset.sum_subtype (p := @isReservoir m) (F := inferInstance) (Finset.univ.filter (@isReservoir m))
    (by simp) (fun x : LegalPriorityTeacher.Input (m+3) => X ^ WordCounts.rareN x)
  rw [← hs]
  simpa only [Finset.sum_filter, fullWeight] using actual_reservoir_generating m

/-- Cardinality of the actual reservoir class at rare count z. -/
def Nz (m z : ℕ) : ℕ := Fintype.card {x : Reservoir m // WordCounts.rareN x.val = z}
/-- Exact cardinalities of all reservoir mass classes, for every prefix length. -/
lemma actual_nz_identity (m z : ℕ) :
    Nz m z = (2*X^2*(2+X)*(2+3*X)^m).coeff z := by
  classical
  have h := congrArg (fun p : Polynomial ℕ => p.coeff z) (reservoir_subtype_generating m)
  rw [Polynomial.finsetSum_coeff] at h
  calc
    Nz m z = ∑ x : Reservoir m, if WordCounts.rareN x.val = z then 1 else 0 := by
      unfold Nz
      rw [Fintype.card_subtype]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = _ := by
      rw [← h]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Polynomial.coeff_X_pow]
      by_cases hz : WordCounts.rareN x.val = z
      · simp [hz]
      · simp [hz, Ne.symm hz]

private lemma prefix_rare_perm {m : ℕ} (p : Fin m → W) (σ : Equiv.Perm (Fin m)) :
    WordCounts.rareN (p ∘ σ) = WordCounts.rareN p := by
  unfold WordCounts.rareN
  simpa [Function.comp_def] using Equiv.sum_comp σ (fun i : Fin m => WordCounts.rb (p i))
/-- Prefix permutations preserve rare count and reservoir membership. -/
lemma actual_prefix_perm {m : ℕ} (p : Fin m → W) (a : Fin 3 → W)
    (σ : Equiv.Perm (Fin m)) :
    WordCounts.rareN (Fin.append (p ∘ σ) a) = WordCounts.rareN (Fin.append p a) ∧
    (isReservoir (Fin.append (p ∘ σ) a) ↔ isReservoir (Fin.append p a)) := by
  simp [append_rare, prefix_rare_perm, append_res]
end
end ReservoirWords

open scoped BigOperators
namespace TeacherLabels
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Roles teacher)
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
/-- The teacher at prefix position i and the first two anchors. -/
def leftRoles {m : ℕ} (i : Fin m) : Roles (m+3) where
  p := i.castAdd 3
  q := ⟨m, by omega⟩
  r := ⟨m+1, by omega⟩
  pq := by change i.val < m; exact i.isLt
  qr := by change m < m+1; omega

/-- The teacher at prefix position i and the last two anchors. -/
def rightRoles {m : ℕ} (i : Fin m) : Roles (m+3) where
  p := i.castAdd 3
  q := ⟨m+1, by omega⟩
  r := ⟨m+2, by omega⟩
  pq := by change i.val < m+1; omega
  qr := by change m+1 < m+2; omega

/-- Actual left-teacher label after separating prefix and anchor coordinates. -/
lemma actual_left_label {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) (i : Fin m) :
    teacher (leftRoles i) (Fin.append p a) =
      if last (p i) && first (a 0) then 1 else if last (a 0) && first (a 1) then 2 else 0 := by
  change (if last (Fin.append p a (i.castAdd 3)) && first (Fin.append p a (Fin.natAdd m 0)) then 1
    else if last (Fin.append p a (Fin.natAdd m 0)) && first (Fin.append p a (Fin.natAdd m 1)) then 2 else 0) = _
  simp
/-- Actual right-teacher label after separating prefix and anchor coordinates. -/
lemma actual_right_label {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) (i : Fin m) :
    teacher (rightRoles i) (Fin.append p a) =
      if last (p i) && first (a 1) then 1 else if last (a 1) && first (a 2) then 2 else 0 := by
  change (if last (Fin.append p a (i.castAdd 3)) && first (Fin.append p a (Fin.natAdd m 1)) then 1
    else if last (Fin.append p a (Fin.natAdd m 1)) && first (Fin.append p a (Fin.natAdd m 2)) then 2 else 0) = _
  simp
/-- All reservoir words have simultaneous left label zero and right label two. -/
lemma actual_reservoir_flat {m : ℕ} (p : Fin m → W) (q v : W)
    (hq : q = .zero ∨ q = .middle ∨ q = .high) (hv : v = .low ∨ v = .ends) (i : Fin m) :
    teacher (leftRoles i) (Fin.append p ![q,.high,v]) = 0 ∧
    teacher (rightRoles i) (Fin.append p ![q,.high,v]) = 2 := by
  rw [actual_left_label, actual_right_label]
  rcases hq with rfl | rfl | rfl <;> rcases hv with rfl | rfl <;> simp [first, last]
end
end TeacherLabels
open scoped BigOperators Polynomial
namespace MajorityGeometry
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
/-- Left-teacher label as a function of its prefix high bit and the two anchors. -/
def aLabel (h : Bool) (q r : W) : Fin 3 :=
  if h && first q then 1 else if last q && first r then 2 else 0
/-- Right-teacher label as a function of its prefix high bit and the two anchors. -/
def bLabel (h : Bool) (r v : W) : Fin 3 :=
  if h && first r then 1 else if last r && first v then 2 else 0
/-- Integer zero-one classification loss. -/
def err (a c : Fin 3) : ℤ := if a = c then 0 else 1
/-- Signed difference of left and right classification losses at one high bit. -/
def ld (h : Bool) (q r v : W) (c : Fin 3) : ℤ :=
  err (aLabel h q r) c - err (bLabel h r v) c
/-- Total teacher votes when k of the m prefix high bits are true. -/
def vt (m k : ℕ) (q r v : W) (c : Fin 3) : ℕ :=
  (m-k)*((if aLabel false q r = c then 1 else 0)+(if bLabel false r v = c then 1 else 0))+
  k*((if aLabel true q r = c then 1 else 0)+(if bLabel true r v = c then 1 else 0))
private def delta (m k : ℕ) (q r v : W) (c : Fin 3) : ℤ :=
  (m-k:ℕ)*ld false q r v c + (k:ℤ)*ld true q r v c
private def top0 (m k : ℕ) (q r v : W) := vt m k q r v 1 ≤ vt m k q r v 0 ∧ vt m k q r v 2 ≤ vt m k q r v 0
private def top1 (m k : ℕ) (q r v : W) := vt m k q r v 0 ≤ vt m k q r v 1 ∧ vt m k q r v 2 ≤ vt m k q r v 1 ∧ ¬(vt m k q r v 0 = vt m k q r v 1 ∧ vt m k q r v 1 = vt m k q r v 2)
private def top2 (m k : ℕ) (q r v : W) := vt m k q r v 0 ≤ vt m k q r v 2 ∧ vt m k q r v 1 ≤ vt m k q r v 2
/-- First maximal-vote label, with the triple-tie convention used by the selector. -/
def firstTop (m k : ℕ) (q r v : W) : Fin 3 := if top0 m k q r v then 0 else if top1 m k q r v then 1 else 2
private def lastTop (m k : ℕ) (q r v : W) : Fin 3 := if top2 m k q r v then 2 else if top1 m k q r v then 1 else 0
/-- Majority label with a coin to balance tied left-right discrepancies. -/
def selector (m k : ℕ) (q r v : W) (coin : Bool) : Fin 3 :=
  if 0 < k ∧ k < m ∧ 3*k ≤ m then
    if top0 m k q r v ∧ (¬ top1 m k q r v ∨ delta m k q r v 1 ≤ delta m k q r v 0) ∧
      (¬top2 m k q r v ∨ delta m k q r v 2 ≤ delta m k q r v 0) then 0
    else if top1 m k q r v ∧ (¬top2 m k q r v ∨ delta m k q r v 2 ≤ delta m k q r v 1) then 1 else 2
  else if delta m k q r v (firstTop m k q r v) = delta m k q r v (lastTop m k q r v) then firstTop m k q r v
  else if coin then lastTop m k q r v else firstTop m k q r v

/-- The ordered rational-breakpoint region of a prefix endpoint count. -/
def region (m k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = m then 7 else if 3*k ≤ m then 1 else
  if 2*k < m then 2 else if 2*k = m then 3 else if 3*k < 2*m then 4 else if 3*k = 2*m then 5 else 6
/-- A fixed pair realizing each of the eight selector regions. -/
def representative : ℕ → ℕ × ℕ
  | 0 => (1,0) | 1 => (4,1) | 2 => (5,2) | 3 => (4,2)
  | 4 => (5,3) | 5 => (3,2) | 6 => (10,9) | _ => (1,1)

set_option maxHeartbeats 8000000 in
private lemma selector_region_one (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hkm : k < m) (h3 : 3*k ≤ m)
    (q r v : W) (coin : Bool) : selector m k q r v coin = selector 4 1 q r v coin := by
  cases q <;> cases r <;> cases v <;> cases coin <;>
    simp [selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel, ld, err, first, last,
      hm, hk, hkm, h3] <;>
    (try split_ifs) <;> omega

set_option maxHeartbeats 8000000 in
/-- The zero-high prefix has the same selector as its fixed representative. -/
lemma selector_region_zero (m : ℕ) (hm : 0 < m)
    (q r v : W) (coin : Bool) : selector m 0 q r v coin = selector 1 0 q r v coin := by
  cases q <;> cases r <;> cases v <;> cases coin <;>
    simp [selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel, ld, err, first, last,
      hm] <;>
    (try split_ifs) <;> omega

set_option maxHeartbeats 8000000 in
private lemma selector_region_two (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hkm : k < m) (h3 : m < 3*k) (h2 : 2*k < m)
    (q r v : W) (coin : Bool) : selector m k q r v coin = selector 5 2 q r v coin := by
  cases q <;> cases r <;> cases v <;> cases coin <;>
    simp [selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel, ld, err, first, last,
      hm, hk, hkm, h3, h2] <;>
    (try split_ifs) <;> omega

set_option maxHeartbeats 8000000 in
private lemma selector_region_three (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hkm : k < m) (h2 : 2*k = m)
    (q r v : W) (coin : Bool) : selector m k q r v coin = selector 4 2 q r v coin := by
  cases q <;> cases r <;> cases v <;> cases coin <;>
    simp [selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel, ld, err, first, last,
      hm, hk, hkm, h2] <;>
    (try split_ifs) <;> omega

set_option maxHeartbeats 8000000 in
private lemma selector_region_four (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hkm : k < m) (h2 : m < 2*k) (h3 : 3*k < 2*m)
    (q r v : W) (coin : Bool) : selector m k q r v coin = selector 5 3 q r v coin := by
  cases q <;> cases r <;> cases v <;> cases coin <;>
    simp [selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel, ld, err, first, last,
      hm, hk, hkm, h3, h2] <;>
    (try split_ifs) <;> omega

set_option maxHeartbeats 8000000 in
private lemma selector_region_five (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hkm : k < m) (h3 : 3*k = 2*m)
    (q r v : W) (coin : Bool) : selector m k q r v coin = selector 3 2 q r v coin := by
  cases q <;> cases r <;> cases v <;> cases coin <;>
    simp [selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel, ld, err, first, last,
      hm, hk, hkm, h3] <;>
    (try split_ifs) <;> omega

set_option maxHeartbeats 8000000 in
private lemma selector_region_six (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hkm : k < m) (h3 : 2*m < 3*k)
    (q r v : W) (coin : Bool) : selector m k q r v coin = selector 10 9 q r v coin := by
  cases q <;> cases r <;> cases v <;> cases coin <;>
    simp [selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel, ld, err, first, last,
      hm, hk, hkm, h3] <;>
    (try split_ifs) <;> omega

set_option maxHeartbeats 8000000 in
private lemma selector_region_seven (m : ℕ) (hm : 0 < m)
    (q r v : W) (coin : Bool) : selector m m q r v coin = selector 1 1 q r v coin := by
  cases q <;> cases r <;> cases v <;> cases coin <;>
    simp [selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel, ld, err, first, last,
      hm] <;>
    (try split_ifs) <;> omega

/-- Selector choices agree with the representative throughout each prefix-count region. -/
lemma selector_stable (m k : ℕ) (hm : 0 < m) (hkm : k ≤ m) (q r v : W) (coin : Bool) :
    selector m k q r v coin =
      selector (representative (region m k)).1 (representative (region m k)).2 q r v coin := by
  by_cases h0 : k = 0
  · subst k; simpa [region, representative] using selector_region_zero m hm q r v coin
  by_cases he : k = m
  · subst k; simpa [region, representative, show m≠0 by omega] using selector_region_seven m hm q r v coin
  have hk : 0 < k := by omega
  have hlt : k < m := by omega
  by_cases h3 : 3*k ≤ m
  · simpa [region, representative, h0, he, h3] using selector_region_one m k hm hk hlt h3 q r v coin
  by_cases h2 : 2*k < m
  · simpa [region, representative, h0, he, h3, h2] using selector_region_two m k hm hk hlt (by omega) h2 q r v coin
  by_cases h2e : 2*k = m
  · simpa [region, representative, h0, he, h3, h2, h2e] using selector_region_three m k hm hk hlt h2e q r v coin
  by_cases h32 : 3*k < 2*m
  · simpa [region, representative, h0, he, h3, h2, h2e, h32] using selector_region_four m k hm hk hlt (by omega) h32 q r v coin
  by_cases h32e : 3*k = 2*m
  · simpa [region, representative, h0, he, h3, h2, h2e, h32, h32e, (show ¬ (2 * m ≤ m) from by omega)] using selector_region_five m k hm hk hlt h32e q r v coin
  · simpa [region, representative, h0, he, h3, h2, h2e, h32, h32e] using selector_region_six m k hm hk hlt (by omega) q r v coin

/-- The first selected label maximizes teacher votes. -/
lemma first_top_majority (m k : ℕ) (q r v : W) (c : Fin 3) :
    vt m k q r v c ≤ vt m k q r v (firstTop m k q r v) := by
  have hc : c=0 ∨ c=1 ∨ c=2 := by omega
  rcases hc with rfl | rfl | rfl <;> unfold firstTop <;>
    split_ifs <;> simp only [top0, top1, top2] at * <;> omega
private lemma last_top_majority (m k : ℕ) (q r v : W) (c : Fin 3) :
    vt m k q r v c ≤ vt m k q r v (lastTop m k q r v) := by
  have hc : c=0 ∨ c=1 ∨ c=2 := by omega
  rcases hc with rfl | rfl | rfl <;> unfold lastTop <;>
    split_ifs <;> simp only [top0, top1, top2] at * <;> omega
/-- Every coin choice of the selector maximizes total teacher votes. -/
lemma selector_majority (m k : ℕ) (q r v : W) (coin : Bool) (c : Fin 3) :
    vt m k q r v c ≤ vt m k q r v (selector m k q r v coin) := by
  unfold selector
  split_ifs
  all_goals (try (first | exact first_top_majority m k q r v c | exact last_top_majority m k q r v c))
  all_goals
    have hc : c=0 ∨ c=1 ∨ c=2 := by omega
    rcases hc with rfl | rfl | rfl <;> simp only [top0, top1, top2] at * <;> omega

/-- Reservoir condition on an ordered anchor triple. -/
def isRes (q r v : W) : Prop := q∈({.zero,.middle,.high}:Finset W) ∧ r = .high ∧ v∈({.low,.ends}:Finset W)
/-- Polynomial discrepancy of the two coin choices over all non-reservoir anchors. -/
def pairAnchor (m k : ℕ) (h : Bool) : Polynomial ℤ := by
  classical exact ∑ q : W, ∑ r : W, ∑ v : W,
    if isRes q r v then 0 else
      Polynomial.C (ld h q r v (selector m k q r v false) + ld h q r v (selector m k q r v true)) *
        Polynomial.X ^ (WordCounts.rb q + WordCounts.rb r + WordCounts.rb v)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the one selector representative. -/
lemma pair_anchor_one (h : Bool) :
    pairAnchor 4 1 h = if h then 0 else -8*Polynomial.X^2+12*Polynomial.X^3 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the two selector representative. -/
lemma pair_anchor_two (h : Bool) :
    pairAnchor 5 2 h = if h then 0 else -16*Polynomial.X^2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the three selector representative. -/
lemma pair_anchor_three (h : Bool) :
    pairAnchor 4 2 h = if h then 0 else -16*Polynomial.X^2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the four selector representative. -/
lemma pair_anchor_four (h : Bool) :
    pairAnchor 5 3 h = if h then 0 else -16*Polynomial.X^2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the five selector representative. -/
lemma pair_anchor_five (h : Bool) :
    pairAnchor 3 2 h = if h then 0 else -16*Polynomial.X^2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the six selector representative. -/
lemma pair_anchor_six (h : Bool) :
    pairAnchor 10 9 h = if h then 0 else -16*Polynomial.X^2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the seven selector representative. -/
lemma pair_anchor_seven : pairAnchor 1 1 true = 0 := by
  simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel,
    ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring

/-- Tie coin obtained from the joint endpoints of the three anchors. -/
def anchorCoin (q r v : W) : Bool :=
  if first v then decide (v=.ends) else if last q then decide (q=.ends) else decide (r=.ends)
/-- Discrepancy polynomial of the zero-high prefix class. -/
def zeroAnchor : Polynomial ℤ := by
  classical exact ∑ q : W, ∑ r : W, ∑ v : W,
    if isRes q r v then 0 else
      Polynomial.C (ld false q r v (selector 1 0 q r v (anchorCoin q r v))) *
        Polynomial.X ^ (WordCounts.rb q+WordCounts.rb r+WordCounts.rb v)
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- The zero-high prefix discrepancy cancels exactly. -/
lemma zero_anchor_eq_zero : zeroAnchor=0 := by
  simp [zeroAnchor, isRes, anchorCoin, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel,
    ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring

end
end MajorityGeometry
end

end D5.S3.Arith.FibonacciAtomic.CommonPrediction
