/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts
   generality: G
   mirror - B: D5 / B / S3 / Arith / FibonacciAtomic / Observer / CommonPredictionWordCounts
   mirror - E: none(waiver:unbounded - symbolic - proof)
   anchors: []
   utility: none
   digest: Exact generating functions and parity balance for priority - teacher word classes. -/
import D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Sum
/-!
The common two - layer priority - teacher problem on independent complete windows.
All prefix lengths and all rare - count classes are included.
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
    (∑ p : Fin n → W, bw p) = (Polynomial.C (2 + X) + Polynomial.C (2 * X) * Y) ^ n := by
  classical
  simp_rw [bw_product]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (a : W) => Polynomial.C (X ^ rb a) * Y ^ hb a)]
  have hpoint : (∑ a : W, Polynomial.C (X ^ rb a) * Y ^ hb a) =
      Polynomial.C (2 + X) + Polynomial.C (2 * X) * Y := by
    simp [rb, hb, last, Finset.univ, Fintype.elems, map_add, map_mul, Polynomial.C_ofNat]
    ring
  simp_rw [hpoint]
  simp
/-- Rare-count generating polynomial at a fixed high-endpoint count. -/
def slice (n k : ℕ) : P := ∑ p : Fin n → W, if highN p = k then X ^ rareN p else 0
private lemma slice_as_coefficient (n k : ℕ) :
    slice n k = ((Polynomial.C (2 + X) + Polynomial.C (2 * X) * Y) ^ n).coeff k := by
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
    slice n k = (n.choose k : P) * (2 * X) ^ k * (2 + X) ^ (n - k) := by
  rw [slice_as_coefficient]
  have hc : (Polynomial.C (2 + X) + Polynomial.C (2 * X) * Y) ^ n =
      ((Y + Polynomial.C (2 + X)) ^ n).comp (Polynomial.C (2 * X) * Y) := by
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
private def sw (a : W) : P := (-1) ^ eb a * X ^ rb a
private def signedWeight {n : ℕ} (p : Fin n → W) : P := ∏ i, sw (p i)
private def sbw {n : ℕ} (p : Fin n → W) : Polynomial P := Polynomial.C (signedWeight p)
  * Y ^ highN p
private lemma signed_weight_formula {n : ℕ} (p : Fin n → W) :
    signedWeight p = (-1) ^ endsN p * X ^ rareN p := by
  simp only [signedWeight, sw, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    endsN, rareN]
private lemma sbw_product {n : ℕ} (p : Fin n → W) :
    sbw p = ∏ i, Polynomial.C (sw (p i)) * Y ^ hb (p i) := by
  unfold sbw signedWeight highN
  rw [← Finset.prod_pow_eq_pow_sum, map_prod, Finset.prod_mul_distrib]
private lemma signed_local : (∑ a : W, Polynomial.C (sw a) * Y ^ hb a) = Polynomial.C (2 + X) := by
  simp [sw, rb, hb, eb, last, Finset.univ, Fintype.elems, map_add, map_ofNat]
  ring
private lemma signed_local_low : (∑ a : W, if last a = false then Polynomial.C (sw a)
  * Y ^ hb a else 0) =
    Polynomial.C (2 + X) := by
  simp [sw, rb, hb, eb, last, Finset.univ, Fintype.elems, map_add, map_ofNat]
  ring
private lemma signed_local_high : (∑ a : W, if last a = true then Polynomial.C (sw a)
  * Y ^ hb a else 0) = 0 := by
  simp [sw, rb, hb, eb, last, Finset.univ, Fintype.elems] <;> ring
private def fw {n : ℕ} (i j : Fin n) (h : Bool) (a : W) : Polynomial P :=
  if j = i then if last a = h then Polynomial.C (sw a) * Y ^ hb a else 0
  else Polynomial.C (sw a) * Y ^ hb a
private lemma forced_point {n : ℕ} (i : Fin n) (h : Bool) (p : Fin n → W) :
    (if last (p i) = h then sbw p else 0) = ∏ j, fw i j h (p j) := by
  classical
  by_cases hi : last (p i) = h
  · rw [if_pos hi, sbw_product]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases he : j = i
    · subst j; simp [fw, hi]
    · simp [fw, he]
  · rw [if_neg hi]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [fw, hi]
private lemma forced_signed_generating {n : ℕ} (i : Fin n) (h : Bool) :
    (∑ p : Fin n → W, if last (p i) = h then sbw p else 0) =
      if h then 0 else Polynomial.C ((2 + X) ^ n) := by
  classical
  simp_rw [forced_point]
  rw [← Fintype.prod_sum]
  cases h
  · have hh (j : Fin n) : (∑ a : W, fw i j false a) = Polynomial.C (2 + X) := by
      by_cases he : j = i
      · simpa [fw, he] using signed_local_low
      · simpa [fw, he] using signed_local
    simp_rw [hh]
    simp
  · simp only [Bool.true_eq, ↓reduceIte]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa [fw] using signed_local_high
private lemma forced_signed_slice_zero {n : ℕ} (i : Fin n) (h : Bool) (k : ℕ) (hk : 0 < k) :
    (∑ p : Fin n → W, if highN p = k ∧ last (p i) = h then signedWeight p else 0) = 0 := by
  have eqn := congrArg (fun p : Polynomial P => p.coeff k) (forced_signed_generating i h)
  rw [Polynomial.finsetSum_coeff] at eqn
  have rhs : (if h then (0 : Polynomial P) else Polynomial.C ((2 + X) ^ n)).coeff k = 0 := by
    cases h <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
      Polynomial.coeff_zero,
      Polynomial.coeff_C_of_ne_zero (Nat.ne_of_gt hk)]
  rw [rhs] at eqn
  calc
    (∑ p : Fin n → W, if highN p = k ∧ last (p i) = h then signedWeight p else 0) =
        ∑ p : Fin n → W, (if last (p i) = h then sbw p else 0).coeff k := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hh : last (p i) = h <;> by_cases hnk : highN p = k <;>
        simp only [hh, hnk, and_self, and_true, and_false, true_and, false_and,
          ↓reduceIte, sbw, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
          eq_comm] <;> split_ifs <;> simp_all
    _ = 0 := eqn
/-- The parity of the number of joint-endpoint windows. -/
def prefixCoin {n : ℕ} (p : Fin n → W) : Bool := decide (endsN p % 2 = 1)
private lemma signed_weight_coin {n : ℕ} (p : Fin n → W) :
    signedWeight p = if prefixCoin p then - X ^ rareN p else X ^ rareN p := by
  rw [signed_weight_formula, neg_one_pow_eq_pow_mod_two]
  have hmod : endsN p % 2 = 0 ∨ endsN p % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [prefixCoin, hmod]
/-- Positive high-endpoint fibers have equal weights at both coin values, even after fixing one
  bit. -/
lemma forced_coin_balance {n : ℕ} (i : Fin n) (h : Bool) (k : ℕ) (hk : 0 < k) :
    (∑ p : Fin n → W, if highN p = k ∧ last (p i) = h
      ∧ prefixCoin p = false then X ^ rareN p else 0) =
    (∑ p : Fin n → W, if highN p = k ∧ last (p i) = h
      ∧ prefixCoin p = true then X ^ rareN p else 0) := by
  have hs := forced_signed_slice_zero i h k hk
  have hp (p : Fin n → W) :
      (if highN p = k ∧ last (p i) = h then signedWeight p else 0) =
      (if highN p = k ∧ last (p i) = h ∧ prefixCoin p = false then X ^ rareN p else 0) -
      (if highN p = k ∧ last (p i) = h ∧ prefixCoin p = true then X ^ rareN p else 0) := by
    rw [signed_weight_coin]
    by_cases hnk : highN p = k <;> by_cases hh : last (p i) = h <;> cases hc : prefixCoin p <;>
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
private lemma positive_local : (∑ a : W, Polynomial.C (X ^ rb a) * Y ^ hb a) =
    Polynomial.C (2 + X) + Polynomial.C (2 * X) * Y := by
  simp [rb, hb, last, Finset.univ, Fintype.elems, map_add, map_mul, Polynomial.C_ofNat]
  ring
private lemma positive_local_low : (∑ a : W, if last a = false then Polynomial.C (X ^ rb a)
  * Y ^ hb a else 0) =
    Polynomial.C (2 + X) := by
  simp [rb, hb, last, Finset.univ, Fintype.elems, map_add, map_ofNat]
  ring
private def pfw {n : ℕ} (i j : Fin n) (a : W) : Polynomial P :=
  if j = i then if last a = false then Polynomial.C (X ^ rb a) * Y ^ hb a else 0
  else Polynomial.C (X ^ rb a) * Y ^ hb a
private lemma positive_forced_point {n : ℕ} (i : Fin n) (p : Fin n → W) :
    (if last (p i) = false then bw p else 0) = ∏ j, pfw i j (p j) := by
  classical
  by_cases hi : last (p i) = false
  · rw [if_pos hi, bw_product]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases he : j = i
    · subst j; simp [pfw, hi]
    · simp [pfw, he]
  · rw [if_neg hi]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [pfw, hi]
private lemma forced_positive_generating {n : ℕ} (i : Fin n) :
    (∑ p : Fin n → W, if last (p i) = false then bw p else 0) =
      Polynomial.C (2 + X) * (Polynomial.C (2 + X) + Polynomial.C (2 * X) * Y) ^ (n - 1) := by
  classical
  simp_rw [positive_forced_point]
  rw [← Fintype.prod_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hhead : (∑ a : W, pfw i i a) = Polynomial.C (2 + X) := by
    simpa [pfw] using positive_local_low
  rw [hhead]
  congr 1
  have hrest (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      (∑ a : W, pfw i j a) = Polynomial.C (2 + X) + Polynomial.C (2 * X) * Y := by
    simpa [pfw, (Finset.mem_erase.mp hj).1] using positive_local
  rw [Finset.prod_congr rfl hrest]
  simp
/-- A prefix fiber with a fixed low high-endpoint bit has an explicit generating polynomial. -/
lemma forced_positive_slice {n : ℕ} (i : Fin n) (k : ℕ) :
    (∑ p : Fin n → W, if highN p = k ∧ last (p i) = false then X ^ rareN p else 0) =
      (2 + X) * slice (n - 1) k := by
  have eqn := congrArg (fun p : Polynomial P => p.coeff k) (forced_positive_generating i)
  rw [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, ← slice_as_coefficient] at eqn
  rw [← eqn]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hh : last (p i) = false <;> by_cases hnk : highN p = k <;>
    simp only [hh, hnk, and_self, and_true, and_false, true_and, false_and,
      ↓reduceIte, bw, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
      eq_comm] <;> split_ifs <;> simp_all
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
lemma high_n_zero_last {n : ℕ} (p : Fin n → W) (i : Fin n) (h : highN p = 0) :
    last (p i) = false := by
  have hi := Finset.single_le_sum (s := Finset.univ) (f := fun j => hb (p j))
    (fun j _ => Nat.zero_le (hb (p j))) (Finset.mem_univ i)
  change hb (p i) ≤ highN p at hi
  rw [h] at hi
  cases hl : last (p i) <;> simp_all [hb]
/-- One false high bit excludes the all-high prefix class. -/
lemma high_n_last_false {n : ℕ} (p : Fin n → W) (i : Fin n) (h : last (p i) = false) :
    highN p < n := by
  classical
  have he : highN p = ∑ j ∈ Finset.univ.erase i, hb (p j) := by
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
lemma prefix_generating (m : ℕ) :
    (∑ x : Fin m → W, X ^ WordCounts.rareN x) = (2 + 3 * X) ^ m := by
  classical
  have hp := Fintype.prod_sum (fun (_ : Fin m) (a : W) => X ^ WordCounts.rb a)
  have hpoint (p : Fin m → W) : X ^ WordCounts.rareN p = ∏ i, X ^ WordCounts.rb (p i) := by
    simp [WordCounts.rareN, Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_congr rfl (fun p _ => hpoint p), ← hp]
  have hw : (∑ a : W, X ^ WordCounts.rb a) = 2 + 3 * X := by
    simp [WordCounts.rb,Finset.univ,Fintype.elems]; ring
  rw [hw]
  simp [Finset.prod_const, Fintype.card_fin]
/-- The three allowed first-anchor windows of the fixed-label reservoir. -/
def qok (a : W) : Prop := a ∈ ({.zero,.middle,.high} : Finset W)
/-- The two allowed last-anchor windows of the fixed-label reservoir. -/
def vok (a : W) : Prop := a ∈ ({.low,.ends} : Finset W)
private noncomputable def aw (q r v : W) : Polynomial ℕ := by
  classical exact if qok q ∧ r = .high ∧ vok v then X ^ (WordCounts.rb q + WordCounts.rb r
    + WordCounts.rb v) else 0
private lemma anchor_generating :
    (∑ q : W, ∑ r : W, ∑ v : W, aw q r v) = 2 * X ^ 2 * (2 + X) := by
  classical
  simp [aw,qok,vok,WordCounts.rb,Finset.univ,Fintype.elems]
  ring
/-- Reduced words on which all left teachers are zero and all right teachers are two. -/
def isReservoir {m : ℕ} (x : LegalPriorityTeacher.Input (m + 3)) : Prop :=
  qok (x ⟨m, by omega⟩) ∧ x ⟨m + 1, by omega⟩ = .high ∧ vok (x ⟨m + 2, by omega⟩)
private def fullWeight {m : ℕ} (x : LegalPriorityTeacher.Input (m + 3)) : Polynomial ℕ := by
  classical exact if isReservoir x then X ^ WordCounts.rareN x else 0
/-- The reservoir predicate depends only on the three appended anchors. -/
lemma append_res (m : ℕ) (p : Fin m → W) (a : Fin 3 → W) :
    isReservoir (Fin.append p a) ↔ qok (a 0) ∧ a 1 = .high ∧ vok (a 2) := by
  change qok (Fin.append p a (Fin.natAdd m 0)) ∧
    Fin.append p a (Fin.natAdd m 1) = .high ∧
    vok (Fin.append p a (Fin.natAdd m 2)) ↔ _
  simp
/-- Rare count splits between the prefix and its three anchors. -/
lemma append_rare (m : ℕ) (p : Fin m → W) (a : Fin 3 → W) :
    WordCounts.rareN (Fin.append p a) = WordCounts.rareN p +
      (WordCounts.rb (a 0) + WordCounts.rb (a 1) + WordCounts.rb (a 2)) := by
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
    (∑ a : Fin 3 → W, aw (a 0) (a 1) (a 2)) = 2 * X ^ 2 * (2 + X) := by
  have hs := Equiv.sum_comp anchorEquiv (fun t : W × W × W => aw t.1 t.2.1 t.2.2)
  change (∑ a : Fin 3 → W, aw (anchorEquiv a).1 (anchorEquiv a).2.1
    (anchorEquiv a).2.2) = _
  rw [hs, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  exact anchor_generating
private lemma actual_reservoir_generating (m : ℕ) :
    (∑ x : LegalPriorityTeacher.Input (m + 3), fullWeight x) = 2 * X ^ 2 * (2 + X) * (2 + 3
      * X) ^ m := by
  classical
  rw [← Equiv.sum_comp (Fin.appendEquiv m 3)]
  change (∑ pa : (Fin m → W) × (Fin 3 → W), fullWeight (Fin.append pa.1 pa.2)) = _
  simp_rw [full_append]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, anchor_function_sum]
  rw [← Finset.sum_mul, prefix_generating]
  ring
local notation "Reservoir" m => ({x : LegalPriorityTeacher.Input (m+3) // isReservoir x})
private lemma reservoir_subtype_generating (m : ℕ) :
    (∑ x : Reservoir m, X ^ WordCounts.rareN x.val) = 2 * X ^ 2 * (2 + X) * (2 + 3 * X) ^ m := by
  classical
  have hs := Finset.sum_subtype (p := @isReservoir m) (F
    := inferInstance) (Finset.univ.filter (@isReservoir m))
    (by simp) (fun x : LegalPriorityTeacher.Input (m + 3) => X ^ WordCounts.rareN x)
  rw [← hs]
  simpa only [Finset.sum_filter, fullWeight] using actual_reservoir_generating m
/-- Cardinality of the actual reservoir class at rare count z. -/
def Nz (m z : ℕ) : ℕ := Fintype.card {x : Reservoir m // WordCounts.rareN x.val = z}
/-- Exact cardinalities of all reservoir mass classes, for every prefix length. -/
lemma actual_nz_identity (m z : ℕ) :
    Nz m z = (2 * X ^ 2 * (2 + X) * (2 + 3 * X) ^ m).coeff z := by
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
def leftRoles {m : ℕ} (i : Fin m) : Roles (m + 3) where
  p := i.castAdd 3
  q := ⟨m, by omega⟩
  r := ⟨m + 1, by omega⟩
  pq := by change i.val < m; exact i.isLt
  qr := by change m < m + 1; omega
/-- The teacher at prefix position i and the last two anchors. -/
def rightRoles {m : ℕ} (i : Fin m) : Roles (m + 3) where
  p := i.castAdd 3
  q := ⟨m + 1, by omega⟩
  r := ⟨m + 2, by omega⟩
  pq := by change i.val < m + 1; omega
  qr := by change m + 1 < m + 2; omega
/-- Actual left-teacher label after separating prefix and anchor coordinates. -/
lemma actual_left_label {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) (i : Fin m) :
    teacher (leftRoles i) (Fin.append p a) =
      if last (p i) && first (a 0) then 1 else if last (a 0) && first (a 1) then 2 else 0 := by
  change (if last (Fin.append p a (i.castAdd 3)) && first (Fin.append p a (Fin.natAdd m 0)) then 1
    else if last (Fin.append p a (Fin.natAdd m 0)) &&
      first (Fin.append p a (Fin.natAdd m 1)) then 2 else 0) = _
  simp
/-- Actual right-teacher label after separating prefix and anchor coordinates. -/
lemma actual_right_label {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) (i : Fin m) :
    teacher (rightRoles i) (Fin.append p a) =
      if last (p i) && first (a 1) then 1 else if last (a 1) && first (a 2) then 2 else 0 := by
  change (if last (Fin.append p a (i.castAdd 3)) && first (Fin.append p a (Fin.natAdd m 1)) then 1
    else if last (Fin.append p a (Fin.natAdd m 1)) &&
      first (Fin.append p a (Fin.natAdd m 2)) then 2 else 0) = _
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
end
open scoped BigOperators Polynomial
namespace Capacity
/-- Binomial weight choose(j,k) times two to the k. -/
def weight (j k : ℕ) : ℕ := j.choose k * 2 ^ k
private def tail (j K : ℕ) : ℕ := ∑ k ∈ Finset.range (j + 1), if K < k then weight j k else 0
/-- Total positive binomial weight at indices at most K. -/
def low (j K : ℕ) : ℕ := ∑ k ∈ Finset.range (j + 1), if 0 < k ∧ k ≤ K then weight j k else 0
/-- Prefix coordinates or binomial prefix factor, according to the enclosing namespace. -/
def pref (n j : ℕ) : ℕ := n.choose j * 2 ^ (n - j)
private lemma total (j : ℕ) : (∑ k ∈ Finset.range (j + 1), weight j k) = 3 ^ j := by
  simpa [weight, mul_comm] using (add_pow (2 : ℕ) 1 j).symm
private lemma moment (j : ℕ) : (∑ k ∈ Finset.range (j + 1), k * weight j k) = 2 * j * 3 ^ (j - 1)
  := by
  cases j with
  | zero => simp [weight]
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [zero_mul, add_zero]
    have hterm (k : ℕ) : (k + 1) * weight (n + 1) (k + 1) = 2 * (n + 1) * weight n k := by
      dsimp [weight]
      rw [pow_succ]
      have h := Nat.add_one_mul_choose_eq n k
      calc
        _ = 2 * ((n + 1).choose (k + 1) * (k + 1)) * 2 ^ k := by ring
        _ = _ := by rw [← h]; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, total]
    simp
private lemma partition (j K : ℕ) : 1 + low j K + tail j K = 3 ^ j := by
  rw [← total]
  have h (k : ℕ) : (if k = 0 then 1 else 0) +
      (if 0 < k ∧ k ≤ K then weight j k else 0) +
      (if K < k then weight j k else 0) = weight j k := by
    by_cases hk : k = 0
    · simp [hk, weight]
    · by_cases hK : K < k <;> simp [hk, hK, show 0 < k by omega, show (k ≤ K) ↔ ¬K < k by omega]
  have := Finset.sum_congr (s₁ := Finset.range (j + 1)) rfl (fun k _ => h k)
  simpa [Finset.sum_add_distrib, low, tail] using this
private lemma tail_markov (m j : ℕ) (hm : 3 ≤ m) (hj : 0 < j) :
    m * tail j (m / 3) + 6 * j ≤ 2 * j * 3 ^ j := by
  have hpoint (k : ℕ) : m * (if m / 3 < k then weight j k else 0) +
      (if k = 1 then 6 * j else 0) ≤ 3 * (k * weight j k) := by
    by_cases hk1 : k = 1
    · subst k
      have hK : ¬ m / 3 < 1 := by omega
      simp [hK, weight]
      omega
    · by_cases hK : m / 3 < k
      · have hmk : m ≤ 3 * k := by omega
        have hh := Nat.mul_le_mul_right (weight j k) hmk
        simpa [hK, hk1, mul_assoc] using hh
      · simp [hK, hk1]
  have hs := Finset.sum_le_sum (s := Finset.range (j + 1)) (fun k _ => hpoint k)
  have hone : (∑ k ∈ Finset.range (j + 1), if k = 1 then 6 * j else 0) = 6 * j := by
    simp [show 1 < j + 1 by omega]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hone, moment] at hs
  dsimp [tail]
  have hp : 3 ^ j = 3 ^ (j - 1) * 3 := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega]
    rw [pow_succ]
  nlinarith
private lemma tail_growth (j K : ℕ) : 3 * tail j K ≤ tail (j + 1) K := by
  have hs := Finset.sum_choose_succ_mul
    (R := ℕ) (fun k _ => if K < k then 2 ^ k else 0) j
  have hf (n : ℕ) (k : ℕ) :
      n.choose k * (if K < k then 2 ^ k else 0) =
        if K < k then weight n k else 0 := by
    split_ifs <;> simp [weight]
  simp only [Nat.cast_id, hf] at hs
  have hb (k : ℕ) : 2 * (if K < k then weight j k else 0) ≤ j.choose k * (if K < k
    + 1 then 2 ^ (k + 1) else 0) := by
    by_cases hk : K < k
    · simp [hk, show K < k + 1 by omega, weight, pow_succ,
        mul_assoc, mul_comm, mul_left_comm]
    · simp [hk]
  have hb := Finset.sum_le_sum (s := Finset.range (j + 1)) (fun k _ => hb k)
  rw [← Finset.mul_sum] at hb
  change tail (j + 1) K = tail j K + _ at hs
  change 2 * tail j K ≤ _ at hb
  omega
private lemma scalar_capacity (m j : ℕ) (hm : 3 ≤ m) (hj : 0 < j) (hjm : j < m) :
    2 * (m - j) * tail j (m / 3) + 2 * m + 4 * j ≤ 6 * j * (3 ^ (j - 1) + low (j - 1) (m / 3)) + 2
      * (m - j) := by
  have htail := tail_markov m j hm hj
  have hprev := tail_growth (j - 1) (m / 3)
  rw [show j - 1 + 1 = j by omega] at hprev
  have hpart := partition (j - 1) (m / 3)
  have hp : 3 ^ j = 3 ^ (j - 1) * 3 := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega]
    rw [pow_succ]
  have hprevscaled := Nat.mul_le_mul_left (2 * j) hprev
  have hmj : m - j + j = m := by omega
  nlinarith
private lemma pref_relation (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjm : j < m) :
    (m - j) * pref (m - 1) (j - 1) = 2 * j * pref (m - 1) j := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hexp : m - 1 - s = (m - 1 - (s + 1)) + 1 := by omega
  have hh := Nat.choose_succ_right_eq (m - 1) s
  have hms : m - (s + 1) = m - 1 - s := by omega
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pref, hms]
  calc
    _ = ((m - 1).choose s * (m - 1 - s)) * (2 ^ (m - 1 - (s + 1)) * 2) := by
      rw [hexp, pow_succ]
      ring
    _ = ((m - 1).choose (s + 1) * (s + 1)) * (2 ^ (m - 1 - (s + 1)) * 2) := by rw [← hh]
    _ = _ := by ring
/-- The nonnegative Q coefficient inequality, for every m> = 3 and every degree j. -/
private theorem coefficient_capacity (m j : ℕ) (hm : 3 ≤ m) :
    2 * pref (m - 1) j * tail j (m / 3) ≤ 3 * pref (m - 1) (j - 1) * (3 ^ (j - 1) + low (j - 1) (m / 3)) + 2
      * pref (m - 1) j := by
  by_cases hj : j = 0
  · simp [hj, tail, weight]
  by_cases hjm : j < m
  · have rel := pref_relation m j (by omega) (by omega) hjm
    have hs := scalar_capacity m j hm (by omega) hjm
    have hsm := Nat.mul_le_mul_left (pref (m - 1) j) hs
    have heq : pref (m - 1) j *
        (6 * j * (3 ^ (j - 1) + low (j - 1) (m / 3)) + 2 * (m - j)) =
        (m - j) * (3 * pref (m - 1) (j - 1) * (3 ^ (j - 1) + low (j - 1) (m / 3)) +
          2 * pref (m - 1) j) := by
      nlinarith [congrArg (fun a => a * (3 * (3 ^ (j - 1) + low (j - 1) (m / 3)))) rel]
    rw [heq] at hsm
    have hl : (m - j) * (2 * pref (m - 1) j * tail j (m / 3)) ≤
        (m - j) * (3 * pref (m - 1) (j - 1) * (3 ^ (j - 1) + low (j - 1) (m / 3)) +
          2 * pref (m - 1) j) := by
      nlinarith
    exact Nat.le_of_mul_le_mul_left hl (by omega)
  · have hc : (m - 1).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [pref, hc]
end Capacity
namespace Capacity
private def pc (m j : ℕ) : ℤ := (pref (m - 1) j : ℤ) * 3 ^ j
private def ac (m j : ℕ) : ℤ := pref (m - 1) j
/-- Coefficient contribution of the low positive prefix-count slices. -/
def lc (m j : ℕ) : ℤ := (pref (m - 1) j : ℤ) * low j (m / 3)
/-- Coefficient transform for multiplication by two plus three X. -/
def mulB (f : ℕ → ℤ) (j : ℕ) : ℤ := 2 * f j + if j = 0 then 0 else 3 * f (j - 1)
/-- Coefficient transform for multiplication by two plus X. -/
def mulV (f : ℕ → ℤ) (j : ℕ) : ℤ := 2 * f j + if j = 0 then 0 else f (j - 1)
/-- Half of the interior exterior-discrepancy coefficient. -/
def dc (m j : ℕ) : ℤ := mulB (lc m) j - 4 * (pc m j - ac m j)
/-- Half of the interior reservoir coefficient. -/
def nc (m j : ℕ) : ℤ := mulB (pc m) j
private lemma pc_nonneg (m j : ℕ) : 0 ≤ pc m j := by unfold pc; positivity
private lemma lc_le_pc (m j : ℕ) : lc m j ≤ pc m j := by
  have hh := partition j (m / 3)
  have hl : low j (m / 3) ≤ 3 ^ j := by omega
  unfold lc pc
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl) (by positivity)
private lemma ac_le_pc (m j : ℕ) : ac m j ≤ pc m j := by
  have h : 1 ≤ (3 : ℕ) ^ j := Nat.one_le_pow j 3 (by decide)
  unfold ac pc
  nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ 3 ^ j by exact_mod_cast h)
    (show (0:ℤ) ≤ pref (m - 1) j by positivity)]
private lemma dc_upper (m j : ℕ) : dc m j ≤ nc m j := by
  have h := lc_le_pc m j
  have hprev := lc_le_pc m (j - 1)
  have hA := ac_le_pc m j
  unfold dc nc mulB
  split_ifs <;> omega
private lemma dc_lower (m j : ℕ) (hm : 3 ≤ m) : -nc m j ≤ dc m j := by
  have ht := partition j (m / 3)
  have hi : 1 + (low j (m / 3):ℤ) + tail j (m / 3) = 3 ^ j := by exact_mod_cast ht
  have hs := coefficient_capacity m j hm
  have hsZ : 2 * (pref (m - 1) j:ℤ) * tail j (m / 3) ≤
      3 * (pref (m - 1) (j - 1):ℤ) * (3 ^ (j - 1) + low (j - 1) (m / 3)) + 2 * pref (m - 1) j := by
    exact_mod_cast hs
  unfold nc dc mulB pc ac lc
  by_cases hj : j = 0
  · simp [hj, low]
  · simp only [if_neg hj]
    nlinarith [congrArg (fun a => (pref (m - 1) j:ℤ) * a) hi]
/-- Coefficientwise capacity of the fixed-label A0/B2 reservoir. -/
private lemma mul_v_preserves (f g : ℕ → ℤ) (h : ∀ j, -f j ≤ g j ∧ g j ≤ f j) (j : ℕ) :
    -mulV f j ≤ mulV g j ∧ mulV g j ≤ mulV f j := by
  have hj := h j
  have hp := h (j - 1)
  unfold mulV
  split_ifs <;> omega
/-- Half of the actual reservoir generating coefficient after the anchor shift. -/
def reservoir_half (m z : ℕ) : ℤ := if 2 ≤ z then mulV (nc m) (z - 2) else 0
/-- Half of the exterior discrepancy coefficient after the anchor shift. -/
def discrepancy_half (m z : ℕ) : ℤ := if 2 ≤ z then mulV (dc m) (z - 2) else 0
end Capacity
namespace Capacity
private lemma low_zero (j : ℕ) : low j 0 = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have h : ¬ (0 < k ∧ k ≤ 0) := by omega
  exact if_neg h
private lemma nc_nonneg (m j : ℕ) : 0 ≤ nc m j := by
  have h := pc_nonneg m j
  have hp := pc_nonneg m (j - 1)
  unfold nc mulB
  split_ifs <;> omega
private lemma core_lower_small (m j : ℕ) (hm : m = 1 ∨ m = 2) : -nc m j ≤ dc m j := by
  have hl (a b : ℕ) (hm : b < 3) : lc b a = 0 := by
    unfold lc
    rw [show b / 3 = 0 by omega, low_zero]
    simp
  rcases hm with rfl | rfl
  · have hd : dc 1 j = 0 := by
      unfold dc mulB
      rw [hl j 1 (by decide), hl (j - 1) 1 (by decide)]
      by_cases hj : j = 0
      · simp [hj, pc, ac, pref]
      · have hchoose : (0:ℕ).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [pc, ac, pref, hchoose]
    rw [hd]
    have := nc_nonneg 1 j
    omega
  · by_cases hj0 : j = 0
    · subst j
      norm_num [dc, nc, mulB, hl, pc, ac, pref]
    by_cases hj1 : j = 1
    · subst j
      norm_num [dc, nc, mulB, hl, pc, ac, pref]
    have hchoose : (1:ℕ).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hd : dc 2 j = 0 := by
      unfold dc mulB
      rw [hl j 2 (by decide), hl (j - 1) 2 (by decide)]
      simp [pc, ac, pref, hchoose]
    rw [hd]
    have := nc_nonneg 2 j
    omega
private theorem core_two_sided_positive (m j : ℕ) (hm : 0 < m) :
    -nc m j ≤ dc m j ∧ dc m j ≤ nc m j := by
  refine ⟨?_, dc_upper m j⟩
  by_cases h3 : 3 ≤ m
  · exact dc_lower m j h3
  · exact core_lower_small m j (by omega)
/-- Every positive prefix length and mass class have a legal integer reservoir split. -/
theorem integer_split_positive (m z : ℕ) (hm : 0 < m) :
    ∃ t : ℕ, (t:ℤ) ≤ 2 * reservoir_half m z ∧
      2 * discrepancy_half m z - 2 * reservoir_half m z + 2 * (t:ℤ) = 0 := by
  have hc : -reservoir_half m z ≤ discrepancy_half m z ∧
      discrepancy_half m z ≤ reservoir_half m z := by
    unfold reservoir_half discrepancy_half
    split_ifs
    · exact mul_v_preserves (nc m) (dc m) (fun j => core_two_sided_positive m j hm) (z - 2)
    · omega
  have hn : 0 ≤ reservoir_half m z - discrepancy_half m z := by omega
  refine ⟨(reservoir_half m z - discrepancy_half m z).toNat, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hn]
    omega
  · rw [Int.toNat_of_nonneg hn]
    ring
end Capacity
end D5.S3.Arith.FibonacciAtomic.CommonPrediction
