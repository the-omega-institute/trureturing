/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exterior discrepancy and a common majority classifier balanced in every rare-count class. -/
import D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts
import D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
/-!
The common two-layer priority-teacher problem on independent complete windows.
All prefix lengths and all rare-count classes are included.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Arith.FibonacciAtomic.CommonPrediction
attribute [local instance] Classical.propDecidable
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open scoped BigOperators Polynomial
namespace MajorityGeometry
noncomputable section
/-- Reservoir condition on an ordered anchor triple. -/
private def isRes (q r v : W) : Prop := q∈({.zero,.middle,.high}:Finset W) ∧ r = .high
  ∧ v∈({.low,.ends}:Finset W)
/-- Polynomial discrepancy of the two coin choices over all non-reservoir anchors. -/
private def pairAnchor (m k : ℕ) (h : Bool) : Polynomial ℤ := by
  classical exact ∑ q : W, ∑ r : W, ∑ v : W,
    if isRes q r v then 0 else
      Polynomial.C (ld h q r v (selector m k q r v false) + ld h q r v (selector m k q r v true)) *
        Polynomial.X ^ (WordCounts.rb q + WordCounts.rb r + WordCounts.rb v)
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the one selector representative. -/
private lemma pair_anchor_one (h : Bool) :
    pairAnchor 4 1 h = if h then 0 else - 8 * Polynomial.X ^ 2 + 12 * Polynomial.X ^ 3 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel,
      bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the two selector representative. -/
private lemma pair_anchor_two (h : Bool) :
    pairAnchor 5 2 h = if h then 0 else - 16 * Polynomial.X ^ 2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel,
      bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the three selector representative. -/
private lemma pair_anchor_three (h : Bool) :
    pairAnchor 4 2 h = if h then 0 else - 16 * Polynomial.X ^ 2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel,
      bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the four selector representative. -/
private lemma pair_anchor_four (h : Bool) :
    pairAnchor 5 3 h = if h then 0 else - 16 * Polynomial.X ^ 2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel,
      bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the five selector representative. -/
private lemma pair_anchor_five (h : Bool) :
    pairAnchor 3 2 h = if h then 0 else - 16 * Polynomial.X ^ 2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel,
      bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the six selector representative. -/
private lemma pair_anchor_six (h : Bool) :
    pairAnchor 10 9 h = if h then 0 else - 16 * Polynomial.X ^ 2 := by
  cases h <;>
    simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel,
      bLabel,
      ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Exact paired-anchor polynomial at the seven selector representative. -/
private lemma pair_anchor_seven : pairAnchor 1 1 true = 0 := by
  simp [pairAnchor, isRes, selector, firstTop, lastTop, top0, top1, top2, vt, delta, aLabel, bLabel,
    ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring
/-- Tie coin obtained from the joint endpoints of the three anchors. -/
def anchorCoin (q r v : W) : Bool :=
  if first v then decide (v = .ends) else if last q then decide (q = .ends) else decide (r = .ends)
/-- Discrepancy polynomial of the zero-high prefix class. -/
private def zeroAnchor : Polynomial ℤ := by
  classical exact ∑ q : W, ∑ r : W, ∑ v : W,
    if isRes q r v then 0 else
      Polynomial.C (ld false q r v (selector 1 0 q r v (anchorCoin q r v))) *
        Polynomial.X ^ (WordCounts.rb q + WordCounts.rb r + WordCounts.rb v)
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- The zero-high prefix discrepancy cancels exactly. -/
private lemma zero_anchor_eq_zero : zeroAnchor = 0 := by
  simp [zeroAnchor, isRes, anchorCoin, selector, firstTop, lastTop, top0, top1, top2, vt, delta,
    aLabel, bLabel,
    ld, err, first, last, WordCounts.rb, Finset.univ, Fintype.elems] <;> ring
end
end MajorityGeometry
end
section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
namespace MajorityGeometry
noncomputable section
private lemma pair_anchor_stable (m k : ℕ) (hm : 0 < m) (hkm : k ≤ m) (h : Bool) :
    pairAnchor m k h =
      pairAnchor (representative (region m k)).1 (representative (region m k)).2 h := by
  unfold pairAnchor
  simp_rw [selector_stable m k hm hkm]
private lemma pair_anchor_general (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hkm : k < m) (h : Bool) :
    pairAnchor m k h = if h then 0 else
      if 3 * k ≤ m then - 8 * Polynomial.X ^ 2 + 12 * Polynomial.X ^ 3 else - 16
        * Polynomial.X ^ 2 := by
  rw [pair_anchor_stable m k hm (by omega)]
  have h0 : k ≠ 0 := by omega
  have he : k ≠ m := by omega
  by_cases h3 : 3 * k ≤ m
  · simpa [region, representative, h0, he, h3] using pair_anchor_one h
  · have hr : region m k = 2 ∨ region m k = 3 ∨ region m k = 4 ∨
        region m k = 5 ∨ region m k = 6 := by
      unfold region
      split_ifs <;> omega
    rcases hr with hr | hr | hr | hr | hr
    · simpa [hr, representative, h3] using pair_anchor_two h
    · simpa [hr, representative, h3] using pair_anchor_three h
    · simpa [hr, representative, h3] using pair_anchor_four h
    · simpa [hr, representative, h3] using pair_anchor_five h
    · simpa [hr, representative, h3] using pair_anchor_six h
private lemma pair_anchor_all_high (m : ℕ) (hm : 0 < m) : pairAnchor m m true = 0 := by
  rw [pair_anchor_stable m m hm (by omega)]
  simpa [region, representative, show m ≠ 0 by omega] using pair_anchor_seven
end
end MajorityGeometry
namespace MajorityGeometry
noncomputable section
private def singleAnchor (m k : ℕ) (h coin : Bool) : Polynomial ℤ := by
  classical exact ∑ q : W, ∑ r : W, ∑ v : W,
    if isRes q r v then 0 else Polynomial.C (ld h q r v (selector m k q r v coin)) *
      Polynomial.X ^ (WordCounts.rb q + WordCounts.rb r + WordCounts.rb v)
private lemma pair_anchor_single (m k : ℕ) (h : Bool) :
    pairAnchor m k h = singleAnchor m k h false + singleAnchor m k h true := by
  classical
  unfold pairAnchor singleAnchor
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases he : isRes q r v <;> simp [he, map_add, add_mul]
private def fwgt {m : ℕ} (i : Fin m) (k : ℕ) (h b : Bool) : Polynomial ℤ :=
  ∑ p : Fin m → W, if WordCounts.highN p = k ∧ last (p i) = h ∧ WordCounts.prefixCoin p = b
    then (Polynomial.X : Polynomial ℤ) ^ WordCounts.rareN p else 0
private def fplain {m : ℕ} (i : Fin m) (k : ℕ) (h : Bool) : Polynomial ℤ :=
  ∑ p : Fin m → W, if WordCounts.highN p = k ∧ last (p i) = h
    then (Polynomial.X : Polynomial ℤ) ^ WordCounts.rareN p else 0
private def fdelta {m : ℕ} (i : Fin m) (k : ℕ) (h : Bool) : Polynomial ℤ :=
  ∑ p : Fin m → W, if WordCounts.highN p = k ∧ last (p i) = h
    then (Polynomial.X : Polynomial ℤ) ^ WordCounts.rareN p
      * singleAnchor m k h (WordCounts.prefixCoin p) else 0
private lemma fplain_split {m : ℕ} (i : Fin m) (k : ℕ) (h : Bool) :
    fplain i k h = fwgt i k h false + fwgt i k h true := by
  rw [fplain, fwgt, fwgt, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk : WordCounts.highN p = k <;> by_cases hh : last (p i) = h <;>
    cases hc : WordCounts.prefixCoin p <;> simp [hk, hh, hc]
private lemma fdelta_split {m : ℕ} (i : Fin m) (k : ℕ) (h : Bool) :
    fdelta i k h = fwgt i k h false * singleAnchor m k h false +
      fwgt i k h true * singleAnchor m k h true := by
  rw [fdelta, fwgt, fwgt, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk : WordCounts.highN p = k <;> by_cases hh : last (p i) = h <;>
    cases hc : WordCounts.prefixCoin p <;> simp [hk, hh, hc]
private lemma exact_fiber_averaging {m : ℕ} (i : Fin m) (k : ℕ) (hk : 0 < k) (h : Bool) :
    2 * fdelta i k h = fplain i k h * pairAnchor m k h := by
  have fair : fwgt i k h false = fwgt i k h true := WordCounts.forced_coin_balance i h k hk
  rw [fdelta_split, fplain_split, pair_anchor_single, fair]
  ring
end
end MajorityGeometry
end
section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
namespace ExteriorCounts
noncomputable section
/-- Prefix coordinates or binomial prefix factor, according to the enclosing namespace. -/
def pref {m : ℕ} (x : Input (m + 3)) : Fin m → W := fun i => x (i.castAdd 3)
/-- The first anchor of a reduced word. -/
def q {m : ℕ} (x : Input (m + 3)) : W := x ⟨m, by omega⟩
/-- The middle anchor of a reduced word. -/
def r {m : ℕ} (x : Input (m + 3)) : W := x ⟨m + 1, by omega⟩
/-- The last anchor of a reduced word. -/
def v {m : ℕ} (x : Input (m + 3)) : W := x ⟨m + 2, by omega⟩
private def wordCoin {m : ℕ} (x : Input (m + 3)) : Bool :=
  if WordCounts.highN (pref x) = 0 then MajorityGeometry.anchorCoin (q x) (r x) (v x)
  else WordCounts.prefixCoin (pref x)
/-- The majority selector on actual reduced words. -/
def exteriorSelector {m : ℕ} (x : Input (m + 3)) : Fin 3 :=
  MajorityGeometry.selector m (WordCounts.highN (pref x)) (q x) (r x) (v x) (wordCoin x)
private def Epoly (m : ℕ) (i : Fin m) : P := by
  classical exact ∑ x : Input (m + 3), if ReservoirWords.isReservoir x then 0 else
    Polynomial.C (MajorityGeometry.err (teacher (TeacherLabels.leftRoles i) x)
      (exteriorSelector x) -
      MajorityGeometry.err (teacher (TeacherLabels.rightRoles i) x) (exteriorSelector x)) *
      X ^ WordCounts.rareN x
/-- Sum of the low positive high-endpoint slices of the shortened prefix. -/
def L (m : ℕ) : P := ∑ k ∈ Finset.Icc 1 (m / 3),
  ((m - 1).choose k : P) * (2 * X) ^ k * (2 + X) ^ (m - 1 - k)
/-- Exact generating polynomial of the exterior left-right error discrepancy. -/
def Eformula (m : ℕ) : P := 2 * X ^ 2 * (2 + X) *
  ((2 + 3 * X) * L m - 4 * ((2 + 3 * X) ^ (m - 1) - (2 + X) ^ (m - 1)))
end
end ExteriorCounts
namespace ExteriorCounts
noncomputable section
private lemma pref_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) : pref (Fin.append p a) = p := by
  funext i
  exact Fin.append_left p a i
private lemma q_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) : q (Fin.append p a) = a 0 := by
  exact Fin.append_right p a 0
private lemma r_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) : r (Fin.append p a) = a 1 := by
  exact Fin.append_right p a 1
private lemma v_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) : v (Fin.append p a) = a 2 := by
  exact Fin.append_right p a 2
private lemma rare_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) :
    WordCounts.rareN (Fin.append p a) = WordCounts.rareN p +
      (WordCounts.rb (a 0) + WordCounts.rb (a 1) + WordCounts.rb (a 2)) := by
  exact ReservoirWords.append_rare m p a
/-- Actual exterior labels expressed in prefix count and three anchor windows. -/
lemma exterior_append {m : ℕ} (p : Fin m → W) (q r v : W) :
    exteriorSelector (Fin.append p ![q,r,v]) =
      MajorityGeometry.selector m (WordCounts.highN p) q r v
        (if WordCounts.highN p = 0 then MajorityGeometry.anchorCoin q r v
          else WordCounts.prefixCoin p) := by
  simp [exteriorSelector, wordCoin, pref_append, q_append, r_append, v_append]
/-- Separate a reduced input into its prefix and ordered anchor triple. -/
def wordEquiv (m : ℕ) : Input (m + 3) ≃ (Fin m → W) × W × W × W :=
  (Fin.appendEquiv m 3).symm.trans (Equiv.prodCongrRight fun _ => ReservoirWords.anchorEquiv)
private lemma word_sum (m : ℕ) (F : Input (m + 3) → P) :
    (∑ x, F x) = ∑ p : Fin m → W, ∑ q : W, ∑ r : W, ∑ v : W, F (Fin.append p ![q,r,v]) := by
  have h := Equiv.sum_comp (wordEquiv m).symm F
  change (∑ t : (Fin m → W) × W × W × W, F (Fin.append t.1 ![t.2.1,t.2.2.1,t.2.2.2])) = ∑ x,
    F x at h
  simpa only [Fintype.sum_prod_type] using h.symm
private lemma epoly_nested (m : ℕ) (i : Fin m) :
    Epoly m i = ∑ p : Fin m → W, ∑ q : W, ∑ r : W, ∑ v : W,
      if MajorityGeometry.isRes q r v then 0 else
        Polynomial.C (MajorityGeometry.ld (LiteralWindowEnd.last (p i)) q r v
          (MajorityGeometry.selector m (WordCounts.highN p) q r v
            (if WordCounts.highN p = 0 then MajorityGeometry.anchorCoin q r v
              else WordCounts.prefixCoin p))) *
        X ^ (WordCounts.rareN p + WordCounts.rb q + WordCounts.rb r + WordCounts.rb v) := by
  classical
  rw [Epoly, word_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro v hv
  simp only [ReservoirWords.append_res]
  simp [ReservoirWords.qok, ReservoirWords.vok, MajorityGeometry.isRes,
    exterior_append, TeacherLabels.actual_left_label, TeacherLabels.actual_right_label,
    MajorityGeometry.ld, MajorityGeometry.aLabel, MajorityGeometry.bLabel, rare_append, add_assoc]
end
end ExteriorCounts
namespace ExteriorCounts
noncomputable section
private lemma sum_bool {m : ℕ} (p : Fin m → W) (A B : ℕ) :
    (∑ i, if LiteralWindowEnd.last (p i) then A else B) =
      (m - WordCounts.highN p) * B + WordCounts.highN p * A := by
  classical
  have hpos : (Finset.univ.filter (fun i => LiteralWindowEnd.last (p i) = true)).card =
      WordCounts.highN p := by
    simp only [WordCounts.highN, WordCounts.hb, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i => LiteralWindowEnd.last (p i) = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hneg : (Finset.univ.filter (fun i => ¬LiteralWindowEnd.last (p i) = true)).card =
      m - WordCounts.highN p := by omega
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, hpos, hneg, add_comm, Nat.cast_id]
/-- Total votes of both actual teacher layers on a reduced input. -/
def actualVotes {m : ℕ} (x : Input (m + 3)) (c : Fin 3) : ℕ :=
  ∑ i : Fin m, ((if teacher (TeacherLabels.leftRoles i) x = c then 1 else 0) +
    (if teacher (TeacherLabels.rightRoles i) x = c then 1 else 0))
/-- Actual teacher votes depend on the prefix endpoint count and anchors. -/
lemma actual_votes_append {m : ℕ} (p : Fin m → W) (q r v : W) (c : Fin 3) :
    actualVotes (Fin.append p ![q,r,v]) c = MajorityGeometry.vt m (WordCounts.highN p) q r v c := by
  unfold actualVotes
  have hp (i : Fin m) :
      ((if teacher (TeacherLabels.leftRoles i) (Fin.append p ![q,r,v]) = c then 1 else 0) +
      (if teacher (TeacherLabels.rightRoles i) (Fin.append p ![q,r,v]) = c then 1 else 0)) =
      if LiteralWindowEnd.last (p i) then
        ((if MajorityGeometry.aLabel true q r = c then 1 else 0)
          + (if MajorityGeometry.bLabel true r v = c then 1 else 0))
      else ((if MajorityGeometry.aLabel false q r = c then 1 else 0) +
        (if MajorityGeometry.bLabel false r v = c then 1 else 0)) := by
    rw [TeacherLabels.actual_left_label, TeacherLabels.actual_right_label]
    cases hl : LiteralWindowEnd.last (p i) <;>
      simp [MajorityGeometry.aLabel, MajorityGeometry.bLabel, hl]
  rw [Finset.sum_congr rfl (fun i _ => hp i), sum_bool]
  rfl
/-- Prefix and anchor views reconstruct the same reduced word. -/
private lemma append_views {m : ℕ} (x : Input (m + 3)) : Fin.append (pref x) ![q x,r x,v x] = x := by
  have ha : (![q x,r x,v x] : Fin 3 → W) = fun j => x (Fin.natAdd m j) := by
    funext j
    fin_cases j <;> rfl
  rw [ha]
  exact Fin.append_castAdd_natAdd (f := x)
private lemma actual_votes_views {m : ℕ} (x : Input (m + 3)) (c : Fin 3) :
    actualVotes x c = MajorityGeometry.vt m (WordCounts.highN (pref x)) (q x) (r x) (v x) c := by
  simpa only [append_views] using actual_votes_append (pref x) (q x) (r x) (v x) c
/-- The exterior selector maximizes the votes of all actual teachers. -/
lemma exterior_majority {m : ℕ} (x : Input (m + 3)) (c : Fin 3) :
    actualVotes x c ≤ actualVotes x (exteriorSelector x) := by
  rw [actual_votes_views, actual_votes_views]
  exact MajorityGeometry.selector_majority _ _ _ _ _ _ _
end
end ExteriorCounts
namespace WordCounts
noncomputable section
private lemma high_n_permutation {m : ℕ} (p : Fin m → W) (σ : Equiv.Perm (Fin m)) :
    highN (p ∘ σ) = highN p := Equiv.sum_comp σ (fun i => hb (p i))
private lemma ends_n_permutation {m : ℕ} (p : Fin m → W) (σ : Equiv.Perm (Fin m)) :
    endsN (p ∘ σ) = endsN p := Equiv.sum_comp σ (fun i => eb (p i))
private lemma prefix_coin_permutation {m : ℕ} (p : Fin m → W) (σ : Equiv.Perm (Fin m)) :
    prefixCoin (p ∘ σ) = prefixCoin p := by rw [prefixCoin, prefixCoin, ends_n_permutation]
end
end WordCounts
namespace ExteriorCounts
noncomputable section
/-- Prefix relabeling leaves the exterior majority choice unchanged. -/
private lemma exterior_prefix_permutation {m : ℕ} (p : Fin m → W) (q r v : W) (σ : Equiv.Perm (Fin m)) :
    exteriorSelector (Fin.append (p ∘ σ) ![q,r,v]) = exteriorSelector (Fin.append p ![q,r,v]) := by
  rw [exterior_append, exterior_append, WordCounts.high_n_permutation,
    WordCounts.prefix_coin_permutation]
open WordCounts (highN rareN prefixCoin)
open MajorityGeometry (singleAnchor fplain fdelta pairAnchor)
private lemma anchor_factor (j : ℕ) (h : Bool) (s : W → W → W → Fin 3) :
    (∑ q : W, ∑ r : W, ∑ v : W, if MajorityGeometry.isRes q r v then 0 else
      Polynomial.C (MajorityGeometry.ld h q r v (s q r v)) *
      X ^ (j + WordCounts.rb q + WordCounts.rb r + WordCounts.rb v)) =
    X ^ j * (∑ q : W, ∑ r : W, ∑ v : W, if MajorityGeometry.isRes q r v then 0 else
      Polynomial.C (MajorityGeometry.ld h q r v (s q r v)) *
      X ^ (WordCounts.rb q + WordCounts.rb r + WordCounts.rb v)) := by
  classical
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro v hv
  by_cases he : MajorityGeometry.isRes q r v
  · simp [he]
  · have hb (w : W) : WordCounts.rb w = WordCounts.rb w := by cases w <;> rfl
    simp only [he, ↓reduceIte, pow_add, hb]
    ring
open WordCounts (highN rareN prefixCoin)
open MajorityGeometry (singleAnchor fplain fdelta pairAnchor)
set_option maxHeartbeats 4000000 in
private lemma epoly_positive (m : ℕ) (hm : 0 < m) (i : Fin m) :
    Epoly m i = ∑ p : Fin m → W, if highN p = 0 then 0 else
      X ^ rareN p * singleAnchor m (highN p) (last (p i)) (prefixCoin p) := by
  classical
  rw [epoly_nested]
  apply Finset.sum_congr rfl
  intro p hp
  rw [anchor_factor]
  by_cases h0 : highN p = 0
  · rw [if_pos h0]
    have hl := WordCounts.high_n_zero_last p i h0
    simp only [h0, hl, ↓reduceIte]
    simp_rw [MajorityGeometry.selector_region_zero m hm]
    change X ^ rareN p * MajorityGeometry.zeroAnchor = 0
    rw [MajorityGeometry.zero_anchor_eq_zero, mul_zero]
  · simp only [h0, ↓reduceIte]
    rfl
open WordCounts (highN rareN prefixCoin)
open MajorityGeometry (singleAnchor fplain fdelta pairAnchor)
private lemma epoly_fibers (m : ℕ) (hm : 0 < m) (i : Fin m) :
    Epoly m i = ∑ k ∈ Finset.Icc 1 m, (fdelta i k false + fdelta i k true) := by
  classical
  rw [epoly_positive m hm]
  simp only [fdelta, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h0 : highN p = 0
  · rw [if_pos h0]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hn : (0:ℕ) ≠ k := by have := (Finset.mem_Icc.mp hk).1; omega
    simp only [h0, hn, false_and, ↓reduceIte, zero_add]
  · have hk : highN p ∈ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]
      exact ⟨by omega, WordCounts.high_n_le p⟩
    rw [if_neg h0]
    rw [Finset.sum_eq_single (highN p)]
    · cases hl : last (p i) <;> simp [hl]
    · intro k hk hne
      simp [Ne.symm hne]
    · exact fun h => (h hk).elim
open WordCounts (highN rareN prefixCoin)
open MajorityGeometry (singleAnchor fplain fdelta pairAnchor)
private lemma fplain_false (m k : ℕ) (i : Fin m) :
    fplain i k false = (2 + X) * WordCounts.slice (m - 1) k :=
  WordCounts.forced_positive_slice i k
private lemma fplain_false_all (m : ℕ) (i : Fin m) : fplain i m false = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  by_cases h : highN p = m ∧ last (p i) = false
  · have := WordCounts.high_n_last_false p i h.2
    omega
  · exact if_neg h
private lemma doubled_fiber (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hkm : k ≤ m) (i : Fin m) :
    2 * (fdelta i k false + fdelta i k true) =
      (2 + X) * WordCounts.slice (m - 1) k *
        (if 3 * k ≤ m then - 8 * X ^ 2 + 12 * X ^ 3 else - 16 * X ^ 2) := by
  rw [mul_add, MajorityGeometry.exact_fiber_averaging i k hk false,
    MajorityGeometry.exact_fiber_averaging i k hk true]
  by_cases he : k = m
  · subst k
    rw [MajorityGeometry.pair_anchor_all_high m hm, fplain_false_all]
    have hz := fplain_false m m i
    rw [fplain_false_all] at hz
    rw [← hz]
    simp
  · have hlt : k < m := by omega
    rw [MajorityGeometry.pair_anchor_general m k hm hk hlt false,
      MajorityGeometry.pair_anchor_general m k hm hk hlt true, fplain_false]
    simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero] <;> rfl
end
end ExteriorCounts
end
section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
namespace WordCounts
noncomputable section
private lemma slices_sum (n m : ℕ) (hnm : n ≤ m) :
    (∑ k ∈ Finset.Icc 0 m, slice n k) = (2 + 3 * X) ^ n := by
  classical
  have huniv : (∑ p : Fin n → W, X ^ rareN p) = (2 + 3 * X) ^ n := by
    have hp := congrArg (Polynomial.map (Nat.castRingHom ℤ))
      (ReservoirWords.prefix_generating n)
    simpa only [Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_natCast, Polynomial.map_ofNat, Polynomial.map_X,
      Nat.coe_castRingHom] using hp
  unfold slice
  rw [Finset.sum_comm, ← huniv]
  apply Finset.sum_congr rfl
  intro p hp
  have hk : highN p ∈ Finset.Icc 0 m := by
    simp only [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, (high_n_le p).trans hnm⟩
  rw [Finset.sum_eq_single (highN p)]
  · simp
  · intro k hk hne
    simp [Ne.symm hne]
  · exact fun h => (h hk).elim
private lemma positive_slices_sum (m : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.Icc 1 m, slice (m - 1) k) = (2 + 3 * X) ^ (m - 1) - (2 + X) ^ (m - 1) := by
  classical
  have hs := slices_sum (m - 1) m (by omega)
  have hi : Finset.Icc 0 m = insert 0 (Finset.Icc 1 m) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hi, Finset.sum_insert (by simp), slice_formula] at hs
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul, Nat.sub_zero] at hs
  exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hs)
end
end WordCounts
end
section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
namespace ExteriorCounts
noncomputable section
open WordCounts (slice)
open MajorityGeometry (fdelta)
private lemma low_slices (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, if 3 * k ≤ m then slice (m - 1) k else 0) = L m := by
  classical
  rw [← Finset.sum_filter]
  have hi : (Finset.Icc 1 m).filter (fun k => 3 * k ≤ m) = Finset.Icc 1 (m / 3) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hi]
  simp_rw [WordCounts.slice_formula]
  rfl
private lemma actual_exterior_identity (m : ℕ) (hm : 0 < m) (i : Fin m) :
    Epoly m i = Eformula m := by
  classical
  have hp : 2 * Epoly m i = 2 * Eformula m := by
    rw [epoly_fibers m hm, Finset.mul_sum]
    have hterm (k : ℕ) (hk : k∈Finset.Icc 1 m) :=
      doubled_fiber m k hm (by have := (Finset.mem_Icc.mp hk).1; omega)
        (Finset.mem_Icc.mp hk).2 i
    rw [Finset.sum_congr rfl hterm]
    have hpoint (k : ℕ) :
        (2 + X) * slice (m - 1) k * (if 3 * k ≤ m then - 8 * X ^ 2 + 12 * X ^ 3 else - 16 * X ^ 2) =
        (2 + X) * ((8 * X ^ 2 + 12 * X ^ 3) * (if 3 * k ≤ m then slice (m - 1) k else 0)
          -16 * X ^ 2 * slice (m - 1) k) := by
      split_ifs <;> ring
    simp_rw [hpoint]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      low_slices, WordCounts.positive_slices_sum m hm]
    unfold Eformula
    ring
  exact mul_left_cancel₀ (by norm_num : (2:P) ≠ 0) hp
/-- Actual exterior left-teacher errors minus right-teacher errors in a rare-count class. -/
def Ez (m z : ℕ) (i : Fin m) : ℤ := by
  classical
  exact ∑ x : Input (m + 3),
    if ¬ReservoirWords.isReservoir x ∧ WordCounts.rareN x = z then
      MajorityGeometry.err (teacher (TeacherLabels.leftRoles i) x) (exteriorSelector x) -
        MajorityGeometry.err (teacher (TeacherLabels.rightRoles i) x) (exteriorSelector x)
    else 0
/-- The actual exterior discrepancy is the z coefficient of the explicit exterior polynomial. -/
private lemma actual_ez_identity (m z : ℕ) (hm : 0 < m) (i : Fin m) :
    Ez m z i = (Eformula m).coeff z := by
  classical
  rw [← actual_exterior_identity m hm i, Epoly, Polynomial.finsetSum_coeff]
  unfold Ez
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hr : ReservoirWords.isReservoir x <;> by_cases hz : WordCounts.rareN x = z <;>
    simp only [hr, hz, not_true_eq_false, not_false_eq_true, and_self,
      and_true, and_false, true_and, false_and, ↓reduceIte,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] <;>
      split_ifs <;> simp_all
end
end ExteriorCounts
end
section
namespace CapacityCoefficients
noncomputable section
open scoped BigOperators Polynomial
private lemma affine_coeff (a b : ℤ) (n j : ℕ) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ n).coeff j =
      (n.choose j:ℤ) * a ^ (n - j) * b ^ j := by
  have he : (Polynomial.C a + Polynomial.C b * Polynomial.X) ^ n =
      ((Polynomial.X + Polynomial.C a) ^ n).comp (Polynomial.C b * Polynomial.X) := by
    simp only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [add_comm]
  rw [he, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_X_add_C_pow]
  ring
private lemma v_coeff (n j : ℕ) :
    ((2 + (Polynomial.X:P)) ^ n).coeff j = (n.choose j:ℤ) * 2 ^ (n - j) := by
  simpa using affine_coeff 2 1 n j
private lemma slice_coeff (n k j : ℕ) :
    (WordCounts.slice n k).coeff j =
      (Capacity.pref n j:ℤ) * (Capacity.weight j k:ℤ) := by
  have he : WordCounts.slice n k =
      Polynomial.C ((n.choose k:ℤ) * 2 ^ k) *
        (Polynomial.X ^ k * (2 + Polynomial.X) ^ (n - k)) := by
    rw [WordCounts.slice_formula]
    simp only [map_mul, map_pow, Polynomial.C_eq_natCast, Polynomial.C_ofNat, mul_pow]
    ring
  rw [he, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hkj : k ≤ j
  · rw [if_pos hkj, v_coeff]
    by_cases hjn : j ≤ n
    · have hexp : n - k - (j - k) = n - j := by omega
      have hch := congrArg (fun x : ℕ => (x:ℤ)) (Nat.choose_mul (n:=n) hkj)
      simp only [Nat.cast_mul] at hch
      rw [hexp]
      unfold Capacity.pref Capacity.weight
      push_cast
      calc
        _ = ((n.choose k:ℤ) * ((n - k).choose (j - k):ℤ)) * 2 ^ (n - j) * 2 ^ k := by ring
        _ = _ := by rw [← hch]; ring
    · have hn : n < j := by omega
      have hcj := Nat.choose_eq_zero_of_lt hn
      by_cases hkn : k ≤ n
      · have hck := Nat.choose_eq_zero_of_lt (show n - k < j - k by omega)
        simp [hck, hcj, Capacity.pref]
      · have hck := Nat.choose_eq_zero_of_lt (show n < k by omega)
        simp [hck, hcj, Capacity.pref]
  · have hck := Nat.choose_eq_zero_of_lt (show j < k by omega)
    simp [hkj, hck, Capacity.weight]
private lemma low_range (j K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, Capacity.weight j k) = Capacity.low j K := by
  classical
  have hzero (k : ℕ) (hk : k∈Finset.Icc 1 K) (hf : k∉(Finset.Icc 1 K).filter (fun k=>k ≤ j)) :
      Capacity.weight j k = 0 := by
    have hkj : j < k := by simpa [hk] using hf
    simp [Capacity.weight, Nat.choose_eq_zero_of_lt hkj]
  have hs := Finset.sum_subset (Finset.filter_subset (fun k=>k ≤ j) (Finset.Icc 1 K)) hzero
  have he : (Finset.Icc 1 K).filter (fun k=>k ≤ j) =
      (Finset.range (j + 1)).filter (fun k=>0 < k ∧ k ≤ K) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [← hs, he, Finset.sum_filter]
  rfl
private lemma l_coeff (m j : ℕ) : (ExteriorCounts.L m).coeff j = Capacity.lc m j := by
  have hL : ExteriorCounts.L m = ∑ k ∈ Finset.Icc 1 (m / 3), WordCounts.slice (m - 1) k := by
    unfold ExteriorCounts.L
    simp_rw [WordCounts.slice_formula]
  rw [hL, Polynomial.finsetSum_coeff]
  simp_rw [slice_coeff]
  rw [← Finset.mul_sum]
  unfold Capacity.lc
  congr 1
  rw [← Nat.cast_sum, low_range]
end
end CapacityCoefficients
namespace CapacityCoefficients
noncomputable section
open scoped BigOperators Polynomial
open Capacity
private lemma b_coeff (n j : ℕ) :
    ((2 + 3 * (Polynomial.X:P)) ^ n).coeff j = (pref n j:ℤ) * 3 ^ j := by
  simpa [pref, Nat.cast_mul, Nat.cast_pow] using affine_coeff 2 3 n j
private lemma mul_b_coeff (p : P) (j : ℕ) :
    ((2 + 3 * Polynomial.X) * p).coeff j = mulB (fun k => p.coeff k) j := by
  have he : (2 + 3 * Polynomial.X) * p = 2 * p + 3 * (Polynomial.X * p) := by ring
  rw [he, Polynomial.coeff_add]
  cases j with
  | zero => simp [mulB]
  | succ n => simp [mulB]
private lemma mul_v_coeff (p : P) (j : ℕ) :
    ((2 + Polynomial.X) * p).coeff j = mulV (fun k => p.coeff k) j := by
  have he : (2 + Polynomial.X) * p = 2 * p + Polynomial.X * p := by ring
  rw [he, Polynomial.coeff_add]
  cases j with
  | zero => simp [mulV]
  | succ n => simp [mulV]
private lemma shift_coeff (p : P) (z : ℕ) :
    (2 * Polynomial.X ^ 2 * p).coeff z = if 2 ≤ z then 2 * p.coeff (z - 2) else 0 := by
  have he : 2 * Polynomial.X ^ 2 * p = 2 * (Polynomial.X ^ 2 * p) := by ring
  rw [he, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow_mul']
  split_ifs <;> simp
private lemma e_coeff (m z : ℕ) :
    (ExteriorCounts.Eformula m).coeff z = 2 * discrepancy_half m z := by
  unfold ExteriorCounts.Eformula
  rw [mul_assoc (2 * Polynomial.X ^ 2) (2 + Polynomial.X), shift_coeff]
  unfold discrepancy_half
  split_ifs
  · rw [mul_v_coeff, mulV]
    have hD (j : ℕ) :
        (((2 + 3 * Polynomial.X) * ExteriorCounts.L m-
          4 * ((2 + 3 * Polynomial.X) ^ (m - 1) - (2 + Polynomial.X) ^ (m - 1))):P).coeff j =
          dc m j := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul, Polynomial.coeff_sub,
        mul_b_coeff]
      simp only [l_coeff, b_coeff, v_coeff]
      rfl
    simp_rw [hD]
    rfl
  · simp
private lemma n_coeff (m z : ℕ) (hmpos : 0 < m) :
    (ReservoirWords.Nz m z:ℤ) = 2 * reservoir_half m z := by
  have he : (ReservoirWords.Nz m z:ℤ) =
      (2 * Polynomial.X ^ 2 * (2 + Polynomial.X) * (2 + 3 * Polynomial.X) ^ m:P).coeff z := by
    rw [ReservoirWords.actual_nz_identity]
    have hm := Polynomial.coeff_map (f := Nat.castRingHom ℤ)
      (p := (2 * (Polynomial.X : Polynomial ℕ) ^ 2 * (2 + (Polynomial.X : Polynomial ℕ))
 * (2 + 3 * (Polynomial.X : Polynomial ℕ)) ^ m)) (n := z)
    simpa only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_natCast, Polynomial.map_ofNat, Polynomial.map_X,
      Nat.coe_castRingHom, Nat.cast_ofNat] using hm.symm
  rw [he]
  have hp : (2 * Polynomial.X ^ 2 * (2 + Polynomial.X) * (2 + 3 * Polynomial.X) ^ m:P) =
      2 * Polynomial.X ^ 2 * ((2 + Polynomial.X) * ((2 + 3 * Polynomial.X) * (2 + 3
        * Polynomial.X) ^ (m - 1))) := by
    have hpow : (2 + 3 * (Polynomial.X:P)) ^ m = (2 + 3 * Polynomial.X) * (2 + 3
      * Polynomial.X) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    ring
  rw [hp, shift_coeff]
  unfold reservoir_half
  split_ifs
  · rw [mul_v_coeff, mulV]
    have hN (j : ℕ) : (((2 + 3 * Polynomial.X) * (2 + 3
      * Polynomial.X) ^ (m - 1)):P).coeff j = nc m j := by
      rw [mul_b_coeff]
      simp_rw [b_coeff]
      rfl
    simp_rw [hN]
    rfl
  · simp
end
end CapacityCoefficients
end
section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
namespace CommonSelector
noncomputable section
open ExteriorCounts
open WordCounts (rareN)
/-- The actual teacher label indexed by layer and prefix position. -/
def label {m : ℕ} (side : Bool) (i : Fin m) (x : Input (m + 3)) : Fin 3 :=
  if side then teacher (TeacherLabels.rightRoles i) x else teacher (TeacherLabels.leftRoles i) x
private def outsideCount {m : ℕ} (z : ℕ) (side : Bool) (i : Fin m) : ℤ :=
  ∑ x : Input (m + 3), if ¬ReservoirWords.isReservoir x ∧ rareN x = z then
    MajorityGeometry.err (label side i x) (exteriorSelector x) else 0
private def wordPerm {m : ℕ} (σ : Equiv.Perm (Fin m)) : Input (m + 3) ≃ Input (m + 3) :=
  (Fin.appendEquiv m 3).symm.trans
    ((Equiv.prodCongr ((Equiv.arrowCongr σ.symm (Equiv.refl W))) (Equiv.refl (Fin 3 → W))).trans
      (Fin.appendEquiv m 3))
private lemma word_perm_append {m : ℕ} (σ : Equiv.Perm (Fin m)) (p : Fin m → W) (a : Fin 3 → W) :
    wordPerm σ (Fin.append p a) = Fin.append (p ∘ σ) a := by
  change (Fin.appendEquiv m 3)
    ((Equiv.prodCongr ((Equiv.arrowCongr σ.symm (Equiv.refl W))) (Equiv.refl _))
    ((Fin.appendEquiv m 3).symm ((Fin.appendEquiv m 3) (p,a)))) = _
  rw [Equiv.symm_apply_apply]
  rfl
private lemma word_perm_views {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Input (m + 3)) :
    wordPerm σ x = Fin.append ((pref x) ∘ σ) ![q x,r x,v x] := by
  conv_lhs => rw [←append_views x, word_perm_append]
private lemma rare_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Input (m + 3)) :
    rareN (wordPerm σ x) = rareN x := by
  rw [word_perm_views]
  exact (ReservoirWords.actual_prefix_perm (pref x) ![q x,r x,v x] σ).1.trans
    (congrArg rareN (append_views x))
private lemma res_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Input (m + 3)) :
    ReservoirWords.isReservoir (wordPerm σ x) ↔ ReservoirWords.isReservoir x := by
  rw [word_perm_views]
  simpa only [append_views] using (ReservoirWords.actual_prefix_perm (pref x) ![q x,r x,v x] σ).2
private lemma selector_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Input (m + 3)) :
    exteriorSelector (wordPerm σ x) = exteriorSelector x := by
  rw [word_perm_views]
  simpa only [append_views] using exterior_prefix_permutation (pref x) (q x) (r x) (v x) σ
private lemma label_swap {m : ℕ} (i j : Fin m) (side : Bool) (x : Input (m + 3)) :
    label side i (wordPerm (Equiv.swap i j) x) = label side j x := by
  have ha := TeacherLabels.actual_left_label (pref x) ![q x,r x,v x] j
  have hb := TeacherLabels.actual_right_label (pref x) ![q x,r x,v x] j
  rw [append_views] at ha hb
  rw [word_perm_views]
  cases side
  · simpa only [label, Bool.false_eq_true, ↓reduceIte, TeacherLabels.actual_left_label,
      Function.comp_apply, Equiv.swap_apply_left] using ha.symm
  · simpa only [label, Bool.true_eq, ↓reduceIte, TeacherLabels.actual_right_label,
      Function.comp_apply, Equiv.swap_apply_left] using hb.symm
private lemma outside_count_equal {m : ℕ} (z : ℕ) (side : Bool) (i j : Fin m) :
    outsideCount z side i = outsideCount z side j := by
  let F : Input (m + 3) → ℤ := fun x => if ¬ReservoirWords.isReservoir x ∧ rareN x = z then
    MajorityGeometry.err (label side i x) (exteriorSelector x) else 0
  calc
    outsideCount z side i = ∑ x, F (wordPerm (Equiv.swap i j) x) :=
      (Equiv.sum_comp (wordPerm (Equiv.swap i j)) F).symm
    _ = outsideCount z side j := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [F, rare_perm, res_perm, selector_perm, label_swap]
private lemma actual_flat {m : ℕ} (x : Input (m
  + 3)) (hx : ReservoirWords.isReservoir x) (i : Fin m) :
    teacher (TeacherLabels.leftRoles i) x = 0 ∧ teacher (TeacherLabels.rightRoles i) x = 2 := by
  have hres : ReservoirWords.qok (q x) ∧ r x = .high ∧ ReservoirWords.vok (v x) := hx
  have hq : q x = .zero ∨ q x = .middle ∨ q x = .high := by
    simpa [ReservoirWords.qok] using hres.1
  have hv : v x = .low ∨ v x = .ends := by simpa [ReservoirWords.vok] using hres.2.2
  have hword : Fin.append (pref x) ![q x,.high,v x] = x := by
    rw [←hres.2.1]
    exact append_views x
  rw [←hword]
  exact TeacherLabels.actual_reservoir_flat (pref x) (q x) (v x) hq hv i
private lemma reservoir_majority {m : ℕ} (x : Input (m + 3)) (hx : ReservoirWords.isReservoir x)
    (c d : Fin 3) (hd : d = 0 ∨ d = 2) : actualVotes x c ≤ actualVotes x d := by
  have hleft : ∀ i, teacher (TeacherLabels.leftRoles i) x = 0 := fun i => (actual_flat x hx i).1
  have hright : ∀ i, teacher (TeacherLabels.rightRoles i) x = 2 := fun i => (actual_flat x hx i).2
  simp only [actualVotes]
  simp_rw [hleft, hright]
  rcases hd with rfl | rfl <;> fin_cases c <;> simp
private def Rset (m z : ℕ) : Finset (Input (m + 3)) :=
  Finset.univ.filter (fun x => ReservoirWords.isReservoir x ∧ rareN x = z)
private lemma rset_card (m z : ℕ) : (Rset m z).card = ReservoirWords.Nz m z := by
  have hc := Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (@ReservoirWords.isReservoir m) (fun x : Input (m + 3) => rareN x = z))
  change ReservoirWords.Nz m z = _ at hc
  rw [Fintype.card_subtype] at hc
  exact hc.symm
private lemma exists_split (m z : ℕ) (hm : 0 < m) :
    ∃ S : Finset (Input (m + 3)), S ⊆ Rset m z ∧
      (Eformula m).coeff z + 2 * (S.card:ℤ) - (ReservoirWords.Nz m z:ℤ) = 0 := by
  obtain ⟨t,ht,hbal⟩ := Capacity.integer_split_positive m z hm
  have hN := CapacityCoefficients.n_coeff m z hm
  have hE := CapacityCoefficients.e_coeff m z
  have hc : t ≤ (Rset m z).card := by
    rw [rset_card]
    have hh : (t:ℤ) ≤ (ReservoirWords.Nz m z:ℤ) := by omega
    exact_mod_cast hh
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq hc
  refine ⟨S,hS,?_⟩
  rw [hcard]
  omega
private def classifier {m : ℕ} (S : ℕ → Finset (Input (m + 3))) (x : Input (m + 3)) : Fin 3 :=
  if ReservoirWords.isReservoir x then if x ∈ S (rareN x) then 2 else 0 else exteriorSelector x
private lemma classifier_majority {m : ℕ} (S : ℕ → Finset (Input (m + 3)))
    (x : Input (m + 3)) (c : Fin 3) : actualVotes x c ≤ actualVotes x (classifier S x) := by
  by_cases hr : ReservoirWords.isReservoir x
  · apply reservoir_majority x hr c
    by_cases hs : x ∈ S (rareN x) <;> simp [classifier, hr, hs]
  · simpa only [classifier, if_neg hr] using exterior_majority x c
/-- Integer error count of one classifier in a specified rare-symbol class. -/
def errorCount {m : ℕ} (z : ℕ) (side : Bool) (i : Fin m)
    (f : Input (m + 3) → Fin 3) : ℤ :=
  ∑ x : Input (m + 3), if rareN x = z then MajorityGeometry.err (label side i x) (f x) else 0
private lemma indicator_sum {m : ℕ} (S : Finset (Input (m + 3))) :
    (∑ x : Input (m + 3), if x∈S then (1:ℤ) else 0) = (S.card:ℤ) := by
  rw [←Finset.sum_filter]
  simp
private lemma left_count {m : ℕ} (S : ℕ → Finset (Input (m + 3)))
    (hS : ∀ z, S z ⊆ Rset m z) (z : ℕ) (i : Fin m) :
    errorCount z false i (classifier S) = outsideCount z false i + (S z).card := by
  have hpoint (x : Input (m + 3)) :
      (if rareN x = z then MajorityGeometry.err (label false i x) (classifier S x) else 0) =
      (if ¬ReservoirWords.isReservoir x ∧ rareN x = z then
        MajorityGeometry.err (label false i x) (exteriorSelector x) else 0) +
      (if x∈S z then (1:ℤ) else 0) := by
    have hin : x∈S z → ReservoirWords.isReservoir x ∧ rareN x = z := by
      intro hx
      exact (Finset.mem_filter.mp (hS z hx)).2
    by_cases hz : rareN x = z
    · by_cases hr : ReservoirWords.isReservoir x
      · have hf := (actual_flat x hr i).1
        by_cases hs : x∈S z <;> simp [label, classifier, hz, hr, hs, hf, MajorityGeometry.err]
      · have hs : x∉S z := fun hx => hr (hin hx).1
        simp [label, classifier, hz, hr, hs]
    · have hs : x∉S z := fun hx => hz (hin hx).2
      simp [hz, hs]
  unfold errorCount outsideCount
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_add_distrib, indicator_sum]
private lemma right_count {m : ℕ} (S : ℕ → Finset (Input (m + 3)))
    (hS : ∀ z, S z ⊆ Rset m z) (z : ℕ) (i : Fin m) :
    errorCount z true i (classifier S) = outsideCount z true i +
      (ReservoirWords.Nz m z:ℤ) - (S z).card := by
  have hpoint (x : Input (m + 3)) :
      (if rareN x = z then MajorityGeometry.err (label true i x) (classifier S x) else 0) =
      (if ¬ReservoirWords.isReservoir x ∧ rareN x = z then
        MajorityGeometry.err (label true i x) (exteriorSelector x) else 0) +
      (if x∈Rset m z then (1:ℤ) else 0) - (if x∈S z then (1:ℤ) else 0) := by
    have hin : x∈S z → ReservoirWords.isReservoir x ∧ rareN x = z := by
      intro hx
      exact (Finset.mem_filter.mp (hS z hx)).2
    by_cases hz : rareN x = z
    · by_cases hr : ReservoirWords.isReservoir x
      · have hf := (actual_flat x hr i).2
        by_cases hs : x∈S z <;> simp [label, classifier, hz, hr, hs, hf, Rset, MajorityGeometry.err]
      · have hs : x∉S z := fun hx => hr (hin hx).1
        simp [label, classifier, hz, hr, hs, Rset]
    · have hs : x∉S z := fun hx => hz (hin hx).2
      simp [hz, hs, Rset]
  unfold errorCount outsideCount
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, indicator_sum, indicator_sum, rset_card]
private lemma outside_difference {m : ℕ} (z : ℕ) (i : Fin m) :
    outsideCount z false i - outsideCount z true i = Ez m z i := by
  unfold outsideCount Ez
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : ¬ReservoirWords.isReservoir x ∧ rareN x = z <;> simp [h, label]
def UniformMassBalanced : Prop :=
  ∀ m : ℕ, 0 < m → ∃ f : Input (m + 3) → Fin 3,
    (∀ x c, actualVotes x c ≤ actualVotes x (f x)) ∧
    (∀ z, ∀ i j : Fin m,
      errorCount z false i f = errorCount z false j f ∧
      errorCount z false i f = errorCount z true j f)
/-- One deterministic pointwise majority classifier balances all teachers in every rare-count
  class. -/
theorem uniform_mass_balanced : UniformMassBalanced := by
  intro m hm
  choose S hS hbal using fun z => exists_split m z hm
  refine ⟨classifier S, classifier_majority S, ?_⟩
  have hcross (z : ℕ) (i : Fin m) :
      errorCount z false i (classifier S) = errorCount z true i (classifier S) := by
    rw [left_count S hS, right_count S hS]
    have he := actual_ez_identity m z hm i
    have hd := outside_difference z i
    have hb := hbal z
    omega
  intro z i j
  have hleft : errorCount z false i (classifier S) = errorCount z false j (classifier S) := by
    rw [left_count S hS, left_count S hS, outside_count_equal z false i j]
  exact ⟨hleft, hleft.trans (hcross z j)⟩
end
end CommonSelector
end
end D5.S3.Arith.FibonacciAtomic.CommonPrediction
