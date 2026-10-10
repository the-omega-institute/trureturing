/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exterior teacher discrepancy and the reservoir capacity inequalities. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts
import D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum


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
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
attribute [local instance] Classical.propDecidable
namespace MajorityGeometry
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
private lemma pair_anchor_stable (m k : ℕ) (hm : 0  <  m) (hkm : k  ≤  m) (h : Bool) :
    pairAnchor m k h = pairAnchor (representative (region m k)).1 (representative (region m k)).2 h := by
  unfold pairAnchor
  simp_rw [selector_stable m k hm hkm]
private lemma pair_anchor_general (m k : ℕ) (hm : 0  <  m) (hk : 0  <  k) (hkm : k  <  m) (h : Bool) :
    pairAnchor m k h = if h then 0 else
      if 3*k  ≤  m then -8*Polynomial.X^2+12*Polynomial.X^3 else -16*Polynomial.X^2 := by
  rw [pair_anchor_stable m k hm (by omega)]
  have h0 : k≠0 := by omega
  have he : k≠m := by omega
  by_cases h3 : 3*k  ≤  m
  · simpa [region, representative, h0, he, h3] using pair_anchor_one h
  · have hr : region m k=2 ∨ region m k=3 ∨ region m k=4 ∨ region m k=5 ∨ region m k=6 := by
      unfold region
      split_ifs <;> omega
    rcases hr with hr | hr | hr | hr | hr
    · simpa [hr, representative, h3] using pair_anchor_two h
    · simpa [hr, representative, h3] using pair_anchor_three h
    · simpa [hr, representative, h3] using pair_anchor_four h
    · simpa [hr, representative, h3] using pair_anchor_five h
    · simpa [hr, representative, h3] using pair_anchor_six h
private lemma pair_anchor_all_high (m : ℕ) (hm : 0  <  m) : pairAnchor m m true = 0 := by
  rw [pair_anchor_stable m m hm (by omega)]
  simpa [region, representative, show m≠0 by omega] using pair_anchor_seven

end
end MajorityGeometry

namespace MajorityGeometry
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
private def singleAnchor (m k : ℕ) (h coin : Bool) : Polynomial ℤ := by
  classical exact ∑ q : W, ∑ r : W, ∑ v : W,
    if isRes q r v then 0 else Polynomial.C (ld h q r v (selector m k q r v coin))*
      Polynomial.X^(rb q+rb r+rb v)
private lemma pair_anchor_single (m k : ℕ) (h : Bool) :
    pairAnchor m k h = singleAnchor m k h false+singleAnchor m k h true := by
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
  ∑ p : Fin m → W, if WordCounts.highN p=k ∧ last (p i)=h ∧ WordCounts.prefixCoin p=b
    then (Polynomial.X : Polynomial ℤ)^WordCounts.rareN p else 0
private def fplain {m : ℕ} (i : Fin m) (k : ℕ) (h : Bool) : Polynomial ℤ :=
  ∑ p : Fin m → W, if WordCounts.highN p=k ∧ last (p i)=h
    then (Polynomial.X : Polynomial ℤ)^WordCounts.rareN p else 0
private def fdelta {m : ℕ} (i : Fin m) (k : ℕ) (h : Bool) : Polynomial ℤ :=
  ∑ p : Fin m → W, if WordCounts.highN p=k ∧ last (p i)=h
    then (Polynomial.X : Polynomial ℤ)^WordCounts.rareN p * singleAnchor m k h (WordCounts.prefixCoin p) else 0
private lemma fplain_split {m : ℕ} (i : Fin m) (k : ℕ) (h : Bool) :
    fplain i k h=fwgt i k h false+fwgt i k h true := by
  rw [fplain, fwgt, fwgt, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk : WordCounts.highN p=k <;> by_cases hh : last (p i)=h <;>
    cases hc : WordCounts.prefixCoin p <;> simp [hk, hh, hc]
private lemma fdelta_split {m : ℕ} (i : Fin m) (k : ℕ) (h : Bool) :
    fdelta i k h=fwgt i k h false*singleAnchor m k h false+
      fwgt i k h true*singleAnchor m k h true := by
  rw [fdelta, fwgt, fwgt, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk : WordCounts.highN p=k <;> by_cases hh : last (p i)=h <;>
    cases hc : WordCounts.prefixCoin p <;> simp [hk, hh, hc]
private lemma exact_fiber_averaging {m : ℕ} (i : Fin m) (k : ℕ) (hk : 0  <  k) (h : Bool) :
    2*fdelta i k h=fplain i k h*pairAnchor m k h := by
  have fair : fwgt i k h false=fwgt i k h true := WordCounts.forced_coin_balance i h k hk
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
attribute [local instance] Classical.propDecidable
namespace ExteriorCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
/-- Prefix coordinates or binomial prefix factor, according to the enclosing namespace. -/
def pref {m : ℕ} (x : Input (m+3)) : Fin m → W := fun i => x (i.castAdd 3)
/-- The first anchor of a reduced word. -/
def q {m : ℕ} (x : Input (m+3)) : W := x ⟨m, by omega⟩
/-- The middle anchor of a reduced word. -/
def r {m : ℕ} (x : Input (m+3)) : W := x ⟨m+1, by omega⟩
/-- The last anchor of a reduced word. -/
def v {m : ℕ} (x : Input (m+3)) : W := x ⟨m+2, by omega⟩
private def wordCoin {m : ℕ} (x : Input (m+3)) : Bool :=
  if WordCounts.highN (pref x)=0 then MajorityGeometry.anchorCoin (q x) (r x) (v x)
  else WordCounts.prefixCoin (pref x)
/-- The majority selector on actual reduced words. -/
def exteriorSelector {m : ℕ} (x : Input (m+3)) : Fin 3 :=
  MajorityGeometry.selector m (WordCounts.highN (pref x)) (q x) (r x) (v x) (wordCoin x)
private def Epoly (m : ℕ) (i : Fin m) : P := by
  classical exact ∑ x : Input (m+3), if ReservoirWords.isReservoir x then 0 else
    Polynomial.C (MajorityGeometry.err (teacher (TeacherLabels.leftRoles i) x) (exteriorSelector x) -
      MajorityGeometry.err (teacher (TeacherLabels.rightRoles i) x) (exteriorSelector x))*
      X ^ WordCounts.rareN x

/-- Sum of the low positive high-endpoint slices of the shortened prefix. -/
def L (m : ℕ) : P := ∑ k ∈ Finset.Icc 1 (m/3),
  ((m-1).choose k : P)*(2*X)^k*(2+X)^(m-1-k)
/-- Exact generating polynomial of the exterior left-right error discrepancy. -/
def Eformula (m : ℕ) : P := 2*X^2*(2+X)*
  ((2+3*X)*L m-4*((2+3*X)^(m-1)-(2+X)^(m-1)))
end
end ExteriorCounts

namespace ExteriorCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
private lemma pref_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) : pref (Fin.append p a)=p := by
  funext i
  exact Fin.append_left p a i
private lemma q_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) : q (Fin.append p a)=a 0 := by
  exact Fin.append_right p a 0
private lemma r_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) : r (Fin.append p a)=a 1 := by
  exact Fin.append_right p a 1
private lemma v_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) : v (Fin.append p a)=a 2 := by
  exact Fin.append_right p a 2
private lemma rare_append {m : ℕ} (p : Fin m → W) (a : Fin 3 → W) :
    WordCounts.rareN (Fin.append p a)=WordCounts.rareN p+
      (WordCounts.rb (a 0)+WordCounts.rb (a 1)+WordCounts.rb (a 2)) := by
  exact ReservoirWords.append_rare m p a
/-- Actual exterior labels expressed in prefix count and three anchor windows. -/
lemma exterior_append {m : ℕ} (p : Fin m → W) (q r v : W) :
    exteriorSelector (Fin.append p ![q,r,v]) =
      MajorityGeometry.selector m (WordCounts.highN p) q r v
        (if WordCounts.highN p=0 then MajorityGeometry.anchorCoin q r v else WordCounts.prefixCoin p) := by
  simp [exteriorSelector, wordCoin, pref_append, q_append, r_append, v_append]

/-- Separate a reduced input into its prefix and ordered anchor triple. -/
def wordEquiv (m : ℕ) : Input (m+3) ≃ (Fin m → W) × W × W × W :=
  (Fin.appendEquiv m 3).symm.trans (Equiv.prodCongrRight fun _ => ReservoirWords.anchorEquiv)
private lemma word_sum (m : ℕ) (F : Input (m+3) → P) :
    (∑ x, F x)=∑ p : Fin m → W, ∑ q : W, ∑ r : W, ∑ v : W, F (Fin.append p ![q,r,v]) := by
  have h := Equiv.sum_comp (wordEquiv m).symm F
  change (∑ t : (Fin m → W) × W × W × W, F (Fin.append t.1 ![t.2.1,t.2.2.1,t.2.2.2])) = ∑ x, F x at h
  simpa only [Fintype.sum_prod_type] using h.symm

private lemma epoly_nested (m : ℕ) (i : Fin m) :
    Epoly m i = ∑ p : Fin m → W, ∑ q : W, ∑ r : W, ∑ v : W,
      if MajorityGeometry.isRes q r v then 0 else
        Polynomial.C (MajorityGeometry.ld (LiteralWindowEnd.last (p i)) q r v
          (MajorityGeometry.selector m (WordCounts.highN p) q r v
            (if WordCounts.highN p=0 then MajorityGeometry.anchorCoin q r v else WordCounts.prefixCoin p))) *
        X^(WordCounts.rareN p+WordCounts.rb q+WordCounts.rb r+WordCounts.rb v) := by
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
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
private lemma sum_bool {m : ℕ} (p : Fin m → W) (A B : ℕ) :
    (∑ i, if LiteralWindowEnd.last (p i) then A else B) =
      (m-WordCounts.highN p)*B+WordCounts.highN p*A := by
  classical
  have hpos : (Finset.univ.filter (fun i => LiteralWindowEnd.last (p i)=true)).card =
      WordCounts.highN p := by
    simp only [WordCounts.highN, WordCounts.hb, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i => LiteralWindowEnd.last (p i)=true)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hneg : (Finset.univ.filter (fun i => ¬LiteralWindowEnd.last (p i)=true)).card =
      m-WordCounts.highN p := by omega
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, hpos, hneg, add_comm, Nat.cast_id]

/-- Total votes of both actual teacher layers on a reduced input. -/
def actualVotes {m : ℕ} (x : Input (m+3)) (c : Fin 3) : ℕ :=
  ∑ i : Fin m, ((if teacher (TeacherLabels.leftRoles i) x=c then 1 else 0)+
    (if teacher (TeacherLabels.rightRoles i) x=c then 1 else 0))
/-- Actual teacher votes depend on the prefix endpoint count and anchors. -/
lemma actual_votes_append {m : ℕ} (p : Fin m → W) (q r v : W) (c : Fin 3) :
    actualVotes (Fin.append p ![q,r,v]) c = MajorityGeometry.vt m (WordCounts.highN p) q r v c := by
  unfold actualVotes
  have hp (i : Fin m) :
      ((if teacher (TeacherLabels.leftRoles i) (Fin.append p ![q,r,v])=c then 1 else 0)+
      (if teacher (TeacherLabels.rightRoles i) (Fin.append p ![q,r,v])=c then 1 else 0)) =
      if LiteralWindowEnd.last (p i) then
        ((if MajorityGeometry.aLabel true q r=c then 1 else 0)+(if MajorityGeometry.bLabel true r v=c then 1 else 0))
      else ((if MajorityGeometry.aLabel false q r=c then 1 else 0)+(if MajorityGeometry.bLabel false r v=c then 1 else 0)) := by
    rw [TeacherLabels.actual_left_label, TeacherLabels.actual_right_label]
    cases hl : LiteralWindowEnd.last (p i) <;>
      simp [MajorityGeometry.aLabel, MajorityGeometry.bLabel, hl]
  rw [Finset.sum_congr rfl (fun i _ => hp i), sum_bool]
  rfl
/-- Prefix and anchor views reconstruct the same reduced word. -/
lemma append_views {m : ℕ} (x : Input (m+3)) : Fin.append (pref x) ![q x,r x,v x]=x := by
  have ha : (![q x,r x,v x] : Fin 3 → W) = fun j => x (Fin.natAdd m j) := by
    funext j
    fin_cases j <;> rfl
  rw [ha]
  exact Fin.append_castAdd_natAdd (f := x)
private lemma actual_votes_views {m : ℕ} (x : Input (m+3)) (c : Fin 3) :
    actualVotes x c=MajorityGeometry.vt m (WordCounts.highN (pref x)) (q x) (r x) (v x) c := by
  simpa only [append_views] using actual_votes_append (pref x) (q x) (r x) (v x) c
/-- The exterior selector maximizes the votes of all actual teachers. -/
lemma exterior_majority {m : ℕ} (x : Input (m+3)) (c : Fin 3) :
    actualVotes x c  ≤  actualVotes x (exteriorSelector x) := by
  rw [actual_votes_views, actual_votes_views]
  exact MajorityGeometry.selector_majority _ _ _ _ _ _ _
end
end ExteriorCounts

namespace WordCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
private lemma high_n_permutation {m : ℕ} (p : Fin m → W) (σ : Equiv.Perm (Fin m)) :
    highN (p ∘ σ)=highN p := Equiv.sum_comp σ (fun i => hb (p i))
private lemma ends_n_permutation {m : ℕ} (p : Fin m → W) (σ : Equiv.Perm (Fin m)) :
    endsN (p ∘ σ)=endsN p := Equiv.sum_comp σ (fun i => eb (p i))
private lemma prefix_coin_permutation {m : ℕ} (p : Fin m → W) (σ : Equiv.Perm (Fin m)) :
    prefixCoin (p ∘ σ)=prefixCoin p := by rw [prefixCoin, prefixCoin, ends_n_permutation]
end
end WordCounts
namespace ExteriorCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
/-- Prefix relabeling leaves the exterior majority choice unchanged. -/
lemma exterior_prefix_permutation {m : ℕ} (p : Fin m → W) (q r v : W) (σ : Equiv.Perm (Fin m)) :
    exteriorSelector (Fin.append (p ∘ σ) ![q,r,v])=exteriorSelector (Fin.append p ![q,r,v]) := by
  rw [exterior_append, exterior_append, WordCounts.high_n_permutation,
    WordCounts.prefix_coin_permutation]
end
end ExteriorCounts

end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
attribute [local instance] Classical.propDecidable
namespace ExteriorCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open WordCounts (highN rareN prefixCoin)
open MajorityGeometry (singleAnchor fplain fdelta pairAnchor)
private lemma anchor_factor (j : ℕ) (h : Bool) (s : W → W → W → Fin 3) :
    (∑ q : W, ∑ r : W, ∑ v : W, if MajorityGeometry.isRes q r v then 0 else
      Polynomial.C (MajorityGeometry.ld h q r v (s q r v))*
      X^(j+WordCounts.rb q+WordCounts.rb r+WordCounts.rb v)) =
    X^j * (∑ q : W, ∑ r : W, ∑ v : W, if MajorityGeometry.isRes q r v then 0 else
      Polynomial.C (MajorityGeometry.ld h q r v (s q r v))*
      X^(WordCounts.rb q+WordCounts.rb r+WordCounts.rb v)) := by
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


end
end ExteriorCounts
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
attribute [local instance] Classical.propDecidable
namespace ExteriorCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open WordCounts (highN rareN prefixCoin)
open MajorityGeometry (singleAnchor fplain fdelta pairAnchor)
set_option maxHeartbeats 1000000 in
private lemma epoly_positive (m : ℕ) (hm : 0 < m) (i : Fin m) :
    Epoly m i = ∑ p : Fin m → W, if highN p=0 then 0 else
      X^rareN p * singleAnchor m (highN p) (last (p i)) (prefixCoin p) := by
  classical
  rw [epoly_nested]
  apply Finset.sum_congr rfl
  intro p hp
  rw [anchor_factor]
  by_cases h0 : highN p=0
  · rw [if_pos h0]
    have hl := WordCounts.high_n_zero_last p i h0
    simp only [h0, hl, ↓reduceIte]
    simp_rw [MajorityGeometry.selector_region_zero m hm]
    change X^rareN p * MajorityGeometry.zeroAnchor = 0
    rw [MajorityGeometry.zero_anchor_eq_zero, mul_zero]
  · simp only [h0, ↓reduceIte]
    rfl


end
end ExteriorCounts
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
attribute [local instance] Classical.propDecidable
namespace ExteriorCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open WordCounts (highN rareN prefixCoin)
open MajorityGeometry (singleAnchor fplain fdelta pairAnchor)
private lemma epoly_fibers (m : ℕ) (hm : 0 < m) (i : Fin m) :
    Epoly m i = ∑ k ∈ Finset.Icc 1 m, (fdelta i k false+fdelta i k true) := by
  classical
  rw [epoly_positive m hm]
  simp only [fdelta, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h0 : highN p=0
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


end
end ExteriorCounts
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
attribute [local instance] Classical.propDecidable
namespace ExteriorCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open WordCounts (highN rareN prefixCoin)
open MajorityGeometry (singleAnchor fplain fdelta pairAnchor)
private lemma fplain_false (m k : ℕ) (i : Fin m) :
    fplain i k false=(2+X)*WordCounts.slice (m-1) k :=
  WordCounts.forced_positive_slice i k
private lemma fplain_false_all (m : ℕ) (i : Fin m) : fplain i m false=0 := by
  apply Finset.sum_eq_zero
  intro p hp
  by_cases h : highN p=m ∧ last (p i)=false
  · have := WordCounts.high_n_last_false p i h.2
    omega
  · exact if_neg h

private lemma doubled_fiber (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hkm : k ≤ m) (i : Fin m) :
    2*(fdelta i k false+fdelta i k true) =
      (2+X)*WordCounts.slice (m-1) k *
        (if 3*k ≤ m then -8*X^2+12*X^3 else -16*X^2) := by
  rw [mul_add, MajorityGeometry.exact_fiber_averaging i k hk false,
    MajorityGeometry.exact_fiber_averaging i k hk true]
  by_cases he : k=m
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
attribute [local instance] Classical.propDecidable
namespace WordCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
private lemma univariate_generating (n : ℕ) : (∑ p : Fin n → W, X^rareN p)=(2+3*X)^n := by
  classical
  have hp (p : Fin n → W) : X^rareN p=∏ i, X^rb (p i) := by
    simp [rareN, Finset.prod_pow_eq_pow_sum]
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (a : W) => X^rb a)]
  have hw : (∑ a : W, X^rb a)=2+3*X := by
    simp [rb, Finset.univ, Fintype.elems]
    ring
  simp_rw [hw]
  simp
private lemma slices_sum (n m : ℕ) (hnm : n ≤ m) :
    (∑ k ∈ Finset.Icc 0 m, slice n k)=(2+3*X)^n := by
  classical
  unfold slice
  rw [Finset.sum_comm, ← univariate_generating]
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
    (∑ k ∈ Finset.Icc 1 m, slice (m-1) k)=(2+3*X)^(m-1)-(2+X)^(m-1) := by
  classical
  have hs := slices_sum (m-1) m (by omega)
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
attribute [local instance] Classical.propDecidable
namespace ExteriorCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
open WordCounts (slice)
open MajorityGeometry (fdelta)
private lemma low_slices (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, if 3*k ≤ m then slice (m-1) k else 0)=L m := by
  classical
  rw [← Finset.sum_filter]
  have hi : (Finset.Icc 1 m).filter (fun k => 3*k ≤ m)=Finset.Icc 1 (m/3) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hi]
  simp_rw [WordCounts.slice_formula]
  rfl
private lemma actual_exterior_identity (m : ℕ) (hm : 0 < m) (i : Fin m) : Epoly m i=Eformula m := by
  classical
  have hp : 2*Epoly m i=2*Eformula m := by
    rw [epoly_fibers m hm, Finset.mul_sum]
    have hterm (k : ℕ) (hk : k∈Finset.Icc 1 m) :=
      doubled_fiber m k hm (by have := (Finset.mem_Icc.mp hk).1; omega)
        (Finset.mem_Icc.mp hk).2 i
    rw [Finset.sum_congr rfl hterm]
    have hpoint (k : ℕ) :
        (2+X)*slice (m-1) k*(if 3*k ≤ m then -8*X^2+12*X^3 else -16*X^2) =
        (2+X)*((8*X^2+12*X^3)*(if 3*k ≤ m then slice (m-1) k else 0)
          -16*X^2*slice (m-1) k) := by
      split_ifs <;> ring
    simp_rw [hpoint]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      low_slices, WordCounts.positive_slices_sum m hm]
    unfold Eformula
    skip
    ring
  exact mul_left_cancel₀ (by norm_num : (2:P)≠0) hp
end
end ExteriorCounts
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (first last)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators Polynomial
attribute [local instance] Classical.propDecidable
namespace ExteriorCounts
noncomputable section
local notation "W" => _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
local notation "P" => Polynomial ℤ
local notation "X" => (Polynomial.X : Polynomial ℤ)
local notation "Y" => (Polynomial.X : Polynomial (Polynomial ℤ))
/-- Actual exterior left-teacher errors minus right-teacher errors in a rare-count class. -/
def Ez (m z : ℕ) (i : Fin m) : ℤ := by
  classical exact ∑ x : Input (m+3), if ¬ReservoirWords.isReservoir x ∧ WordCounts.rareN x=z then
    MajorityGeometry.err (teacher (TeacherLabels.leftRoles i) x) (exteriorSelector x) -
      MajorityGeometry.err (teacher (TeacherLabels.rightRoles i) x) (exteriorSelector x) else 0
/-- The actual exterior discrepancy is the z coefficient of the explicit exterior polynomial. -/
lemma actual_ez_identity (m z : ℕ) (hm : 0 < m) (i : Fin m) :
    Ez m z i=(Eformula m).coeff z := by
  classical
  rw [← actual_exterior_identity m hm i, Epoly, Polynomial.finsetSum_coeff]
  unfold Ez
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hr : ReservoirWords.isReservoir x <;> by_cases hz : WordCounts.rareN x=z <;>
    simp only [hr, hz, not_true_eq_false, not_false_eq_true, and_self, and_true, and_false, true_and, false_and, ↓reduceIte, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] <;> split_ifs <;> simp_all
end
end ExteriorCounts
end

section
open scoped BigOperators
namespace Capacity

/-- Binomial weight choose(j,k) times two to the k. -/
def weight (j k : ℕ) : ℕ := j.choose k * 2 ^ k

private def tail (j K : ℕ) : ℕ := ∑ k ∈ Finset.range (j + 1), if K < k then weight j k else 0

/-- Total positive binomial weight at indices at most K. -/
def low (j K : ℕ) : ℕ := ∑ k ∈ Finset.range (j + 1), if 0 < k ∧ k ≤ K then weight j k else 0

/-- Prefix coordinates or binomial prefix factor, according to the enclosing namespace. -/
def pref (n j : ℕ) : ℕ := n.choose j * 2 ^ (n - j)

private lemma total (j : ℕ) : (∑ k ∈ Finset.range (j+1), weight j k) = 3^j := by
  simpa [weight, mul_comm] using (add_pow (2 : ℕ) 1 j).symm

private lemma moment (j : ℕ) : (∑ k ∈ Finset.range (j+1), k * weight j k) = 2*j*3^(j-1) := by
  cases j with
  | zero => simp [weight]
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [zero_mul, add_zero]
    have hterm (k : ℕ) : (k+1)*weight (n+1) (k+1) = 2*(n+1)*weight n k := by
      dsimp [weight]
      rw [pow_succ]
      have h := Nat.add_one_mul_choose_eq n k
      calc
        _ = 2 * ((n+1).choose (k+1) * (k+1)) * 2^k := by ring
        _ = _ := by rw [← h]; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, total]
    simp

private lemma partition (j K : ℕ) : 1 + low j K + tail j K = 3^j := by
  rw [← total]
  have h (k : ℕ) : (if k = 0 then 1 else 0) +
      (if 0 < k ∧ k ≤ K then weight j k else 0) +
      (if K < k then weight j k else 0) = weight j k := by
    by_cases hk : k = 0
    · simp [hk, weight]
    · by_cases hK : K < k <;> simp [hk, hK, show 0 < k by omega, show (k ≤ K) ↔ ¬K < k by omega]
  have := Finset.sum_congr (s₁ := Finset.range (j+1)) rfl (fun k _ => h k)
  simpa [Finset.sum_add_distrib, low, tail] using this

private lemma tail_markov (m j : ℕ) (hm : 3 ≤ m) (hj : 0 < j) :
    m*tail j (m/3) + 6*j ≤ 2*j*3^j := by
  have hpoint (k : ℕ) : m*(if m/3 < k then weight j k else 0) +
      (if k = 1 then 6*j else 0) ≤ 3*(k*weight j k) := by
    by_cases hk1 : k = 1
    · subst k
      have hK : ¬ m/3 < 1 := by omega
      simp [hK, weight]
      omega
    · by_cases hK : m/3 < k
      · have hmk : m ≤ 3*k := by omega
        have hh := Nat.mul_le_mul_right (weight j k) hmk
        simpa [hK, hk1, mul_assoc] using hh
      · simp [hK, hk1]
  have hs := Finset.sum_le_sum (s := Finset.range (j+1)) (fun k _ => hpoint k)
  have hone : (∑ k ∈ Finset.range (j+1), if k = 1 then 6*j else 0) = 6*j := by
    simp [show 1 < j+1 by omega]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hone, moment] at hs
  dsimp [tail]
  have hp : 3^j = 3^(j-1)*3 := by
    conv_lhs => rw [show j = (j-1)+1 by omega]
    rw [pow_succ]
  nlinarith

private lemma tail_growth (j K : ℕ) : 3*tail j K ≤ tail (j+1) K := by
  have hs := Finset.sum_choose_succ_mul
    (R := ℕ) (fun k _ => if K < k then 2^k else 0) j
  have hf (n : ℕ) (k : ℕ) : n.choose k * (if K < k then 2^k else 0) = if K < k then weight n k else 0 := by split_ifs <;> simp [weight]
  simp only [Nat.cast_id, hf] at hs
  have hb (k : ℕ) : 2*(if K < k then weight j k else 0) ≤ j.choose k * (if K < k+1 then 2^(k+1) else 0) := by
    by_cases hk : K < k
    · simp [hk, show K < k+1 by omega, weight, pow_succ,
        mul_assoc, mul_comm, mul_left_comm]
    · simp [hk]
  have hb := Finset.sum_le_sum (s := Finset.range (j+1)) (fun k _ => hb k)
  rw [← Finset.mul_sum] at hb
  change tail (j+1) K = tail j K + _ at hs
  change 2*tail j K ≤ _ at hb
  omega

private lemma scalar_capacity (m j : ℕ) (hm : 3 ≤ m) (hj : 0 < j) (hjm : j < m) :
    2*(m-j)*tail j (m/3) + 2*m+4*j ≤ 6*j*(3^(j-1)+low (j-1) (m/3)) + 2*(m-j) := by
  have htail := tail_markov m j hm hj
  have hprev := tail_growth (j-1) (m/3)
  rw [show j-1+1 = j by omega] at hprev
  have hpart := partition (j-1) (m/3)
  have hp : 3^j = 3^(j-1)*3 := by
    conv_lhs => rw [show j = (j-1)+1 by omega]
    rw [pow_succ]
  have hprevscaled := Nat.mul_le_mul_left (2*j) hprev
  have hmj : m-j+j = m := by omega
  nlinarith

private lemma pref_relation (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjm : j < m) :
    (m-j)*pref (m-1) (j-1) = 2*j*pref (m-1) j := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hexp : m-1-s = (m-1-(s+1))+1 := by omega
  have hh := Nat.choose_succ_right_eq (m-1) s
  have hms : m-(s+1) = m-1-s := by omega
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pref, hms]
  calc
    _ = ((m-1).choose s * (m-1-s)) * (2^(m-1-(s+1))*2) := by
      rw [hexp, pow_succ]
      ring
    _ = ((m-1).choose (s+1) * (s+1)) * (2^(m-1-(s+1))*2) := by rw [← hh]
    _ = _ := by ring

/-- The nonnegative Q coefficient inequality, for every m> = 3 and every degree j. -/
private theorem coefficient_capacity (m j : ℕ) (hm : 3 ≤ m) :
    2*pref (m-1) j * tail j (m/3) ≤ 3*pref (m-1) (j-1)*(3^(j-1)+low (j-1) (m/3)) + 2*pref (m-1) j := by
  by_cases hj : j = 0
  · simp [hj, tail, weight]
  by_cases hjm : j < m
  · have rel := pref_relation m j (by omega) (by omega) hjm
    have hs := scalar_capacity m j hm (by omega) hjm
    have hsm := Nat.mul_le_mul_left (pref (m-1) j) hs
    have heq : pref (m-1) j * (6*j*(3^(j-1)+low (j-1) (m/3))+2*(m-j)) = (m-j)*(3*pref (m-1) (j-1)*(3^(j-1)+low (j-1) (m/3))+2*pref (m-1) j) := by
      nlinarith [congrArg (fun a => a*(3*(3^(j-1)+low (j-1) (m/3)))) rel]
    rw [heq] at hsm
    have hl : (m-j)*(2*pref (m-1) j * tail j (m/3)) ≤ (m-j)*(3*pref (m-1) (j-1)*(3^(j-1)+low (j-1) (m/3))+2*pref (m-1) j) := by
      nlinarith
    exact Nat.le_of_mul_le_mul_left hl (by omega)
  · have hc : (m-1).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [pref, hc]

end Capacity

namespace Capacity

private def pc (m j : ℕ) : ℤ := (pref (m-1) j : ℤ)*3^j

private def ac (m j : ℕ) : ℤ := pref (m-1) j

/-- Coefficient contribution of the low positive prefix-count slices. -/
def lc (m j : ℕ) : ℤ := (pref (m-1) j : ℤ)*low j (m/3)

/-- Coefficient transform for multiplication by two plus three X. -/
def mulB (f : ℕ → ℤ) (j : ℕ) : ℤ := 2*f j + if j=0 then 0 else 3*f (j-1)

/-- Coefficient transform for multiplication by two plus X. -/
def mulV (f : ℕ → ℤ) (j : ℕ) : ℤ := 2*f j + if j=0 then 0 else f (j-1)

/-- Half of the interior exterior-discrepancy coefficient. -/
def dc (m j : ℕ) : ℤ := mulB (lc m) j - 4*(pc m j-ac m j)

/-- Half of the interior reservoir coefficient. -/
def nc (m j : ℕ) : ℤ := mulB (pc m) j

private lemma pc_nonneg (m j : ℕ) : 0 ≤ pc m j := by unfold pc; positivity
private lemma lc_le_pc (m j : ℕ) : lc m j ≤ pc m j := by
  have hh := partition j (m/3)
  have hl : low j (m/3) ≤ 3^j := by omega
  unfold lc pc
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl) (by positivity)

private lemma ac_le_pc (m j : ℕ) : ac m j ≤ pc m j := by
  have h : 1 ≤ (3 : ℕ)^j := Nat.one_le_pow j 3 (by decide)
  unfold ac pc
  nlinarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ 3^j by exact_mod_cast h)
    (show (0:ℤ) ≤ pref (m-1) j by positivity)]

private lemma dc_upper (m j : ℕ) : dc m j ≤ nc m j := by
  have h := lc_le_pc m j
  have hprev := lc_le_pc m (j-1)
  have hA := ac_le_pc m j
  unfold dc nc mulB
  split_ifs <;> omega

private lemma dc_lower (m j : ℕ) (hm : 3 ≤ m) : -nc m j ≤ dc m j := by
  have ht := partition j (m/3)
  have hi : 1 + (low j (m/3):ℤ) + tail j (m/3) = 3^j := by exact_mod_cast ht
  have hs := coefficient_capacity m j hm
  have hsZ : 2*(pref (m-1) j:ℤ)*tail j (m/3) ≤
      3*(pref (m-1) (j-1):ℤ)*(3^(j-1)+low (j-1) (m/3)) + 2*pref (m-1) j := by
    exact_mod_cast hs
  unfold nc dc mulB pc ac lc
  by_cases hj : j=0
  · simp [hj, low]
  · simp only [if_neg hj]
    nlinarith [congrArg (fun a => (pref (m-1) j:ℤ)*a) hi]

/-- Coefficientwise capacity of the fixed-label A0/B2 reservoir. -/
private lemma mul_v_preserves (f g : ℕ → ℤ) (h : ∀ j, -f j ≤ g j ∧ g j ≤ f j) (j : ℕ) :
    -mulV f j ≤ mulV g j ∧ mulV g j ≤ mulV f j := by
  have hj := h j
  have hp := h (j-1)
  unfold mulV
  split_ifs <;> omega

/-- Half of the actual reservoir generating coefficient after the anchor shift. -/
def reservoir_half (m z : ℕ) : ℤ := if 2 ≤ z then mulV (nc m) (z-2) else 0

/-- Half of the exterior discrepancy coefficient after the anchor shift. -/
def discrepancy_half (m z : ℕ) : ℤ := if 2 ≤ z then mulV (dc m) (z-2) else 0

end Capacity

namespace Capacity

private lemma low_zero (j : ℕ) : low j 0 = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have h : ¬ (0<k ∧ k≤0) := by omega
  exact if_neg h

private lemma nc_nonneg (m j : ℕ) : 0 ≤ nc m j := by
  have h := pc_nonneg m j
  have hp := pc_nonneg m (j-1)
  unfold nc mulB
  split_ifs <;> omega

private lemma core_lower_small (m j : ℕ) (hm : m=1 ∨ m=2) : -nc m j ≤ dc m j := by
  have hl (a b : ℕ) (hm : b<3) : lc b a = 0 := by
    unfold lc
    rw [show b/3=0 by omega, low_zero]
    simp
  rcases hm with rfl | rfl
  · have hd : dc 1 j = 0 := by
      unfold dc mulB
      rw [hl j 1 (by decide), hl (j-1) 1 (by decide)]
      by_cases hj : j=0
      · simp [hj, pc, ac, pref]
      · have hchoose : (0:ℕ).choose j=0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [pc, ac, pref, hchoose]
    rw [hd]
    have := nc_nonneg 1 j
    omega
  · by_cases hj0 : j=0
    · subst j
      norm_num [dc, nc, mulB, hl, pc, ac, pref]
    by_cases hj1 : j=1
    · subst j
      norm_num [dc, nc, mulB, hl, pc, ac, pref]
    have hchoose : (1:ℕ).choose j=0 := Nat.choose_eq_zero_of_lt (by omega)
    have hd : dc 2 j=0 := by
      unfold dc mulB
      rw [hl j 2 (by decide), hl (j-1) 2 (by decide)]
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

/-- For every positive m and every mass class z the explicit threshold is legal. -/
/-- Every positive prefix length and mass class have a legal integer reservoir split. -/
theorem integer_split_positive (m z : ℕ) (hm : 0 < m) :
    ∃ t : ℕ, (t:ℤ) ≤ 2*reservoir_half m z ∧
      2*discrepancy_half m z-2*reservoir_half m z+2*(t:ℤ)=0 := by
  have hc : -reservoir_half m z ≤ discrepancy_half m z ∧
      discrepancy_half m z ≤ reservoir_half m z := by
    unfold reservoir_half discrepancy_half
    split_ifs
    · exact mul_v_preserves (nc m) (dc m) (fun j => core_two_sided_positive m j hm) (z-2)
    · omega
  have hn : 0 ≤ reservoir_half m z-discrepancy_half m z := by omega
  refine ⟨(reservoir_half m z-discrepancy_half m z).toNat, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hn]
    omega
  · rw [Int.toNat_of_nonneg hn]
    ring

end Capacity
end

end D5.S3.Arith.FibonacciAtomic.CommonPrediction
