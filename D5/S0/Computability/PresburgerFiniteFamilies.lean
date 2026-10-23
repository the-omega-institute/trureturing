/- GID: D5/S0/Computability/PresburgerFiniteFamilies
   generality: G
   mirror-B: D5/B/S0/Computability/PresburgerFiniteFamilies
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite dependent products and chart sums preserve polynomial trace bounds. -/

import D5.S0.Computability.PresburgerPatternGrowth
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
Finite families of separated-atom relations on arbitrary dependent source and
sample carriers. Restriction to the indices of each sample type injects global
patterns into a product of trace families. The product is an upper bound and
need not be jointly realizable. A finite union over source charts gives a fixed
positive polynomial bound. Empty carriers and repeated samples are included.
-/

set_option autoImplicit false

namespace PresburgerFiniteFamilies

open PresburgerPatternGrowth
open scoped BigOperators

universe u v w z r

/-- Evaluation on the disjoint unions of source charts and descriptor types. -/
def joint {K : Type u} {T : Type v} {X : K → Type w} {Y : T → Type z}
    (f : (k : K) → (t : T) → X k → Y t → Bool)
    (x : Sigma X) (y : Sigma Y) : Bool := f x.1 y.1 x.2 y.2

open Classical in
/-- A common source with several dependent descriptor types has a product
upper bound on its finite patterns. No descriptor carrier needs an inhabitant. -/
theorem trace_card_dependent_product {T : Type u} [Fintype T]
    {X : Type v} {Y : T → Type w} {I : Type z} [Fintype I]
    (f : (t : T) → X → Y t → Bool) (sample : I → Sigma Y) :
    (traces (fun x i => f (sample i).1 x (sample i).2)).card ≤
      ∏ t, (traces (fun x (i : {i : I // (sample i).1 = t}) =>
        f t x (cast (congrArg Y i.2) (sample i.1).2))).card := by
  classical
  let slice (t : T) := traces (fun x (i : {i : I // (sample i).1 = t}) =>
    f t x (cast (congrArg Y i.2) (sample i.1).2))
  let Code := (t : T) → {p // p ∈ slice t}
  let code (x : X) : Code := fun t =>
    ⟨fun i => f t x (cast (congrArg Y i.2) (sample i.1).2),
      (mem_traces _ _).mpr ⟨x, rfl⟩⟩
  let decode (c : Code) (i : I) := (c (sample i).1).1 ⟨i, rfl⟩
  calc
    _ ≤ Fintype.card Code := trace_card_factor _ code decode (fun _ => rfl)
    _ = _ := by simp only [Code, slice, Fintype.card_pi, Fintype.card_coe]

/-- A source-chart union is bounded by the sum of its trace counts. -/
theorem trace_card_chart_sum {K : Type u} [Fintype K]
    {X : K → Type v} {I : Type w} [Fintype I]
    (f : (k : K) → X k → I → Bool) :
    (traces (fun (x : Sigma X) i => f x.1 x.2 i)).card ≤
      ∑ k, (traces (f k)).card := by
  classical
  calc
    _ ≤ (Finset.univ.biUnion (fun k => traces (f k))).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨⟨k,x⟩, rfl⟩ := (mem_traces _ _).mp hp
      exact Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_univ _, (mem_traces _ _).mpr ⟨x,rfl⟩⟩
    _ ≤ _ := Finset.card_biUnion_le

/-- The fixed coefficient is one plus the sum of chart products. The fixed
exponent is the sum of all component exponents, including unused types. -/
theorem finite_family_polynomial_bound {K : Type u} {T : Type v}
    [Fintype K] [Fintype T] {X : K → Type w} {Y : T → Type z}
    (f : (k : K) → (t : T) → X k → Y t → Bool)
    (C s : K → T → Nat) (h : ∀ k t, Growth (f k t) (C k t) (s k t)) :
    0 < (∑ k, ∏ t, C k t) + 1 ∧
    ∀ {I : Type r} [Fintype I] (sample : I → Sigma Y),
      (traces (fun x i => joint f x (sample i))).card ≤
        ((∑ k, ∏ t, C k t) + 1) *
          (Fintype.card I + 1) ^ (∑ k, ∑ t, s k t) := by
  classical
  refine ⟨Nat.succ_pos _, ?_⟩
  intro I _ sample
  have chart (k : K) :
      (traces (fun x i => f k (sample i).1 x (sample i).2)).card ≤
        (∏ t, C k t) * (Fintype.card I + 1) ^ (∑ t, s k t) := by
    calc
      _ ≤ ∏ t, (traces (fun x (i : {i : I // (sample i).1 = t}) =>
            f k t x (cast (congrArg Y i.2) (sample i.1).2))).card :=
        trace_card_dependent_product (f k) sample
      _ ≤ ∏ t, C k t * (Fintype.card I + 1) ^ (s k t) := by
        apply Finset.prod_le_prod'
        intro t _
        exact ((polynomial_trace_bound (h k t)).2
          (fun i : {i : I // (sample i).1 = t} => cast (congrArg Y i.2) (sample i.1).2)).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
            (Nat.add_le_add_right (Fintype.card_subtype_le _) 1) _))
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ ∑ k, (traces (fun x i => f k (sample i).1 x (sample i).2)).card :=
      trace_card_chart_sum _
    _ ≤ ∑ k, (∏ t, C k t) * (Fintype.card I + 1) ^ (∑ k, ∑ t, s k t) := by
      apply Finset.sum_le_sum
      intro k _
      exact (chart k).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega)
          (Finset.single_le_sum (f := fun k => ∑ t, s k t)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))))
    _ = (∑ k, ∏ t, C k t) * (Fintype.card I + 1) ^ (∑ k, ∑ t, s k t) :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- An explicit finite index at which the exponential exceeds any given
natural-coefficient polynomial. -/
theorem finite_exponential_domination (C s : Nat) :
    ∃ n : Nat, C * (n + 1) ^ s < 2 ^ n := by
  let k := C * (s + 2) ^ s + 1
  have hk : 0 < k := Nat.succ_pos _
  refine ⟨(s + 1) * k, ?_⟩
  have hsize : (s + 1) * k + 1 ≤ (s + 2) * k := by
    nlinarith
  calc
    C * ((s + 1) * k + 1) ^ s ≤ C * ((s + 2) * k) ^ s :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize _)
    _ = (C * (s + 2) ^ s) * k ^ s := by rw [mul_pow, Nat.mul_assoc]
    _ < k * k ^ s := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (pow_pos hk _)
    _ = k ^ (s + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ (2 ^ k) ^ (s + 1) := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) _
    _ = 2 ^ ((s + 1) * k) := by rw [← pow_mul, Nat.mul_comm]

#print axioms trace_card_dependent_product
#print axioms trace_card_chart_sum
#print axioms finite_family_polynomial_bound
#print axioms finite_exponential_domination

end PresburgerFiniteFamilies
