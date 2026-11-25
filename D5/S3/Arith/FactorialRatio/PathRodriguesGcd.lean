/- GID: D5/S3/Arith/FactorialRatio/PathRodriguesGcd
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/PathRodriguesGcd
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Multinomial]
   utility: none
   digest: Signed path factorial moments have an exact primitive tail-LCM gcd. -/

module

public import D5.S3.Arith.FactorialRatio.CompactFactorialGcd
import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# The exact path Rodrigues gcd

There are n real edges and n + 1 vertices. On an edge with allocation j,
j derivatives go to the source and k - j go to the target. The moment
functional on exponent tuples is the product of their factorials.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.PathRodriguesGcd

open Finset
open scoped BigOperators Nat
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd (factorialProduct tailLCM tailLCM_eq_gcd)
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd (compact_tail_factorization tail_nonzero)

/-! ## Signed binomial transitions -/

private def alternatingChoose (m : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ h ∈ range (m + 1), (-1 : ℤ) ^ h * (m.choose h : ℤ) * f h

private theorem alternatingChoose_succ (m : ℕ) (f : ℕ → ℤ) :
    alternatingChoose (m + 1) f = alternatingChoose m (fun h => f h - f (h + 1)) := by
  let P (h : ℕ) : ℤ := (-1 : ℤ) ^ h * (m.choose h : ℤ) * f h
  let Q (h : ℕ) : ℤ := (-1 : ℤ) ^ h * (m.choose h : ℤ) * f (h + 1)
  have hP0 : P 0 = f 0 := by simp [P]
  have hPend : P (m + 1) = 0 := by
    simp [P]
  have hsumP : (∑ h ∈ range (m + 1), P (h + 1)) + f 0 =
      ∑ h ∈ range (m + 1), P h := by
    calc
      _ = ∑ h ∈ range ((m + 1) + 1), P h := by
        rw [Finset.sum_range_succ' P (m + 1), hP0]
      _ = _ := by rw [Finset.sum_range_succ P (m + 1), hPend, add_zero]
  calc
    alternatingChoose (m + 1) f =
        (∑ h ∈ range (m + 1), (P (h + 1) - Q h)) + f 0 := by
      unfold alternatingChoose
      rw [Finset.sum_range_succ' _ (m + 1)]
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      dsimp only [P, Q]
      rw [Nat.choose_succ_succ', Nat.cast_add, pow_succ]
      ring
    _ = (∑ h ∈ range (m + 1), P h) - ∑ h ∈ range (m + 1), Q h := by
      rw [Finset.sum_sub_distrib, ← hsumP]
      ring
    _ = alternatingChoose m (fun h => f h - f (h + 1)) := by
      unfold alternatingChoose
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro h _
      dsimp only [P, Q]
      ring

private theorem alternatingChoose_shift (k N : ℕ) :
    alternatingChoose k (fun h => ((N + h).choose k : ℤ)) = (-1 : ℤ) ^ k := by
  induction k with
  | zero => simp [alternatingChoose]
  | succ k ih =>
      rw [alternatingChoose_succ]
      have hdiff : (fun h : ℕ =>
          ((N + h).choose (k + 1) : ℤ) - ((N + (h + 1)).choose (k + 1) : ℤ)) =
          fun h => -((N + h).choose k : ℤ) := by
        funext h
        rw [← Nat.add_assoc, Nat.choose_succ_succ', Nat.cast_add]
        ring
      rw [hdiff]
      calc
        alternatingChoose k (fun h => -((N + h).choose k : ℤ)) =
            -alternatingChoose k (fun h => ((N + h).choose k : ℤ)) := by
          simp only [alternatingChoose, mul_neg, Finset.sum_neg_distrib]
        _ = (-1 : ℤ) ^ (k + 1) := by rw [ih, pow_succ]; ring

private def transition (s : ℕ) {k : ℕ} (a b : Fin (k + 1)) : ℤ :=
  (-1 : ℤ) ^ (k - b.val) * (k.choose b.val : ℤ) * ((s + a.val - b.val).choose k : ℤ)

private theorem sum_transition {s k : ℕ} (hs : k ≤ s) (a : Fin (k + 1)) :
    (∑ b : Fin (k + 1), transition s a b) = (-1 : ℤ) ^ k := by
  let N := s + a.val - k
  calc
    (∑ b : Fin (k + 1), transition s a b) =
        ∑ h : Fin (k + 1), transition s a h.rev :=
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (k + 1))) (transition s a)).symm
    _ = ∑ h : Fin (k + 1), (-1 : ℤ) ^ h.val * (k.choose h.val : ℤ) *
          ((N + h.val).choose k : ℤ) := by
      apply Finset.sum_congr rfl
      intro h _
      have hh : h.val ≤ k := Nat.le_of_lt_succ h.isLt
      have hr : h.rev.val = k - h.val := by rw [Fin.val_rev]; omega
      have hsign : k - h.rev.val = h.val := by omega
      have hm : s + a.val - h.rev.val = N + h.val := by dsimp only [N]; omega
      rw [transition, hsign, hm, hr, Nat.choose_symm hh]
    _ = alternatingChoose k (fun h => ((N + h).choose k : ℤ)) :=
      Fin.sum_univ_eq_sum_range
        (fun h => (-1 : ℤ) ^ h * (k.choose h : ℤ) * ((N + h).choose k : ℤ)) (k + 1)
    _ = (-1 : ℤ) ^ k := alternatingChoose_shift k N

/-- Each real edge has a source load between zero and k. -/
public abbrev Allocation (n k : ℕ) := Fin n → Fin (k + 1)

private def pathWeight {n k : ℕ} (s : ℕ) (a : Fin (k + 1)) (j : Allocation n k) : ℤ :=
  ∏ i : Fin n, transition s (Fin.cons (α := fun _ => Fin (k + 1)) a j i.castSucc) (j i)

private theorem pathWeight_cons {n k : ℕ} (s : ℕ) (a b : Fin (k + 1))
    (j : Allocation n k) :
    pathWeight s a (Fin.cons (α := fun _ => Fin (k + 1)) b j : Allocation (n + 1) k) =
      transition s a b * pathWeight s b j := by
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  have hzero : (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 1 + 1)) := rfl
  simp only [hzero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]

private theorem sum_pathWeight {s k : ℕ} (hs : k ≤ s) (n : ℕ) (a : Fin (k + 1)) :
    (∑ j : Allocation n k, pathWeight s a j) = (-1 : ℤ) ^ (n * k) := by
  induction n generalizing a with
  | zero => rw [Fintype.sum_unique]; simp [pathWeight]
  | succ n ih =>
      let e := Fin.consEquiv (fun _ : Fin (n + 1) => Fin (k + 1))
      calc
        (∑ j : Allocation (n + 1) k, pathWeight s a j) =
            ∑ u : Fin (k + 1) × Allocation n k, pathWeight s a (e u) :=
          (Equiv.sum_comp e (pathWeight s a)).symm
        _ = ∑ b : Fin (k + 1), ∑ j : Allocation n k,
              transition s a b * pathWeight s b j := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro j _
          exact pathWeight_cons s a b j
        _ = (∑ b : Fin (k + 1), transition s a b) * (-1 : ℤ) ^ (n * k) := by
          simp only [← Finset.mul_sum, ih, ← Finset.sum_mul]
        _ = (-1 : ℤ) ^ ((n + 1) * k) := by
          rw [sum_transition hs, Nat.add_mul, one_mul, pow_add, mul_comm]

/-! ## Path coefficients and factorial moments -/

/-- The outgoing source load is zero at the final vertex. -/
@[expose] public def outgoing {n k : ℕ} (j : Allocation n k) (v : Fin (n + 1)) : ℕ :=
  (Fin.snoc (α := fun _ => Fin (k + 1)) j (0 : Fin (k + 1)) v).val

/-- The incoming target load is zero at the initial vertex. -/
@[expose] public def incoming {n k : ℕ} (j : Allocation n k) (v : Fin (n + 1)) : ℕ :=
  k - (Fin.cons (α := fun _ => Fin (k + 1)) (Fin.last k) j v).val

@[expose] public def Feasible {n k : ℕ} (s : ℕ) (j : Allocation n k) : Prop :=
  ∀ v, outgoing j v + incoming j v ≤ s

@[expose] public def feasibleAllocations (n s k : ℕ) : Finset (Allocation n k) :=
  Finset.univ.filter fun j => ∀ v : Fin (n + 1), outgoing j v + incoming j v ≤ s

@[simp] public theorem mem_feasibleAllocations {n s k : ℕ} {j : Allocation n k} :
    j ∈ feasibleAllocations n s k ↔ Feasible s j := by
  simp [feasibleAllocations, Feasible]

/-- Every real edge sends all derivatives to its source. -/
@[expose] public def allSource (n k : ℕ) : Allocation n k := fun _ => Fin.last k

public theorem allSource_feasible {n s k : ℕ} (hs : k ≤ s) : Feasible s (allSource n k) := by
  intro v
  have hin : incoming (allSource n k) v = 0 := by
    refine Fin.cases ?_ (fun i => ?_) v
    · simp [incoming]
    · simp [incoming, allSource]
  have hout : outgoing (allSource n k) v ≤ k :=
    Nat.le_of_lt_succ
      (Fin.snoc (α := fun _ => Fin (k + 1)) (allSource n k) (0 : Fin (k + 1)) v).isLt
  simpa only [hin, add_zero] using hout.trans hs

@[expose] public def residual {n k : ℕ} (s : ℕ) (j : Allocation n k) (v : Fin (n + 1)) : ℕ :=
  s - (outgoing j v + incoming j v)

@[expose] public def exponent {n k : ℕ} (s : ℕ) (j : Allocation n k) (v : Fin (n + 1)) : ℕ :=
  residual s j v + Fin.snoc (α := fun _ => ℕ) (fun _ : Fin n => k) 0 v

@[expose] public def coefficient {n k : ℕ} (s : ℕ) (j : Allocation n k) : ℕ :=
  ∏ v : Fin (n + 1),
    Nat.multinomial Finset.univ ![outgoing j v, incoming j v, residual s j v]

@[expose] public def sign {n k : ℕ} (j : Allocation n k) : ℤ :=
  ∏ i : Fin n, (-1 : ℤ) ^ (k - (j i).val)

@[expose] public def F (n s : ℕ) : ℕ := (s !) ^ (n + 1)

@[expose] public def A (n s : ℕ) : ℕ := tailLCM ((n + 1) * s + n) n

@[expose] public def rawMoment (n s k : ℕ) : ℤ :=
  ∑ j ∈ feasibleAllocations n s k,
    sign j * (coefficient s j : ℤ) * (factorialProduct (exponent s j) : ℤ)

private theorem parts_sum {n s k : ℕ} {j : Allocation n k} (hj : Feasible s j)
    (v : Fin (n + 1)) : outgoing j v + incoming j v + residual s j v = s := by
  exact Nat.add_sub_of_le (hj v)

private theorem load_mass {n s k : ℕ} {j : Allocation n k} (hj : Feasible s j) :
    (∑ i : Fin n, (j i).val) + (∑ i : Fin n, (k - (j i).val)) +
        (∑ v, residual s j v) = (n + 1) * s := by
  have hout : (∑ v, outgoing j v) = ∑ i : Fin n, (j i).val := by
    rw [Fin.sum_univ_castSucc]
    simp [outgoing]
  have hin : (∑ v, incoming j v) = ∑ i : Fin n, (k - (j i).val) := by
    rw [Fin.sum_univ_succ]
    simp [incoming]
  calc
    _ = ∑ v, (outgoing j v + incoming j v + residual s j v) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hout, hin]
    _ = (n + 1) * s := by
      simp [parts_sum hj]

public theorem exponent_degree {n s k : ℕ} {j : Allocation n k} (hj : Feasible s j) :
    (∑ v, exponent s j v) = (n + 1) * s := by
  have hweight :
      (∑ v : Fin (n + 1), Fin.snoc (α := fun _ => ℕ) (fun _ : Fin n => k) 0 v) = n * k := by
    rw [Fin.sum_univ_castSucc]
    simp
  have hloads : (∑ i : Fin n, (j i).val) + (∑ i : Fin n, (k - (j i).val)) = n * k := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : Fin n, k := by
        apply Finset.sum_congr rfl
        intro i _
        exact Nat.add_sub_of_le (Nat.le_of_lt_succ (j i).isLt)
      _ = _ := by simp
  have hm := load_mass hj
  rw [hloads] at hm
  unfold exponent
  rw [Finset.sum_add_distrib, hweight, add_comm]
  exact hm

private theorem exponent_castSucc {n s k : ℕ} {j : Allocation n k} (hk : k ≤ s)
    (hj : Feasible s j) (i : Fin n) :
    exponent s j i.castSucc =
      s + (Fin.cons (α := fun _ => Fin (k + 1)) (Fin.last k) j i.castSucc).val - (j i).val := by
  have hv := parts_sum hj i.castSucc
  have hp := Nat.le_of_lt_succ (Fin.cons (α := fun _ => Fin (k + 1)) (Fin.last k) j i.castSucc).isLt
  have hi := Nat.le_of_lt_succ (j i).isLt
  simp only [outgoing, incoming, Fin.snoc_castSucc] at hv
  simp only [exponent, Fin.snoc_castSucc]
  omega

public theorem exponent_injective {n s k : ℕ} (hk : k ≤ s) :
    Function.Injective (fun j : {j : Allocation n k // Feasible s j} => exponent s j.val) := by
  intro j j' he
  apply Subtype.ext
  have hj : ∀ v : Fin (n + 1),
      Fin.cons (α := fun _ => Fin (k + 1)) (Fin.last k) j.val v =
        Fin.cons (α := fun _ => Fin (k + 1)) (Fin.last k) j'.val v := by
    intro v
    refine Fin.induction ?_ ?_ v
    · simp
    · intro i hi
      have hp := congrArg (fun a : Fin (k + 1) => a.val) hi
      have hm := congrFun he i.castSucc
      change exponent s j.val i.castSucc = exponent s j'.val i.castSucc at hm
      rw [exponent_castSucc hk j.property, exponent_castSucc hk j'.property] at hm
      have hleft := Nat.le_of_lt_succ (j.val i).isLt
      have hright := Nat.le_of_lt_succ (j'.val i).isLt
      simp only [Fin.cons_succ]
      apply Fin.ext
      omega
  funext i
  simpa only [Fin.cons_succ] using hj i.succ

public theorem coefficient_pos {n s k : ℕ} (j : Allocation n k) : 0 < coefficient s j := by
  unfold coefficient
  exact Finset.prod_pos fun _ _ => Nat.multinomial_pos _ _

private def splitDenominator {n : ℕ} (a b : Fin n → ℕ) (c : Fin (n + 1) → ℕ) : ℕ :=
  (∏ i, (a i)!) * (∏ i, (b i)!) * (∏ i, (c i)!)

private def denominator {n k : ℕ} (s : ℕ) (j : Allocation n k) : ℕ :=
  splitDenominator (fun i => (j i).val) (fun i => k - (j i).val) (residual s j)

private theorem coefficient_mul_denominator {n s k : ℕ} {j : Allocation n k}
    (hj : Feasible s j) : coefficient s j * denominator s j = F n s := by
  have hout : (∏ v, (outgoing j v)!) = ∏ i : Fin n, ((j i).val)! := by
    rw [Fin.prod_univ_castSucc]
    simp [outgoing]
  have hin : (∏ v, (incoming j v)!) = ∏ i : Fin n, (k - (j i).val)! := by
    rw [Fin.prod_univ_succ]
    simp [incoming]
  let f (v : Fin (n + 1)) : Fin 3 → ℕ := ![outgoing j v, incoming j v, residual s j v]
  unfold coefficient denominator splitDenominator
  rw [← hout, ← hin, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  calc
    _ = ∏ v : Fin (n + 1), s ! := by
      apply Finset.prod_congr rfl
      intro v _
      have hm := Nat.multinomial_spec Finset.univ (f v)
      rw [Fin.prod_univ_three, Fin.sum_univ_three] at hm
      change ((outgoing j v)! * (incoming j v)! * (residual s j v)!) *
          Nat.multinomial Finset.univ (f v) =
          (outgoing j v + incoming j v + residual s j v)! at hm
      rw [parts_sum hj v] at hm
      exact (mul_comm _ _).trans hm
    _ = F n s := by simp [F]

private theorem factorialProd_ne_zero {m : ℕ} (f : Fin m → ℕ) :
    (∏ i, (f i)!) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero (f i))

private theorem splitDenominator_ne_zero {n : ℕ} (a b : Fin n → ℕ) (c : Fin (n + 1) → ℕ) :
    splitDenominator a b c ≠ 0 :=
  mul_ne_zero (mul_ne_zero (factorialProd_ne_zero a) (factorialProd_ne_zero b))
    (factorialProd_ne_zero c)

private def binomialProduct {n k : ℕ} (s : ℕ) (j : Allocation n k) : ℕ :=
  ∏ i : Fin n, k.choose (j i).val * (exponent s j i.castSucc).choose k

private theorem denominator_mul_binomialProduct {n s k : ℕ} (j : Allocation n k) :
    denominator s j * binomialProduct s j = factorialProduct (exponent s j) := by
  let a (i : Fin n) := (j i).val
  let b (i : Fin n) := k - (j i).val
  let c := residual s j
  change ((∏ i, (a i)!) * (∏ i, (b i)!) * (∏ v, (c v)!)) *
      (∏ i : Fin n, k.choose (a i) * (exponent s j i.castSucc).choose k) = _
  rw [Fin.prod_univ_castSucc (fun v => (c v)!)]
  calc
    _ = (∏ i : Fin n, (k.choose (a i) * (a i)! * (b i)!) *
              ((c i.castSucc)! * (exponent s j i.castSucc).choose k)) *
            (c (Fin.last n))! := by
      simp only [Finset.prod_mul_distrib]
      ring
    _ = (∏ i : Fin n, (exponent s j i.castSucc)!) * (c (Fin.last n))! := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      have hi : a i ≤ k := Nat.le_of_lt_succ (j i).isLt
      have hchoose : k.choose (a i) * (a i)! * (b i)! = k ! :=
        Nat.choose_mul_factorial_mul_factorial hi
      have hm : exponent s j i.castSucc = c i.castSucc + k := by
        simp only [exponent, Fin.snoc_castSucc, c]
      have hex := Nat.choose_mul_factorial_mul_factorial
        (n := c i.castSucc + k) (k := k) (Nat.le_add_left _ _)
      rw [Nat.add_sub_cancel] at hex
      rw [hchoose, hm, ← hex]
      ring
    _ = factorialProduct (exponent s j) := by
      unfold factorialProduct
      rw [Fin.prod_univ_castSucc]
      simp [exponent, c]

private theorem coefficient_mul_factorialProduct {n s k : ℕ} {j : Allocation n k}
    (hj : Feasible s j) :
    coefficient s j * factorialProduct (exponent s j) = F n s * binomialProduct s j := by
  rw [← denominator_mul_binomialProduct j, ← mul_assoc, coefficient_mul_denominator hj]

private theorem pathWeight_eq_sign_mul {n s k : ℕ} (hk : k ≤ s)
    {j : Allocation n k} (hj : Feasible s j) :
    pathWeight s (Fin.last k) j = sign j * (binomialProduct s j : ℤ) := by
  unfold pathWeight sign binomialProduct
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [transition, exponent_castSucc hk hj]
  ring

private theorem pathWeight_eq_zero {n s k : ℕ} (hk : k ≤ s)
    {j : Allocation n k} (hj : ¬ Feasible s j) : pathWeight s (Fin.last k) j = 0 := by
  unfold Feasible at hj
  push Not at hj
  obtain ⟨v, hv⟩ := hj
  have hlast : outgoing j (Fin.last n) + incoming j (Fin.last n) ≤ s := by
    have h := Nat.sub_le k (Fin.cons (α := fun _ => Fin (k + 1)) (Fin.last k) j (Fin.last n)).val
    simpa [outgoing, incoming] using h.trans hk
  have hlt (i : Fin n) (hi : s < outgoing j i.castSucc + incoming j i.castSucc) :
      s + (Fin.cons (α := fun _ => Fin (k + 1)) (Fin.last k) j i.castSucc).val - (j i).val < k := by
    have hb := Nat.le_of_lt_succ
      (Fin.cons (α := fun _ => Fin (k + 1)) (Fin.last k) j i.castSucc).isLt
    have ha := Nat.le_of_lt_succ (j i).isLt
    simp only [outgoing, incoming, Fin.snoc_castSucc] at hi
    omega
  revert hv
  refine Fin.lastCases ?_ ?_ v
  · intro hv
    exact (not_lt_of_ge hlast hv).elim
  · intro i hi
    unfold pathWeight
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [transition, Nat.choose_eq_zero_of_lt (hlt i hi), Nat.cast_zero, mul_zero]

/-- The exact signed factorial moment of the surviving path terms. -/
public theorem rawMoment_eq {n s k : ℕ} (hk : k ≤ s) :
    rawMoment n s k = (-1 : ℤ) ^ (n * k) * (F n s : ℤ) := by
  unfold rawMoment
  calc
    _ = ∑ j ∈ feasibleAllocations n s k, (F n s : ℤ) * pathWeight s (Fin.last k) j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hf := mem_feasibleAllocations.mp hj
      have hc := congrArg (fun z : ℕ => (z : ℤ)) (coefficient_mul_factorialProduct hf)
      simp only [Int.natCast_mul] at hc
      rw [pathWeight_eq_sign_mul hk hf, mul_assoc, hc]
      ring
    _ = ∑ j : Allocation n k, (F n s : ℤ) * pathWeight s (Fin.last k) j := by
      unfold feasibleAllocations
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : Feasible s j
      · exact ite_eq_left hj
      · have hn : ¬ ∀ v, outgoing j v + incoming j v ≤ s := hj
        rw [ite_eq_right hn, pathWeight_eq_zero hk hj, mul_zero]
    _ = _ := by rw [← Finset.mul_sum, sum_pathWeight hk, mul_comm]

/-! ## Content and divisibility of the primitive moment -/

@[expose] public def C (n s k : ℕ) : ℕ := (feasibleAllocations n s k).gcd (coefficient s)

@[expose] public def B (n s k : ℕ) : ℕ := F n s / C n s k

/-- The signed moment after dividing each surviving coefficient by its content. -/
@[expose] public def primitiveMoment (n s k : ℕ) : ℤ :=
  ∑ j ∈ feasibleAllocations n s k,
    sign j * ((coefficient s j / C n s k : ℕ) : ℤ) *
      (factorialProduct (exponent s j) : ℤ)

private theorem F_ne_zero (n s : ℕ) : F n s ≠ 0 :=
  pow_ne_zero _ (Nat.factorial_ne_zero _)

private theorem A_ne_zero (n s : ℕ) : A n s ≠ 0 := tail_nonzero _ _

public theorem C_ne_zero {n s k : ℕ} (hk : k ≤ s) : C n s k ≠ 0 := by
  unfold C
  exact Finset.gcd_ne_zero_iff.mpr
    ⟨allSource n k, mem_feasibleAllocations.mpr (allSource_feasible hk),
      (coefficient_pos (allSource n k)).ne'⟩

private theorem C_dvd_coefficient {n s k : ℕ} {j : Allocation n k} (hj : Feasible s j) :
    C n s k ∣ coefficient s j :=
  Finset.gcd_dvd (mem_feasibleAllocations.mpr hj)

public theorem C_dvd_F {n s k : ℕ} (hk : k ≤ s) : C n s k ∣ F n s := by
  have hj : Feasible s (allSource n k) := allSource_feasible hk
  exact (C_dvd_coefficient hj).trans ⟨denominator s (allSource n k),
    (coefficient_mul_denominator hj).symm⟩

public theorem B_mul_C {n s k : ℕ} (hk : k ≤ s) : B n s k * C n s k = F n s :=
  Nat.div_mul_cancel (C_dvd_F hk)

/-- The absolute magnitude of the signed primitive moment is the factorial quotient B. -/
public theorem primitiveMoment_eq {n s k : ℕ} (hk : k ≤ s) :
    primitiveMoment n s k = (-1 : ℤ) ^ (n * k) * (B n s k : ℤ) := by
  have hC : (C n s k : ℤ) ≠ 0 := by exact_mod_cast C_ne_zero (n := n) hk
  have hraw : primitiveMoment n s k * (C n s k : ℤ) = rawMoment n s k := by
    unfold primitiveMoment rawMoment
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hc := Nat.div_mul_cancel (C_dvd_coefficient (mem_feasibleAllocations.mp hj))
    have hc' : ((coefficient s j / C n s k : ℕ) : ℤ) * (C n s k : ℤ) =
        (coefficient s j : ℤ) := by exact_mod_cast hc
    calc
      _ = sign j * (((coefficient s j / C n s k : ℕ) : ℤ) * (C n s k : ℤ)) *
          (factorialProduct (exponent s j) : ℤ) := by ring
      _ = _ := by rw [hc']
  apply mul_right_cancel₀ hC
  rw [hraw, rawMoment_eq hk, mul_assoc, ← Int.natCast_mul, B_mul_C hk]

private theorem B_ne_zero {n s k : ℕ} (hk : k ≤ s) : B n s k ≠ 0 := by
  intro hz
  have h := B_mul_C (n := n) hk
  rw [hz, zero_mul] at h
  exact F_ne_zero n s h.symm

private theorem A_dvd_factorialProduct {n s : ℕ} (m : Fin (n + 1) → ℕ)
    (hm : (∑ v, m v) = (n + 1) * s) : A n s ∣ factorialProduct m := by
  have hH : n ≤ (n + 1) * s + n := Nat.le_add_left _ _
  unfold A
  rw [tailLCM_eq_gcd _ _ hH, Nat.add_sub_cancel]
  exact Finset.gcd_dvd (Finset.Nat.mem_antidiagonalTuple.mpr hm)

public theorem A_dvd_B {n s k : ℕ} (hk : k ≤ s) : A n s ∣ B n s k := by
  have hraw : ((C n s k * A n s : ℕ) : ℤ) ∣ rawMoment n s k := by
    unfold rawMoment
    apply Finset.dvd_sum
    intro j hj
    have hf := mem_feasibleAllocations.mp hj
    have hterm : C n s k * A n s ∣ coefficient s j * factorialProduct (exponent s j) :=
      Nat.mul_dvd_mul (C_dvd_coefficient hf)
        (A_dvd_factorialProduct (exponent s j) (exponent_degree hf))
    have hcast : ((C n s k * A n s : ℕ) : ℤ) ∣
        (coefficient s j : ℤ) * (factorialProduct (exponent s j) : ℤ) := by
      exact_mod_cast hterm
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right hcast (sign j)
  rw [rawMoment_eq hk] at hraw
  have hsign : (-1 : ℤ) ^ (n * k) * (-1 : ℤ) ^ (n * k) = 1 := by
    rw [← mul_pow]
    norm_num
  have hF := dvd_mul_of_dvd_right hraw ((-1 : ℤ) ^ (n * k))
  rw [← mul_assoc, hsign, one_mul] at hF
  exact (Nat.dvd_div_iff_mul_dvd (C_dvd_F hk)).mpr (Int.natCast_dvd_natCast.mp hF)

/-! ## Prime-specific denominator bound -/

-- The floor argument here specializes the independently reviewed split bound.
private theorem split_residues {a b q : ℕ} (hq : 0 < q) (h : q ∣ a + b + 1) :
    a % q + b % q = q - 1 := by
  have ha := Nat.mod_lt a hq
  have hb := Nat.mod_lt b hq
  have hm : (a % q + b % q + 1) % q = 0 := by
    calc
      _ = ((a % q + b % q) % q + 1 % q) % q := Nat.add_mod _ _ _
      _ = ((a + b) % q + 1 % q) % q := by rw [← Nat.add_mod a b q]
      _ = (a + b + 1) % q := (Nat.add_mod _ _ _).symm
      _ = 0 := Nat.mod_eq_zero_of_dvd h
  by_cases hl : a % q + b % q + 1 < q
  · rw [Nat.mod_eq_of_lt hl] at hm
    omega
  · have hge : q ≤ a % q + b % q + 1 := by omega
    have hsmall : a % q + b % q + 1 - q < q := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsmall] at hm
    omega

private theorem split_floor_upper {n s k q : ℕ} (hq : 0 < q) (hk : q ∣ k + 1)
    (a b : Fin n → ℕ) (c : Fin (n + 1) → ℕ)
    (hsplit : ∀ i, a i + b i = k)
    (hmass : (∑ i, a i) + (∑ i, b i) + (∑ i, c i) = (n + 1) * s) :
    (∑ i, a i / q) + (∑ i, b i / q) + (∑ i, c i / q) ≤
      ((n + 1) * s + n) / q - n := by
  let E := (∑ i, a i / q) + (∑ i, b i / q)
  let R := ∑ i, c i / q
  have hres (i : Fin n) : a i % q + b i % q = q - 1 :=
    split_residues hq (by rw [hsplit i]; exact hk)
  have hlocal (i : Fin n) :
      q * (a i / q + b i / q) + (q - 1) = a i + b i := by
    calc
      _ = (q * (a i / q) + a i % q) + (q * (b i / q) + b i % q) := by
        rw [← hres i]
        ring
      _ = _ := by rw [Nat.div_add_mod, Nat.div_add_mod]
  have hedge : q * E + n * (q - 1) = (∑ i, a i) + (∑ i, b i) := by
    calc
      _ = ∑ i : Fin n, (q * (a i / q + b i / q) + (q - 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
        simp [E]
      _ = ∑ i : Fin n, (a i + b i) := Finset.sum_congr rfl (fun i _ => hlocal i)
      _ = _ := Finset.sum_add_distrib
  have hrem : q * R ≤ ∑ i, c i := by
    unfold R
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := Nat.div_add_mod (c i) q
    omega
  have hshift : n * (q - 1) + n = n * q := by
    calc
      _ = n * (q - 1 + 1) := by ring
      _ = n * q := by rw [Nat.sub_add_cancel (show 1 ≤ q by omega)]
  have hbudget : (E + R + n) * q ≤ (n + 1) * s + n := by
    calc
      _ = q * E + q * R + n * q := by ring
      _ = (q * E + n * (q - 1)) + q * R + n := by rw [← hshift]; ring
      _ ≤ _ := by rw [hedge]; omega
  have hle : E + R + n ≤ ((n + 1) * s + n) / q :=
    (Nat.le_div_iff_mul_le hq).mpr hbudget
  change E + R ≤ ((n + 1) * s + n) / q - n
  omega

private theorem factorialProd_factorization {m p s K : ℕ} (hp : p.Prime)
    (hlog : Nat.log p s < K) (f : Fin m → ℕ) (hf : ∀ i, f i ≤ s) :
    (∏ i, (f i)!).factorization p = ∑ e ∈ Ico 1 K, ∑ i, f i / p ^ e := by
  rw [Nat.factorization_prod_apply (fun i _ => Nat.factorial_ne_zero (f i))]
  calc
    _ = ∑ i : Fin m, ∑ e ∈ Ico 1 K, f i / p ^ e :=
      Finset.sum_congr rfl (fun i _ =>
        Nat.factorization_factorial hp ((Nat.log_mono_right (hf i)).trans_lt hlog))
    _ = _ := Finset.sum_comm

private theorem splitDenominator_factorization_le {n s k p L : ℕ} (hp : p.Prime)
    (hk : k + 1 = p ^ L) (hsK : s < p ^ (L + 1))
    (a b : Fin n → ℕ) (c : Fin (n + 1) → ℕ)
    (hsplit : ∀ i, a i + b i = k)
    (hmass : (∑ i, a i) + (∑ i, b i) + (∑ i, c i) = (n + 1) * s)
    (ha : ∀ i, a i ≤ s) (hb : ∀ i, b i ≤ s) (hc : ∀ i, c i ≤ s) :
    (splitDenominator a b c).factorization p ≤ (A n s).factorization p := by
  have hlog : Nat.log p s < L + 1 := Nat.log_lt_of_lt_pow' (by omega) hsK
  have htail := compact_tail_factorization (r := n + 1) hp (by omega) hsK
  have htail' : (A n s).factorization p =
      ∑ e ∈ Ico 1 (L + 1), (((n + 1) * s + n) / p ^ e - n) := by
    simpa only [A, Nat.add_sub_cancel] using htail
  rw [splitDenominator, Nat.factorization_mul
      (mul_ne_zero (factorialProd_ne_zero a) (factorialProd_ne_zero b))
      (factorialProd_ne_zero c), Finsupp.add_apply,
      Nat.factorization_mul (factorialProd_ne_zero a) (factorialProd_ne_zero b),
      Finsupp.add_apply, factorialProd_factorization hp hlog a ha,
      factorialProd_factorization hp hlog b hb, factorialProd_factorization hp hlog c hc,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, htail']
  apply Finset.sum_le_sum
  intro e he
  have heL : e ≤ L := Nat.le_of_lt_succ (Finset.mem_Ico.mp he).2
  have hq : p ^ e ∣ k + 1 := by
    rw [hk]
    exact Nat.pow_dvd_pow p heL
  exact split_floor_upper (pow_pos hp.pos e) hq a b c hsplit hmass

/-- All surviving coefficients at an order k + 1 = p^L have the same
lower bound on their p-adic valuation. -/
public theorem coefficient_factorization_lower {n s k p L : ℕ} (hp : p.Prime)
    (hk : k ≤ s) (hkL : k + 1 = p ^ L) (hsK : s < p ^ (L + 1))
    {j : Allocation n k} (hj : Feasible s j) :
    (F n s).factorization p - (A n s).factorization p ≤ (coefficient s j).factorization p := by
  let a (i : Fin n) := (j i).val
  let b (i : Fin n) := k - (j i).val
  let c := residual s j
  have ha (i : Fin n) : a i ≤ k := Nat.le_of_lt_succ (j i).isLt
  have hb (i : Fin n) : b i ≤ k := Nat.sub_le _ _
  have hc (v : Fin (n + 1)) : c v ≤ s := Nat.sub_le _ _
  have hab (i : Fin n) : a i + b i = k := Nat.add_sub_of_le (ha i)
  have hD : (denominator s j).factorization p ≤ (A n s).factorization p :=
    splitDenominator_factorization_le hp hkL hsK a b c hab (load_mass hj)
      (fun i => (ha i).trans hk) (fun i => (hb i).trans hk) hc
  have hDne : denominator s j ≠ 0 := splitDenominator_ne_zero a b c
  have hval := congrArg (fun z : ℕ => z.factorization p) (coefficient_mul_denominator hj)
  change (coefficient s j * denominator s j).factorization p = (F n s).factorization p at hval
  rw [Nat.factorization_mul (coefficient_pos j).ne' hDne, Finsupp.add_apply] at hval
  omega

/-- An explicit order attaining the exact valuation for the given prime. -/
@[expose] public def primeOrder (p s : ℕ) : ℕ := p ^ Nat.log p (s + 1) - 1

public theorem primeOrder_le (p s : ℕ) : primeOrder p s ≤ s := by
  have h : p ^ Nat.log p (s + 1) ≤ s + 1 := Nat.pow_log_le_self p (Nat.succ_ne_zero s)
  unfold primeOrder
  omega

public theorem B_factorization_primeOrder {p : ℕ} (hp : p.Prime) (n s : ℕ) :
    (B n s (primeOrder p s)).factorization p = (A n s).factorization p := by
  let L := Nat.log p (s + 1)
  let k := primeOrder p s
  change (B n s k).factorization p = (A n s).factorization p
  have hk : k ≤ s := primeOrder_le p s
  have hkL : k + 1 = p ^ L :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos hp.pos L))
  have hsK : s < p ^ (L + 1) :=
    (Nat.lt_succ_self s).trans (Nat.lt_pow_succ_log_self hp.one_lt (s + 1))
  have hpow : p ^ ((F n s).factorization p - (A n s).factorization p) ∣ C n s k := by
    unfold C
    apply Finset.dvd_gcd
    intro j hj
    exact (hp.pow_dvd_iff_le_factorization (coefficient_pos j).ne').mpr
      (coefficient_factorization_lower hp hk hkL hsK (mem_feasibleAllocations.mp hj))
  have hC := (hp.pow_dvd_iff_le_factorization (C_ne_zero hk)).mp hpow
  have hA := (Nat.factorization_prime_le_iff_dvd (A_ne_zero n s) (B_ne_zero hk)).mpr
    (A_dvd_B hk) p hp
  have hF := congrArg (fun z : ℕ => z.factorization p) (B_mul_C (n := n) hk)
  change (B n s k * C n s k).factorization p = (F n s).factorization p at hF
  rw [Nat.factorization_mul (B_ne_zero hk) (C_ne_zero hk), Finsupp.add_apply] at hF
  omega

/-- The gcd of the primitive path moments for orders 0 through s. -/
public theorem gcd_B_eq_A (n s : ℕ) : (Finset.range (s + 1)).gcd (B n s) = A n s := by
  let G := (Finset.range (s + 1)).gcd (B n s)
  change G = A n s
  have hAG : A n s ∣ G := by
    apply Finset.dvd_gcd
    intro k hk
    exact A_dvd_B (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hG : G ≠ 0 := Finset.gcd_ne_zero_iff.mpr
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ s), B_ne_zero (Nat.zero_le s)⟩
  apply Nat.dvd_antisymm _ hAG
  apply (Nat.factorization_prime_le_iff_dvd hG (A_ne_zero n s)).mp
  intro p hp
  have hk : primeOrder p s ∈ Finset.range (s + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (primeOrder_le p s))
  have hd : G ∣ B n s (primeOrder p s) := Finset.gcd_dvd hk
  have hv := (Nat.factorization_prime_le_iff_dvd hG (B_ne_zero (primeOrder_le p s))).mpr hd p hp
  exact hv.trans_eq (B_factorization_primeOrder hp n s)

/-- In vertex-count coordinates, the exact Rodrigues gcd is the rank-one
tail at H = r(s + 1) - 1 and M = r - 1. -/
public theorem exact_path_rodrigues_gcd {r : ℕ} (hr : 2 ≤ r) (s : ℕ) :
    (Finset.range (s + 1)).gcd (B (r - 1) s) = tailLCM (r * (s + 1) - 1) (r - 1) := by
  rw [gcd_B_eq_A, A, Nat.sub_add_cancel (show 1 ≤ r by omega)]
  rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_assoc (show 1 ≤ r by omega)]

#print axioms rawMoment_eq
#print axioms primitiveMoment_eq
#print axioms B_factorization_primeOrder
#print axioms exact_path_rodrigues_gcd

end D5.S3.Arith.FactorialRatio.PathRodriguesGcd
