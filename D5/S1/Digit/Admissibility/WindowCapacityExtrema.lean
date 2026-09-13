/- GID: D5/S1/Digit/Admissibility/WindowCapacityExtrema
   generality: I
   mirror-B: D5/B/S1/Digit/Admissibility/WindowCapacityExtrema
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact capacities for products of Fibonacci windows and all conditions for equality. -/

import D5.S0.Conventions.WDigits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Lemmas

set_option autoImplicit false

namespace D5.S1.Digit.Admissibility.WindowCapacityExtrema

open D5.S0.Conventions
open scoped BigOperators

/-- Width vectors with a prescribed total width. -/
def feasibleWidths (k B : ℕ) : Set (Fin k → ℕ) :=
  {L | ∑ i, L i = B}

/-- The number of states in the product of the specified Fibonacci windows. -/
def windowProduct {k : ℕ} (L : Fin k → ℕ) : ℕ :=
  ∏ i, wValue (L i)

/-- Below the register count the widths are zero or one; above it all but one are one. -/
def ExtremalShape {k : ℕ} (B : ℕ) (L : Fin k → ℕ) : Prop :=
  (B ≤ k → ∀ i, L i ≤ 1) ∧
  (k ≤ B → ∃ i, L i = B - k + 1 ∧ ∀ j, j ≠ i → L j = 1)

/-- The explicit capacity for a positive number of registers and a total width budget. -/
def capacity (k B : ℕ) : ℕ :=
  if B ≤ k then 2 ^ B else 2 ^ (k - 1) * wValue (B - k + 1)

/-- Every width vector maximizing the window product at fixed total width has the stated extremal shape. -/
theorem maximizer_has_extremal_shape {k B : ℕ} (hk : 1 ≤ k) (L : Fin k → ℕ)
    (hL : L ∈ feasibleWidths k B)
    (hmax : ∀ M ∈ feasibleWidths k B, windowProduct M ≤ windowProduct L) :
    ExtremalShape B L := by
  classical
  have hsum : ∑ i, L i = B := hL
  have improve (i j : Fin k) (hij : i ≠ j) (a b : ℕ)
      (hab : a + b = L i + L j)
      (hprod : wValue (L i) * wValue (L j) < wValue a * wValue b) : False := by
    let S := (Finset.univ.erase i).erase j
    let M : Fin k → ℕ := fun x => if x = i then a else if x = j then b else L x
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    have sum_split (f : Fin k → ℕ) : ∑ x, f x = f i + f j + ∑ x ∈ S, f x := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ hj]
      exact (Nat.add_assoc _ _ _).symm
    have prod_split (f : Fin k → ℕ) : ∏ x, f x = f i * f j * ∏ x ∈ S, f x := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ _ hj]
      exact (Nat.mul_assoc _ _ _).symm
    have hM (x : Fin k) (hx : x ∈ S) : M x = L x := by
      have hxj := (Finset.mem_erase.mp hx).1
      have hxi := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      simp [M, hxi, hxj]
    have hMi : M i = a := by simp [M]
    have hMj : M j = b := by simp [M, hij.symm]
    have hfeas : M ∈ feasibleWidths k B := by
      change ∑ x, M x = B
      rw [sum_split, hMi, hMj, Finset.sum_congr rfl hM, hab, ← sum_split, hsum]
    have htail : 0 < ∏ x ∈ S, wValue (L x) := by
      apply Finset.prod_pos
      intro x _
      exact Nat.fib_pos.mpr (by omega)
    have hgt : windowProduct L < windowProduct M := by
      unfold windowProduct
      rw [prod_split, prod_split (fun x => wValue (M x)), hMi, hMj]
      have heq : (∏ x ∈ S, wValue (M x)) = ∏ x ∈ S, wValue (L x) :=
        Finset.prod_congr rfl fun x hx => congrArg wValue (hM x hx)
      rw [heq]
      exact Nat.mul_lt_mul_of_pos_right hprod htail
    exact (not_lt_of_ge (hmax M hfeas)) hgt
  have no_zero_large (i j : Fin k) (hi : L i = 0) (hj : 2 ≤ L j) : False := by
    have hij : i ≠ j := by rintro rfl; omega
    obtain ⟨n, hn⟩ : ∃ n, L j = n + 2 := ⟨L j - 2, by omega⟩
    apply improve i j hij 1 (n + 1)
    · omega
    · rw [hi, hn, wValue_zero, wValue_one, one_mul]
      unfold wValue
      have hrec := Nat.fib_add_two (n := n + 2)
      have hstrict := Nat.fib_lt_fib_succ (n := n + 2) (by omega)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hrec hstrict ⊢
      omega
  have no_two_large (i j : Fin k) (hij : i ≠ j) (hi : 2 ≤ L i) (hj : 2 ≤ L j) : False := by
    obtain ⟨a, ha⟩ : ∃ a, L i = a + 1 := ⟨L i - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, L j = b + 1 := ⟨L j - 1, by omega⟩
    apply improve i j hij (a + b + 1) 1
    · omega
    · rw [ha, hb, wValue_one]
      have hid : 2 * wValue (a + b + 1) =
          wValue (a + 1) * wValue (b + 1) + Nat.fib a * Nat.fib b := by
        unfold wValue
        have hab := Nat.fib_add (a + 1) (b + 1)
        simp only [Nat.add_assoc, Nat.reduceAdd] at hab ⊢
        rw [show a + (1 + (b + 2)) = a + (b + 3) by omega] at hab
        have ha2 := Nat.fib_add_two (n := a)
        have ha3 := Nat.fib_add_two (n := a + 1)
        have hb2 := Nat.fib_add_two (n := b)
        have hb3 := Nat.fib_add_two (n := b + 1)
        simp only [Nat.add_assoc, Nat.reduceAdd] at ha3 hb3
        nlinarith
      have hapos : 0 < Nat.fib a := Nat.fib_pos.mpr (by omega)
      have hbpos : 0 < Nat.fib b := Nat.fib_pos.mpr (by omega)
      nlinarith [Nat.mul_pos hapos hbpos]
  constructor
  · intro hBk i
    by_contra hi
    have hilarge : 2 ≤ L i := by omega
    have hpos : ∀ j, 1 ≤ L j := by
      intro j
      by_contra hj
      exact no_zero_large j i (by omega) hilarge
    have hlt : (∑ _j : Fin k, (1 : ℕ)) < ∑ j, L j :=
      Finset.sum_lt_sum (fun j _ => hpos j) ⟨i, Finset.mem_univ i, by omega⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hlt
    omega
  · intro hkB
    have hpos : ∀ j, 1 ≤ L j := by
      intro j
      by_contra hj
      have hjzero : L j = 0 := by omega
      have hsmall : ∀ i, L i ≤ 1 := by
        intro i
        by_contra hi
        exact no_zero_large j i hjzero (by omega)
      have hlt : (∑ i, L i) < ∑ _i : Fin k, (1 : ℕ) :=
        Finset.sum_lt_sum (fun i _ => hsmall i) ⟨j, Finset.mem_univ j, by omega⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hlt
      omega
    obtain ⟨i, hrest⟩ : ∃ i : Fin k, ∀ j, j ≠ i → L j = 1 := by
      by_cases hlarge : ∃ i, 2 ≤ L i
      · obtain ⟨i, hi⟩ := hlarge
        refine ⟨i, ?_⟩
        intro j hji
        have hjpos := hpos j
        by_contra hj
        exact no_two_large j i hji (by omega) hi
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro j _
        have hj := hpos j
        have hn : ¬ 2 ≤ L j := fun h => hlarge ⟨j, h⟩
        omega
    refine ⟨i, ?_, hrest⟩
    have htail : (∑ j ∈ Finset.univ.erase i, L j) = k - 1 := by
      calc
        _ = ∑ _j ∈ Finset.univ.erase i, (1 : ℕ) :=
          Finset.sum_congr rfl fun j hj => hrest j (Finset.mem_erase.mp hj).1
        _ = k - 1 := by simp
    have heq := Finset.sum_erase_add Finset.univ L (Finset.mem_univ i)
    rw [htail, hsum] at heq
    omega

#print axioms maximizer_has_extremal_shape

/-- The explicit capacity is attained and is the greatest window product; equality holds exactly
for the extremal width shapes. -/
theorem capacity_isGreatest_and_eq_iff {k B : ℕ} (hk : 1 ≤ k) :
    IsGreatest (windowProduct '' feasibleWidths k B) (capacity k B) ∧
      ∀ L ∈ feasibleWidths k B, windowProduct L = capacity k B ↔ ExtremalShape B L := by
  classical
  have evaluate (L : Fin k → ℕ) (hL : L ∈ feasibleWidths k B)
      (hshape : ExtremalShape B L) : windowProduct L = capacity k B := by
    have hsum : ∑ i, L i = B := hL
    by_cases hBk : B ≤ k
    · have hfactor (i : Fin k) : wValue (L i) = 2 ^ L i := by
        have hi := hshape.1 hBk i
        have hi01 : L i = 0 ∨ L i = 1 := by omega
        rcases hi01 with h | h <;> simp [h]
      calc
        windowProduct L = ∏ i, 2 ^ L i := Finset.prod_congr rfl fun i _ => hfactor i
        _ = 2 ^ B := by rw [Finset.prod_pow_eq_pow_sum, hsum]
        _ = capacity k B := by simp [capacity, hBk]
    · obtain ⟨i, hi, hrest⟩ := hshape.2 (by omega)
      have htail : (∏ j ∈ Finset.univ.erase i, wValue (L j)) = 2 ^ (k - 1) := by
        calc
          _ = ∏ _j ∈ Finset.univ.erase i, (2 : ℕ) :=
            Finset.prod_congr rfl fun j hj => by
              rw [hrest j (Finset.mem_erase.mp hj).1, wValue_one]
          _ = 2 ^ (k - 1) := by simp
      unfold windowProduct
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hi, htail]
      simp [capacity, hBk, Nat.mul_comm]
  have hfinite : (feasibleWidths k B).Finite := by
    apply (Set.Finite.pi' (t := fun _ : Fin k => Set.Iic B)
      (fun _ => Set.finite_le_nat B)).subset
    intro L hL i
    have hsum : ∑ j, L j = B := hL
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
      Nat.zero_le (L j)) (Finset.mem_univ i)
    change L i ≤ B
    omega
  have hnonempty : (feasibleWidths k B).Nonempty := by
    let i : Fin k := ⟨0, by omega⟩
    refine ⟨fun j => if j = i then B else 0, ?_⟩
    change (∑ j : Fin k, if j = i then B else 0) = B
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image (feasibleWidths k B) windowProduct
    hfinite hnonempty
  have hvalue := evaluate M hM (maximizer_has_extremal_shape hk M hM hmax)
  have hbound (L : Fin k → ℕ) (hL : L ∈ feasibleWidths k B) :
      windowProduct L ≤ capacity k B := by
    rw [← hvalue]
    exact hmax L hL
  refine ⟨⟨⟨M, hM, hvalue⟩, ?_⟩, ?_⟩
  · rintro _ ⟨L, hL, rfl⟩
    exact hbound L hL
  · intro L hL
    constructor
    · intro heq
      apply maximizer_has_extremal_shape hk L hL
      intro N hN
      rw [heq]
      exact hbound N hN
    · exact evaluate L hL

#print axioms capacity_isGreatest_and_eq_iff

/-- The product of the register state counts is bounded by the exact capacity. Equality holds
exactly when the budget is exhausted, the widths are extremal, and every register is saturated. -/
theorem state_product_le_capacity_and_eq_iff {k B : ℕ} (hk : 1 ≤ k)
    (L A : Fin k → ℕ) (hA : ∀ i, A i < wValue (L i)) (hbudget : ∑ i, L i ≤ B) :
    (∏ i, (A i + 1)) ≤ capacity k B ∧
      ((∏ i, (A i + 1)) = capacity k B ↔
        (∑ i, L i) = B ∧ ExtremalShape B L ∧ ∀ i, A i = wValue (L i) - 1) := by
  classical
  let i : Fin k := ⟨0, by omega⟩
  let M : Fin k → ℕ := fun j => if j = i then L j + (B - ∑ x, L x) else L j
  have hMi : M i = L i + (B - ∑ x, L x) := by simp [M]
  have hrest (j : Fin k) (hj : j ∈ Finset.univ.erase i) : M j = L j := by
    simp [M, (Finset.mem_erase.mp hj).1]
  have hM : M ∈ feasibleWidths k B := by
    change ∑ j, M j = B
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hMi,
      Finset.sum_congr rfl hrest]
    rw [Nat.add_right_comm, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    exact Nat.add_sub_of_le hbudget
  have hLM (j : Fin k) : L j ≤ M j := by
    by_cases hji : j = i <;> simp [M, hji]
  have hfactor (j : Fin k) : wValue (L j) ≤ wValue (M j) :=
    Nat.fib_add_two_strictMono.monotone (hLM j)
  have hpositive (j : Fin k) : 0 < wValue (L j) := Nat.fib_pos.mpr (by omega)
  have hWM : windowProduct L ≤ windowProduct M :=
    Finset.prod_le_prod (fun j _ => Nat.zero_le _) (fun j _ => hfactor j)
  have hMC : windowProduct M ≤ capacity k B :=
    (capacity_isGreatest_and_eq_iff hk).1.2 ⟨M, hM, rfl⟩
  have hAC : (∏ j, (A j + 1)) ≤ windowProduct L :=
    Finset.prod_le_prod (fun j _ => Nat.zero_le _) (fun j _ => hA j)
  have hWC : windowProduct L ≤ capacity k B := hWM.trans hMC
  refine ⟨hAC.trans hWC, ?_⟩
  constructor
  · intro heq
    have hfull : (∑ j, L j) = B := by
      by_contra hne
      have hstrict : windowProduct L < windowProduct M := by
        apply Finset.prod_lt_prod (fun j _ => hpositive j) (fun j _ => hfactor j)
        refine ⟨i, Finset.mem_univ i, ?_⟩
        apply Nat.fib_add_two_strictMono
        rw [hMi]
        omega
      have := hAC.trans_lt (hstrict.trans_le hMC)
      omega
    have hvalue : windowProduct L = capacity k B := by omega
    refine ⟨hfull, (capacity_isGreatest_and_eq_iff hk).2 L hfull |>.mp hvalue, ?_⟩
    intro j
    have heqfactor : A j + 1 = wValue (L j) := by
      by_contra hne
      have hstrict : (∏ x, (A x + 1)) < windowProduct L := by
        apply Finset.prod_lt_prod (fun x _ => Nat.succ_pos _) (fun x _ => hA x)
        exact ⟨j, Finset.mem_univ j, by have := hA j; omega⟩
      omega
    omega
  · rintro ⟨hfull, hshape, hsat⟩
    have hvalue := (capacity_isGreatest_and_eq_iff hk).2 L hfull |>.mpr hshape
    calc
      (∏ j, (A j + 1)) = windowProduct L := by
        apply Finset.prod_congr rfl
        intro j _
        rw [hsat j]
        have := hpositive j
        omega
      _ = capacity k B := hvalue

#print axioms state_product_le_capacity_and_eq_iff

end D5.S1.Digit.Admissibility.WindowCapacityExtrema
