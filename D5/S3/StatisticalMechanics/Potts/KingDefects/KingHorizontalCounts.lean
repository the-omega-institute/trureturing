/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Interior counts and horizontal orientation sums. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229571.result, HardinA229573.result, HardinA229574.result, HardinA229575.result, HardinA229576.result, HardinA229577.result, HardinA229578.result)
interior_count_support: proof_shape=bind-only; consumers=KingHorizontal.interior_count
supports: proof_shape=bind-only; consumers=KingHorizontal.pair_support_cases,KingHorizontal.support_case_count,KingHorizontal.support_case_eval,KingHorizontal.support_sizes_correct,KingHorizontal.supports_equiv
supports_equiv: proof_shape=bind-only; consumers=KingHorizontal.pair_support_cases
lower_pair_values: proof_shape=bind-only; consumers=KingHorizontal.lower_pair,KingHorizontal.lower_pair_valid
lower_pair_valid: proof_shape=bind-only; consumers=KingHorizontal.lower_pair
lower_pair: proof_shape=bind-only; consumers=KingHorizontal.interior_count,KingHorizontal.lower_pair_equiv,KingHorizontal.pair_support_cases,KingHorizontal.support_sizes_correct
lower_pair_equiv: proof_shape=bind-only; consumers=KingHorizontal.interior_count
support_sizes: proof_shape=bind-only; consumers=KingHorizontal.pair_support_cases,KingHorizontal.support_case_count,KingHorizontal.support_case_eval,KingHorizontal.support_sizes_correct
support_sizes_correct: proof_shape=bind-only; consumers=KingHorizontal.pair_support_cases
support_case_count: proof_shape=bind-only; consumers=KingHorizontal.interior_count,KingHorizontal.pair_support_cases,KingHorizontal.support_case_eval
pair_support_cases: proof_shape=bind-only; consumers=KingHorizontal.interior_count
P: proof_shape=bind-only; consumers=KingHorizontal.interior_count,KingHorizontal.interior_endpoint_value,KingHorizontal.interior_middle_value,KingHorizontal.interior_row_sum,KingHorizontal.interior_three_rows_count,KingHorizontal.six_case_value,KingHorizontal.support_case_eval
Q: proof_shape=bind-only; consumers=KingHorizontal.interior_count,KingHorizontal.interior_endpoint_value,KingHorizontal.interior_middle_value,KingHorizontal.interior_row_sum,KingHorizontal.interior_three_rows_count,KingHorizontal.six_case_value,KingHorizontal.support_case_eval
six_case_value: proof_shape=bind-only; consumers=KingHorizontal.interior_count,KingHorizontal.support_case_eval
support_case_eval: proof_shape=bind-only; consumers=KingHorizontal.interior_count
interior_count: proof_shape=bind-only; consumers=KingHorizontal.interior_row_sum,KingHorizontal.interior_three_rows_count
horizontal_two_rows: proof_shape=bind-only; consumers=KingClosedForm.width_two,KingHorizontal.horizontal_two_columns
boundary_one_column: proof_shape=bind-only; consumers=KingHorizontal.boundary_slots_one_column,KingHorizontal.horizontal_two_columns
boundary_slots_one_column: proof_shape=bind-only; consumers=KingHorizontal.interior_one_column_count
interior_one_column_count: proof_shape=bind-only; consumers=KingHorizontal.horizontal_two_columns
horizontal_two_columns: proof_shape=bind-only; consumers=KingClosedForm.width_two
interior_three_rows_count: proof_shape=bind-only; consumers=KingHorizontal.horizontal_three_rows
sum_two_powers: proof_shape=bind-only; consumers=KingHorizontal.boundary_row_sum,KingHorizontal.horizontal_sum,KingHorizontal.horizontal_three_rows,KingHorizontal.interior_row_sum,KingHorizontal.sum_two_powers_reverse
sum_two_powers_reverse: proof_shape=bind-only; consumers=KingHorizontal.boundary_row_sum,KingHorizontal.horizontal_sum,KingHorizontal.horizontal_three_rows,KingHorizontal.interior_row_sum
horizontal_three_rows: proof_shape=bind-only; consumers=KingClosedForm.width_three
interior_endpoint_value: proof_shape=bind-only; consumers=KingHorizontal.interior_row_sum
interior_middle_value: proof_shape=bind-only; consumers=KingHorizontal.interior_row_sum
interior_row_sum: proof_shape=bind-only; consumers=KingHorizontal.horizontal_sum
boundary_row_sum: proof_shape=bind-only; consumers=KingHorizontal.horizontal_sum
sum_left_indicator: proof_shape=bind-only; consumers=KingHorizontal.horizontal_sum,KingHorizontal.sum_right_indicator
sum_right_indicator: proof_shape=bind-only; consumers=KingHorizontal.horizontal_sum
horizontal_sum: proof_shape=bind-only; consumers=KingClosedForm.closed_form,KingClosedForm.width_three
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
import Mathlib.Algebra.Ring.GeomSum

/-! Horizontal defects, with dimensions expressed as numbers of steps. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal

open KingGrid KingDifference
open scoped IsAddKleinFour

/-- The general interior count reduces to sixteen support pairs for each ordered pair. -/
theorem interior_count_support (a b c d : ℕ) :
    N_e (.H (cut_row (a + 1) (b + 1)) (pivot c d) :
      Edge ((a + 1) + (b + 1) + 1) (c + (d + 1) + 1)) =
      ∑ x : NZPair, ∑ y : NZPair, pair_support_count a b c d x y := by
  rw [interior_count_alphabets]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact pair_count_support a b c d x y

def supports : Fin 4 → Finset Bool := ![∅,{false},{true},Finset.univ]

private noncomputable def supports_equiv : Fin 4 ≃ Finset Bool :=
  Equiv.ofBijective supports (by decide)

def lower_pair_values (x : NZPair) : Fin 6 → K × K :=
  ![(x.val.1,x.val.2),(x.val.2,x.val.1),(x.val.1,x.val.1+x.val.2),
    (x.val.1+x.val.2,x.val.2),(x.val.1+x.val.2,x.val.1),(x.val.2,x.val.1+x.val.2)]

theorem lower_pair_valid (x : NZPair) (i : Fin 6) :
    (lower_pair_values x i).1 ≠ 0 ∧ (lower_pair_values x i).2 ≠ 0 ∧
      (lower_pair_values x i).1 ≠ (lower_pair_values x i).2 := by
  have h : ∀ x : NZPair, ∀ i : Fin 6,
      (lower_pair_values x i).1 ≠ 0 ∧ (lower_pair_values x i).2 ≠ 0 ∧
        (lower_pair_values x i).1 ≠ (lower_pair_values x i).2 := by decide
  exact h x i

def lower_pair (x : NZPair) (i : Fin 6) : NZPair :=
  ⟨lower_pair_values x i,lower_pair_valid x i⟩

private noncomputable def lower_pair_equiv (x : NZPair) : Fin 6 ≃ NZPair :=
  Equiv.ofBijective (lower_pair x) (by
    have h : ∀ x : NZPair,
        (∀ i j, lower_pair x i = lower_pair x j → i = j) ∧
        (∀ y, ∃ i, lower_pair x i = y) := by decide
    exact h x)

def support_sizes : Fin 6 → Fin 4 → Fin 4 → ℕ × ℕ :=
  ![![![(2,2),(2,1),(1,2),(1,1)],
      ![(2,1),(2,1),(1,1),(1,1)],
      ![(1,2),(1,1),(1,2),(1,1)],
      ![(1,1),(1,1),(1,1),(1,1)]],
    ![![(1,1),(1,1),(1,1),(1,1)],
      ![(1,1),(1,1),(1,1),(1,1)],
      ![(1,1),(1,1),(1,1),(1,1)],
      ![(1,1),(1,1),(1,1),(1,1)]],
    ![![(2,1),(2,0),(1,1),(1,0)],
      ![(2,0),(2,0),(1,0),(1,0)],
      ![(1,1),(1,0),(0,1),(0,0)],
      ![(1,0),(1,0),(0,0),(0,0)]],
    ![![(1,2),(1,1),(0,2),(0,1)],
      ![(1,1),(1,0),(0,1),(0,0)],
      ![(0,2),(0,1),(0,2),(0,1)],
      ![(0,1),(0,0),(0,1),(0,0)]],
    ![![(1,1),(1,0),(1,1),(1,0)],
      ![(1,1),(1,0),(1,1),(1,0)],
      ![(0,1),(0,0),(0,1),(0,0)],
      ![(0,1),(0,0),(0,1),(0,0)]],
    ![![(1,1),(1,1),(0,1),(0,1)],
      ![(1,0),(1,0),(0,0),(0,0)],
      ![(1,1),(1,1),(0,1),(0,1)],
      ![(1,0),(1,0),(0,0),(0,0)]]]

theorem support_sizes_correct (x : NZPair) (i : Fin 6) (j k : Fin 4) :
    (Nat.card (SupportAlphabet x (lower_pair x i) (supports j) (supports k)
      x.val.1 (lower_pair x i).val.1),
    Nat.card (SupportAlphabet x (lower_pair x i) (supports j) (supports k)
      x.val.2 (lower_pair x i).val.2)) = support_sizes i j k := by
  have h : ∀ x : NZPair, ∀ i : Fin 6, ∀ j k : Fin 4,
      (Fintype.card (SupportAlphabet x (lower_pair x i) (supports j) (supports k)
        x.val.1 (lower_pair x i).val.1),
      Fintype.card (SupportAlphabet x (lower_pair x i) (supports j) (supports k)
        x.val.2 (lower_pair x i).val.2)) = support_sizes i j k := by decide
  simpa only [Nat.card_eq_fintype_card] using h x i j k

def support_case_count (a b c d : ℕ) (i : Fin 6) : ℕ :=
  ∑ j : Fin 4, ∑ k : Fin 4, support_weight a (supports j) * support_weight b (supports k) *
    (support_sizes i j k).1 ^ c * (support_sizes i j k).2 ^ d

theorem pair_support_cases (a b c d : ℕ) (x : NZPair) (i : Fin 6) :
    pair_support_count a b c d x (lower_pair x i) = support_case_count a b c d i := by
  unfold pair_support_count support_case_count
  symm
  apply Fintype.sum_equiv supports_equiv
  intro j
  apply Fintype.sum_equiv supports_equiv
  intro k
  have h := support_sizes_correct x i j k
  rw [← h]
  rfl

/-- The P term in the six lower-pair cases, including all empty-side cases. -/
def P (a b c d : ℕ) : ℕ :=
  if d = 0 then E c a b else ((if a = 0 then 1 else 0) + (if b = 0 then 1 else 0)) ^ c

/-- The Q term in the six lower-pair cases. -/
def Q (a b c d : ℕ) : ℕ :=
  (1 + if c = 0 then 1 else 0) ^ a * (1 + if d = 0 then 1 else 0) ^ b

def six_case_value (a b c d : ℕ) : Fin 6 → ℕ :=
  ![E (a+b) c d,2^(a+b),P a b c d,P a b d c,Q a b c d,Q a b d c]

set_option maxHeartbeats 800000 in
-- The six support tables cover every zero/nonzero combination of four word lengths.
theorem support_case_eval (a b c d : ℕ) (i : Fin 6) :
    support_case_count a b c d i = six_case_value a b c d i := by
  have ha : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have hb : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by decide)
  have hc : 1 ≤ 2 ^ c := Nat.one_le_pow c 2 (by decide)
  have hd : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
  have sub_bound (n : ℕ) : n=0 ∨ 2^n-2+2=2^n := by
    by_cases hn : n=0
    · exact Or.inl hn
    · exact Or.inr (Nat.sub_add_cancel
        (Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two (Nat.pos_of_ne_zero hn)))
  have hsa := sub_bound a
  have hsb := sub_bound b
  have hse : a+b=0 ∨ (2^(a+b)+2^c+2^d-2)+2=2^(a+b)+2^c+2^d := by
    by_cases hm : a+b=0
    · exact Or.inl hm
    · right
      apply Nat.sub_add_cancel
      have hp : 2 ≤ 2^(a+b) :=
        Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two (Nat.pos_of_ne_zero hm)
      omega
  have h2 : (Finset.univ : Finset Bool) ≠ {true} := by decide
  fin_cases i <;>
    simp only [support_case_count, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    cases a <;> cases b <;> cases c <;> cases d <;>
    simp [supports, support_weight, support_sizes, six_case_value, E, P, Q,
      pow_add,pow_succ] at ha hb hc hd hsa hsb hse ⊢ <;> simp_all <;> first | omega | nlinarith

/-- Lemma 7, equation (10), for all interior rows and every empty-side case. -/
theorem interior_count (a b c d : ℕ) :
    N_e (.H (cut_row (a + 1) (b + 1)) (pivot c d) :
      Edge ((a + 1) + (b + 1) + 1) (c + (d + 1) + 1)) =
      6 * (E (a+b) c d + 2^(a+b) + P a b c d + P a b d c + Q a b c d + Q a b d c) := by
  rw [interior_count_support]
  have h (x : NZPair) :
      (∑ y : NZPair, pair_support_count a b c d x y) =
        E (a+b) c d + 2^(a+b) + P a b c d + P a b d c + Q a b c d + Q a b d c := by
    rw [← Equiv.sum_comp (lower_pair_equiv x)]
    change (∑ i : Fin 6, pair_support_count a b c d x (lower_pair x i)) = _
    simp_rw [pair_support_cases, support_case_eval]
    simp [six_case_value, Fin.sum_univ_succ, add_assoc]
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hp : Fintype.card NZPair = 6 := by simpa [Nat.card_eq_fintype_card] using nz_pair_card
  rw [hp]

/-- The horizontal sum on two rows, including the empty edge set. -/
theorem horizontal_two_rows (M : ℕ) : N_H 1 M = 6 * (M * 2 ^ M) := by
  cases M with
  | zero => simp [N_H]
  | succ M =>
    have hc (r : Fin 2) (s : Fin (M + 1)) :
        N_e (.H r s : Edge 2 (M + 1 + 1)) = 6 * 2 ^ M := by
      have hr : r = 0 ∨ r = Fin.last 1 := by fin_cases r <;> simp
      have h := boundary_rows_count r s hr
      have hs : s.val + (M + 1 - 1 - s.val) = M := by have := s.isLt; omega
      change N_e (.H r s : Edge 2 (M + 1 + 1)) =
        6 * 2 ^ (s.val + (M + 1 - 1 - s.val)) at h
      rw [hs] at h
      exact h
    unfold N_H
    simp_rw [hc]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, pow_succ]
    ring

theorem boundary_one_column (m : ℕ) :
    N_e (.H 0 (0 : Fin 1) : Edge (m + 1 + 1) 2) = 6 * 2 ^ m := by
  have h := boundary_count m 0 0
  have he : E m 0 0 = 2 ^ m := by
    cases m <;> simp [E]
  simpa [he, pivot] using h

theorem boundary_slots_one_column (m : ℕ) :
    Nat.card {b : BoundaryData m 1 // BoundaryValid (0 : Fin 1) b} = 6 * 2 ^ m := by
  rw [← Nat.card_congr (boundary_slot_equiv m 1 0)]
  exact boundary_one_column m

/-- With one column interval the two boundary assignments have no compatibility condition. -/
theorem interior_one_column_count (a b : ℕ) :
    N_e (.H (cut_row (a + 1) (b + 1)) (0 : Fin 1) :
      Edge ((a + 1) + (b + 1) + 1) 2) = 36 * 2 ^ (a + b) := by
  let e : InteriorSlots a b 1 0 ≃
      {u : BoundaryData a 1 // BoundaryValid (0 : Fin 1) u} ×
        {l : BoundaryData b 1 // BoundaryValid (0 : Fin 1) l} :=
    Equiv.subtypeUnivEquiv (fun q j hj => (hj (Subsingleton.elim j 0)).elim)
  unfold N_e
  rw [Nat.card_congr (interior_slot_equiv a b 1 0), Nat.card_congr e, Nat.card_prod,
    boundary_slots_one_column, boundary_slots_one_column, pow_add]
  ring

/-- The sum at width two, stated without truncated subtraction. -/
theorem horizontal_two_columns (p : ℕ) : N_H (p + 1) 1 = 6 * ((3 * p + 2) * 2 ^ p) := by
  cases p with
  | zero => simpa using horizontal_two_rows 1
  | succ p =>
    have hc (i : Fin (p + 1)) :
        N_e (.H i.castSucc.succ (0 : Fin 1) : Edge (p + 1 + 1 + 1) 2) = 36 * 2 ^ p := by
      have aux (a b : ℕ) {P : ℕ} (hP : P = (a + 1) + (b + 1))
          (r : Fin (P + 1)) (hr : r.val = a + 1) :
          N_e (.H r (0 : Fin 1) : Edge (P + 1) 2) = 36 * 2 ^ (a + b) := by
        subst P
        have he : r = cut_row (a + 1) (b + 1) := Fin.ext hr
        subst r
        exact interior_one_column_count a b
      have h := aux i.val (p - i.val) (P := p + 1 + 1)
        (by have := i.isLt; omega) i.castSucc.succ rfl
      have he : i.val + (p - i.val) = p := by have := i.isLt; omega
      simpa [he] using h
    have ht := boundary_one_column (p + 1)
    have hb : N_e (.H (Fin.last (p + 1 + 1)) (0 : Fin 1) : Edge (p + 1 + 1 + 1) 2) =
        6 * 2 ^ (p + 1) := by
      have h := horizontal_count_row_reflect (0 : Fin (p + 1 + 1 + 1)) (0 : Fin 1)
      simpa using h.trans ht
    unfold N_H
    simp only [Fin.sum_univ_one]
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp_rw [hc]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    simp only [Fin.succ_last]
    rw [ht, hb]
    simp only [pow_succ]
    ring

/-- The middle row of a three-row rectangle, including empty left or right sides. -/
theorem interior_three_rows_count (c d : ℕ) :
    N_e (.H (1 : Fin 3) (pivot c d) : Edge 3 (c + (d + 1) + 1)) =
      6 * (2 ^ (c + d) + 2 ^ c + 2 ^ d + 3) := by
  have hp (c d : ℕ) : P 0 0 c d = 2^c := by
    cases c <;> cases d <;> simp [P,E]
  have hq (c d : ℕ) : Q 0 0 c d = 1 := by simp [Q]
  have h := interior_count 0 0 c d
  have hr : cut_row (0+1) (0+1) = (1 : Fin 3) := Fin.ext rfl
  rw [hr,hp,hp,hq,hq] at h
  simp only [Nat.zero_add,E,ite_true,pow_zero] at h
  omega

private theorem sum_two_powers (q : ℕ) : (∑ i : Fin q, 2 ^ i.val) + 1 = 2 ^ q := by
  rw [Fin.sum_univ_eq_sum_range]
  simpa using (geom_sum_mul_add (1 : ℕ) q)

private theorem sum_two_powers_reverse (q : ℕ) :
    (∑ i : Fin (q + 1), 2 ^ (q - i.val)) + 1 = 2 ^ (q + 1) := by
  have hr := Equiv.sum_comp (Fin.revPerm (n := q + 1)) (fun i : Fin (q+1) => (2 : ℕ)^i.val)
  have hv (i : Fin (q + 1)) : (Fin.revPerm i).val = q - i.val := by simp [Fin.revPerm, Fin.rev]
  simp only [hv] at hr
  rw [hr]
  exact sum_two_powers (q + 1)

/-- Three rows and any width at least two, in subtraction-free form. -/
theorem horizontal_three_rows (q : ℕ) :
    N_H 2 (q + 1) + 54 = 6 * ((q + 13) * 2 ^ q + 3 * (q + 2)) := by
  have hc (s : Fin (q + 1)) :
      N_e (.H (1 : Fin 3) s : Edge 3 (q + 1 + 1)) =
        6 * (2 ^ q + 2 ^ s.val + 2 ^ (q - s.val) + 3) := by
    have aux (c d : ℕ) {M : ℕ} (hM : M = c + (d + 1))
        (s : Fin M) (hs : s.val = c) :
        N_e (.H (1 : Fin 3) s : Edge 3 (M + 1)) =
          6 * (2 ^ (c + d) + 2 ^ c + 2 ^ d + 3) := by
      subst M
      have hp : s = pivot c d := Fin.ext hs
      subst s
      exact interior_three_rows_count c d
    have h := aux s.val (q - s.val) (by have := s.isLt; omega) s rfl
    have he : s.val + (q - s.val) = q := by have := s.isLt; omega
    simpa [he] using h
  have hb (s : Fin (q + 1)) :
      N_e (.H (0 : Fin 3) s : Edge 3 (q + 1 + 1)) + 12 =
        6 * (2 + 2 ^ s.val + 2 ^ (q - s.val)) := by
    have h := boundary_count_at (m := 1) s
    simp only [E, one_ne_zero, ↓reduceIte, pow_one] at h
    have hp : (2 : ℕ) ≤ 2 + 2 ^ s.val + 2 ^ (q - s.val) :=
      (Nat.le_add_right 2 _).trans (Nat.le_add_right _ _)
    have hs : q + 1 - 1 - s.val = q - s.val := by omega
    rw [hs] at h
    omega
  have hb' (s : Fin (q + 1)) :
      N_e (.H (Fin.last 2) s : Edge 3 (q + 1 + 1)) =
        N_e (.H (0 : Fin 3) s) := by
    simpa using horizontal_count_row_reflect (0 : Fin 3) s
  have hbs := congrArg (fun f : Fin (q+1) → ℕ => ∑ s, f s) (funext hb)
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbs
  have hgeom := sum_two_powers (q+1)
  have hrev := sum_two_powers_reverse q
  unfold N_H
  rw [Fin.sum_univ_three]
  simp_rw [hc]
  have hlast : (2 : Fin 3) = Fin.last 2 := rfl
  rw [hlast]
  simp_rw [hb']
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbs ⊢
  simp only [pow_succ] at hgeom hrev
  nlinarith

theorem interior_endpoint_value (a b d : ℕ) (hm : 0 < a + b) (hd : 0 < d) :
    E (a+b) 0 d + 2^(a+b) + P a b 0 d + P a b d 0 + Q a b 0 d + Q a b d 0 + 2 =
      2^(a+b+1) + 2^(d+1) + 2^(a+1) + 2^(b+1) := by
  have he : 2 ≤ 2 ^ (a+b) := Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two hm
  have hpa : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have hpb : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by decide)
  have hpd : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
  simp only [E,P,Q,Nat.ne_of_gt hm,Nat.ne_of_gt hd,ite_false,ite_true,
    pow_zero,one_pow,zero_add,add_zero,pow_succ]
  norm_num
  omega

theorem interior_middle_value (a b c d : ℕ) (hm : 0 < a + b)
    (hc : 0 < c) (hd : 0 < d) :
    E (a+b) c d + 2^(a+b) + P a b c d + P a b d c + Q a b c d + Q a b d c =
      2^(a+b+1) + 2^c + 2^d + 2*((if a=0 then 1 else 0)+(if b=0 then 1 else 0)) := by
  have he : 2 ≤ 2 ^ (a+b) := Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two hm
  simp only [E,P,Q,Nat.ne_of_gt hm,Nat.ne_of_gt hc,Nat.ne_of_gt hd,
    ite_false,add_zero,one_pow,pow_succ]
  have hpc : (1 : ℕ) ≤ 2^c := Nat.one_le_pow c 2 (by decide)
  have hpd : (1 : ℕ) ≤ 2^d := Nat.one_le_pow d 2 (by decide)
  by_cases ha : a=0 <;> by_cases hb : b=0 <;>
    simp_all [Nat.ne_of_gt hc,Nat.ne_of_gt hd]
  all_goals omega

/-- A whole interior row, with two endpoint positions separated from the middle. -/
theorem interior_row_sum (a b q : ℕ) (hm : 0 < a + b) :
    (∑ s : Fin (q+2),
      N_e (.H (cut_row (a+1) (b+1)) s : Edge ((a+1)+(b+1)+1) (q+2+1))) + 48 =
      6*((q+2)*2^(a+b+1) + 3*2^(q+2) + 2^(a+2) + 2^(b+2) +
        2*q*((if a=0 then 1 else 0)+(if b=0 then 1 else 0))) := by
  have aux (c d : ℕ) {M : ℕ} (hM : M = c+(d+1)) (s : Fin M) (hs : s.val=c) :
      N_e (.H (cut_row (a+1) (b+1)) s : Edge ((a+1)+(b+1)+1) (M+1)) =
        6*(E (a+b) c d + 2^(a+b) + P a b c d + P a b d c + Q a b c d + Q a b d c) := by
    subst M
    have hp : s = pivot c d := Fin.ext hs
    subst s
    exact interior_count a b c d
  have hfirst := aux 0 (q+1) (M:=q+2) (by omega) (0 : Fin (q+2)) rfl
  have hlast := aux (q+1) 0 (M:=q+2) (by omega) (Fin.last (q+1)) rfl
  have he := interior_endpoint_value a b (q+1) hm (by omega)
  have hsym (c d : ℕ) :
      E (a+b) c d + 2^(a+b) + P a b c d + P a b d c + Q a b c d + Q a b d c =
      E (a+b) d c + 2^(a+b) + P a b d c + P a b c d + Q a b d c + Q a b c d := by
    have he : E (a+b) c d = E (a+b) d c := by
      simp only [E,Nat.ne_of_gt hm,ite_false]
      congr 1
      omega
    rw [he]
    omega
  rw [hsym] at hlast
  have hqe : q+1+1=q+2 := by omega
  rw [hqe] at he
  have hfirst' : N_e (.H (cut_row (a+1) (b+1)) (0 : Fin (q+2))) + 12 =
      6*(2^(a+b+1)+2^(q+2)+2^(a+1)+2^(b+1)) := by omega
  have hlast' : N_e (.H (cut_row (a+1) (b+1)) (Fin.last (q+1) : Fin (q+2))) + 12 =
      6*(2^(a+b+1)+2^(q+2)+2^(a+1)+2^(b+1)) := by omega
  have hmid (s : Fin q) :
      N_e (.H (cut_row (a+1) (b+1)) s.castSucc.succ :
        Edge ((a+1)+(b+1)+1) (q+2+1)) =
        6*(2^(a+b+1)+2^(s.val+1)+2^(q-s.val)+
          2*((if a=0 then 1 else 0)+(if b=0 then 1 else 0))) := by
    have h := aux (s.val+1) (q-s.val) (by have := s.isLt; omega) s.castSucc.succ rfl
    rw [h,interior_middle_value a b _ _ hm (by omega) (by have := s.isLt; omega)]
  have hg := sum_two_powers q
  have hr : (∑ s : Fin q, 2^(q-s.val)) + 2 = 2^(q+1) := by
    cases q with
    | zero => simp
    | succ q =>
      have h := sum_two_powers_reverse q
      have he (s : Fin (q+1)) : q+1-s.val = (q-s.val)+1 := by have := s.isLt; omega
      simp_rw [he,pow_succ]
      rw [← Finset.sum_mul]
      omega
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc (fun s : Fin (q+1) =>
    N_e (.H (cut_row (a+1) (b+1)) s.succ : Edge ((a+1)+(b+1)+1) (q+2+1)))]
  simp only [Fin.succ_last]
  simp_rw [hmid]
  simp only [pow_succ]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  simp only [pow_succ] at hfirst' hlast' hr ⊢
  nlinarith

theorem boundary_row_sum (m q : ℕ) (hm : 0 < m) :
    (∑ s : Fin (q+2), N_e (.H (0 : Fin (m+2)) s : Edge (m+2) (q+2+1))) +
        12*(q+2)+12 = 6*((q+2)*2^m+2^(q+3)) := by
  have hc (s : Fin (q+2)) : N_e (.H (0 : Fin (m+2)) s : Edge (m+2) (q+2+1)) + 12 =
      6*(2^m+2^s.val+2^(q+1-s.val)) := by
    have h := boundary_count_at (m:=m) s
    unfold E at h
    rw [ite_eq_right (Nat.ne_of_gt hm)] at h
    have he : q+2-1-s.val=q+1-s.val := by omega
    rw [he] at h
    have hp : 2 ≤ 2^m := Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two hm
    have hpc : (0 : ℕ) ≤ 2^s.val := Nat.zero_le _
    have hpd : (0 : ℕ) ≤ 2^(q+1-s.val) := Nat.zero_le _
    omega
  have hsum := congrArg (fun f : Fin (q+2) → ℕ => ∑ s, f s) (funext hc)
  have hg := sum_two_powers (q+2)
  have hr := sum_two_powers_reverse (q+1)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  simp only [pow_succ] at hg hr ⊢
  nlinarith

private theorem sum_left_indicator (t : ℕ) :
    (∑ i : Fin (t+2), if i.val=0 then 1 else 0) = (1 : ℕ) := by
  rw [Fin.sum_univ_succ]
  simp

private theorem sum_right_indicator (t : ℕ) :
    (∑ i : Fin (t+2), if t+1-i.val=0 then 1 else 0) = (1 : ℕ) := by
  have hr := Equiv.sum_comp (Fin.revPerm (n:=t+2))
    (fun i : Fin (t+2) => if i.val=0 then (1 : ℕ) else 0)
  have hv (i : Fin (t+2)) : (Fin.revPerm i).val = t+1-i.val := by
    simp [Fin.revPerm,Fin.rev]
  simp only [hv] at hr
  rw [hr]
  exact sum_left_indicator t

/-- Lemma 9 for at least four rows and three columns, with no natural subtraction. -/
theorem horizontal_sum (t q : ℕ) :
    N_H (t+3) (q+2) + 6*(8*(t+4)+4) =
      6*((((t+4)*(q+2)+8)*2^(t+2))+(3*t+10)*2^(q+2)) := by
  have hrows (i : Fin (t+2)) :
      (∑ s : Fin (q+2), N_e (.H i.castSucc.succ s : Edge (t+3+1) (q+2+1))) + 48 =
        6*((q+2)*2^(t+2)+3*2^(q+2)+2^(i.val+2)+2^(t+1-i.val+2)+
          2*q*((if i.val=0 then 1 else 0)+(if t+1-i.val=0 then 1 else 0))) := by
    have aux (a b : ℕ) {N : ℕ} (hN : N=(a+1)+(b+1))
        (r : Fin (N+1)) (hr : r.val=a+1) (hm : 0<a+b) :
        (∑ s : Fin (q+2), N_e (.H r s : Edge (N+1) (q+2+1))) + 48 =
          6*((q+2)*2^(a+b+1)+3*2^(q+2)+2^(a+2)+2^(b+2)+
            2*q*((if a=0 then 1 else 0)+(if b=0 then 1 else 0))) := by
      subst N
      have he : r=cut_row (a+1) (b+1) := Fin.ext hr
      subst r
      exact interior_row_sum a b q hm
    have hi := i.isLt
    have h := aux i.val (t+1-i.val) (by omega) i.castSucc.succ rfl (by omega)
    have he : i.val+(t+1-i.val)+1=t+2 := by omega
    simpa only [he] using h
  have hsum := congrArg (fun f : Fin (t+2) → ℕ => ∑ i, f i) (funext hrows)
  have hb := boundary_row_sum (t+2) q (by omega)
  have hbottom :
      (∑ s : Fin (q+2), N_e (.H (Fin.last (t+3)) s : Edge (t+3+1) (q+2+1))) =
        ∑ s : Fin (q+2), N_e (.H (0 : Fin (t+3+1)) s) := by
    apply Finset.sum_congr rfl
    intro s _
    simpa using horizontal_count_row_reflect (0 : Fin (t+3+1)) s
  have hg := sum_two_powers (t+2)
  have hr := sum_two_powers_reverse (t+1)
  have hl := sum_left_indicator t
  have hri := sum_right_indicator t
  simp only [pow_add, pow_two] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  rw [hl,hri] at hsum
  unfold N_H
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc (fun i : Fin (t+3) =>
    ∑ s : Fin (q+2), N_e (.H i.succ s : Edge (t+3+1) (q+2+1)))]
  simp only [Fin.succ_last]
  rw [hbottom]
  simp only [pow_succ] at hg hr hb ⊢
  nlinarith

#print axioms BoundaryData
#print axioms BoundaryValid
#print axioms boundary_build
#print axioms boundary_extract
#print axioms boundary_h
#print axioms boundary_slot_equiv
#print axioms BoundaryWords
#print axioms boundary_words_zero_card
#print axioms boundary_words_pos_card
#print axioms NZPair
#print axioms pivot
#print axioms boundary_count_zero
#print axioms boundary_count_pos
#print axioms horizontal_count_row_reflect
#print axioms E
#print axioms boundary_count
#print axioms boundary_count_at
#print axioms boundary_rows_count
#print axioms row_reflect
#print axioms row_reflect_raw
#print axioms row_reflect_equiv
#print axioms boundary_bottom_slot_equiv
#print axioms cut_row
#print axioms InteriorSlots
#print axioms interior_slot_equiv
#print axioms OrdinaryAlphabet
#print axioms InteriorAlphabet
#print axioms interior_count_alphabets
#print axioms interior_count_support
#print axioms lower_pair
#print axioms P
#print axioms Q
#print axioms six_case_value
#print axioms interior_count
#print axioms horizontal_two_rows
#print axioms interior_one_column_count
#print axioms horizontal_two_columns
#print axioms interior_three_rows_count
#print axioms horizontal_three_rows
#print axioms interior_row_sum
#print axioms horizontal_sum

end D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal
