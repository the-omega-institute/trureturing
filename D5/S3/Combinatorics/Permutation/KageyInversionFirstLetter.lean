/- GID: D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/KageyInversionFirstLetter
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The first-letter weighted inversion count equals the next Mahonian count for k < n. -/

/-
admission_basis: open-problem-resolution (#19726; Proved)
result: proof_shape: content; escape_witness: weighted_identity.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20067.
Direct frozen dependencies: D5/S1/Digit/Carry/ListInversions.inv
  statement_id: sha256:746f5581415a1e255341cd9dd423347ba85b2d2e1a58842f35a43f09f4f536e8.
D5/S1/Digit/Carry/ListInversions.inv.eq_2
  statement_id: sha256:69bd830643f87954c28a04707b099a28d9d83eac89456836918b87d6b9c61b21.
D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord.word (Lean PSW.word)
  statement_id: sha256:529b4e417178afa62800d8f33994ccf71231d25a506249de5b2d92421d0817cd.
The source's one-line notation is PSW.word, whose body is exactly List.ofFn
(fun i => (π i).val + 1). Its inversion statistic is ListInversions.inv (PSW.word π).
E retains the source's sum-over-cardinality expression; result uses Finset.expect
through the private E_eq_expect correspondence.
Public definitions (proof_shape: bind-only, as definitional encodings):
  M: consumers: E, claim, result.
  E: consumers: claim, result.
  claim: consumer: result.
Private theorem classifications:
  count_ofFn: bind-only; consumers: inv_ofFn_congr, inv_decompose.
  inv_ofFn_congr: content; escape_witness: inv_ofFn_congr; consumer: inv_decompose.
  inv_decompose: content; escape_witness: inv_ofFn_congr; consumers: M_decompose, weighted_decompose, double_decompose.
  M_decompose: content; escape_witness: inv_decompose; consumer: double_decompose.
  weighted_decompose: content; escape_witness: inv_decompose; consumer: weighted_identity.
  double_decompose: content; escape_witness: inv_decompose; consumer: weighted_identity.
  sum_digit: bind-only; consumer: rectangle_count.
  sum_unit_digit: bind-only; consumer: rectangle_count.
  rectangle_count: bind-only; consumer: weighted_identity.
  weighted_identity: content; escape_witness: inv_decompose; consumer: result.
  E_eq_expect: bind-only; consumer: result.
utility none: no standalone computational certificate or bounded enumeration is
introduced; the universal argument is structural, including its length-one case.
-/


import D5.S1.Digit.Carry.ListInversions
import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsWord
import Mathlib.Algebra.BigOperators.Expect

namespace D5.S3.Combinatorics.Permutation.KageyInversionFirstLetter

open D5.S1.Digit.Carry.ListInversions (inv)

/-- `M(n, k) = #{w ∈ S_n : inv(w) = k}`. -/
def M (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun π : Equiv.Perm (Fin n) => inv (PSW.word π) = k).card

/-- `E[π(1) | π ∈ S_n, inv(π) = k]`: the mean first letter over the permutations with `k` inversions. -/
def E (n k : ℕ) : ℚ :=
  (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => inv (PSW.word π) = k), ((PSW.word π).headD 0 : ℚ)) / (M n k : ℚ)

/-- Conjecture 5.1. -/
def claim : Prop :=
  ∀ k n : ℕ, k < n → E n k = (M (n + 1) k : ℚ) / (M n k : ℚ)

end D5.S3.Combinatorics.Permutation.KageyInversionFirstLetter

namespace D5.S3.Combinatorics.Permutation.KageyInversionFirstLetter
open scoped BigOperators
open D5.S1.Digit.Carry.ListInversions (inv)

private theorem count_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).countP p = ∑ i : Fin n, if p (f i) then 1 else 0 := by
  simpa [Function.comp_def, List.map_ofFn, List.sum_ofFn] using
    (List.countP_flatMap (p := p) (l := List.ofFn f) (f := fun a => [a]))

private theorem inv_ofFn_congr {n : ℕ} (f g : Fin n → ℕ)
    (h : ∀ a b, f a < f b ↔ g a < g b) :
    inv (List.ofFn f) = inv (List.ofFn g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, inv, inv,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun a b => h a.succ b.succ),
      count_ofFn, count_ofFn]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [decide_eq_true_eq, h]

private theorem inv_decompose {n : ℕ} (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    inv (PSW.word (Equiv.Perm.decomposeFin'Symm i σ)) = inv (PSW.word σ) + i.val := by
  classical
  unfold PSW.word
  rw [List.ofFn_succ, inv]
  have htail :
      inv (List.ofFn (fun j => (Equiv.Perm.decomposeFin'Symm i σ j.succ).val + 1)) =
      inv (List.ofFn (fun j => (σ j).val + 1)) := by
    apply inv_ofFn_congr
    intro a b
    simp only [Equiv.Perm.decomposeFin'Symm_succ, Nat.add_lt_add_iff_right,
      ← Fin.lt_def, Fin.succAbove_lt_succAbove_iff]
  rw [htail]
  congr 1
  rw [count_ofFn]
  simp only [Equiv.Perm.decomposeFin'Symm_succ, Equiv.Perm.decomposeFin'Symm_zero,
    decide_eq_true_eq, Nat.add_lt_add_iff_right, ← Fin.lt_def,
    Fin.succAbove_lt_iff_castSucc_lt]
  rw [Equiv.sum_comp σ (fun j : Fin (n + 1) => if j.castSucc < i then 1 else 0)]
  change (∑ j : Fin (n + 1), if j.val < i.val then 1 else 0) = i.val
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < i.val then 1 else 0)]
  have hi : i.val ≤ n + 1 := Fin.is_le i
  rw [show (∑ j ∈ Finset.range (n + 1), if j < i.val then 1 else 0) =
      (Finset.range i.val).card by
    rw [← Finset.sum_filter]
    have hf : (Finset.range (n + 1)).filter (fun j => j < i.val) = Finset.range i.val := by
      simpa only [Nat.Iio_eq_range, min_eq_right hi] using
        (Finset.Iio_filter_lt (n + 1) i.val)
    rw [hf]
    simp]
  simp

private theorem M_decompose (n k : ℕ) :
    M (n + 2) k = ∑ i : Fin (n + 2), ∑ σ : Equiv.Perm (Fin (n + 1)),
      if inv (PSW.word σ) + i.val = k then 1 else 0 := by
  classical
  unfold M
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Equiv.Perm.decomposeFin'.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin'_symm, inv_decompose]

private theorem weighted_decompose (n k : ℕ) :
    (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin (n + 2)) => inv (PSW.word π) = k),
      (PSW.word π).headD 0) =
    ∑ i : Fin (n + 2), ∑ σ : Equiv.Perm (Fin (n + 1)),
      if inv (PSW.word σ) + i.val = k then i.val + 1 else 0 := by
  classical
  rw [Finset.sum_filter]
  rw [← Equiv.Perm.decomposeFin'.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin'_symm, inv_decompose]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [PSW.word, List.ofFn_succ, List.headD_cons,
    Equiv.Perm.decomposeFin'Symm_zero]

private theorem double_decompose (n k : ℕ) :
    M (n + 3) k =
      ∑ a : Fin (n + 3), ∑ b : Fin (n + 2), ∑ σ : Equiv.Perm (Fin (n + 1)),
        if inv (PSW.word σ) + b.val + a.val = k then 1 else 0 := by
  classical
  rw [M_decompose (n + 1) k]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Equiv.Perm.decomposeFin'.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin'_symm, inv_decompose]

private theorem sum_digit {N q k : ℕ} (hk : k < N) :
    (∑ b : Fin N, if q + b.val = k then b.val + 1 else 0) =
      if q ≤ k then k - q + 1 else 0 := by
  classical
  by_cases hq : q ≤ k
  · rw [ite_eq_left hq]
    let b : Fin N := ⟨k - q, by omega⟩
    rw [Finset.sum_eq_single b]
    · simp [b, Nat.add_sub_of_le hq]
    · intro c hc hcb
      rw [ite_eq_right]
      intro h
      apply hcb
      apply Fin.ext
      dsimp [b]
      omega
    · simp
  · rw [ite_eq_right hq]
    apply Finset.sum_eq_zero
    intro b hb
    rw [ite_eq_right (by omega)]

private theorem sum_unit_digit {N q k : ℕ} (hk : k < N) :
    (∑ b : Fin N, if q + b.val = k then 1 else 0) =
      if q ≤ k then 1 else 0 := by
  classical
  by_cases hq : q ≤ k
  · rw [ite_eq_left hq]
    let b : Fin N := ⟨k - q, by omega⟩
    rw [Finset.sum_eq_single b]
    · simp [b, Nat.add_sub_of_le hq]
    · intro c hc hcb
      rw [ite_eq_right]
      intro h
      apply hcb
      apply Fin.ext
      dsimp [b]
      omega
    · simp
  · rw [ite_eq_right hq]
    apply Finset.sum_eq_zero
    intro b hb
    rw [ite_eq_right (by omega)]

private theorem rectangle_count {N q k : ℕ} (hk : k < N) :
    (∑ a : Fin (N + 1), ∑ b : Fin N,
        if q + b.val + a.val = k then 1 else 0) =
      ∑ b : Fin N, if q + b.val = k then b.val + 1 else 0 := by
  classical
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext b
    rw [sum_unit_digit (by omega : k < N + 1)]
  rw [sum_digit hk]
  by_cases hq : q ≤ k
  · rw [ite_eq_left hq]
    rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => if q + b ≤ k then 1 else 0)]
    have hf : (Finset.range N).filter (fun b => q + b ≤ k) =
        Finset.range (k - q + 1) := by
      have hbound : k - q + 1 ≤ N := by omega
      simpa only [Nat.Iio_eq_range, min_eq_right hbound, Nat.lt_succ_iff,
        Nat.le_sub_iff_add_le hq, Nat.add_comm] using
        (Finset.Iio_filter_lt N (k - q + 1))
    rw [← Finset.sum_filter, hf]
    simp
  · rw [ite_eq_right hq]
    apply Finset.sum_eq_zero
    intro b hb
    rw [ite_eq_right (by omega)]

private theorem weighted_identity (k n : ℕ) (hk : k < n) :
    (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => inv (PSW.word π) = k),
      (PSW.word π).headD 0) = M (n + 1) k := by
  classical
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      have hk0 : k = 0 := Nat.lt_one_iff.mp hk
      subst k
      decide
    | succ n =>
      rw [weighted_decompose n k, double_decompose n k]
      conv_lhs => rw [Finset.sum_comm]
      conv_rhs =>
        arg 2
        ext a
        rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ hσ
      exact (rectangle_count hk).symm

private theorem E_eq_expect (n k : ℕ) : E n k =
    Finset.expect (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => inv (PSW.word π) = k))
      (fun π => ((PSW.word π).headD 0 : ℚ)) := by
  simpa only [E, M] using
    (Finset.expect_eq_sum_div_card
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => inv (PSW.word π) = k))
      (fun π => ((PSW.word π).headD 0 : ℚ))).symm

theorem result : claim := by
  intro k n hk
  rw [E_eq_expect, Finset.expect_eq_sum_div_card]
  congr 1
  rw [← Nat.cast_sum]
  exact congrArg (fun m : ℕ => (m : ℚ)) (weighted_identity k n hk)

end D5.S3.Combinatorics.Permutation.KageyInversionFirstLetter
