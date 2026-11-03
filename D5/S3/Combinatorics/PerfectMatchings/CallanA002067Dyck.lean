/- GID: D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted Dyck paths satisfy the A002067 recurrence. -/

/-
proof_shape: source_unique, poly_is_source, source_eq_dyck: content (unbounded induction).
escape_witness: source_eq_dyck, through words_polynomial and wordPoly_monomial.
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24743
Direct frozen dependencies:
  D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality.words;
  D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.PrefixNonnegative
  and its Step constructors and instances;
  D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.heightAfter
  statement_id: sha256:8031371a0d6ac25411b4257ddc07ba754959ed555b98db10eedbf8a70c60266f.
The finite-word set and prefix predicate use these owners; the public weights retain
Callan's formulas, with default D for out-of-range step lookup.
-/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import D5.S1.Recurrence.Invariants.SchroederPeakAlternatingQuadraticMoment
import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs
import Mathlib.Combinatorics.Enumerative.DyckWord

open D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs (heightAfter)

/-! Binding definitions for David Callan's two conjectures in OEIS A002067.
The OEIS source has no arXiv version.
The polynomial recurrence and the path weights use natural-number coefficients.
Positions and vertex labels are one-based; empty products are one.
-/

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck

open scoped BigOperators

/-- The NAME recurrence, with its initial term from the source's terms and program.
The source index n >= 1 is written n + 1, so each summand has k <= n. -/
def IsSourceSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ,
    a (n + 1) = ∑ k ∈ Finset.range (n + 1),
      Nat.choose (2 * (n + 1)) (2 * k) * a k * a (n - k)

/-- Prefix height of a Mathlib Dyck word. Its prefix condition ensures that
this natural subtraction agrees with integer height, including empty prefixes. -/
def prefixHeight (p : DyckWord) (j : ℕ) : ℕ :=
  ((p.toList.take j).count DyckStep.U) - ((p.toList.take j).count DyckStep.D)

/-- Product of one-based upstep positions times the heights of their top vertices. -/
def pathWeight (p : DyckWord) : ℕ :=
  ∏ j ∈ (Finset.range p.toList.length).filter
    (fun j => p.toList.getD j DyckStep.D = DyckStep.U),
      (j + 1) * prefixHeight p (j + 1)

private theorem getD_up_iff (p : DyckWord) :
    ∀ j, (p.toList.getD j DyckStep.D = DyckStep.U) ↔ (p.toList[j]? = some DyckStep.U) := by
  intro j
  rw [List.getD_eq_getElem?_getD]
  cases p.toList[j]? <;> simp

/-- The total source weight over every Dyck n-path, including the empty path at n = 0. -/
noncomputable def weightedDyckSum (n : ℕ) : ℕ :=
  ∑ p : {p : DyckWord // p.semilength = n}, pathWeight p.val

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
open scoped BigOperators

theorem source_unique {a b : ℕ → ℕ}
    (ha : IsSourceSequence a) (hb : IsSourceSequence b) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ha.1.trans hb.1.symm
    | succ n =>
      rw [ha.2 n, hb.2 n]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      rw [ih k hk', ih (n - k) (by omega)]

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck

open scoped BigOperators
open Finset Polynomial
namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck

noncomputable def walkPoly : ℕ → Polynomial ℕ
  | 0 => 1
  | n + 1 => (walkPoly n).derivative + C (n + 1) * X * walkPoly n

private theorem truncated_pascal {R : Type*} [CommSemiring R]
    (f : ℕ → R) (hf : f 0 = 1) (n : ℕ) :
    (∑ k ∈ range (n + 2), ((n + 3).choose k : R) * f k * f (n + 1 - k)) =
      (n + 2 : R) * f (n + 1) +
        ∑ k ∈ range (n + 1), ((n + 2).choose k : R) *
          (f (k + 1) * f (n - k) + f k * f (n + 1 - k)) := by
  have hend : (n + 2).choose (n + 1) = n + 2 := by
    exact Nat.choose_succ_self_right (n + 1)
  have hs :
      (∑ k ∈ range (n + 1), ((n + 2).choose (k + 1) : R) * f (k + 1) * f (n - k)) +
        f (n + 1) =
      (∑ k ∈ range (n + 1), ((n + 2).choose k : R) * f k * f (n + 1 - k)) +
        (n + 2 : R) * f (n + 1) := by
    rw [sum_range_succ (f := fun k => ((n + 2).choose (k + 1) : R) *
      f (k + 1) * f (n - k))]
    rw [sum_range_succ' (f := fun k => ((n + 2).choose k : R) *
      f k * f (n + 1 - k))]
    simp only [Nat.sub_self, hf, mul_one, hend, Nat.cast_add,
      Nat.cast_one, Nat.choose_zero_right, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
    ring
  rw [sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, hf, Nat.sub_zero]
  have pascal (k : ℕ) : ((n + 3).choose (k + 1) : R) =
      ((n + 2).choose k : R) + ((n + 2).choose (k + 1) : R) := by
    rw [show n + 3 = (n + 2) + 1 by omega, Nat.choose_succ_succ', Nat.cast_add]
  simp only [pascal, add_mul, sum_add_distrib]
  simp only [Nat.add_sub_add_right]
  calc
    _ = (∑ k ∈ range (n + 1), ((n + 2).choose k : R) * f (k + 1) * f (n - k)) +
        ((∑ k ∈ range (n + 1), ((n + 2).choose (k + 1) : R) *
          f (k + 1) * f (n - k)) + f (n + 1)) := by ring
    _ = _ := by rw [hs]; simp_rw [mul_add, sum_add_distrib]; ring

private theorem derivative_convolution (n : ℕ) :
    (walkPoly (n + 1)).derivative =
      ∑ k ∈ range (n + 1), C ((n + 2).choose k) * walkPoly k * walkPoly (n - k) := by
  induction n with
  | zero => simp [walkPoly]
  | succ n ih =>
    let S : Polynomial ℕ := ∑ k ∈ range (n + 1),
      C ((n + 2).choose k) * walkPoly k * walkPoly (n - k)
    have hs : S.derivative + C (n + 2) * X * S =
        ∑ k ∈ range (n + 1), C ((n + 2).choose k) *
          (walkPoly (k + 1) * walkPoly (n - k) +
            walkPoly k * walkPoly (n + 1 - k)) := by
      dsimp [S]
      rw [derivative_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      have hk' : k ≤ n := mem_range_succ_iff.mp hk
      have hn : n + 1 - k = n - k + 1 := by exact Nat.sub_add_comm hk'
      have hc : C (n + 2) = C (k + 1) + C (n - k + 1) := by
        rw [← C_add]
        congr 1
        omega
      rw [hn, walkPoly, walkPoly]
      simp only [derivative_mul, derivative_C, zero_mul, zero_add]
      rw [hc]
      ring
    have hd : (walkPoly (n + 2)).derivative =
        C (n + 2) * walkPoly (n + 1) +
          (S.derivative + C (n + 2) * X * S) := by
      rw [walkPoly]
      simp only [derivative_add, derivative_mul, derivative_C, derivative_X,
        zero_mul, zero_add, mul_one]
      change (walkPoly (n + 1)).derivative.derivative +
        (C (n + 2) * walkPoly (n + 1) +
          C (n + 2) * X * (walkPoly (n + 1)).derivative) = _
      rw [ih]
      dsimp [S]
      ring
    rw [show n + 1 + 1 = n + 2 by omega, hd, hs]
    have hp := truncated_pascal walkPoly (by rfl) n
    convert hp.symm using 1 <;> simp only [← C_eq_natCast, Nat.cast_id, Nat.add_assoc, C_add, C_ofNat]

private theorem walkPoly_coeff_parity (n k : ℕ) (h : (n + k) % 2 = 1) :
    (walkPoly n).coeff k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => simp [walkPoly, coeff_one]
  | succ n ih =>
    cases k with
    | zero =>
      simp only [walkPoly, coeff_add, coeff_derivative, mul_one,
        mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero]
      simpa only [Nat.zero_add, Nat.cast_zero, zero_add, mul_one] using ih 1 (by omega)
    | succ k =>
      simp only [walkPoly, coeff_add, coeff_derivative, mul_assoc,
        coeff_C_mul, coeff_X_mul]
      rw [ih (k + 1 + 1) (by omega), ih k (by omega)]
      simp

private theorem polyConst_odd (n : ℕ) : (walkPoly (2 * n + 1)).eval 0 = 0 := by
  simpa only [coeff_zero_eq_eval_zero] using walkPoly_coeff_parity (2 * n + 1) 0 (by omega)

private theorem sum_even_only {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (hf : ∀ n, f (2 * n + 1) = 0) (n : ℕ) :
    (∑ k ∈ range (2 * n + 1), f k) = ∑ k ∈ range (n + 1), f (2 * k) := by
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => 2 * a) ?_ ?_ ?_ ?_
  · intro a ha hfa
    exact mem_range.mpr (by have := mem_range.mp ha; omega)
  · intro a ha hfa b hb hfb he
    omega
  · intro b hb hfb
    have heven : b % 2 = 0 := by
      by_contra h
      have hodd : b = 2 * (b / 2) + 1 := by omega
      rw [hodd, hf] at hfb
      exact hfb rfl
    have he : 2 * (b / 2) = b := by omega
    refine ⟨b / 2, mem_range.mpr (by have := mem_range.mp hb; omega), ?_, he⟩
    simpa only [he] using hfb
  · intro a ha hfa
    rfl

private theorem polyConst_convolution (r : ℕ) :
    (walkPoly (r + 2)).eval 0 = ∑ k ∈ range (r + 1),
      (r + 2).choose k * (walkPoly (k)).eval 0 * (walkPoly (r - k)).eval 0 := by
  change (walkPoly (r + 1 + 1)).eval 0 = _
  rw [walkPoly]
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_mul, add_zero]
  rw [derivative_convolution]
  simp only [eval_finsetSum, eval_mul, eval_C]

private theorem polyConst_source_recurrence (n : ℕ) :
    (walkPoly (2 * (n + 1))).eval 0 = ∑ k ∈ range (n + 1),
      (2 * (n + 1)).choose (2 * k) * (walkPoly (2 * k)).eval 0 * (walkPoly (2 * (n - k))).eval 0 := by
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, polyConst_convolution]
  rw [sum_even_only (hf := fun m => by rw [polyConst_odd]; simp)]
  apply sum_congr rfl
  intro k hk
  rw [show 2 * n - 2 * k = 2 * (n - k) by omega]

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
open scoped BigOperators
open Finset

private theorem crossing_factorial (height : ℕ → ℕ) (up : ℕ → Prop) [DecidablePred up]
    (n : ℕ)
    (step : ∀ i < n, if up i then height (i + 1) = height i + 1
      else height i = height (i + 1) + 1) :
    (∏ i ∈ range n, if up i then height (i + 1) else 1) * (height 0).factorial =
      (∏ i ∈ range n, if up i then 1 else height i) * (height n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i hi => step i (by omega))
    have hs := step n (by omega)
    rw [prod_range_succ, prod_range_succ]
    by_cases hu : up n
    · simp only [hu, ite_true] at hs ⊢
      rw [hs, Nat.factorial_succ]
      calc
        _ = ((∏ i ∈ range n, if up i then height (i + 1) else 1) *
          (height 0).factorial) * (height n + 1) := by ring
        _ = _ := by rw [ih']; ring
    · simp only [hu, ite_false] at hs ⊢
      simpa only [mul_one, hs, Nat.factorial_succ, mul_assoc] using ih'

private theorem crossing_products (height : ℕ → ℕ) (up : ℕ → Prop) [DecidablePred up]
    (n : ℕ)
    (step : ∀ i < n, if up i then height (i + 1) = height i + 1
      else height i = height (i + 1) + 1)
    (returns : height n = height 0) :
    (∏ i ∈ range n, if up i then height (i + 1) else 1) =
      ∏ i ∈ range n, if up i then 1 else height i := by
  apply mul_right_cancel₀ (Nat.factorial_ne_zero (height 0))
  simpa only [returns] using crossing_factorial height up n step

private theorem prefixHeight_step (p : DyckWord) (j : ℕ) (hj : j < p.toList.length) :
    if p.toList[j]? = some DyckStep.U then
      prefixHeight p (j + 1) = prefixHeight p j + 1
    else prefixHeight p j = prefixHeight p (j + 1) + 1 := by
  have ht := List.take_succ_eq_append_getElem hj
  have hlookup := List.getElem?_eq_getElem hj
  have h0 := p.count_D_le_count_U j
  have h1 := p.count_D_le_count_U (j + 1)
  rw [ht] at h1
  cases he : p.toList[j] with
  | U =>
    simp [he] at h1
    simp [prefixHeight, ht, hlookup, he]
    omega
  | D =>
    simp [he] at h1
    simp [prefixHeight, ht, hlookup, he]
    omega

private theorem dyck_height_products (p : DyckWord) :
    (∏ j ∈ range p.toList.length,
      if p.toList[j]? = some DyckStep.U then prefixHeight p (j + 1) else 1) =
    ∏ j ∈ range p.toList.length,
      if p.toList[j]? = some DyckStep.U then 1 else prefixHeight p j := by
  apply crossing_products (prefixHeight p) (fun j => p.toList[j]? = some DyckStep.U)
  · exact fun j hj => prefixHeight_step p j hj
  · simp [prefixHeight, p.count_U_eq_count_D]

private theorem pathWeight_downsteps (p : DyckWord) :
    pathWeight p =
      (∏ j ∈ range p.toList.length, if p.toList[j]? = some DyckStep.U then j + 1 else 1) *
      ∏ j ∈ range p.toList.length,
        if p.toList[j]? = some DyckStep.U then 1 else prefixHeight p j := by
  rw [← dyck_height_products p, ← prod_mul_distrib]
  simp only [pathWeight, prod_filter, getD_up_iff]
  apply prod_congr rfl
  intro j hj
  split_ifs <;> simp

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
open scoped BigOperators
open Finset Polynomial

private noncomputable def wordPoly (w : List DyckStep) : Polynomial ℕ :=
  w.reverseRecOn 1 (fun v s q =>
    if s = DyckStep.U then C (v.length + 1) * X * q else q.derivative)

private theorem wordPoly_nil : wordPoly [] = 1 := by simp [wordPoly]

private theorem wordPoly_snoc (w : List DyckStep) (s : DyckStep) :
    wordPoly (w ++ [s]) = if s = DyckStep.U then
      C (w.length + 1) * X * wordPoly w else (wordPoly w).derivative := by
  simp only [wordPoly, List.reverseRecOn_concat]

private instance instFintypeDyckStep : Fintype DyckStep where
  elems := {DyckStep.U, DyckStep.D}
  complete s := by cases s <;> simp

open D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality (words)

private theorem mem_words (r : ℕ) (w : List DyckStep) : w ∈ words r ↔ w.length = r := by
  classical
  unfold words
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property
  · intro h
    exact ⟨⟨w, h⟩, rfl⟩

private theorem words_zero : words (α := DyckStep) 0 = {[]} := by
  exact val_eq_singleton_iff.mp rfl

private theorem words_succ (r : ℕ) : words (α := DyckStep) (r + 1) =
    ((words r).image (fun w => w ++ [DyckStep.U])) ∪
      ((words r).image (fun w => w ++ [DyckStep.D])) := by
  ext w
  rw [mem_words]
  symm
  simp only [mem_union, mem_image]
  constructor
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) <;>
      simp only [List.length_append, List.length_singleton, (mem_words r _).mp hv]
  · intro hw
    rcases List.eq_nil_or_concat' w with rfl | ⟨v, s, rfl⟩
    · simp at hw
    · have hv : v.length = r := by simp only [List.length_append, List.length_singleton] at hw; omega
      cases s with
      | U => exact Or.inl ⟨v, (mem_words r v).mpr hv, rfl⟩
      | D => exact Or.inr ⟨v, (mem_words r v).mpr hv, rfl⟩

private theorem words_disjoint (r : ℕ) :
    Disjoint ((words r).image (fun w => w ++ [DyckStep.U]))
      ((words r).image (fun w => w ++ [DyckStep.D])) := by
  apply disjoint_left.mpr
  intro w hu hd
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hu
  obtain ⟨v, hv, h⟩ := mem_image.mp hd
  have := congrArg List.getLast? h
  simp at this

private theorem words_polynomial (r : ℕ) :
    (∑ w ∈ words r, wordPoly w) = walkPoly r := by
  induction r with
  | zero => simp [words_zero, wordPoly, walkPoly]
  | succ r ih =>
    rw [words_succ, sum_union (words_disjoint r)]
    rw [sum_image (fun a _ b _ hab => List.append_cancel_right hab),
      sum_image (fun a _ b _ hab => List.append_cancel_right hab)]
    simp only [wordPoly_snoc, reduceCtorEq, ↓reduceIte]
    have hsum : (∑ w ∈ words r, C (w.length + 1) * X * wordPoly w) =
        C (r + 1) * X * ∑ w ∈ words r, wordPoly w := by
      rw [mul_sum]
      apply sum_congr rfl
      intro w hw
      rw [(mem_words r w).mp hw]
    rw [hsum, ← derivative_sum, ih, walkPoly]
    ring

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
open scoped BigOperators
open Finset Polynomial
attribute [local instance] Classical.propDecidable

private theorem heightAfter_counts (w : List DyckStep) :
    (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat =
      w.count DyckStep.U - w.count DyckStep.D := by
  symm
  let b : DyckStep → Bool := fun s => decide (s = DyckStep.U)
  have hi : Function.Injective b := by
    intro a c h
    cases a <;> cases c <;> simp_all [b]
  have ht : (w.map b).take w.length = w.map b := by
    simpa only [List.length_map] using (List.take_length (l := w.map b))
  have hu : (w.map b).count true = w.count DyckStep.U := by
    simpa [b] using List.count_map_of_injective w b hi DyckStep.U
  have hd : (w.map b).count false = w.count DyckStep.D := by
    simpa [b] using List.count_map_of_injective w b hi DyckStep.D
  have hc : ((w.map b).map fun q => if q then (1 : ℤ) else -1).sum =
      (w.count DyckStep.U : ℤ) - (w.count DyckStep.D : ℤ) := by
    rw [Finset.sum_list_map_count]
    have he : (∑ q ∈ (w.map b).toFinset,
        (w.map b).count q • (if q then (1 : ℤ) else -1)) =
        ∑ q : Bool, (w.map b).count q • (if q then (1 : ℤ) else -1) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro q _ hq
      have hn : q ∉ w.map b := by simpa only [List.mem_toFinset] using hq
      simp [List.count_eq_zero_of_not_mem hn]
    rw [he, Fintype.sum_bool]
    simp [hu, hd, sub_eq_add_neg]
  change w.count DyckStep.U - w.count DyckStep.D = (heightAfter (w.map b) w.length).toNat
  unfold heightAfter
  rw [ht, hc]
  omega

private def schroederStep : DyckStep →
    D5.S1.Recurrence.Invariants.SchroederPeakAlternatingQuadraticMoment.Step
  | .U => .U
  | .D => .D

open D5.S1.Recurrence.Invariants.SchroederPeakAlternatingQuadraticMoment (PrefixNonnegative)

private theorem prefixNonnegative_iff (w : List DyckStep) :
    PrefixNonnegative (w.map schroederStep) ↔
      ∀ j : ℕ, (w.take j).count DyckStep.D ≤ (w.take j).count DyckStep.U := by
  have hi : Function.Injective schroederStep := by
    intro a b h
    cases a <;> cases b <;> simp_all [schroederStep]
  unfold PrefixNonnegative
  simp only [← List.map_take]
  change (∀ j, ((w.take j).map schroederStep).count (schroederStep DyckStep.D) ≤
    ((w.take j).map schroederStep).count (schroederStep DyckStep.U)) ↔ _
  apply forall_congr'
  intro j
  rw [List.count_map_of_injective (w.take j) schroederStep hi DyckStep.D,
    List.count_map_of_injective (w.take j) schroederStep hi DyckStep.U]

private def wordWeight (w : List DyckStep) : ℕ :=
  ∏ j ∈ range w.length, if w[j]? = some DyckStep.U then j + 1 else (heightAfter ((w.take j).map fun s => decide (s = DyckStep.U)) (w.take j).length).toNat

private theorem nonnegative_prefix (w v : List DyckStep) (h : PrefixNonnegative ((w ++ v).map schroederStep)) :
    PrefixNonnegative (w.map schroederStep) := by
  rw [prefixNonnegative_iff] at h ⊢
  intro j
  have hm : min j w.length - w.length = 0 := by omega
  have ht : (w ++ v).take (min j w.length) = w.take j := by
    rw [List.take_append, hm, List.take_zero, List.append_nil]
    simpa only [List.take_length] using (List.take_take (i := j) (j := w.length) (l := w)).symm
  simpa only [ht] using h (min j w.length)

private theorem nonnegative_snoc (w : List DyckStep) (s : DyckStep) :
    PrefixNonnegative ((w ++ [s]).map schroederStep) ↔ PrefixNonnegative (w.map schroederStep) ∧ (s = DyckStep.U ∨ 0 < (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat) := by
  constructor
  · intro h
    refine ⟨nonnegative_prefix w [s] h, ?_⟩
    cases s with
    | U => exact Or.inl rfl
    | D =>
      right
      have ht := (prefixNonnegative_iff _).mp h (w.length + 1)
      have hlen : (w ++ [DyckStep.D]).length = w.length + 1 := by simp
      rw [← hlen, List.take_length] at ht
      simp at ht
      simp only [heightAfter_counts]
      omega
  · rintro ⟨hw, hs⟩
    apply (prefixNonnegative_iff _).mpr
    intro j
    by_cases hj : j ≤ w.length
    · have ht : (w ++ [s]).take j = w.take j := by
        exact List.take_append_of_le_length hj
      simpa only [ht] using (prefixNonnegative_iff _).mp hw j
    · have hj' : (w ++ [s]).length ≤ j := by simp; omega
      rw [List.take_of_length_le hj']
      have ht := (prefixNonnegative_iff _).mp hw w.length
      simp only [List.take_length] at ht
      cases s with
      | U => simp; omega
      | D =>
        simp only [reduceCtorEq, false_or] at hs
        simp only [heightAfter_counts] at hs
        simp
        omega

private theorem wordWeight_snoc (w : List DyckStep) (s : DyckStep) :
    wordWeight (w ++ [s]) = wordWeight w *
      (if s = DyckStep.U then w.length + 1 else (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat) := by
  unfold wordWeight
  simp only [List.length_append, List.length_singleton]
  rw [prod_range_succ]
  have ht : (w ++ [s]).take w.length = w := by exact List.take_left
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.some.injEq, ht]
  congr 1
  apply prod_congr rfl
  intro j hj
  have hj' : j < w.length := mem_range.mp hj
  rw [List.getElem?_append_left hj']
  rw [List.take_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hj'),
    List.take_zero, List.append_nil]

private theorem wordPoly_monomial (w : List DyckStep) :
    wordPoly w = if PrefixNonnegative (w.map schroederStep) then C (wordWeight w) * X ^ (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat else 0 := by
  classical
  induction w using List.reverseRecOn with
  | nil =>
    simp only [heightAfter_counts]
    simp [wordPoly_nil, PrefixNonnegative, wordWeight]
  | append_singleton w s ih =>
    rw [wordPoly_snoc, wordWeight_snoc]
    by_cases hw : PrefixNonnegative (w.map schroederStep)
    · have ht := (prefixNonnegative_iff _).mp hw w.length
      simp only [List.take_length] at ht
      rw [if_pos hw] at ih
      cases s with
      | U =>
        have hh : (heightAfter ((w ++ [DyckStep.U]).map fun s => decide (s = DyckStep.U)) (w ++ [DyckStep.U]).length).toNat = (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat + 1 := by
          simp only [heightAfter_counts] at *
          simp
          omega
        simp only [nonnegative_snoc, hw, true_and, true_or, ↓reduceIte]
        rw [ih, hh, C_mul, pow_succ]
        ring
      | D =>
        by_cases hh : 0 < (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat
        · have he : (heightAfter ((w ++ [DyckStep.D]).map fun s => decide (s = DyckStep.U)) (w ++ [DyckStep.D]).length).toNat = (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat - 1 := by
            simp only [heightAfter_counts] at *
            simp
            omega
          simp only [nonnegative_snoc, hw, hh, true_and, or_true, ↓reduceIte]
          rw [ih, derivative_C_mul_X_pow, he]
          simp
        · have he : (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat = 0 := by exact Nat.eq_zero_of_not_pos hh
          simp [nonnegative_snoc, hw, hh, ih, he]
    · have he : ¬ PrefixNonnegative ((w ++ [s]).map schroederStep) := by
        intro h
        exact hw (nonnegative_prefix w [s] h)
      simp [hw] at ih
      rw [if_neg he]
      simp [ih]

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
open scoped BigOperators
open Finset Polynomial
attribute [local instance] Classical.propDecidable

open D5.S1.Recurrence.Invariants.SchroederPeakAlternatingQuadraticMoment (PrefixNonnegative)

private def returning (w : List DyckStep) : Prop := PrefixNonnegative (w.map schroederStep) ∧ (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat = 0

open D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality (words)

private noncomputable def returningWords (n : ℕ) : Finset (List DyckStep) := by
  classical
  exact (words (2 * n)).filter returning

private theorem wordWeight_dyck (p : DyckWord) : wordWeight p.toList = pathWeight p := by
  rw [pathWeight_downsteps, wordWeight, ← prod_mul_distrib]
  simp only [heightAfter_counts]
  apply prod_congr rfl
  intro j hj
  by_cases h : p.toList[j]? = some DyckStep.U <;> simp [h, prefixHeight]

private theorem wordPoly_eval_zero (w : List DyckStep) :
    (wordPoly w).eval 0 = if returning w then wordWeight w else 0 := by
  classical
  by_cases hw : PrefixNonnegative (w.map schroederStep) <;> by_cases hh : (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat = 0 <;>
    simp [wordPoly_monomial, returning, hw, hh]

private theorem polyConst_returns (n : ℕ) :
    (walkPoly (2 * n)).eval 0 = ∑ w ∈ returningWords n, wordWeight w := by
  classical
  rw [← words_polynomial, eval_finsetSum]
  simp only [wordPoly_eval_zero, returningWords, sum_filter]

private noncomputable def returnWord (n : ℕ) (w : List DyckStep) (hw : w ∈ returningWords n) :
    {p : DyckWord // p.semilength = n} := by
  classical
  have hm := mem_filter.mp hw
  have hn : PrefixNonnegative (w.map schroederStep) := hm.2.1
  have hz : (heightAfter (w.map fun s => decide (s = DyckStep.U)) w.length).toNat = 0 := hm.2.2
  have ht := (prefixNonnegative_iff _).mp hn w.length
  simp only [List.take_length] at ht
  have hc : w.count DyckStep.U = w.count DyckStep.D := by
    simp only [heightAfter_counts] at hz
    omega
  let p : DyckWord := ⟨w, hc, (prefixNonnegative_iff _).mp hn⟩
  refine ⟨p, ?_⟩
  have hl : w.length = 2 * n := (mem_words (2 * n) w).mp hm.1
  have hp := p.two_mul_semilength_eq_length
  change 2 * p.semilength = w.length at hp
  omega

private theorem weightedDyckSum_returns (n : ℕ) :
    weightedDyckSum n = ∑ w ∈ returningWords n, wordWeight w := by
  classical
  unfold weightedDyckSum
  symm
  refine sum_bij (fun w hw => returnWord n w hw) ?_ ?_ ?_ ?_
  · intro w hw
    exact mem_univ _
  · intro w hw v hv h
    exact congrArg (fun p => p.val.toList) h
  · intro p hp
    have hm : p.val.toList ∈ returningWords n := by
      apply mem_filter.mpr
      refine ⟨(mem_words (2 * n) p.val.toList).mpr ?_, (prefixNonnegative_iff _).mpr p.val.count_D_le_count_U, ?_⟩
      · have h := p.val.two_mul_semilength_eq_length
        rw [p.property] at h
        exact h.symm
      · simp [heightAfter_counts, p.val.count_U_eq_count_D]
    refine ⟨p.val.toList, hm, ?_⟩
    apply Subtype.ext
    apply DyckWord.ext
    rfl
  · intro w hw
    exact wordWeight_dyck (returnWord n w hw).val

private theorem polyConst_dyck (n : ℕ) : (walkPoly (2 * n)).eval 0 = weightedDyckSum n :=
  (polyConst_returns n).trans (weightedDyckSum_returns n).symm

theorem poly_is_source : IsSourceSequence (fun n => (walkPoly (2 * n)).eval 0) := by
  refine ⟨?_, polyConst_source_recurrence⟩
  simp [walkPoly]

theorem source_eq_dyck (a : ℕ → ℕ) (ha : IsSourceSequence a) (n : ℕ) :
    a n = weightedDyckSum n := by
  have he := source_unique ha poly_is_source
  exact (congrFun he n).trans (polyConst_dyck n)

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
