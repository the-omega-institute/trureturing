/- GID: D5/S3/Quantum/Schatten/WordTraceExponentBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/WordTraceExponentBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint diagonal word-trace witnesses and their common trace normalization. -/

import D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation
import D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Joint diagonal realizations retain the common coordinate labels in every assertion. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Observer.Hankel.WordHankelRealization (wordProduct)
open D5.S3.Quantum.Schatten.FractionalSchattenAlignmentRefutation (word_diagonal norm_diagonal)
open D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal

namespace D5.S3.Quantum.Schatten.WordTraceExponentBoundary

/-- Subsets name the actual shared coordinates, rather than four independent spectra. -/
def coordinates (q : ℕ) : Fin (2 ^ q) ≃ Finset (Fin q) :=
  Fintype.equivOfCardEq (by simp)

private lemma sum_coordinates (q : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin (2 ^ q), f ((coordinates q i).card)) =
      ∑ a ∈ range (q + 1), (q.choose a : ℝ) * f a := by
  rw [(coordinates q).sum_comp (fun S => f S.card)]
  simpa only [powerset_univ, card_univ, Fintype.card_fin, nsmul_eq_mul] using
    (sum_powerset_apply_card f (x := (univ : Finset (Fin q))))

/-- The mark is one on the positive part of the q-th difference. -/
def mark (q a : ℕ) : ℝ := if Even (q - a) then 1 else 0

private lemma mark_cases (q a : ℕ) : mark q a = 0 ∨ mark q a = 1 := by
  unfold mark
  split_ifs <;> simp

private lemma mark_sign (q a : ℕ) : 2 * mark q a - 1 = (-1 : ℝ) ^ (q - a) := by
  rw [neg_one_pow_eq_ite]
  unfold mark
  split_ifs <;> norm_num

private lemma signed_sum (q : ℕ) (u : ℝ) (f : ℝ → ℝ) :
    (∑ a ∈ range (q + 1), (q.choose a : ℝ) * (2 * mark q a - 1) * f (u + a)) =
      (fwdDiff 1)^[q] f u := by
  rw [fwdDiff_iter_eq_sum_shift]
  apply sum_congr rfl
  intro a ha
  rw [mark_sign]
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast]
  ring

/-- Source entries, with j = a + epsilon and therefore j - epsilon = a. -/
def higherDiagonal (q : ℕ) (u c : ℝ) (b : Bool) (i : Fin (2 ^ q)) : ℝ :=
  if b then c + mark q ((coordinates q i).card) else u + (coordinates q i).card

def higherOtherDiagonal (q : ℕ) (u c : ℝ) (b : Bool) (i : Fin (2 ^ q)) : ℝ :=
  if b then c + 1 - mark q ((coordinates q i).card) else u + (coordinates q i).card

private lemma real_word_trace {n : ℕ} (d : Bool → Fin n → ℝ) (s : List Bool) :
    (wordProduct (fun b => diagonal (fun i => (d b i : ℂ))) s).trace =
      ((∑ i, d false i ^ s.count false * d true i ^ s.count true : ℝ) : ℂ) := by
  have hd : (fun b => diagonal (fun i => (d b i : ℂ))) =
      (fun b : Bool => if b then diagonal (fun i => (d true i : ℂ)) else
        diagonal (fun i => (d false i : ℂ))) := by
    funext b
    cases b <;> rfl
  rw [hd, word_diagonal, trace_diagonal]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]

private lemma higher_word_difference (q : ℕ) (u c : ℝ) (s : List Bool) :
    (wordProduct (fun b => diagonal (fun i => (higherDiagonal q u c b i : ℂ))) s).trace -
      (wordProduct (fun b => diagonal (fun i => (higherOtherDiagonal q u c b i : ℂ))) s).trace =
      ((((c + 1) ^ s.count true - c ^ s.count true) *
        (fwdDiff 1)^[q] (fun x : ℝ => x ^ s.count false) u : ℝ) : ℂ) := by
  rw [real_word_trace, real_word_trace, ← Complex.ofReal_sub]
  congr 1
  simp only [higherDiagonal, higherOtherDiagonal, Bool.false_eq_true, reduceIte]
  rw [sum_coordinates q (fun a => (u + a) ^ s.count false * (c + mark q a) ^ s.count true),
    sum_coordinates q (fun a => (u + a) ^ s.count false * (c + 1 - mark q a) ^ s.count true),
    ← sum_sub_distrib]
  rw [← signed_sum, mul_sum]
  apply sum_congr rfl
  intro a ha
  rcases mark_cases q a with h | h
  · rw [h]
    simp only [add_zero, sub_zero]
    ring
  · rw [h]
    ring

private lemma higher_sum_difference (q : ℕ) (u c : ℝ) (f : ℝ → ℝ) :
    (∑ i : Fin (2 ^ q), f (higherDiagonal q u c false i + higherDiagonal q u c true i)) -
      (∑ i : Fin (2 ^ q), f (higherOtherDiagonal q u c false i + higherOtherDiagonal q u c true i)) =
      (fwdDiff 1)^[q + 1] f (u + c) := by
  simp only [higherDiagonal, higherOtherDiagonal, Bool.false_eq_true, reduceIte]
  rw [sum_coordinates q (fun a => f (u + a + (c + mark q a))),
    sum_coordinates q (fun a => f (u + a + (c + 1 - mark q a))),
    ← sum_sub_distrib, Function.iterate_succ_apply, ← signed_sum]
  apply sum_congr rfl
  intro a ha
  rcases mark_cases q a with h | h <;>
    simp only [h, add_zero, sub_zero, add_sub_cancel_right, fwdDiff,
      add_assoc, add_left_comm, add_comm] <;> ring

private lemma power_smooth (p : ℝ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (iteratedDeriv n (fun y : ℝ => y ^ p)) x := by
  have he : iteratedDeriv n (fun y : ℝ => y ^ p) =
      fun y : ℝ => (descPochhammer ℝ n).eval p * y ^ (p - n) := by
    funext y
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  rw [he]
  exact ((Real.hasDerivAt_rpow_const (p := p - n) (Or.inl hx.ne')).const_mul _).differentiableAt

private lemma power_difference_negative (q : ℕ) (hq : 1 ≤ q) (p x : ℝ)
    (hx : 0 < x) (hp : (q : ℝ) - 1 < p) (hp' : p < q) :
    (fwdDiff 1)^[q + 1] (fun y : ℝ => y ^ p) x < 0 := by
  obtain ⟨y, hy, he⟩ := exists_fwd_diff_iter_eq_iterated_deriv
    (fun y : ℝ => y ^ p) (q + 1) (x := x) (by norm_num : (0 : ℝ) < 1)
    (fun n _ y hy => power_smooth p n y (lt_of_lt_of_le hx hy.1))
  rw [he, one_pow, one_mul, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const,
    descPochhammer_eval_eq_prod_range, prod_range_succ]
  have hprod : 0 < ∏ a ∈ range q, (p - a) := by
    apply prod_pos
    intro a ha
    have ha' : (a : ℝ) ≤ (q : ℝ) - 1 := by
      have : a + 1 ≤ q := mem_range.mp ha
      have ht : (a : ℝ) + 1 ≤ q := by exact_mod_cast this
      linarith
    linarith
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hprod (sub_neg.mpr hp'))
    (Real.rpow_pos_of_pos (lt_of_lt_of_le hx hy.1) _)

private lemma nat_power_difference_nonnegative (q m : ℕ) (u : ℝ) (hu : 0 < u) :
    0 ≤ (fwdDiff 1)^[q] (fun y : ℝ => y ^ m) u := by
  by_cases hmq : m < q
  · have h := congr_fun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hmq) u
    simpa only [Pi.zero_apply, h] using (le_refl (0 : ℝ))
  · have hqm : q ≤ m := Nat.le_of_not_gt hmq
    have hn (y : ℝ) : y ^ m = y ^ (m : ℝ) := (Real.rpow_natCast y m).symm
    simp_rw [hn]
    obtain ⟨y, hy, he⟩ := exists_fwd_diff_iter_eq_iterated_deriv
      (fun y : ℝ => y ^ (m : ℝ)) q (x := u) (by norm_num : (0 : ℝ) < 1)
      (fun n _ y hy => power_smooth m n y (lt_of_lt_of_le hu hy.1))
    rw [he, one_pow, one_mul, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const,
      descPochhammer_eval_eq_prod_range]
    apply mul_nonneg _ (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hu hy.1)) _)
    apply prod_nonneg
    intro a ha
    have : a ≤ m := le_trans (Nat.le_of_lt (mem_range.mp ha)) hqm
    exact sub_nonneg.mpr (by exact_mod_cast this)

private lemma first_power_difference_negative (p : ℝ) (hp : 1 < p) (hp' : p < 2) :
    2 * (3 : ℝ) ^ p + 6 ^ p - 2 ^ p - 2 * 5 ^ p < 0 := by
  have h₂ := power_difference_negative 2 (by omega) p 2 (by norm_num) (by norm_num; exact hp) hp'
  have h₃ := power_difference_negative 2 (by omega) p 3 (by norm_num) (by norm_num; exact hp) hp'
  norm_num [Function.iterate_succ_apply', fwdDiff] at h₂ h₃
  linarith

private lemma mark_sum (q : ℕ) (hq : 0 < q) :
    (∑ i : Fin (2 ^ q), mark q ((coordinates q i).card)) = (2 : ℝ) ^ q / 2 := by
  have hz := congr_fun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) (j := 0) hq) 0
  have hs := signed_sum q 0 (fun _ : ℝ => 1)
  simp only [pow_zero, Pi.zero_apply] at hz
  have hs' : (∑ i : Fin (2 ^ q), (2 * mark q ((coordinates q i).card) - 1)) = 0 := by
    rw [sum_coordinates q (fun a => 2 * mark q a - 1)]
    simpa using hs.trans hz
  simp only [sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at hs'
  linarith

private lemma mark_card_balance (q : ℕ) (hq : 0 < q) :
    (univ.filter (fun i : Fin (2 ^ q) => Even (q - (coordinates q i).card))).card =
      (univ.filter (fun i : Fin (2 ^ q) => ¬ Even (q - (coordinates q i).card))).card := by
  have ht := mark_sum q hq
  have hp : (∑ i : Fin (2 ^ q), mark q ((coordinates q i).card)) =
      ((univ.filter (fun i : Fin (2 ^ q) => Even (q - (coordinates q i).card))).card : ℝ) := by
    simp [mark, sum_ite]
  have hn : (∑ i : Fin (2 ^ q), (1 - mark q ((coordinates q i).card))) =
      ((univ.filter (fun i : Fin (2 ^ q) => ¬ Even (q - (coordinates q i).card))).card : ℝ) := by
    simp only [mark]
    simp_rw [sub_ite, sub_self, sub_zero]
    simp [sum_ite]
  have htotal : (∑ i : Fin (2 ^ q), (1 - mark q ((coordinates q i).card))) =
      (2 : ℝ) ^ q - ∑ i : Fin (2 ^ q), mark q ((coordinates q i).card) := by
    simp [sum_sub_distrib]
  exact_mod_cast (show ((univ.filter (fun i : Fin (2 ^ q) => Even (q - (coordinates q i).card))).card : ℝ) =
      ((univ.filter (fun i : Fin (2 ^ q) => ¬ Even (q - (coordinates q i).card))).card : ℝ) by
    rw [← hp, ← hn, htotal, ht]; ring)

private lemma higher_spectra_products (q : ℕ) (hq : 0 < q) (u c : ℝ)
    (f : ℝ → Polynomial ℂ) (b : Bool) :
    (∏ i : Fin (2 ^ q), f (higherDiagonal q u c b i)) =
      ∏ i : Fin (2 ^ q), f (higherOtherDiagonal q u c b i) := by
  cases b
  · rfl
  · simp only [higherDiagonal, higherOtherDiagonal, reduceIte, mark]
    simp only [add_ite, add_zero, sub_ite, sub_zero, add_sub_cancel_right, apply_ite]
    rw [prod_ite, prod_ite]
    simp only [prod_const]
    rw [mark_card_balance q hq]
    exact mul_comm _ _

private lemma coordinate_card_sum (q : ℕ) (hq : 0 < q) :
    (∑ i : Fin (2 ^ q), ((coordinates q i).card : ℝ)) = (q : ℝ) * (2 : ℝ) ^ q / 2 := by
  rw [sum_coordinates q (fun a => (a : ℝ))]
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.sum_range_mul_choose q)
  push_cast at h
  have ht : (2 : ℝ) ^ q = 2 * 2 ^ (q - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hq]
  simp_rw [mul_comm (q.choose _ : ℝ)]
  rw [h, ht]
  ring

private lemma higher_traces (q : ℕ) (hq : 0 < q) (u c : ℝ)
    (hc : u + (q : ℝ) / 2 = c + 1 / 2) (b : Bool) :
    (∑ i : Fin (2 ^ q), higherDiagonal q u c b i) = (c + 1 / 2) * (2 : ℝ) ^ q ∧
    (∑ i : Fin (2 ^ q), higherOtherDiagonal q u c b i) = (c + 1 / 2) * (2 : ℝ) ^ q := by
  cases b <;>
    simp only [higherDiagonal, higherOtherDiagonal, Bool.false_eq_true, reduceIte,
      sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, coordinate_card_sum q hq, mark_sum q hq]
  · have he := congrArg (fun z : ℝ => z * (2 : ℝ) ^ q) hc
    constructor <;> nlinarith only [he]
  · constructor <;> ring

/-- The scalar data all belong to the same two diagonal pairs. -/
structure DiagonalRelations (n k : ℕ) (a b : Bool → Fin n → ℝ) (T : ℝ) : Prop where
  positive_a : ∀ j i, 0 < a j i
  positive_b : ∀ j i, 0 < b j i
  spectra : ∀ (f : ℝ → Polynomial ℂ) j, (∏ i, f (a j i)) = ∏ i, f (b j i)
  words : ∀ m l : ℕ, (∑ i, b false i ^ m * b true i ^ l) ≤ ∑ i, a false i ^ m * a true i ^ l
  moments : ∀ l : ℕ, 1 ≤ l → l ≤ k + 1 →
    (∑ i, (a false i + a true i) ^ l) = ∑ i, (b false i + b true i) ^ l
  powers : ∀ p : ℝ, (k : ℝ) < p → p < (k : ℝ) + 1 →
    (∑ i, (a false i + a true i) ^ p) < ∑ i, (b false i + b true i) ^ p
  traces : ∀ j, (∑ i, a j i) = T ∧ (∑ i, b j i) = T
  trace_pos : 0 < T

private lemma higher_relations (k : ℕ) (hk : 2 ≤ k) :
    let q := k + 1
    let tau : ℝ := k + 4
    let c : ℝ := (tau + (k + 2 : ℝ) / 2 - 1) / 2
    DiagonalRelations (2 ^ q) k (higherDiagonal q (tau - c) c)
      (higherOtherDiagonal q (tau - c) c) ((c + 1 / 2) * (2 : ℝ) ^ q) := by
  dsimp only
  let c : ℝ := (((k : ℝ) + 4) + ((k : ℝ) + 2) / 2 - 1) / 2
  let u : ℝ := (k : ℝ) + 4 - c
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 0 < c := by dsimp [c]; linarith
  have hu : 0 < u := by dsimp [u, c]; linarith
  have hm (i : Fin (2 ^ (k + 1))) : 0 ≤ mark (k + 1) ((coordinates (k + 1) i).card) ∧
      mark (k + 1) ((coordinates (k + 1) i).card) ≤ 1 := by
    rcases mark_cases (k + 1) ((coordinates (k + 1) i).card) with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, ?_, higher_spectra_products (k + 1) (by omega) u c, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i
    cases j <;> simp only [higherDiagonal, Bool.false_eq_true, reduceIte]
    · exact add_pos_of_pos_of_nonneg hu (Nat.cast_nonneg _)
    · exact add_pos_of_pos_of_nonneg hc (hm i).1
  · intro j i
    cases j <;> simp only [higherOtherDiagonal, Bool.false_eq_true, reduceIte]
    · exact add_pos_of_pos_of_nonneg hu (Nat.cast_nonneg _)
    · linarith [(hm i).2]
  · intro m l
    have hd := higher_word_difference (k + 1) u c
      (List.replicate m false ++ List.replicate l true)
    rw [real_word_trace, real_word_trace, ← Complex.ofReal_sub] at hd
    have hd' := congrArg Complex.re hd
    simp only [Complex.ofReal_re] at hd'
    have hmcount : (List.replicate m false ++ List.replicate l true).count false = m := by
      simp [List.count_append, List.count_replicate]
    have hlcount : (List.replicate m false ++ List.replicate l true).count true = l := by
      simp [List.count_append, List.count_replicate]
    rw [hmcount, hlcount] at hd'
    have hs : 0 ≤ ((c + 1) ^ l - c ^ l) *
        (fwdDiff 1)^[k + 1] (fun x : ℝ => x ^ m) u :=
      mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hc.le (by linarith) l))
        (nat_power_difference_nonnegative (k + 1) m u hu)
    linarith
  · intro l hl hl'
    have hz := congr_fun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) (show l < k + 1 + 1 by omega)) (u + c)
    have hd := higher_sum_difference (k + 1) u c (fun x : ℝ => x ^ l)
    rw [hz] at hd
    simpa only [Pi.zero_apply] using sub_eq_zero.mp hd
  · intro p hp hp'
    have hd := higher_sum_difference (k + 1) u c (fun x : ℝ => x ^ p)
    have hn := power_difference_negative (k + 1) (by omega) p (u + c) (by linarith)
      (by push_cast; linarith) (by exact_mod_cast hp')
    linarith
  · intro j
    apply higher_traces (k + 1) (by omega) u c _ j
    dsimp [u, c]
    push_cast
    ring
  · exact mul_pos (by linarith) (by positivity)

/-- The shifted dimension-four source, on the original shared coordinates. -/
def firstDiagonal (b : Bool) : Fin 4 → ℝ :=
  if b then ![2, 1, 2, 3] else ![1, 2, 2, 3]

def firstOtherDiagonal (b : Bool) : Fin 4 → ℝ :=
  if b then ![1, 2, 3, 2] else ![1, 2, 2, 3]

private lemma first_relations : DiagonalRelations 4 1 firstDiagonal firstOtherDiagonal 8 := by
  have hm (m : ℕ) : 2 * (2 : ℝ) ^ m ≤ 1 + 3 ^ m := by
    have hc := (convexOn_pow (𝕜 := ℝ) m).2
      (show (1 : ℝ) ∈ Set.Ici 0 by norm_num) (show (3 : ℝ) ∈ Set.Ici 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    norm_num [smul_eq_mul] at hc
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · intro j i
    cases j <;> fin_cases i <;> norm_num [firstDiagonal]
  · intro j i
    cases j <;> fin_cases i <;> norm_num [firstOtherDiagonal]
  · intro f j
    cases j <;> simp [firstDiagonal, firstOtherDiagonal, Fin.prod_univ_succ] <;> ring
  · intro m l
    have hm0 : 0 ≤ (2 : ℝ) ^ m - 1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    have hl0 : 0 ≤ (2 : ℝ) ^ l - 1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    have hmul := mul_le_mul (show (2 : ℝ) ^ m - 1 ≤ 3 ^ m - 2 ^ m by linarith [hm m])
      (show (2 : ℝ) ^ l - 1 ≤ 3 ^ l - 2 ^ l by linarith [hm l]) hl0
      (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num) m))
    simp only [firstDiagonal, firstOtherDiagonal, Bool.false_eq_true, reduceIte]
    norm_num [Fin.sum_univ_succ]
    nlinarith [hmul]
  · intro l hl hl'
    have : l = 1 ∨ l = 2 := by omega
    rcases this with rfl | rfl <;> norm_num [firstDiagonal, firstOtherDiagonal, Fin.sum_univ_succ]
  · intro p hp hp'
    have h := first_power_difference_negative p (by norm_num at hp; exact hp) (by norm_num at hp'; exact hp')
    norm_num [firstDiagonal, firstOtherDiagonal, Fin.sum_univ_succ]
    linarith
  · intro j
    cases j <;> norm_num [firstDiagonal, firstOtherDiagonal, Fin.sum_univ_succ]

/-- The native matrices at a single common scale. -/
def matrices {n : ℕ} (d : Bool → Fin n → ℝ) (gamma : ℝ) (j : Bool) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal (fun i => ((gamma * d j i : ℝ) : ℂ))

private lemma matrices_sum {n : ℕ} (d : Bool → Fin n → ℝ) (gamma : ℝ) :
    matrices d gamma false + matrices d gamma true =
      diagonal (fun i => ((gamma * (d false i + d true i) : ℝ) : ℂ)) := by
  rw [matrices, matrices, diagonal_add]
  congr 1
  funext i
  push_cast
  ring

private lemma scaled_word_trace {n : ℕ} (d : Bool → Fin n → ℝ) (gamma : ℝ) (s : List Bool) :
    (wordProduct (matrices d gamma) s).trace =
      ((gamma ^ s.length * ∑ i, d false i ^ s.count false * d true i ^ s.count true : ℝ) : ℂ) := by
  rw [show matrices d gamma = (fun j => diagonal (fun i => ((gamma * d j i : ℝ) : ℂ))) by rfl,
    real_word_trace]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mul_pow, mul_pow, ← List.count_false_add_count_true s, pow_add]
  ring

private lemma native_moment {n : ℕ} (d : Bool → Fin n → ℝ) (gamma : ℝ) (l : ℕ) :
    ((matrices d gamma false + matrices d gamma true) ^ l).trace =
      ((gamma ^ l * ∑ i, (d false i + d true i) ^ l : ℝ) : ℂ) := by
  rw [matrices_sum, diagonal_pow, trace_diagonal]
  simp only [Pi.pow_apply, ← Complex.ofReal_pow, ← Complex.ofReal_sum]
  congr 1
  simp_rw [mul_pow]
  rw [← mul_sum]

private lemma native_norm {n : ℕ} (d : Bool → Fin n → ℝ) (gamma p : ℝ)
    (hd : ∀ j i, 0 < d j i) (hg : 0 < gamma) :
    schattenNorm (matrices d gamma false + matrices d gamma true) p =
      (gamma ^ p * ∑ i, (d false i + d true i) ^ p) ^ (1 / p) := by
  rw [matrices_sum, norm_diagonal _ (fun i => mul_nonneg hg.le (by linarith [hd false i, hd true i]))]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  exact Real.mul_rpow hg.le (by linarith [hd false i, hd true i])

/-- Source and normalized assertions use the same native matrices throughout. -/
structure NativeRelations (n k : ℕ) (A B : Bool → Matrix (Fin n) (Fin n) ℂ) (T : ℝ) : Prop where
  positive_a : ∀ j, (A j).PosDef
  positive_b : ∀ j, (B j).PosDef
  commuting : ∀ side side' j j' : Bool,
    Commute ((if side then B else A) j) ((if side' then B else A) j')
  spectra : ∀ j, (A j).charpoly = (B j).charpoly
  words : ∀ s : List Bool,
    (wordProduct A s).trace.im = 0 ∧ (wordProduct B s).trace.im = 0 ∧
    0 ≤ (wordProduct A s).trace.re ∧ 0 ≤ (wordProduct B s).trace.re ∧
    ‖(wordProduct B s).trace‖ ≤ (wordProduct A s).trace.re
  moments : ∀ l : ℕ, 1 ≤ l → l ≤ k + 1 →
    ((A false + A true) ^ l).trace = ((B false + B true) ^ l).trace
  endpoint_norms : ∀ l : ℕ, 1 ≤ l → l ≤ k + 1 →
    schattenNorm (A false + A true) (l : ℝ) = schattenNorm (B false + B true) (l : ℝ)
  reversal : ∀ p : ℝ, (k : ℝ) < p → p < (k : ℝ) + 1 →
    schattenNorm (A false + A true) p < schattenNorm (B false + B true) p
  traces : ∀ j, (A j).trace = (T : ℂ) ∧ (B j).trace = (T : ℂ)
  trace_pos : 0 < T

private lemma native_relations {n k : ℕ} {a b : Bool → Fin n → ℝ} {T : ℝ}
    (h : DiagonalRelations n k a b T) (gamma : ℝ) (hg : 0 < gamma) :
    NativeRelations n k (matrices a gamma) (matrices b gamma) (gamma * T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, mul_pos hg h.trace_pos⟩
  · intro j
    exact Matrix.PosDef.diagonal (fun i => by exact_mod_cast mul_pos hg (h.positive_a j i))
  · intro j
    exact Matrix.PosDef.diagonal (fun i => by exact_mod_cast mul_pos hg (h.positive_b j i))
  · intro side side' j j'
    cases side <;> cases side' <;>
      simp only [Bool.false_eq_true, reduceIte, matrices, Commute, SemiconjBy, diagonal_mul_diagonal] <;>
      congr 1 <;> funext i <;> ring
  · intro j
    simp only [matrices, charpoly_diagonal]
    exact h.spectra (fun x => Polynomial.X - Polynomial.C ((gamma * x : ℝ) : ℂ)) j
  · intro s
    rw [scaled_word_trace, scaled_word_trace]
    have hb0 : 0 ≤ ∑ i, b false i ^ s.count false * b true i ^ s.count true :=
      sum_nonneg (fun i _ => mul_nonneg (pow_nonneg (h.positive_b false i).le _)
        (pow_nonneg (h.positive_b true i).le _))
    have ha0 : 0 ≤ ∑ i, a false i ^ s.count false * a true i ^ s.count true :=
      le_trans hb0 (h.words _ _)
    have hg0 : 0 ≤ gamma ^ s.length := (pow_pos hg _).le
    simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hg0 hb0)]
    exact ⟨True.intro, True.intro, mul_nonneg hg0 ha0, mul_nonneg hg0 hb0,
      mul_le_mul_of_nonneg_left (h.words _ _) hg0⟩
  · intro l hl hl'
    rw [native_moment, native_moment, h.moments l hl hl']
  · intro l hl hl'
    rw [native_norm _ _ _ h.positive_a hg, native_norm _ _ _ h.positive_b hg]
    simp_rw [Real.rpow_natCast]
    rw [h.moments l hl hl']
  · intro p hp hp'
    rw [native_norm _ _ _ h.positive_a hg, native_norm _ _ _ h.positive_b hg]
    apply Real.rpow_lt_rpow
    · exact mul_nonneg (Real.rpow_nonneg hg.le _) (sum_nonneg (fun i _ =>
        Real.rpow_nonneg (by linarith [h.positive_a false i, h.positive_a true i]) _))
    · exact mul_lt_mul_of_pos_left (h.powers p hp hp') (Real.rpow_pos_of_pos hg p)
    · exact one_div_pos.mpr (lt_of_le_of_lt (Nat.cast_nonneg k) hp)
  · intro j
    constructor <;> simp only [matrices, trace_diagonal, ← Complex.ofReal_sum, ← mul_sum]
    · rw [(h.traces j).1]
    · rw [(h.traces j).2]

/-- Every cardinality fiber has exactly the source binomial multiplicity. -/
private lemma coordinate_multiplicity (q a : ℕ) :
    (univ.filter (fun i : Fin (2 ^ q) => (coordinates q i).card = a)).card = q.choose a := by
  have hs := sum_coordinates q (fun n => if n = a then 1 else 0)
  by_cases ha : a ≤ q
  · have hm : a ∈ range (q + 1) := mem_range.mpr (by omega)
    simpa [mul_ite, sum_ite, hm] using hs
  · have hm : a ∉ range (q + 1) := by simp; omega
    have hz := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)
    simpa [mul_ite, sum_ite, hm, hz] using hs

private lemma higher_sum_spectrum (q : ℕ) (u c : ℝ) (f : ℝ → ℝ) :
    (∑ i : Fin (2 ^ q), f (higherDiagonal q u c false i + higherDiagonal q u c true i)) =
      ∑ j ∈ range (q + 2), if Even (q + 1 - j) then
        ((q + 1).choose j : ℝ) * f (u + c + j) else 0 := by
  simp only [higherDiagonal, Bool.false_eq_true, reduceIte]
  rw [sum_coordinates q (fun a => f (u + a + (c + mark q a)))]
  have hs := sum_choose_succ_mul
    (fun a b => if Even b then f (u + c + a) else 0) q
  simp only [mul_ite, mul_zero] at hs
  rw [hs, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have ha' : a ≤ q := by simpa using ha
  have he : q + 1 - a = q - a + 1 := by omega
  simp only [he, Nat.even_add_one]
  by_cases hm : Even (q - a) <;>
    simp only [mark, hm, not_true_eq_false, not_false_eq_true, if_true, if_false,
      add_zero, zero_add] <;> congr 1 <;> congr 1 <;> push_cast <;> ring

private lemma higher_other_sum_spectrum (q : ℕ) (u c : ℝ) (f : ℝ → ℝ) :
    (∑ i : Fin (2 ^ q), f (higherOtherDiagonal q u c false i + higherOtherDiagonal q u c true i)) =
      ∑ j ∈ range (q + 2), if ¬ Even (q + 1 - j) then
        ((q + 1).choose j : ℝ) * f (u + c + j) else 0 := by
  simp only [higherOtherDiagonal, Bool.false_eq_true, reduceIte]
  rw [sum_coordinates q (fun a => f (u + a + (c + 1 - mark q a)))]
  have hs := sum_choose_succ_mul
    (fun a b => if ¬ Even b then f (u + c + a) else 0) q
  simp only [mul_ite, mul_zero] at hs
  rw [hs, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have ha' : a ≤ q := by simpa using ha
  have he : q + 1 - a = q - a + 1 := by omega
  simp only [he, Nat.even_add_one]
  by_cases hm : Even (q - a) <;>
    simp only [mark, hm, not_true_eq_false, not_false_eq_true, if_true, if_false,
      add_zero, zero_add, add_sub_cancel_right, sub_zero] <;>
    congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The source j and epsilon are coordinates of each actual shared label. -/
def labelMark (q : ℕ) (i : Fin (2 ^ q)) : ℕ :=
  if Even (q - (coordinates q i).card) then 1 else 0

def labelIndex (q : ℕ) (i : Fin (2 ^ q)) : ℕ :=
  (coordinates q i).card + labelMark q i

private lemma source_label (q : ℕ) (i : Fin (2 ^ q)) :
    labelIndex q i ≤ q + 1 ∧ Even (q + 1 - labelIndex q i) ∧
    mark q ((coordinates q i).card) = (labelMark q i : ℝ) := by
  have ha : (coordinates q i).card ≤ q := by
    simpa using card_le_card (subset_univ (coordinates q i))
  simp only [labelIndex, labelMark, mark]
  split_ifs with he
  · constructor
    · omega
    constructor
    · simpa only [show q + 1 - ((coordinates q i).card + 1) = q - (coordinates q i).card by omega] using he
    · norm_num
  · constructor
    · omega
    constructor
    · rw [add_zero, show q + 1 - (coordinates q i).card = q - (coordinates q i).card + 1 by omega,
        Nat.even_add_one]
      exact he
    · norm_num

private lemma source_entries (q : ℕ) (tau c : ℝ) (i : Fin (2 ^ q)) :
    higherDiagonal q (tau - c) c false i = tau + labelIndex q i - c - labelMark q i ∧
    higherDiagonal q (tau - c) c true i = c + labelMark q i ∧
    higherOtherDiagonal q (tau - c) c false i = tau + labelIndex q i - c - labelMark q i ∧
    higherOtherDiagonal q (tau - c) c true i = c + 1 - labelMark q i := by
  have he := (source_label q i).2.2
  simp only [higherDiagonal, higherOtherDiagonal, Bool.false_eq_true, reduceIte, he, labelIndex]
  push_cast
  exact ⟨by ring, True.intro, by ring, True.intro⟩

private lemma scaled_word_product {n : ℕ} (d : Bool → Fin n → ℝ) (gamma : ℝ) (s : List Bool) :
    wordProduct (matrices d gamma) s = (gamma : ℂ) ^ s.length • wordProduct (matrices d 1) s := by
  have hd (t : ℝ) : matrices d t = fun b : Bool =>
      if b then diagonal (fun i => ((t * d true i : ℝ) : ℂ)) else
        diagonal (fun i => ((t * d false i : ℝ) : ℂ)) := by
    funext b
    cases b <;> rfl
  rw [hd gamma, hd 1, word_diagonal, word_diagonal, ← diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, one_mul,
    Complex.ofReal_one, mul_pow]
  rw [← List.count_false_add_count_true s, pow_add]
  ring

private lemma matrix_scaling {n : ℕ} (d : Bool → Fin n → ℝ) (gamma : ℝ) (j : Bool) :
    matrices d gamma j = (gamma : ℂ) • matrices d 1 j := by
  simp only [matrices, ← diagonal_smul]
  congr 1
  funext i
  simp [Complex.ofReal_mul]

/-- A witness is constrained to the exact source diagonals, including their trace formula. -/
def SourceSpecification (k n : ℕ) (a b : Bool → Fin n → ℝ) (T : ℝ) : Prop :=
  (k = 1 ∧ n = 4 ∧ HEq a firstDiagonal ∧ HEq b firstOtherDiagonal ∧ T = 8) ∨
  (2 ≤ k ∧ n = 2 ^ (k + 1) ∧
    HEq a (higherDiagonal (k + 1)
      ((k + 4 : ℝ) - (((k + 4 : ℝ) + (k + 2 : ℝ) / 2 - 1) / 2))
      (((k + 4 : ℝ) + (k + 2 : ℝ) / 2 - 1) / 2)) ∧
    HEq b (higherOtherDiagonal (k + 1)
      ((k + 4 : ℝ) - (((k + 4 : ℝ) + (k + 2 : ℝ) / 2 - 1) / 2))
      (((k + 4 : ℝ) + (k + 2 : ℝ) / 2 - 1) / 2)) ∧
    T = ((((k + 4 : ℝ) + (k + 2 : ℝ) / 2 - 1) / 2) + 1 / 2) * (2 : ℝ) ^ (k + 1))

private theorem exact_normalized_application (k : ℕ) (hk : 1 ≤ k) :
    ∃ (n : ℕ) (a b : Bool → Fin n → ℝ) (T : ℝ),
      n = 2 ^ (k + 1) ∧ SourceSpecification k n a b T ∧
      DiagonalRelations n k a b T ∧
      NativeRelations n k (matrices a 1) (matrices b 1) T ∧
      NativeRelations n k (matrices a T⁻¹) (matrices b T⁻¹) 1 ∧
      0 < T⁻¹ ∧
      (∀ (d : Bool → Fin n → ℝ),
        (∀ j, matrices d T⁻¹ j = ((T⁻¹ : ℝ) : ℂ) • matrices d 1 j) ∧
        (∀ s : List Bool, wordProduct (matrices d T⁻¹) s =
          ((T⁻¹ : ℝ) : ℂ) ^ s.length • wordProduct (matrices d 1) s) ∧
        (∀ s : List Bool, (wordProduct (matrices d T⁻¹) s).trace =
          ((T⁻¹ : ℝ) : ℂ) ^ s.length * (wordProduct (matrices d 1) s).trace) ∧
        matrices d T⁻¹ false + matrices d T⁻¹ true =
          ((T⁻¹ : ℝ) : ℂ) • (matrices d 1 false + matrices d 1 true)) := by
  have build {n : ℕ} (a b : Bool → Fin n → ℝ) (T : ℝ)
      (hn : n = 2 ^ (k + 1)) (hs : SourceSpecification k n a b T)
      (h : DiagonalRelations n k a b T) :
      ∃ (n : ℕ) (a b : Bool → Fin n → ℝ) (T : ℝ),
        n = 2 ^ (k + 1) ∧ SourceSpecification k n a b T ∧ DiagonalRelations n k a b T ∧
        NativeRelations n k (matrices a 1) (matrices b 1) T ∧
        NativeRelations n k (matrices a T⁻¹) (matrices b T⁻¹) 1 ∧ 0 < T⁻¹ ∧
        (∀ d : Bool → Fin n → ℝ,
          (∀ j, matrices d T⁻¹ j = ((T⁻¹ : ℝ) : ℂ) • matrices d 1 j) ∧
          (∀ s : List Bool, wordProduct (matrices d T⁻¹) s =
            ((T⁻¹ : ℝ) : ℂ) ^ s.length • wordProduct (matrices d 1) s) ∧
          (∀ s : List Bool, (wordProduct (matrices d T⁻¹) s).trace =
            ((T⁻¹ : ℝ) : ℂ) ^ s.length * (wordProduct (matrices d 1) s).trace) ∧
          matrices d T⁻¹ false + matrices d T⁻¹ true =
            ((T⁻¹ : ℝ) : ℂ) • (matrices d 1 false + matrices d 1 true)) := by
    refine ⟨n, a, b, T, hn, hs, h, ?_, ?_, inv_pos.mpr h.trace_pos, ?_⟩
    · simpa using native_relations h 1 (by norm_num)
    · simpa [inv_mul_cancel₀ h.trace_pos.ne'] using native_relations h T⁻¹ (inv_pos.mpr h.trace_pos)
    · intro d
      refine ⟨matrix_scaling d T⁻¹, scaled_word_product d T⁻¹, ?_, ?_⟩
      · intro s
        rw [scaled_word_product, trace_smul, smul_eq_mul]
      · rw [matrix_scaling d T⁻¹ false, matrix_scaling d T⁻¹ true, smul_add]
  by_cases he : k = 1
  · subst k
    exact build firstDiagonal firstOtherDiagonal 8 (by norm_num)
      (Or.inl ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl⟩) first_relations
  · have hk2 : 2 ≤ k := by omega
    exact build _ _ _ rfl (Or.inr ⟨hk2, rfl, HEq.rfl, HEq.rfl, rfl⟩) (higher_relations k hk2)

#print axioms exact_normalized_application

private lemma source_marked_multiplicities (q j : ℕ) (hj : j ≤ q + 1)
    (hpar : Even (q + 1 - j)) :
    (univ.filter (fun i : Fin (2 ^ q) => labelIndex q i = j ∧ labelMark q i = 0)).card = q.choose j ∧
    (univ.filter (fun i : Fin (2 ^ q) => labelIndex q i = j ∧ labelMark q i = 1)).card =
      (if j = 0 then 0 else q.choose (j - 1)) := by
  constructor
  · have he : (univ.filter (fun i : Fin (2 ^ q) => labelIndex q i = j ∧ labelMark q i = 0)) =
        univ.filter (fun i : Fin (2 ^ q) => (coordinates q i).card = j) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hji, hmi⟩
        simpa only [labelIndex, hmi, add_zero] using hji
      · intro hai
        have ha : j ≤ q := by simpa [hai] using card_le_card (subset_univ (coordinates q i))
        have hn : ¬ Even (q - j) := by
          have hp := hpar
          rw [show q + 1 - j = q - j + 1 by omega, Nat.even_add_one] at hp
          exact hp
        have hm : labelMark q i = 0 := by simp [labelMark, hai, hn]
        exact ⟨by simp [labelIndex, hai, hm], hm⟩
    rw [he, coordinate_multiplicity]
  · by_cases hz : j = 0
    · subst j
      have he : (univ.filter (fun i : Fin (2 ^ q) => labelIndex q i = 0 ∧ labelMark q i = 1)) = ∅ := by
        ext i
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
        intro hi hm
        simp only [labelIndex, hm] at hi
        omega
      simp [he]
    · have he : (univ.filter (fun i : Fin (2 ^ q) => labelIndex q i = j ∧ labelMark q i = 1)) =
          univ.filter (fun i : Fin (2 ^ q) => (coordinates q i).card = j - 1) := by
        ext i
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨hji, hmi⟩
          simp only [labelIndex, hmi] at hji
          omega
        · intro hai
          have hp : Even (q - (j - 1)) := by
            simpa only [show q + 1 - j = q - (j - 1) by omega] using hpar
          have hm : labelMark q i = 1 := by simp [labelMark, hai, hp]
          refine ⟨?_, hm⟩
          simp only [labelIndex, hai, hm]
          omega
      rw [he, coordinate_multiplicity]
      simp [hz]

private lemma native_real_power_trace {n : ℕ} (d : Bool → Fin n → ℝ) (gamma p : ℝ) :
    (cfc (fun x : ℝ => x ^ p) (matrices d gamma false + matrices d gamma true)).trace =
      ((∑ i, (gamma * (d false i + d true i)) ^ p : ℝ) : ℂ) := by
  rw [matrices_sum,
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal, trace_diagonal]
  simp only [Complex.ofReal_sum]

private theorem exact_source_bridges :
    (∀ q a : ℕ, (univ.filter (fun i : Fin (2 ^ q) => (coordinates q i).card = a)).card = q.choose a) ∧
    (∀ (q j : ℕ), j ≤ q + 1 → Even (q + 1 - j) →
      (univ.filter (fun i : Fin (2 ^ q) => labelIndex q i = j ∧ labelMark q i = 0)).card = q.choose j ∧
      (univ.filter (fun i : Fin (2 ^ q) => labelIndex q i = j ∧ labelMark q i = 1)).card =
        (if j = 0 then 0 else q.choose (j - 1))) ∧
    (∀ (q : ℕ) (u c : ℝ) (f : ℝ → ℝ),
      (∑ i : Fin (2 ^ q), f (higherDiagonal q u c false i + higherDiagonal q u c true i)) =
        ∑ j ∈ range (q + 2), if Even (q + 1 - j) then
          ((q + 1).choose j : ℝ) * f (u + c + j) else 0) ∧
    (∀ (q : ℕ) (u c : ℝ) (f : ℝ → ℝ),
      (∑ i : Fin (2 ^ q), f (higherOtherDiagonal q u c false i + higherOtherDiagonal q u c true i)) =
        ∑ j ∈ range (q + 2), if ¬ Even (q + 1 - j) then
          ((q + 1).choose j : ℝ) * f (u + c + j) else 0) ∧
    (∀ (q : ℕ) (u c : ℝ) (f : ℝ → ℝ),
      (∑ i : Fin (2 ^ q), f (higherDiagonal q u c false i + higherDiagonal q u c true i)) -
        (∑ i : Fin (2 ^ q), f (higherOtherDiagonal q u c false i + higherOtherDiagonal q u c true i)) =
        (fwdDiff 1)^[q + 1] f (u + c)) ∧
    (∀ (q : ℕ) (u c : ℝ) (s : List Bool),
      (wordProduct (fun b => diagonal (fun i => (higherDiagonal q u c b i : ℂ))) s).trace -
        (wordProduct (fun b => diagonal (fun i => (higherOtherDiagonal q u c b i : ℂ))) s).trace =
        ((((c + 1) ^ s.count true - c ^ s.count true) *
          (fwdDiff 1)^[q] (fun x : ℝ => x ^ s.count false) u : ℝ) : ℂ)) := by
  exact ⟨coordinate_multiplicity, source_marked_multiplicities, higher_sum_spectrum,
    higher_other_sum_spectrum, higher_sum_difference, higher_word_difference⟩

#print axioms exact_source_bridges

private theorem exact_first_source_bridge :
    matrices firstDiagonal 1 false = diagonal (![0, 1, 1, 2] : Fin 4 → ℂ) + 1 ∧
    matrices firstDiagonal 1 true = diagonal (![1, 0, 1, 2] : Fin 4 → ℂ) + 1 ∧
    matrices firstOtherDiagonal 1 false = diagonal (![0, 1, 1, 2] : Fin 4 → ℂ) + 1 ∧
    matrices firstOtherDiagonal 1 true = diagonal (![0, 1, 2, 1] : Fin 4 → ℂ) + 1 ∧
    matrices firstDiagonal 1 false + matrices firstDiagonal 1 true =
      diagonal (![3, 3, 4, 6] : Fin 4 → ℂ) ∧
    matrices firstOtherDiagonal 1 false + matrices firstOtherDiagonal 1 true =
      diagonal (![2, 4, 5, 5] : Fin 4 → ℂ) := by
  repeat' constructor
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrices, firstDiagonal, firstOtherDiagonal, Matrix.diagonal, Matrix.one_apply]

private theorem exact_first_difference (p : ℝ) :
    2 * (3 : ℝ) ^ p + 6 ^ p - 2 ^ p - 2 * 5 ^ p =
      (fwdDiff 1)^[2] (fun x : ℝ => x ^ p) 4 -
        (fwdDiff 1)^[2] (fun x : ℝ => x ^ p) 2 := by
  norm_num [Function.iterate_succ_apply', fwdDiff]
  ring

#print axioms exact_first_source_bridge
#print axioms exact_first_difference
#print axioms source_label
#print axioms source_entries
#print axioms native_real_power_trace

private theorem exact_source_parity (r j : ℕ) (hj : j ≤ r) :
    Even (r - j) ↔ j % 2 = r % 2 := by
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
  omega

private theorem exact_source_trace_formula (k : ℕ) :
    let N : ℝ := (2 : ℝ) ^ (k + 1)
    let tau : ℝ := k + 4
    let r : ℝ := k + 2
    let c : ℝ := (tau + r / 2 - 1) / 2
    tau * N + (r / 2) * N - c * N - N / 2 = (c + 1 / 2) * N := by
  dsimp
  ring

#print axioms exact_source_parity
#print axioms exact_source_trace_formula

end D5.S3.Quantum.Schatten.WordTraceExponentBoundary
