/- GID: D5/S1/Words/Complexity/ThueMorsePositionalRecovery
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ThueMorsePositionalRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binomial counts and word-factor reconstruction for lacunary marked hierarchies. -/
/-
admission_basis: escape-witness
proof_shape: content (`top_profile_injectivity`, `root_power_dvd_of_translated_coeff`);
supporting lemmas are consumed on the live rigidity paths.
escape_witness: `RootTransport.root_pullback_square`, the coprime root-order descent
used by `Rigidity.rootRigid_mu` and `top_profile_injectivity`.
Direct frozen dependencies: extracted from the scoped Lean report.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23567.
-/
import Batteries.Tactic.OpenPrivate
import D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore
import D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall
import D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
import D5.S1.Words.Complexity.LacunaryBinomialMarkers
import D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency
import D5.S1.Words.Complexity.MorseHedlund
import D5.S1.Words.Complexity.SubshiftTopology
import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import D5.S1.Words.Complexity.UniformWordRecurrence
import D5.S1.Words.Complexity.VivionBinomialConverseFails
import D5.S1.Words.GoldenWord
import D5.S1.Words.ThueMorseDyadic
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1024
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Moment
open Polynomial
open scoped BigOperators
private noncomputable def thueFactor (k : Nat) : ℚ[X] :=
  ∏ i ∈ Finset.range k, (1 - X ^ (2 ^ i))
private theorem thueFactor_eval_zero (k : Nat) : (thueFactor k).eval 0 = 1 := by
  simp [thueFactor, eval_prod, Nat.two_pow_pos]
private theorem thueFactor_ne_zero (k : Nat) : thueFactor k ≠ 0 := by
  intro h
  have hz := thueFactor_eval_zero k
  rw [h] at hz
  norm_num at hz
private theorem simple_thue_root (i : Nat) :
    rootMultiplicity (1 : ℚ) (1 - X ^ (2 ^ i) : ℚ[X]) = 1 := by
  let p : ℚ[X] := 1 - X ^ (2 ^ i)
  have hp : p ≠ 0 := by
    intro hz
    have he := congrArg (Polynomial.eval (0 : ℚ)) hz
    simp [p, Nat.two_pow_pos] at he
  have hr : p.IsRoot 1 := by simp [p, IsRoot]
  have hlo : 0 < rootMultiplicity (1 : ℚ) p := (rootMultiplicity_pos hp).mpr hr
  have hhi : ¬ 1 < rootMultiplicity (1 : ℚ) p := by
    rw [one_lt_rootMultiplicity_iff_isRoot hp]
    intro h
    have hd := h.2
    simp [p, IsRoot, derivative_sub, derivative_X_pow, Nat.two_pow_pos] at hd
  change rootMultiplicity (1 : ℚ) p = 1
  omega
private theorem thueFactor_rootMultiplicity (k : Nat) :
    rootMultiplicity (1 : ℚ) (thueFactor k) = k := by
  induction k with
  | zero => simp [thueFactor]
  | succ k ih =>
      have heq : thueFactor (k + 1) = thueFactor k * (1 - X ^ (2 ^ k)) := by
        simp [thueFactor, Finset.prod_range_succ]
      rw [heq, rootMultiplicity_mul (by rw [← heq]; exact thueFactor_ne_zero (k + 1)),
        ih, simple_thue_root]
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Moment
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery
open Polynomial
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence
open D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
private noncomputable def headDeck (r : Nat) (u : List Bool) : ℚ :=
  ((u.sublistsLen (r + 1)).map (fun w : List Bool => match w with | [] => (0 : ℚ) | a :: _ => (D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.sign a : ℚ))).sum
noncomputable def reversePolynomial (u : List Bool) : ℚ[X] :=
  Polynomial.ofCoeffList (u.reverse.map
    (fun a => (D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.sign a : ℚ)))
theorem ofCoeffList_append (u v : List ℚ) :
    Polynomial.ofCoeffList (u ++ v) = Polynomial.ofCoeffList u +
      X ^ u.length * Polynomial.ofCoeffList v := by
  induction u with
  | nil => simp
  | cons a u ih =>
    simp only [List.cons_append, Polynomial.ofCoeffList_cons, List.length_cons, ih]
    ring
private theorem reversePolynomial_cons (a : Bool) (u : List Bool) :
    reversePolynomial (a :: u) =
      C ((D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.sign a : ℚ)) *
        X ^ u.length + reversePolynomial u := by
  simp only [reversePolynomial, List.reverse_cons, List.map_append, List.map_cons,
    List.map_nil, ofCoeffList_append, List.length_map, List.length_reverse,
    Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil, mul_zero, add_zero]
  ring
private theorem headDeck_cons (r : Nat) (a : Bool) (u : List Bool) :
    headDeck r (a :: u) = headDeck r u + (u.length.choose r : ℚ) * (D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.sign a : ℚ) := by
  simp [headDeck, List.sublistsLen_succ_cons, List.map_map,
    Function.comp_def, nsmul_eq_mul]
private theorem reversePolynomial_coeff (r : Nat) (u : List Bool) :
    ((reversePolynomial u).comp (X + 1)).coeff r = headDeck r u := by
  induction u with
  | nil => simp [reversePolynomial, headDeck]
  | cons a u ih =>
      rw [reversePolynomial_cons, add_comp, mul_comp, C_comp, pow_comp, X_comp,
        coeff_add, coeff_C_mul, coeff_X_add_one_pow, ih, headDeck_cons]
      ring
private theorem headDeck_eq_of_counts (r : Nat) (u v : List Bool) (h : ∀ p : List Bool, p.length = r + 1 → scatteredCount p u = scatteredCount p v) :
    headDeck r u = headDeck r v := by
  have hd : exactKDeck (r + 1) u = exactKDeck (r + 1) v := by
    funext p
    have hdec : (fun a b : Bool => Classical.propDecidable (a = b)) =
        (inferInstance : DecidableEq Bool) := Subsingleton.elim _ _
    unfold exactKDeck
    rw [hdec]
    exact h p.val p.property
  exact ((sublistsLen_perm_of_exactKDeck_eq (r + 1) u v hd).map (fun w : List Bool => match w with | [] => (0 : ℚ) | a :: _ => (D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.sign a : ℚ))).sum_eq
theorem positional_coeff_eq_of_counts (m : Nat) (u v : List Bool) (h : ∀ p : List Bool, p.length ≤ m → scatteredCount p u = scatteredCount p v)
    (r : Nat) (hr : r < m) :
    ((reversePolynomial u - reversePolynomial v).comp (X + 1)).coeff r = 0 := by
  rw [sub_comp, coeff_sub, reversePolynomial_coeff, reversePolynomial_coeff,
    headDeck_eq_of_counts r u v (fun p hp => h p (by omega)), sub_self]
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery
open Polynomial
theorem root_power_dvd_of_translated_coeff (p : ℚ[X]) (m : Nat) (h : ∀ r < m, (p.comp (X + 1)).coeff r = 0) : (X - 1) ^ m ∣ p := by
  have hd : X ^ m ∣ p.comp (X + 1) := X_pow_dvd_iff.mpr h
  obtain ⟨q, hq⟩ := hd
  refine ⟨q.comp (X - 1), ?_⟩
  have he := congrArg (fun f : ℚ[X] => f.comp (X - 1)) hq
  simpa only [Polynomial.comp_assoc, add_comp, X_comp, one_comp,
    sub_add_cancel, comp_X, mul_comp, pow_comp] using he
private theorem root_moments_of_transport (k q : Nat) (hq : 0 < q) (p t : ℚ[X]) (ht : t ≠ 0) (horder : rootMultiplicity (1 : ℚ) t = k) (hd : (X - 1) ^ (k + 2) ∣ t * p.comp (X ^ q)) :
    p.eval 1 = 0 ∧ p.derivative.eval 1 = 0 := by
  by_cases hp : p.comp (X ^ q) = 0
  · have he := congrArg (Polynomial.eval (1 : ℚ)) hp
    have hd := congrArg (fun f : ℚ[X] => f.derivative.eval 1) hp
    simp only [eval_comp, eval_pow, eval_X, one_pow, eval_zero] at he
    simp only [derivative_comp, derivative_zero, eval_mul, eval_comp,
      eval_pow, eval_X, one_pow, derivative_X_pow, eval_C, eval_one,
      mul_one, eval_zero] at hd
    exact ⟨he, (mul_eq_zero.mp hd).resolve_left (by exact_mod_cast Nat.ne_of_gt hq)⟩
  · have hprod : t * p.comp (X ^ q) ≠ 0 := mul_ne_zero ht hp
    have hm := (le_rootMultiplicity_iff hprod).mpr hd
    rw [rootMultiplicity_mul hprod, horder] at hm
    have htwo : 1 < rootMultiplicity (1 : ℚ) (p.comp (X ^ q)) := by omega
    obtain ⟨he, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot hp).mp htwo
    simp only [IsRoot, eval_comp, eval_pow, eval_X, one_pow] at he
    simp only [IsRoot, derivative_comp, eval_mul, eval_comp, eval_pow,
      eval_X, one_pow, derivative_X_pow, eval_C, mul_one] at hd
    exact ⟨he, (mul_eq_zero.mp hd).resolve_left (by exact_mod_cast Nat.ne_of_gt hq)⟩
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery
open Polynomial
theorem reverse_tm (u : List Bool) :
    reversePolynomial (D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm u) =
      (X - 1) * (reversePolynomial u).comp (X ^ 2) := by
  induction u with
  | nil => simp [D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm, reversePolynomial]
  | cons a u ih =>
      have hlen : (D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm u).length = 2 * u.length := by
        skip
        exact D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm_length u
      cases a <;>
        simp only [D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm, reversePolynomial_cons, List.length_cons, hlen,
          Bool.not_false, Bool.not_true, D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.sign, Int.cast_neg, Int.cast_one, Bool.false_eq_true, ite_false, ite_true,
          map_one, map_neg, neg_comp, add_comp, mul_comp, C_comp, one_comp, X_comp,
          pow_comp, ← pow_mul, pow_succ, ih] <;> ring
private theorem reverse_iterate (k : Nat) (u : List Bool) :
    reversePolynomial ((Nat.iterate D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm) k u) =
      C ((-1 : ℚ) ^ k) * D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Moment.thueFactor k *
        (reversePolynomial u).comp (X ^ (2 ^ k)) := by
  induction k generalizing u with
  | zero => simp [Nat.iterate, D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Moment.thueFactor]
  | succ k ih =>
      rw [Nat.iterate, ih, reverse_tm, mul_comp, sub_comp, X_comp,
        one_comp, Polynomial.comp_assoc]
      have hpow : (X ^ 2 : ℚ[X]).comp (X ^ (2 ^ k)) = X ^ (2 ^ (k + 1)) := by
        simp only [pow_comp, X_comp, ← pow_mul,
          show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k]
      rw [hpow]
      simp only [D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Moment.thueFactor, Finset.prod_range_succ, pow_succ, map_mul,
        map_neg, map_one]
      ring
private theorem image_recovers_moments (k : Nat) (u v : List Bool) (h : ∀ p : List Bool, p.length ≤ k + 2 →
      D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount p
        ((Nat.iterate D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm) k u) =
      D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount p
        ((Nat.iterate D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm) k v)) :
    (reversePolynomial u).eval 1 = (reversePolynomial v).eval 1 ∧
      (reversePolynomial u).derivative.eval 1 =
        (reversePolynomial v).derivative.eval 1 := by
  let t : ℚ[X] := C ((-1 : ℚ) ^ k) * D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Moment.thueFactor k
  have ht : t ≠ 0 := mul_ne_zero (by simp) (D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Moment.thueFactor_ne_zero k)
  have ho : rootMultiplicity (1 : ℚ) t = k := by
    rw [rootMultiplicity_mul ht, rootMultiplicity_C, zero_add,
      D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Moment.thueFactor_rootMultiplicity]
  have hd := root_power_dvd_of_translated_coeff
    (reversePolynomial ((Nat.iterate D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm) k u) -
      reversePolynomial ((Nat.iterate D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm) k v)) (k + 2)
      (positional_coeff_eq_of_counts (k + 2) _ _ h)
  rw [reverse_iterate, reverse_iterate, ← mul_sub, ← sub_comp] at hd
  have hm := root_moments_of_transport k (2 ^ k) (Nat.two_pow_pos k)
    (reversePolynomial u - reversePolynomial v) t ht ho hd
  simpa only [eval_sub, derivative_sub, sub_eq_zero] using hm
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery
open Polynomial
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence
private theorem reverse_eval (u : List Bool) :
    (reversePolynomial u).eval 1 =
      2 * (scatteredCount [false] u : ℚ) - u.length := by
  induction u with
  | nil => simp [reversePolynomial, scatteredCount]
  | cons a u ih =>
      cases a <;> simp [reversePolynomial_cons, D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.sign, Int.cast_neg, Int.cast_one, scatteredCount, ih] <;> ring
private theorem reverse_derivative (u : List Bool) :
    (reversePolynomial u).derivative.eval 1 =
      2 * ((scatteredCount [false, false] u : ℚ) +
        (scatteredCount [false, true] u : ℚ)) - (u.length.choose 2 : ℚ) := by
  induction u with
  | nil => simp [reversePolynomial, scatteredCount]
  | cons a u ih =>
      have hc : (scatteredCount [false] u : ℚ) +
          (scatteredCount [true] u : ℚ) = u.length := by
        exact_mod_cast D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary.singleton_counts_total u
      cases a <;>
        simp [reversePolynomial_cons, D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.sign, Int.cast_neg, Int.cast_one, scatteredCount, derivative_add,
          derivative_C_mul, derivative_X_pow, ih, Nat.choose_succ_succ',
          Nat.choose_one_right] <;> push_cast <;> linarith
theorem recover_counts_of_moments (u v : List Bool) (hlen : u.length = v.length) (he : (reversePolynomial u).eval 1 = (reversePolynomial v).eval 1) (hd : (reversePolynomial u).derivative.eval 1 =
      (reversePolynomial v).derivative.eval 1) :
    scatteredCount [false] u = scatteredCount [false] v ∧
      scatteredCount [false, true] u = scatteredCount [false, true] v := by
  rw [reverse_eval, reverse_eval, hlen] at he
  have hc : (scatteredCount [false] u : ℚ) = (scatteredCount [false] v : ℚ) := by
    linarith
  have hzero : scatteredCount [false] u = scatteredCount [false] v := by
    exact_mod_cast hc
  refine ⟨hzero, ?_⟩
  rw [reverse_derivative, reverse_derivative, D5.S1.Words.Complexity.UniformWordRecurrence.Counts.repeated_false_count,
    D5.S1.Words.Complexity.UniformWordRecurrence.Counts.repeated_false_count, hzero, hlen] at hd
  have hp : (scatteredCount [false, true] u : ℚ) =
      (scatteredCount [false, true] v : ℚ) := by linarith
  exact_mod_cast hp
private theorem image_recovers_two_counts (k : Nat) (u v : List Bool) (hlen : u.length = v.length)
    (h : ∀ p : List Bool, p.length ≤ k + 2 →
      scatteredCount p ((Nat.iterate D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm) k u) =
        scatteredCount p ((Nat.iterate D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm) k v)) :
    scatteredCount [false] u = scatteredCount [false] v ∧
      scatteredCount [false, true] u = scatteredCount [false, true] v := by
  obtain ⟨he, hd⟩ := image_recovers_moments k u v h
  exact recover_counts_of_moments u v hlen he hd
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence
open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
private theorem mixed_counts (u : List Bool) :
    scatteredCount [false] u * scatteredCount [true] u =
      scatteredCount [false, true] u + scatteredCount [true, false] u := by
  have he := D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration.scatteredCount_mul_eq_sum_overlapInfiltrations
    [false] [true] u
  simpa [D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration.overlapInfiltrations] using he
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence
open D5.S1.Words.Complexity.UniformWordRecurrence.Core D5.S1.Words.Complexity.UniformWordRecurrence.Filtration
private theorem thueWord_zero (u : List Bool) : thueWord 0 u = u := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa only [thueWord, List.flatMap_cons, thueBlock_zero,
      List.singleton_append] using congrArg (List.cons a) ih
private theorem thueWord_succ (k : Nat) (u : List Bool) :
    thueWord (k + 1) u = thueWord k (D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm u) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      simpa only [thueWord, List.flatMap_cons, D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm, thueBlock_succ,
        List.append_assoc] using congrArg (fun w =>
          thueBlock k a ++ (thueBlock k (!a) ++ w)) ih
theorem iterate_eq_thueWord (k : Nat) (u : List Bool) :
    (Nat.iterate D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm) k u = thueWord k u := by
  induction k generalizing u with
  | zero => exact (thueWord_zero u).symm
  | succ k ih => rw [Nat.iterate, ih, thueWord_succ]
private theorem block_image_recovers_two_counts (k : Nat) (u v : List Bool)
    (hlen : u.length = v.length)
    (h : ∀ p : List Bool, p.length ≤ k + 2 →
      scatteredCount p (thueWord k u) = scatteredCount p (thueWord k v)) :
    scatteredCount [false] u = scatteredCount [false] v ∧
      scatteredCount [false, true] u = scatteredCount [false, true] v := by
  apply image_recovers_two_counts k u v hlen
  simpa only [iterate_eq_thueWord] using h
private theorem core_aligned_factor (k n s : Nat) :
    List.ofFn (D5.S1.Words.Complexity.wordFactor (core k) (2 ^ k * n) (2 ^ k * s)) =
      thueWord k (List.ofFn (fun i : Fin n => !(D5.S1.Words.goldenWord (s + i.val)))) := by
  rw [List.ofFn_mul']
  unfold thueWord
  rw [List.flatMap_def, List.map_ofFn]
  congr 1
  congr 1
  funext i
  unfold thueBlock
  congr 1
  funext j
  change Bool.xor (!(D5.S1.Words.goldenWord
    ((2 ^ k * s + (2 ^ k * i.val + j.val)) / 2 ^ k)))
    (D5.S1.Words.Complexity.thueMorse
      ((2 ^ k * s + (2 ^ k * i.val + j.val)) % 2 ^ k)) = _
  rw [show 2 ^ k * s + (2 ^ k * i.val + j.val) = 2 ^ k * (s + i.val) + j.val by ring]
  simp [Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt j.isLt,
    Nat.mod_eq_of_lt j.isLt]
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence
open D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration
open D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall (scatteredCount_singleton_eq_count)
open D5.S1.Words.Complexity.UniformWordRecurrence.Core D5.S1.Words.Complexity.UniformWordRecurrence.Filtration D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
theorem counts_two_of_zero_pair (u v : List Bool) (hlen : u.length = v.length)
    (hz : scatteredCount [false] u = scatteredCount [false] v)
    (hp : scatteredCount [false, true] u = scatteredCount [false, true] v) :
    ∀ p : List Bool, p.length ≤ 2 → scatteredCount p u = scatteredCount p v := by
  have ht : scatteredCount [true] u = scatteredCount [true] v := by
    have hu := D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary.singleton_counts_total u
    have hv := D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary.singleton_counts_total v
    omega
  have htf : scatteredCount [true, false] u = scatteredCount [true, false] v := by
    have hu := mixed_counts u
    have hv := mixed_counts v
    rw [hz, ht, hp] at hu
    omega
  have hrepeat (a : Bool) (ha : scatteredCount [a] u = scatteredCount [a] v) :
      scatteredCount [a, a] u = scatteredCount [a, a] v := by
    have hu := scatteredCount_mul_eq_sum_overlapInfiltrations [a] [a] u
    have hv := scatteredCount_mul_eq_sum_overlapInfiltrations [a] [a] v
    simp [overlapInfiltrations] at hu hv
    rw [ha] at hu
    omega
  have hff := hrepeat false hz
  have htt := hrepeat true ht
  intro p hlenp
  cases p with
  | nil => simp [scatteredCount]
  | cons a p =>
      cases p with
      | nil => cases a <;> assumption
      | cons b p =>
          cases p with
          | nil => cases a <;> cases b <;> assumption
          | cons c p => simp only [List.length_cons] at hlenp; omega
private theorem core_last_strict_at (k n : Nat) (hn : 3 ≤ n) :
    binomialComplexity (core k) (k + 1) (2 ^ k * n) <
      binomialComplexity (core k) (k + 2) (2 ^ k * n) := by
  have hgold : binomialComplexity D5.S1.Words.goldenWord 1 n <
      binomialComplexity D5.S1.Words.goldenWord 2 n := by
    have ht := (complexity_eq_factor_iff D5.S1.Words.goldenWord 2 n).mpr
      (D5.S1.Words.Complexity.LacunaryBinomialMarkers.Golden.golden_profile_two_injective n)
    rw [ht, D5.S1.Words.Complexity.SubshiftTopology.golden_wordFactorSet_card]
    have hb := D5.S1.Words.Complexity.LacunaryBinomialMarkers.Golden.golden_abelian_bound n
    omega
  obtain ⟨u, hu, v, hv, hlow, hhigh⟩ :=
    split_of_complexity_lt D5.S1.Words.goldenWord (by omega : 1 ≤ 2) hgold
  have hperm : (List.ofFn u).Perm (List.ofFn v) := by
    rw [List.perm_iff_count]
    intro a
    rw [← scatteredCount_singleton_eq_count, ← scatteredCount_singleton_eq_count]
    exact profile_eq_iff.mp hlow [a] (by simp)
  obtain ⟨a, rfl⟩ := mem_wordFactorSet.mp hu
  obtain ⟨b, rfl⟩ := mem_wordFactorSet.mp hv
  have hmap :
      (List.ofFn (fun i : Fin n => !(D5.S1.Words.goldenWord (a + i.val)))).Perm
      (List.ofFn (fun i : Fin n => !(D5.S1.Words.goldenWord (b + i.val)))) := by
    simpa only [List.map_ofFn, Function.comp_def, wordFactor] using hperm.map Bool.not
  apply complexity_lt_of_split (core k) (by omega : k + 1 ≤ k + 2)
    (mem_wordFactorSet.mpr ⟨2 ^ k * a, rfl⟩)
    (mem_wordFactorSet.mpr ⟨2 ^ k * b, rfl⟩)
  · apply profile_eq_iff.mpr
    intro p hp
    rw [core_aligned_factor, core_aligned_factor]
    exact thueWord_of_permutation k hmap p hp
  · intro heq
    have hcounts : ∀ p : List Bool, p.length ≤ k + 2 →
        scatteredCount p (thueWord k
          (List.ofFn (fun i : Fin n => !(D5.S1.Words.goldenWord (a + i.val))))) =
        scatteredCount p (thueWord k
          (List.ofFn (fun i : Fin n => !(D5.S1.Words.goldenWord (b + i.val))))) := by
      intro p hp
      have hh := profile_eq_iff.mp heq p hp
      rw [core_aligned_factor, core_aligned_factor] at hh
      exact hh
    obtain ⟨hz, hp⟩ := block_image_recovers_two_counts k _ _ (by simp) hcounts
    have htwo : binomialProfile 2
        (fun i : Fin n => !(D5.S1.Words.goldenWord (a + i.val))) =
      binomialProfile 2 (fun i : Fin n => !(D5.S1.Words.goldenWord (b + i.val))) := by
      apply profile_eq_iff.mpr
      exact counts_two_of_zero_pair _ _ (by simp) hz hp
    have hback := profile_eq_map Bool.not htwo
    apply hhigh
    change binomialProfile 2 (fun i : Fin n => D5.S1.Words.goldenWord (a + i.val)) =
      binomialProfile 2 (fun i : Fin n => D5.S1.Words.goldenWord (b + i.val))
    simpa only [Function.comp_def, Bool.not_not] using hback
theorem core_last_strict (k : Nat) :
    Set.Infinite {n | binomialComplexity (core k) (k + 1) n <
      binomialComplexity (core k) (k + 2) n} := by
  have hi : Set.InjOn (fun n : Nat => 2 ^ k * n) (Set.Ici 3) := by
    intro a ha b hb he
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos k) he
  have hs := (Set.Ici_infinite (3 : Nat)).image hi
  apply hs.mono
  rintro m ⟨n, hn, rfl⟩
  exact core_last_strict_at k n hn
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery
open D5.S1.Words D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection D5.S1.Words.Complexity.UniformWordRecurrence D5.S1.Words.Complexity.UniformWordRecurrence.Core D5.S1.Words.Complexity.UniformWordRecurrence.Filtration
open D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall (scatteredCount_singleton_eq_count)
theorem expanded_aligned_factor (w : Nat → Bool) (r n s : Nat) :
    List.ofFn (wordFactor
      (uniformExpansion (2 ^ r) (Nat.two_pow_pos r)
        (fun a i => Bool.xor a (thueMorse i)) w)
      (2 ^ r * n) (2 ^ r * s)) = thueWord r (List.ofFn (wordFactor w n s)) := by
  rw [List.ofFn_mul']
  unfold thueWord
  rw [List.flatMap_def, List.map_ofFn]
  congr 1
  congr 1
  funext i
  unfold thueBlock
  congr 1
  funext j
  change Bool.xor (w ((2 ^ r * s + (2 ^ r * i.val + j.val)) / 2 ^ r))
    (thueMorse ((2 ^ r * s + (2 ^ r * i.val + j.val)) % 2 ^ r)) = _
  rw [show 2 ^ r * s + (2 ^ r * i.val + j.val) = 2 ^ r * (s + i.val) + j.val by ring]
  simp [Nat.mul_add_div (Nat.two_pow_pos r), Nat.div_eq_of_lt j.isLt,
    Nat.mod_eq_of_lt j.isLt, wordFactor]
private theorem expansion_lifts_first_strict (w : Nat → Bool) (r n : Nat)
    (hstrict : binomialComplexity w 1 n < binomialComplexity w 2 n) :
    binomialComplexity
      (uniformExpansion (2 ^ r) (Nat.two_pow_pos r)
        (fun a i => Bool.xor a (thueMorse i)) w) (r + 1) (2 ^ r * n) <
    binomialComplexity
      (uniformExpansion (2 ^ r) (Nat.two_pow_pos r)
        (fun a i => Bool.xor a (thueMorse i)) w) (r + 2) (2 ^ r * n) := by
  obtain ⟨u, hu, v, hv, hlow, hhigh⟩ := split_of_complexity_lt w (by omega : 1 ≤ 2) hstrict
  have hperm : (List.ofFn u).Perm (List.ofFn v) := by
    rw [List.perm_iff_count]
    intro a
    rw [← scatteredCount_singleton_eq_count, ← scatteredCount_singleton_eq_count]
    exact profile_eq_iff.mp hlow [a] (by simp)
  obtain ⟨a, rfl⟩ := mem_wordFactorSet.mp hu
  obtain ⟨b, rfl⟩ := mem_wordFactorSet.mp hv
  apply complexity_lt_of_split _ (by omega : r + 1 ≤ r + 2)
    (mem_wordFactorSet.mpr ⟨2 ^ r * a, rfl⟩)
    (mem_wordFactorSet.mpr ⟨2 ^ r * b, rfl⟩)
  · apply profile_eq_iff.mpr
    intro p hp
    rw [expanded_aligned_factor, expanded_aligned_factor]
    exact thueWord_of_permutation r hperm p hp
  · intro heq
    have hc : ∀ p : List Bool, p.length ≤ r + 2 →
        scatteredCount p (thueWord r (List.ofFn (wordFactor w n a))) =
        scatteredCount p (thueWord r (List.ofFn (wordFactor w n b))) := by
      intro p hp
      have hh := profile_eq_iff.mp heq p hp
      rw [expanded_aligned_factor, expanded_aligned_factor] at hh
      exact hh
    obtain ⟨hz, hp⟩ := block_image_recovers_two_counts r _ _ (by simp) hc
    apply hhigh
    exact profile_eq_iff.mpr (counts_two_of_zero_pair _ _ (by simp) hz hp)
private theorem core_block_decomposition (r k m u : Nat) (hu : u < 2 ^ r) :
    core (r + k) (2 ^ r * m + u) = Bool.xor (core k m) (thueMorse u) := by
  have hm := Nat.mod_lt m (Nat.two_pow_pos k)
  have hrem : 2 ^ r * (m % 2 ^ k) + u < 2 ^ (r + k) := by
    rw [pow_add]
    have hp := Nat.two_pow_pos r
    nlinarith
  have he : 2 ^ r * m + u =
      2 ^ (r + k) * (m / 2 ^ k) + (2 ^ r * (m % 2 ^ k) + u) := by
    rw [pow_add]
    have hh := Nat.div_add_mod m (2 ^ k)
    calc
      2 ^ r * m + u = 2 ^ r * (2 ^ k * (m / 2 ^ k) + m % 2 ^ k) + u := by rw [hh]
      _ = _ := by ring
  change Bool.xor (!(goldenWord ((2 ^ r * m + u) / 2 ^ (r + k))))
    (thueMorse ((2 ^ r * m + u) % 2 ^ (r + k))) =
    Bool.xor (Bool.xor (!(goldenWord (m / 2 ^ k))) (thueMorse (m % 2 ^ k))) (thueMorse u)
  rw [he, Nat.mul_add_div (Nat.two_pow_pos (r + k)), Nat.div_eq_of_lt hrem,
    Nat.add_zero, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrem]
  rw [show 2 ^ r * (m % 2 ^ k) + u = (m % 2 ^ k) * 2 ^ r + u by ring,
    ThueMorseDyadic.dyadic_block r (m % 2 ^ k) u hu]
  cases goldenWord (m / 2 ^ k) <;> cases thueMorse (m % 2 ^ k) <;>
    cases thueMorse u <;> rfl
theorem core_as_expansion (r k : Nat) :
    core (r + k) = uniformExpansion (2 ^ r) (Nat.two_pow_pos r)
      (fun a i => Bool.xor a (thueMorse i)) (core k) := by
  funext n
  have h := core_block_decomposition r k (n / 2 ^ r) (n % 2 ^ r)
    (Nat.mod_lt n (Nat.two_pow_pos r))
  rw [Nat.div_add_mod] at h
  exact h
theorem core_middle_strict (k j : Nat) (hj : 2 ≤ j) (hjk : j ≤ k) :
    Set.Infinite {n | binomialComplexity (core k) j n <
      binomialComplexity (core k) (j + 1) n} := by
  let r := j - 1
  let d := k - r
  have hd : 1 ≤ d := by dsimp [d, r]; omega
  have hk : r + d = k := by dsimp [d, r]; omega
  have hjr : r + 1 = j := by dsimp [r]; omega
  have hs := core_first_strict d hd
  have hi : Set.InjOn (fun n : Nat => 2 ^ r * n)
      {n | binomialComplexity (core d) 1 n < binomialComplexity (core d) 2 n} := by
    intro a ha b hb he
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos r) he
  apply (hs.image hi).mono
  rintro m ⟨n, hn, rfl⟩
  have ht := expansion_lifts_first_strict (core d) r n hn
  rw [← core_as_expansion, hk, hjr] at ht
  have hjr2 : r + 2 = j + 1 := by omega
  rw [hjr2] at ht
  exact ht
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Alignment
open D5.S1.Words.Complexity.VivionBinomialConverseFails D5.S1.Words.Complexity.UniformWordRecurrence.Counts
open D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall (scatteredCount_singleton_eq_count)
private theorem zero_le_length (u : List Bool) : (scatteredCount [false]) u ≤ u.length := by
  rw [scatteredCount_singleton_eq_count]
  exact List.count_le_length
private theorem zero_extreme (u : List Bool) :
    ((scatteredCount [false]) u = 0 → u = List.replicate u.length true) ∧
    ((scatteredCount [false]) u = u.length → u = List.replicate u.length false) := by
  constructor
  · intro hz
    have ht : u.count true = u.length := by
      have htot := D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary.singleton_counts_total u
      rw [scatteredCount_singleton_eq_count, scatteredCount_singleton_eq_count] at htot
      rw [scatteredCount_singleton_eq_count] at hz
      omega
    simpa only [ht] using (List.replicate_count_eq_of_count_eq_length ht).symm
  · intro hz
    rw [scatteredCount_singleton_eq_count] at hz
    simpa only [hz] using (List.replicate_count_eq_of_count_eq_length hz).symm
private theorem count_snoc (u : List Bool) (a : Bool) :
    (scatteredCount [false]) (u ++ [a]) = (scatteredCount [false]) u + (if a then 0 else 1) ∧
    (scatteredCount [false, true]) (u ++ [a]) = (scatteredCount [false, true]) u + (if a then (scatteredCount [false]) u else 0) := by
  constructor
  · simp only [scatteredCount_singleton_eq_count, List.count_append]
    cases a <;> simp
  · have h := D5.S1.Words.Complexity.UniformWordRecurrence.pair_count_snoc false true a u
    cases a <;> simpa using h
private theorem alternating_shift (a : Bool) (m : Nat) :
    a :: tm (List.replicate m (!a)) = tm (List.replicate m a) ++ [a] := by
  induction m with
  | zero => simp [tm]
  | succ m ih =>
    cases a <;> simp_all [List.replicate_succ, tm]
private theorem tm_both_counts (u : List Bool) (a b : Bool) :
    (scatteredCount [false]) (a :: (tm u ++ [b])) =
      u.length + (if a then 0 else 1) + (if b then 0 else 1) ∧
    (scatteredCount [false, true]) (a :: (tm u ++ [b])) =
      (scatteredCount [false]) u + u.length.choose 2 +
        (if b then u.length else 0) +
        (if a then 0 else u.length + (if b then 1 else 0)) := by
  have ht := tm_counts u
  have hs := count_snoc (tm u) b
  have htot := D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary.singleton_counts_total (tm u ++ [b])
  cases a <;> cases b <;>
    simp_all [scatteredCount, tm_length] <;> omega
private theorem tm_vs_both (u v : List Bool) (a b : Bool)
    (hlen : (tm u).length = (a :: (tm v ++ [b])).length)
    (hz : (scatteredCount [false]) (tm u) = (scatteredCount [false]) (a :: (tm v ++ [b])))
    (hp : (scatteredCount [false, true]) (tm u) = (scatteredCount [false, true]) (a :: (tm v ++ [b]))) :
    tm u = a :: (tm v ++ [b]) := by
  have hl : u.length = v.length + 1 := by
    simp only [tm_length, List.length_cons, List.length_append, List.length_singleton, List.length_nil] at hlen
    omega
  have hu := tm_counts u
  have hv := tm_both_counts v a b
  have hbu := zero_le_length u
  have hbv := zero_le_length v
  rw [hu.1, hv.1] at hz
  have hchoose : (v.length + 1).choose 2 = v.length.choose 2 + v.length := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ v.length 1
  rw [hu.2.2.1, hv.2, hl, hchoose] at hp
  cases a <;> cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hz hp
  · omega
  · have hzu : (scatteredCount [false]) u = u.length := by omega
    have hzv : (scatteredCount [false]) v = 0 := by omega
    rw [(zero_extreme u).2 hzu, (zero_extreme v).1 hzv, hl,
      List.replicate_succ, tm]
    exact congrArg (List.cons false) (alternating_shift true v.length)
  · have hzu : (scatteredCount [false]) u = 0 := by omega
    have hzv : (scatteredCount [false]) v = v.length := by omega
    rw [(zero_extreme u).1 hzu, (zero_extreme v).2 hzv, hl,
      List.replicate_succ, tm]
    exact congrArg (List.cons true) (alternating_shift false v.length)
  · omega
private theorem tm_left_counts (u : List Bool) (a : Bool) :
    (scatteredCount [false]) (a :: tm u) = u.length + (if a then 0 else 1) ∧
    (scatteredCount [false, true]) (a :: tm u) = (scatteredCount [false]) u + u.length.choose 2 + (if a then 0 else u.length) := by
  have ht := tm_counts u
  cases a <;> simp_all [scatteredCount]
private theorem tm_right_counts (u : List Bool) (a : Bool) :
    (scatteredCount [false]) (tm u ++ [a]) = u.length + (if a then 0 else 1) ∧
    (scatteredCount [false, true]) (tm u ++ [a]) = (scatteredCount [false]) u + u.length.choose 2 + (if a then u.length else 0) := by
  have ht := tm_counts u
  simpa only [ht.1, ht.2.2.1] using count_snoc (tm u) a
private theorem left_vs_right (u v : List Bool) (a b : Bool)
    (hlen : (a :: tm u).length = (tm v ++ [b]).length)
    (hz : (scatteredCount [false]) (a :: tm u) = (scatteredCount [false]) (tm v ++ [b]))
    (hp : (scatteredCount [false, true]) (a :: tm u) = (scatteredCount [false, true]) (tm v ++ [b])) :
    a :: tm u = tm v ++ [b] := by
  have hl : u.length = v.length := by
    simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil, tm_length] at hlen
    omega
  have hu := tm_left_counts u a
  have hv := tm_right_counts v b
  have hbu := zero_le_length u
  have hbv := zero_le_length v
  rw [hu.1, hv.1, hl] at hz
  rw [hu.2, hv.2, hl] at hp
  cases a <;> cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hz hp
  · have hzu : (scatteredCount [false]) u = 0 := by omega
    have hzv : (scatteredCount [false]) v = v.length := by omega
    rw [(zero_extreme u).1 hzu, (zero_extreme v).2 hzv, hl]
    exact alternating_shift false v.length
  · omega
  · omega
  · have hzu : (scatteredCount [false]) u = u.length := by omega
    have hzv : (scatteredCount [false]) v = 0 := by omega
    rw [(zero_extreme u).2 hzu, (zero_extreme v).1 hzv, hl]
    exact alternating_shift true v.length
private theorem both_boundary_eq (u v : List Bool) (a b c d : Bool)
    (hlen : (a :: (tm u ++ [b])).length = (c :: (tm v ++ [d])).length)
    (hz : (scatteredCount [false]) (a :: (tm u ++ [b])) = (scatteredCount [false]) (c :: (tm v ++ [d])))
    (hp : (scatteredCount [false, true]) (a :: (tm u ++ [b])) = (scatteredCount [false, true]) (c :: (tm v ++ [d]))) :
    a = c ∧ b = d := by
  have hl : u.length = v.length := by
    simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil, tm_length] at hlen
    omega
  have hu := tm_both_counts u a b
  have hv := tm_both_counts v c d
  have hbu := zero_le_length u
  have hbv := zero_le_length v
  rw [hu.1, hv.1, hl] at hz
  rw [hu.2, hv.2, hl] at hp
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
      true_and, and_true, and_self] at hz hp ⊢ <;> omega
def frame (l : Option Bool) (u : List Bool) (r : Option Bool) : List Bool :=
  l.toList ++ tm u ++ r.toList
private theorem left_boundary_eq (u v : List Bool) (a b : Bool)
    (hlen : (a :: tm u).length = (b :: tm v).length)
    (hz : (scatteredCount [false]) (a :: tm u) = (scatteredCount [false]) (b :: tm v)) : a = b := by
  have hu := tm_left_counts u a
  have hv := tm_left_counts v b
  simp only [List.length_cons, tm_length] at hlen
  rw [hu.1, hv.1] at hz
  cases a <;> cases b <;> simp at hz ⊢ <;> omega
private theorem right_boundary_eq (u v : List Bool) (a b : Bool)
    (hlen : (tm u ++ [a]).length = (tm v ++ [b]).length)
    (hz : (scatteredCount [false]) (tm u ++ [a]) = (scatteredCount [false]) (tm v ++ [b])) : a = b := by
  have hu := tm_right_counts u a
  have hv := tm_right_counts v b
  simp only [List.length_append, List.length_singleton, List.length_nil, tm_length] at hlen
  rw [hu.1, hv.1] at hz
  cases a <;> cases b <;> simp at hz ⊢ <;> omega
theorem frame_alignment (l r l' r' : Option Bool) (u v : List Bool)
    (hlen : (frame l u r).length = (frame l' v r').length)
    (hz : (scatteredCount [false]) (frame l u r) = (scatteredCount [false]) (frame l' v r'))
    (hp : (scatteredCount [false, true]) (frame l u r) = (scatteredCount [false, true]) (frame l' v r')) :
    (l = l' ∧ r = r' ∧ u.length = v.length) ∨ frame l u r = frame l' v r' := by
  cases l <;> cases r <;> cases l' <;> cases r'
  all_goals simp only [frame, Option.toList, List.nil_append,
    List.singleton_append, List.append_nil] at hlen hz hp ⊢
  all_goals first
    | exact Or.inr (tm_vs_both _ _ _ _ hlen hz hp)
    | exact Or.inr (tm_vs_both _ _ _ _ hlen.symm hz.symm hp.symm).symm
    | exact Or.inr (left_vs_right _ _ _ _ hlen hz hp)
    | exact Or.inr (left_vs_right _ _ _ _ hlen.symm hz.symm hp.symm).symm
    | skip
  all_goals try (exfalso; simp only [List.length_cons, List.length_append,
    List.length_singleton, List.length_nil, tm_length] at hlen; omega)
  all_goals first
    | (have hb := left_boundary_eq _ _ _ _ hlen hz
       subst_vars
       left
       simp only [true_and, List.length_cons, tm_length] at *
       omega)
    | (have hb := right_boundary_eq _ _ _ _ hlen hz
       subst_vars
       left
       simp only [true_and, List.length_append, List.length_singleton, List.length_nil, tm_length] at *
       omega)
    | (have hb := both_boundary_eq _ _ _ _ _ _ hlen hz hp
       rcases hb with ⟨rfl, rfl⟩
       left
       simp only [true_and, List.length_cons, List.length_append,
         List.length_singleton, List.length_nil, tm_length] at *
       omega)
    | (left
       simp only [true_and, tm_length] at *
       omega)
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Alignment
namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Alignment.FactorFrames
open D5.S1.Words.Complexity D5.S1.Words.Complexity.UniformWordRecurrence D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Alignment
def mu (w : Nat → Bool) : Nat → Bool :=
  fun n => Bool.xor (w (n / 2)) (thueMorse (n % 2))
private theorem mu_even (w : Nat → Bool) (s : Nat) : mu w (2 * s) = w s := by
  simp [mu, uniformExpansion]
private theorem mu_odd (w : Nat → Bool) (s : Nat) : mu w (2 * s + 1) = !(w s) := by
  have hdiv : (2 * s + 1) / 2 = s := by omega
  simp [mu, uniformExpansion, hdiv, show thueMorse 1 = true from rfl]
private theorem factorList_append (w : Nat → Bool) (n m s : Nat) :
    (List.ofFn (wordFactor w (n + m) s)) = (List.ofFn (wordFactor w n s)) ++ (List.ofFn (wordFactor w m (s + n))) := by
  skip
  rw [List.ofFn_add]
  congr 1
  congr 1
  funext i
  simp [wordFactor, Nat.add_assoc]
private theorem factorList_one (w : Nat → Bool) (s : Nat) : (List.ofFn (wordFactor w 1 s)) = [w s] := by
  simp [List.ofFn_succ, wordFactor]
private theorem mu_aligned (w : Nat → Bool) (m s : Nat) :
    (List.ofFn (wordFactor (mu w) (2 * m) (2 * s))) = D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm ((List.ofFn (wordFactor w m s))) := by
  have h := D5.S1.Words.Complexity.ThueMorsePositionalRecovery.expanded_aligned_factor w 1 m s
  change (List.ofFn (wordFactor (mu w) (2 * m) (2 * s))) =
    D5.S1.Words.Complexity.UniformWordRecurrence.Filtration.thueWord 1 ((List.ofFn (wordFactor w m s))) at h
  rw [← D5.S1.Words.Complexity.ThueMorsePositionalRecovery.iterate_eq_thueWord] at h
  change (List.ofFn (wordFactor (mu w) (2 * m) (2 * s))) = D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm ((List.ofFn (wordFactor w m s))) at h
  exact h
theorem factor_frame (w : Nat → Bool) (n s : Nat) :
    ∃ (l r : Option Bool) (m t : Nat),
      (List.ofFn (wordFactor (mu w) n s)) = frame l ((List.ofFn (wordFactor w m t))) r := by
  have hs := Nat.mod_lt s (by decide : 0 < 2)
  have hn := Nat.mod_lt n (by decide : 0 < 2)
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · exact ⟨none, none, 0, 0, by simp [frame, D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm]⟩
  rcases (by omega : s % 2 = 0 ∨ s % 2 = 1) with hs0 | hs1
  · have hse : s = 2 * (s / 2) := by omega
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn0 | hn1
    · have hne : n = 2 * (n / 2) := by omega
      refine ⟨none, none, n / 2, s / 2, ?_⟩
      conv_lhs => rw [hse, hne]
      simpa [frame] using mu_aligned w (n / 2) (s / 2)
    · have hne : n = 2 * (n / 2) + 1 := by omega
      refine ⟨none, some (w (s / 2 + n / 2)), n / 2, s / 2, ?_⟩
      conv_lhs => rw [hne, hse]
      rw [factorList_append, mu_aligned, factorList_one,
        show 2 * (s / 2) + 2 * (n / 2) = 2 * (s / 2 + n / 2) by omega, mu_even]
      rfl
  · have hse : s = 2 * (s / 2) + 1 := by omega
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn0 | hn1
    · have hne : n = 1 + (2 * (n / 2 - 1) + 1) := by omega
      refine ⟨some (!(w (s / 2))), some (w (s / 2 + n / 2)), n / 2 - 1, s / 2 + 1, ?_⟩
      conv_lhs => rw [hne]
      rw [factorList_append, factorList_one]
      conv_lhs => rw [hse]
      rw [mu_odd]
      have he : 2 * (s / 2) + 1 + 1 = 2 * (s / 2 + 1) := by omega
      rw [he, factorList_append, mu_aligned, factorList_one]
      have he' : 2 * (s / 2 + 1) + 2 * (n / 2 - 1) = 2 * (s / 2 + n / 2) := by omega
      rw [he', mu_even]
      rfl
    · have hne : n = 1 + 2 * (n / 2) := by omega
      refine ⟨some (!(w (s / 2))), none, n / 2, s / 2 + 1, ?_⟩
      conv_lhs => rw [hne]
      rw [factorList_append, factorList_one]
      conv_lhs => rw [hse]
      rw [mu_odd]
      have he : 2 * (s / 2) + 1 + 1 = 2 * (s / 2 + 1) := by omega
      rw [he, mu_aligned]
      simp [frame]
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Alignment.FactorFrames

namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery.RootTransport
open Polynomial D5.S1.Words.Complexity.ThueMorsePositionalRecovery
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence
private noncomputable def RootEq (m : Nat) (u v : List Bool) : Prop :=
  (X - 1 : ℚ[X]) ^ m ∣ reversePolynomial u - reversePolynomial v
private theorem rootEq_of_counts (m : Nat) (u v : List Bool)
    (h : ∀ p : List Bool, p.length ≤ m →
      D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount p u =
      D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount p v) :
    RootEq m u v :=
  root_power_dvd_of_translated_coeff _ m (positional_coeff_eq_of_counts m u v h)
private theorem rootEq_mono {m n : Nat} (hm : m ≤ n) {u v : List Bool}
    (h : RootEq n u v) : RootEq m u v :=
  (pow_dvd_pow (X - 1 : ℚ[X]) hm).trans h
private theorem rootEq_counts_two {m : Nat} (hm : 2 ≤ m) (u v : List Bool)
    (hlen : u.length = v.length) (h : RootEq m u v) :
    scatteredCount [false] u = scatteredCount [false] v ∧
      scatteredCount [false, true] u = scatteredCount [false, true] v := by
  have h2 := rootEq_mono hm h
  change (X - 1 : ℚ[X]) ^ 2 ∣ reversePolynomial u - reversePolynomial v at h2
  obtain ⟨q, hq⟩ := h2
  have he := congrArg (Polynomial.eval (1 : ℚ)) hq
  have hd := congrArg (fun p : ℚ[X] => p.derivative.eval 1) hq
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_one, sub_self,
    zero_pow (by decide : 2 ≠ 0), zero_mul] at he
  simp [derivative_mul, derivative_pow] at hd
  exact recover_counts_of_moments u v hlen (sub_eq_zero.mp he)
    (sub_eq_zero.mp hd)
private theorem reverse_append (u v : List Bool) :
    reversePolynomial (u ++ v) = reversePolynomial u * X ^ v.length +
      reversePolynomial v := by
  unfold reversePolynomial
  rw [List.reverse_append, List.map_append, ofCoeffList_append]
  simp only [List.length_map, List.length_reverse]
  ring
private theorem rootEq_cancel_padding (m : Nat) (l r u v : List Bool)
    (hlen : u.length = v.length)
    (h : RootEq m (l ++ u ++ r) (l ++ v ++ r)) : RootEq m u v := by
  unfold RootEq at *
  have hid : reversePolynomial (l ++ u ++ r) - reversePolynomial (l ++ v ++ r) =
      (reversePolynomial u - reversePolynomial v) * X ^ r.length := by
    simp only [reverse_append, List.length_append, hlen]
    ring
  rw [hid] at h
  have hc : IsCoprime (X - 1 : ℚ[X]) X := by
    refine ⟨-1, 1, ?_⟩
    ring
  exact (hc.pow (m := m) (n := r.length)).dvd_of_dvd_mul_right h
private theorem root_pullback_square (m : Nat) (p : ℚ[X])
    (h : (X - 1 : ℚ[X]) ^ m ∣ p.comp (X ^ 2)) :
    (X - 1 : ℚ[X]) ^ m ∣ p := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    have h1 : (X - 1 : ℚ[X]) ∣ p.comp (X ^ 2) := by
      simpa only [pow_one] using
        (pow_dvd_pow (X - 1 : ℚ[X]) (by omega : 1 ≤ m + 1)).trans h
    have he : p.eval 1 = 0 := by
      have hd : (X - C (1 : ℚ)) ∣ p.comp (X ^ 2) := by simpa only [C_1] using h1
      have he := dvd_iff_isRoot.mp hd
      simpa [IsRoot] using he
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr (show IsRoot p 1 from he)
    simp only [C_1] at hq
    have hfac : (p.comp (X ^ 2)) = (X - 1) * ((X + 1) * q.comp (X ^ 2)) := by
      rw [hq]
      simp only [mul_comp, sub_comp, X_comp, C_comp, C_1, one_comp]
      ring
    rw [hfac, pow_succ, mul_comm ((X - 1 : ℚ[X]) ^ m),
      mul_dvd_mul_iff_left (by simpa only [C_1] using (X_sub_C_ne_zero (1 : ℚ)))] at h
    have hc : IsCoprime (X - 1 : ℚ[X]) (X + 1) := by
      have hc := isCoprime_X_sub_C_of_isUnit_sub
        ((by norm_num : (1 : ℚ) - (-1) ≠ 0).isUnit)
      simpa only [map_one, map_neg, sub_neg_eq_add] using hc
    have hd := (hc.pow_left (m := m)).dvd_of_dvd_mul_left h
    have hrec := ih q hd
    rw [hq, pow_succ, mul_comm ((X - (1 : ℚ[X])) ^ m)]
    simpa only [C_1] using mul_dvd_mul_left (X - (1 : ℚ[X])) hrec
private theorem rootEq_tm_descent (m : Nat) (u v : List Bool)
    (h : RootEq (m + 1) (D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm u) (D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm v)) :
    RootEq m u v := by
  unfold RootEq at *
  rw [reverse_tm, reverse_tm,
    ← mul_sub, ← sub_comp, pow_succ, mul_comm ((X - 1 : ℚ[X]) ^ m),
    mul_dvd_mul_iff_left (by simpa only [C_1] using (X_sub_C_ne_zero (1 : ℚ)))] at h
  exact root_pullback_square m _ h
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery.RootTransport

namespace D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Rigidity
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence
open D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Alignment.FactorFrames D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Alignment D5.S1.Words.Complexity.ThueMorsePositionalRecovery.RootTransport D5.S1.Words.Complexity.ThueMorsePositionalRecovery D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
private def RootRigid (w : Nat → Bool) (d : Nat) : Prop :=
  ∀ n i j, RootEq d ((List.ofFn (wordFactor w n i))) ((List.ofFn (wordFactor w n j))) →
    (List.ofFn (wordFactor w n i)) = (List.ofFn (wordFactor w n j))
private theorem rootRigid_mu (w : Nat → Bool) (d : Nat) (hd : 1 ≤ d)
    (hw : RootRigid w d) : RootRigid (mu w) (d + 1) := by
  intro n i j he
  obtain ⟨l, r, m, s, hi⟩ := factor_frame w n i
  obtain ⟨l', r', m', s', hj⟩ := factor_frame w n j
  have hlen : (frame l ((List.ofFn (wordFactor w m s))) r).length =
      (frame l' ((List.ofFn (wordFactor w m' s'))) r').length := by
    rw [← hi, ← hj]
    simp [List.length_ofFn]
  rw [hi, hj] at he
  obtain ⟨hz, hp⟩ := rootEq_counts_two (by omega : 2 ≤ d + 1) _ _ hlen he
  rcases frame_alignment l r l' r' _ _ hlen hz hp with hframe | heq
  · rcases hframe with ⟨hll, hrr, hlen'⟩
    subst l'
    subst r'
    have hmm : m = m' := by simpa [List.length_ofFn] using hlen'
    subst m'
    have ht := rootEq_cancel_padding (d + 1) l.toList r.toList
      (D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm ((List.ofFn (wordFactor w m s))))
      (D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm ((List.ofFn (wordFactor w m s')))) (by simp [D5.S1.Words.Complexity.UniformWordRecurrence.Counts.tm_length]) he
    have hs := hw m s s' (rootEq_tm_descent d _ _ ht)
    rw [hi, hj, hs]
  · exact hi.trans (heq.trans hj.symm)
private theorem core_zero (s : Nat) : D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0 s = !(D5.S1.Words.goldenWord s) := by
  change Bool.xor (!(D5.S1.Words.goldenWord (s / 1))) (thueMorse (s % 1)) = _
  rw [Nat.div_one, Nat.mod_one, thueMorse_zero]
  cases D5.S1.Words.goldenWord s <;> rfl
private theorem rootRigid_core_zero : RootRigid (D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0) 2 := by
  intro n i j he
  have hlen : ((List.ofFn (wordFactor (D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0) n i))).length =
      ((List.ofFn (wordFactor (D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0) n j))).length := by simp [List.length_ofFn]
  obtain ⟨hz, hp⟩ := rootEq_counts_two (by decide : 2 ≤ 2) _ _ hlen he
  have hc := counts_two_of_zero_pair _ _ hlen hz hp
  have hprof : binomialProfile 2 (wordFactor (D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0) n i) =
      binomialProfile 2 (wordFactor (D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0) n j) := profile_eq_iff.mpr hc
  have hm := profile_eq_map Bool.not hprof
  have hcomp (s : Nat) : Bool.not ∘ wordFactor (D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0) n s =
      wordFactor D5.S1.Words.goldenWord n s := by
    funext r
    change (!(D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0 (s + r.val))) = D5.S1.Words.goldenWord (s + r.val)
    rw [core_zero]
    exact Bool.not_not _
  rw [hcomp i, hcomp j] at hm
  have heq := hm
  have heq' := D5.S1.Words.Complexity.LacunaryBinomialMarkers.Golden.golden_profile_two_injective n
    (mem_wordFactorSet.mpr ⟨i, rfl⟩) (mem_wordFactorSet.mpr ⟨j, rfl⟩) heq
  skip
  congr 1
  funext r
  have hh := congrFun heq' r
  change D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0 (i + r.val) = D5.S1.Words.Complexity.UniformWordRecurrence.Core.core 0 (j + r.val)
  rw [core_zero, core_zero]
  exact congrArg Bool.not hh
private theorem rootRigid_core (k : Nat) : RootRigid (D5.S1.Words.Complexity.UniformWordRecurrence.Core.core k) (k + 2) := by
  induction k with
  | zero => exact rootRigid_core_zero
  | succ k ih =>
    have hmu : D5.S1.Words.Complexity.UniformWordRecurrence.Core.core (k + 1) = mu (D5.S1.Words.Complexity.UniformWordRecurrence.Core.core k) := by
      have h := core_as_expansion 1 k
      rw [Nat.add_comm 1 k] at h
      exact h
    rw [hmu]
    exact rootRigid_mu _ (k + 2) (by omega) ih
theorem top_profile_injectivity : ∀ k n : Nat,
    Set.InjOn (binomialProfile (k + 2))
      (wordFactorSet (D5.S1.Words.Complexity.UniformWordRecurrence.Core.core k) n : Set (Fin n → Bool)) := by
  intro k n u hu v hv he
  obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hu
  obtain ⟨j, rfl⟩ := mem_wordFactorSet.mp hv
  apply List.ofFn_injective
  exact rootRigid_core k n i j (rootEq_of_counts (k + 2) _ _ (profile_eq_iff.mp he))
end D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Rigidity
