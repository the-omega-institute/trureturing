/- GID: D5/S1/Words/Complexity/UniformWordRecurrence
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/UniformWordRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binomial counts and word-factor reconstruction for lacunary marked hierarchies. -/

/-
admission_basis: escape-witness
proof_shape: content (`core_first_strict`, `core_recurrent`); supporting lemmas are
consumed on the live recurrence and strictness paths.
escape_witness: `strict_one_two_of_return`, the finite-factor strict inequality used by
`recurrent_nonconstant_strict_one_two` and `core_first_strict`.
Direct frozen dependencies: extracted from the scoped Lean report.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23567.
-/

import Batteries.Tactic.OpenPrivate
import D5.S1.Words.Complexity.LacunaryBinomialMarkers
import D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall
import D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
import D5.S1.Words.Complexity.MorseHedlund
import D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
import D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
import D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import D5.S1.Words.Complexity.VivionBinomialConverseFails
import D5.S1.Words.GoldenFactorComplexity
import D5.S1.Words.GoldenUniformRecurrence
import D5.S1.Words.GoldenWord
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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

namespace D5.S1.Words.Complexity.UniformWordRecurrence
open D5.S1.Words.Complexity
variable {A B : Type*} [Fintype A] [Fintype B]
def Recurrent (x : Nat → A) : Prop :=
  ∀ n, ∀ u ∈ wordFactorSet x n,
    ∃ R, ∀ s, ∃ t, s ≤ t ∧ t + n ≤ s + R ∧ u = wordFactor x n t
def uniformExpansion (q : Nat) (hq : 0 < q) (block : A → Fin q → B)
    (x : Nat → A) (n : Nat) : B :=
  block (x (n / q)) ⟨n % q, Nat.mod_lt n hq⟩
private theorem factor_alignment (q : Nat) (hq : 0 < q) (block : A → Fin q → B)
    (x : Nat → A) (n a t : Nat)
    (hsource : wordFactor x (n + 1) (a / q) = wordFactor x (n + 1) t) :
    wordFactor (uniformExpansion q hq block x) n a =
      wordFactor (uniformExpansion q hq block x) n (q * t + a % q) := by
  funext r
  have hr : a % q + r.val < (n + 1) * q := by
    have hm := Nat.mod_lt a hq
    have hn := r.isLt
    nlinarith
  let d : Fin (n + 1) := ⟨(a % q + r.val) / q, (Nat.div_lt_iff_lt_mul hq).mpr hr⟩
  have hf := congrFun hsource d
  have hleft : (a + r.val) / q = a / q + d.val := by
    have ha := Nat.div_add_mod a q
    calc
      (a + r.val) / q = ((a % q + r.val) + q * (a / q)) / q := by congr 1; omega
      _ = (a % q + r.val) / q + a / q := Nat.add_mul_div_left _ _ hq
      _ = a / q + d.val := by dsimp [d]; omega
  have hright : (q * t + a % q + r.val) / q = t + d.val := by
    rw [Nat.add_assoc, Nat.add_comm (q * t), Nat.add_mul_div_left _ _ hq]
    dsimp [d]
    omega
  have hmod : (a + r.val) % q = (q * t + a % q + r.val) % q := by
    rw [Nat.add_assoc, Nat.mul_add_mod_self_left]
    exact (Nat.mod_add_mod a q r.val).symm
  change block (x ((a + r.val) / q)) _ = block (x ((q * t + a % q + r.val) / q)) _
  rw [hleft, hright]
  change x (a / q + d.val) = x (t + d.val) at hf
  rw [hf]
  congr 1
  exact Fin.ext hmod
private theorem uniformExpansion_recurrent (x : Nat → A) (hx : Recurrent x)
    (q : Nat) (hq : 0 < q) (block : A → Fin q → B) :
    Recurrent (uniformExpansion q hq block x) := by
  intro n u hu
  obtain ⟨a, rfl⟩ := mem_wordFactorSet.mp hu
  obtain ⟨R, hR⟩ := hx (n + 1) (wordFactor x (n + 1) (a / q))
    (mem_wordFactorSet.mpr ⟨a / q, rfl⟩)
  refine ⟨q * (R + 2) + n, ?_⟩
  intro s
  obtain ⟨t, hst, htend, hfac⟩ := hR (s / q + 1)
  refine ⟨q * t + a % q, ?_, ?_, factor_alignment q hq block x n a t hfac⟩
  · have hm := Nat.mod_lt s hq
    have hs := Nat.div_add_mod s q
    have hmul : q * (s / q) + q ≤ q * t := by
      simpa only [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left q hst
    omega
  · have hm := Nat.mod_lt a hq
    have hs := Nat.div_add_mod s q
    have ht : t ≤ s / q + 1 + R := by omega
    have hmul : q * t ≤ q * (s / q) + q + q * R := by
      simpa only [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left q ht
    simp only [Nat.mul_add, Nat.mul_succ, Nat.mul_one] at *
    omega
end D5.S1.Words.Complexity.UniformWordRecurrence
namespace D5.S1.Words.Complexity.UniformWordRecurrence
open D5.S1.Words D5.S1.Words.Complexity
private theorem golden_recurrent : Recurrent goldenWord := by
  intro n u hu
  obtain ⟨s, rfl⟩ := mem_wordFactorSet.mp hu
  have hlist : List.ofFn (wordFactor goldenWord n s) ∈ goldenFactorSet n :=
    mem_goldenFactorSet.mpr ⟨s, rfl⟩
  refine ⟨goldenRecurrenceBound n, ?_⟩
  intro a
  obtain ⟨t, hat, htend, hfac⟩ := golden_factor_uniformly_recurrent hlist a
  exact ⟨t, hat, htend, List.ofFn_injective hfac⟩
private theorem expanded_golden_recurrent (q : Nat) (hq : 0 < q)
    (block : Bool → Fin q → Bool) :
    Recurrent (uniformExpansion q hq block goldenWord) :=
  uniformExpansion_recurrent goldenWord golden_recurrent q hq block
end D5.S1.Words.Complexity.UniformWordRecurrence
namespace D5.S1.Words.Complexity.UniformWordRecurrence.Core
open D5.S1.Words.Complexity D5.S1.Words.Complexity.UniformWordRecurrence
def thueBlock (k : Nat) (a : Bool) : List Bool :=
  List.ofFn (fun j : Fin (2 ^ k) => Bool.xor a (thueMorse j))
theorem thueBlock_zero (a : Bool) : thueBlock 0 a = [a] := by
  cases a <;> simp [thueBlock]
theorem thueBlock_succ (k : Nat) (a : Bool) :
    thueBlock (k + 1) a = thueBlock k a ++ thueBlock k (!a) := by
  unfold thueBlock
  rw [pow_succ, Nat.mul_two, List.ofFn_add]
  congr 1
  congr 1
  funext j
  simp only [Fin.coe_natAdd, thueMorse_two_pow_add k j.val j.isLt]
  cases a <;> cases thueMorse j.val <;> rfl
def core (k : Nat) : Nat → Bool :=
  fun n => Bool.xor (!(D5.S1.Words.goldenWord (n / (2 ^ k)))) (thueMorse (n % (2 ^ k)))
theorem core_recurrent (k : Nat) : Recurrent (core k) := by
  exact expanded_golden_recurrent (2 ^ k) (Nat.two_pow_pos k)
    (fun a j => Bool.xor (!a) (thueMorse j))
end D5.S1.Words.Complexity.UniformWordRecurrence.Core
namespace D5.S1.Words.Complexity.UniformWordRecurrence.Filtration
open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence.Core
private theorem rationalMagnus_append (u v : List Bool) :
    (toRationalWordPolynomial (magnusPolynomial (u ++ v))) = (toRationalWordPolynomial (magnusPolynomial u)) * (toRationalWordPolynomial (magnusPolynomial v)) := by
  simp [magnusPolynomial, List.prod_append]
private theorem rationalMagnus_empty_coeff (source : List Bool) :
    ((toRationalWordPolynomial (magnusPolynomial source))).coeff 1 = 1 := by
  simp only [toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom]
  change ((magnusPolynomial source).coeff (FreeMonoid.ofList []) : ℚ) = 1
  rw [magnusPolynomial_coeff_scatteredCount]
  norm_num [scatteredCount]
private theorem cutoff_tail_vanishes (cutoff : Nat) (source : List Bool) :
    VanishesBelow cutoff 1 (cutoffMagnus cutoff source - cutoffOne cutoff) := by
  intro w hw
  have he : w.1 = 1 := by
    apply FreeMonoid.toList.injective
    exact List.length_eq_zero_iff.mp (by
      simpa only [FreeMonoid.length] using (show FreeMonoid.length w.1 = 0 by omega))
  change ((toRationalWordPolynomial (magnusPolynomial source))).coeff w.1 -
    (1 : RationalWordPolynomial Bool).coeff w.1 = 0
  rw [he, rationalMagnus_empty_coeff]
  simp
private theorem swapped_blocks_vanish (cutoff d : Nat) (u v : List Bool)
    (h : VanishesBelow cutoff d (cutoffMagnus cutoff u - cutoffMagnus cutoff v)) :
    VanishesBelow cutoff (d + 1)
      (cutoffMagnus cutoff (u ++ v) - cutoffMagnus cutoff (v ++ u)) := by
  let delta := (toRationalWordPolynomial (magnusPolynomial u)) - (toRationalWordPolynomial (magnusPolynomial v))
  let tail := (toRationalWordPolynomial (magnusPolynomial v)) - 1
  have hd : VanishesBelow cutoff d (cutoffRestriction cutoff delta) := h
  have ht : VanishesBelow cutoff 1 (cutoffRestriction cutoff tail) :=
    cutoff_tail_vanishes cutoff v
  have hleft := cutoffMul_vanishesBelow cutoff d 1
    (cutoffRestriction cutoff delta) (cutoffRestriction cutoff tail) hd ht
  have hright := cutoffMul_vanishesBelow cutoff 1 d
    (cutoffRestriction cutoff tail) (cutoffRestriction cutoff delta) ht hd
  have hid : (toRationalWordPolynomial (magnusPolynomial (u ++ v))) - (toRationalWordPolynomial (magnusPolynomial (v ++ u))) =
      delta * tail - tail * delta := by
    rw [rationalMagnus_append, rationalMagnus_append]
    dsimp [delta, tail]
    noncomm_ring
  have hres : cutoffRestriction cutoff (delta * tail - tail * delta) =
      cutoffMul cutoff (cutoffRestriction cutoff delta) (cutoffRestriction cutoff tail) -
        cutoffMul cutoff (cutoffRestriction cutoff tail) (cutoffRestriction cutoff delta) := by
    funext w
    rw [Pi.sub_apply, ← cutoffRestriction_mul, ← cutoffRestriction_mul]
    rfl
  intro w hw
  change (cutoffRestriction cutoff
    ((toRationalWordPolynomial (magnusPolynomial (u ++ v))) - (toRationalWordPolynomial (magnusPolynomial (v ++ u))))) w = 0
  rw [hid, hres, Pi.sub_apply, hleft w hw, hright w (by omega), sub_self]
private theorem thueBlock_filtration (k cutoff : Nat) :
    VanishesBelow cutoff (k + 1)
      (cutoffMagnus cutoff (thueBlock k false) - cutoffMagnus cutoff (thueBlock k true)) := by
  induction k with
  | zero =>
      rw [thueBlock_zero, thueBlock_zero]
      intro w hw
      have ha := cutoff_tail_vanishes cutoff [false] w hw
      have hb := cutoff_tail_vanishes cutoff [true] w hw
      change cutoffMagnus cutoff [false] w - cutoffMagnus cutoff [true] w = 0
      change cutoffMagnus cutoff [false] w - cutoffOne cutoff w = 0 at ha
      change cutoffMagnus cutoff [true] w - cutoffOne cutoff w = 0 at hb
      exact sub_eq_zero.mpr ((sub_eq_zero.mp ha).trans (sub_eq_zero.mp hb).symm)
  | succ k ih =>
      rw [thueBlock_succ, thueBlock_succ]
      simp only [Bool.not_false, Bool.not_true]
      exact swapped_blocks_vanish cutoff (k + 1) (thueBlock k false) (thueBlock k true) ih
def thueWord (k : Nat) (source : List Bool) : List Bool :=
  source.flatMap (thueBlock k)
private theorem cutoffMagnus_append (cutoff : Nat) (u v : List Bool) :
    cutoffMagnus cutoff (u ++ v) =
      cutoffMul cutoff (cutoffMagnus cutoff u) (cutoffMagnus cutoff v) := by
  simp only [cutoffMagnus, magnusPolynomial, List.map_append, List.prod_append,
    map_mul, cutoffRestriction_mul]
private theorem cutoff_thueBlock_swap (k : Nat) (a b : Bool) :
    cutoffMagnus (k + 1) (thueBlock k a ++ thueBlock k b) =
      cutoffMagnus (k + 1) (thueBlock k b ++ thueBlock k a) := by
  have hab : cutoffMagnus (k + 1) (thueBlock k false ++ thueBlock k true) =
      cutoffMagnus (k + 1) (thueBlock k true ++ thueBlock k false) := by
    funext w
    have hw := swapped_blocks_vanish (k + 1) (k + 1)
      (thueBlock k false) (thueBlock k true) (thueBlock_filtration k (k + 1)) w
      (by have h := w.2; omega)
    exact sub_eq_zero.mp hw
  cases a <;> cases b
  · rfl
  · exact hab
  · exact hab.symm
  · rfl
private theorem cutoff_thueWord_permutation (k : Nat) {u v : List Bool} (h : u.Perm v) :
    cutoffMagnus (k + 1) (thueWord k u) = cutoffMagnus (k + 1) (thueWord k v) := by
  unfold thueWord
  induction h with
  | nil => rfl
  | cons a h ih =>
      simp only [List.flatMap_cons, cutoffMagnus_append]
      rw [ih]
  | swap a b word =>
      simp only [List.flatMap_cons]
      rw [← List.append_assoc, ← List.append_assoc,
        cutoffMagnus_append (k + 1) (thueBlock k b ++ thueBlock k a)
          (word.flatMap (thueBlock k)),
        cutoffMagnus_append (k + 1) (thueBlock k a ++ thueBlock k b)
          (word.flatMap (thueBlock k)), cutoff_thueBlock_swap]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
theorem thueWord_of_permutation (k : Nat) {u v : List Bool} (h : u.Perm v)
    (pattern : List Bool) (hp : pattern.length ≤ k + 1) :
    scatteredCount pattern (thueWord k u) = scatteredCount pattern (thueWord k v) := by
  have he := congrFun (cutoff_thueWord_permutation k h)
    ⟨FreeMonoid.ofList pattern, by simpa only [FreeMonoid.length, FreeMonoid.toList_ofList] using hp⟩
  change ((toRationalWordPolynomial (magnusPolynomial (thueWord k u)))).coeff (FreeMonoid.ofList pattern) =
    ((toRationalWordPolynomial (magnusPolynomial (thueWord k v)))).coeff (FreeMonoid.ofList pattern) at he
  simp only [toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom,
    magnusPolynomial_coeff_scatteredCount, Int.cast_natCast] at he
  have hh : ((scatteredCount pattern (thueWord k u) : ℤ) : ℚ) =
      ((scatteredCount pattern (thueWord k v) : ℤ) : ℚ) := he
  exact_mod_cast hh
end D5.S1.Words.Complexity.UniformWordRecurrence.Filtration

namespace D5.S1.Words.Complexity.UniformWordRecurrence.Counts
open D5.S1.Words.Complexity.VivionBinomialConverseFails
def tm : List Bool → List Bool
  | [] => []
  | a :: source => a :: (!a) :: tm source
theorem tm_length (source : List Bool) : (tm source).length = 2 * source.length := by
  induction source with
  | nil => rfl
  | cons a source ih => simp only [tm, List.length_cons, ih]; omega
theorem tm_counts (source : List Bool) :
    scatteredCount [false] (tm source) = source.length ∧
    scatteredCount [true] (tm source) = source.length ∧
    scatteredCount [false, true] (tm source) =
      scatteredCount [false] source + Nat.choose source.length 2 ∧
    scatteredCount [true, true] (tm source) = Nat.choose source.length 2 ∧
    scatteredCount [false, true, true] (tm source) =
      scatteredCount [false, false] source + scatteredCount [false, true] source +
        Nat.choose source.length 3 := by
  induction source with
  | nil => decide
  | cons a source ih =>
      have htot := D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary.singleton_counts_total source
      rcases ih with ⟨hz, ho, h01, h11, h011⟩
      cases a <;>
        simp only [tm, List.length_cons, scatteredCount, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, add_zero,
          hz, ho, h01, h11, h011, Nat.choose_succ_succ, Nat.choose_one_right,
          Nat.choose_zero_right] <;>
        simp only [show Nat.succ 1 = 2 from rfl, show Nat.succ 2 = 3 from rfl] <;>
        and_intros <;> first | trivial | omega
theorem repeated_false_count (source : List Bool) :
    scatteredCount [false, false] source = Nat.choose (scatteredCount [false] source) 2 := by
  induction source with
  | nil => decide
  | cons a source ih =>
      cases a <;> simp [scatteredCount, ih, Nat.choose_succ_succ'] <;> omega
end D5.S1.Words.Complexity.UniformWordRecurrence.Counts

namespace D5.S1.Words.Complexity.UniformWordRecurrence
open D5.S1.Words D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection D5.S1.Words.Complexity.UniformWordRecurrence D5.S1.Words.Complexity.UniformWordRecurrence.Core
open D5.S1.Words.Complexity.ExactDecks.Growth.PositiveWordBall (scatteredCount_singleton_eq_count)
theorem pair_count_snoc (a b c : Bool) (u : List Bool) :
    scatteredCount [a, b] (u ++ [c]) = scatteredCount [a, b] u +
      if b = c then scatteredCount [a] u else 0 := by
  induction u with
  | nil => cases a <;> cases b <;> cases c <;> simp [scatteredCount]
  | cons d u ih =>
      have hs := scatteredCount_singleton_eq_count b (u ++ [c])
      rw [List.count_append, ← scatteredCount_singleton_eq_count] at hs
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp [scatteredCount, ih, hs] <;> omega
private theorem strict_one_two_of_return (w : Nat → Bool) (m : Nat)
    (hreturn : w (m + 1) = w 0)
    (hdiff : ∃ i : Fin m, w (1 + i.val) ≠ w 0) :
    binomialComplexity w 1 (m + 1) < binomialComplexity w 2 (m + 1) := by
  let z := List.ofFn (wordFactor w m 1)
  have hu : List.ofFn (wordFactor w (m + 1) 0) = w 0 :: z := by
    rw [List.ofFn_succ]
    simp [z, D5.S1.Words.Complexity.wordFactor, Nat.add_comm]
    funext i
    change w (i.val + 1) = w (1 + i.val)
    congr 1
    omega
  have hv : List.ofFn (wordFactor w (m + 1) 1) = z ++ [w 0] := by
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, wordFactor, Fin.val_castSucc, Fin.val_last]
    rw [show 1 + m = m + 1 by omega, hreturn]
    rfl
  have hc : 0 < scatteredCount [!(w 0)] z := by
    rw [scatteredCount_singleton_eq_count]
    apply List.count_pos_iff.mpr
    obtain ⟨i, hi⟩ := hdiff
    apply List.mem_ofFn.mpr
    refine ⟨i, ?_⟩
    change w (1 + i.val) = !(w 0)
    cases h0 : w 0 <;> cases h1 : w (1 + i.val) <;> simp_all
  apply complexity_lt_of_split w (by decide : 1 ≤ 2)
    (mem_wordFactorSet.mpr ⟨0, rfl⟩) (mem_wordFactorSet.mpr ⟨1, rfl⟩)
  · apply D5.S1.Words.Complexity.LacunaryBinomialMarkers.Binary.profile_one_eq_of_true_count
    rw [hu, hv]
    rw [scatteredCount_singleton_eq_count, scatteredCount_singleton_eq_count]
    simp [List.count_cons, List.count_append, Nat.add_comm]
  · intro h
    have he := profile_eq_iff.mp h [w 0, !(w 0)] (by simp)
    rw [hu, hv, pair_count_snoc] at he
    cases h0 : w 0 <;> simp [h0, scatteredCount] at he hc <;> omega
private theorem recurrent_nonconstant_strict_one_two (w : Nat → Bool) (hw : Recurrent w)
    (hneq : ∃ r, w r ≠ w 0) :
    Set.Infinite {n | binomialComplexity w 1 n < binomialComplexity w 2 n} := by
  by_contra hf
  have hfinite : {n | binomialComplexity w 1 n < binomialComplexity w 2 n}.Finite := not_not.mp hf
  obtain ⟨B, hB⟩ := hfinite.bddAbove
  obtain ⟨r, hr⟩ := hneq
  have hrpos : 0 < r := by
    by_contra h
    have he : r = 0 := by omega
    exact hr (congrArg w he)
  obtain ⟨R, hR⟩ := hw 1 (wordFactor w 1 0) (mem_wordFactorSet.mpr ⟨0, rfl⟩)
  obtain ⟨t, hst, htend, hfac⟩ := hR (B + r + 2)
  cases t with
  | zero => omega
  | succ m =>
      have he := congrFun hfac (0 : Fin 1)
      change w 0 = w (m + 1) at he
      have hd : ∃ i : Fin m, w (1 + i.val) ≠ w 0 := by
        refine ⟨⟨r - 1, by omega⟩, ?_⟩
        simpa only [show 1 + (r - 1) = r by omega] using hr
      have hs := strict_one_two_of_return w m he.symm hd
      have hb : m + 1 ≤ B := hB hs
      omega
theorem core_first_strict (k : Nat) (hk : 1 ≤ k) :
    Set.Infinite {n | binomialComplexity (core k) 1 n <
      binomialComplexity (core k) 2 n} := by
  apply recurrent_nonconstant_strict_one_two (core k) (core_recurrent k)
  have hq : 1 < 2 ^ k := by
    cases k with
    | zero => omega
    | succ k => rw [pow_succ]; have hp := Nat.two_pow_pos k; omega
  have ht : thueMorse 1 = true := by simpa using thueMorse_two_mul_add_one 0
  refine ⟨1, ?_⟩
  change Bool.xor (!(goldenWord (1 / 2 ^ k))) (thueMorse (1 % 2 ^ k)) ≠
    Bool.xor (!(goldenWord (0 / 2 ^ k))) (thueMorse (0 % 2 ^ k))
  rw [Nat.div_eq_of_lt hq, Nat.mod_eq_of_lt hq, ht]
  simp only [Nat.zero_div, Nat.zero_mod, thueMorse_zero]
  cases goldenWord 0 <;> decide
end D5.S1.Words.Complexity.UniformWordRecurrence
