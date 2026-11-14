/- GID: D5/S1/Words/Complexity/ThueMorseFactorRigidity
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ThueMorseFactorRigidity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binomial counts and word-factor reconstruction for lacunary marked hierarchies. -/

/-
Admission classification is incomplete; this unfrozen source is not ready for deposit.
admission_basis: open-problem-resolution (#23400; Proved)
proof_shape: unverified
escape_witness: none
Direct frozen dependencies: pending exact compiled dependency extraction.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23567.
-/

import Batteries.Tactic.OpenPrivate
import D5.S0.Tower.GoldenGapWord
import D5.S1.Words.Complexity.LacunaryBinomialMarkers
import D5.S1.Words.Complexity.MorseHedlund
import D5.S1.Words.Complexity.ThueMorsePositionalRecovery
import D5.S1.Words.Complexity.ThueMorseReducedAbelianOdd
import D5.S1.Words.Complexity.UniformWordRecurrence
import D5.S1.Words.Complexity.VivionBinomialConverseFails
import D5.S1.Words.GoldenWord
import D5.S1.Words.RankOneMorphismIterationBoundDefs
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
import Mathlib.Tactic.DeriveFintype
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1024

open D5.S1.Words.RankOneMorphismIterationBound (image)
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity
private theorem morphismImageStep {A : Type*} (f : A → List A) (n : Nat) (a : A) :
    image f (n + 1) a = (f a).flatMap (image f n) := by
  simpa only [D5.S1.Words.RankOneMorphismIterationBound.image_one,
    D5.S1.Words.RankOneMorphismIterationBound.subst] using
    D5.S1.Words.RankOneMorphismIterationBound.image_add f n 1 a
private theorem morphismImageStepFun {A : Type*} (f : A → List A) (n : Nat) :
    image f (n + 1) = fun a => (f a).flatMap (image f n) := by
  funext a
  exact morphismImageStep f n a
end D5.S1.Words.Complexity.ThueMorseFactorRigidity

namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
private inductive Symbol
  | root | zero | one | starZero | starOne
  deriving DecidableEq
open Symbol
private instance symbolFintype : Fintype Symbol where
  elems := {root, zero, one, starZero, starOne}
  complete a := by cases a <;> simp
private def erase : Symbol → Bool
  | root | zero | starZero => false
  | one | starOne => true
private def isStar : Symbol → Bool
  | starZero | starOne => true
  | _ => false
private def theta : Symbol → List Symbol
  | root => [root, starOne, zero, zero, one]
  | zero => [zero, one, zero, zero, one]
  | one => [zero, one, zero]
  | starZero => [starZero, one, zero, zero, one]
  | starOne => [starZero, one, zero]
private def cube : Bool → List Bool
  | false => [false, true, false, false, true]
  | true => [false, true, false]
private theorem erase_image (n : Nat) (a : Symbol) :
    (image theta n a).map erase = (image cube) n (erase a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      cases a <;> simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, morphismImageStep, theta, cube, erase, morphismImageStep, ih, List.map_append]
private theorem image_root_step (n : Nat) :
    image theta (n + 1) root = image theta n root ++
      (image theta n starOne ++ image theta n zero ++ image theta n zero ++ image theta n one) := by
  simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, morphismImageStep, theta, List.append_assoc]
private theorem image_root_length_eq_zero (n : Nat) :
    (image theta n root).length = (image theta n zero).length := by
  have h := (erase_image n root).trans (erase_image n zero).symm
  simpa only [List.length_map] using congrArg List.length h
private theorem fib_three_steps (n : Nat) :
    Nat.fib (n + 3) = 2 * Nat.fib (n + 1) + Nat.fib n ∧
      Nat.fib (n + 4) = 3 * Nat.fib (n + 1) + 2 * Nat.fib n := by
  have h2 := Nat.fib_add_two (n := n)
  have h3 := Nat.fib_add_two (n := n + 1)
  have h4 := Nat.fib_add_two (n := n + 2)
  constructor <;> nlinarith
private theorem image_lengths (n : Nat) :
    (image theta n zero).length = Nat.fib (3 * n + 2) ∧
      (image theta n one).length = Nat.fib (3 * n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hf := fib_three_steps (3 * n + 1)
      have hz : 3 * (n + 1) + 2 = (3 * n + 1) + 4 := by omega
      have ho : 3 * (n + 1) + 1 = (3 * n + 1) + 3 := by omega
      constructor
      · simp only [morphismImageStep, theta, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.length_append, ih.1, ih.2]
        rw [hz]
        nlinarith [hf.2]
      · simp only [morphismImageStep, theta, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.length_append, ih.1, ih.2]
        rw [ho]
        nlinarith [hf.1]
private theorem image_root_length (n : Nat) :
    (image theta n root).length = Nat.fib (3 * n + 2) :=
  (image_root_length_eq_zero n).trans (image_lengths n).1
private def starCount (w : List Symbol) : Nat := (w.map isStar).count true
private theorem image_star_count (n : Nat) :
    starCount (image theta n root) = n ∧
    starCount (image theta n zero) = 0 ∧
    starCount (image theta n one) = 0 ∧
    starCount (image theta n starZero) = 1 ∧
    starCount (image theta n starOne) = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [morphismImageStep, theta, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        starCount, List.map_append, List.count_append] at *
      omega
private theorem star_head (n : Nat) :
    ∃ a tail, image theta n starOne = a :: tail ∧ isStar a = true := by
  have hboth :
      (∃ a tail, image theta n starZero = a :: tail ∧ isStar a = true) ∧
      (∃ a tail, image theta n starOne = a :: tail ∧ isStar a = true) := by
    induction n with
    | zero => exact ⟨⟨starZero, [], rfl, rfl⟩, ⟨starOne, [], rfl, rfl⟩⟩
    | succ n ih =>
        obtain ⟨a, tail, ha, hs⟩ := ih.1
        constructor
        · refine ⟨a, tail ++ image theta n one ++ image theta n zero ++ image theta n zero ++ image theta n one, ?_, hs⟩
          simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, morphismImageStep, theta, ha, List.append_assoc]
        · refine ⟨a, tail ++ image theta n one ++ image theta n zero, ?_, hs⟩
          simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, morphismImageStep, theta, ha, List.append_assoc]
  exact hboth.2
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
open Symbol
private theorem image_root_prefix (n : Nat) : image theta n root <+: image theta (n + 1) root := by
  rw [image_root_step]
  exact List.prefix_append _ _
private theorem image_root_prefix_of_le {m n : Nat} (h : m ≤ n) : image theta m root <+: image theta n root := by
  induction h with
  | refl => exact List.prefix_refl _
  | @step n h ih => exact ih.trans (image_root_prefix n)
private theorem root_length_exceeds (n : Nat) : n < (image theta (n + 1) root).length := by
  rw [image_root_length]
  have h := Nat.le_fib_self (show 5 ≤ 3 * (n + 1) + 2 by omega)
  omega
private def fixedSymbolWord (n : Nat) : Symbol :=
  (image theta (n + 1) root)[n]'(root_length_exceeds n)
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
open Symbol
private theorem fixedSymbolWord_eq_image_get (n r : Nat) (hr : r < (image theta n root).length) :
    fixedSymbolWord r = (image theta n root)[r]'hr := by
  have hn := image_root_prefix_of_le (Nat.le_max_left n (r + 1))
  have hrn := image_root_prefix_of_le (Nat.le_max_right n (r + 1))
  exact (hrn.getElem (root_length_exceeds r)).trans (hn.getElem hr).symm
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
open Symbol
private theorem no_star_of_count_zero (w : List Symbol) (hzero : starCount w = 0)
    (r : Nat) (hr : r < w.length) : isStar (w[r]'hr) = false := by
  have hn : true ∉ w.map isStar := List.not_mem_of_count_eq_zero hzero
  cases hs : isStar (w[r]'hr) with
  | false => rfl
  | true =>
      exact (hn (List.mem_map.mpr ⟨w[r]'hr, List.getElem_mem hr, hs⟩)).elim
private theorem only_first_of_count_one (w : List Symbol)
    (hhead : ∃ a tail, w = a :: tail ∧ isStar a = true)
    (hc : starCount w = 1) (r : Nat) (hr : r < w.length) :
    isStar (w[r]'hr) = true ↔ r = 0 := by
  obtain ⟨a, tail, ha, hs⟩ := hhead
  change (List.map isStar w).count true = 1 at hc
  rw [ha, List.map_cons, hs, List.count_cons_self] at hc
  have htail : starCount tail = 0 := by unfold starCount; omega
  cases r with
  | zero => simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, ha, hs]
  | succ r =>
      have hr' : r < tail.length := by simpa [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, ha] using hr
      have hz := no_star_of_count_zero tail htail r hr'
      simpa only [ha, List.getElem_cons_succ, hz, Bool.false_eq_true, Nat.succ_ne_zero]
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
open Symbol
private def extension (n : Nat) : List Symbol :=
  image theta n starOne ++ image theta n zero ++ image theta n zero ++ image theta n one
private theorem extension_only_first (n r : Nat) (hr : r < (extension n).length) :
    isStar ((extension n)[r]'hr) = true ↔ r = 0 := by
  apply only_first_of_count_one
  · obtain ⟨a, tail, ha, hs⟩ := star_head n
    refine ⟨a, tail ++ image theta n zero ++ image theta n zero ++ image theta n one, ?_, hs⟩
    simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, extension, ha, List.append_assoc]
  · have h := image_star_count n
    simp only [extension, starCount, List.map_append, List.count_append] at *
    omega
private theorem marker_strict {i j : Nat} (hij : i < j) :
    Nat.fib (3 * i + 2) < Nat.fib (3 * j + 2) :=
  (Nat.fib_lt_fib (by omega : 2 ≤ 3 * i + 2)).mpr (by omega)
private theorem finite_marker_positions (n r : Nat) (hr : r < (image theta n root).length) :
    isStar ((image theta n root)[r]'hr) = true ↔ ∃ i < n, r = Nat.fib (3 * i + 2) := by
  induction n generalizing r with
  | zero =>
      have hr0 : r = 0 := by simpa [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, morphismImageStep, D5.S1.Words.RankOneMorphismIterationBound.image_zero] using hr
      subst r
      simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, D5.S1.Words.RankOneMorphismIterationBound.image_zero, isStar]
  | succ n ih =>
      have hsplit : image theta (n + 1) root = image theta n root ++ extension n := image_root_step n
      by_cases hleft : r < (image theta n root).length
      · have htag : isStar ((image theta (n + 1) root)[r]'hr) =
            isStar ((image theta n root)[r]'hleft) := by
          simp only [hsplit, List.getElem_append_left hleft]
        rw [htag, ih r hleft]
        constructor
        · rintro ⟨i, hi, heq⟩; exact ⟨i, by omega, heq⟩
        · rintro ⟨i, hi, heq⟩
          have hne : i ≠ n := by intro h; subst i; rw [image_root_length, ← heq] at hleft; omega
          exact ⟨i, by omega, heq⟩
      · have hr' : r - (image theta n root).length < (extension n).length := by
          rw [hsplit, List.length_append] at hr
          omega
        have htag : isStar ((image theta (n + 1) root)[r]'hr) =
            isStar ((extension n)[r - (image theta n root).length]'hr') := by
          simp only [hsplit, List.getElem_append_right (by omega : (image theta n root).length ≤ r)]
        rw [htag, extension_only_first n _ hr']
        constructor
        · intro hz
          refine ⟨n, by omega, ?_⟩
          rw [← image_root_length]
          omega
        · rintro ⟨i, hi, heq⟩
          have hin : i = n := by
            by_contra hne
            have hsmall : i < n := by omega
            have h := marker_strict hsmall
            rw [← heq, ← image_root_length n] at h
            omega
          subst i
          rw [image_root_length, heq]
          omega
private theorem fixed_marker_positions (r : Nat) :
    isStar (fixedSymbolWord r) = true ↔ ∃ i, r = Nat.fib (3 * i + 2) := by
  rw [fixedSymbolWord, finite_marker_positions]
  constructor
  · rintro ⟨i, _, heq⟩; exact ⟨i, heq⟩
  · rintro ⟨i, heq⟩
    refine ⟨i, ?_, heq⟩
    have h := Nat.le_fib_add_one (3 * i + 2)
    omega
private theorem fixed_prefix_first_coordinate (n : Nat) :
    (List.ofFn (fun r : Fin (image theta n root).length => erase (fixedSymbolWord r.val))) =
      (image cube) n false := by
  have he : (image theta n root).map erase = (image cube) n false := erase_image n root
  rw [← he]
  change List.ofFn (erase ∘ (fun r : Fin (image theta n root).length => fixedSymbolWord r.val)) = _
  rw [← List.map_ofFn]
  congr 1
  have heq : (fun r : Fin (image theta n root).length => fixedSymbolWord r.val) = (image theta n root).get := by
    funext r
    exact fixedSymbolWord_eq_image_get n r.val r.isLt
  rw [heq, List.ofFn_get]
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
open Symbol
open D5.S1.Words D5.S0.Tower.GoldenGapWord
private theorem fibWord_cube_map (n : Nat) :
    (fibWord (n + 3)).map Bool.not = ((fibWord n).map Bool.not).flatMap cube := by
  simp only [fibWord, List.map_flatMap, List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro b _
  cases b <;> rfl
private theorem binaryImage_fibonacci (n : Nat) :
    (image cube) n false = (fibWord (3 * n)).map Bool.not := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [D5.S1.Words.RankOneMorphismIterationBound.image_succ,
        D5.S1.Words.RankOneMorphismIterationBound.subst, ih, show 3 * (n + 1) = 3 * n + 3 by omega, fibWord_cube_map]
private theorem fixed_first_coordinate (r : Nat) :
    erase (fixedSymbolWord r) = !(goldenWord r) := by
  have hr := root_length_exceeds r
  have hb : r < (fibWord (3 * (r + 1))).length := by
    rw [fibWord_length]
    rwa [image_root_length] at hr
  have hp := fixed_prefix_first_coordinate (r + 1)
  rw [binaryImage_fibonacci] at hp
  have hget := congrArg (fun w : List Bool => w[r]?) hp
  have h : erase (fixedSymbolWord r) = !((fibWord (3 * (r + 1)))[r]'hb) := by
    simpa [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, List.getElem?_ofFn, hr, hb] using hget
  have hg : goldenWord r = (fibWord (3 * (r + 1)))[r]'hb :=
    goldenWord_eq_fibWord_get _ _ hb
  rwa [← hg] at h
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
private def expandedTag (q r : Nat) : Bool :=
  isStar (fixedSymbolWord (r / q)) && decide (r % q = 0)
private theorem expanded_tag_positions (q : Nat) (hq : 0 < q) (r : Nat) :
    expandedTag q r = true ↔ ∃ i, r = q * Nat.fib (3 * i + 2) := by
  simp only [expandedTag, Bool.and_eq_true, decide_eq_true_eq, fixed_marker_positions]
  constructor
  · rintro ⟨⟨i, hi⟩, hm⟩
    refine ⟨i, ?_⟩
    have h := Nat.div_add_mod r q
    rw [hi, hm, Nat.add_zero] at h
    exact h.symm
  · rintro ⟨i, rfl⟩
    simp only [Nat.mul_div_right _ hq, Nat.mul_mod_right]
    exact ⟨⟨i, rfl⟩, True.intro⟩
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic.Synchronize
variable {A : Type*}
private def letterExpand (q : Nat) (a : A) : List (A × Fin q) :=
  List.ofFn (fun j => (a, j))
private def expand (q : Nat) (word : List A) : List (A × Fin q) :=
  word.flatMap (letterExpand q)
private def expandedEntry (q : Nat) (hq : 0 < q) (word : List A)
    (r : Fin (q * word.length)) : A × Fin q :=
  (word[r.val / q]'((Nat.div_lt_iff_lt_mul hq).mpr (by
    simpa only [Nat.mul_comm] using r.isLt)), ⟨r.val % q, Nat.mod_lt _ hq⟩)
private theorem expand_as_indexed (q : Nat) (hq : 0 < q) (word : List A) :
    expand q word = List.ofFn (expandedEntry q hq word) := by
  rw [List.ofFn_mul']
  unfold expand
  rw [List.flatMap_def]
  congr 1
  conv_lhs => rw [← List.ofFn_get word]
  rw [List.map_ofFn]
  congr 1
  funext i
  change List.ofFn (fun j : Fin q => (word[i.val], j)) = _
  congr 1
  funext j
  apply Prod.ext
  · change word[i.val]'i.isLt = word[(q * i.val + j.val) / q]'_
    congr 1
    rw [Nat.add_comm (q * i.val), Nat.add_mul_div_left _ _ hq,
      Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  · apply Fin.ext
    change j.val = (q * i.val + j.val) % q
    rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt j.isLt]
private def expandedTheta (theta : A → List A) (q : Nat) (hq : 0 < q)
    (state : A × Fin q) : List (A × Fin q) :=
  List.ofFn (fun j : Fin (theta state.1).length =>
    expandedEntry q hq (theta state.1)
      ⟨state.2.val * (theta state.1).length + j.val, by
        have hj := j.isLt
        have hi := Nat.mul_le_mul_right (theta state.1).length (Nat.succ_le_of_lt state.2.isLt)
        nlinarith⟩)
private theorem expandedTheta_commutes_letter (theta : A → List A)
    (q : Nat) (hq : 0 < q) (a : A) :
    (letterExpand q a).flatMap (expandedTheta theta q hq) = expand q (theta a) := by
  rw [expand_as_indexed q hq, List.ofFn_mul]
  simp only [letterExpand, List.flatMap_def, List.map_ofFn, expandedTheta,
    Function.comp_def]
private theorem expandedTheta_length (theta : A → List A) (q : Nat) (hq : 0 < q)
    (state : A × Fin q) :
    (expandedTheta theta q hq state).length = (theta state.1).length :=
  List.length_ofFn
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic.Synchronize
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
open Symbol D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic.Synchronize
open D5.S1.Words
private theorem theta_lengths (a : Symbol) : (theta a).length = 3 ∨ (theta a).length = 5 := by
  cases a <;> decide
private theorem expandedTheta_root_head (q : Nat) (hq : 0 < q) :
    (expandedTheta theta q hq (root, ⟨0, hq⟩)).head? = some (root, ⟨0, hq⟩) := by
  simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, expandedTheta, theta, expandedEntry, List.ofFn_succ]
private theorem expandedTheta_prolongable (q : Nat) (hq : 0 < q) :
    ∃ tail, expandedTheta theta q hq (root, ⟨0, hq⟩) = (root, ⟨0, hq⟩) :: tail ∧
      tail ≠ [] := by
  obtain ⟨tail, ht⟩ := List.head?_eq_some_iff.mp (expandedTheta_root_head q hq)
  refine ⟨tail, ht, ?_⟩
  intro hz
  have hl := expandedTheta_length theta q hq (root, ⟨0, hq⟩)
  rw [ht, hz] at hl
  simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, theta] at hl
private def expandedFixedWord (q : Nat) (hq : 0 < q) (r : Nat) : Symbol × Fin q :=
  (fixedSymbolWord (r / q), ⟨r % q, Nat.mod_lt r hq⟩)
private def taggedCoding {q : Nat} (block : Bool → Fin q → Bool)
    (state : Symbol × Fin q) : Bool × Bool :=
  (block (erase state.1) state.2, isStar state.1 && decide (state.2.val = 0))
private theorem coded_coordinates (q : Nat) (hq : 0 < q) (block : Bool → Fin q → Bool) (r : Nat) :
    (taggedCoding block (expandedFixedWord q hq r)).1 =
      block (!(goldenWord (r / q))) ⟨r % q, Nat.mod_lt r hq⟩ ∧
    ((taggedCoding block (expandedFixedWord q hq r)).2 = true ↔
      ∃ i, r = q * Nat.fib (3 * i + 2)) := by
  constructor
  · exact congrArg (fun a => block a ⟨r % q, Nat.mod_lt r hq⟩) (fixed_first_coordinate (r / q))
  · exact expanded_tag_positions q hq r
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
open Symbol D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic.Synchronize
private theorem expandedImage_commutes (q : Nat) (hq : 0 < q) (n : Nat) (a : Symbol) :
    (letterExpand q a).flatMap (image (expandedTheta theta q hq) n) = expand q (image theta n a) := by
  induction n generalizing a with
  | zero => simp [D5.S1.Words.RankOneMorphismIterationBound.image, expand]
  | succ n ih =>
      simp only [morphismImageStepFun, morphismImageStep, List.flatMap_assoc, expand]
      calc
        _ = (expand q (theta a)).flatMap (image (expandedTheta theta q hq) n) := by
          rw [← expandedTheta_commutes_letter theta q hq a]
          simp only [letterExpand, List.flatMap_assoc]
        _ = (theta a).flatMap (fun b => expand q (image theta n b)) := by
          unfold expand
          rw [List.flatMap_assoc]
          congr 1
          funext b
          exact ih b
        _ = _ := by simp only [expand]
private theorem expandedImage_prefix (q : Nat) (hq : 0 < q) (n : Nat) :
    image (expandedTheta theta q hq) n (root, ⟨0, hq⟩) <+: expand q (image theta n root) := by
  have hs : [(root, (⟨0, hq⟩ : Fin q))] <+: letterExpand q root := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    subst q
    simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, letterExpand, List.ofFn_succ]
  have hp := hs.flatMap (image (expandedTheta theta q hq) n)
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    expandedImage_commutes] using hp
private theorem expandedImage_length_lower (q : Nat) (hq : 0 < q) (n : Nat)
    (state : Symbol × Fin q) : n + 1 ≤ (image (expandedTheta theta q hq) n state).length := by
  induction n generalizing state with
  | zero => simp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, D5.S1.Words.RankOneMorphismIterationBound.image_zero]
  | succ n ih =>
      have lower (word : List (Symbol × Fin q)) :
          (n + 1) * word.length ≤ (word.flatMap (image (expandedTheta theta q hq) n)).length := by
        induction word with
        | nil => simp
        | cons a word hw =>
            simp only [List.length_cons, List.flatMap_cons, List.length_append]
            have ha := ih a
            nlinarith
      have hl := lower (expandedTheta theta q hq state)
      have ht := theta_lengths state.1
      rw [expandedTheta_length] at hl
      rw [morphismImageStep]
      change n + 1 + 1 ≤ ((expandedTheta theta q hq state).flatMap
        (image (expandedTheta theta q hq) n)).length
      rcases ht with ht | ht <;> rw [ht] at hl <;> nlinarith
private theorem expandedFixedWord_eq_image_get (q : Nat) (hq : 0 < q) (n r : Nat)
    (hr : r < (image (expandedTheta theta q hq) n (root, ⟨0, hq⟩)).length) :
    expandedFixedWord q hq r =
      (image (expandedTheta theta q hq) n (root, ⟨0, hq⟩))[r]'hr := by
  have hp := expandedImage_prefix q hq n
  have hb : r < (expand q (image theta n root)).length := lt_of_lt_of_le hr hp.length_le
  have hlen : (expand q (image theta n root)).length = q * (image theta n root).length := by
    rw [expand_as_indexed q hq, List.length_ofFn]
  have hparent : r / q < (image theta n root).length := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    rw [hlen] at hb
    simpa only [Nat.mul_comm] using hb
  have hget := hp.getElem hr
  simp only [expand_as_indexed q hq, List.getElem_ofFn, expandedEntry] at hget
  rw [hget]
  unfold expandedFixedWord
  congr 1
  exact fixedSymbolWord_eq_image_get n (r / q) hparent
private theorem expanded_fixed_realization (q : Nat) (hq : 0 < q) :
    (∃ tail, expandedTheta theta q hq (root, ⟨0, hq⟩) =
      (root, ⟨0, hq⟩) :: tail ∧ tail ≠ []) ∧
    (∀ n r (hr : r < (image (expandedTheta theta q hq) n (root, ⟨0, hq⟩)).length),
      expandedFixedWord q hq r =
        (image (expandedTheta theta q hq) n (root, ⟨0, hq⟩))[r]'hr) ∧
    (∀ bound, ∃ n, bound < (image (expandedTheta theta q hq) n (root, ⟨0, hq⟩)).length) := by
  refine ⟨expandedTheta_prolongable q hq, expandedFixedWord_eq_image_get q hq, ?_⟩
  intro bound
  exact ⟨bound, Nat.lt_of_lt_of_le (Nat.lt_succ_self bound)
    (expandedImage_length_lower q hq bound _)⟩
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
open D5.S1.Words.Complexity D5.S1.Words.Complexity.UniformWordRecurrence.Core D5.S1.Words.Complexity.UniformWordRecurrence D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic.Synchronize
private theorem coded_core_coordinates (k r : Nat) :
    (taggedCoding (fun a j => Bool.xor a (thueMorse j))
      (expandedFixedWord (2 ^ k) (Nat.two_pow_pos k) r)).1 = core k r ∧
    ((taggedCoding (fun a j => Bool.xor a (thueMorse j))
      (expandedFixedWord (2 ^ k) (Nat.two_pow_pos k) r)).2 = true ↔
        ∃ i, r = 2 ^ k * Nat.fib (3 * i + 2)) := by
  exact coded_coordinates (2 ^ k) (Nat.two_pow_pos k) _ r
end D5.S1.Words.Complexity.ThueMorseFactorRigidity.Morphic
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
/-
Binding conventions for Michel Rigo, Manon Stipulanti and Markus A. Whiteland,
Characterizations of families of morphisms and words via binomial complexities,
arXiv:2201.04603v2 (6 December 2022), Question C in Section 7.1.
The source uses A* for finite words over a finite alphabet A, A≤k for words of
length at most k, and L_n(w) for the set of length-n contiguous factors of an
infinite word w. Its Definition 1.1 is the number of increasing position
selections spelling a prescribed finite word. The imported owner
VivionBinomialConverseFails.scatteredCount is this definition, with the empty
pattern count equal to one. Definition 1.2 says u ∼ₖ v exactly when all such
counts agree for every x ∈ A≤k; the imported BinomialEquivalent is that
profile equality. Definition 1.3 says b_w^(k)(n) is the cardinality of
L_n(w)/∼ₖ; the imported binomialComplexity is its cardinality of represented
profiles. Definition 1.4 says f ≺ g when f(n) < g(n) for infinitely many n.
The factor complexity p_w(n) is the cardinality of L_n(w), represented here
by factorComplexity. The source's Question C asks for an unbounded b^(1), the
strict chain through b^(ℓ), and b^(ℓ) = p; its optional pure-morphic clause is
kept as the construction route rather than added as an extra hypothesis.
The binding alphabet Fin 4 records the claimed at-most-four-letter witness.
The implication 2 ≤ ℓ is the feasible range: Remark 7.1 and the source's
unboundedness requirement rule out ℓ = 1.
-/
noncomputable def factorComplexity (word : Nat → Fin 4) (n : Nat) : Nat :=
  (wordFactorSet word n).card

noncomputable def binomialAt (word : Nat → Fin 4) (k n : Nat) : Nat :=
  binomialComplexity word k n

def Prec (f g : Nat → Nat) : Prop :=
  Set.Infinite {n | f n < g n}

def Unbounded (f : Nat → Nat) : Prop :=
  ∀ bound : Nat, ∃ n : Nat, bound < f n

def Hierarchy (word : Nat → Fin 4) (ell : Nat) : Prop :=
  Unbounded (binomialAt word 1) ∧
    (∀ j : Nat, 1 ≤ j → j < ell →
      Prec (binomialAt word j) (binomialAt word (j + 1))) ∧
    (∀ n : Nat, binomialAt word ell n = factorComplexity word n)

def claim : Prop :=
  ∀ ell : Nat, 2 ≤ ell → ∃ word : Nat → Fin 4, Hierarchy word ell

end D5.S1.Words.Complexity.ThueMorseFactorRigidity
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
private theorem hierarchy_of_core_and_marker (x y : Nat → Bool) (ell : Nat)
    (hunbounded : ∀ bound : Nat, ∃ n : Nat, bound < binomialComplexity y 1 n)
    (hstrict : ∀ j : Nat, 1 ≤ j → j < ell →
      Set.Infinite {n | binomialComplexity x j n < binomialComplexity x (j + 1) n})
    (hx : ∀ n, Set.InjOn (binomialProfile ell)
      (wordFactorSet x n : Set (Fin n → Bool)))
    (hy : ∀ n, Set.InjOn (binomialProfile ell)
      (wordFactorSet y n : Set (Fin n → Bool)))
    (hlift : ∀ n, ∀ u ∈ wordFactorSet x n,
      (fun r => (u r, false)) ∈ wordFactorSet (fun i => (x i, y i)) n) :
    Hierarchy (pairCode ∘ (fun i => (x i, y i))) ell := by
  let z := fun i => (x i, y i)
  have hc (k n : Nat) : binomialComplexity (pairCode ∘ z) k n = binomialComplexity z k n :=
    complexity_map_eq_of_leftInverse pairCode pairDecode pairCode_leftInverse z k n
  have hf (n : Nat) : factorComplexity (pairCode ∘ z) n = (wordFactorSet z n).card :=
    factor_card_map_eq_of_injective pairCode pairCode_leftInverse.injective z n
  refine ⟨?_, ?_, ?_⟩
  · intro bound
    obtain ⟨n, hn⟩ := hunbounded bound
    refine ⟨n, ?_⟩
    change bound < binomialComplexity (pairCode ∘ z) 1 n
    rw [hc]
    exact hn.trans_le (complexity_map_le Prod.snd z 1 n)
  · intro j hj hjell
    apply (hstrict j hj hjell).mono
    intro n hn
    change binomialComplexity (pairCode ∘ z) j n < binomialComplexity (pairCode ∘ z) (j + 1) n
    rw [hc, hc]
    exact strict_lifts_through_constant_tag x y false (by omega) (hlift n) hn
  · intro n
    change binomialComplexity (pairCode ∘ z) ell n = factorComplexity (pairCode ∘ z) n
    rw [hc, hf]
    exact (complexity_eq_factor_iff z ell n).mpr
      (product_profile_injective x y ell n (hx n) (hy n))
end D5.S1.Words.Complexity.ThueMorseFactorRigidity
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection D5.S1.Words.Complexity.LacunaryBinomialMarkers
private theorem marker_hierarchy_two {p : Nat → Nat} (hp : Lacunary p) :
    Hierarchy (boolCode ∘ markerWord p) 2 := by
  have hc (k n : Nat) :
      binomialComplexity (boolCode ∘ markerWord p) k n = binomialComplexity (markerWord p) k n :=
    complexity_map_eq_of_leftInverse boolCode boolDecode boolCode_leftInverse _ k n
  have hf (n : Nat) : factorComplexity (boolCode ∘ markerWord p) n =
      (wordFactorSet (markerWord p) n).card :=
    factor_card_map_eq_of_injective boolCode boolCode_leftInverse.injective _ n
  refine ⟨?_, ?_, ?_⟩
  · intro bound
    obtain ⟨n, hn⟩ := marker_unbounded_abelian hp bound
    refine ⟨n, ?_⟩
    change bound < binomialComplexity (boolCode ∘ markerWord p) 1 n
    simpa only [hc] using hn
  · intro j hj hjell
    have hjone : j = 1 := by exact Nat.eq_of_le_of_lt_succ hj hjell
    subst j
    apply (Set.Ici_infinite (2 : Nat)).mono
    intro n hn
    change binomialComplexity (boolCode ∘ markerWord p) 1 n <
      binomialComplexity (boolCode ∘ markerWord p) 2 n
    rw [hc, hc]
    exact marker_strict_one_two hp n hn
  · intro n
    change binomialComplexity (boolCode ∘ markerWord p) 2 n =
      factorComplexity (boolCode ∘ markerWord p) n
    rw [hc, hf]
    exact marker_complexity_two hp n
end D5.S1.Words.Complexity.ThueMorseFactorRigidity
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection D5.S1.Words.Complexity.LacunaryBinomialMarkers
private theorem hierarchy_with_lacunary_marker (ell : Nat) (hell : 2 ≤ ell) (x : Nat → Bool)
    (p : Nat → Nat) (hp : Lacunary p)
    (hrecur : ∀ n, ∀ u ∈ wordFactorSet x n,
      ∃ R, ∀ s, ∃ t, s ≤ t ∧ t + n ≤ s + R ∧ u = wordFactor x n t)
    (hstrict : ∀ j : Nat, 1 ≤ j → j < ell →
      Set.Infinite {n | binomialComplexity x j n < binomialComplexity x (j + 1) n})
    (hx : ∀ n, Set.InjOn (binomialProfile ell)
      (wordFactorSet x n : Set (Fin n → Bool))) :
    Hierarchy (pairCode ∘ (fun i => (x i, markerWord p i))) ell := by
  apply hierarchy_of_core_and_marker x (markerWord p) ell
    (marker_unbounded_abelian hp) hstrict hx
  · intro n u hu v hv heq
    exact marker_profile_two_injective hp n hu hv
      (profile_eq_mono hell heq)
  · exact constant_tag_factors_of_recurrence x (markerWord p) hrecur
      (marker_zero_intervals hp)
end D5.S1.Words.Complexity.ThueMorseFactorRigidity
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence.Core D5.S1.Words.Complexity.LacunaryBinomialMarkers D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection D5.S1.Words.Complexity.UniformWordRecurrence
end D5.S1.Words.Complexity.ThueMorseFactorRigidity
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence.Core D5.S1.Words.Complexity.ThueMorsePositionalRecovery
end D5.S1.Words.Complexity.ThueMorseFactorRigidity
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.UniformWordRecurrence.Core D5.S1.Words.Complexity.ThueMorsePositionalRecovery
end D5.S1.Words.Complexity.ThueMorseFactorRigidity
namespace D5.S1.Words.Complexity.ThueMorseFactorRigidity
open Morphic Morphic.Synchronize
open D5.S1.Words.Complexity.LacunaryBinomialMarkers
open D5.S1.Words.Complexity.LacunaryBinomialMarkers.Projection
open D5.S1.Words.Complexity.UniformWordRecurrence.Core
open D5.S1.Words.Complexity.ThueMorsePositionalRecovery

private theorem coded_hierarchy (ell : Nat) (hell : 2 ≤ ell) :
    ∃ (q : Nat) (hq : 0 < q) (code : Morphic.Symbol × Fin q → Fin 4),
      Hierarchy (code ∘ Morphic.expandedFixedWord q hq) ell ∧
      (∃ tail, Morphic.Synchronize.expandedTheta Morphic.theta q hq
        (Morphic.Symbol.root, ⟨0, hq⟩) = (Morphic.Symbol.root, ⟨0, hq⟩) :: tail ∧ tail ≠ []) ∧
      (∀ n r (hr : r < (image (expandedTheta theta q hq) n
          (Morphic.Symbol.root, ⟨0, hq⟩)).length),
        Morphic.expandedFixedWord q hq r =
          (image (expandedTheta theta q hq) n (Morphic.Symbol.root, ⟨0, hq⟩))[r]'hr) ∧
      (∀ bound, ∃ n, bound < (image (expandedTheta theta q hq) n
        (Morphic.Symbol.root, ⟨0, hq⟩)).length) := by
  by_cases ht : ell = 2
  · subst ell
    let code : Morphic.Symbol × Fin 1 → Fin 4 := fun a => boolCode (isStar a.1)
    refine ⟨1, by decide, code, ?_, expanded_fixed_realization 1 (by decide)⟩
    have hw : code ∘ expandedFixedWord 1 (by decide) = boolCode ∘ markerWord marker := by
      funext r
      apply congrArg boolCode
      change isStar (fixedSymbolWord (r / 1)) = markerWord marker r
      simp only [Nat.div_one]
      apply Bool.eq_iff_iff.mpr
      rw [fixed_marker_positions, markerWord_eq_true]
      simp only [marker, eq_comm]
    rw [hw]
    exact marker_hierarchy_two marker_lacunary
  · let k := ell - 2
    have hk : 1 ≤ k := by dsimp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, k]; omega
    have he : ell = k + 2 := by dsimp [-D5.S1.Words.RankOneMorphismIterationBound.image_succ, k]; omega
    let block : Bool → Fin (2 ^ k) → Bool := fun a j => Bool.xor a (thueMorse j)
    let code : Morphic.Symbol × Fin (2 ^ k) → Fin 4 := pairCode ∘ taggedCoding block
    refine ⟨2 ^ k, Nat.two_pow_pos k, code, ?_,
      expanded_fixed_realization (2 ^ k) (Nat.two_pow_pos k)⟩
    have hw : code ∘ expandedFixedWord (2 ^ k) (Nat.two_pow_pos k) =
        pairCode ∘ (fun r => (core k r, markerWord (fun i => 2 ^ k * marker i) r)) := by
      funext r
      apply congrArg pairCode
      apply Prod.ext
      · exact (coded_core_coordinates k r).1
      · apply Bool.eq_iff_iff.mpr
        rw [(coded_core_coordinates k r).2, markerWord_eq_true]
        simp only [marker, eq_comm]
    rw [hw, he]
    apply hierarchy_with_lacunary_marker (k + 2) (by omega) (core k)
      (fun i => 2 ^ k * marker i)
      (scaled_lacunary marker_lacunary (2 ^ k) (Nat.two_pow_pos k)) (core_recurrent k)
    · intro j hj hjk
      by_cases hfirst : j = 1
      · subst j; exact D5.S1.Words.Complexity.UniformWordRecurrence.core_first_strict k hk
      by_cases hlast : j = k + 1
      · subst j; exact core_last_strict k
      exact core_middle_strict k j (by omega) (by omega)
    · exact D5.S1.Words.Complexity.ThueMorsePositionalRecovery.Rigidity.top_profile_injectivity k

private theorem expandedImage_iterate (q : Nat) (hq : 0 < q) (n : Nat)
    (a : Morphic.Symbol × Fin q) :
    image (expandedTheta theta q hq) n a =
      (List.flatMap (expandedTheta theta q hq))^[n] [a] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [D5.S1.Words.RankOneMorphismIterationBound.image_succ,
      D5.S1.Words.RankOneMorphismIterationBound.subst, Function.iterate_succ_apply', ← ih]

theorem morphic_result (ell : Nat) (hell : 2 ≤ ell) :
    ∃ (A : Type) (sigma : A → List A) (a : A) (u : Nat → A) (code : A → Fin 4),
      Finite A ∧ Hierarchy (code ∘ u) ell ∧
      (∃ tail, sigma a = a :: tail ∧ tail ≠ []) ∧
      (∀ n r (hr : r < ((List.flatMap sigma)^[n] [a]).length),
        u r = ((List.flatMap sigma)^[n] [a]).get ⟨r, hr⟩) ∧
      (∀ bound, ∃ n, bound < ((List.flatMap sigma)^[n] [a]).length) := by
  obtain ⟨q, hq, code, hh, hp, hi, hg⟩ := coded_hierarchy ell hell
  refine ⟨Morphic.Symbol × Fin q, expandedTheta theta q hq,
    (Morphic.Symbol.root, ⟨0, hq⟩), expandedFixedWord q hq, code,
    inferInstance, hh, hp, ?_, ?_⟩
  · intro n r hr
    have hr' : r < (image (expandedTheta theta q hq) n (Morphic.Symbol.root, ⟨0, hq⟩)).length := by
      simpa only [expandedImage_iterate] using hr
    have hi' := hi n r hr'
    simpa only [expandedImage_iterate, List.get_eq_getElem] using hi'
  · intro bound
    obtain ⟨n, hn⟩ := hg bound
    refine ⟨n, ?_⟩
    rwa [← expandedImage_iterate]

theorem result : claim := by
  intro ell hell
  obtain ⟨A, sigma, a, u, code, _, hh, _⟩ := morphic_result ell hell
  exact ⟨code ∘ u, hh⟩
end D5.S1.Words.Complexity.ThueMorseFactorRigidity
