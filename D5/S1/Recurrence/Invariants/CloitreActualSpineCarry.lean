/- GID: D5/S1/Recurrence/Invariants/CloitreActualSpineCarry
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreActualSpineCarry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional occurrence-preserving actual Cloitre spine and scalar carry conservation. -/

import D5.S1.Recurrence.Invariants.CloitreActualEndpointPhase
import D5.S0.Tower.GoldenGapZeckendorf
import D5.S1.Deficit.GoldenPhaseDeficit
import Mathlib.Data.Tree.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace D5.S1.Recurrence.Invariants.CloitreActualSpineCarry

open D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open D5.S1.Recurrence.Invariants.CloitreActualEndpointPhase
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Deficit.GoldenPhaseDeficit
open D5.S0.Conventions

local notation "F" => Nat.fib
local notation "G" => D5.S1.Phase.SelfReference.GoldenShellRecurrence.g

/-- The finite actual ordered split tree, with positive terminal labels one and two. -/
def actualTree (n : ℕ) : BinaryTree ℕ :=
  if _hz : n = 0 then .nil else
  if _hn : n < 3 then .node n .nil .nil else
    .node n (actualTree (g n)) (actualTree (n - g n))
termination_by n
decreasing_by
  all_goals
    have hg := actual_foundations.1 n (d n) (by omega)
    change 1 ≤ g n ∧ g n ≤ n - 1 at hg
    omega

/-- Root label; zero is the exterior convention for the empty tree. -/
def rootLabel : BinaryTree ℕ → ℕ
  | .nil => 0
  | .node n _ _ => n

/-- An address selects a complete subtree, preserving node occurrences. False is left. -/
def subtreeAt : BinaryTree ℕ → List Bool → Option (BinaryTree ℕ)
  | tree, [] => some tree
  | .nil, _ :: _ => none
  | .node _ left right, b :: path => subtreeAt (if b then right else left) path

noncomputable section

/-- Structural sum of scalar carries over internal nodes. Terminal labels contribute zero. -/
def totalCarry : BinaryTree ℕ → ℤ
  | .nil => 0
  | .node n left right =>
    if n < 3 then 0 else
      beattyDeficit (rootLabel left) (rootLabel right) + totalCarry left + totalCarry right

/-- Endpoint threshold, retaining the numerical width. -/
def threshold (t : ℕ) : ℕ := 12 * t + 7

/-- The actual selected parity decides which ordered child retains the offset. -/
def retainedBit (t j : ℕ) : Bool :=
  if (F (j - 1) + t - 1) % 2 = 0 then false else true

/-- Rank decrement of the offset child. -/
def stepSize (t j : ℕ) : ℕ :=
  if (F (j - 1) + t - 1) % 2 = 0 then 1 else 2

/-- Rank of the opposite Fibonacci anchor. -/
def anchorRank (t j : ℕ) : ℕ :=
  if (F (j - 1) + t - 1) % 2 = 0 then j - 2 else j - 1

/-- Successive ranks; the first subthreshold rank is the only stopping point claimed. -/
def rank (t k i : ℕ) : ℕ := (fun j => j - stepSize t j)^[i] k

/-- Occurrence addresses obtained by appending the offset child's ordered side. -/
def address (t k : ℕ) : ℕ → List Bool
  | 0 => []
  | i + 1 => address t k i ++ [retainedBit t (rank t k i)]

/-- The ordered split, scalar defects, zero split carry, and width-one boundary. -/
def SplitFacts (t j : ℕ) : Prop :=
  let N := F j + t
  let retained := F (j - stepSize t j) + t
  let anchor := F (anchorRank t j)
  g N = (if retainedBit t j then anchor else retained) ∧
  N - g N = (if retainedBit t j then retained else anchor) ∧
  canonicalDefect N = widthDefect t ∧
  canonicalDefect retained = widthDefect t ∧ canonicalDefect anchor = 0 ∧
  beattyDeficit (g N) (N - g N) = 0 ∧
  (2 ≤ t →
    (0 < canonicalDefect (g N) ↔ retainedBit t j = false) ∧
    (0 < canonicalDefect (N - g N) ↔ retainedBit t j = true)) ∧
  (t = 1 → canonicalDefect (g N) = 0 ∧ canonicalDefect (N - g N) = 0)

/-- Six congruence transitions, using subtraction on the full rank before reduction. -/
def CongruenceControl (t j : ℕ) : Prop :=
  (t % 2 = 1 → j % 3 = 0 → stepSize t j = 2 ∧ (j - stepSize t j) % 3 = 1) ∧
  (t % 2 = 1 → j % 3 = 1 → stepSize t j = 1 ∧ (j - stepSize t j) % 3 = 0) ∧
  (t % 2 = 1 → j % 3 = 2 → stepSize t j = 2 ∧ (j - stepSize t j) % 3 = 0) ∧
  (t % 2 = 0 → j % 3 = 0 → stepSize t j = 1 ∧ (j - stepSize t j) % 3 = 2) ∧
  (t % 2 = 0 → j % 3 = 1 → stepSize t j = 2 ∧ (j - stepSize t j) % 3 = 2) ∧
  (t % 2 = 0 → j % 3 = 2 → stepSize t j = 1 ∧ (j - stepSize t j) % 3 = 1)

set_option maxHeartbeats 2000000 in
-- The complete tree telescope and occurrence spine require nested inductions.
/-- Complete conditional spine theorem on one actual root tree. All anchor and terminal
subtrees are complete occurrences of that tree; scalar totals do not assert unit-bit
carries or individual internal-anchor carries vanish. -/
theorem full22_2 (U : ℕ → ℕ) (h : Hyp21_1 U) :
    (∀ n : ℕ, 1 ≤ n → totalCarry (actualTree n) = (canonicalDefect n : ℤ)) ∧
    ∀ t k : ℕ, 1 ≤ t → threshold t ≤ k →
      (∀ j : ℕ, threshold t ≤ j → SplitFacts t j ∧ CongruenceControl t j) ∧
      ∃ L : ℕ,
        0 < L ∧ rank t k L < threshold t ∧
        (rank t k L = threshold t - 1 ∨ rank t k L = threshold t - 2) ∧
        (∀ i : ℕ, i < L → threshold t ≤ rank t k i ∧
          rank t k (i + 1) = rank t k i - stepSize t (rank t k i) ∧
          (stepSize t (rank t k i) = 1 ∨ stepSize t (rank t k i) = 2)) ∧
        (∀ i : ℕ, i ≤ L →
          subtreeAt (actualTree (F k + t)) (address t k i) =
            some (actualTree (F (rank t k i) + t))) ∧
        (∀ i : ℕ, i < L →
          subtreeAt (actualTree (F k + t))
              (address t k i ++ [!(retainedBit t (rank t k i))]) =
            some (actualTree (F (anchorRank t (rank t k i)))) ∧
          totalCarry (actualTree (F (anchorRank t (rank t k i)))) = 0 ∧
          totalCarry (actualTree (F (rank t k i) + t)) =
            totalCarry (actualTree (F (rank t k (i + 1)) + t))) ∧
        canonicalDefect (F (rank t k L) + t) = widthDefect t ∧
        totalCarry (actualTree (F k + t)) =
          totalCarry (actualTree (F (rank t k L) + t)) ∧
        totalCarry (actualTree (F (rank t k L) + t)) = (widthDefect t : ℤ) := by
  have label : ∀ n : ℕ, rootLabel (actualTree n) = n := by
    intro n
    rw [actualTree]
    split
    · subst n; rfl
    · split <;> rfl
  have shiftRead : ∀ n : ℕ, displacementDecode n = n + G n := by
    intro n
    have hr := displacement_decode_eq_beatty_floor n
    have he : ((n : ℝ) + 1) * Real.goldenRatio =
        ((n : ℝ) + 1) * Real.goldenRatio⁻¹ + (n + 1 : ℕ) := by
      rw [Real.inv_goldenRatio]
      have := Real.goldenRatio_add_goldenConj
      push_cast
      nlinarith
    rw [he, Int.floor_add_natCast,
      ← Int.natCast_floor_eq_floor (by positivity)] at hr
    change (displacementDecode n : ℤ) = (G n : ℤ) + (n + 1 : ℕ) - 1 at hr
    exact_mod_cast (show (displacementDecode n : ℤ) = (n : ℤ) + (G n : ℤ) by omega)
  have carryRead : ∀ a b : ℕ, beattyDeficit a b = (G a : ℤ) + (G b : ℤ) - (G (a+b) : ℤ) := by
    intro a b
    have hs : ∀ n : ℕ, goldenShift n = (n : ℤ) + (G n : ℤ) := by
      intro n
      have hd := displacement_decode_eq_beatty_floor n
      rw [shiftRead n] at hd
      unfold goldenShift
      push_cast at hd
      omega
    rw [beattyDeficit, hs a, hs b, hs (a+b)]
    push_cast
    ring
  have c1 : C 1 = 1 := rfl
  have c2 : C 2 = 1 := rfl
  have g1 : G 1 = 1 := by
    have := (h.anchors 2 (by omega)).2.2
    norm_num [Nat.fib] at this
    exact this
  have g2 : G 2 = 1 := by
    have := (h.anchors 3 (by omega)).2.2
    norm_num [Nat.fib] at this
    exact this
  have telescope : ∀ n : ℕ, 1 ≤ n →
      totalCarry (actualTree n) = (C n : ℤ) - (G n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn3 : n < 3
      · have cases : n = 1 ∨ n = 2 := by omega
        rcases cases with rfl | rfl
        · rw [actualTree, dif_neg (by omega), dif_pos (by omega)]
          simp [totalCarry, c1, g1]
        · rw [actualTree, dif_neg (by omega), dif_pos (by omega)]
          simp [totalCarry, c2, g2]
      · have hg := actual_foundations.1 n (d n) (by omega)
        change 1 ≤ g n ∧ g n ≤ n - 1 at hg
        have hc : 1 ≤ n - g n := by omega
        have sum : g n + (n - g n) = n := by omega
        have recurrence :=  actual_foundations.2 n (by omega)
        rw [actualTree, dif_neg (by omega), dif_neg hn3, totalCarry, if_neg hn3,
          label, label, ih (g n) (by omega) hg.1, ih (n-g n) (by omega) hc,
          carryRead, sum, recurrence]
        push_cast
        ring
  have totalDefect : ∀ n : ℕ, 1 ≤ n → totalCarry (actualTree n) = (canonicalDefect n : ℤ) := by
    intro n hn
    rw [telescope n hn, canonicalDefect, Nat.cast_sub (h.bounds n hn).2.1]
  refine ⟨totalDefect, ?_⟩
  intro t k ht hk
  have rBounds : ∀ j : ℕ, stepSize t j = 1 ∨ stepSize t j = 2 := by
    intro j
    unfold stepSize
    split <;> simp
  have rankSucc : ∀ i : ℕ, rank t k (i+1) = rank t k i - stepSize t (rank t k i) := by
    intro i
    exact Function.iterate_succ_apply' _ _ _
  have profile : ∀ ell : ℕ, threshold t - 2 ≤ ell →
      C (F ell+t) = F (ell-1)+t ∧ G (F ell+t) = F (ell-1)+G t ∧
      canonicalDefect (F ell+t) = widthDefect t := by
    intro ell hell
    have hell3 : 3 ≤ ell := by unfold threshold at hell; omega
    have htF : t < F (ell-1) := by
      have hf := Nat.le_fib_add_one (ell-1)
      unfold threshold at hell
      omega
    have hc := full21_3 U h t ell (by unfold threshold at hell; omega)
    have hd := D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add
      (ell-3) ⟨t, by simpa only [show ell-3+2=ell-1 by omega] using htF⟩
    simp only [show ell-3+3=ell by omega] at hd
    have hdecode : displacementDecode (F ell+t) = F (ell+1)+displacementDecode t := by
      unfold displacementDecode
      rw [hd]
      simp
    have hf := Nat.fib_add_two (n := ell-1)
    rw [show ell-1+2=ell+1 by omega, show ell-1+1=ell by omega] at hf
    rw [shiftRead, shiftRead] at hdecode
    have hg : G (F ell+t) = F (ell-1)+G t := by omega
    refine ⟨hc, hg, ?_⟩
    rw [canonicalDefect, hc, hg, widthDefect]
    omega
  have splitFacts : ∀ j : ℕ, threshold t ≤ j → SplitFacts t j := by
    intro j hj
    have hj3 : 3 ≤ j := by unfold threshold at hj; omega
    have hc := (profile j (by omega)).2.2
    have hp1 := profile (j-1) (by omega)
    have hp2 := profile (j-2) (by omega)
    have ha1 := h.anchors (j-1) (by unfold threshold at hj; omega)
    have ha2 := h.anchors (j-2) (by unfold threshold at hj; omega)
    have za1 : canonicalDefect (F (j-1)) = 0 := by
      simp [canonicalDefect, ha1.2.1, ha1.2.2]
    have za2 : canonicalDefect (F (j-2)) = 0 := by
      simp [canonicalDefect, ha2.2.1, ha2.2.2]
    obtain ⟨μ, _, _, _, _, _, _, _, _, _, sel, _, _, _, _, _⟩ :=
      (full22_1 U h).1 t j ht hj
    have ff := Nat.fib_add_two (n := j-2)
    rw [show j-2+2=j by omega, show j-2+1=j-1 by omega] at ff
    have ff' := Nat.fib_add_two (n := j-3)
    rw [show j-3+2=j-1 by omega, show j-3+1=j-2 by omega] at ff'
    have wp := (full22_1 U h).2.2.1
    have wo := (full22_1 U h).2.1
    by_cases he : (F (j-1)+t-1)%2=0
    · simp only [if_pos he] at sel
      have other : F j+t-g (F j+t)=F (j-2) := by omega
      have carry : beattyDeficit (g (F j+t)) (F j+t-g (F j+t)) = 0 := by
        rw [carryRead, other, sel]
        have gs := (profile j (by omega)).2.1
        rw [show F (j-1)+t+F (j-2)=F j+t by omega, gs, hp1.2.1, ha2.2.2]
        simp only [Nat.sub_sub] at *
        push_cast
        omega
      simp only [SplitFacts, retainedBit, stepSize, anchorRank, if_pos he, Bool.false_eq_true,
        ↓reduceIte]
      refine ⟨sel, other, hc, hp1.2.2, za2, carry, ?_, ?_⟩
      · intro ht2
        rw [other, sel, hp1.2.2, za2]
        simp [wp t ht2]
      · intro ht1
        rw [other, sel, hp1.2.2, za2, ht1, wo]
        exact ⟨rfl, rfl⟩
    · simp only [if_neg he] at sel
      have other : F j+t-g (F j+t)=F (j-2)+t := by omega
      have carry : beattyDeficit (g (F j+t)) (F j+t-g (F j+t)) = 0 := by
        rw [carryRead, other, sel]
        have gs := (profile j (by omega)).2.1
        rw [show F (j-1)+(F (j-2)+t)=F j+t by omega, gs, ha1.2.2, hp2.2.1]
        simp only [Nat.sub_sub] at *
        push_cast
        omega
      simp only [SplitFacts, retainedBit, stepSize, anchorRank, if_neg he, ↓reduceIte]
      refine ⟨sel, other, hc, hp2.2.2, za1, carry, ?_, ?_⟩
      · intro ht2
        rw [other, sel, za1, hp2.2.2]
        simp [wp t ht2]
      · intro ht1
        rw [other, sel, za1, hp2.2.2, ht1, wo]
        exact ⟨rfl, rfl⟩
  have controls : ∀ j : ℕ, threshold t ≤ j → CongruenceControl t j := by
    intro j hj
    have hj2 : 2 ≤ j := by unfold threshold at hj; omega
    have parity : F (j-1) % 2 = 0 ↔ (j-1) % 3 = 0 := by
      have hh := D5.S1.Recurrence.GoldenFibDivisibility.fib_dvd_iff 3 (j-1) (by omega)
      norm_num [Nat.dvd_iff_mod_eq_zero, Nat.fib] at hh
      exact hh
    have hf := Nat.mod_lt (F (j-1)) (by omega : 0 < 2)
    unfold CongruenceControl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intro htpar hjpar <;> unfold stepSize <;> split <;> omega
  refine ⟨fun j hj => ⟨splitFacts j hj, controls j hj⟩, ?_⟩
  have descent : ∀ j : ℕ, ∃ i : ℕ, rank t j i < threshold t := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases hj : j < threshold t
      · exact ⟨0, hj⟩
      · have hr := rBounds j
        have smaller : j-stepSize t j < j := by unfold threshold at hj; omega
        obtain ⟨i, hi⟩ := ih (j-stepSize t j) smaller
        refine ⟨i+1, ?_⟩
        simpa only [rank, Function.iterate_succ_apply] using hi
  let L := Nat.find (descent k)
  have terminal : rank t k L < threshold t := Nat.find_spec (descent k)
  have active : ∀ i : ℕ, i < L → threshold t ≤ rank t k i := by
    intro i hi
    have hn := Nat.find_min (descent k) hi
    omega
  have Lpos : 0 < L := by
    by_contra hn
    have hL : L=0 := by omega
    rw [hL] at terminal
    change k < threshold t at terminal
    omega
  have lastStep := rankSucc (L-1)
  rw [show L-1+1=L by omega] at lastStep
  have lastActive := active (L-1) (by omega)
  have lastSize := rBounds (rank t k (L-1))
  have band : rank t k L = threshold t-1 ∨ rank t k L = threshold t-2 := by omega
  have atAppend : ∀ (tree : BinaryTree ℕ) (p : List Bool) (b : Bool),
      subtreeAt tree (p++[b]) = (subtreeAt tree p).bind (fun s => subtreeAt s [b]) := by
    intro tree p
    induction p generalizing tree with
    | nil => intro b; rfl
    | cons a p ih =>
      intro b
      cases tree with
      | nil => rfl
      | node n left right =>
        simpa only [List.cons_append, subtreeAt] using
          ih (if a then right else left) b
  have childOccurrences : ∀ j : ℕ, threshold t ≤ j →
      subtreeAt (actualTree (F j+t)) [retainedBit t j] =
        some (actualTree (F (j-stepSize t j)+t)) ∧
      subtreeAt (actualTree (F j+t)) [!(retainedBit t j)] =
        some (actualTree (F (anchorRank t j))) := by
    intro j hj
    have sf := splitFacts j hj
    have hn : 3 ≤ F j+t := by
      have hf := Nat.le_fib_add_one j
      unfold threshold at hj
      omega
    rw [actualTree, dif_neg (by omega), dif_neg (by omega)]
    change _ ∧ _
    cases hb : retainedBit t j
    · have left := sf.1
      have right := sf.2.1
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at left right
      simp only [subtreeAt, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      rw [right, left]
      exact ⟨rfl, rfl⟩
    · have left := sf.1
      have right := sf.2.1
      simp only [hb, ↓reduceIte] at left right
      simp only [subtreeAt, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [right, left]
      exact ⟨rfl, rfl⟩
  have siblingTotal : ∀ j : ℕ, threshold t ≤ j →
      totalCarry (actualTree (F (anchorRank t j))) = 0 := by
    intro j hj
    have ha : 2 ≤ anchorRank t j := by
      unfold anchorRank
      split <;> unfold threshold at hj <;> omega
    have hf := Nat.le_fib_add_one (anchorRank t j)
    rw [totalDefect _ (by omega), (splitFacts j hj).2.2.2.2.1]
    rfl
  have carryNext : ∀ j : ℕ, threshold t ≤ j →
      totalCarry (actualTree (F j+t)) =
        totalCarry (actualTree (F (j-stepSize t j)+t)) := by
    intro j hj
    have sf := splitFacts j hj
    have hn : 3 ≤ F j+t := by
      have hf := Nat.le_fib_add_one j
      unfold threshold at hj
      omega
    rw [actualTree, dif_neg (by omega), dif_neg (by omega), totalCarry,
      if_neg (by omega), label, label, sf.2.2.2.2.2.1]
    have left := sf.1
    have right := sf.2.1
    cases hb : retainedBit t j
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at left right
      rw [right, left, siblingTotal j hj]
      ring
    · simp only [hb, ↓reduceIte] at left right
      rw [right, left, siblingTotal j hj]
      ring
  have occurrences : ∀ i : ℕ, i ≤ L →
      subtreeAt (actualTree (F k+t)) (address t k i) =
        some (actualTree (F (rank t k i)+t)) := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
      intro hi
      have hai := active i (by omega)
      rw [address, atAppend, ih (by omega), Option.bind_some,
        (childOccurrences _ hai).1, rankSucc]
  have conservation : ∀ i : ℕ, i ≤ L → totalCarry (actualTree (F k+t)) =
      totalCarry (actualTree (F (rank t k i)+t)) := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
      intro hi
      rw [ih (by omega), carryNext _ (active i (by omega)), rankSucc]
  refine ⟨L, Lpos, terminal, band, ?_, occurrences, ?_,
    (profile _ (by omega)).2.2, conservation L le_rfl, ?_⟩
  · intro i hi
    exact ⟨active i hi, rankSucc i, rBounds _⟩
  · intro i hi
    have hai := active i hi
    rw [atAppend, occurrences i (by omega), Option.bind_some,
      (childOccurrences _ hai).2]
    exact ⟨rfl, siblingTotal _ hai, by rw [carryNext _ hai, rankSucc]⟩
  · rw [totalDefect _ (by omega), (profile _ (by omega)).2.2]

end
end D5.S1.Recurrence.Invariants.CloitreActualSpineCarry
