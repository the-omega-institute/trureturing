/- GID: D5/S0/Tower/GoldenGaps
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenGaps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden name values have exactly two adjacent gap lengths from level two. -/

import D5.S0.Tower.GoldenNames
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

namespace D5.S0.Tower.GoldenGaps

open D5.S0.Conventions
open D5.S0.Tower.GoldenNames

local notation "φ" => Real.goldenRatio

private theorem fib_level_pos (Q : ℕ) : 0 < Nat.fib (Q + 2) := by
  exact Nat.fib_pos.2 (by omega)

private def liftName {Q : ℕ} (name : GoldenName Q) : GoldenName (Q + 1) :=
  ⟨name.1, fun k hk ↦ by have := name.2 k hk; omega⟩

private def prependName (Q : ℕ) (name : GoldenName Q) : GoldenName (Q + 2) := by
  refine ⟨⟨(Q + 3) :: name.1.1, ?_⟩, ?_⟩
  · rw [List.IsZeckendorfRep, List.cons_append]
    apply name.1.2.cons
    intro k hk
    have hk_mem := List.mem_of_mem_head? hk
    rw [List.mem_append, List.mem_singleton] at hk_mem
    rcases hk_mem with hk_digits | rfl
    · have := name.2 k hk_digits
      omega
    · omega
  · intro k hk
    have hk' : k = Q + 3 ∨ k ∈ name.1.1 := List.mem_cons.mp hk
    rcases hk' with hk | hk
    · rw [hk]
      omega
    · have := name.2 k hk
      omega

private theorem zpow_shift_one (Q : ℕ) :
    φ ^ (-(Q : ℤ)) * φ ^ (-1 : ℤ) = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  rw [← zpow_add₀ Real.goldenRatio_ne_zero]
  congr 1
  push_cast
  omega

private theorem zpow_shift_two (Q : ℕ) :
    φ ^ (-(Q : ℤ)) * φ ^ (-2 : ℤ) = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
  rw [← zpow_add₀ Real.goldenRatio_ne_zero]
  congr 1
  push_cast
  omega

private theorem inverse_sum : φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) = 1 := by
  rw [zpow_neg, zpow_neg]
  norm_num only [zpow_ofNat, pow_one]
  calc
    φ⁻¹ + (φ ^ 2)⁻¹ = (φ + 1) / φ ^ 2 := by
      field_simp [Real.goldenRatio_ne_zero]
    _ = 1 := by
      rw [Real.goldenRatio_sq]
      exact div_self (by nlinarith [Real.goldenRatio_pos])

private theorem nameValue_lift {Q : ℕ} (name : GoldenName Q) :
    nameValue (Q + 1) (liftName name) = φ ^ (-1 : ℤ) * nameValue Q name := by
  unfold nameValue liftName
  induction name.1.1 with
  | nil => simp
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons]
      have hexponent :
          (k : ℤ) - (((Q + 1) + 2 : ℕ) : ℤ) =
            -1 + ((k : ℤ) - ((Q + 2 : ℕ) : ℤ)) := by
        push_cast
        omega
      rw [hexponent, zpow_add₀ Real.goldenRatio_ne_zero, ih]
      ring

private theorem nameValue_prepend (Q : ℕ) (name : GoldenName Q) :
    nameValue (Q + 2) (prependName Q name) =
      φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * nameValue Q name := by
  unfold nameValue prependName
  simp only [List.map_cons, List.sum_cons]
  have hhead :
      ((Q + 3 : ℕ) : ℤ) - (((Q + 2) + 2 : ℕ) : ℤ) = -1 := by
    push_cast
    omega
  rw [hhead]
  congr 1
  induction name.1.1 with
  | nil => simp
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons]
      have hexponent :
          (k : ℤ) - (((Q + 2) + 2 : ℕ) : ℤ) =
            -2 + ((k : ℤ) - ((Q + 2 : ℕ) : ℤ)) := by
        push_cast
        omega
      rw [hexponent, zpow_add₀ Real.goldenRatio_ne_zero, ih]
      ring

/-- The value of the `n`th golden name under the frozen Fibonacci-interval equivalence. -/
noncomputable def indexedNameValue (Q : ℕ) (n : Fin (Nat.fib (Q + 2))) : ℝ :=
  nameValue Q (goldenNameEquiv Q n)

private theorem indexedNameValue_lower (Q : ℕ) (i : Fin (Nat.fib (Q + 4)))
    (hi : i.1 < Nat.fib (Q + 3)) :
    indexedNameValue (Q + 2) i =
      φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨i.1, hi⟩ := by
  have hname : goldenNameEquiv (Q + 2) i = liftName (goldenNameEquiv (Q + 1) ⟨i.1, hi⟩) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [indexedNameValue, indexedNameValue, hname, nameValue_lift]

private theorem indexedNameValue_upper (Q : ℕ) (i : Fin (Nat.fib (Q + 4)))
    (hi : Nat.fib (Q + 3) ≤ i.1) :
    indexedNameValue (Q + 2) i =
      φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) *
        indexedNameValue Q ⟨i.1 - Nat.fib (Q + 3), by
          have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
            rw [Nat.fib_add_two (n := Q + 2), add_comm]
          rw [hrec] at i
          omega⟩ := by
  let j : Fin (Nat.fib (Q + 2)) := ⟨i.1 - Nat.fib (Q + 3), by
    have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
      rw [Nat.fib_add_two (n := Q + 2), add_comm]
    rw [hrec] at i
    omega⟩
  have hj_sum : Nat.fib (Q + 3) + j.1 = i.1 := by
    dsimp [j]
    omega
  have hdigits : wdigits i.1 = (Q + 3) :: wdigits j.1 := by
    rw [← hj_sum]
    symm
    have hcanonical : ((Q + 3) :: wdigits j.1).IsZeckendorfRep :=
      (prependName Q (goldenNameEquiv Q j)).1.2
    apply wdigits_unique hcanonical
    change Nat.fib (Q + 3) + ((wdigits j.1).map Nat.fib).sum =
      Nat.fib (Q + 3) + j.1
    rw [decode_wdigits]
  have hname : goldenNameEquiv (Q + 2) i = prependName Q (goldenNameEquiv Q j) := by
    exact Subtype.ext (Subtype.ext hdigits)
  rw [indexedNameValue, hname, nameValue_prepend, indexedNameValue]

private theorem indexedNameValue_zero (Q : ℕ) :
    indexedNameValue Q ⟨0, fib_level_pos Q⟩ = 0 := by
  change ((wdigits 0).map fun k : ℕ ↦
    φ ^ ((k : ℤ) - ((Q + 2 : ℕ) : ℤ))).sum = 0
  rw [show wdigits 0 = [] by
    symm
    apply wdigits_unique
    · exact List.IsZeckendorfRep_nil
    · rfl]
  rfl

private theorem indexedNameValue_one (Q : ℕ) (h : 1 < Nat.fib (Q + 2)) :
    indexedNameValue Q ⟨1, h⟩ = φ ^ (-(Q : ℤ)) := by
  change ((wdigits 1).map fun k : ℕ ↦
    φ ^ ((k : ℤ) - ((Q + 2 : ℕ) : ℤ))).sum = _
  rw [show wdigits 1 = [2] by
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  push_cast
  omega

private theorem indexedNameValue_two (Q : ℕ) (h : 2 < Nat.fib (Q + 2)) :
    indexedNameValue Q ⟨2, h⟩ = φ ^ ((1 : ℤ) - (Q : ℤ)) := by
  change ((wdigits 2).map fun k : ℕ ↦
    φ ^ ((k : ℤ) - ((Q + 2 : ℕ) : ℤ))).sum = _
  rw [show wdigits 2 = [3] by
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  push_cast
  omega

private def lastIndex (Q : ℕ) : Fin (Nat.fib (Q + 2)) :=
  ⟨Nat.fib (Q + 2) - 1, Nat.sub_lt (fib_level_pos Q) (by omega)⟩

private noncomputable def terminalGap (Q : ℕ) : ℝ :=
  1 - indexedNameValue Q (lastIndex Q)

private theorem gap_and_terminal : ∀ Q : ℕ,
    (∀ n (hn : n + 1 < Nat.fib (Q + 2)),
      indexedNameValue Q ⟨n + 1, hn⟩ -
          indexedNameValue Q ⟨n, lt_trans (Nat.lt_succ_self n) hn⟩ =
            φ ^ (-(Q : ℤ)) ∨
      indexedNameValue Q ⟨n + 1, hn⟩ -
          indexedNameValue Q ⟨n, lt_trans (Nat.lt_succ_self n) hn⟩ =
            φ ^ (-((Q + 1 : ℕ) : ℤ))) ∧
    (terminalGap Q = φ ^ (-(Q : ℤ)) ∨
      terminalGap Q = φ ^ (-((Q + 1 : ℕ) : ℤ))) := by
  apply Nat.twoStepInduction
  · constructor
    · intro n hn
      norm_num [Nat.fib] at hn
    · left
      norm_num [terminalGap, lastIndex, indexedNameValue_zero]
  · constructor
    · intro n hn
      have hn_zero : n = 0 := by norm_num [Nat.fib] at hn ⊢; omega
      subst n
      left
      rw [indexedNameValue_one 1, indexedNameValue_zero]
      ring
    · right
      have hlast : lastIndex 1 = ⟨1, by norm_num [Nat.fib]⟩ := by
        apply Fin.ext
        norm_num [lastIndex, Nat.fib]
      rw [terminalGap, hlast, indexedNameValue_one]
      change 1 - φ ^ (-1 : ℤ) = φ ^ (-2 : ℤ)
      linarith [inverse_sum]
  · intro Q hQ hQ1
    constructor
    · intro n hn
      have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
        rw [Nat.fib_add_two (n := Q + 2), add_comm]
      by_cases hlower : n + 1 < Nat.fib (Q + 3)
      · have hleft : n < Nat.fib (Q + 3) := lt_trans (Nat.lt_succ_self n) hlower
        rw [indexedNameValue_lower Q ⟨n + 1, by simpa [hrec] using hn⟩ hlower,
          indexedNameValue_lower Q ⟨n, by simpa [hrec] using
            (lt_trans (Nat.lt_succ_self n) hn)⟩ hleft]
        rcases hQ1.1 n hlower with hgap | hgap
        · left
          calc
            φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨n + 1, hlower⟩ -
                φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨n, hleft⟩ =
                φ ^ (-1 : ℤ) *
                  (indexedNameValue (Q + 1) ⟨n + 1, hlower⟩ -
                    indexedNameValue (Q + 1) ⟨n, hleft⟩) := by ring
            _ = φ ^ (-1 : ℤ) * φ ^ (-((Q + 1 : ℕ) : ℤ)) := by rw [hgap]
            _ = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
              rw [mul_comm, zpow_shift_one]
        · right
          calc
            φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨n + 1, hlower⟩ -
                φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨n, hleft⟩ =
                φ ^ (-1 : ℤ) *
                  (indexedNameValue (Q + 1) ⟨n + 1, hlower⟩ -
                    indexedNameValue (Q + 1) ⟨n, hleft⟩) := by ring
            _ = φ ^ (-1 : ℤ) * φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
              convert congrArg (φ ^ (-1 : ℤ) * ·) hgap using 1
            _ = φ ^ (-((Q + 3 : ℕ) : ℤ)) := by
              rw [mul_comm, zpow_shift_one]
      · have hboundary : Nat.fib (Q + 3) ≤ n + 1 := Nat.le_of_not_gt hlower
        by_cases heq : n + 1 = Nat.fib (Q + 3)
        · have hleft : n < Nat.fib (Q + 3) := by omega
          have hright : Nat.fib (Q + 3) ≤ n + 1 := by omega
          rw [indexedNameValue_lower Q ⟨n, by simpa [hrec] using
            (lt_trans (Nat.lt_succ_self n) hn)⟩ hleft,
            indexedNameValue_upper Q ⟨n + 1, by simpa [hrec] using hn⟩ hright]
          have hresBound : n + 1 - Nat.fib (Q + 3) < Nat.fib (Q + 2) := by
            have hn' : n + 1 < Nat.fib (Q + 4) := by convert hn using 1
            rw [hrec] at hn'
            omega
          have hzero :
              indexedNameValue Q
                ⟨n + 1 - Nat.fib (Q + 3), hresBound⟩ = 0 := by
            have hindex :
                (⟨n + 1 - Nat.fib (Q + 3), hresBound⟩ : Fin (Nat.fib (Q + 2))) =
                  ⟨0, fib_level_pos Q⟩ := by
              apply Fin.ext
              change n + 1 - Nat.fib (Q + 3) = 0
              omega
            rw [hindex, indexedNameValue_zero]
          rw [hzero]
          simp only [mul_zero, add_zero]
          rcases hQ1.2 with hterminal | hterminal
          · left
            have hlast :
                (⟨n, hleft⟩ : Fin (Nat.fib ((Q + 1) + 2))) =
                  lastIndex (Q + 1) := by
              apply Fin.ext
              dsimp [lastIndex]
              change n = Nat.fib (Q + 3) - 1
              have := fib_level_pos (Q + 1)
              omega
            calc
              φ ^ (-1 : ℤ) -
                  φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨n, hleft⟩ =
                  terminalGap (Q + 1) * φ ^ (-1 : ℤ) := by
                rw [hlast]
                unfold terminalGap
                ring
              _ = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
                rw [hterminal, zpow_shift_one]
          · right
            have hlast :
                (⟨n, hleft⟩ : Fin (Nat.fib ((Q + 1) + 2))) =
                  lastIndex (Q + 1) := by
              apply Fin.ext
              dsimp [lastIndex]
              change n = Nat.fib (Q + 3) - 1
              have := fib_level_pos (Q + 1)
              omega
            calc
              φ ^ (-1 : ℤ) -
                  φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨n, hleft⟩ =
                  terminalGap (Q + 1) * φ ^ (-1 : ℤ) := by
                rw [hlast]
                unfold terminalGap
                ring
              _ = φ ^ (-((Q + 3 : ℕ) : ℤ)) := by
                rw [hterminal]
                convert zpow_shift_one (Q + 2) using 1
        · have hupper : Nat.fib (Q + 3) ≤ n := by omega
          rw [indexedNameValue_upper Q ⟨n + 1, by simpa [hrec] using hn⟩ hboundary,
            indexedNameValue_upper Q ⟨n, by simpa [hrec] using
              (lt_trans (Nat.lt_succ_self n) hn)⟩ hupper]
          have hsmallBound :
              (n - Nat.fib (Q + 3)) + 1 < Nat.fib (Q + 2) := by
            rw [hrec] at hn
            omega
          rcases hQ.1 (n - Nat.fib (Q + 3)) hsmallBound with hgap | hgap
          · left
            have hrightIndex :
                (⟨n + 1 - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩ :
                    Fin (Nat.fib (Q + 2))) =
                  ⟨(n - Nat.fib (Q + 3)) + 1, hsmallBound⟩ := by
              apply Fin.ext
              change n + 1 - Nat.fib (Q + 3) = n - Nat.fib (Q + 3) + 1
              omega
            have hgap' :
                indexedNameValue Q
                    ⟨n + 1 - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩ -
                  indexedNameValue Q
                    ⟨n - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩ =
                  φ ^ (-(Q : ℤ)) := by
              rw [hrightIndex]
              exact hgap
            calc
              (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q
                    ⟨n + 1 - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩) -
                  (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q
                    ⟨n - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩) =
                  (indexedNameValue Q
                      ⟨n + 1 - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩ -
                    indexedNameValue Q
                      ⟨n - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩) *
                    φ ^ (-2 : ℤ) := by ring
              _ = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by rw [hgap', zpow_shift_two]
          · right
            have hrightIndex :
                (⟨n + 1 - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩ :
                    Fin (Nat.fib (Q + 2))) =
                  ⟨(n - Nat.fib (Q + 3)) + 1, hsmallBound⟩ := by
              apply Fin.ext
              change n + 1 - Nat.fib (Q + 3) = n - Nat.fib (Q + 3) + 1
              omega
            have hgap' :
                indexedNameValue Q
                    ⟨n + 1 - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩ -
                  indexedNameValue Q
                    ⟨n - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩ =
                  φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
              rw [hrightIndex]
              exact hgap
            calc
              (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q
                    ⟨n + 1 - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩) -
                  (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q
                    ⟨n - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩) =
                  (indexedNameValue Q
                      ⟨n + 1 - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩ -
                    indexedNameValue Q
                      ⟨n - Nat.fib (Q + 3), by rw [hrec] at hn; omega⟩) *
                    φ ^ (-2 : ℤ) := by ring
              _ = φ ^ (-((Q + 3 : ℕ) : ℤ)) := by
                rw [hgap', zpow_shift_two]
    · have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
        rw [Nat.fib_add_two (n := Q + 2), add_comm]
      have hlastUpper : Nat.fib (Q + 3) ≤ (lastIndex (Q + 2)).1 := by
        dsimp [lastIndex]
        change Nat.fib (Q + 3) ≤ Nat.fib (Q + 4) - 1
        rw [hrec]
        have := fib_level_pos Q
        omega
      have hresBound :
          (lastIndex (Q + 2)).1 - Nat.fib (Q + 3) < Nat.fib (Q + 2) := by
        dsimp [lastIndex]
        change Nat.fib (Q + 4) - 1 - Nat.fib (Q + 3) < Nat.fib (Q + 2)
        rw [hrec]
        have := fib_level_pos Q
        omega
      have hindex :
          (⟨(lastIndex (Q + 2)).1 - Nat.fib (Q + 3), hresBound⟩ :
            Fin (Nat.fib (Q + 2))) = lastIndex Q := by
        apply Fin.ext
        dsimp [lastIndex]
        change Nat.fib (Q + 4) - 1 - Nat.fib (Q + 3) = Nat.fib (Q + 2) - 1
        rw [hrec]
        have := fib_level_pos Q
        omega
      have hterminalRec : terminalGap (Q + 2) = terminalGap Q * φ ^ (-2 : ℤ) := by
        rw [terminalGap, indexedNameValue_upper Q (lastIndex (Q + 2)) hlastUpper]
        change 1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) *
            indexedNameValue Q
              ⟨(lastIndex (Q + 2)).1 - Nat.fib (Q + 3), hresBound⟩) = _
        rw [hindex]
        unfold terminalGap
        calc
          1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) *
              indexedNameValue Q (lastIndex Q)) =
              (1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ))) +
                (1 - indexedNameValue Q (lastIndex Q)) * φ ^ (-2 : ℤ) := by ring
          _ = (1 - indexedNameValue Q (lastIndex Q)) * φ ^ (-2 : ℤ) := by
            rw [inverse_sum]
            ring
      rw [hterminalRec]
      rcases hQ.2 with hterminal | hterminal
      · left
        rw [hterminal, zpow_shift_two]
      · right
        rw [hterminal, zpow_shift_two]

/-- Consecutive entries in the Fibonacci-index enumeration have one of the two
golden gap lengths. -/
theorem consecutive_nameValue_gap (Q : ℕ) (i : Fin (Nat.fib (Q + 2) - 1)) :
    indexedNameValue Q
          ⟨i.1 + 1, by have := i.2; have := fib_level_pos Q; omega⟩ -
        indexedNameValue Q ⟨i.1, by have := i.2; have := fib_level_pos Q; omega⟩ =
          φ ^ (-(Q : ℤ)) ∨
    indexedNameValue Q
          ⟨i.1 + 1, by have := i.2; have := fib_level_pos Q; omega⟩ -
        indexedNameValue Q ⟨i.1, by have := i.2; have := fib_level_pos Q; omega⟩ =
          φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  exact (gap_and_terminal Q).1 i.1 (by
    have := i.2
    have := fib_level_pos Q
    omega)

/-- The frozen equivalence enumerates golden name values in strictly increasing order. -/
theorem indexed_nameValue_strictMono (Q : ℕ) : StrictMono (indexedNameValue Q) := by
  have hcard : Nat.fib (Q + 2) - 1 + 1 = Nat.fib (Q + 2) := by
    have := fib_level_pos Q
    omega
  let f : Fin (Nat.fib (Q + 2) - 1 + 1) → ℝ := fun i ↦
    indexedNameValue Q (Fin.cast hcard i)
  have hf : StrictMono f := Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    have hleft :
        Fin.cast hcard i.castSucc =
          (⟨i.1, by have := i.2; have := fib_level_pos Q; omega⟩ :
            Fin (Nat.fib (Q + 2))) := by
      apply Fin.ext
      rfl
    have hright :
        Fin.cast hcard i.succ =
          (⟨i.1 + 1, by have := i.2; have := fib_level_pos Q; omega⟩ :
            Fin (Nat.fib (Q + 2))) := by
      apply Fin.ext
      rfl
    rcases consecutive_nameValue_gap Q i with hgap | hgap
    · have hpos : 0 < φ ^ (-(Q : ℤ)) := zpow_pos Real.goldenRatio_pos _
      dsimp [f]
      rw [hleft, hright]
      nlinarith
    · have hpos : 0 < φ ^ (-((Q + 1 : ℕ) : ℤ)) :=
        zpow_pos Real.goldenRatio_pos _
      dsimp [f]
      rw [hleft, hright]
      nlinarith
  intro i j hij
  let i' : Fin (Nat.fib (Q + 2) - 1 + 1) := Fin.cast hcard.symm i
  let j' : Fin (Nat.fib (Q + 2) - 1 + 1) := Fin.cast hcard.symm j
  have hij' : i' < j' := hij
  simpa [f, i', j'] using hf hij'

/-- All level-`Q` name values, listed increasingly. -/
noncomputable def sortedNameValues (Q : ℕ) : List ℝ :=
  List.ofFn (indexedNameValue Q)

theorem sortedNameValues_sorted (Q : ℕ) : (sortedNameValues Q).SortedLT := by
  unfold sortedNameValues
  exact (List.pairwise_ofFn.mpr (indexed_nameValue_strictMono Q)).sortedLT

theorem sortedNameValues_toFinset (Q : ℕ) :
    (sortedNameValues Q).toFinset = Finset.univ.image (nameValue Q) := by
  ext x
  simp only [List.mem_toFinset, sortedNameValues, List.mem_ofFn, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨goldenNameEquiv Q i, by simpa [indexedNameValue] using hi⟩
  · rintro ⟨name, hname⟩
    refine ⟨(goldenNameEquiv Q).symm name, ?_⟩
    simpa [indexedNameValue] using hname

/-- The finite set of differences between consecutive sorted golden name values. -/
noncomputable def adjacentGapSpectrum (Q : ℕ) : Finset ℝ :=
  Finset.univ.image fun i : Fin (Nat.fib (Q + 2) - 1) ↦
    indexedNameValue Q
          ⟨i.1 + 1, by have := i.2; have := fib_level_pos Q; omega⟩ -
        indexedNameValue Q ⟨i.1, by have := i.2; have := fib_level_pos Q; omega⟩

private theorem first_indexed_gap (Q : ℕ) (hQ : 1 ≤ Q) :
    indexedNameValue Q ⟨1, by
        have hmono := Nat.fib_mono (by omega : 3 ≤ Q + 2)
        norm_num [Nat.fib] at hmono ⊢
        omega⟩ -
      indexedNameValue Q ⟨0, fib_level_pos Q⟩ = φ ^ (-(Q : ℤ)) := by
  rw [indexedNameValue_one, indexedNameValue_zero, sub_zero]

private theorem second_indexed_gap (Q : ℕ) :
    indexedNameValue (Q + 2) ⟨2, by
        have hmono := Nat.fib_mono (by omega : 4 ≤ (Q + 2) + 2)
        norm_num [Nat.fib] at hmono ⊢
        omega⟩ -
      indexedNameValue (Q + 2) ⟨1, by
        have hmono := Nat.fib_mono (by omega : 3 ≤ (Q + 2) + 2)
        norm_num [Nat.fib] at hmono ⊢
        omega⟩ = φ ^ (-(((Q + 2) + 1 : ℕ) : ℤ)) := by
  rw [indexedNameValue_two, indexedNameValue_one]
  have hne := Real.goldenRatio_ne_zero
  rw [show (1 : ℤ) - (Q + 2 : ℕ) =
      -((((Q + 2) + 1 : ℕ) : ℤ)) + 2 by push_cast; omega,
    show -((Q + 2 : ℕ) : ℤ) =
      -((((Q + 2) + 1 : ℕ) : ℤ)) + 1 by push_cast; omega,
    zpow_add₀ hne, zpow_add₀ hne]
  norm_num only [zpow_ofNat, pow_one]
  rw [Real.goldenRatio_sq]
  ring

/-- From level two onward, the adjacent-gap spectrum is exactly the two golden
lengths; normalizing by the larger one gives `{1, phi^(-1)}`. -/
theorem adjacent_gap_spectrum (Q : ℕ) (hQ : 2 ≤ Q) :
    adjacentGapSpectrum Q =
      {φ ^ (-(Q : ℤ)), φ ^ (-((Q + 1 : ℕ) : ℤ))} := by
  ext gap
  constructor
  · intro hgap
    rw [adjacentGapSpectrum, Finset.mem_image] at hgap
    rcases hgap with ⟨i, _, rfl⟩
    rcases consecutive_nameValue_gap Q i with hlarge | hsmall
    · simp [hlarge]
    · simp [hsmall]
  · intro hgap
    simp only [Finset.mem_insert, Finset.mem_singleton] at hgap
    rcases hgap with rfl | rfl
    · rw [adjacentGapSpectrum, Finset.mem_image]
      have hcount : 2 < Nat.fib (Q + 2) := by
        have hmono := Nat.fib_mono (by omega : 4 ≤ Q + 2)
        norm_num [Nat.fib] at hmono ⊢
        omega
      let i : Fin (Nat.fib (Q + 2) - 1) := ⟨0, by omega⟩
      exact ⟨i, Finset.mem_univ _, by simpa [i] using first_indexed_gap Q (by omega)⟩
    · rw [adjacentGapSpectrum, Finset.mem_image]
      have hcount : 2 < Nat.fib (Q + 2) := by
        have hmono := Nat.fib_mono (by omega : 4 ≤ Q + 2)
        norm_num [Nat.fib] at hmono ⊢
        omega
      let i : Fin (Nat.fib (Q + 2) - 1) := ⟨1, by omega⟩
      obtain ⟨R, rfl⟩ : ∃ R, Q = R + 2 := ⟨Q - 2, by omega⟩
      exact ⟨i, Finset.mem_univ _, by simpa [i] using second_indexed_gap R⟩

end D5.S0.Tower.GoldenGaps
