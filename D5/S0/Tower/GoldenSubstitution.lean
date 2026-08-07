/- GID: D5/S0/Tower/GoldenSubstitution
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenSubstitution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refining golden gaps realizes the oriented golden substitution. -/

import D5.S0.Tower.GoldenGaps
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

namespace D5.S0.Tower.GoldenSubstitution

open D5.S0.Conventions
open D5.S0.Tower.GoldenNames
open D5.S0.Tower.GoldenGaps

local notation "φ" => Real.goldenRatio

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem level_card_pos (Q : ℕ) : 0 < Nat.fib (Q + 2) := by
  exact Nat.fib_pos.2 (by omega)

private def shiftedName {Q : ℕ} (name : GoldenName Q) : GoldenName (Q + 1) := by
  refine ⟨⟨name.1.1.map (· + 1), ?_⟩, ?_⟩
  · have hparts := List.pairwise_append.1
      (List.isChain_iff_pairwise.1 name.1.2)
    rw [List.IsZeckendorfRep, List.isChain_iff_pairwise, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact hparts.1.imp fun hab ↦ by omega
    · simp
    · intro a ha b hb
      simp only [List.mem_map] at ha
      rcases ha with ⟨k, hk, rfl⟩
      simp only [List.mem_singleton] at hb
      subst b
      have := hparts.2.2 k hk 0 (by simp)
      omega
  · intro k hk
    simp only [List.mem_map] at hk
    rcases hk with ⟨j, hj, rfl⟩
    have := name.2 j hj
    omega

private theorem nameValue_shifted (Q : ℕ) (name : GoldenName Q) :
    nameValue (Q + 1) (shiftedName name) = nameValue Q name := by
  unfold nameValue shiftedName
  simp only [List.map_map]
  induction name.1.1 with
  | nil => rfl
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      have hexponent :
          (((k + 1 : ℕ) : ℤ) - ((((Q + 1) + 2 : ℕ) : ℤ))) =
            (k : ℤ) - ((Q + 2 : ℕ) : ℤ) := by
        push_cast
        omega
      rw [hexponent, ih]

/-- The index at level `Q + 1` of the level-`Q` name with the same real value. -/
noncomputable def levelEmbedding (Q : ℕ) (i : Fin (Nat.fib (Q + 2))) :
    Fin (Nat.fib (Q + 3)) :=
  (goldenNameEquiv (Q + 1)).symm (shiftedName (goldenNameEquiv Q i))

theorem levelEmbedding_value (Q : ℕ) (i : Fin (Nat.fib (Q + 2))) :
    indexedNameValue (Q + 1) (levelEmbedding Q i) = indexedNameValue Q i := by
  change nameValue (Q + 1)
      (goldenNameEquiv (Q + 1) ((goldenNameEquiv (Q + 1)).symm
        (shiftedName (goldenNameEquiv Q i)))) =
    nameValue Q (goldenNameEquiv Q i)
  rw [(goldenNameEquiv (Q + 1)).apply_symm_apply]
  exact nameValue_shifted Q (goldenNameEquiv Q i)

private theorem levelEmbedding_digits (Q : ℕ) (i : Fin (Nat.fib (Q + 2))) :
    wdigits (levelEmbedding Q i).1 = (wdigits i.1).map (· + 1) := by
  have hname := (goldenNameEquiv (Q + 1)).apply_symm_apply
    (shiftedName (goldenNameEquiv Q i))
  exact congrArg (fun name : GoldenName (Q + 1) ↦ name.1.1) hname

theorem levelEmbedding_strictMono (Q : ℕ) : StrictMono (levelEmbedding Q) := by
  intro i j hij
  apply ((indexed_nameValue_strictMono (Q + 1)).lt_iff_lt).mp
  rw [levelEmbedding_value, levelEmbedding_value]
  exact indexed_nameValue_strictMono Q hij

private def gapLeft (Q : ℕ) (i : Fin (Nat.fib (Q + 2) - 1)) :
    Fin (Nat.fib (Q + 2)) :=
  ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩

private def gapRight (Q : ℕ) (i : Fin (Nat.fib (Q + 2) - 1)) :
    Fin (Nat.fib (Q + 2)) :=
  ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩

private theorem gapLeft_lt_gapRight (Q : ℕ)
    (i : Fin (Nat.fib (Q + 2) - 1)) : gapLeft Q i < gapRight Q i := by
  simp [gapLeft, gapRight]

private theorem embedded_succ_bound (Q : ℕ)
    (i : Fin (Nat.fib (Q + 2) - 1)) :
    (levelEmbedding Q (gapLeft Q i)).1 + 1 < Nat.fib (Q + 3) := by
  have hlt := levelEmbedding_strictMono Q (gapLeft_lt_gapRight Q i)
  have hright := (levelEmbedding Q (gapRight Q i)).2
  omega

private noncomputable def refinementIndex (Q : ℕ) (i : Fin (Nat.fib (Q + 2) - 1)) :
    Fin (Nat.fib (Q + 3)) :=
  ⟨(levelEmbedding Q (gapLeft Q i)).1 + 1, embedded_succ_bound Q i⟩

/-- Fine-level indices strictly between the embedded endpoints of a coarse adjacent gap. -/
noncomputable def insertedNameIndices (Q : ℕ)
    (i : Fin (Nat.fib (Q + 2) - 1)) : Finset (Fin (Nat.fib (Q + 3))) :=
  Finset.Ioo (levelEmbedding Q (gapLeft Q i)) (levelEmbedding Q (gapRight Q i))

theorem mem_insertedNameIndices_iff (Q : ℕ)
    (i : Fin (Nat.fib (Q + 2) - 1)) (j : Fin (Nat.fib (Q + 3))) :
    j ∈ insertedNameIndices Q i ↔
      indexedNameValue Q
          ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ <
        indexedNameValue (Q + 1) j ∧
      indexedNameValue (Q + 1) j <
        indexedNameValue Q
          ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ := by
  rw [insertedNameIndices, Finset.mem_Ioo]
  rw [← (indexed_nameValue_strictMono (Q + 1)).lt_iff_lt,
    ← (indexed_nameValue_strictMono (Q + 1)).lt_iff_lt]
  simp only [levelEmbedding_value, gapLeft, gapRight]

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

private theorem indexedNameValue_lower (Q : ℕ) (i : Fin (Nat.fib (Q + 4)))
    (hi : i.1 < Nat.fib (Q + 3)) :
    indexedNameValue (Q + 2) i =
      φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨i.1, hi⟩ := by
  change ((wdigits i.1).map fun k : ℕ ↦
      φ ^ ((k : ℤ) - ((Q + 4 : ℕ) : ℤ))).sum =
    φ ^ (-1 : ℤ) *
      ((wdigits i.1).map fun k : ℕ ↦
        φ ^ ((k : ℤ) - ((Q + 3 : ℕ) : ℤ))).sum
  induction wdigits i.1 with
  | nil => simp
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons]
      have hexponent :
          (k : ℤ) - ((Q + 4 : ℕ) : ℤ) =
            -1 + ((k : ℤ) - ((Q + 3 : ℕ) : ℤ)) := by
        push_cast
        omega
      rw [hexponent, zpow_add₀ Real.goldenRatio_ne_zero, ih]
      ring

private theorem wdigits_fib_add (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) :
    wdigits (Nat.fib (Q + 3) + j.1) = (Q + 3) :: wdigits j.1 := by
  symm
  apply wdigits_unique
  · rw [List.IsZeckendorfRep, List.cons_append]
    apply (goldenNameEquiv Q j).1.2.cons
    intro k hk
    have hk_mem := List.mem_of_mem_head? hk
    rw [List.mem_append, List.mem_singleton] at hk_mem
    rcases hk_mem with hk_digits | rfl
    · have := (goldenNameEquiv Q j).2 k hk_digits
      omega
    · omega
  · change Nat.fib (Q + 3) + ((wdigits j.1).map Nat.fib).sum =
      Nat.fib (Q + 3) + j.1
    rw [decode_wdigits]

private theorem indexedNameValue_upper (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) :
    indexedNameValue (Q + 2)
        ⟨Nat.fib (Q + 3) + j.1, by
          have hrec :
              Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
            rw [Nat.fib_add_two (n := Q + 2), add_comm]
          rw [hrec]
          omega⟩ =
      φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q j := by
  change ((wdigits (Nat.fib (Q + 3) + j.1)).map fun k : ℕ ↦
      φ ^ ((k : ℤ) - ((Q + 4 : ℕ) : ℤ))).sum = _
  rw [wdigits_fib_add]
  simp only [List.map_cons, List.sum_cons]
  have hhead :
      ((Q + 3 : ℕ) : ℤ) - ((Q + 4 : ℕ) : ℤ) = -1 := by
    push_cast
    omega
  rw [hhead]
  congr 1
  change ((wdigits j.1).map fun k : ℕ ↦
      φ ^ ((k : ℤ) - ((Q + 4 : ℕ) : ℤ))).sum =
    φ ^ (-2 : ℤ) *
      ((wdigits j.1).map fun k : ℕ ↦
        φ ^ ((k : ℤ) - ((Q + 2 : ℕ) : ℤ))).sum
  induction wdigits j.1 with
  | nil => simp
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons]
      have hexponent :
          (k : ℤ) - ((Q + 4 : ℕ) : ℤ) =
            -2 + ((k : ℤ) - ((Q + 2 : ℕ) : ℤ)) := by
        push_cast
        omega
      rw [hexponent, zpow_add₀ Real.goldenRatio_ne_zero, ih]
      ring

private theorem indexedNameValue_zero (Q : ℕ) :
    indexedNameValue Q ⟨0, level_card_pos Q⟩ = 0 := by
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

private theorem wdigits_one : wdigits 1 = [2] := by
  symm
  apply wdigits_unique
  · norm_num [List.IsZeckendorfRep]
  · norm_num [Nat.fib]

private def lastIndex (Q : ℕ) : Fin (Nat.fib (Q + 2)) :=
  ⟨Nat.fib (Q + 2) - 1, Nat.sub_lt (level_card_pos Q) (by omega)⟩

private noncomputable def terminalGap (Q : ℕ) : ℝ :=
  1 - indexedNameValue Q (lastIndex Q)

private theorem large_gap_of_no_low_digit_and_terminal : ∀ Q : ℕ,
    (∀ n (hn : n + 1 < Nat.fib (Q + 2)), 2 ∉ wdigits n →
      indexedNameValue Q ⟨n + 1, hn⟩ -
          indexedNameValue Q ⟨n, lt_trans (Nat.lt_succ_self n) hn⟩ =
        φ ^ (-(Q : ℤ))) ∧
    (2 ∉ wdigits (lastIndex Q).1 → terminalGap Q = φ ^ (-(Q : ℤ))) := by
  apply Nat.twoStepInduction
  · constructor
    · intro n hn
      norm_num [Nat.fib] at hn
    · intro _
      norm_num [terminalGap, lastIndex, indexedNameValue_zero]
  · constructor
    · intro n hn _
      have hn_zero : n = 0 := by norm_num [Nat.fib] at hn ⊢; omega
      subst n
      rw [indexedNameValue_one 1, indexedNameValue_zero]
      ring
    · intro htwo
      have hlast : (lastIndex 1).1 = 1 := by norm_num [lastIndex, Nat.fib]
      rw [hlast, wdigits_one] at htwo
      exact (htwo (by simp)).elim
  · intro Q hQ hQ1
    constructor
    · intro n hn htwo
      have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
        rw [Nat.fib_add_two (n := Q + 2), add_comm]
      by_cases hlower : n + 1 < Nat.fib (Q + 3)
      · have hleft : n < Nat.fib (Q + 3) := lt_trans (Nat.lt_succ_self n) hlower
        rw [indexedNameValue_lower Q ⟨n + 1, by simpa [hrec] using hn⟩ hlower,
          indexedNameValue_lower Q ⟨n, by simpa [hrec] using
            (lt_trans (Nat.lt_succ_self n) hn)⟩ hleft]
        have hgap := hQ1.1 n hlower htwo
        calc
          φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨n + 1, hlower⟩ -
              φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨n, hleft⟩ =
              φ ^ (-1 : ℤ) *
                (indexedNameValue (Q + 1) ⟨n + 1, hlower⟩ -
                  indexedNameValue (Q + 1) ⟨n, hleft⟩) := by ring
          _ = φ ^ (-1 : ℤ) * φ ^ (-((Q + 1 : ℕ) : ℤ)) := by rw [hgap]
          _ = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
            rw [mul_comm, zpow_shift_one]
      · have hboundary : Nat.fib (Q + 3) ≤ n + 1 := Nat.le_of_not_gt hlower
        by_cases heq : n + 1 = Nat.fib (Q + 3)
        · have hleft : n < Nat.fib (Q + 3) := by omega
          have hrightIndex :
              (⟨n + 1, by simpa [hrec] using hn⟩ : Fin (Nat.fib (Q + 4))) =
                ⟨Nat.fib (Q + 3) + (0 : ℕ), by
                  rw [hrec]
                  have := level_card_pos Q
                  omega⟩ := by
            apply Fin.ext
            simp [heq]
          rw [indexedNameValue_lower Q ⟨n, by simpa [hrec] using
              (lt_trans (Nat.lt_succ_self n) hn)⟩ hleft,
            hrightIndex, indexedNameValue_upper Q ⟨0, level_card_pos Q⟩,
            indexedNameValue_zero]
          simp only [mul_zero, add_zero]
          have hnlast : n = Nat.fib (Q + 3) - 1 := by omega
          have hterminal := hQ1.2 (by
            change 2 ∉ wdigits (Nat.fib (Q + 3) - 1)
            rwa [← hnlast])
          calc
            φ ^ (-1 : ℤ) -
                φ ^ (-1 : ℤ) * indexedNameValue (Q + 1) ⟨n, hleft⟩ =
                terminalGap (Q + 1) * φ ^ (-1 : ℤ) := by
              unfold terminalGap
              have hlast :
                  (⟨n, hleft⟩ : Fin (Nat.fib ((Q + 1) + 2))) =
                    lastIndex (Q + 1) := by
                apply Fin.ext
                dsimp [lastIndex]
                omega
              rw [← hlast]
              ring
            _ = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
              rw [hterminal, zpow_shift_one]
        · have hupper : Nat.fib (Q + 3) ≤ n := by omega
          have hsmallBound :
              (n - Nat.fib (Q + 3)) + 1 < Nat.fib (Q + 2) := by
            rw [hrec] at hn
            omega
          let left : Fin (Nat.fib (Q + 2)) :=
            ⟨n - Nat.fib (Q + 3), lt_trans (Nat.lt_succ_self _) hsmallBound⟩
          let right : Fin (Nat.fib (Q + 2)) :=
            ⟨(n - Nat.fib (Q + 3)) + 1, hsmallBound⟩
          have hn_decomp : Nat.fib (Q + 3) + left.1 = n := by
            dsimp [left]
            omega
          have hsucc_decomp : Nat.fib (Q + 3) + right.1 = n + 1 := by
            dsimp [right]
            omega
          have hleftIndex :
              (⟨n, by simpa [hrec] using
                (lt_trans (Nat.lt_succ_self n) hn)⟩ : Fin (Nat.fib (Q + 4))) =
                ⟨Nat.fib (Q + 3) + left.1, by
                  rw [hrec]
                  have := left.2
                  omega⟩ := by
            apply Fin.ext
            exact hn_decomp.symm
          have hrightIndex :
              (⟨n + 1, by simpa [hrec] using hn⟩ : Fin (Nat.fib (Q + 4))) =
                ⟨Nat.fib (Q + 3) + right.1, by
                  rw [hrec]
                  have := right.2
                  omega⟩ := by
            apply Fin.ext
            exact hsucc_decomp.symm
          rw [hleftIndex, indexedNameValue_upper Q left,
            hrightIndex, indexedNameValue_upper Q right]
          have htwo_left : 2 ∉ wdigits left.1 := by
            intro hmem
            apply htwo
            rw [← hn_decomp, wdigits_fib_add]
            simp [hmem]
          have hgap := hQ.1 left.1 hsmallBound htwo_left
          calc
            (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q right) -
                (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) * indexedNameValue Q left) =
                (indexedNameValue Q right - indexedNameValue Q left) *
                  φ ^ (-2 : ℤ) := by ring
            _ = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
              rw [show right =
                    ⟨left.1 + 1, hsmallBound⟩ by apply Fin.ext; rfl,
                hgap, zpow_shift_two]
    · intro htwo
      have hrec : Nat.fib (Q + 4) = Nat.fib (Q + 3) + Nat.fib (Q + 2) := by
        rw [Nat.fib_add_two (n := Q + 2), add_comm]
      have hlastIndex :
          lastIndex (Q + 2) =
            ⟨Nat.fib (Q + 3) + (lastIndex Q).1, by
              rw [hrec]
              have := (lastIndex Q).2
              omega⟩ := by
        apply Fin.ext
        dsimp [lastIndex]
        rw [hrec]
        have := level_card_pos Q
        omega
      have htwoQ : 2 ∉ wdigits (lastIndex Q).1 := by
        intro hmem
        apply htwo
        rw [hlastIndex, wdigits_fib_add]
        simp [hmem]
      have hterminal := hQ.2 htwoQ
      rw [terminalGap, hlastIndex, indexedNameValue_upper Q (lastIndex Q)]
      change 1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) *
          indexedNameValue Q (lastIndex Q)) = _
      calc
        1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) *
            indexedNameValue Q (lastIndex Q)) =
            terminalGap Q * φ ^ (-2 : ℤ) := by
          unfold terminalGap
          calc
            1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) *
                indexedNameValue Q (lastIndex Q)) =
                (1 - (φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ))) +
                  (1 - indexedNameValue Q (lastIndex Q)) * φ ^ (-2 : ℤ) := by ring
            _ = (1 - indexedNameValue Q (lastIndex Q)) * φ ^ (-2 : ℤ) := by
              rw [inverse_sum]
              ring
        _ = φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
          rw [hterminal, zpow_shift_two]

private theorem refinementIndex_gap (Q : ℕ)
    (i : Fin (Nat.fib (Q + 2) - 1)) :
    indexedNameValue (Q + 1) (refinementIndex Q i) -
        indexedNameValue Q (gapLeft Q i) = φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  rw [← levelEmbedding_value Q (gapLeft Q i)]
  apply (large_gap_of_no_low_digit_and_terminal (Q + 1)).1
  intro htwo
  rw [levelEmbedding_digits] at htwo
  simp only [List.mem_map] at htwo
  rcases htwo with ⟨k, hk, hk_two⟩
  have hcanonical := List.pairwise_append.1
    (List.isChain_iff_pairwise.1 (wdigits_isCanonical (gapLeft Q i).1))
  have hk_min := hcanonical.2.2 k hk 0 (by simp)
  omega

private theorem large_eq_next_sum (Q : ℕ) :
    φ ^ (-((Q + 1 : ℕ) : ℤ)) + φ ^ (-((Q + 2 : ℕ) : ℤ)) =
      φ ^ (-(Q : ℤ)) := by
  calc
    φ ^ (-((Q + 1 : ℕ) : ℤ)) + φ ^ (-((Q + 2 : ℕ) : ℤ)) =
        φ ^ (-(Q : ℤ)) * φ ^ (-1 : ℤ) +
          φ ^ (-(Q : ℤ)) * φ ^ (-2 : ℤ) := by
      rw [zpow_shift_one, zpow_shift_two]
    _ = φ ^ (-(Q : ℤ)) := by rw [← mul_add, inverse_sum, mul_one]

private theorem next_small_lt_next_large (Q : ℕ) :
    φ ^ (-((Q + 2 : ℕ) : ℤ)) < φ ^ (-((Q + 1 : ℕ) : ℤ)) := by
  exact zpow_lt_zpow_right₀ Real.one_lt_goldenRatio (by push_cast; omega)

private theorem refinement_endpoint_indices (Q : ℕ)
    (i : Fin (Nat.fib (Q + 2) - 1)) :
    (indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          φ ^ (-(Q : ℤ)) ∧
        (levelEmbedding Q (gapRight Q i)).1 =
          (levelEmbedding Q (gapLeft Q i)).1 + 2) ∨
    (indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          φ ^ (-((Q + 1 : ℕ) : ℤ)) ∧
        (levelEmbedding Q (gapRight Q i)).1 =
          (levelEmbedding Q (gapLeft Q i)).1 + 1) := by
  have hcoarse := consecutive_nameValue_gap Q i
  change
    indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          φ ^ (-(Q : ℤ)) ∨
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          φ ^ (-((Q + 1 : ℕ) : ℤ)) at hcoarse
  rcases hcoarse with hlarge | hsmall
  · left
    refine ⟨hlarge, ?_⟩
    have hrefinement := refinementIndex_gap Q i
    have hremaining :
        indexedNameValue (Q + 1) (levelEmbedding Q (gapRight Q i)) -
            indexedNameValue (Q + 1) (refinementIndex Q i) =
          φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
      rw [levelEmbedding_value]
      nlinarith [large_eq_next_sum Q]
    have hmid_lt :
        refinementIndex Q i < levelEmbedding Q (gapRight Q i) :=
      ((indexed_nameValue_strictMono (Q + 1)).lt_iff_lt).mp (by
        nlinarith [zpow_pos Real.goldenRatio_pos (-((Q + 2 : ℕ) : ℤ))])
    have hafter_bound :
        (levelEmbedding Q (gapLeft Q i)).1 + 2 < Nat.fib (Q + 3) := by
      have hright := (levelEmbedding Q (gapRight Q i)).2
      change (levelEmbedding Q (gapLeft Q i)).1 + 1 <
        (levelEmbedding Q (gapRight Q i)).1 at hmid_lt
      omega
    let after : Fin (Nat.fib (Q + 3)) :=
      ⟨(levelEmbedding Q (gapLeft Q i)).1 + 2, hafter_bound⟩
    let step : Fin (Nat.fib (Q + 3) - 1) :=
      ⟨(levelEmbedding Q (gapLeft Q i)).1 + 1, by omega⟩
    have hnext := consecutive_nameValue_gap (Q + 1) step
    change
      indexedNameValue (Q + 1) after -
            indexedNameValue (Q + 1) (refinementIndex Q i) =
          φ ^ (-((Q + 1 : ℕ) : ℤ)) ∨
        indexedNameValue (Q + 1) after -
            indexedNameValue (Q + 1) (refinementIndex Q i) =
          φ ^ (-((Q + 2 : ℕ) : ℤ)) at hnext
    rcases hnext with hnext_large | hnext_small
    · have hafter_le : after ≤ levelEmbedding Q (gapRight Q i) := by
        change (levelEmbedding Q (gapLeft Q i)).1 + 2 ≤
          (levelEmbedding Q (gapRight Q i)).1
        change (levelEmbedding Q (gapLeft Q i)).1 + 1 <
          (levelEmbedding Q (gapRight Q i)).1 at hmid_lt
        omega
      have hvalue_le := (indexed_nameValue_strictMono (Q + 1)).monotone hafter_le
      exfalso
      nlinarith [next_small_lt_next_large Q]
    · have hvalue :
          indexedNameValue (Q + 1) after =
            indexedNameValue (Q + 1) (levelEmbedding Q (gapRight Q i)) := by
        nlinarith
      have hindex := (indexed_nameValue_strictMono (Q + 1)).injective hvalue
      exact congrArg Fin.val hindex.symm
  · right
    refine ⟨hsmall, ?_⟩
    have hrefinement := refinementIndex_gap Q i
    have hvalue :
        indexedNameValue (Q + 1) (levelEmbedding Q (gapRight Q i)) =
          indexedNameValue (Q + 1) (refinementIndex Q i) := by
      rw [levelEmbedding_value]
      nlinarith
    have hindex := (indexed_nameValue_strictMono (Q + 1)).injective hvalue
    exact congrArg Fin.val hindex

/-- Between embedded endpoints, a large level-`Q` gap contains exactly one new
level-`Q + 1` name, while a small gap contains none. -/
theorem golden_gap_insertion_count (Q : ℕ) (_hQ : 2 ≤ Q)
    (i : Fin (Nat.fib (Q + 2) - 1)) :
    ((insertedNameIndices Q i).card = 1 ↔
      indexedNameValue Q
            ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
          indexedNameValue Q
            ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
        φ ^ (-(Q : ℤ))) ∧
    ((insertedNameIndices Q i).card = 0 ↔
      indexedNameValue Q
            ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
          indexedNameValue Q
            ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
        φ ^ (-((Q + 1 : ℕ) : ℤ))) := by
  change
    ((insertedNameIndices Q i).card = 1 ↔
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
        φ ^ (-(Q : ℤ))) ∧
    ((insertedNameIndices Q i).card = 0 ↔
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
        φ ^ (-((Q + 1 : ℕ) : ℤ)))
  have hne :
      φ ^ (-((Q + 1 : ℕ) : ℤ)) ≠ φ ^ (-(Q : ℤ)) :=
    ne_of_lt (by
      exact zpow_lt_zpow_right₀ Real.one_lt_goldenRatio (by push_cast; omega))
  rcases refinement_endpoint_indices Q i with ⟨hlarge, hindices⟩ | ⟨hsmall, hindices⟩
  · have hcard : (insertedNameIndices Q i).card = 1 := by
      rw [insertedNameIndices, Fin.card_Ioo]
      omega
    constructor
    · exact ⟨fun _ ↦ hlarge, fun _ ↦ hcard⟩
    · constructor
      · intro hzero
        omega
      · intro hsmall
        exact (hne (hsmall.symm.trans hlarge)).elim
  · have hcard : (insertedNameIndices Q i).card = 0 := by
      rw [insertedNameIndices, Fin.card_Ioo]
      omega
    constructor
    · constructor
      · intro hone
        omega
      · intro hlarge
        exact (hne (hsmall.symm.trans hlarge)).elim
    · exact ⟨fun _ ↦ hsmall, fun _ ↦ hcard⟩

/-- Every coarse adjacent interval contains zero or one fine-level names. -/
theorem golden_gap_insertion_count_values (Q : ℕ) (hQ : 2 ≤ Q)
    (i : Fin (Nat.fib (Q + 2) - 1)) :
    (insertedNameIndices Q i).card = 0 ∨ (insertedNameIndices Q i).card = 1 := by
  rcases consecutive_nameValue_gap Q i with hlarge | hsmall
  · right
    apply (golden_gap_insertion_count Q hQ i).1.2
    exact hlarge
  · left
    apply (golden_gap_insertion_count Q hQ i).2.2
    exact hsmall

/-- The unique point inserted into a large gap lies at its `phi⁻¹` fraction from
the left and leaves the new large length followed by the new small length. -/
theorem golden_gap_split_position (Q : ℕ) (_hQ : 2 ≤ Q)
    (i : Fin (Nat.fib (Q + 2) - 1))
    (hlarge :
      indexedNameValue Q
            ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
          indexedNameValue Q
            ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
        φ ^ (-(Q : ℤ))) :
    ∃ j : Fin (Nat.fib (Q + 3)),
      insertedNameIndices Q i = {j} ∧
      indexedNameValue (Q + 1) j -
          indexedNameValue Q
            ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
        φ ^ (-((Q + 1 : ℕ) : ℤ)) ∧
      indexedNameValue Q
            ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
          indexedNameValue (Q + 1) j =
        φ ^ (-((Q + 2 : ℕ) : ℤ)) ∧
      indexedNameValue (Q + 1) j -
          indexedNameValue Q
            ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
        φ ^ (-1 : ℤ) *
          (indexedNameValue Q
                ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
            indexedNameValue Q
                ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩) := by
  change indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
    φ ^ (-(Q : ℤ)) at hlarge
  have hindices :
      (levelEmbedding Q (gapRight Q i)).1 =
        (levelEmbedding Q (gapLeft Q i)).1 + 2 := by
    rcases refinement_endpoint_indices Q i with h | h
    · exact h.2
    · have hne :
          φ ^ (-((Q + 1 : ℕ) : ℤ)) ≠ φ ^ (-(Q : ℤ)) :=
        ne_of_lt (zpow_lt_zpow_right₀ Real.one_lt_goldenRatio (by push_cast; omega))
      exact (hne (h.1.symm.trans hlarge)).elim
  have hrefinement := refinementIndex_gap Q i
  have hremaining :
      indexedNameValue Q (gapRight Q i) -
          indexedNameValue (Q + 1) (refinementIndex Q i) =
        φ ^ (-((Q + 2 : ℕ) : ℤ)) := by
    nlinarith [large_eq_next_sum Q]
  have hinserted : insertedNameIndices Q i = {refinementIndex Q i} := by
    ext j
    simp only [insertedNameIndices, Finset.mem_Ioo, Finset.mem_singleton]
    constructor
    · intro hj
      apply Fin.ext
      change j.1 = (levelEmbedding Q (gapLeft Q i)).1 + 1
      change (levelEmbedding Q (gapLeft Q i)).1 < j.1 ∧
        j.1 < (levelEmbedding Q (gapRight Q i)).1 at hj
      omega
    · intro hj
      subst j
      change (levelEmbedding Q (gapLeft Q i)).1 <
          (levelEmbedding Q (gapLeft Q i)).1 + 1 ∧
        (levelEmbedding Q (gapLeft Q i)).1 + 1 <
          (levelEmbedding Q (gapRight Q i)).1
      omega
  refine ⟨refinementIndex Q i, hinserted, hrefinement, hremaining, ?_⟩
  calc
    indexedNameValue (Q + 1) (refinementIndex Q i) -
        indexedNameValue Q (gapLeft Q i) =
        φ ^ (-((Q + 1 : ℕ) : ℤ)) := hrefinement
    _ = φ ^ (-1 : ℤ) *
        (indexedNameValue Q (gapRight Q i) -
          indexedNameValue Q (gapLeft Q i)) := by
      rw [hlarge, mul_comm, zpow_shift_one]

/-- Reweighting the refined lengths gives the golden replacement directly:
small gaps become the new large gap, and large gaps become new-large then new-small. -/
theorem golden_gap_substitution (Q : ℕ) (hQ : 2 ≤ Q)
    (i : Fin (Nat.fib (Q + 2) - 1)) :
    (indexedNameValue Q
              ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
            indexedNameValue Q
              ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
          φ ^ (-((Q + 1 : ℕ) : ℤ)) →
        insertedNameIndices Q i = ∅ ∧
        indexedNameValue (Q + 1)
              (levelEmbedding Q
                ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩) -
            indexedNameValue (Q + 1)
              (levelEmbedding Q
                ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩) =
          φ ^ (-((Q + 1 : ℕ) : ℤ))) ∧
    (indexedNameValue Q
              ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
            indexedNameValue Q
              ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
          φ ^ (-(Q : ℤ)) →
        ∃ j : Fin (Nat.fib (Q + 3)),
          insertedNameIndices Q i = {j} ∧
          indexedNameValue (Q + 1) j -
              indexedNameValue Q
                ⟨i.1, by have := i.2; have := level_card_pos Q; omega⟩ =
            φ ^ (-((Q + 1 : ℕ) : ℤ)) ∧
          indexedNameValue Q
                ⟨i.1 + 1, by have := i.2; have := level_card_pos Q; omega⟩ -
              indexedNameValue (Q + 1) j =
            φ ^ (-((Q + 2 : ℕ) : ℤ))) := by
  constructor
  · intro hsmall
    have hcount := (golden_gap_insertion_count Q hQ i).2.2 hsmall
    constructor
    · exact Finset.card_eq_zero.mp hcount
    · rw [levelEmbedding_value, levelEmbedding_value]
      exact hsmall
  · intro hlarge
    rcases golden_gap_split_position Q hQ i hlarge with
      ⟨j, hinserted, hleft, hright, _⟩
    exact ⟨j, hinserted, hleft, hright⟩

end D5.S0.Tower.GoldenSubstitution
