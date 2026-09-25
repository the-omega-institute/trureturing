/- GID: D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact fixed-length decks recover every shorter scattered count. -/

import D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
import D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
import D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration
import D5.S1.Words.Complexity.VivionBinomialConverseFails

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore

open scoped BigOperators
open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra
open D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
open D5.S1.Words.Complexity.PositivePairs.Coefficients.PositivePairFiltration

variable {A : Type*}

private theorem scatteredCount_eq_count_sublistsLen [DecidableEq A]
    (pattern source : List A) :
    scatteredCount pattern source =
      (source.sublistsLen pattern.length).count pattern := by
  induction source generalizing pattern with
  | nil =>
      cases pattern <;> simp [scatteredCount]
  | cons first source ih =>
      cases pattern with
      | nil => simp [scatteredCount]
      | cons letter pattern =>
          rw [scatteredCount, List.length_cons, List.sublistsLen_succ_cons,
            List.count_append, ih]
          by_cases h : letter = first
          · subst first
            simp [List.count_map_of_injective, ih]
          · have hzero :
                (List.map (List.cons first)
                  (List.sublistsLen pattern.length source)).count
                    (letter :: pattern) = 0 := by
              apply List.count_eq_zero.mpr
              intro hmem
              rw [List.mem_map] at hmem
              obtain ⟨middle, _, hmiddle⟩ := hmem
              exact h (List.cons.inj hmiddle).1.symm
            simp [h, hzero]

private def nestedSelectionMass [DecidableEq A]
    (lower upper : Nat) (pattern source : List A) : Nat :=
  ((source.sublistsLen upper).map
    (fun middle => (middle.sublistsLen lower).count pattern)).sum

private theorem nestedSelectionMass_identity [DecidableEq A]
    (pattern source : List A) (lower upper : Nat)
    (hpattern : pattern.length = lower) (hlower : lower ≤ upper) :
    nestedSelectionMass lower upper pattern source =
      Nat.choose (source.length - lower) (upper - lower) *
        (source.sublistsLen lower).count pattern := by
  have hcount_cons_map_cons :
      ∀ (first letter : A) (pattern : List A) (lists : List (List A)),
        (lists.map (List.cons first)).count (letter :: pattern) =
          if letter = first then lists.count pattern else 0 := by
    intro first letter pattern lists
    by_cases h : letter = first
    · subst first
      simp [List.count_map_of_injective]
    · rw [if_neg h, List.count_eq_zero]
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨middle, _, hmiddle⟩ := hmem
      exact h (List.cons.inj hmiddle).1.symm
  have hsucc :
      ∀ (first letter : A) (pattern source : List A) (lower upper : Nat),
        nestedSelectionMass (lower + 1) (upper + 1)
            (letter :: pattern) (first :: source) =
          nestedSelectionMass (lower + 1) (upper + 1)
              (letter :: pattern) source +
            nestedSelectionMass (lower + 1) upper
              (letter :: pattern) source +
            if letter = first then
              nestedSelectionMass lower upper pattern source else 0 := by
    intro first letter pattern source lower upper
    unfold nestedSelectionMass
    rw [List.sublistsLen_succ_cons, List.map_append, List.sum_append]
    simp only [List.map_map, Function.comp_def]
    simp_rw [List.sublistsLen_succ_cons, List.count_append,
      hcount_cons_map_cons]
    rw [List.sum_map_add]
    by_cases h : letter = first <;> simp [h, Nat.add_assoc]
  have hzero_of_lt :
      ∀ (pattern source : List A) (lower upper : Nat), upper < lower →
        nestedSelectionMass lower upper pattern source = 0 := by
    intro pattern source lower upper h
    unfold nestedSelectionMass
    apply List.sum_eq_zero
    intro count hcount
    rw [List.mem_map] at hcount
    obtain ⟨middle, hmiddle, rfl⟩ := hcount
    have hlength : middle.length = upper := List.length_of_sublistsLen hmiddle
    rw [List.sublistsLen_of_length_lt (hlength.trans_lt h)]
    simp
  induction source generalizing pattern lower upper with
  | nil =>
      cases pattern with
      | nil =>
          have hlower0 : lower = 0 := by simpa using hpattern.symm
          subst lower
          cases upper <;> simp [nestedSelectionMass]
      | cons letter pattern =>
          cases lower with
          | zero => simp at hpattern
          | succ lower =>
              cases upper <;>
                simp [nestedSelectionMass, List.sublistsLen_succ_nil]
  | cons first source ih =>
      cases upper with
      | zero =>
          have hlower0 : lower = 0 := by omega
          have hpattern0 : pattern = [] :=
            List.length_eq_zero_iff.mp (hpattern.trans hlower0)
          subst lower
          subst pattern
          simp [nestedSelectionMass]
      | succ upper =>
          cases lower with
          | zero =>
              have hpattern0 : pattern = [] := List.length_eq_zero_iff.mp hpattern
              subst pattern
              simp [nestedSelectionMass, Function.comp_def,
                List.length_sublistsLen, Nat.choose_succ_succ, Nat.add_comm]
          | succ lower =>
              cases pattern with
              | nil => simp at hpattern
              | cons letter pattern =>
                  have hpattern' : pattern.length = lower := by
                    simpa using hpattern
                  have hlower' : lower ≤ upper := by omega
                  rw [hsucc]
                  have hfirst :=
                    ih (letter :: pattern) (lower + 1) (upper + 1)
                      (by simp [hpattern']) (by omega)
                  have hthird := ih pattern lower upper hpattern' hlower'
                  by_cases heq : lower = upper
                  · subst upper
                    have hzero := hzero_of_lt
                      (letter :: pattern) source (lower + 1) lower (by omega)
                    rw [hfirst, hzero, hthird]
                    simp only [List.length_cons, List.sublistsLen_succ_cons,
                      List.count_append, hcount_cons_map_cons,
                      Nat.succ_sub_succ_eq_sub, Nat.sub_self,
                      Nat.choose_zero_right, Nat.one_mul]
                    by_cases hletter : letter = first <;> simp [hletter]
                  · have hlt : lower < upper := lt_of_le_of_ne hlower' heq
                    have hsecond := ih (letter :: pattern) (lower + 1) upper
                      (by simp [hpattern']) (by omega)
                    rw [hfirst, hsecond, hthird]
                    simp only [List.length_cons, List.sublistsLen_succ_cons,
                      List.count_append, hcount_cons_map_cons,
                      Nat.succ_sub_succ_eq_sub]
                    have hsourcePred :
                        source.length - (lower + 1) =
                          source.length - lower - 1 := by
                      omega
                    have huppPred : upper - (lower + 1) =
                        upper - lower - 1 := by
                      omega
                    rw [hsourcePred, huppPred]
                    by_cases hn : lower < source.length
                    · rw [show source.length - lower =
                          (source.length - lower - 1) + 1 by omega,
                        show upper - lower = (upper - lower - 1) + 1 by omega,
                        Nat.choose_succ_succ]
                      by_cases hletter : letter = first <;>
                        simp [hletter] <;> ring
                    · have hsle : source.length ≤ lower := by omega
                      have hzeroSucc :
                          List.sublistsLen (lower + 1) source = [] :=
                        List.sublistsLen_of_length_lt (by omega)
                      rw [hzeroSucc]
                      by_cases hsourceEq : source.length = lower
                      · subst lower
                        simp [hsourceEq]
                      · have hslt : source.length < lower := by omega
                        have hzeroLower :
                            List.sublistsLen lower source = [] :=
                          List.sublistsLen_of_length_lt hslt
                        rw [hzeroLower]
                        simp

noncomputable def exactKDeck [Fintype A] (k : ℕ) (source : List A) :
    {pattern : List A // pattern.length = k} → ℕ :=
  by
    classical
    exact fun pattern ↦ scatteredCount pattern.1 source

noncomputable def exactKDeckImage [Fintype A] (k n : ℕ) :
    Finset ({pattern : List A // pattern.length = k} → ℕ) := by
  classical
  letI : Fintype {source : List A // source.length = n} :=
    Set.Finite.fintype (List.finite_length_eq A n)
  exact Finset.univ.image
    (fun source : {source : List A // source.length = n} ↦
      exactKDeck k source.1)

private theorem sublistsLen_perm_of_exactKDeck_eq [Fintype A]
    (k : ℕ) (left right : List A)
    (hdeck : exactKDeck k left = exactKDeck k right) :
    List.Perm (left.sublistsLen k) (right.sublistsLen k) := by
  classical
  rw [List.perm_iff_count]
  intro pattern
  by_cases hpattern : pattern.length = k
  · have hcount := congrFun hdeck ⟨pattern, hpattern⟩
    simpa only [exactKDeck, scatteredCount_eq_count_sublistsLen,
      hpattern] using hcount
  · have hleft : (left.sublistsLen k).count pattern = 0 := by
      apply List.count_eq_zero.mpr
      intro hmem
      exact hpattern (List.length_of_sublistsLen hmem)
    have hright : (right.sublistsLen k).count pattern = 0 := by
      apply List.count_eq_zero.mpr
      intro hmem
      exact hpattern (List.length_of_sublistsLen hmem)
    rw [hleft, hright]

theorem scatteredCount_eq_of_exactKDeck_eq [Fintype A] [DecidableEq A]
    (k n : ℕ) (left right pattern : List A)
    (hleft : left.length = n) (hright : right.length = n)
    (hkn : k ≤ n) (hpattern : pattern.length ≤ k)
    (hdeck : exactKDeck k left = exactKDeck k right) :
    scatteredCount pattern left = scatteredCount pattern right := by
  classical
  let j := pattern.length
  have hjk : j ≤ k := hpattern
  have hperm := sublistsLen_perm_of_exactKDeck_eq k left right hdeck
  have hmass : nestedSelectionMass j k pattern left =
      nestedSelectionMass j k pattern right := by
    unfold nestedSelectionMass
    exact (hperm.map
      (fun middle ↦ (middle.sublistsLen j).count pattern)).sum_eq
  rw [nestedSelectionMass_identity pattern left j k rfl hjk,
    nestedSelectionMass_identity pattern right j k rfl hjk,
    hleft, hright] at hmass
  have hchoose : 0 < Nat.choose (n - j) (k - j) := by
    apply Nat.choose_pos
    omega
  have hcount := Nat.eq_of_mul_eq_mul_left hchoose hmass
  simpa only [scatteredCount_eq_count_sublistsLen] using hcount

theorem exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length [Fintype A]
    (k n : ℕ) (left right : List A)
    (hleft : left.length = n) (hright : right.length = n) (hkn : k ≤ n) :
    exactKDeck k left = exactKDeck k right ↔
      cutoffMagnus k left = cutoffMagnus k right := by
  classical
  constructor
  · intro hdeck
    funext word
    let pattern := FreeMonoid.toList word.1
    have hpattern : pattern.length ≤ k := by
      simpa [pattern, FreeMonoid.length] using word.2
    have hcount := scatteredCount_eq_of_exactKDeck_eq k n left right pattern
      hleft hright hkn hpattern hdeck
    simp only [cutoffMagnus, cutoffRestriction, toRationalWordPolynomial,
      MonoidAlgebra.coeff_mapRingHom]
    rw [show word.1 = FreeMonoid.ofList pattern by
      apply FreeMonoid.toList.injective
      simp [pattern]]
    simp only [magnusPolynomial_coeff_scatteredCount]
    have hq : (scatteredCount pattern left : ℚ) =
        (scatteredCount pattern right : ℚ) := by
      exact_mod_cast hcount
    simpa using hq
  · intro hcutoff
    funext pattern
    change scatteredCount pattern.1 left = scatteredCount pattern.1 right
    have hcoeff := congrFun hcutoff
      (⟨FreeMonoid.ofList pattern.1, by
        simp [FreeMonoid.length, pattern.2]⟩ : CutoffWord A k)
    simp only [cutoffMagnus, cutoffRestriction, toRationalWordPolynomial,
      MonoidAlgebra.coeff_mapRingHom,
      magnusPolynomial_coeff_scatteredCount] at hcoeff
    have hq : (scatteredCount pattern.1 left : ℚ) =
        (scatteredCount pattern.1 right : ℚ) := by
      simpa using hcoeff
    exact_mod_cast hq


end D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore
