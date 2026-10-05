/- GID: D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries
   mirror-E: none(waiver:first-action-enumeration)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Expand]
   utility: none
   digest: First-action bijections enumerate accepted words at every height and phase. -/

import D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsCorrespondence
import Mathlib.RingTheory.PowerSeries.Expand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings

open TripleAvoidingMatchingsDefs PowerSeries

/-- The finite alphabet contains distinct labels for the two available closures. -/
instance : Fintype Action :=
  ⟨{.opening, .oldest, .second}, by intro a; cases a <;> simp⟩

/-- Count accepted suffixes by their full length, retaining their starting phase. -/
noncomputable def wordSeries (h : ℕ) (f : Bool) : PowerSeries ℤ :=
  mk fun l => (Nat.card {w : Fin l → Action // AcceptFrom h f (List.ofFn w)} : ℤ)

set_option maxHeartbeats 1200000 in
-- The coefficient proofs include finite bijections at all heights and a parity induction.
/-- First-action decomposition gives the boundary and bulk equations. At height
zero the series is the even-degree expansion of the literal matching count. -/
theorem word_series_recursion :
    wordSeries 0 false = 1 + X * wordSeries 1 false ∧
    wordSeries 1 false = X * wordSeries 2 false + X * wordSeries 0 false ∧
    wordSeries 2 false = X * wordSeries 3 false + 2 * X * wordSeries 1 false ∧
    wordSeries 2 true = X * wordSeries 3 true + X * wordSeries 1 false ∧
    (∀ h, wordSeries (h + 3) false = X * wordSeries (h + 4) false +
      X * (wordSeries (h + 2) false + wordSeries (h + 2) true)) ∧
    (∀ h, wordSeries (h + 3) true = X * wordSeries (h + 4) true +
      X * wordSeries (h + 2) false) ∧
    wordSeries 0 false = expand 2 (by decide) aSeries := by
  classical
  let c (h : ℕ) (f : Bool) (l : ℕ) :=
    Nat.card {w : Fin l → Action // AcceptFrom h f (List.ofFn w)}
  have c0 (h : ℕ) (f : Bool) : c h f 0 = if h = 0 ∧ f = false then 1 else 0 := by
    simp only [c, List.ofFn_zero, AcceptFrom]
    by_cases hh : h = 0 ∧ f = false
    · simp [hh, Nat.card_eq_fintype_card, Fintype.card_subtype]
    · simp [hh, Nat.card_eq_fintype_card]
  have cs (h : ℕ) (f : Bool) (l : ℕ) : c h f (l + 1) =
      c (h + 1) f l + (if 0 < h then c (h - 1) false l else 0) +
      (if f = false ∧ 2 ≤ h then c (h - 1) (decide (3 ≤ h)) l else 0) := by
    let P (a : Action) (w : Fin l → Action) := AcceptFrom h f (a :: List.ofFn w)
    let e : {w : Fin (l + 1) → Action // AcceptFrom h f (List.ofFn w)} ≃
        (a : Action) × {w : Fin l → Action // P a w} :=
      { toFun := fun w => ⟨w.1 0, ⟨fun i => w.1 i.succ, by
          simpa [P, List.ofFn_succ] using w.2⟩⟩
        invFun := fun w => ⟨Fin.cons w.1 w.2.1, by
          simpa [List.ofFn_cons, P] using w.2.2⟩
        left_inv := by
          intro w
          apply Subtype.ext
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        right_inv := by
          rintro ⟨a, w⟩
          congr }
    have cond (b : Prop) (h' : ℕ) (f' : Bool) :
        Nat.card {w : Fin l → Action // b ∧ AcceptFrom h' f' (List.ofFn w)} =
          if b then c h' f' l else 0 := by
      by_cases hb : b
      · simp [hb, c]
      · simp [hb, Nat.card_eq_fintype_card]
    have univ : (Finset.univ : Finset Action) = {.opening, .oldest, .second} := rfl
    rw [show c h f (l + 1) = Nat.card (Sigma fun a =>
      {w : Fin l → Action // P a w}) from Nat.card_congr e, Nat.card_sigma, univ]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      reduceCtorEq, or_false, not_false_eq_true, Finset.sum_singleton]
    change Nat.card {w : Fin l → Action // AcceptFrom (h + 1) f (List.ofFn w)} +
      (Nat.card {w : Fin l → Action // 0 < h ∧
        AcceptFrom (h - 1) false (List.ofFn w)} +
      Nat.card {w : Fin l → Action // f = false ∧ 2 ≤ h ∧
        AcceptFrom (h - 1) (decide (3 ≤ h)) (List.ofFn w)}) = _
    rw [cond]
    have hc : Nat.card {w : Fin l → Action // f = false ∧ 2 ≤ h ∧
        AcceptFrom (h - 1) (decide (3 ≤ h)) (List.ofFn w)} =
        if f = false ∧ 2 ≤ h then c (h - 1) (decide (3 ≤ h)) l else 0 := by
      let e' : {w : Fin l → Action // f = false ∧ 2 ≤ h ∧
          AcceptFrom (h - 1) (decide (3 ≤ h)) (List.ofFn w)} ≃
          {w : Fin l → Action // (f = false ∧ 2 ≤ h) ∧
          AcceptFrom (h - 1) (decide (3 ≤ h)) (List.ofFn w)} :=
        Equiv.subtypeEquivRight (fun _ => and_assoc.symm)
      by_cases hb : f = false ∧ 2 ≤ h
      all_goals simpa only [if_pos, if_neg, hb] using
        (Nat.card_congr e').trans (cond (f = false ∧ 2 ≤ h) (h - 1) (decide (3 ≤ h)))
    rw [hc]
    change c (h + 1) f l + (_ + _) = _
    split_ifs <;> omega
  have equations :
      wordSeries 0 false = 1 + X * wordSeries 1 false ∧
      wordSeries 1 false = X * wordSeries 2 false + X * wordSeries 0 false ∧
      wordSeries 2 false = X * wordSeries 3 false + 2 * X * wordSeries 1 false ∧
      wordSeries 2 true = X * wordSeries 3 true + X * wordSeries 1 false ∧
      (∀ h, wordSeries (h + 3) false = X * wordSeries (h + 4) false +
        X * (wordSeries (h + 2) false + wordSeries (h + 2) true)) ∧
      (∀ h, wordSeries (h + 3) true = X * wordSeries (h + 4) true +
        X * wordSeries (h + 2) false) := by
    have cc (h : ℕ) (f : Bool) (l : ℕ) :
        (wordSeries h f).coeff l = (c h f l : ℤ) := by simp [wordSeries, c]
    have h2 (h : ℕ) : 2 ≤ h + 3 := by omega
    have h3 (h : ℕ) : 3 ≤ h + 3 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try intro h
    all_goals try rw [show 2 * X * wordSeries 1 false =
      X * (wordSeries 1 false + wordSeries 1 false) by ring]
    all_goals apply PowerSeries.ext
    all_goals intro l
    all_goals cases l with
    | zero => simp [cc, c0]
    | succ l =>
      simp only [map_add, coeff_succ_X_mul, coeff_one, Nat.succ_ne_zero,
        if_false, zero_add, cc]
      all_goals norm_cast
      all_goals rw [cs]
      all_goals simp [Nat.add_assoc, h2, h3]
  have parity : ∀ (w : List Action) (h : ℕ) (f : Bool),
      AcceptFrom h f w → h ≤ w.length ∧ h % 2 = w.length % 2 := by
    intro w
    induction w with
    | nil =>
      intro h f ha
      simp only [AcceptFrom] at ha
      simp [ha.1]
    | cons a w ih =>
      intro h f ha
      cases a with
      | opening =>
        obtain ⟨hle, hpar⟩ := ih (h + 1) f ha
        simp only [List.length_cons]
        omega
      | oldest =>
        obtain ⟨hle, hpar⟩ := ih (h - 1) false ha.2
        have hpos : 0 < h := ha.1
        simp only [List.length_cons]
        omega
      | second =>
        obtain ⟨hle, hpar⟩ := ih (h - 1) (decide (3 ≤ h)) ha.2.2
        have hpos : 2 ≤ h := ha.2.1
        simp only [List.length_cons]
        omega
  refine ⟨equations.1, equations.2.1, equations.2.2.1, equations.2.2.2.1,
    equations.2.2.2.2.1, equations.2.2.2.2.2, ?_⟩
  apply PowerSeries.ext
  intro l
  by_cases heven : 2 ∣ l
  · obtain ⟨k, rfl⟩ := heven
    rw [coeff_expand_mul]
    have hcard : c 0 false (2 * k) = a k := by
      have hc := Nat.card_congr (matchingEquiv k)
      have ha : a k = Nat.card {m : Matching k // AvoidsP1 m} := by
        simp [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact hc.symm.trans ha.symm
    simpa [wordSeries, coeff_mk, aSeries, c] using congrArg (Int.ofNat) hcard
  · have hempty : IsEmpty {w : Fin l → Action // AcceptFrom 0 false (List.ofFn w)} := by
      refine ⟨fun w => ?_⟩
      have hh := (parity (List.ofFn w.1) 0 false w.2).2
      simp only [List.length_ofFn, Nat.zero_mod] at hh
      exact heven (Nat.dvd_of_mod_eq_zero hh.symm)
    haveI := hempty
    rw [coeff_expand_of_not_dvd 2 (by decide) aSeries heven]
    simp [wordSeries, Nat.card_eq_fintype_card]

end D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings
