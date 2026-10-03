/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCancellation
   mirror-E: none(waiver:colored-gap-cancellation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: Color-preserving first-defect involution with its exact fixed-gap characterization. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionSkeleton
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionCancellation

open CiglerStripExpansionSkeleton CiglerStripExpansionPairing

def gapInvolution : List (List Bool) → List (List Bool)
  | evenGap :: oddGap :: rest =>
    if evenGap.length % 2 = 0 then
      match oddGap with
      | [] => evenGap :: [] :: gapInvolution rest
      | color :: colors => (evenGap ++ [color]) :: colors :: rest
    else
      match evenGap.reverse with
      | [] => evenGap :: oddGap :: rest
      | color :: colors => colors.reverse :: (color :: oddGap) :: rest
  | gaps => gaps

def FixedGaps : List (List Bool) → Prop
  | evenGap :: oddGap :: rest =>
    evenGap.length % 2 = 0 ∧ oddGap = [] ∧ FixedGaps rest
  | _ => True

theorem colored_gap_involution :
    (∀ gaps : List (List Bool),
      (gapInvolution gaps).length = gaps.length ∧
        (gapInvolution gaps).flatten = gaps.flatten ∧
        gapInvolution (gapInvolution gaps) = gaps ∧
        (gapInvolution gaps = gaps ↔ FixedGaps gaps) ∧
        (FixedGaps gaps → gapCharge true gaps = 0) ∧
        (gapInvolution gaps ≠ gaps →
          (-1 : ℤ) ^ gapCharge true (gapInvolution gaps) =
            -((-1 : ℤ) ^ gapCharge true gaps))) ∧
      ∃ transform : List (Bool × Bool) → List (Bool × Bool),
        Function.Involutive transform ∧
        (∀ blocks,
          (transform blocks).length = blocks.length ∧
            (extractData (transform blocks)).1 = (extractData blocks).1 ∧
            (extractData (transform blocks)).2.flatten = (extractData blocks).2.flatten ∧
            (transform blocks = blocks ↔ FixedGaps (extractData blocks).2)) ∧
        (∀ bound blocks, IsMotzkinStrip bound (transform blocks) ↔
          IsMotzkinStrip bound blocks) ∧
        (∀ bound blocks, IsMotzkinStrip bound blocks → transform blocks ≠ blocks →
          motzkinWeight true 0 (transform blocks) = -motzkinWeight true 0 blocks) := by
  have properties : ∀ length : ℕ, ∀ gaps : List (List Bool), gaps.length = length →
      (gapInvolution gaps).length = gaps.length ∧
        (gapInvolution gaps).flatten = gaps.flatten ∧
        gapInvolution (gapInvolution gaps) = gaps ∧
        (gapInvolution gaps = gaps ↔ FixedGaps gaps) ∧
        (FixedGaps gaps → gapCharge true gaps = 0) ∧
        (gapInvolution gaps ≠ gaps →
          (-1 : ℤ) ^ gapCharge true (gapInvolution gaps) =
            -((-1 : ℤ) ^ gapCharge true gaps)) := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length induction_hyp =>
      intro gaps length_eq
      cases gaps with
      | nil => simp [gapInvolution, FixedGaps, gapCharge]
      | cons evenGap gaps =>
        cases gaps with
        | nil => simp [gapInvolution, FixedGaps, gapCharge]
        | cons oddGap rest =>
          have smaller : rest.length < length := by
            simp only [List.length_cons] at length_eq
            omega
          have recurse := induction_hyp rest.length smaller rest rfl
          by_cases even_length : evenGap.length % 2 = 0
          · cases oddGap with
            | nil =>
              have image : gapInvolution (evenGap :: [] :: rest) =
                  evenGap :: [] :: gapInvolution rest := by
                rw [gapInvolution, if_pos even_length]
              rw [image]
              refine ⟨by simp [recurse.1], by simp [recurse.2.1], ?_, ?_, ?_, ?_⟩
              · simp [gapInvolution, even_length, recurse.2.2.1]
              · simpa [FixedGaps, even_length] using recurse.2.2.2.1
              · intro fixed
                simpa [gapCharge] using recurse.2.2.2.2.1 fixed.2.2
              · intro not_fixed
                have tail_not_fixed : gapInvolution rest ≠ rest := by
                  intro fixed
                  exact not_fixed (by simp [fixed])
                simpa [gapCharge] using recurse.2.2.2.2.2 tail_not_fixed
            | cons color colors =>
              have new_parity : (evenGap ++ [color]).length % 2 = 1 := by
                simp only [List.length_append, List.length_cons, List.length_nil]
                omega
              have changed : (evenGap ++ [color]) :: colors :: rest ≠
                  evenGap :: (color :: colors) :: rest := by
                intro equal
                have lengths := congrArg (fun data : List (List Bool) =>
                  (data.headD []).length) equal
                simp at lengths
              have image : gapInvolution (evenGap :: (color :: colors) :: rest) =
                  (evenGap ++ [color]) :: colors :: rest := by
                rw [gapInvolution, if_pos even_length]
              refine ⟨by rw [image]; simp, by rw [image]; simp [List.append_assoc],
                ?_, ?_, ?_, ?_⟩
              · calc
                  gapInvolution (gapInvolution (evenGap :: (color :: colors) :: rest)) =
                      gapInvolution ((evenGap ++ [color]) :: colors :: rest) :=
                    congrArg gapInvolution image
                  _ = evenGap :: (color :: colors) :: rest := by
                    have next_odd : (evenGap.length + 1) % 2 = 1 := by
                      simpa using new_parity
                    simp [gapInvolution, next_odd, List.reverse_append]
              · rw [image]
                simp [changed, FixedGaps]
              · simp [FixedGaps]
              · intro not_fixed
                rw [image]
                simp [gapCharge, pow_add, pow_succ, mul_comm]
          · cases reversed : evenGap.reverse with
            | nil =>
              have empty : evenGap = [] := List.reverse_eq_nil_iff.mp reversed
              simp [empty] at even_length
            | cons color colors =>
              have original : evenGap = colors.reverse ++ [color] := by
                have equal := congrArg List.reverse reversed
                simpa using equal
              have new_parity : colors.reverse.length % 2 = 0 := by
                have lengths := congrArg List.length original
                simp at lengths
                simp only [List.length_reverse]
                omega
              have changed : colors.reverse :: (color :: oddGap) :: rest ≠
                  evenGap :: oddGap :: rest := by
                intro equal
                have lengths := congrArg (fun data : List (List Bool) =>
                  (data.headD []).length) equal
                have original_lengths := congrArg List.length original
                simp at lengths original_lengths
                omega
              have image : gapInvolution (evenGap :: oddGap :: rest) =
                  colors.reverse :: (color :: oddGap) :: rest := by
                simp only [gapInvolution, even_length, if_false, reversed]
              refine ⟨by rw [image]; simp, ?_, ?_, ?_, ?_, ?_⟩
              · rw [image]
                simp [original, List.append_assoc]
              · calc
                  gapInvolution (gapInvolution (evenGap :: oddGap :: rest)) =
                      gapInvolution (colors.reverse :: (color :: oddGap) :: rest) :=
                    congrArg gapInvolution image
                  _ = evenGap :: oddGap :: rest := by
                    have length_parity : colors.length % 2 = 0 := by
                      simpa using new_parity
                    simp [gapInvolution, length_parity, original]
              · rw [image]
                simp [changed, FixedGaps, even_length]
              · simp [FixedGaps, even_length]
              · intro not_fixed
                rw [image]
                simp [gapCharge, pow_add, pow_succ, mul_comm]
  have gap_properties (gaps : List (List Bool)) := properties gaps.length gaps rfl
  obtain ⟨correspondence, encode_agrees, decode_agrees, sizes, strips⟩ :=
    skeleton_decomposition
  let transform (blocks : List (Bool × Bool)) :=
    insertData (extractData blocks).1 (gapInvolution (extractData blocks).2)
  have transformed_data (blocks : List (Bool × Bool)) :
      extractData (transform blocks) =
        ((extractData blocks).1, gapInvolution (extractData blocks).2) := by
    have shape := (correspondence blocks).property
    rw [encode_agrees] at shape
    let changed : {data : List Bool × List (List Bool) //
        data.2.length = data.1.length + 1} :=
      ⟨((extractData blocks).1, gapInvolution (extractData blocks).2), by
        simpa only [Prod.fst, Prod.snd, (gap_properties (extractData blocks).2).1] using shape⟩
    have recovered : transform blocks = correspondence.symm changed := by
      simpa only [changed, transform] using (decode_agrees changed).symm
    rw [← encode_agrees, recovered, correspondence.apply_symm_apply]
  have reconstructed (blocks : List (Bool × Bool)) :
      insertData (extractData blocks).1 (extractData blocks).2 = blocks := by
    have recovered := decode_agrees (correspondence blocks)
    rw [correspondence.symm_apply_apply, encode_agrees] at recovered
    exact recovered.symm
  have involutive : Function.Involutive transform := by
    intro blocks
    change insertData (extractData (transform blocks)).1
      (gapInvolution (extractData (transform blocks)).2) = blocks
    rw [transformed_data]
    simp only [(gap_properties (extractData blocks).2).2.2.1]
    exact reconstructed blocks
  have fixed_iff (blocks : List (Bool × Bool)) :
      transform blocks = blocks ↔ FixedGaps (extractData blocks).2 := by
    rw [← (gap_properties (extractData blocks).2).2.2.2.1]
    constructor
    · intro fixed
      have data_eq := congrArg extractData fixed
      rw [transformed_data] at data_eq
      exact congrArg Prod.snd data_eq
    · intro fixed
      change insertData (extractData blocks).1 (gapInvolution (extractData blocks).2) = blocks
      rw [fixed, reconstructed]
  have strip_preserved (bound : ℕ) (blocks : List (Bool × Bool)) :
      IsMotzkinStrip bound (transform blocks) ↔ IsMotzkinStrip bound blocks := by
    rw [strips, strips, transformed_data]
  refine ⟨gap_properties, transform, involutive, ?_, strip_preserved, ?_⟩
  · intro blocks
    refine ⟨?_, ?_, ?_, fixed_iff blocks⟩
    · rw [sizes (transform blocks), transformed_data]
      simp only [(gap_properties (extractData blocks).2).2.1]
      exact (sizes blocks).symm
    · rw [transformed_data]
    · rw [transformed_data]
      exact (gap_properties (extractData blocks).2).2.1
  · intro bound blocks valid nonfixed
    have original_weight := (skeleton_weights bound blocks valid).2
    have changed_weight := (skeleton_weights bound (transform blocks)
      ((strip_preserved bound blocks).mpr valid)).2
    rw [transformed_data] at changed_weight
    simp only [(gap_properties (extractData blocks).2).2.1]
      at changed_weight
    have gap_nonfixed : gapInvolution (extractData blocks).2 ≠ (extractData blocks).2 := by
      intro fixed
      apply nonfixed
      change insertData (extractData blocks).1 (gapInvolution (extractData blocks).2) = blocks
      rw [fixed, reconstructed]
    have sign_reversal := (gap_properties (extractData blocks).2).2.2.2.2.2 gap_nonfixed
    rw [changed_weight, original_weight]
    simp only [pow_add, Polynomial.C_mul, sign_reversal, Polynomial.C_neg,
      mul_neg, neg_mul]

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionCancellation
