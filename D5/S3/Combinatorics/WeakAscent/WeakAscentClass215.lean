/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentClass215
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentClass215
   mirror-E: none(waiver:quadruple-weak-ascent-equivalence)
   anchors: [mathlib/module/Mathlib.Tactic.LinearCombination]
   utility: none
   digest: Replays actual left words as histories and proves Class 215 in every length. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Transitions
import D5.S3.Combinatorics.WeakAscent.WeakAscent215RightWords
import D5.S3.Combinatorics.WeakAscent.WeakAscent215Survivors
import D5.S3.Combinatorics.WeakAscent.WeakAscent215Kernel
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentClass215

open WeakAscentDefs WeakAscentQuadrupleDefs WeakAscent215Renewal
open WeakAscent215Sites WeakAscent215Transitions WeakAscent215WordHistory
open WeakAscent215Pure WeakAscent215Pieces WeakAscent215Decomposition
open WeakAscent215Finite WeakAscent215Products WeakAscent215Endpoints
open WeakAscent215GroupedRenewal WeakAscent215Survivors WeakAscent215Kernel
open Finset PowerSeries
set_option maxHeartbeats 4000000 in
theorem result : WeakAscentQuadrupleDefs.claim215 := by
  classical
  have left_word_histories (word : List ℕ) (hne : word ≠ [])
      (hword : word ∈ avoiders word.length [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]])
      (depth : ℕ) :
      Nonempty ({suffix : List ℕ // suffix.length = depth ∧ word ++ suffix ∈
          avoiders (word.length + depth) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]} ≃
        {steps : List FullStep // steps.length = depth ∧
          FullRun (activeMarks word) (1 + wasc word - word.foldr max 0)
            (decide (word.getLast?.getD 0 = word.foldr max 0)) steps}) := by
    classical
    let patterns : List (List ℕ) := [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]
    let budget (base : List ℕ) := 1 + wasc base - base.foldr max 0
    let mode (base : List ℕ) := decide (base.getLast?.getD 0 = base.foldr max 0)
    let state (base : List ℕ) : List Bool × ℕ × Bool :=
      (activeMarks base, budget base, mode base)
    let Words (base : List ℕ) (size : ℕ) := {suffix : List ℕ // suffix.length = size ∧
      base ++ suffix ∈ avoiders (base.length + size) patterns}
    let Histories (label : List Bool × ℕ × Bool) (size : ℕ) :=
      {steps : List FullStep // steps.length = size ∧ FullRun label.1 label.2.1 label.2.2 steps}
    let next (stack : List Bool) (height : ℕ) (ending : Bool) (count : ℕ)
        (choice : Fin height ⊕ Fin count) : List Bool × ℕ × Bool :=
      match choice with
      | .inl gap => (stack ++ List.replicate gap.val false ++ [true], height - gap.val, true)
      | .inr site =>
        if stack.getD site.val true = false then (stack.take site.val, height, false)
        else
          let repeats := ending && (site.val + 1 == stack.length)
          (bif repeats then [true] else [], bif repeats then height + 1 else height, repeats)
    have prefix_member (base suffix : List ℕ)
        (hmember : base ++ suffix ∈ avoiders (base ++ suffix).length patterns) :
        base ∈ avoiders base.length patterns := by
      refine ⟨rfl, ?_, ?_⟩
      · intro index hindex
        have hbound := hmember.2.1 index (by simp; omega)
        rw [List.getD_append _ _ _ _ hindex,
          List.take_append_of_le_length (Nat.le_of_lt hindex)] at hbound
        exact hbound
      · intro pattern hpattern hoccurs
        apply hmember.2.2 pattern hpattern
        rcases hoccurs with ⟨values, hstep, hletters, hsub, harrows⟩
        exact ⟨values, hstep, fun rank hpos hbound =>
          List.mem_append_left suffix (hletters rank hpos hbound),
          hsub.trans (List.sublist_append_left _ _), by simp⟩
    have replayEquiv : ∀ size : ℕ, ∀ base : List ℕ, base ≠ [] →
        base ∈ avoiders base.length patterns →
          Nonempty (Words base size ≃ Histories (state base) size) := by
      intro size
      induction size with
      | zero =>
        intro base hnonempty hbase
        have hpositive : 0 < budget base := by
          have := (WeakAscent215Sites.left_active_structure base hnonempty hbase).1
          dsimp [budget]
          omega
        let wordZero : Words base 0 := ⟨[], by simp [hbase]⟩
        let historyZero : Histories (state base) 0 := ⟨[], rfl, FullRun.nil _ _ _ hpositive⟩
        refine ⟨⟨fun _ => historyZero, fun _ => wordZero, ?_, ?_⟩⟩
        · intro suffix
          apply Subtype.ext
          exact (List.length_eq_zero_iff.mp suffix.property.1).symm
        · intro steps
          apply Subtype.ext
          exact (List.length_eq_zero_iff.mp steps.property.1).symm
      | succ size ih =>
        intro base hnonempty hbase
        let Letters := {letter : ℕ // base ++ [letter] ∈ avoiders (base.length + 1) patterns}
        have first_admitted (suffix : Words base (size + 1)) :
            base ++ [suffix.val.getD 0 0] ∈ avoiders (base.length + 1) patterns := by
          cases hsuffix : suffix.val with
          | nil => have := suffix.property.1; simp [hsuffix] at this
          | cons letter rest =>
            have hmember := suffix.property.2
            have hlength := suffix.property.1
            simp only [hsuffix, List.length_cons] at hlength
            have hfull : (base ++ [letter]) ++ rest ∈
                avoiders ((base ++ [letter]) ++ rest).length patterns := by
              simpa [hsuffix, List.append_assoc, hlength] using hmember
            simpa [hsuffix] using prefix_member (base ++ [letter]) rest hfull
        have recover_suffix (suffix : Words base (size + 1)) :
            suffix.val.getD 0 0 :: suffix.val.tail = suffix.val := by
          rcases suffix with ⟨values, hlength, hmember⟩
          cases values with
          | nil => simp at hlength
          | cons letter rest => rfl
        let splitWord : Words base (size + 1) → Σ letter : Letters,
            Words (base ++ [letter.val]) size := fun suffix =>
          ⟨⟨suffix.val.getD 0 0, first_admitted suffix⟩, ⟨suffix.val.tail, by
              have hlength := suffix.property.1
              simp only [List.length_tail]
              omega,
            by
              have hmember := suffix.property.2
              simpa only [List.append_assoc, List.singleton_append,
                recover_suffix suffix, List.length_append, List.length_singleton,
                Nat.add_assoc, Nat.add_comm 1 size] using hmember⟩⟩
        let joinWord : (Σ letter : Letters, Words (base ++ [letter.val]) size) →
            Words base (size + 1) := fun piece =>
          ⟨piece.1.val :: piece.2.val, by simp [piece.2.property.1], by
            simpa only [List.length_append, List.length_singleton, List.append_assoc,
              List.singleton_append, Nat.add_assoc, Nat.add_comm 1 size] using piece.2.property.2⟩
        let wordSplit : Words base (size + 1) ≃
            (Σ letter : Letters, Words (base ++ [letter.val]) size) :=
          ⟨splitWord, joinWord, by
            intro suffix
            apply Subtype.ext
            exact recover_suffix suffix, by
            rintro ⟨letter, suffix⟩
            rfl⟩
        obtain ⟨childChoice, hrecord, hsite⟩ := left_transitions base hnonempty hbase
        let Choices := Fin (budget base) ⊕ Fin (activeValues base).length
        have child_nonempty (letter : Letters) : base ++ [letter.val] ≠ [] := by simp
        have child_valid (letter : Letters) :
            base ++ [letter.val] ∈ avoiders (base ++ [letter.val]).length patterns := by
          simpa only [List.length_append, List.length_singleton] using letter.property
        let childHistories (letter : Letters) : Words (base ++ [letter.val]) size ≃
            Histories (state (base ++ [letter.val])) size :=
          Classical.choice (ih _ (child_nonempty letter) (child_valid letter))
        let byLetter := Equiv.sigmaCongrRight childHistories
        let byChoice := (Equiv.sigmaCongrLeft (β := fun letter : Letters =>
          Histories (state (base ++ [letter.val])) size) childChoice).symm
        have marksLength : (activeMarks base).length = (activeValues base).length := by
          simp [activeMarks]
        have state_next (choice : Choices) :
            state (base ++ [(childChoice choice).val]) =
              next (activeMarks base) (budget base) (mode base)
                (activeValues base).length choice := by
          cases choice with
          | inl gap =>
            obtain ⟨hletter, hmarks, hbudget, hmode⟩ := hrecord gap
            change (activeMarks _, budget _, mode _) = _
            exact Prod.ext hmarks (Prod.ext hbudget hmode)
          | inr site =>
            obtain ⟨hletter, hupdate⟩ := hsite site
            dsimp only [next]
            by_cases hfresh : (activeMarks base).getD site.val true = false
            · rw [if_pos hfresh] at hupdate ⊢
              exact Prod.ext hupdate.1 (Prod.ext hupdate.2.1 hupdate.2.2)
            · rw [if_neg hfresh] at hupdate ⊢
              rw [marksLength]
              split at hupdate
              · rename_i htop
                simp only [mode] at ⊢
                rw [htop]
                exact Prod.ext hupdate.1 (Prod.ext hupdate.2.1 hupdate.2.2)
              · rename_i htop
                have hfalse : (mode base &&
                    (site.val + 1 == (activeValues base).length)) = false := by
                  exact Bool.eq_false_of_not_eq_true htop
                rw [hfalse]
                exact Prod.ext hupdate.1 (Prod.ext hupdate.2.1 hupdate.2.2)
        let byState := Equiv.sigmaCongrRight fun choice : Choices =>
          Equiv.cast (congrArg (fun label => Histories label size) (state_next choice))
        have hpositive : 0 < budget base := by
          have := (WeakAscent215Sites.left_active_structure base hnonempty hbase).1
          dsimp [budget]
          omega
        let byHead := Classical.choice
          ((first_old_decomposition (activeMarks base) (budget base) (mode base)).2
            (activeValues base).length size hpositive marksLength)
        exact ⟨wordSplit.trans (byLetter.trans (byChoice.trans (byState.trans byHead.symm)))⟩
    exact replayEquiv depth word hne hword
  have target_series_equation :
      constantCoeff targetSeries = 1 ∧
      (targetSeries - 1) * (1 - X ^ 2 * targetSeries ^ 2) = X * targetSeries ^ 2 ∧
      (∀ degree : ℕ, coeff (degree + 1) targetSeries = (kernelCoefficients degree : ℚ)) := by
    classical
    have causality (R : Type) [CommSemiring R] (degree : ℕ) (first second : PowerSeries R)
        (lower : ∀ index : ℕ, index < degree → coeff index first = coeff index second) :
        coeff degree (positiveStep first) = coeff degree (positiveStep second) := by
      have prodCoeff (bound index : ℕ) (index_bound : index ≤ bound)
          (left right left' right' : PowerSeries R)
          (left_eq : ∀ position ≤ bound, coeff position left = coeff position left')
          (right_eq : ∀ position ≤ bound, coeff position right = coeff position right') :
          coeff index (left * right) = coeff index (left' * right') := by
        rw [coeff_mul, coeff_mul]
        apply sum_congr rfl
        intro pair pair_mem
        have pair_sum := mem_antidiagonal.mp pair_mem
        rw [left_eq pair.1 (by omega), right_eq pair.2 (by omega)]
      have shifted_coeff (index : ℕ) (index_bound : index ≤ degree) :
          coeff index (1 + X * first) = coeff index (1 + X * second) := by
        cases index with
        | zero => simp [coeff_zero_eq_constantCoeff]
        | succ index => simp only [map_add, coeff_succ_X_mul]; rw [lower index (by omega)]
      have square_coeff (index : ℕ) (index_bound : index ≤ degree) :
          coeff index ((1 + X * first) ^ 2) = coeff index ((1 + X * second) ^ 2) := by
        rw [pow_two, pow_two]
        exact prodCoeff degree index index_bound _ _ _ _ shifted_coeff shifted_coeff
      unfold positiveStep
      rw [map_add, map_add, square_coeff degree le_rfl]
      congr 1
      cases degree with
      | zero => simp [coeff_zero_eq_constantCoeff]
      | succ degree =>
        cases degree with
        | zero => simp [coeff_X_pow_mul']
        | succ degree =>
          rw [coeff_X_pow_mul', coeff_X_pow_mul']
          apply prodCoeff degree degree le_rfl
          · intro index index_bound
            exact square_coeff index (by omega)
          · intro index index_bound
            exact lower index (by omega)
    let natTail : PowerSeries ℕ := mk kernelCoefficients
    let ratTail : PowerSeries ℚ := mk fun degree => (kernelCoefficients degree : ℚ)
    have recCoeff (degree : ℕ) :
        kernelCoefficients degree = coeff degree (positiveStep natTail) := by
      conv_lhs => unfold kernelCoefficients; rw [Nat.strongRec_eq]
      apply causality ℕ degree
      intro index index_lower
      simp only [coeff_mk, index_lower, ↓reduceDIte, natTail]
      rfl
    have natFixed : natTail = positiveStep natTail := by
      apply PowerSeries.ext
      intro degree
      simpa only [natTail, coeff_mk] using recCoeff degree
    let castMap := PowerSeries.map (Nat.castRingHom ℚ)
    have tailImage : castMap natTail = ratTail := by
      apply PowerSeries.ext
      intro degree
      simp [castMap, natTail, ratTail]
    have varImage : castMap (X : PowerSeries ℕ) = X := PowerSeries.map_X (Nat.castRingHom ℚ)
    have ratFixed : ratTail = positiveStep ratTail := by
      calc
        ratTail = castMap natTail := tailImage.symm
        _ = castMap (positiveStep natTail) := congrArg castMap natFixed
        _ = positiveStep ratTail := by
          simp only [positiveStep, map_add, map_pow, map_mul, map_one, varImage, tailImage]
    have tailEq :
        ratTail = targetSeries ^ 2 + X ^ 2 * (targetSeries ^ 2 * ratTail) :=
      ratFixed
    have targetEq :
        (targetSeries - 1) * (1 - X ^ 2 * targetSeries ^ 2) = X * targetSeries ^ 2 := by
      have difference : ratTail - X ^ 2 * targetSeries ^ 2 * ratTail = targetSeries ^ 2 := by
        calc
          ratTail - X ^ 2 * targetSeries ^ 2 * ratTail =
              (targetSeries ^ 2 + X ^ 2 * (targetSeries ^ 2 * ratTail)) -
                X ^ 2 * targetSeries ^ 2 * ratTail :=
            congrArg (fun tail => tail - X ^ 2 * targetSeries ^ 2 * ratTail) tailEq
          _ = targetSeries ^ 2 := by ring
      calc
        (targetSeries - 1) * (1 - X ^ 2 * targetSeries ^ 2) =
            X * (ratTail - X ^ 2 * targetSeries ^ 2 * ratTail) := by
          change (1 + X * ratTail - 1) * (1 - X ^ 2 * targetSeries ^ 2) = _
          ring
        _ = X * targetSeries ^ 2 := by rw [difference]
    refine ⟨by simp [targetSeries], targetEq, ?_⟩
    intro degree
    simp [targetSeries, coeff_succ_X_mul, coeff_one]
  have left_history_series :
      1 + X * PowerSeries.map (Nat.castRingHom ℚ) (fullSeries true 1) = targetSeries := by
    classical
    have kernel_algebra {R : Type} [CommRing R] (z t D E H U V tail Y : R)
        (unit : IsUnit (1 - t)) (cancel : Function.Injective fun value : R => t * value)
        (hH : H = D * E)
        (hE : E = z * D + t * E)
        (hV : V = Y + t * tail)
        (h0 : U + z * E * U + t * (z * (H * U) + z * (E * tail)) =
          D + (z * (H * U) + z * (E * tail)) + t * (U + z * E * U))
        (h1 : V + z * (E + 1) * U + t * (z * ((H + D) * U) + z * ((E + 1) * tail)) =
          D + (z * ((H + D) * U) + z * ((E + 1) * tail)) + t * (V + z * (E + 1) * U)) :
        ((t - z) * (1 - t) - (z) ^ 2 * D * (1 + t * (D - 1))) * U =
          (t - z) * D - (z) ^ 2 * D * Y := by
      change E = z * D + t * E at hE
      change V = Y + t * tail at hV
      have r0 : (1 - t) * U = D + (1 - t) * z * (H - E) * U + (1 - t) * z * E * tail := by
        linear_combination h0
      have r1 : (1 - t) * V = D + (1 - t) * z * (H + D - 1 - E) * U +
          (1 - t) * z * (1 + E) * tail := by
        linear_combination h1
      have shift : (t - z) * V = t * (1 + z * (D - 1)) * U - z * Y := by
        have cancelled : (1 - t) * ((t - z) * V - (t * (1 + z * (D - 1)) * U - z * Y)) = 0 := by
          linear_combination t * r1 - t * r0 - z * (1 - t) * hV
        exact sub_eq_zero.mp (unit.mul_left_cancel (by simpa using cancelled))
      have kernel :
          ((t - z) * (1 - t) - z * (1 - t) * E * (1 + t * (D - 1))) * U =
            (t - z) * D - z * (1 - t) * E * Y := by
        apply cancel
        change t * _ = t * _
        rw [hH] at r0
        linear_combination t * (t - z) * r0 +
          z * (1 - t) * E * shift - z * (1 - t) * E * (t - z) * hV
      have ending : (1 - t) * E = z * D := by linear_combination hE
      change ((t - z) * (1 - t) - z ^ 2 * D * (1 + t * (D - 1))) * U = (t - z) * D - z ^ 2 * D * Y
      calc
        _ = ((t - z) * (1 - t) - z * ((1 - t) * E) * (1 + t * (D - 1))) * U := by rw [ending]; ring
        _ = (t - z) * D - z * (1 - t) * E * Y := by simpa only [mul_assoc] using kernel
        _ = _ := by rw [show z * (1 - t) * E = z * ((1 - t) * E) by ring, ending]; ring
    have eliminate_root {R : Type} [CommRing R] (z T d u y : R)
        (d_unit : IsUnit d) (t_unit : IsUnit (1 - T))
        (cancel : Function.Injective fun value : R => z * value)
        (pure : d + T * (1 + z * d) = 1 + z * d + T * (1 + z * d) * d)
        (root : (T - z) * (1 - T) = z ^ 2 * d * (1 + T * (d - 1)))
        (kernel : ((T - z) * (1 - T) - z ^ 2 * d * (1 + T * (d - 1))) * u =
          (T - z) * d - z ^ 2 * d * y) :
        (1 + z * y - 1) * (1 - z ^ 2 * (1 + z * y) ^ 2) = z * (1 + z * y) ^ 2 := by
      have root_y : T = z + z ^ 2 * y := by
        apply d_unit.mul_left_cancel
        linear_combination -kernel + u * root
      let S := z * d
      have pure_equation : (S - z) * (1 - T - T * S) = z * S := by
        dsimp only [S]
        linear_combination z * pure
      have root_equation : (T - z) * (1 - T) = z * S * (1 - T) + T * S ^ 2 := by
        dsimp only [S]
        linear_combination root
      have same : S = T := by
        apply t_unit.mul_left_cancel
        linear_combination pure_equation - root_equation
      have cubic : T * (1 - T - T ^ 2) = z * (1 - T ^ 2) := by
        rw [same] at pure_equation
        linear_combination pure_equation
      apply cancel
      rw [root_y] at cubic
      linear_combination cubic
    have construct_root (kernel : MvPowerSeries (Option Unit) ℚ) :
        constantCoeff (smallRoot kernel) = 0 ∧
        smallRoot kernel = X + X ^ 2 * kernel.subst (fun position =>
          if position = some () then X else smallRoot kernel) := by
      classical
      let evaluate : PowerSeries ℚ → PowerSeries ℚ := fun root =>
        kernel.subst fun position => if position = some () then X else root
      have substCausality (bound : ℕ) (first second : PowerSeries ℚ)
          (firstZero : constantCoeff first = 0) (second_zero : constantCoeff second = 0)
          (lower : ∀ index : ℕ, index < bound → coeff index first = coeff index second)
          (index : ℕ) (index_lower : index < bound) :
          coeff index (evaluate first) = coeff index (evaluate second) := by
        let firstArgs : Option Unit → PowerSeries ℚ := fun position =>
          if position = some () then X else first
        let secondArgs : Option Unit → PowerSeries ℚ := fun position =>
          if position = some () then X else second
        have first_subst : MvPowerSeries.HasSubst firstArgs := by
          apply MvPowerSeries.hasSubst_of_constantCoeff_zero
          intro position
          change constantCoeff (firstArgs position) = 0
          by_cases position_zero : position = some ()
          · simp [firstArgs, position_zero]
          · simpa [firstArgs, position_zero] using firstZero
        have second_subst : MvPowerSeries.HasSubst secondArgs := by
          apply MvPowerSeries.hasSubst_of_constantCoeff_zero
          intro position
          change constantCoeff (secondArgs position) = 0
          by_cases position_zero : position = some ()
          · simp [secondArgs, position_zero]
          · simpa [secondArgs, position_zero] using second_zero
        have tail_truncation :
            MvPowerSeries.truncTotal bound first = MvPowerSeries.truncTotal bound second := by
          apply MvPolynomial.ext
          intro exponent
          by_cases exponent_lower : exponent.degree < bound
          · rw [MvPowerSeries.coeff_truncTotal _ exponent_lower,
              MvPowerSeries.coeff_truncTotal _ exponent_lower]
            rw [← PowerSeries.coeff_def (rfl : exponent () = exponent ())]
            apply lower
            have exponent_eq : exponent = Finsupp.single () (exponent ()) :=
              Finsupp.unique_single exponent
            rw [exponent_eq, Finsupp.degree_single] at exponent_lower
            exact exponent_lower
          · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (not_lt.mp exponent_lower),
              MvPowerSeries.coeff_truncTotal_eq_zero _ (not_lt.mp exponent_lower)]
        have inputs_truncation :
            (fun position =>
              (MvPowerSeries.truncTotal bound (firstArgs position)).toMvPowerSeries) =
              (fun position =>
                (MvPowerSeries.truncTotal bound (secondArgs position)).toMvPowerSeries) := by
          funext position
          by_cases position_zero : position = some ()
          · simp [firstArgs, secondArgs, position_zero]
          · simp [firstArgs, secondArgs, position_zero, tail_truncation]
        have output_truncation :
            MvPowerSeries.truncTotal bound (evaluate first) =
              MvPowerSeries.truncTotal bound (evaluate second) := by
          change (kernel.subst firstArgs).truncTotal bound =
            (kernel.subst secondArgs).truncTotal bound
          rw [MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
              first_subst (x := fun _ => bound) (fun _ => le_rfl),
            MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
              second_subst (x := fun _ => bound) (fun _ => le_rfl), inputs_truncation]
        have exponent_lower : (Finsupp.single () index).degree < bound := by simpa using index_lower
        have output_coeff := congrArg (MvPolynomial.coeff (Finsupp.single () index))
          output_truncation
        simpa only [MvPowerSeries.coeff_truncTotal _ exponent_lower, PowerSeries.coeff]
          using output_coeff
      have root_step_causality (degree : ℕ) (first second : PowerSeries ℚ)
          (firstZero : constantCoeff first = 0) (second_zero : constantCoeff second = 0)
          (lower : ∀ index : ℕ, index < degree → coeff index first = coeff index second) :
          coeff degree (X + X ^ 2 * evaluate first) =
            coeff degree (X + X ^ 2 * evaluate second) := by
        rw [map_add, map_add]
        congr 1
        cases degree with
        | zero => simp [coeff_zero_eq_constantCoeff]
        | succ degree =>
          cases degree with
          | zero => simp [coeff_X_pow_mul']
          | succ degree =>
            rw [coeff_X_pow_mul', coeff_X_pow_mul']
            exact substCausality (degree + 1 + 1) first second firstZero second_zero
              lower degree (by omega)
      have coefficient_zero : smallRootCoefficients kernel 0 = 0 := by
        unfold smallRootCoefficients
        rw [Nat.strongRec_eq]
        simp [coeff_zero_eq_constantCoeff]
      have root_zero : constantCoeff (smallRoot kernel) = 0 := by
        simpa only [smallRoot, constantCoeff_mk] using coefficient_zero
      have recCoeff (degree : ℕ) :
          smallRootCoefficients kernel degree =
            coeff degree (X + X ^ 2 * evaluate (smallRoot kernel)) := by
        conv_lhs => unfold smallRootCoefficients; rw [Nat.strongRec_eq]
        apply root_step_causality degree
        · rw [constantCoeff_mk]
          by_cases degree_positive : 0 < degree
          · simp only [degree_positive, ↓reduceDIte]
            exact coefficient_zero
          · simp [degree_positive]
        · exact root_zero
        · intro index index_lower
          simp only [coeff_mk, smallRoot, index_lower, ↓reduceDIte]
          rfl
      have root_equation :
          smallRoot kernel = X + X ^ 2 * evaluate (smallRoot kernel) := by
        apply PowerSeries.ext
        intro degree
        simpa only [smallRoot, coeff_mk] using recCoeff degree
      exact ⟨root_zero, root_equation⟩
    let castInner := PowerSeries.map (Nat.castRingHom ℚ)
    let castMap := PowerSeries.map castInner
    let z : PowerSeries (PowerSeries ℚ) := castMap (C X)
    let t : PowerSeries (PowerSeries ℚ) := castMap X
    let D := castMap pureSeries
    let E := castMap recordSeries
    let H := castMap survivorSeries
    let U := castMap (budgetSeries false)
    let V := castMap (budgetSeries true)
    let tail := castMap (mk fun budget => fullSeries true (budget + 2))
    let Y := castInner (fullSeries true 1)
    have z_eq : z = C X := by simp [castMap, castInner, z]
    have t_eq : t = X := by simp [castMap, t]
    have hD : D + t * (1 + z * D) = 1 + z * D + t * (1 + z * D) * D := by
      have := congrArg castMap first_record_decomposition.2
      simpa only [map_add, map_mul, map_one] using this
    have hE : E = z * D + t * E := by
      have := congrArg castMap grouped_renewal.1
      simpa only [map_add, map_mul] using this
    have hH : H = D * E := by
      simpa only [map_mul] using congrArg castMap WeakAscent215Survivors.survivor_series
    have h0 : U + z * E * U + t * (z * (H * U) + z * (E * tail)) =
        D + (z * (H * U) + z * (E * tail)) + t * (U + z * E * U) := by
      have original := grouped_renewal.2 false
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at original
      have mapped := congrArg castMap original
      simpa only [map_add, map_mul, mul_assoc] using mapped
    have h1 : V + z * (E + 1) * U + t * (z * ((H + D) * U) + z * ((E + 1) * tail)) =
        D + (z * ((H + D) * U) + z * ((E + 1) * tail)) + t * (V + z * (E + 1) * U) := by
      have original := grouped_renewal.2 true
      simp only [↓reduceIte] at original
      have mapped := congrArg castMap original
      simpa only [map_add, map_mul, map_one, mul_assoc] using mapped
    have hV : V = C Y + t * tail := by
      rw [t_eq]
      apply PowerSeries.ext
      intro budget
      cases budget with
      | zero => simp [V, Y, budgetSeries, castMap, coeff_zero_eq_constantCoeff]
      | succ budget => simp [V, tail, budgetSeries, castMap, coeff_succ_X_mul]
    have unit_t : IsUnit (1 - t) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      rw [t_eq]
      simp
    have cancel_t : Function.Injective fun value : PowerSeries (PowerSeries ℚ) =>
        t * value := by
      rw [t_eq]
      exact PowerSeries.X_mul_injective
    have cleared_kernel := kernel_algebra z t D E H U V tail (C Y) unit_t cancel_t hH hE hV h0 h1
    let geometric : PowerSeries (PowerSeries ℚ) := invOfUnit (1 - t) 1
    have geometric_inverse : (1 - t) * geometric = 1 := by
      apply PowerSeries.mul_invOfUnit
      rw [t_eq]
      simp
    let G := D * (1 + t * (D - 1)) * geometric
    let split := MvPowerSeries.optionEquivLeft Unit ℚ
    let kernel := split.symm G
    let T := smallRoot kernel
    have root_data := construct_root kernel
    have hzero : constantCoeff T = 0 := root_data.1
    let inputs : Option Unit → PowerSeries ℚ :=
      fun position => if position = some () then X else T
    have valid : MvPowerSeries.HasSubst inputs := MvPowerSeries.hasSubst_of_constantCoeff_zero (by
        intro position
        change constantCoeff (inputs position) = 0
        simp only [inputs]
        split_ifs <;> simp [hzero])
    let evaluate : PowerSeries (PowerSeries ℚ) →+* PowerSeries ℚ :=
      (MvPowerSeries.substAlgHom valid).toRingHom.comp split.symm.toRingHom
    have split_constant (series : PowerSeries ℚ) :
        split (series.subst (MvPowerSeries.X (some ()))) = C series := by
      apply PowerSeries.ext
      intro total
      apply PowerSeries.ext
      intro size
      change MvPowerSeries.coeff (Finsupp.single () size) (PowerSeries.coeff total
          (MvPowerSeries.optionEquivLeft Unit ℚ (series.subst (MvPowerSeries.X (some ()))))) = _
      rw [MvPowerSeries.coeff_coeff_optionEquivLeft, PowerSeries.coeff_subst_single]
      have read : (Finsupp.optionElim total (Finsupp.single () size)) (some ()) = size := by simp
      rw [read]
      have isolated : Finsupp.optionElim total (Finsupp.single () size) =
          Finsupp.single (some ()) size ↔ total = 0 := by
        constructor
        · intro heq
          simpa using congrArg (fun exponent => exponent none) heq
        · rintro rfl
          ext position
          cases position <;> simp
      simp only [isolated, coeff_C, apply_ite, map_zero]
      split_ifs <;> rfl
    have constImage (series : PowerSeries ℚ) : evaluate (C series) = series := by
      have preimage : split.symm (C series) = series.subst (MvPowerSeries.X (some ())) :=
        split.injective (by rw [split.apply_symm_apply, split_constant])
      change MvPowerSeries.substAlgHom valid (split.symm (C series)) = series
      rw [MvPowerSeries.substAlgHom_apply]
      rw [preimage]
      change MvPowerSeries.subst inputs
        (MvPowerSeries.subst (fun _ : Unit => MvPowerSeries.X (some ())) series) = series
      have single_valid : MvPowerSeries.HasSubst
          (fun _ : Unit => (MvPowerSeries.X (some ()) : MvPowerSeries (Option Unit) ℚ)) :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro position; simp)
      rw [MvPowerSeries.subst_comp_subst_apply single_valid valid]
      change series.subst (MvPowerSeries.subst inputs (MvPowerSeries.X (some ()))) = series
      rw [MvPowerSeries.subst_X valid]
      simp only [inputs, ↓reduceIte, X_subst]
    have variable_image : evaluate X = T := by
      have preimage : split.symm X = MvPowerSeries.X none :=
        split.injective (by simp [split])
      change MvPowerSeries.substAlgHom valid (split.symm X) = T
      rw [MvPowerSeries.substAlgHom_apply]
      rw [preimage, MvPowerSeries.subst_X valid]
      simp [inputs]
    have root_equation : T = X + X ^ 2 * evaluate G := by
      change smallRoot kernel = X + X ^ 2 * MvPowerSeries.substAlgHom valid (split.symm G)
      rw [MvPowerSeries.substAlgHom_apply]
      exact root_data.2
    have images : evaluate z = X ∧ evaluate t = T :=
      ⟨by rw [z_eq]; exact constImage X, by rw [t_eq]; exact variable_image⟩
    have mapped_pure : evaluate D + T * (1 + X * evaluate D) =
        1 + X * evaluate D + T * (1 + X * evaluate D) * evaluate D := by
      have := congrArg evaluate hD
      simpa only [map_add, map_mul, map_one, images.1, images.2] using this
    have mapped_inverse : (1 - T) * evaluate geometric = 1 := by
      have := congrArg evaluate geometric_inverse
      simpa only [map_sub, map_mul, map_one, images.2] using this
    have mapped_root : (T - X) * (1 - T) = X ^ 2 * evaluate D * (1 + T * (evaluate D - 1)) := by
      have eqG : evaluate G = evaluate D * (1 + T * (evaluate D - 1)) * evaluate geometric := by
        simp only [G, map_mul, map_add, map_sub, map_one, images.2]
      rw [eqG] at root_equation
      have algebra {R : Type} [CommRing R] (z root data inverse : R)
          (heq : root = z + z ^ 2 * data * inverse)
          (hinv : (1 - root) * inverse = 1) :
          (root - z) * (1 - root) = z ^ 2 * data := by
        linear_combination (1 - root) * heq + z ^ 2 * data * hinv
      simpa only [mul_assoc] using algebra X T (evaluate D * (1 + T * (evaluate D - 1)))
        (evaluate geometric) (by simpa only [mul_assoc] using root_equation) mapped_inverse
    have data_unit : IsUnit (evaluate D) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      have hconstant := congrArg constantCoeff mapped_pure
      have : constantCoeff (evaluate D) = 1 := by simpa [hzero] using hconstant
      rw [this]
      exact isUnit_one
    have root_unit : IsUnit (1 - T) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      simp [hzero]
    have mapped_kernel :
        ((T - X) * (1 - T) - X ^ 2 * evaluate D * (1 + T * (evaluate D - 1))) * evaluate U =
        (T - X) * evaluate D - X ^ 2 * evaluate D * Y := by
      have := congrArg evaluate cleared_kernel
      simpa only [map_sub, map_mul, map_add, map_one, map_pow, images.1, images.2,
        constImage] using this
    have equation := eliminate_root X T (evaluate D) (evaluate U) Y
      data_unit root_unit PowerSeries.X_mul_injective mapped_pure mapped_root mapped_kernel
    have causality (R : Type) [CommSemiring R] (degree : ℕ) (first second : PowerSeries R)
        (lower : ∀ index : ℕ, index < degree → coeff index first = coeff index second) :
        coeff degree (positiveStep first) = coeff degree (positiveStep second) := by
      have prodCoeff (bound index : ℕ) (index_bound : index ≤ bound)
          (left right left' right' : PowerSeries R)
          (left_eq : ∀ position ≤ bound, coeff position left = coeff position left')
          (right_eq : ∀ position ≤ bound, coeff position right = coeff position right') :
          coeff index (left * right) = coeff index (left' * right') := by
        rw [coeff_mul, coeff_mul]
        apply sum_congr rfl
        intro pair pair_mem
        have pair_sum := mem_antidiagonal.mp pair_mem
        rw [left_eq pair.1 (by omega), right_eq pair.2 (by omega)]
      have shifted_coeff (index : ℕ) (index_bound : index ≤ degree) :
          coeff index (1 + X * first) = coeff index (1 + X * second) := by
        cases index with
        | zero => simp [coeff_zero_eq_constantCoeff]
        | succ index => simp only [map_add, coeff_succ_X_mul]; rw [lower index (by omega)]
      have square_coeff (index : ℕ) (index_bound : index ≤ degree) :
          coeff index ((1 + X * first) ^ 2) = coeff index ((1 + X * second) ^ 2) := by
        rw [pow_two, pow_two]
        exact prodCoeff degree index index_bound _ _ _ _ shifted_coeff shifted_coeff
      unfold positiveStep
      rw [map_add, map_add, square_coeff degree le_rfl]
      congr 1
      cases degree with
      | zero => simp [coeff_zero_eq_constantCoeff]
      | succ degree =>
        cases degree with
        | zero => simp [coeff_X_pow_mul']
        | succ degree =>
          rw [coeff_X_pow_mul', coeff_X_pow_mul']
          apply prodCoeff degree degree le_rfl
          · intro index index_bound
            exact square_coeff index (by omega)
          · intro index index_bound
            exact lower index (by omega)
    let ratTail : PowerSeries ℚ := mk fun degree => (kernelCoefficients degree : ℚ)
    have ratFixed : ratTail = positiveStep ratTail := by
      let series := targetSeries
      have seriesShift : series = 1 + X * ratTail := rfl
      have equation := target_series_equation.2.1
      apply PowerSeries.X_mul_injective
      change X * ratTail = X * ((1 + X * ratTail) ^ 2 + X ^ 2 * ((1 + X * ratTail) ^ 2 * ratTail))
      rw [← seriesShift]
      calc
        X * ratTail = (series - 1) * (1 - X ^ 2 * series ^ 2) + X ^ 3 * series ^ 2 * ratTail := by
          rw [seriesShift]
          ring
        _ = X * (series ^ 2 + X ^ 2 * (series ^ 2 * ratTail)) := by rw [equation]; ring
    have uniqueness (series : PowerSeries ℚ) (constOne : constantCoeff series = 1)
        (equation : (series - 1) * (1 - X ^ 2 * series ^ 2) = X * series ^ 2) :
        series = targetSeries := by
      let tail := mk fun degree => coeff (degree + 1) series
      have seriesShift : series = 1 + X * tail := by
        simpa [constOne, tail, add_comm] using eq_X_mul_shift_add_const series
      have tail_fixed : tail = positiveStep tail := by
        apply PowerSeries.X_mul_injective
        change X * tail = X * ((1 + X * tail) ^ 2 + X ^ 2 * ((1 + X * tail) ^ 2 * tail))
        rw [← seriesShift]
        calc
          X * tail = (series - 1) * (1 - X ^ 2 * series ^ 2) + X ^ 3 * series ^ 2 * tail := by
            rw [seriesShift]
            ring
          _ = X * (series ^ 2 + X ^ 2 * (series ^ 2 * tail)) := by rw [equation]; ring
      have tail_equal : tail = ratTail := by
        apply PowerSeries.ext
        intro degree
        induction degree using Nat.strong_induction_on with
        | h degree previous =>
          calc
            coeff degree tail = coeff degree (positiveStep tail) :=
              congrArg (coeff degree) tail_fixed
            _ = coeff degree (positiveStep ratTail) := causality ℚ degree tail ratTail previous
            _ = coeff degree ratTail := (congrArg (coeff degree) ratFixed).symm
      rw [seriesShift, tail_equal]
      rfl
    exact uniqueness (1 + X * Y) (by simp) equation
  have series := left_history_series
  let patterns : List (List ℕ) := [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]
  have short_valid (word : List ℕ) (hweak : IsWeakAscent word) (hshort : word.length < 3) :
      word ∈ avoiders word.length patterns := by
    refine ⟨rfl, hweak, ?_⟩
    intro pattern hpattern hoccurs
    rcases hoccurs with ⟨values, hstep, hletters, hsub, harrows⟩
    have hlength := hsub.length_le
    have hthree : pattern.length = 3 := by
      simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl | rfl <;> rfl
    simp only [List.length_map, hthree] at hlength
    omega
  have zero_valid : [0] ∈ avoiders 1 patterns := by
    apply short_valid
    · intro index hindex
      have : index = 0 := by simpa using hindex
      subst index
      simp
    · simp
  have double_zero_valid : [0, 0] ∈ avoiders 2 patterns := by
    apply short_valid
    · intro index hindex
      have : index = 0 ∨ index = 1 := by simp at hindex; omega
      rcases this with rfl | rfl <;> simp [wasc]
    · simp
  have marks : activeMarks [0] = [true] := by
    have values : activeValues [0] = [0] := by
      simp only [activeValues, List.foldr_cons, List.foldr_nil, Nat.max_self,
        Nat.zero_add, Finset.range_one]
      rw [Finset.filter_singleton]
      change ((if [0, 0] ∈ avoiders 2 patterns then ({0} : Finset ℕ) else ∅).sort
        (fun first second => first ≤ second)) = [0]
      rw [if_pos double_zero_valid]
      simp
    simp [activeMarks, values]
  intro size
  cases size with
  | zero =>
    have left_zero : avoiders 0 patterns = {[]} := by
      ext word
      constructor
      · intro hword
        exact List.length_eq_zero_iff.mp hword.1
      · rintro rfl
        apply short_valid
        · intro index hindex
          simp at hindex
        · simp
    have right_zero : avoiders 0 [[1, 3, 2], [2, 1, 2], [3, 1, 2], [3, 2, 1]] = {[]} := by
      ext word
      constructor
      · intro hword
        exact List.length_eq_zero_iff.mp hword.1
      · rintro rfl
        refine ⟨rfl, ?_, ?_⟩
        · intro index hindex
          simp at hindex
        · intro pattern hpattern hoccurs
          rcases hoccurs with ⟨values, hstep, hletters, hsub, harrows⟩
          have hlength := hsub.length_le
          have hthree : pattern.length = 3 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
            rcases hpattern with rfl | rfl | rfl | rfl <;> rfl
          simp [hthree] at hlength
    change (avoiders 0 patterns).ncard = _
    rw [left_zero, right_zero]
  | succ size =>
    let Suffix := {suffix : List ℕ // suffix.length = size ∧
      [0] ++ suffix ∈ avoiders (size + 1) patterns}
    let prepend : Suffix → avoiders (size + 1) patterns := fun suffix =>
      ⟨[0] ++ suffix.val, suffix.property.2⟩
    have firstZero (word : List ℕ) (hword : word ∈ avoiders (size + 1) patterns) :
        word = 0 :: word.tail := by
      cases word with
      | nil => have hlength := hword.1; simp at hlength
      | cons first rest =>
        have hfirst := hword.2.1 0 (by simp)
        simp only [List.getD_cons_zero] at hfirst
        have : first = 0 := Nat.eq_zero_of_le_zero hfirst
        subst first
        rfl
    let remove : avoiders (size + 1) patterns → Suffix := fun word =>
      ⟨word.val.tail, by
        have hword := firstZero word.val word.property
        constructor
        · have hlength := word.property.1
          rw [hword, List.length_cons] at hlength
          omega
        · simpa only [List.singleton_append, ← hword] using word.property⟩
    let equivalence : Suffix ≃ avoiders (size + 1) patterns :=
      { toFun := prepend
        invFun := remove
        left_inv := fun suffix => by apply Subtype.ext; rfl
        right_inv := fun word => by
          apply Subtype.ext
          exact (firstZero word.val word.property).symm }
    obtain ⟨histories⟩ := left_word_histories [0] (by simp) zero_valid size
    have history_card : Nat.card Suffix = Nat.card {steps : List FullStep //
          steps.length = size ∧ FullRun [true] 1 true steps} := by
      have := Nat.card_congr histories
      simpa only [marks, wasc, List.zip_cons_cons, List.tail_cons, List.zip_nil_right,
        List.filter_nil, List.length_nil, List.foldr_cons, List.foldr_nil,
        Nat.max_self, Nat.add_zero, Nat.sub_zero, List.getLast?_singleton, Option.getD_some,
        decide_true, List.length_singleton, Nat.add_comm] using this
    have count : ((avoiders (size + 1) patterns).ncard : ℚ) =
        PowerSeries.coeff (size + 1) WeakAscent215Kernel.targetSeries := by
      rw [← series, map_add, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_one, if_neg (by omega), zero_add, PowerSeries.coeff_map]
      simp only [fullSeries, PowerSeries.coeff_mk]
      change ((avoiders (size + 1) patterns).ncard : ℚ) = (Nat.card {steps : List FullStep //
          steps.length = size ∧ FullRun [true] 1 true steps} : ℚ)
      rw [← history_card, Nat.card_congr equivalence, Nat.card_coe_set_eq]
    apply Nat.cast_injective (R := ℚ)
    exact count.trans (WeakAscent215RightWords.right_word_counts (size + 1)).symm
end D5.S3.Combinatorics.WeakAscent.WeakAscentClass215
