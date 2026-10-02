/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215RightWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215RightWords
   mirror-E: none(waiver:right-word-generating-tree-bijection)
   anchors: [mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: Splits actual right words bijectively into children and counts their continuations. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Right
import D5.S3.Combinatorics.WeakAscent.WeakAscent215RightCounting
import D5.S3.Combinatorics.WeakAscent.WeakAscent215Kernel
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215RightWords

open WeakAscentDefs WeakAscentQuadrupleDefs WeakAscent215Right WeakAscent215RightCounting
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs (Occurs)
open WeakAscent215Kernel
open Finset PowerSeries
theorem right_word_counts (length : ℕ) :
    ((avoiders length [[1, 3, 2], [2, 1, 2], [3, 1, 2], [3, 2, 1]]).ncard : ℚ) =
      PowerSeries.coeff length WeakAscent215Kernel.targetSeries := by
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
  have right_continuation_certificate (series : PowerSeries ℚ)
      (constOne : constantCoeff series = 1)
      (left_equation : (series - 1) * (1 - X ^ 2 * series ^ 2) = X * series ^ 2) :
      (∀ budget : ℕ, 0 < budget →
        qSeries budget = numerator series * ratio series ^ (budget - 1) ∧
        pSeries budget = positiveBase series * ratio series ^ (budget - 1)) ∧
      (∀ budget : ℕ, 0 < budget → qSeries budget = 1 + X * (qSeries (budget + 1) +
          ∑ index ∈ range budget, pSeries (index + 1)) ∧
        pSeries budget = 1 + X * (qSeries budget + pSeries (budget + 1) +
          ∑ index ∈ range budget, pSeries (index + 1))) ∧
      (∀ zeroFamily positiveFamily : ℕ → PowerSeries ℚ, (∀ budget : ℕ, 0 < budget →
          zeroFamily budget = 1 + X * (zeroFamily (budget + 1) +
            ∑ index ∈ range budget, positiveFamily (index + 1)) ∧
          positiveFamily budget = 1 + X * (zeroFamily budget + positiveFamily (budget + 1) +
            ∑ index ∈ range budget, positiveFamily (index + 1))) →
        ∀ budget : ℕ, 0 < budget →
          zeroFamily budget = qSeries budget ∧ positiveFamily budget = pSeries budget) := by
    classical
    let indeterminate : PowerSeries ℚ := X
    let denominator : PowerSeries ℚ := 1 - indeterminate ^ 2 * series ^ 2
    let base := numerator series
    let growth := ratio series
    let positive := positiveBase series
    have denominator_one : constantCoeff denominator = 1 := by simp [denominator, indeterminate]
    have seriesInv : series * series⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel series (by rw [constOne]; exact one_ne_zero)
    have denomInv : denominator * denominator⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel denominator (by rw [denominator_one]; exact one_ne_zero)
    have base_denominator : base * denominator = series ^ 2 := by
      change (series ^ 2 * denominator⁻¹) * denominator = series ^ 2
      calc
        (series ^ 2 * denominator⁻¹) * denominator =
            series ^ 2 * (denominator * denominator⁻¹) := by ring
        _ = series ^ 2 := by rw [denomInv, mul_one]
    have series_base : series = 1 + indeterminate * base := by
      calc
        series = 1 + (series - 1) := by ring
        _ = 1 + ((series - 1) * denominator) * denominator⁻¹ := by
          rw [mul_assoc, denomInv, mul_one]
        _ = 1 + indeterminate * base := by
          rw [show (series - 1) * denominator = indeterminate * series ^ 2 from left_equation]
          change 1 + indeterminate * series ^ 2 * denominator⁻¹ =
            1 + indeterminate * (series ^ 2 * denominator⁻¹)
          ring
    have base_expand : base = series ^ 2 + indeterminate ^ 2 * series ^ 2 * base := by
      calc
        base = base * denominator + indeterminate ^ 2 * series ^ 2 * base := by
          dsimp [denominator]
          ring
        _ = series ^ 2 + indeterminate ^ 2 * series ^ 2 * base := by rw [base_denominator]
    have base_difference : base - series = indeterminate * series * positive := by
      calc
        base - series = series * (series - 1) + indeterminate ^ 2 * series ^ 2 * base := by
          conv_lhs => rw [base_expand]
          ring
        _ = indeterminate * series * positive := by
          rw [show series - 1 = indeterminate * base by rw [series_base]; ring]
          dsimp [positive, positiveBase, base]
          ring
    have growth_difference : growth - 1 = indeterminate * positive := by
      calc
        growth - 1 = (base - series) * series⁻¹ := by
          dsimp [growth, ratio, base]
          rw [sub_mul, seriesInv]
        _ = indeterminate * positive := by
          rw [base_difference]
          calc
            indeterminate * series * positive * series⁻¹ =
                indeterminate * positive * (series * series⁻¹) := by ring
            _ = indeterminate * positive := by rw [seriesInv, mul_one]
    have inverse_relation : 1 - indeterminate * growth = series⁻¹ := by
      calc
        1 - indeterminate * growth = (series - indeterminate * base) * series⁻¹ := by
          dsimp [growth, ratio, base]
          rw [sub_mul, seriesInv]
          ring
        _ = series⁻¹ := by rw [series_base]; ring
    have positive_relation :
        positive * (1 - indeterminate * growth) = growth + indeterminate * base := by
      rw [inverse_relation]
      change (base * (1 + indeterminate * series)) * series⁻¹ = growth + indeterminate * base
      calc
        (base * (1 + indeterminate * series)) * series⁻¹ =
            base * series⁻¹ + indeterminate * base * (series * series⁻¹) := by ring
        _ = growth + indeterminate * base := by rw [seriesInv, mul_one]; rfl
    have growth_base : series * growth = base := by
      change series * (base * series⁻¹) = base
      calc
        series * (base * series⁻¹) = base * (series * series⁻¹) := by ring
        _ = base := by rw [seriesInv, mul_one]
    have finite_sum (budget : ℕ) :
        indeterminate * (∑ index ∈ range budget, positive * growth ^ index) =
          growth ^ budget - 1 := by
      rw [← mul_sum]
      calc
        indeterminate * (positive * ∑ index ∈ range budget, growth ^ index) =
            (growth - 1) * ∑ index ∈ range budget, growth ^ index := by
          rw [growth_difference]
          ring
        _ = growth ^ budget - 1 := mul_geom_sum growth budget
    have candidate_recurrence (budget : ℕ) (budgetPos : 0 < budget) :
        base * growth ^ (budget - 1) = 1 + indeterminate * (base * growth ^ budget +
              ∑ index ∈ range budget, positive * growth ^ index) ∧
        positive * growth ^ (budget - 1) =
            1 + indeterminate * (base * growth ^ (budget - 1) + positive * growth ^ budget +
              ∑ index ∈ range budget, positive * growth ^ index) := by
      have budget_step : budget - 1 + 1 = budget := Nat.sub_add_cancel budgetPos
      have power_step : growth ^ budget = growth ^ (budget - 1) * growth := by
        calc
          growth ^ budget = growth ^ (budget - 1 + 1) := congrArg (growth ^ ·) budget_step.symm
          _ = growth ^ (budget - 1) * growth := pow_succ growth (budget - 1)
      constructor
      · calc
          base * growth ^ (budget - 1) = series * growth ^ budget := by
            rw [power_step, ← growth_base]
            ring
          _ = 1 + indeterminate * (base * growth ^ budget +
                ∑ index ∈ range budget, positive * growth ^ index) := by
            rw [mul_add, finite_sum, series_base]
            ring
      · have positive_expand :
            positive = growth + indeterminate * base + indeterminate * positive * growth := by
          calc
            positive = positive * (1 - indeterminate * growth) +
                indeterminate * positive * growth := by ring
            _ = growth + indeterminate * base + indeterminate * positive * growth := by
              rw [positive_relation]
        calc
          positive * growth ^ (budget - 1) =
              (growth + indeterminate * base + indeterminate * positive * growth) *
                growth ^ (budget - 1) := by rw [← positive_expand]
          _ = 1 + indeterminate * (base * growth ^ (budget - 1) + positive * growth ^ budget +
                ∑ index ∈ range budget, positive * growth ^ index) := by
            rw [mul_add, finite_sum, power_step]
            ring
    have recurrence (budget : ℕ) :
        qSeries budget = 1 + X * (qSeries (budget + 1) +
          ∑ index ∈ range budget, pSeries (index + 1)) ∧
        pSeries budget = 1 + X * (qSeries budget + pSeries (budget + 1) +
          ∑ index ∈ range budget, pSeries (index + 1)) := by
      constructor <;> apply PowerSeries.ext <;> intro degree
      all_goals cases degree with
      | zero => simp [qSeries, pSeries, continuationCounts, coeff_zero_eq_constantCoeff]
      | succ degree => simp [qSeries, pSeries, continuationCounts, coeff_succ_X_mul, coeff_one]
    have uniqueness (zeroFamily positiveFamily : ℕ → PowerSeries ℚ)
        (family_recurrence : ∀ budget : ℕ, 0 < budget →
          zeroFamily budget = 1 + X * (zeroFamily (budget + 1) +
            ∑ index ∈ range budget, positiveFamily (index + 1)) ∧
          positiveFamily budget = 1 + X * (zeroFamily budget + positiveFamily (budget + 1) +
            ∑ index ∈ range budget, positiveFamily (index + 1))) :
        ∀ budget : ℕ, 0 < budget →
          zeroFamily budget = qSeries budget ∧ positiveFamily budget = pSeries budget := by
      have degrees : ∀ degree budget : ℕ, 0 < budget →
          coeff degree (zeroFamily budget) = coeff degree (qSeries budget) ∧
          coeff degree (positiveFamily budget) = coeff degree (pSeries budget) := by
        intro degree
        induction degree with
        | zero =>
          intro budget budgetPos
          rcases family_recurrence budget budgetPos with ⟨zero_eq, positive_eq⟩
          constructor
          · rw [zero_eq]
            simp [qSeries, continuationCounts, coeff_zero_eq_constantCoeff]
          · rw [positive_eq]
            simp [pSeries, continuationCounts, coeff_zero_eq_constantCoeff]
        | succ degree induction_hypothesis =>
          intro budget budgetPos
          rcases family_recurrence budget budgetPos with ⟨zero_eq, positive_eq⟩
          rcases recurrence budget with ⟨count_zero_eq, count_positive_eq⟩
          have sum_eq :
              ∑ index ∈ range budget, coeff degree (positiveFamily (index + 1)) =
                ∑ index ∈ range budget, coeff degree (pSeries (index + 1)) := by
            apply sum_congr rfl
            intro index _
            exact (induction_hypothesis (index + 1) (Nat.succ_pos index)).2
          constructor
          · rw [zero_eq, count_zero_eq]
            simp only [map_add, coeff_succ_X_mul, map_sum]
            rw [(induction_hypothesis (budget + 1) (Nat.succ_pos budget)).1, sum_eq]
          · rw [positive_eq, count_positive_eq]
            simp only [map_add, coeff_succ_X_mul, map_sum]
            rw [(induction_hypothesis budget budgetPos).1,
              (induction_hypothesis (budget + 1) (Nat.succ_pos budget)).2, sum_eq]
      intro budget budgetPos
      exact ⟨PowerSeries.ext fun degree => (degrees degree budget budgetPos).1,
        PowerSeries.ext fun degree => (degrees degree budget budgetPos).2⟩
    have candidateEq := uniqueness (fun budget => base * growth ^ (budget - 1))
      (fun budget => positive * growth ^ (budget - 1)) (by
        intro budget budgetPos
        simpa [indeterminate] using candidate_recurrence budget budgetPos)
    refine ⟨?_, fun budget _ => recurrence budget, uniqueness⟩
    intro budget budgetPos
    exact ⟨(candidateEq budget budgetPos).1.symm, (candidateEq budget budgetPos).2.symm⟩
  classical
  let patterns : List (List ℕ) := [[1, 3, 2], [2, 1, 2], [3, 1, 2], [3, 2, 1]]
  let extensions (base : List ℕ) (depth : ℕ) : Set (List ℕ) :=
    {word | word ∈ avoiders (base.length + depth) patterns ∧ word.take base.length = base}
  let budget (word : List ℕ) := 1 + wasc word - word.foldr max 0
  let count (depth : ℕ) (word : List ℕ) :=
    if word.getLast?.getD 0 = 0 then (continuationCounts depth (budget word)).1
    else (continuationCounts depth (budget word)).2
  have finite_words (size : ℕ) : (avoiders size patterns).Finite := by
    have coordinate_bound (word : List ℕ) (hweak : IsWeakAscent word) (index : ℕ)
        (hindex : index < word.length) : word.getD index 0 ≤ index := by
      have hbound := hweak index hindex
      by_cases hzero : index = 0
      · simpa [hzero] using hbound
      · have hfilter := List.length_filter_le (fun pair : ℕ × ℕ => decide (pair.1 ≤ pair.2))
          ((word.take index).zip (word.take index).tail)
        simp only [List.length_zip, List.length_tail, List.length_take] at hfilter
        simp only [if_neg hzero] at hbound
        unfold wasc at hbound
        omega
    let decode (coordinates : Fin size → Fin (size + 1)) : List ℕ :=
      List.ofFn fun index => (coordinates index).val
    apply (Set.finite_univ.image decode).subset
    intro word hmember
    have hlength : word.length = size := hmember.1
    let coordinates : Fin size → Fin (size + 1) := fun index =>
      ⟨word.getD index.val 0, by
        have hindex : index.val < word.length := by simp [hlength]
        have hbound := coordinate_bound word hmember.2.1 index.val hindex
        omega⟩
    refine ⟨coordinates, Set.mem_univ _, ?_⟩
    apply List.ext_getElem
    · simp [decode, hlength]
    · intro index hleft hright
      simp only [decode, List.getElem_ofFn, coordinates]
      exact List.getD_eq_getElem word 0 hright
  have finite_extensions (base : List ℕ) (depth : ℕ) : (extensions base depth).Finite :=
    (finite_words (base.length + depth)).subset fun _ hmember => hmember.1
  let (base : List ℕ) (depth : ℕ) : Fintype (extensions base depth) :=
    (finite_extensions base depth).fintype
  have prefix_member (word : List ℕ) (size : ℕ)
      (hword : word ∈ avoiders word.length patterns) (hsize : size ≤ word.length) :
      word.take size ∈ avoiders size patterns := by
    have prefix_read (index : ℕ) (hindex : index < size) :
        (word.take size).getD index 0 = word.getD index 0 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hindex]
    refine ⟨by simp [List.length_take, min_eq_left hsize], ?_, ?_⟩
    · intro index hindex
      have hi : index < size := by simpa [List.length_take, min_eq_left hsize] using hindex
      rw [prefix_read index hi, List.take_take, min_eq_left (by omega)]
      exact hword.2.1 index (by omega)
    · intro pattern hpattern hoccurs
      apply hword.2.2 pattern hpattern
      rcases hoccurs with ⟨values, hstep, hletters, hsub, harrows⟩
      exact ⟨values, hstep,
        fun rank hpos hbound => List.mem_of_mem_take (hletters rank hpos hbound),
        hsub.trans (List.take_sublist _ _), by simp⟩
  have ascents_append (parent : List ℕ) (letter : ℕ) :
      wasc (parent ++ [letter]) = wasc parent +
        if parent = [] then 0 else if parent.getLast?.getD 0 ≤ letter then 1 else 0 := by
    induction parent with
    | nil => simp [wasc]
    | cons first rest ih =>
      cases rest with
      | nil => by_cases hpair : first ≤ letter <;> simp [wasc, hpair]
      | cons second tail =>
        simp only [List.cons_append, wasc, List.tail_cons, List.zip_cons_cons,
          List.filter_cons] at ih ⊢
        by_cases hpair : first ≤ second
        · simp [hpair, List.getLast?_cons_cons, List.cons_ne_nil] at ih ⊢
          omega
        · simp only [decide_eq_true_eq, hpair, reduceCtorEq, ↓reduceIte,
            List.getLast?_cons_cons] at ih ⊢
          exact ih
  have maximum_append (parent : List ℕ) (letter : ℕ) :
      (parent ++ [letter]).foldr max 0 = max (parent.foldr max 0) letter := by
    induction parent with
    | nil => simp
    | cons first rest ih => simp [ih, max_assoc]
  have continuation_count : ∀ depth : ℕ, ∀ base : List ℕ, base ≠ [] →
      base ∈ avoiders base.length patterns →
      (extensions base depth).ncard = count depth base := by
    intro depth
    induction depth with
    | zero =>
      intro base hne hbase
      have hsingleton : extensions base 0 = {base} := by
        ext word
        constructor
        · rintro ⟨hword, hprefix⟩
          have hlength : word.length = base.length := by simpa using hword.1
          rw [← hlength, List.take_length] at hprefix
          exact hprefix
        · intro hword
          have heq : word = base := hword
          subst word
          exact ⟨by simpa using hbase, List.take_length⟩
      rw [hsingleton, Set.ncard_singleton]
      simp [count, continuationCounts]
    | succ depth ih =>
      intro base hne hbase
      let maximum := base.foldr max 0
      let height := 1 + wasc base
      have hheight : maximum < height := WeakAscentGrowth.height_dominates base hbase.2.1
      have hbudget : 0 < budget base := by dsimp [budget, height, maximum] at *; omega
      have hlastbound : base.getLast?.getD 0 ≤ maximum := by
        rw [List.getLast?_eq_some_getLast hne, Option.getD_some]
        exact List.le_max_of_le (List.getLast_mem hne) (Nat.le_refl _)
      let Letters := {letter : ℕ // base ++ [letter] ∈
        avoiders (base.length + 1) patterns}
      let Choices := Unit ⊕ (Fin (budget base) ⊕
        Fin (if base.getLast?.getD 0 = 0 then 0 else 1))
      let chosen : Choices → ℕ
        | .inl _ => 0
        | .inr (.inl record) => maximum + budget base - record.val
        | .inr (.inr _) => maximum
      have chosen_valid (choice : Choices) : base ++ [chosen choice] ∈
          avoiders (base.length + 1) patterns := by
        apply (right_append_iff base (chosen choice) hne hbase).mpr
        cases choice with
        | inl zeroChoice => exact ⟨Nat.zero_le _, Or.inl rfl⟩
        | inr positiveChoice =>
          cases positiveChoice with
          | inl record =>
            have hi := record.isLt
            dsimp [chosen]
            have hsum : maximum + budget base = height := by dsimp [budget]; omega
            constructor
            · dsimp [height] at hsum
              omega
            · exact Or.inr (Or.inl (by omega))
          | inr repeatChoice =>
            have hpositive : base.getLast?.getD 0 ≠ 0 := by
              intro hzero
              have hi := repeatChoice.isLt
              simp [hzero] at hi
            dsimp [chosen]
            exact ⟨by dsimp [height] at hheight; omega, Or.inr (Or.inr ⟨rfl, by omega⟩)⟩
      let chooseLetter : Choices → Letters :=
        fun choice => ⟨chosen choice, chosen_valid choice⟩
      have chosen_injective : Function.Injective chooseLetter := by
        intro first second heq
        have hvalue : chosen first = chosen second := congrArg Subtype.val heq
        have hrecord (record : Fin (budget base)) :
            maximum < maximum + budget base - record.val := by
          have hi := record.isLt
          omega
        have hrepeat (repeatChoice : Fin (if base.getLast?.getD 0 = 0 then 0 else 1)) :
            0 < maximum := by
          have hpositive : base.getLast?.getD 0 ≠ 0 := by
            intro hzero
            have hi := repeatChoice.isLt
            simp [hzero] at hi
          omega
        cases first with
        | inl first =>
          cases second with
          | inl second => congr
          | inr second =>
            cases second with
            | inl record => have := hrecord record; dsimp [chosen] at hvalue; omega
            | inr repeatChoice =>
              have := hrepeat repeatChoice
              dsimp [chosen] at hvalue
              omega
        | inr first =>
          cases first with
          | inl first =>
            cases second with
            | inl zeroChoice => have := hrecord first; dsimp [chosen] at hvalue; omega
            | inr second =>
              cases second with
              | inl second =>
                have hfirst := first.isLt
                have hsecond := second.isLt
                have hindex : first.val = second.val := by dsimp [chosen] at hvalue; omega
                exact congrArg (fun record => Sum.inr (Sum.inl record)) (Fin.ext hindex)
              | inr repeatChoice =>
                have := hrecord first
                dsimp [chosen] at hvalue
                omega
          | inr first =>
            cases second with
            | inl zeroChoice => have := hrepeat first; dsimp [chosen] at hvalue; omega
            | inr second =>
              cases second with
              | inl record => have := hrecord record; dsimp [chosen] at hvalue; omega
              | inr second =>
                have hpositive : base.getLast?.getD 0 ≠ 0 := by
                  intro hzero
                  have hi := first.isLt
                  simp [hzero] at hi
                have hindex : first = second := by
                  apply Fin.ext
                  have hfirst := first.isLt
                  have hsecond := second.isLt
                  simp only [if_neg hpositive] at hfirst hsecond
                  omega
                exact congrArg (fun repeatChoice => Sum.inr (Sum.inr repeatChoice)) hindex
      have chosen_surjective : Function.Surjective chooseLetter := by
        intro letter
        have hlegal := (right_append_iff base letter.val hne hbase).mp letter.property
        rcases hlegal.2 with hzero | hrecord | ⟨hrepeat, hpositive⟩
        · refine ⟨.inl (), Subtype.ext ?_⟩
          exact hzero.symm
        · have hsum : maximum + budget base = height := by dsimp [budget]; omega
          let index : Fin (budget base) := ⟨height - letter.val, by
            dsimp [height, maximum] at *
            omega⟩
          refine ⟨.inr (.inl index), Subtype.ext ?_⟩
          dsimp [chooseLetter, chosen, index]
          dsimp [height] at hsum
          omega
        · let repeatChoice : Fin (if base.getLast?.getD 0 = 0 then 0 else 1) :=
            ⟨0, by simp [show base.getLast?.getD 0 ≠ 0 by omega]⟩
          exact ⟨.inr (.inr repeatChoice), Subtype.ext hrepeat.symm⟩
      let choiceEquiv : Choices ≃ Letters :=
        Equiv.ofBijective chooseLetter ⟨chosen_injective, chosen_surjective⟩
      let : Finite Letters := Finite.of_equiv Choices choiceEquiv
      let : Fintype Letters := Fintype.ofFinite Letters
      have first_child (word : extensions base (depth + 1)) :
          word.val.take (base.length + 1) = base ++ [word.val.getD base.length 0] := by
        have hlength : word.val.length = base.length + (depth + 1) := word.property.1.1
        rw [List.take_succ_eq_append_getElem (by omega), word.property.2,
          List.getD_eq_getElem _ _ (by omega)]
      have first_admitted (word : extensions base (depth + 1)) :
          base ++ [word.val.getD base.length 0] ∈ avoiders (base.length + 1) patterns := by
        have hlength : word.val.length = base.length + (depth + 1) := word.property.1.1
        have hmember := prefix_member word.val (base.length + 1)
          ⟨rfl, word.property.1.2⟩ (by omega)
        rwa [first_child word] at hmember
      let splitExtension : extensions base (depth + 1) →
          Σ letter : Letters, extensions (base ++ [letter.val]) depth := fun word =>
        ⟨⟨word.val.getD base.length 0, first_admitted word⟩, ⟨word.val, ⟨by
            refine ⟨?_, word.property.1.2⟩
            have hlength := word.property.1.1
            simp only [List.length_append, List.length_singleton]
            omega,
          by simpa only [List.length_append, List.length_singleton] using first_child word⟩⟩⟩
      let joinExtension : (Σ letter : Letters, extensions (base ++ [letter.val]) depth) →
          extensions base (depth + 1) := fun child =>
        ⟨child.2.val, ⟨by
          refine ⟨?_, child.2.property.1.2⟩
          have hlength := child.2.property.1.1
          simp only [List.length_append, List.length_singleton] at hlength
          omega,
        by
          have hprefix := congrArg (List.take base.length) child.2.property.2
          simp only [List.length_append, List.length_singleton, List.take_take,
            min_eq_left (show base.length ≤ base.length + 1 by omega)] at hprefix
          rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hprefix
          exact hprefix⟩⟩
      have recover_letter (child : Σ letter : Letters, extensions (base ++ [letter.val]) depth) :
          child.2.val.getD base.length 0 = child.1.val := by
        have hread := congrArg (fun word : List ℕ => word.getD base.length 0) child.2.property.2
        have htaken : (child.2.val.take (base ++ [child.1.val]).length).getD base.length 0 =
            child.2.val.getD base.length 0 := by
          simp only [List.length_append, List.length_singleton,
            List.getD_eq_getElem?_getD, List.getElem?_take,
            if_pos (show base.length < base.length + 1 by omega)]
        rw [htaken, List.getD_append_right _ _ _ _ (Nat.le_refl _)] at hread
        simpa using hread
      let splitEquiv : extensions base (depth + 1) ≃
          (Σ letter : Letters, extensions (base ++ [letter.val]) depth) :=
        ⟨splitExtension, joinExtension, by
          intro word
          apply Subtype.ext
          rfl,
        by
          intro child
          have hletter : (splitExtension (joinExtension child)).1 = child.1 := by
            apply Subtype.ext
            exact recover_letter child
          apply Sigma.ext hletter
          have hpredicate := congrArg (fun letter : Letters => fun word : List ℕ =>
            word ∈ extensions (base ++ [letter.val]) depth) hletter
          exact (Subtype.heq_iff_coe_heq rfl (heq_of_eq hpredicate)).mpr HEq.rfl⟩
      have count_zero : count depth (base ++ [0]) = (continuationCounts depth
            (budget base + if base.getLast?.getD 0 = 0 then 1 else 0)).1 := by
        have hupdate := ascents_append base 0
        rw [if_neg hne] at hupdate
        dsimp [count, budget]
        simp only [List.getLast?_append_of_ne_nil _ (by simp : [0] ≠ []), List.getLast?_singleton,
          Option.getD_some, ↓reduceIte]
        rw [maximum_append]
        simp only [_root_.max_zero]
        congr 2
        by_cases hzero : base.getLast?.getD 0 = 0
        · simp only [hzero, Nat.le_refl, ↓reduceIte] at hupdate ⊢
          omega
        · simp only [if_neg hzero] at ⊢
          rw [if_neg (by omega)] at hupdate
          omega
      have count_record (record : Fin (budget base)) :
          count depth (base ++ [chosen (.inr (.inl record))]) =
            (continuationCounts depth (record.val + 1)).2 := by
        have hi := record.isLt
        have hrecord : maximum < maximum + budget base - record.val := by omega
        have hupdate := ascents_append base (maximum + budget base - record.val)
        rw [if_neg hne, if_pos (by omega)] at hupdate
        dsimp [count, budget, chosen]
        have hlast : (base ++ [maximum + budget base - record.val]).getLast?.getD 0 =
            maximum + budget base - record.val := by simp
        rw [hlast, if_neg (by omega : maximum + budget base - record.val ≠ 0)]
        rw [maximum_append, max_eq_right (Nat.le_of_lt hrecord), hupdate]
        congr 2
        dsimp [budget, maximum] at *
        omega
      have count_repeat (repeatChoice : Fin (if base.getLast?.getD 0 = 0 then 0 else 1)) :
          count depth (base ++ [chosen (.inr (.inr repeatChoice))]) =
            (continuationCounts depth (budget base + 1)).2 := by
        have hpositive : base.getLast?.getD 0 ≠ 0 := by
          intro hzero
          have hi := repeatChoice.isLt
          simp [hzero] at hi
        have hmaxpositive : maximum ≠ 0 := by omega
        have hupdate := ascents_append base maximum
        rw [if_neg hne, if_pos hlastbound] at hupdate
        dsimp [count, budget, chosen]
        simp only [List.getLast?_append_of_ne_nil _ (by simp : [maximum] ≠ []),
          List.getLast?_singleton,
          Option.getD_some, if_neg hmaxpositive]
        rw [maximum_append, max_self, hupdate]
        congr 2
        dsimp [budget, maximum] at *
        omega
      rw [← Nat.card_coe_set_eq, Nat.card_congr splitEquiv, Nat.card_sigma]
      simp only [Nat.card_coe_set_eq]
      calc
        (∑ letter : Letters, (extensions (base ++ [letter.val]) depth).ncard) =
            ∑ letter : Letters, count depth (base ++ [letter.val]) := by
          apply Finset.sum_congr rfl
          intro letter _
          exact ih (base ++ [letter.val]) (by simp)
            (by simpa only [List.length_append, List.length_singleton] using letter.property)
        _ = ∑ choice : Choices, count depth (base ++ [chosen choice]) := by
          symm
          apply Fintype.sum_equiv choiceEquiv
          intro choice
          rfl
        _ = count (depth + 1) base := by
          simp only [Choices, Fintype.sum_sum_type, Fintype.sum_unique]
          rw [count_zero]
          simp_rw [count_record, count_repeat]
          rw [Fin.sum_univ_eq_sum_range (fun index => (continuationCounts depth (index + 1)).2)]
          by_cases hzero : base.getLast?.getD 0 = 0
          · simp [count, hzero, continuationCounts]
          · simp [count, hzero, continuationCounts, Nat.add_assoc, Nat.add_comm]
  have zero_valid : [0] ∈ avoiders 1 patterns := by
    refine ⟨rfl, ?_, ?_⟩
    · intro index hindex
      have : index = 0 := by simpa using hindex
      subst index
      simp
    · intro pattern hpattern hoccurs
      rcases hoccurs with ⟨values, hstep, hletters, hsub, harrows⟩
      have hlength := hsub.length_le
      have hthree : pattern.length = 3 := by
        simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl | rfl | rfl <;> rfl
      simp only [List.length_map, List.length_singleton, hthree] at hlength
      omega
  have series_eq : WeakAscent215Kernel.targetSeries = 1 + PowerSeries.X * qSeries 1 := by
    open PowerSeries in
    let series := WeakAscent215Kernel.targetSeries
    have htarget := target_series_equation
    have hlabel := ((right_continuation_certificate series htarget.1 htarget.2.1).1 1 (by omega)).1
    have hlabel' : qSeries 1 = numerator series := by simpa using hlabel
    let denominator : PowerSeries ℚ := 1 - X ^ 2 * series ^ 2
    have hconstant : constantCoeff denominator = 1 := by simp [denominator]
    have hinverse : denominator * denominator⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel denominator (by rw [hconstant]; exact one_ne_zero)
    change series = 1 + X * qSeries 1
    rw [hlabel']
    calc
      series = 1 + (series - 1) := by ring
      _ = 1 + ((series - 1) * denominator) * denominator⁻¹ := by
        rw [mul_assoc, hinverse, mul_one]
      _ = 1 + X * numerator series := by
        rw [show (series - 1) * denominator = X * series ^ 2 from htarget.2.1]
        unfold numerator
        ring
  cases length with
  | zero =>
    have hset : avoiders 0 patterns = {[]} := by
      ext word
      constructor
      · intro hword
        exact List.length_eq_zero_iff.mp hword.1
      · intro hword
        have heq : word = [] := hword
        subst word
        refine ⟨rfl, by simp [IsWeakAscent], ?_⟩
        intro pattern hpattern hoccurs
        rcases hoccurs with ⟨values, hstep, hletters, hsub, harrows⟩
        have hlength := hsub.length_le
        have hthree : pattern.length = 3 := by
          simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hpattern
          rcases hpattern with rfl | rfl | rfl | rfl <;> rfl
        simp only [List.length_map, List.length_nil, hthree] at hlength
        omega
    change ((avoiders 0 patterns).ncard : ℚ) = _
    rw [hset, Set.ncard_singleton]
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff, Nat.cast_one] using
      target_series_equation.1.symm
  | succ depth =>
    have hset : avoiders (depth + 1) patterns = extensions [0] depth := by
      ext word
      constructor
      · intro hword
        refine ⟨by simpa [Nat.add_comm] using hword, ?_⟩
        have hlength : 0 < word.length := by rw [hword.1]; omega
        have hhead : word.getD 0 0 = 0 := by
          have hbound := hword.2.1 0 hlength
          change word.getD 0 0 ≤ 0 at hbound
          omega
        rw [List.length_singleton, List.take_succ_eq_append_getElem hlength]
        simp only [List.take_zero, List.nil_append]
        rw [← List.getD_eq_getElem word 0 hlength, hhead]
      · intro hword
        simpa [Nat.add_comm] using hword.1
    change ((avoiders (depth + 1) patterns).ncard : ℚ) = _
    rw [hset, continuation_count depth [0] (by simp) (by simpa using zero_valid)]
    rw [series_eq]
    simp [count, budget, wasc, qSeries, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one]
end D5.S3.Combinatorics.WeakAscent.WeakAscent215RightWords
