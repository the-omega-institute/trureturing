/- GID: D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary
   mirror-E: none(waiver:boundary-minimal-permutation-geometry)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Fin]
   utility: none
   digest: Boundary-minimal forbidden permutations have family shape and three placements. -/
import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookRegions
import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords
import Mathlib.Order.Interval.Finset.Fin
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookBoundary
open D5.S3.Combinatorics.CrosswordRookCounts (Cell SameAcross SameDown IsRookPlacement rookCount)
open D5.S3.Combinatorics.CrosswordPermutationGridRefutation (permGrid)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords (word_structure)
theorem boundary_minimal_classification {n : ℕ} (positive : 1 ≤ n)
    (w : Equiv.Perm (Fin n)) (first last : Fin n) (first_row : first.val = 0)
    (last_row : last.val + 1 = n)
    (not_skew : ¬ D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDefs.SkewMerged w)
    (minimal : ∀ left lower upper right : Fin n,
      left < lower → lower < upper → upper < right →
      ((w lower < w left ∧ w left < w right ∧ w right < w upper) ∨
       (w upper < w right ∧ w right < w left ∧ w left < w lower)) →
      (first = left ∨ first = lower ∨ first = upper ∨ first = right) ∧
      (last = left ∨ last = lower ∨ last = upper ∨ last = right) ∧
      (w.symm first = left ∨ w.symm first = lower ∨
        w.symm first = upper ∨ w.symm first = right) ∧
      (w.symm last = left ∨ w.symm last = lower ∨
        w.symm last = upper ∨ w.symm last = right)) :
    ∃ source : Equiv.Perm (Fin n), (source = w ∨ source = w.trans Fin.revPerm) ∧
      ∃ minimum maximum : Fin n,
        first < minimum ∧ minimum < maximum ∧ maximum < last ∧
        source minimum = first ∧ source maximum = last ∧ source first < source last ∧
        ∃ arm middle : ℕ, n = arm + middle + 4 ∧
          ((minimum.val = arm + 1 ∧ maximum.val + 2 = n ∧ (source first).val = 1 ∧
            (source last).val = middle + 2 ∧
            ∀ row : Fin n,
              (first < row ∧ row < minimum → (source row).val + row.val = n - 1) ∧
              (minimum < row ∧ row < maximum →
                (source row).val = row.val - minimum.val + 1)) ∨
           (minimum.val = 1 ∧ maximum.val = middle + 2 ∧
            (source first).val = arm + 1 ∧ (source last).val + 2 = n ∧
            ∀ row : Fin n,
              (minimum < row ∧ row < maximum →
                (source row).val = row.val - minimum.val + (source first).val) ∧
              (maximum < row ∧ row < last → (source row).val + row.val = n - 1))) := by
  classical
  have shape (w : Equiv.Perm (Fin n)) (minimum maximum : Fin n)
      (order : first < minimum ∧ minimum < maximum ∧ maximum < last)
      (minimum_value : (w minimum).val = 0) (maximum_value : (w maximum).val + 1 = n)
      (end_values : w first < w last)
      (unique : ∀ left lower upper right : Fin n,
        left < lower → lower < upper → upper < right →
        ((w lower < w left ∧ w left < w right ∧ w right < w upper) ∨
         (w upper < w right ∧ w right < w left ∧ w left < w lower)) →
        left = first ∧ lower = minimum ∧ upper = maximum ∧ right = last) :
      ∃ arm middle : ℕ, n = arm + middle + 4 ∧
        ((minimum.val = arm + 1 ∧ maximum.val + 2 = n ∧ (w first).val = 1 ∧
          (w last).val = middle + 2 ∧
          ∀ row : Fin n,
            (first < row ∧ row < minimum → (w row).val + row.val = n - 1) ∧
            (minimum < row ∧ row < maximum →
              (w row).val = row.val - minimum.val + 1)) ∨
         (minimum.val = 1 ∧ maximum.val = middle + 2 ∧ (w first).val = arm + 1 ∧
          (w last).val + 2 = n ∧
          ∀ row : Fin n,
            (minimum < row ∧ row < maximum →
              (w row).val = row.val - minimum.val + (w first).val) ∧
            (maximum < row ∧ row < last → (w row).val + row.val = n - 1))) := by
    have first_minimum := order.1; have minimum_maximum := order.2.1
    have maximum_last := order.2.2; have size_bound : 4 ≤ n := by omega
    have first_le (row : Fin n) : first ≤ row := by omega
    have last_le (row : Fin n) : row ≤ last := by omega
    have minimum_le (row : Fin n) : w minimum ≤ w row := by omega
    have maximum_le (row : Fin n) : w row ≤ w maximum := by omega
    have minimum_lt_first : w minimum < w first := by
      have different := w.injective.ne (ne_of_lt order.1).symm
      exact lt_of_le_of_ne (minimum_le first) different
    have last_lt_maximum : w last < w maximum := by
      have different := w.injective.ne (ne_of_lt order.2.2).symm
      exact lt_of_le_of_ne (maximum_le last) different
    have boxes (row : Fin n) (not_first : row ≠ first) (not_minimum : row ≠ minimum)
        (not_maximum : row ≠ maximum) (not_last : row ≠ last) :
        (first < row ∧ row < minimum ∧ w last < w row) ∨
        (minimum < row ∧ row < maximum ∧ w first < w row ∧ w row < w last) ∨
        (maximum < row ∧ row < last ∧ w row < w first) := by
      have row_gt : first < row := lt_of_le_of_ne (first_le row) not_first.symm
      have row_lt : row < last := lt_of_le_of_ne (last_le row) not_last
      have value_gt : w minimum < w row :=
        lt_of_le_of_ne (minimum_le row) (w.injective.ne not_minimum).symm
      have value_lt : w row < w maximum :=
        lt_of_le_of_ne (maximum_le row) (w.injective.ne not_maximum)
      by_cases before : row < minimum
      · refine Or.inl ⟨row_gt, before, ?_⟩
        by_contra bad
        have below : w row < w last :=
          lt_of_le_of_ne (le_of_not_gt bad) (w.injective.ne not_last)
        exact not_first (unique row minimum maximum last before order.2.1 order.2.2
          (Or.inl ⟨value_gt, below, last_lt_maximum⟩)).1
      · have after : minimum < row := lt_of_le_of_ne (le_of_not_gt before) not_minimum.symm
        by_cases central : row < maximum
        · refine Or.inr (Or.inl ⟨after, central, ?_, ?_⟩)
          · by_contra bad
            have below : w row < w first :=
              lt_of_le_of_ne (le_of_not_gt bad) (w.injective.ne not_first)
            exact not_minimum (unique first row maximum last row_gt central order.2.2
              (Or.inl ⟨below, end_values, last_lt_maximum⟩)).2.1
          · by_contra bad
            have above : w last < w row :=
              lt_of_le_of_ne (le_of_not_gt bad) (w.injective.ne not_last).symm
            exact not_maximum (unique first minimum row last order.1 after row_lt
              (Or.inl ⟨minimum_lt_first, end_values, above⟩)).2.2.1
        · have beyond : maximum < row :=
            lt_of_le_of_ne (le_of_not_gt central) not_maximum.symm
          refine Or.inr (Or.inr ⟨beyond, row_lt, ?_⟩)
          by_contra bad
          have above : w first < w row :=
            lt_of_le_of_ne (le_of_not_gt bad) (w.injective.ne not_first).symm
          exact not_last (unique first minimum maximum row order.1 order.2.1 beyond
            (Or.inl ⟨minimum_lt_first, above, value_lt⟩)).2.2.2
    have arm_ne (row : Fin n) (hr : first < row ∧ row < minimum) : w last < w row := by
      have description := boxes row (ne_of_gt hr.1) (ne_of_lt hr.2)
        (ne_of_lt (hr.2.trans order.2.1)) (ne_of_lt (hr.2.trans (order.2.1.trans order.2.2)))
      rcases description with description | description | description
      · exact description.2.2
      · exact False.elim (lt_asymm hr.2 description.1)
      · exact False.elim (lt_asymm (hr.2.trans order.2.1) description.1)
    have arm_sw (row : Fin n) (hr : maximum < row ∧ row < last) : w row < w first := by
      have description := boxes row (ne_of_gt (order.1.trans (order.2.1.trans hr.1)))
        (ne_of_gt (order.2.1.trans hr.1)) (ne_of_gt hr.1) (ne_of_lt hr.2)
      rcases description with description | description | description
      · exact False.elim (lt_asymm (order.2.1.trans hr.1) description.2.1)
      · exact False.elim (lt_asymm hr.1 description.2.1)
      · exact description.2.2
    have central_iff (row : Fin n) :
        (minimum < row ∧ row < maximum) ↔ (w first < w row ∧ w row < w last) := by
      constructor
      · intro hr
        have description := boxes row (ne_of_gt (order.1.trans hr.1)) (ne_of_gt hr.1)
          (ne_of_lt hr.2) (ne_of_lt (hr.2.trans order.2.2))
        rcases description with description | description | description
        · exact False.elim (lt_asymm hr.1 description.2.1)
        · exact description.2.2
        · exact False.elim (lt_asymm hr.2 description.1)
      · intro hv
        have not_first : row ≠ first := fun heq => lt_irrefl _ (heq ▸ hv.1)
        have not_last : row ≠ last := fun heq => lt_irrefl _ (heq ▸ hv.2)
        have not_minimum : row ≠ minimum := by
          intro heq
          have hh := minimum_le first
          rw [heq] at hv
          exact not_lt_of_ge hh hv.1
        have not_maximum : row ≠ maximum := by
          intro heq
          have hh := maximum_le last
          rw [heq] at hv
          exact not_lt_of_ge hh hv.2
        rcases boxes row not_first not_minimum not_maximum not_last with hr | hr | hr
        · exact False.elim (lt_asymm hv.2 hr.2.2)
        · exact ⟨hr.1, hr.2.1⟩
        · exact False.elim (lt_asymm hv.1 hr.2.2)
    have central_inc (left right : Fin n) (hl : minimum < left ∧ left < maximum)
        (hr : minimum < right ∧ right < maximum) (hlt : left < right) : w left < w right := by
      by_contra bad
      have decrease : w right < w left :=
        lt_of_le_of_ne (le_of_not_gt bad) (w.injective.ne (ne_of_lt hlt)).symm
      have hv := (central_iff right).mp hr
      have equal := (unique first minimum left right order.1 hl.1 hlt
        (Or.inl ⟨minimum_lt_first, hv.1, decrease⟩)).2.2.1
      exact ne_of_lt hl.2 equal
    have ne_dec (left right : Fin n) (hl : first < left ∧ left < minimum)
        (hr : first < right ∧ right < minimum) (hlt : left < right) : w right < w left := by
      by_contra bad
      have increase : w left < w right :=
        lt_of_le_of_ne (le_of_not_gt bad) (w.injective.ne (ne_of_lt hlt))
      have equal := (unique left right minimum last hlt hr.2
        (order.2.1.trans order.2.2)
        (Or.inr ⟨minimum_lt_first.trans end_values, arm_ne left hl, increase⟩)).1
      exact ne_of_gt hl.1 equal
    have sw_dec (left right : Fin n) (hl : maximum < left ∧ left < last)
        (hr : maximum < right ∧ right < last) (hlt : left < right) : w right < w left := by
      by_contra bad
      have increase : w left < w right :=
        lt_of_le_of_ne (le_of_not_gt bad) (w.injective.ne (ne_of_lt hlt))
      have equal := (unique first maximum left right (order.1.trans order.2.1) hl.1 hlt
        (Or.inr ⟨increase, arm_sw right hr, end_values.trans last_lt_maximum⟩)).2.1
      exact ne_of_gt order.2.1 equal
    have incompatible (left right : Fin n) (hl : first < left ∧ left < minimum)
        (hr : maximum < right ∧ right < last) : False := by
      have equal := (unique left maximum right last (hl.2.trans order.2.1) hr.1 hr.2
        (Or.inr ⟨(arm_sw right hr).trans end_values, arm_ne left hl,
          lt_of_le_of_ne (maximum_le left)
            (w.injective.ne (ne_of_lt (hl.2.trans order.2.1)))⟩)).2.1
      exact ne_of_gt order.2.1 equal
    have interval_rigid (source : Equiv.Perm (Fin n)) (lo hi low high : Fin n)
        (positions : lo < hi) (values : low < high)
        (span : ∀ row : Fin n, (lo < row ∧ row < hi) ↔
          (low < source row ∧ source row < high))
        (monotone : ∀ left right : Fin n,
          lo < left ∧ left < hi → lo < right ∧ right < hi →
          left < right → source left < source right) :
        hi.val - lo.val - 1 = high.val - low.val - 1 ∧
        ∀ row : Fin n, lo < row ∧ row < hi →
          (source row).val = row.val - lo.val + low.val := by
      have image : (Finset.Ioo lo hi).image source = Finset.Ioo low high := by
        ext value
        simp only [Finset.mem_image, Finset.mem_Ioo]
        constructor
        · rintro ⟨row, hr, rfl⟩
          exact (span row).mp hr
        · intro hv
          refine ⟨source.symm value, (span _).mpr ?_, source.apply_symm_apply _⟩
          simpa only [source.apply_symm_apply] using hv
      have lengths : hi.val - lo.val - 1 = high.val - low.val - 1 := by
        have cards := congrArg Finset.card image
        rw [Finset.card_image_of_injective _ source.injective, Fin.card_Ioo,
          Fin.card_Ioo] at cards
        exact cards
      let map : Fin (hi.val - lo.val - 1) → Fin (hi.val - lo.val - 1) := fun index =>
        let row : Fin n := ⟨lo.val + index.val + 1, by omega⟩
        ⟨(source row).val - low.val - 1, by
          have bound := (span row).mp (by
            change lo.val < lo.val + index.val + 1 ∧ lo.val + index.val + 1 < hi.val
            constructor <;> omega)
          omega⟩
      have strict : StrictMono map := by
        intro left right hlt
        have increase := monotone
          ⟨lo.val + left.val + 1, by omega⟩ ⟨lo.val + right.val + 1, by omega⟩
          (by
            change lo.val < lo.val + left.val + 1 ∧ lo.val + left.val + 1 < hi.val
            constructor <;> omega)
          (by
            change lo.val < lo.val + right.val + 1 ∧ lo.val + right.val + 1 < hi.val
            constructor <;> omega)
          (by change lo.val + left.val + 1 < lo.val + right.val + 1; omega)
        change (source ⟨lo.val + left.val + 1, _⟩).val - low.val - 1 <
          (source ⟨lo.val + right.val + 1, _⟩).val - low.val - 1
        have lower := (span ⟨lo.val + left.val + 1, by omega⟩).mp
          (by
            change lo.val < lo.val + left.val + 1 ∧ lo.val + left.val + 1 < hi.val
            constructor <;> omega)
        omega
      refine ⟨lengths, ?_⟩
      intro row hr
      let index : Fin (hi.val - lo.val - 1) := ⟨row.val - lo.val - 1, by omega⟩
      have fixed := congrArg Fin.val (strict.apply_eq (x := index))
      have rebuilt : (⟨lo.val + index.val + 1, by omega⟩ : Fin n) = row := by
        apply Fin.ext; dsimp [index]
        omega
      change (source ⟨lo.val + index.val + 1, _⟩).val - low.val - 1 = index.val at fixed
      rw [rebuilt] at fixed
      have lower := (span row).mp hr
      dsimp [index] at fixed
      omega
    obtain ⟨middle_size, middle_formula⟩ := interval_rigid w minimum maximum
      (w first) (w last) order.2.1 end_values central_iff central_inc
    by_cases ne_exists : ∃ row : Fin n, first < row ∧ row < minimum
    · obtain ⟨witness, hwitness⟩ := ne_exists
      have no_sw (row : Fin n) : ¬ (maximum < row ∧ row < last) :=
        fun hr => incompatible witness row hwitness hr
      have maximum_row : maximum.val + 2 = n := by
        by_contra bad
        let row : Fin n := ⟨maximum.val + 1, by omega⟩
        exact no_sw row (by
          change maximum.val < maximum.val + 1 ∧ maximum.val + 1 < last.val
          constructor <;> omega)
      have first_value : (w first).val = 1 := by
        by_contra bad
        let value : Fin n := ⟨1, by omega⟩
        let row := w.symm value
        have hr_value : w row = value := w.apply_symm_apply _
        have hr_val : (w row).val = 1 := congrArg Fin.val hr_value
        have not_first : row ≠ first := by intro heq; rw [heq] at hr_val; omega
        have not_minimum : row ≠ minimum := by intro heq; rw [heq] at hr_val; omega
        have not_maximum : row ≠ maximum := by intro heq; rw [heq] at hr_val; omega
        have not_last : row ≠ last := by intro heq; rw [heq] at hr_val; omega
        rcases boxes row not_first not_minimum not_maximum not_last with hr | hr | hr
        · have hh := hr.2.2; omega
        · have hh := hr.2.2.1; omega
        · exact no_sw row ⟨hr.1, hr.2.1⟩
      have ne_span (row : Fin n) : (first < row ∧ row < minimum) ↔
          ((w maximum).rev < (w row).rev ∧ (w row).rev < (w last).rev) := by
        constructor
        · intro hr
          have upper := arm_ne row hr
          have lower : w row < w maximum :=
            lt_of_le_of_ne (maximum_le row)
              (w.injective.ne (ne_of_lt (hr.2.trans order.2.1)))
          exact ⟨Fin.rev_lt_rev.mpr lower, Fin.rev_lt_rev.mpr upper⟩
        · intro hv
          have higher := Fin.rev_lt_rev.mp hv.2
          have lower := Fin.rev_lt_rev.mp hv.1
          have not_first : row ≠ first := by intro heq; rw [heq] at higher; omega
          have not_minimum : row ≠ minimum := by intro heq; rw [heq] at higher; omega
          have not_maximum : row ≠ maximum := fun heq => lt_irrefl _ (heq ▸ lower)
          have not_last : row ≠ last := fun heq => lt_irrefl _ (heq ▸ higher)
          rcases boxes row not_first not_minimum not_maximum not_last with hr | hr | hr
          · exact ⟨hr.1, hr.2.1⟩
          · exact False.elim (lt_asymm higher hr.2.2.2)
          · exact no_sw row ⟨hr.1, hr.2.1⟩ |>.elim
      obtain ⟨_, arm_formula⟩ := interval_rigid (w.trans Fin.revPerm) first minimum
        (w maximum).rev (w last).rev order.1 (Fin.rev_lt_rev.mpr last_lt_maximum)
        ne_span (fun left right hl hr hlt => Fin.rev_lt_rev.mpr (ne_dec left right hl hr hlt))
      refine ⟨minimum.val - 1, maximum.val - minimum.val - 1, by omega,
        Or.inl ⟨by omega, maximum_row, first_value, by omega, ?_⟩⟩
      intro row
      constructor
      · intro hr
        have equation := arm_formula row hr
        change (w row).rev.val = row.val - first.val + (w maximum).rev.val at equation
        simp only [Fin.val_rev] at equation
        omega
      · intro hr
        have equation := middle_formula row hr
        omega
    · have no_ne (row : Fin n) : ¬ (first < row ∧ row < minimum) :=
        fun hr => ne_exists ⟨row, hr⟩
      have minimum_row : minimum.val = 1 := by
        by_contra bad
        let row : Fin n := ⟨1, by omega⟩
        exact no_ne row (by change first.val < 1 ∧ 1 < minimum.val; constructor <;> omega)
      have last_value : (w last).val + 2 = n := by
        by_contra bad
        let value : Fin n := ⟨n - 2, by omega⟩
        let row := w.symm value
        have hr_value : w row = value := w.apply_symm_apply _
        have hr_val : (w row).val = n - 2 := congrArg Fin.val hr_value
        have not_first : row ≠ first := by intro heq; rw [heq] at hr_val; omega
        have not_minimum : row ≠ minimum := by intro heq; rw [heq] at hr_val; omega
        have not_maximum : row ≠ maximum := by intro heq; rw [heq] at hr_val; omega
        have not_last : row ≠ last := by intro heq; rw [heq] at hr_val; omega
        rcases boxes row not_first not_minimum not_maximum not_last with hr | hr | hr
        · exact no_ne row ⟨hr.1, hr.2.1⟩
        · have hh := hr.2.2.2; omega
        · have hh := hr.2.2; omega
      have sw_span (row : Fin n) : (maximum < row ∧ row < last) ↔
          ((w first).rev < (w row).rev ∧ (w row).rev < (w minimum).rev) := by
        constructor
        · intro hr
          have upper := arm_sw row hr
          have lower : w minimum < w row :=
            lt_of_le_of_ne (minimum_le row)
              (w.injective.ne (ne_of_gt (order.2.1.trans hr.1))).symm
          exact ⟨Fin.rev_lt_rev.mpr upper, Fin.rev_lt_rev.mpr lower⟩
        · intro hv
          have higher := Fin.rev_lt_rev.mp hv.2
          have lower := Fin.rev_lt_rev.mp hv.1
          have not_first : row ≠ first := fun heq => lt_irrefl _ (heq ▸ lower)
          have not_minimum : row ≠ minimum := fun heq => lt_irrefl _ (heq ▸ higher)
          have not_maximum : row ≠ maximum := by intro heq; rw [heq] at lower; omega
          have not_last : row ≠ last := by intro heq; rw [heq] at lower; omega
          rcases boxes row not_first not_minimum not_maximum not_last with hr | hr | hr
          · exact no_ne row ⟨hr.1, hr.2.1⟩ |>.elim
          · exact False.elim (lt_asymm lower hr.2.2.1)
          · exact ⟨hr.1, hr.2.1⟩
      obtain ⟨_, arm_formula⟩ := interval_rigid (w.trans Fin.revPerm) maximum last
        (w first).rev (w minimum).rev order.2.2 (Fin.rev_lt_rev.mpr minimum_lt_first)
        sw_span (fun left right hl hr hlt => Fin.rev_lt_rev.mpr (sw_dec left right hl hr hlt))
      refine ⟨n - maximum.val - 2, maximum.val - 2, by omega,
        Or.inr ⟨minimum_row, by omega, by omega, last_value, ?_⟩⟩
      intro row
      constructor
      · exact middle_formula row
      · intro hr
        have equation := arm_formula row hr
        change (w row).rev.val = row.val - maximum.val + (w first).rev.val at equation
        simp only [Fin.val_rev] at equation
        omega
  have forbidden : ∃ left lower upper right : Fin n,
      left < lower ∧ lower < upper ∧ upper < right ∧
      ((w lower < w left ∧ w left < w right ∧ w right < w upper) ∨
       (w upper < w right ∧ w right < w left ∧ w left < w lower)) := by
    by_contra absent
    apply not_skew
    apply (SkewMergedRookRegions.skew_iff_avoidance positive w).mpr
    intro left lower upper right hl hm hr bad
    exact absent ⟨left, lower, upper, right, hl, hm, hr, bad⟩
  obtain ⟨left, lower, upper, right, hl, hm, hr, pattern⟩ := forbidden
  obtain ⟨first_mem, last_mem, min_mem, max_mem⟩ := minimal left lower upper right hl hm hr
    pattern
  have left_first : left = first := by
    rcases first_mem with heq | heq | heq | heq
    · exact heq.symm
    · have bound : first ≤ left := by omega
      rw [heq] at bound
      exact False.elim (not_le_of_gt hl bound)
    · have bound : first ≤ left := by omega
      rw [heq] at bound
      exact False.elim (not_le_of_gt (hl.trans hm) bound)
    · have bound : first ≤ left := by omega
      rw [heq] at bound
      exact False.elim (not_le_of_gt (hl.trans (hm.trans hr)) bound)
  have right_last : right = last := by
    rcases last_mem with heq | heq | heq | heq
    · have bound : right ≤ last := by omega
      rw [heq] at bound
      exact False.elim (not_le_of_gt (hl.trans (hm.trans hr)) bound)
    · have bound : right ≤ last := by omega
      rw [heq] at bound
      exact False.elim (not_le_of_gt (hm.trans hr) bound)
    · have bound : right ≤ last := by omega
      rw [heq] at bound
      exact False.elim (not_le_of_gt hr bound)
    · exact heq.symm
  subst left; subst right
  have minimum_zero : (w (w.symm first)).val = 0 := by simp [first_row]
  have maximum_last : (w (w.symm last)).val + 1 = n := by simp [last_row]
  have extremal_positions :
      (w.symm first = lower ∧ w.symm last = upper) ∨
      (w.symm first = upper ∧ w.symm last = lower) := by
    rcases pattern with ⟨vlow, vmiddle, vhigh⟩ | ⟨vlow, vmiddle, vhigh⟩
    · left
      constructor
      · rcases min_mem with heq | heq | heq | heq
        · rw [heq] at minimum_zero; omega
        · exact heq
        · rw [heq] at minimum_zero; omega
        · rw [heq] at minimum_zero; omega
      · rcases max_mem with heq | heq | heq | heq
        · rw [heq] at maximum_last; omega
        · rw [heq] at maximum_last; omega
        · exact heq
        · rw [heq] at maximum_last; omega
    · right
      constructor
      · rcases min_mem with heq | heq | heq | heq
        · rw [heq] at minimum_zero; omega
        · rw [heq] at minimum_zero; omega
        · exact heq
        · rw [heq] at minimum_zero; omega
      · rcases max_mem with heq | heq | heq | heq
        · rw [heq] at maximum_last; omega
        · exact heq
        · rw [heq] at maximum_last; omega
        · rw [heq] at maximum_last; omega
  have unique_original (left second third right : Fin n)
      (hleft : left < second) (hmid : second < third) (hright : third < right)
      (bad : (w second < w left ∧ w left < w right ∧ w right < w third) ∨
        (w third < w right ∧ w right < w left ∧ w left < w second)) :
      left = first ∧ second = lower ∧ third = upper ∧ right = last := by
    obtain ⟨hfirst, hlast, hmin, hmax⟩ := minimal left second third right hleft hmid hright bad
    have first_equal : left = first := by
      rcases hfirst with heq | heq | heq | heq
      · exact heq.symm
      · have bound : first ≤ left := by omega
        rw [heq] at bound
        exact False.elim (not_le_of_gt hleft bound)
      · have bound : first ≤ left := by omega
        rw [heq] at bound
        exact False.elim (not_le_of_gt (hleft.trans hmid) bound)
      · have bound : first ≤ left := by omega
        rw [heq] at bound
        exact False.elim (not_le_of_gt (hleft.trans (hmid.trans hright)) bound)
    have last_equal : right = last := by
      rcases hlast with heq | heq | heq | heq
      · have bound : right ≤ last := by omega
        rw [heq] at bound
        exact False.elim (not_le_of_gt (hleft.trans (hmid.trans hright)) bound)
      · have bound : right ≤ last := by omega
        rw [heq] at bound
        exact False.elim (not_le_of_gt (hmid.trans hright) bound)
      · have bound : right ≤ last := by omega
        rw [heq] at bound
        exact False.elim (not_le_of_gt hright bound)
      · exact heq.symm
    subst left; subst right
    have both :
        (lower = first ∨ lower = second ∨ lower = third ∨ lower = last) ∧
        (upper = first ∨ upper = second ∨ upper = third ∨ upper = last) := by
      rcases extremal_positions with ⟨heqmin, heqmax⟩ | ⟨heqmin, heqmax⟩
      · simpa only [heqmin, heqmax] using And.intro hmin hmax
      · simpa only [heqmin, heqmax] using And.intro hmax hmin
    obtain ⟨hlower, hupper⟩ := both
    have lower_pair : lower = second ∨ lower = third := by
      rcases hlower with heq | heq | heq | heq
      · exact False.elim (ne_of_gt hl heq)
      · exact Or.inl heq
      · exact Or.inr heq
      · exact False.elim (ne_of_lt (hm.trans hr) heq)
    have upper_pair : upper = second ∨ upper = third := by
      rcases hupper with heq | heq | heq | heq
      · exact False.elim (ne_of_gt (hl.trans hm) heq)
      · exact Or.inl heq
      · exact Or.inr heq
      · exact False.elim (ne_of_lt hr heq)
    rcases lower_pair with hlow | hlow <;> rcases upper_pair with hupp | hupp
    · have contradiction := hm
      rw [hlow, hupp] at contradiction
      exact False.elim (lt_irrefl _ contradiction)
    · exact ⟨rfl, hlow.symm, hupp.symm, rfl⟩
    · have contradiction := hm
      rw [hlow, hupp] at contradiction
      exact False.elim (lt_asymm hmid contradiction)
    · have contradiction := hm
      rw [hlow, hupp] at contradiction
      exact False.elim (lt_irrefl _ contradiction)
  rcases pattern with pattern | pattern
  · have min_pos : w.symm first = lower := by
      rcases extremal_positions with extrema | extrema
      · exact extrema.1
      · have bound := minimum_zero
        rw [extrema.1] at bound
        obtain ⟨vlow, vmid, vhigh⟩ := pattern
        omega
    have max_pos : w.symm last = upper := by
      rcases extremal_positions with extrema | extrema
      · exact extrema.2
      · rw [extrema.1] at minimum_zero
        obtain ⟨vlow, vmid, vhigh⟩ := pattern
        omega
    have min_eq : w lower = first := by rw [← min_pos, w.apply_symm_apply]
    have max_eq : w upper = last := by rw [← max_pos, w.apply_symm_apply]
    refine ⟨w, Or.inl rfl, lower, upper, hl, hm, hr, min_eq, max_eq, pattern.2.1, ?_⟩
    exact shape w lower upper ⟨hl, hm, hr⟩ (by rw [min_eq]; exact first_row)
      (by rw [max_eq]; exact last_row) pattern.2.1 unique_original
  · have min_pos : w.symm first = upper := by
      rcases extremal_positions with extrema | extrema
      · rw [extrema.1] at minimum_zero
        obtain ⟨vlow, vmid, vhigh⟩ := pattern
        omega
      · exact extrema.1
    have max_pos : w.symm last = lower := by
      rcases extremal_positions with extrema | extrema
      · rw [extrema.1] at minimum_zero
        obtain ⟨vlow, vmid, vhigh⟩ := pattern
        omega
      · exact extrema.2
    let source := w.trans Fin.revPerm
    have min_eq : source lower = first := by
      apply Fin.ext
      change (w lower).rev.val = first.val
      rw [← max_pos, w.apply_symm_apply, Fin.val_rev]
      omega
    have max_eq : source upper = last := by
      apply Fin.ext
      change (w upper).rev.val = last.val
      rw [← min_pos, w.apply_symm_apply, Fin.val_rev]
      omega
    have ends : source first < source last := Fin.rev_lt_rev.mpr pattern.2.1
    have unique_source (left second third right : Fin n)
        (hleft : left < second) (hmid : second < third) (hright : third < right)
        (bad : (source second < source left ∧ source left < source right ∧
          source right < source third) ∨
          (source third < source right ∧ source right < source left ∧
            source left < source second)) :
        left = first ∧ second = lower ∧ third = upper ∧ right = last := by
      apply unique_original left second third right hleft hmid hright
      rcases bad with ⟨vlow, vmid, vhigh⟩ | ⟨vlow, vmid, vhigh⟩
      · exact Or.inr ⟨Fin.rev_lt_rev.mp vhigh, Fin.rev_lt_rev.mp vmid,
          Fin.rev_lt_rev.mp vlow⟩
      · exact Or.inl ⟨Fin.rev_lt_rev.mp vhigh, Fin.rev_lt_rev.mp vmid,
          Fin.rev_lt_rev.mp vlow⟩
    refine ⟨source, Or.inr rfl, lower, upper, hl, hm, hr, min_eq, max_eq, ends, ?_⟩
    exact shape source lower upper ⟨hl, hm, hr⟩ (by rw [min_eq]; exact first_row)
      (by rw [max_eq]; exact last_row) ends unique_source
set_option maxHeartbeats 0 in
theorem family_count {n : ℕ} (positive : 1 ≤ n) (arm middle : ℕ)
    (size : n = arm + middle + 4)
    (w : Equiv.Perm (Fin n))
    (code : ∀ row : Fin n, (w row).val =
      if row.val = 0 then 1 else if row.val ≤ arm then n - row.val - 1
      else if row.val = arm + 1 then 0 else if row.val < arm + middle + 2 then row.val - arm
      else if row.val = arm + middle + 2 then n - 1 else middle + 2) :
    3 ≤ rookCount (permGrid w) := by
  classical
  let west (seed : Fin 3) (row : ℕ) : ℕ :=
    if row = 0 then 0 else if row ≤ arm then
      if row < arm then n - row - 2
      else if seed.val = 2 then if middle = 0 then 1 else 2 else middle + 2
    else if row = arm + 1 then 0 else if row < arm + middle + 2 then
      if row = arm + 2 then if seed.val = 1 then 0 else 1 else row - arm - 1
    else if row = arm + middle + 2 then
      if middle = 0 then
        if seed.val = 0 then 1 else if seed.val = 1 then 0 else if arm = 0 then 2 else 3
      else middle + 1
    else if seed.val = 1 then 1 else 0
  let east (seed : Fin 3) (row : ℕ) : ℕ :=
    if row = 0 then
      if arm = 0 then if seed.val = 2 then middle + 3 else middle + 2 else n - 2
    else if row ≤ arm then n - row else if row = arm + 1 then
      if middle = 0 then if seed.val = 2 then if arm = 0 then 1 else 2 else 3
      else if seed.val = 2 ∧ 0 < arm then middle + 2 else 2
    else if row < arm + middle + 2 then
      if row < arm + middle + 1 then row - arm + 1
      else if seed.val = 2 ∧ arm = 0 then middle + 2 else middle + 3
    else n - 1
  let north (seed : Fin 3) (column : ℕ) : ℕ :=
    if column = 0 then 0 else if column = 1 then 0 else if column = middle + 2 then
      if seed.val = 2 then
        if arm = 0 then if middle = 0 then 2 else middle + 1 else arm + 1
      else arm
    else if column + 1 = n then
      if arm = 0 then if seed.val = 2 then 0 else arm + middle + 1 else 1
    else if column ≤ middle + 1 then
      if column = 2 ∧ seed.val = 2 ∧ 0 < arm then arm else arm + column - 1
    else n - column - 2
  let south (seed : Fin 3) (column : ℕ) : ℕ :=
    if column = 0 then if seed.val = 1 then arm + 2 else arm + middle + 3
    else if column = 1 then
      if seed.val = 0 then arm + 2 else if seed.val = 1 then arm + middle + 3
      else if middle = 0 then if arm = 0 then arm + 1 else arm else arm + 2
    else if column = middle + 2 then arm + middle + 3
    else if column + 1 = n then arm + middle + 3
    else if column ≤ middle + 1 then arm + column + 1
    else if column = middle + 3 then
      if middle = 0 ∧ seed.val = 2 then arm + 2 else arm + middle + 1
    else n - column
  let placement (seed : Fin 3) : Finset (Cell n) := Finset.univ.filter fun cell =>
    (cell.2.val < (w cell.1).val ∧ cell.2.val = west seed cell.1.val) ∨
    ((w cell.1).val < cell.2.val ∧ cell.2.val = east seed cell.1.val)
  have inverse (column : Fin n) : (w.symm column).val =
      if column.val = 0 then arm + 1 else if column.val = 1 then 0
      else if column.val = middle + 2 then arm + middle + 3
      else if column.val + 1 = n then arm + middle + 2
      else if column.val ≤ middle + 1 then arm + column.val
      else n - column.val - 1 := by
    have equation := code (w.symm column)
    rw [w.apply_symm_apply] at equation
    repeat' first | contradiction | omega | split at equation | split
  have horizontal_bounds (seed : Fin 3) (row : Fin n) :
      (0 < (w row).val → west seed row.val < (w row).val) ∧
      ((w row).val + 1 < n → (w row).val < east seed row.val ∧ east seed row.val < n) := by
    have equation := code row
    dsimp only [west, east]
    repeat' first | contradiction | omega | split at equation | split
  have vertical_bounds (seed : Fin 3) (column : Fin n) :
      (0 < (w.symm column).val → north seed column.val < (w.symm column).val) ∧
      ((w.symm column).val + 1 < n →
        (w.symm column).val < south seed column.val ∧ south seed column.val < n) := by
    have equation := inverse column
    dsimp only [north, south]
    repeat' first | contradiction | omega | split at equation | split
  have vertical_code (seed : Fin 3) (cell : Cell n) : cell ∈ placement seed ↔
      (cell.1.val < (w.symm cell.2).val ∧ cell.1.val = north seed cell.2.val) ∨
      ((w.symm cell.2).val < cell.1.val ∧ cell.1.val = south seed cell.2.val) := by
    have equation := code cell.1
    have inverse_equation := inverse cell.2
    simp only [placement, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [west, east, north, south]
    repeat' first | contradiction | omega | split at equation | split at inverse_equation | split
  obtain ⟨across, data, down_code⟩ := word_structure positive w
  have down (cell other : Cell n) (hc : cell ∈ permGrid w) (ho : other ∈ permGrid w) :
      SameDown (permGrid w) cell other ↔ cell.2 = other.2 ∧
        (cell.1 < w.symm cell.2 ↔ other.1 < w.symm other.2) := by
    rw [data.down_iff cell hc other ho, down_code, down_code]
    constructor
    · intro equal
      have columns : cell.2 = other.2 := by
        apply Fin.ext
        split_ifs at equal <;> omega
      refine ⟨columns, ?_⟩
      rw [columns] at equal ⊢
      split_ifs at equal <;> omega
    · rintro ⟨columns, sides⟩
      rw [columns] at sides ⊢
      split_ifs <;> omega
  have valid (seed : Fin 3) : IsRookPlacement (permGrid w) (placement seed) := by
    have white (cell : Cell n) (hc : cell ∈ placement seed) : cell ∈ permGrid w := by
      simp only [placement, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
      intro equal
      have values := congrArg Fin.val equal
      omega
    refine ⟨fun _ hc => white _ hc, ?_, ?_⟩
    · intro cell hc other ho different
      constructor
      · intro collision
        obtain ⟨rows, sides⟩ := (across cell (white cell hc) other (white other ho)).mp
          collision
        simp only [placement, Finset.mem_filter, Finset.mem_univ, true_and] at hc ho
        apply different; apply Prod.ext rows
        apply Fin.ext; rw [← rows] at ho sides
        rcases hc with hc | hc <;> rcases ho with ho | ho
        · omega
        · have hs := sides.mp hc.1; omega
        · have hs := sides.mpr ho.1; omega
        · omega
      · intro collision
        obtain ⟨columns, sides⟩ := (down cell other (white cell hc) (white other ho)).mp
          collision
        rw [vertical_code] at hc ho; apply different
        refine Prod.ext ?_ columns
        apply Fin.ext; rw [← columns] at ho sides
        rcases hc with hc | hc <;> rcases ho with ho | ho
        · omega
        · have hs := sides.mp hc.1; omega
        · have hs := sides.mpr ho.1; omega
        · omega
    · intro cell hc
      have nonblack : w cell.1 ≠ cell.2 := by simpa only [permGrid, Finset.mem_filter,
        Finset.mem_univ, true_and] using hc
      have nonblack_down : w.symm cell.2 ≠ cell.1 := by
        intro equal
        apply nonblack
        rw [← equal, w.apply_symm_apply]
      constructor
      · by_cases before : cell.2 < w cell.1
        · have bound := (horizontal_bounds seed cell.1).1 (by omega)
          let rook : Cell n := (cell.1, ⟨west seed cell.1.val, by omega⟩)
          have member : rook ∈ placement seed := by
            simp only [placement, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Or.inl ⟨bound, rfl⟩
          refine ⟨rook, member, (across cell hc rook (white rook member)).mpr ?_⟩
          exact ⟨rfl, iff_of_true before bound⟩
        · have after : w cell.1 < cell.2 := lt_of_le_of_ne (le_of_not_gt before) nonblack
          obtain ⟨bound, inside⟩ := (horizontal_bounds seed cell.1).2 (by omega)
          let rook : Cell n := (cell.1, ⟨east seed cell.1.val, inside⟩)
          have member : rook ∈ placement seed := by
            simp only [placement, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Or.inr ⟨bound, rfl⟩
          refine ⟨rook, member, (across cell hc rook (white rook member)).mpr ?_⟩
          exact ⟨rfl, iff_of_false before (not_lt_of_ge bound.le)⟩
      · by_cases before : cell.1 < w.symm cell.2
        · have bound := (vertical_bounds seed cell.2).1 (by omega)
          let rook : Cell n := (⟨north seed cell.2.val, by omega⟩, cell.2)
          have member : rook ∈ placement seed := (vertical_code seed rook).mpr
            (Or.inl ⟨bound, rfl⟩)
          refine ⟨rook, member, (down cell rook hc (white rook member)).mpr ?_⟩
          exact ⟨rfl, iff_of_true before bound⟩
        · have after : w.symm cell.2 < cell.1 :=
            lt_of_le_of_ne (le_of_not_gt before) nonblack_down
          obtain ⟨bound, inside⟩ := (vertical_bounds seed cell.2).2 (by omega)
          let rook : Cell n := (⟨south seed cell.2.val, inside⟩, cell.2)
          have member : rook ∈ placement seed := (vertical_code seed rook).mpr
            (Or.inr ⟨bound, rfl⟩)
          refine ⟨rook, member, (down cell rook hc (white rook member)).mpr ?_⟩
          exact ⟨rfl, iff_of_false before (not_lt_of_ge bound.le)⟩
  have distinguish_last (seed : Fin 3) :
      ((⟨arm + middle + 3, by omega⟩, ⟨1, by omega⟩) : Cell n) ∈ placement seed ↔
      seed.val = 1 := by
    let row : Fin n := ⟨arm + middle + 3, by omega⟩
    have equation : (w row).val = middle + 2 := by
      have equation := code row
      change (w row).val = if arm + middle + 3 = 0 then 1
        else if arm + middle + 3 ≤ arm then n - (arm + middle + 3) - 1
        else if arm + middle + 3 = arm + 1 then 0
        else if arm + middle + 3 < arm + middle + 2 then arm + middle + 3 - arm
        else if arm + middle + 3 = arm + middle + 2 then n - 1
        else middle + 2 at equation
      split_ifs at equation <;> first | contradiction | omega
    simp only [placement, Finset.mem_filter, Finset.mem_univ, true_and]
    change (1 < (w row).val ∧ 1 = west seed (arm + middle + 3) ∨
      (w row).val < 1 ∧ 1 = east seed (arm + middle + 3)) ↔ seed.val = 1
    rw [equation]; dsimp only [west, east]
    clear * - seed arm middle n size
    split_ifs <;> simp_all <;> omega
  have distinguish_third (seed : Fin 3) :
      ((⟨if arm = 0 then 0 else arm, by split_ifs <;> omega⟩,
        ⟨if arm = 0 then middle + 3 else if middle = 0 then 1 else 2,
          by split_ifs <;> omega⟩) : Cell n) ∈ placement seed ↔
      seed.val = 2 := by
    simp only [placement, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases empty : arm = 0
    · simp only [empty, if_true]
      let row : Fin n := ⟨0, by omega⟩
      have equation : (w row).val = 1 := by
        have equation := code row
        change (w row).val = 1 at equation
        exact equation
      change (middle + 3 < (w row).val ∧ middle + 3 = west seed 0 ∨
        (w row).val < middle + 3 ∧ middle + 3 = east seed 0) ↔ seed.val = 2
      rw [equation]; dsimp only [west, east]
      clear * - seed arm middle n size empty
      split_ifs <;> omega
    · simp only [empty, if_false]
      let row : Fin n := ⟨arm, by omega⟩
      have equation : (w row).val = middle + 3 := by
        have equation := code row
        change (w row).val = if arm = 0 then 1 else if arm ≤ arm then n - arm - 1
          else if arm = arm + 1 then 0 else if arm < arm + middle + 2 then arm - arm
          else if arm = arm + middle + 2 then n - 1 else middle + 2 at equation
        split_ifs at equation <;> omega
      change ((if middle = 0 then 1 else 2) < (w row).val ∧
        (if middle = 0 then 1 else 2) = west seed arm ∨
        (w row).val < (if middle = 0 then 1 else 2) ∧
        (if middle = 0 then 1 else 2) = east seed arm) ↔ seed.val = 2
      rw [equation]; dsimp only [west, east]
      clear * - seed arm middle n size empty
      split_ifs <;> omega
  have injective : Function.Injective placement := by
    intro seed other equal
    have last_equal : (seed.val = 1 ↔ other.val = 1) := by
      rw [← distinguish_last seed, ← distinguish_last other, equal]
    have third_equal : (seed.val = 2 ↔ other.val = 2) := by
      rw [← distinguish_third seed, ← distinguish_third other, equal]
    apply Fin.ext
    omega
  have subset : Finset.univ.image placement ⊆
      (permGrid w).powerset.filter (IsRookPlacement (permGrid w)) := by
    intro rooks hrooks
    obtain ⟨seed, _, rfl⟩ := Finset.mem_image.mp hrooks
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (valid seed).1, valid seed⟩
  have count := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ injective, Finset.card_univ, Fintype.card_fin] at count
  exact count
end D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookBoundary
