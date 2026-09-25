/- GID: D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleWeave
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleWeave
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected indexed traces can be refilled monotonically in fixed positions. -/

import D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleWeave


variable {A : Type*}

private def weave : List Bool → List A → List A → List A
  | [], _, _ => []
  | true :: mask, selected, other =>
      match selected with
      | [] => []
      | value :: selected => value :: weave mask selected other
  | false :: mask, selected, other =>
      match other with
      | [] => []
      | value :: other => value :: weave mask selected other

private theorem weave_le [LinearOrder A] (mask : List Bool)
    (oldSelected newSelected other : List A)
    (holdLength : oldSelected.length = mask.count true)
    (hnewLength : newSelected.length = mask.count true)
    (hotherLength : other.length = mask.count false)
    (hselected : oldSelected ≤ newSelected) :
    weave mask oldSelected other ≤ weave mask newSelected other := by
  induction mask generalizing oldSelected newSelected other with
  | nil => simp [weave]
  | cons selected mask ih =>
      cases selected with
      | false =>
          cases other with
          | nil => simp at hotherLength
          | cons value other =>
              simp at holdLength hnewLength hotherLength
              simp only [weave]
              exact List.cons_le_cons value
                (ih oldSelected newSelected other holdLength hnewLength
                  (by omega) hselected)
      | true =>
          cases oldSelected with
          | nil => simp at holdLength
          | cons oldValue oldSelected =>
              cases newSelected with
              | nil => simp at hnewLength
              | cons newValue newSelected =>
                  simp at holdLength hnewLength hotherLength
                  simp only [weave]
                  rcases hselected.eq_or_lt with heq | hlt
                  · cases heq
                    exact le_rfl
                  · cases hlt with
                    | rel hvalue => exact le_of_lt (List.Lex.rel hvalue)
                    | cons htail =>
                        exact List.cons_le_cons oldValue
                          (ih oldSelected newSelected other (by omega) (by omega)
                            hotherLength (le_of_lt htail))

private theorem mapM_eq_weave {B : Type*} (entries : List B)
    (selected : B → Bool) (read : B → Option A)
    (word selectedWord otherWord : List A)
    (hword : entries.mapM read = some word)
    (hselected : (entries.filter selected).mapM read = some selectedWord)
    (hother : (entries.filter fun entry => !selected entry).mapM read =
      some otherWord) :
    word = weave (entries.map selected) selectedWord otherWord := by
  induction entries generalizing word selectedWord otherWord with
  | nil =>
      simp at hword hselected hother
      subst word
      subst selectedWord
      subst otherWord
      rfl
  | cons entry entries ih =>
      cases hread : read entry with
      | none => simp [hread] at hword
      | some value =>
          cases htail : entries.mapM read with
          | none => simp [hread, htail] at hword
          | some tail =>
              simp [hread, htail] at hword
              subst word
              cases hchoice : selected entry with
              | false =>
                  have hselectedTail :
                      (entries.filter selected).mapM read = some selectedWord := by
                    simpa [hchoice] using hselected
                  cases hotherTail :
                      (entries.filter fun item => !selected item).mapM read with
                  | none => simp [hchoice, hread, hotherTail] at hother
                  | some otherTail =>
                      have hotherWord : otherWord = value :: otherTail := by
                        simpa [hchoice, hread, hotherTail] using hother.symm
                      subst otherWord
                      rw [ih tail selectedWord otherTail htail hselectedTail
                        hotherTail]
                      simp [weave, hchoice]
              | true =>
                  have hotherTail :
                      (entries.filter fun item => !selected item).mapM read =
                        some otherWord := by
                    simpa [hchoice] using hother
                  cases hselectedTail : (entries.filter selected).mapM read with
                  | none => simp [hchoice, hread, hselectedTail] at hselected
                  | some selectedTail =>
                      have hselectedWord :
                          selectedWord = value :: selectedTail := by
                        simpa [hchoice, hread, hselectedTail] using hselected.symm
                      subst selectedWord
                      rw [ih tail selectedTail otherWord htail hselectedTail
                        hotherTail]
                      simp [weave, hchoice]

private def refillWhere {B : Type*} (selected : B → Bool) :
    List B → List B → Option (List B)
  | replacements, [] => if replacements = [] then some [] else none
  | replacements, entry :: entries =>
      if selected entry then
        match replacements with
        | [] => none
        | replacement :: replacements =>
            (replacement :: ·) <$> refillWhere selected replacements entries
      else
        (entry :: ·) <$> refillWhere selected replacements entries

private theorem refillWhere_spec {B : Type*} (selected : B → Bool)
    (replacements entries : List B)
    (hlength : replacements.length = (entries.filter selected).length)
    (hreplacements : ∀ replacement ∈ replacements,
      selected replacement = true) :
    ∃ filled,
      refillWhere selected replacements entries = some filled ∧
      filled.map selected = entries.map selected ∧
      filled.filter selected = replacements ∧
      filled.filter (fun entry => !selected entry) =
        entries.filter (fun entry => !selected entry) := by
  induction entries generalizing replacements with
  | nil =>
      have hreplacementsNil : replacements = [] := by simpa using hlength
      subst replacements
      exact ⟨[], by simp [refillWhere]⟩
  | cons entry entries ih =>
      cases hchoice : selected entry with
      | false =>
          have htailLength :
              replacements.length = (entries.filter selected).length := by
            simpa [hchoice] using hlength
          rcases ih replacements htailLength hreplacements with
            ⟨filled, hfill, hmask, hselected, hother⟩
          refine ⟨entry :: filled, ?_, ?_, ?_, ?_⟩
          · simp [refillWhere, hchoice, hfill]
          · simp [hchoice, hmask]
          · simp [hchoice, hselected]
          · simp [hchoice, hother]
      | true =>
          cases replacements with
          | nil => simp [hchoice] at hlength
          | cons replacement replacements =>
              have hreplacement : selected replacement = true :=
                hreplacements replacement (by simp)
              have htailReplacements : ∀ item ∈ replacements,
                  selected item = true := by
                intro item hitem
                exact hreplacements item (by simp [hitem])
              have htailLength :
                  replacements.length = (entries.filter selected).length := by
                simpa [hchoice] using hlength
              rcases ih replacements htailLength htailReplacements with
                ⟨filled, hfill, hmask, hselected, hother⟩
              refine ⟨replacement :: filled, ?_, ?_, ?_, ?_⟩
              · simp [refillWhere, hchoice, hfill]
              · simp [hchoice, hreplacement, hmask]
              · simp [hreplacement, hselected]
              · simp [hchoice, hreplacement, hother]

theorem mapM_length {B : Type*} (read : B → Option A)
    (entries : List B) (word : List A)
    (hread : entries.mapM read = some word) : word.length = entries.length := by
  induction entries generalizing word with
  | nil =>
      simp at hread
      subst word
      rfl
  | cons entry entries ih =>
      cases hentry : read entry with
      | none => simp [hentry] at hread
      | some value =>
          cases htail : entries.mapM read with
          | none => simp [hentry, htail] at hread
          | some tail =>
              have hword : word = value :: tail := by
                simpa [hentry, htail] using hread.symm
              subst word
              simp [ih tail htail]

private theorem refillWhere_mapM_mono [LinearOrder A] {B : Type*}
    (selected : B → Bool) (read : B → Option A)
    (replacements entries filled : List B)
    (oldWord newWord oldSelected newSelected otherWord : List A)
    (hlength : replacements.length = (entries.filter selected).length)
    (hreplacements : ∀ replacement ∈ replacements,
      selected replacement = true)
    (hfill : refillWhere selected replacements entries = some filled)
    (hold : entries.mapM read = some oldWord)
    (hnew : filled.mapM read = some newWord)
    (holdSelected : (entries.filter selected).mapM read = some oldSelected)
    (hnewSelected : replacements.mapM read = some newSelected)
    (hother : (entries.filter fun entry => !selected entry).mapM read =
      some otherWord)
    (hselected : oldSelected ≤ newSelected) : oldWord ≤ newWord := by
  rcases refillWhere_spec selected replacements entries hlength hreplacements with
    ⟨expected, hexpected, hmask, hselectedFilter, hotherFilter⟩
  rw [hfill] at hexpected
  cases Option.some.inj hexpected
  have hnewSelected' :
      (filled.filter selected).mapM read = some newSelected := by
    rw [hselectedFilter]
    exact hnewSelected
  have hnewOther :
      (filled.filter fun entry => !selected entry).mapM read = some otherWord := by
    rw [hotherFilter]
    exact hother
  have holdWeave := mapM_eq_weave entries selected read oldWord oldSelected
    otherWord hold holdSelected hother
  have hnewWeave := mapM_eq_weave filled selected read newWord newSelected
    otherWord hnew hnewSelected' hnewOther
  rw [hmask] at hnewWeave
  rw [holdWeave, hnewWeave]
  have hselectedTrue :
      ((fun choice : Bool => choice == true) ∘ selected) = selected := by
    funext entry
    cases hchoice : selected entry <;> simp [Function.comp_def, hchoice]
  have hselectedFalse :
      ((fun choice : Bool => choice == false) ∘ selected) =
        (fun entry => !selected entry) := by
    funext entry
    cases hchoice : selected entry <;> simp [Function.comp_def, hchoice]
  apply weave_le (entries.map selected) oldSelected newSelected otherWord
  · rw [mapM_length read _ _ holdSelected,
      List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
      hselectedTrue]
  · rw [mapM_length read _ _ hnewSelected, hlength,
      List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
      hselectedTrue]
  · rw [mapM_length read _ _ hother,
      List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
      hselectedFalse]
  · exact hselected


end D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleWeave
