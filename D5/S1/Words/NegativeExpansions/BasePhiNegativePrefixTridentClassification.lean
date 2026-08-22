/- GID: D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentClassification
   generality: I
   mirror-B: none(waiver:negative-prefix-trident-classification)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Complete canonical negative tails classify every nonempty admissible prefix Core. -/

import D5.S1.Words.NegativeExpansions.BasePhiNegativePrefixTridentCore

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S0.Carrier
open D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiTailBounds
open D5.S1.Words.NegativeExpansions.NegaFibonacci
open D5.S1.Words.NegativeExpansions.BasePhiNegativeTailWords

noncomputable section

private noncomputable def prefixTrace (w : List Bool) : Int :=
  trace (basePhiValue (wordDigits (prefixWord w)))

private theorem prefixWord_last {w : List Bool} {bit : Bool}
    (hlast : w.getLast? = some bit) :
    (prefixWord w).getLast? = some (if bit then 1 else 0) := by
  rw [prefixWord, List.getLast?_map, hlast]
  rfl

private theorem mem_core_iff_suffix {w : List Bool} (hw : w ≠ []) (q : Nat) :
    q ∈ Core w ↔
      ∃ suffix : List Nat,
        Canonical (prefixWord w ++ suffix) ∧
          (prefixWord w ++ suffix).getLast? = some 1 ∧
          Even (prefixWord w ++ suffix).length ∧
          (q : Int) =
            trace (basePhiValue (wordDigits (prefixWord w ++ suffix))) - 1 := by
  constructor
  · intro hq
    let suffix := (completeWord q).drop w.length
    have hsplit := completeWord_split_prefix hq.2
    refine ⟨suffix, ?_, ?_, ?_, ?_⟩
    · rw [← hsplit]
      exact completeWord_canonical q
    · rw [← hsplit]
      exact completeWord_last_one hq.2.1
    · rw [← hsplit]
      exact completeWord_length_even hq.2
    · have htrace := fiberStart_trace ⟨w.length, hq.2.1⟩ hq.1
      have hfullTrace :
          trace (basePhiValue (wordDigits (completeWord q))) = (q : Int) + 1 := by
        rw [completeWord_value]
        exact htrace
      rw [hsplit] at hfullTrace
      change (q : Int) = trace (basePhiValue
        (wordDigits (prefixWord w ++ (completeWord q).drop w.length))) - 1
      omega
  · rintro ⟨suffix, hcanonical, hlast, heven, hq⟩
    have hcore := core_of_suffix_word hw hcanonical hlast heven
    have htrace := trace_word_gt_one hcanonical hlast heven
    have hnonnegative :
        0 ≤ trace (basePhiValue (wordDigits (prefixWord w ++ suffix))) - 1 := by
      omega
    have hcast :
        ((trace (basePhiValue (wordDigits (prefixWord w ++ suffix))) - 1).toNat : Int) =
          trace (basePhiValue (wordDigits (prefixWord w ++ suffix))) - 1 :=
      Int.toNat_of_nonneg hnonnegative
    have heq :
        (trace (basePhiValue (wordDigits (prefixWord w ++ suffix))) - 1).toNat = q := by
      exact_mod_cast hcast.trans hq.symm
    simpa [heq] using hcore

private theorem canonical_append_of_last_zero {left right : List Nat}
    (hleft : Canonical left) (hright : Canonical right)
    (hlast : left.getLast? = some 0) : Canonical (left ++ right) := by
  apply canonical_append hleft hright
  intro x hx y hy
  have hxzero : 0 = x := by simpa [hlast] using hx
  exact Or.inl hxzero.symm

private theorem suffix_nonempty_of_prefix_last_zero {w : List Bool} {suffix : List Nat}
    (hlastPrefix : (prefixWord w).getLast? = some 0)
    (hlast : (prefixWord w ++ suffix).getLast? = some 1) : suffix ≠ [] := by
  intro hnil
  subst suffix
  simp [hlastPrefix] at hlast

private theorem suffix_last_one {w : List Bool} {suffix : List Nat}
    (hsuffix : suffix ≠ [])
    (hlast : (prefixWord w ++ suffix).getLast? = some 1) :
    suffix.getLast? = some 1 := by
  simpa [hsuffix] using hlast

private theorem core_eq_false_even {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hlast : w.getLast? = some false) (heven : Even w.length) :
    Core w = sequenceRange
      (positiveSuffixSequence w.length (prefixTrace w)) := by
  obtain ⟨seed, _, hseed⟩ := hadmissible
  have hprefixCanonical := prefixWord_canonical_of_occurs hseed
  have hprefixLast : (prefixWord w).getLast? = some 0 := prefixWord_last hlast
  ext q
  constructor
  · intro hq
    obtain ⟨suffix, hcanonical, hfullLast, hfullEven, hqTrace⟩ :=
      (mem_core_iff_suffix hw q).mp hq
    have hsuffixNonempty := suffix_nonempty_of_prefix_last_zero hprefixLast hfullLast
    have hsuffixLast := suffix_last_one hsuffixNonempty hfullLast
    have hsuffixCanonical : Canonical suffix := by
      simpa using canonical_drop (prefixWord w).length hcanonical
    have hreverseCanonical := canonical_reverse hsuffixCanonical
    have hreverseHead : suffix.reverse.head? = some 1 := by simpa using hsuffixLast
    have hsuffixEven : Even suffix.length := by
      obtain ⟨a, ha⟩ := heven
      obtain ⟨b, hb⟩ := hfullEven
      simp only [List.length_append, prefixWord_length] at hb
      refine ⟨b - a, ?_⟩
      omega
    have hreverseEven : Even suffix.reverse.length := by simpa using hsuffixEven
    have hweightPos := weight_pos_of_head_one_even hreverseCanonical
      hreverseHead hreverseEven
    let k := (weight suffix.reverse).toNat
    have hkCast : (k : Int) = weight suffix.reverse :=
      Int.toNat_of_nonneg hweightPos.le
    have hkPos : 0 < k := by
      have : (0 : Int) < (k : Int) := by rw [hkCast]; exact hweightPos
      exact_mod_cast this
    let n := k - 1
    have hnk : n + 1 = k := Nat.sub_add_cancel hkPos
    have hweight : weight suffix.reverse = (n + 1 : Nat) := by
      rw [hnk, hkCast]
    have hformula := trace_append_positive (prefixWord w) suffix.reverse n
      hreverseCanonical hreverseHead hweight (by simpa using heven)
    simp only [List.reverse_reverse] at hformula
    have hformula' :
        trace (basePhiValue (wordDigits (prefixWord w ++ suffix))) - 1 =
          positiveSuffixSequence w.length (prefixTrace w) n := by
      simpa [prefixTrace] using hformula
    exact ⟨n, by omega⟩
  · rintro ⟨n, hn⟩
    obtain ⟨digits, hdigitsCanonical, hdigitsNonempty, hdigitsHead,
      hdigitsEven, hdigitsWeight⟩ := positive_representation (n + 1) (by omega)
    have hsuffixCanonical := canonical_reverse hdigitsCanonical
    have hfullCanonical := canonical_append_of_last_zero hprefixCanonical
      hsuffixCanonical hprefixLast
    have hsuffixLast : digits.reverse.getLast? = some 1 := by simpa using hdigitsHead
    have hfullLast : (prefixWord w ++ digits.reverse).getLast? = some 1 := by
      simpa [hdigitsNonempty] using hsuffixLast
    have hfullEven : Even (prefixWord w ++ digits.reverse).length := by
      simpa using heven.add (by simpa using hdigitsEven)
    apply (mem_core_iff_suffix hw q).mpr
    refine ⟨digits.reverse, hfullCanonical, hfullLast, hfullEven, ?_⟩
    have hformula := trace_append_positive (prefixWord w) digits n
      hdigitsCanonical hdigitsHead hdigitsWeight (by simpa using heven)
    have hformula' :
        trace (basePhiValue (wordDigits (prefixWord w ++ digits.reverse))) - 1 =
          positiveSuffixSequence w.length (prefixTrace w) n := by
      simpa [prefixTrace] using hformula
    change (q : Int) = positiveSuffixSequence w.length (prefixTrace w) n at hn
    exact hn.trans hformula'.symm

private theorem core_eq_false_odd {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hlast : w.getLast? = some false) (hodd : Odd w.length) :
    Core w = sequenceRange
      (negativeSuffixSequence w.length (prefixTrace w)) := by
  obtain ⟨seed, _, hseed⟩ := hadmissible
  have hprefixCanonical := prefixWord_canonical_of_occurs hseed
  have hprefixLast : (prefixWord w).getLast? = some 0 := prefixWord_last hlast
  ext q
  constructor
  · intro hq
    obtain ⟨suffix, hcanonical, hfullLast, hfullEven, hqTrace⟩ :=
      (mem_core_iff_suffix hw q).mp hq
    have hsuffixNonempty := suffix_nonempty_of_prefix_last_zero hprefixLast hfullLast
    have hsuffixLast := suffix_last_one hsuffixNonempty hfullLast
    have hsuffixCanonical : Canonical suffix := by
      simpa using canonical_drop (prefixWord w).length hcanonical
    have hreverseCanonical := canonical_reverse hsuffixCanonical
    have hreverseHead : suffix.reverse.head? = some 1 := by simpa using hsuffixLast
    have hsuffixOdd : Odd suffix.length := by
      obtain ⟨a, ha⟩ := hodd
      obtain ⟨b, hb⟩ := hfullEven
      simp only [List.length_append, prefixWord_length] at hb
      refine ⟨b - a - 1, ?_⟩
      omega
    have hreverseOdd : Odd suffix.reverse.length := by simpa using hsuffixOdd
    have hweightNeg := weight_neg_of_head_one_odd hreverseCanonical
      hreverseHead hreverseOdd
    let k := (-weight suffix.reverse).toNat
    have hkCast : (k : Int) = -weight suffix.reverse :=
      Int.toNat_of_nonneg (by omega)
    have hkPos : 0 < k := by
      have : (0 : Int) < (k : Int) := by rw [hkCast]; omega
      exact_mod_cast this
    let n := k - 1
    have hnk : n + 1 = k := Nat.sub_add_cancel hkPos
    have hweight : weight suffix.reverse = -((n + 1 : Nat) : Int) := by
      rw [hnk, hkCast]
      ring
    have hformula := trace_append_negative (prefixWord w) suffix.reverse n
      hreverseCanonical hreverseHead hweight (by simpa using hodd)
    simp only [List.reverse_reverse] at hformula
    have hformula' :
        trace (basePhiValue (wordDigits (prefixWord w ++ suffix))) - 1 =
          negativeSuffixSequence w.length (prefixTrace w) n := by
      simpa [prefixTrace] using hformula
    exact ⟨n, by omega⟩
  · rintro ⟨n, hn⟩
    obtain ⟨digits, hdigitsCanonical, hdigitsNonempty, hdigitsHead,
      hdigitsOdd, hdigitsWeight⟩ := negative_representation (n + 1) (by omega)
    have hsuffixCanonical := canonical_reverse hdigitsCanonical
    have hfullCanonical := canonical_append_of_last_zero hprefixCanonical
      hsuffixCanonical hprefixLast
    have hsuffixLast : digits.reverse.getLast? = some 1 := by simpa using hdigitsHead
    have hfullLast : (prefixWord w ++ digits.reverse).getLast? = some 1 := by
      simpa [hdigitsNonempty] using hsuffixLast
    have hfullEven : Even (prefixWord w ++ digits.reverse).length := by
      simpa using hodd.add_odd (by simpa using hdigitsOdd)
    apply (mem_core_iff_suffix hw q).mpr
    refine ⟨digits.reverse, hfullCanonical, hfullLast, hfullEven, ?_⟩
    have hformula := trace_append_negative (prefixWord w) digits n
      hdigitsCanonical hdigitsHead hdigitsWeight (by simpa using hodd)
    have hformula' :
        trace (basePhiValue (wordDigits (prefixWord w ++ digits.reverse))) - 1 =
          negativeSuffixSequence w.length (prefixTrace w) n := by
      simpa [prefixTrace] using hformula
    exact hn.trans hformula'.symm

private theorem canonical_append_head_zero : ∀ {left right : List Nat},
    Canonical (left ++ right) → left.getLast? = some 1 → right ≠ [] →
      right.head? = some 0
  | [], _, _, hlast, _ => by simp at hlast
  | [x], right, hcanonical, hlast, hright => by
      obtain ⟨y, tail, rfl⟩ := List.exists_cons_of_ne_nil hright
      have hx : x = 1 := by simpa using hlast
      have hy : y = 0 := hcanonical.2.1 hx
      simp [hy]
  | x :: y :: left, right, hcanonical, hlast, hright => by
      apply canonical_append_head_zero hcanonical.2.2 (by simpa using hlast) hright

private theorem canonical_append_of_head_zero {left right : List Nat}
    (hleft : Canonical left) (hright : Canonical right)
    (hhead : right.head? = some 0) : Canonical (left ++ right) := by
  apply canonical_append hleft hright
  intro x hx y hy
  have hyzero : 0 = y := by simpa [hhead] using hy
  exact Or.inr hyzero.symm

private theorem prefix_zero_trace (w : List Bool) :
    trace (basePhiValue (wordDigits (prefixWord w ++ [0]))) = prefixTrace w := by
  simp [prefixTrace, wordDigits_append, wordDigits, basePhiValue]

private theorem core_eq_true_odd {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hlast : w.getLast? = some true) (hodd : Odd w.length) :
    Core w = sequenceRange
      (positiveSuffixSequence (w.length + 1) (prefixTrace w)) := by
  obtain ⟨seed, _, hseed⟩ := hadmissible
  have hprefixCanonical := prefixWord_canonical_of_occurs hseed
  have hprefixLast : (prefixWord w).getLast? = some 1 := prefixWord_last hlast
  ext q
  constructor
  · intro hq
    obtain ⟨suffix, hcanonical, hfullLast, hfullEven, hqTrace⟩ :=
      (mem_core_iff_suffix hw q).mp hq
    have hsuffixNonempty : suffix ≠ [] := by
      intro hnil
      subst suffix
      have hevenPrefix : Even w.length := by simpa using hfullEven
      obtain ⟨a, ha⟩ := hodd
      obtain ⟨b, hb⟩ := hevenPrefix
      omega
    have hsuffixHead := canonical_append_head_zero hcanonical hprefixLast hsuffixNonempty
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hsuffixNonempty
    have hfirst : first = 0 := by simpa using hsuffixHead
    subst first
    have hrestNonempty : rest ≠ [] := by
      intro hnil
      subst rest
      simp [hprefixLast] at hfullLast
    have hrestLast : rest.getLast? = some 1 := by
      rw [List.getLast?_append_of_ne_nil _ (by simp)] at hfullLast
      rw [show 0 :: rest = [0] ++ rest by rfl,
        List.getLast?_append_of_ne_nil _ hrestNonempty] at hfullLast
      exact hfullLast
    have hzeroRestCanonical : Canonical (0 :: rest) := by
      simpa using canonical_drop (prefixWord w).length hcanonical
    have hrestCanonical := hzeroRestCanonical.2.2
    have hreverseCanonical := canonical_reverse hrestCanonical
    have hreverseHead : rest.reverse.head? = some 1 := by simpa using hrestLast
    have hrestEven : Even rest.length := by
      obtain ⟨a, ha⟩ := hodd
      obtain ⟨b, hb⟩ := hfullEven
      simp only [List.length_append, prefixWord_length, List.length_cons] at hb
      refine ⟨b - a - 1, ?_⟩
      omega
    have hreverseEven : Even rest.reverse.length := by simpa using hrestEven
    have hweightPos := weight_pos_of_head_one_even hreverseCanonical
      hreverseHead hreverseEven
    let k := (weight rest.reverse).toNat
    have hkCast : (k : Int) = weight rest.reverse :=
      Int.toNat_of_nonneg hweightPos.le
    have hkPos : 0 < k := by
      have : (0 : Int) < (k : Int) := by rw [hkCast]; exact hweightPos
      exact_mod_cast this
    let n := k - 1
    have hnk : n + 1 = k := Nat.sub_add_cancel hkPos
    have hweight : weight rest.reverse = (n + 1 : Nat) := by rw [hnk, hkCast]
    have hleftEven : Even (prefixWord w ++ [0]).length := by
      simpa using hodd.add_one
    have hformula := trace_append_positive (prefixWord w ++ [0]) rest.reverse n
      hreverseCanonical hreverseHead hweight hleftEven
    simp only [List.reverse_reverse] at hformula
    have hformula' :
        trace (basePhiValue (wordDigits (prefixWord w ++ 0 :: rest))) - 1 =
          positiveSuffixSequence (w.length + 1) (prefixTrace w) n := by
      simpa [List.append_assoc, prefix_zero_trace] using hformula
    exact ⟨n, by omega⟩
  · rintro ⟨n, hn⟩
    obtain ⟨digits, hdigitsCanonical, hdigitsNonempty, hdigitsHead,
      hdigitsEven, hdigitsWeight⟩ := positive_representation (n + 1) (by omega)
    have hrightCanonical := canonical_zero_cons (canonical_reverse hdigitsCanonical)
    have hrightHead : (0 :: digits.reverse).head? = some 0 := rfl
    have hfullCanonical := canonical_append_of_head_zero hprefixCanonical
      hrightCanonical hrightHead
    have hfullLast : (prefixWord w ++ 0 :: digits.reverse).getLast? = some 1 := by
      have hdigitsReverseNonempty : digits.reverse ≠ [] := by simpa using hdigitsNonempty
      rw [List.getLast?_append_of_ne_nil _ (by simp),
        show 0 :: digits.reverse = [0] ++ digits.reverse by rfl,
        List.getLast?_append_of_ne_nil _ hdigitsReverseNonempty]
      simpa using hdigitsHead
    have hfullEven : Even (prefixWord w ++ 0 :: digits.reverse).length := by
      have hsuffixOdd : Odd (0 :: digits.reverse).length := by
        simpa using (by simpa using hdigitsEven : Even digits.reverse.length).add_one
      simpa using hodd.add_odd hsuffixOdd
    apply (mem_core_iff_suffix hw q).mpr
    refine ⟨0 :: digits.reverse, hfullCanonical, hfullLast, hfullEven, ?_⟩
    have hleftEven : Even (prefixWord w ++ [0]).length := by simpa using hodd.add_one
    have hformula := trace_append_positive (prefixWord w ++ [0]) digits n
      hdigitsCanonical hdigitsHead hdigitsWeight hleftEven
    have hformula' :
        trace (basePhiValue (wordDigits (prefixWord w ++ 0 :: digits.reverse))) - 1 =
          positiveSuffixSequence (w.length + 1) (prefixTrace w) n := by
      simpa [List.append_assoc, prefix_zero_trace] using hformula
    exact hn.trans hformula'.symm

private theorem core_eq_true_even {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hlast : w.getLast? = some true) (heven : Even w.length) :
    Core w = sequenceRange
      (exactThenNegativeSequence (w.length + 1) (prefixTrace w)) := by
  obtain ⟨seed, _, hseed⟩ := hadmissible
  have hprefixCanonical := prefixWord_canonical_of_occurs hseed
  have hprefixLast : (prefixWord w).getLast? = some 1 := prefixWord_last hlast
  ext q
  constructor
  · intro hq
    obtain ⟨suffix, hcanonical, hfullLast, hfullEven, hqTrace⟩ :=
      (mem_core_iff_suffix hw q).mp hq
    by_cases hsuffix : suffix = []
    · subst suffix
      refine ⟨0, ?_⟩
      simp only [exactThenNegativeSequence]
      simpa [prefixTrace] using hqTrace
    · have hsuffixHead := canonical_append_head_zero hcanonical hprefixLast hsuffix
      obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hsuffix
      have hfirst : first = 0 := by simpa using hsuffixHead
      subst first
      have hrestNonempty : rest ≠ [] := by
        intro hnil
        subst rest
        simp [hprefixLast] at hfullLast
      have hrestLast : rest.getLast? = some 1 := by
        rw [List.getLast?_append_of_ne_nil _ (by simp)] at hfullLast
        rw [show 0 :: rest = [0] ++ rest by rfl,
          List.getLast?_append_of_ne_nil _ hrestNonempty] at hfullLast
        exact hfullLast
      have hzeroRestCanonical : Canonical (0 :: rest) := by
        simpa using canonical_drop (prefixWord w).length hcanonical
      have hrestCanonical := hzeroRestCanonical.2.2
      have hreverseCanonical := canonical_reverse hrestCanonical
      have hreverseHead : rest.reverse.head? = some 1 := by simpa using hrestLast
      have hrestOdd : Odd rest.length := by
        obtain ⟨a, ha⟩ := heven
        obtain ⟨b, hb⟩ := hfullEven
        simp only [List.length_append, prefixWord_length, List.length_cons] at hb
        refine ⟨b - a - 1, ?_⟩
        omega
      have hreverseOdd : Odd rest.reverse.length := by simpa using hrestOdd
      have hweightNeg := weight_neg_of_head_one_odd hreverseCanonical
        hreverseHead hreverseOdd
      let k := (-weight rest.reverse).toNat
      have hkCast : (k : Int) = -weight rest.reverse :=
        Int.toNat_of_nonneg (by omega)
      have hkPos : 0 < k := by
        have : (0 : Int) < (k : Int) := by rw [hkCast]; omega
        exact_mod_cast this
      let n := k - 1
      have hnk : n + 1 = k := Nat.sub_add_cancel hkPos
      have hweight : weight rest.reverse = -((n + 1 : Nat) : Int) := by
        rw [hnk, hkCast]
        ring
      have hleftOdd : Odd (prefixWord w ++ [0]).length := by
        simpa using heven.add_one
      have hformula := trace_append_negative (prefixWord w ++ [0]) rest.reverse n
        hreverseCanonical hreverseHead hweight hleftOdd
      simp only [List.reverse_reverse] at hformula
      have hformula' :
          trace (basePhiValue (wordDigits (prefixWord w ++ 0 :: rest))) - 1 =
            negativeSuffixSequence (w.length + 1) (prefixTrace w) n := by
        simpa [List.append_assoc, prefix_zero_trace] using hformula
      refine ⟨n + 1, ?_⟩
      change (q : Int) = negativeSuffixSequence (w.length + 1) (prefixTrace w) n
      omega
  · rintro ⟨index, hindex⟩
    cases index with
    | zero =>
        apply (mem_core_iff_suffix hw q).mpr
        refine ⟨[], by simpa using hprefixCanonical, by simpa using hprefixLast,
          by simpa using heven, ?_⟩
        change (q : Int) = prefixTrace w - 1 at hindex
        simpa [prefixTrace] using hindex
    | succ n =>
        obtain ⟨digits, hdigitsCanonical, hdigitsNonempty, hdigitsHead,
          hdigitsOdd, hdigitsWeight⟩ := negative_representation (n + 1) (by omega)
        have hrightCanonical := canonical_zero_cons (canonical_reverse hdigitsCanonical)
        have hfullCanonical := canonical_append_of_head_zero hprefixCanonical
          hrightCanonical (by rfl)
        have hfullLast : (prefixWord w ++ 0 :: digits.reverse).getLast? = some 1 := by
          have hdigitsReverseNonempty : digits.reverse ≠ [] := by
            simpa using hdigitsNonempty
          rw [List.getLast?_append_of_ne_nil _ (by simp),
            show 0 :: digits.reverse = [0] ++ digits.reverse by rfl,
            List.getLast?_append_of_ne_nil _ hdigitsReverseNonempty]
          simpa using hdigitsHead
        have hfullEven : Even (prefixWord w ++ 0 :: digits.reverse).length := by
          have hsuffixEven : Even (0 :: digits.reverse).length := by
            simpa using (by simpa using hdigitsOdd : Odd digits.reverse.length).add_one
          simpa using heven.add hsuffixEven
        apply (mem_core_iff_suffix hw q).mpr
        refine ⟨0 :: digits.reverse, hfullCanonical, hfullLast, hfullEven, ?_⟩
        have hleftOdd : Odd (prefixWord w ++ [0]).length := by
          simpa using heven.add_one
        have hformula := trace_append_negative (prefixWord w ++ [0]) digits n
          hdigitsCanonical hdigitsHead hdigitsWeight hleftOdd
        have hformula' :
            trace (basePhiValue (wordDigits (prefixWord w ++ 0 :: digits.reverse))) - 1 =
              negativeSuffixSequence (w.length + 1) (prefixTrace w) n := by
          simpa [List.append_assoc, prefix_zero_trace] using hformula
        change (q : Int) = negativeSuffixSequence (w.length + 1) (prefixTrace w) n at hindex
        exact hindex.trans hformula'.symm

private theorem positiveSuffixSequence_first_pos {left : List Nat}
    (hcanonical : Canonical left) (hlast : left.getLast? = some 0)
    (heven : Even left.length) :
    0 < positiveSuffixSequence left.length
      (trace (basePhiValue (wordDigits left))) 0 := by
  obtain ⟨digits, hdigitsCanonical, hdigitsNonempty, hdigitsHead,
    hdigitsEven, hdigitsWeight⟩ := positive_representation 1 (by omega)
  have hfullCanonical := canonical_append_of_last_zero hcanonical
    (canonical_reverse hdigitsCanonical) hlast
  have hfullLast : (left ++ digits.reverse).getLast? = some 1 := by
    have : digits.reverse.getLast? = some 1 := by simpa using hdigitsHead
    simpa [hdigitsNonempty] using this
  have hfullEven : Even (left ++ digits.reverse).length := by
    simpa using heven.add (by simpa using hdigitsEven)
  have htrace := trace_word_gt_one hfullCanonical hfullLast hfullEven
  have hformula := trace_append_positive left digits 0 hdigitsCanonical
    hdigitsHead (by simpa using hdigitsWeight) heven
  omega

private theorem negativeSuffixSequence_first_pos {left : List Nat}
    (hcanonical : Canonical left) (hlast : left.getLast? = some 0)
    (hodd : Odd left.length) :
    0 < negativeSuffixSequence left.length
      (trace (basePhiValue (wordDigits left))) 0 := by
  obtain ⟨digits, hdigitsCanonical, hdigitsNonempty, hdigitsHead,
    hdigitsOdd, hdigitsWeight⟩ := negative_representation 1 (by omega)
  have hfullCanonical := canonical_append_of_last_zero hcanonical
    (canonical_reverse hdigitsCanonical) hlast
  have hfullLast : (left ++ digits.reverse).getLast? = some 1 := by
    have : digits.reverse.getLast? = some 1 := by simpa using hdigitsHead
    simpa [hdigitsNonempty] using this
  have hfullEven : Even (left ++ digits.reverse).length := by
    simpa using hodd.add_odd (by simpa using hdigitsOdd)
  have htrace := trace_word_gt_one hfullCanonical hfullLast hfullEven
  have hformula := trace_append_negative left digits 0 hdigitsCanonical
    hdigitsHead (by simpa using hdigitsWeight) hodd
  omega

theorem core_lucas_witness_of_admissible {w : List Bool}
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) :
    CoreLucasWitness w := by
  have hadmissible' := hadmissible
  obtain ⟨seed, _, hseed⟩ := hadmissible'
  have hwLength : 0 < w.length := hseed.1.1
  have hw : w ≠ [] := by
    intro hnil
    subst w
    simp at hwLength
  have hprefixCanonical := prefixWord_canonical_of_occurs hseed
  let bit := w.getLast hw
  have hlast : w.getLast? = some bit := List.getLast?_eq_getLast_of_ne_nil hw
  cases hbit : bit with
  | false =>
      have hlastFalse : w.getLast? = some false := by simpa [bit, hbit] using hlast
      have hprefixLast : (prefixWord w).getLast? = some 0 := prefixWord_last hlastFalse
      by_cases heven : Even w.length
      · have hcore := core_eq_false_even hw hadmissible hlastFalse heven
        rw [positiveSuffixSequence_eq_vF] at hcore
        have hr := positiveSuffixSequence_first_pos hprefixCanonical hprefixLast
          (by simpa using heven)
        rw [positiveSuffixSequence_zero] at hr
        simp only [prefixWord_length] at hr
        refine ⟨.F, goldenLucas (w.length + 2), goldenLucas (w.length + 1),
          prefixTrace w + goldenLucas (w.length + 2) - 1,
          ⟨w.length + 1, by omega, rfl, rfl⟩, (by simpa [prefixTrace] using hr), ?_⟩
        change Core w = sequenceRange (vF (goldenLucas (w.length + 2))
          (goldenLucas (w.length + 1)) (prefixTrace w + goldenLucas (w.length + 2) - 1))
        exact hcore
      · have hodd := Nat.not_even_iff_odd.mp heven
        have hcore := core_eq_false_odd hw hadmissible hlastFalse hodd
        rw [negativeSuffixSequence_eq_vF] at hcore
        have hr := negativeSuffixSequence_first_pos hprefixCanonical hprefixLast
          (by simpa using hodd)
        rw [negativeSuffixSequence_zero] at hr
        simp only [prefixWord_length] at hr
        refine ⟨.F, goldenLucas (w.length + 2), goldenLucas (w.length + 1),
          prefixTrace w + goldenLucas (w.length + 1) - 1,
          ⟨w.length + 1, by omega, rfl, rfl⟩, (by simpa [prefixTrace] using hr), ?_⟩
        change Core w = sequenceRange (vF (goldenLucas (w.length + 2))
          (goldenLucas (w.length + 1)) (prefixTrace w + goldenLucas (w.length + 1) - 1))
        exact hcore
  | true =>
      have hlastTrue : w.getLast? = some true := by simpa [bit, hbit] using hlast
      have hprefixLast : (prefixWord w).getLast? = some 1 := prefixWord_last hlastTrue
      by_cases heven : Even w.length
      · have hcore := core_eq_true_even hw hadmissible hlastTrue heven
        rw [exactThenNegative_eq_vG] at hcore
        have hr : 0 < prefixTrace w - 1 := by
          have htrace := trace_word_gt_one hprefixCanonical hprefixLast
            (by simpa using heven)
          simpa [prefixTrace] using htrace
        refine ⟨.G, goldenLucas (w.length + 3), goldenLucas (w.length + 2),
          prefixTrace w - 1, ⟨w.length + 2, by omega, by congr 1,
            by congr 1⟩, hr, ?_⟩
        change Core w = sequenceRange (vG (goldenLucas (w.length + 3))
          (goldenLucas (w.length + 2)) (prefixTrace w - 1))
        simpa only [show w.length + 1 + 2 = w.length + 3 by omega,
          show w.length + 1 + 1 = w.length + 2 by omega] using hcore
      · have hodd := Nat.not_even_iff_odd.mp heven
        have hcore := core_eq_true_odd hw hadmissible hlastTrue hodd
        rw [positiveSuffixSequence_eq_vF] at hcore
        have hleftCanonical : Canonical (prefixWord w ++ [0]) :=
          canonical_append_of_head_zero hprefixCanonical (by simp [Canonical]) (by rfl)
        have hleftLast : (prefixWord w ++ [0]).getLast? = some 0 := by simp
        have hr := positiveSuffixSequence_first_pos hleftCanonical hleftLast
          (by simpa using hodd.add_one)
        rw [positiveSuffixSequence_zero] at hr
        refine ⟨.F, goldenLucas (w.length + 3), goldenLucas (w.length + 2),
          prefixTrace w + goldenLucas (w.length + 3) - 1,
          ⟨w.length + 2, by omega, by congr 1,
            by congr 1⟩, ?_, ?_⟩
        · simpa [prefix_zero_trace] using hr
        · change Core w = sequenceRange (vF (goldenLucas (w.length + 3))
            (goldenLucas (w.length + 2))
              (prefixTrace w + goldenLucas (w.length + 3) - 1))
          simpa only [
            show w.length + 1 + 2 = w.length + 3 by omega,
            show w.length + 1 + 1 = w.length + 2 by omega] using hcore

end

end D5.X_Frontier.BasePhiNegativePrefixTrident
