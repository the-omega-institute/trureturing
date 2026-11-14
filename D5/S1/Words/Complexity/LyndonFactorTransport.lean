/- GID: D5/S1/Words/Complexity/LyndonFactorTransport
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonFactorTransport
   mirror-E: none(waiver:research-return-assignment-A)
   anchors: []
   utility: none
   digest: Suffix-minimum scanning computes the actual distinct contiguous Lyndon factors. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
import Mathlib.Data.List.Infix
import D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization

/-! Exact scanning on arbitrary ordered alphabets and an actual elementary morphism.

Admission basis: escape-witness (research return #29680).
All declarations are universal mathematical identities or inductive proofs, not bounded
positive instances, numeric reductions, or certificate/reflection infrastructure; utility:none.
The scan produces factor strings, rather than checking a supplied certificate.

Consumed bind-only organization: lt_leastSuffix -> scan_accept_iff -> mem_suffixScan ->
mem_factorScan -> factorScan_eq_occurrence_image -> distinctLyndon_eq_scan.
The first two helpers and mem_suffixScan contain the suffix-minimum induction; the set/count
endpoints consume that induction and reconstruct actual occurrence indices, not a counting proxy.
elementaryLeft_order is content (first differing image/continuation comparison) and is used
in elementaryLeft_lyndon_iff and elementaryLeft_factor_growth. The latter consumes actual
Lyndon preservation, infix transport, injectivity and the additional letter outside the image.
These are genuine universal content paths, with no new independent finite instance.

Existing frozen proof owners: LyndonOrder.isLyndon_iff_lt_suffix, isLyndon_append,
its private list_lt_self_append, and LyndonStandardFactorization.isLyndon_standardLeft.
The original three finite-index definitions retain their namespace and exact bodies; their
original certificate consumer imports this general owner. No second refutation is introduced.
New public audit targets are disclosed individually under #29680 if registration is unfinished.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.LyndonFactorChristoffelMinimumRefutation
open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder (IsLyndon)

/-- Drop `i` letters and take at most `l` letters of `w`. -/
def factor {σ n : ℕ} (w : Fin n → Fin σ) (i l : ℕ) : List (Fin σ) :=
  ((List.finRange n).map w).drop i |>.take l

/-- Occurrences `(i, l)`, `l ≥ 1`, `i + l ≤ n`, of Lyndon factors of `w`. -/
noncomputable def lyndonOccurrences {σ n : ℕ} (w : Fin n → Fin σ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range n ×ˢ Finset.range (n + 1)).filter fun p =>
    1 ≤ p.2 ∧ p.1 + p.2 ≤ n ∧ IsLyndon (factor w p.1 p.2))

/-- `D(W)`: the number of distinct Lyndon factors of `W`. -/
noncomputable def distinctLyndon {σ n : ℕ} (w : Fin n → Fin σ) : ℕ := by
  classical
  exact ((lyndonOccurrences w).image fun p => factor w p.1 p.2).card
end D5.S1.Words.Complexity.LyndonFactorChristoffelMinimumRefutation

namespace D5.S1.Words.Complexity.LyndonFactorTransport
open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open D5.S1.Words.Complexity.LyndonFactorChristoffelMinimumRefutation
variable {A : Type*} [LinearOrder A]

/-- Minimum among nonempty suffixes; the empty input has a harmless empty sentinel. -/
def leastSuffix : List A → List A
  | [] => []
  | [a] => [a]
  | a :: b :: w => min (a :: b :: w) (leastSuffix (b :: w))

/-- Scan shorter suffixes first; accept a new suffix only when it beats their minimum. -/
def suffixScan : List A → List (List A)
  | [] => []
  | a :: w => if w = [] then [[a]] else
      if a :: w < leastSuffix w then (a :: w) :: suffixScan w else suffixScan w

private theorem lt_leastSuffix (z w : List A) (hw : w ≠ []) :
    z < leastSuffix w ↔ ∀ v : List A, v ≠ [] → v <:+ w → z < v := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons a w ih =>
    cases w with
    | nil =>
      simp only [leastSuffix]
      constructor
      · intro h v hv hs
        rcases List.suffix_cons_iff.mp hs with rfl | hs
        · exact h
        · have : v = [] := List.eq_nil_of_suffix_nil hs
          exact (hv this).elim
      · intro h
        exact h [a] (by simp) (List.suffix_refl _)
    | cons b w =>
      rw [leastSuffix, lt_min_iff, ih (by simp)]
      constructor
      · rintro ⟨h, ht⟩ v hv hs
        rcases List.suffix_cons_iff.mp hs with rfl | hs
        · exact h
        · exact ht v hv hs
      · intro h
        exact ⟨h _ (by simp) (List.suffix_refl _),
          fun v hv hs => h v hv (hs.trans (List.suffix_cons _ _))⟩

private theorem scan_accept_iff (a : A) (w : List A) (hw : w ≠ []) :
    a :: w < leastSuffix w ↔ IsLyndon (a :: w) := by
  rw [lt_leastSuffix _ _ hw, isLyndon_iff_lt_suffix]
  constructor
  · intro h
    refine ⟨by simp, ?_⟩
    intro v hv hs hn
    rcases List.suffix_cons_iff.mp hs with he | hs
    · exact (hn he).elim
    · exact h v hv hs
  · rintro ⟨_, h⟩ v hv hs
    apply h v hv (hs.trans (List.suffix_cons _ _))
    intro he
    have hh := hs.length_le
    simp only [he, List.length_cons] at hh
    omega

/-- The scan accepts exactly the actual Lyndon suffix strings, including letters. -/
theorem mem_suffixScan (u w : List A) :
    u ∈ suffixScan w ↔ IsLyndon u ∧ u <:+ w := by
  induction w with
  | nil =>
    simp only [suffixScan, List.not_mem_nil, false_iff]
    rintro ⟨hu, hs⟩
    exact hu.1 (List.eq_nil_of_suffix_nil hs)
  | cons a w ih =>
    by_cases hw : w = []
    · subst w
      have ha : IsLyndon [a] := by
        apply (isLyndon_iff_lt_suffix _).mpr
        refine ⟨by simp, ?_⟩
        intro v hv hs hn
        rcases List.suffix_cons_iff.mp hs with he | hs
        · exact (hn he).elim
        · exact (hv (List.eq_nil_of_suffix_nil hs)).elim
      simp only [suffixScan, ↓reduceIte, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨ha, List.suffix_refl _⟩
      · rintro ⟨hu, hs⟩
        rcases List.suffix_cons_iff.mp hs with he | hs
        · exact he
        · exact (hu.1 (List.eq_nil_of_suffix_nil hs)).elim
    · have hc := scan_accept_iff a w hw
      simp only [suffixScan, if_neg hw]
      by_cases hL : IsLyndon (a :: w)
      · rw [if_pos (hc.mpr hL), List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨hu, hs⟩)
          · exact ⟨hL, List.suffix_refl _⟩
          · exact ⟨hu, hs.trans (List.suffix_cons _ _)⟩
        · rintro ⟨hu, hs⟩
          exact (List.suffix_cons_iff.mp hs).imp id (fun hs => ⟨hu, hs⟩)
      · rw [if_neg (fun h => hL (hc.mp h)), ih]
        constructor
        · rintro ⟨hu, hs⟩
          exact ⟨hu, hs.trans (List.suffix_cons _ _)⟩
        · rintro ⟨hu, hs⟩
          rcases List.suffix_cons_iff.mp hs with rfl | hs
          · exact (hL hu).elim
          · exact ⟨hu, hs⟩

/-- Scan all right endpoints, then identify equal strings rather than occurrences. -/
def factorScan (w : List A) : Finset (List A) :=
  (w.inits.flatMap suffixScan).toFinset

/-- Exact set correctness of the right-endpoint scan, over any ordered alphabet. -/
theorem mem_factorScan (u w : List A) :
    u ∈ factorScan w ↔ IsLyndon u ∧ u <:+: w := by
  simp only [factorScan, List.mem_toFinset, List.mem_flatMap, mem_suffixScan,
    List.mem_inits]
  constructor
  · rintro ⟨t, ht, hu, hs⟩
    exact ⟨hu, List.infix_iff_suffix_prefix.mpr ⟨t, hs, ht⟩⟩
  · rintro ⟨hu, hi⟩
    rcases List.infix_iff_suffix_prefix.mp hi with ⟨t, hs, ht⟩
    exact ⟨t, ht, hu, hs⟩

/-- The scan computes precisely the occurrence image used by the original certificate. -/
theorem factorScan_eq_occurrence_image {σ n : ℕ} (w : Fin n → Fin σ) :
    factorScan ((List.finRange n).map w) =
      (lyndonOccurrences w).image (fun p => factor w p.1 p.2) := by
  classical
  ext u
  rw [mem_factorScan, Finset.mem_image]
  constructor
  · rintro ⟨hu, ⟨l, r, he⟩⟩
    have hlen := congrArg List.length he
    simp only [List.length_append, List.length_map, List.length_finRange] at hlen
    have hup := List.length_pos_of_ne_nil hu.1
    have hf : factor w l.length u.length = u := by
      unfold factor
      rw [← he]
      simp
    refine ⟨(l.length, u.length), ?_, hf⟩
    simp only [lyndonOccurrences, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega, by omega, by simpa [hf] using hu⟩
  · rintro ⟨⟨i, k⟩, hp, rfl⟩
    simp only [lyndonOccurrences, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hp
    refine ⟨hp.2.2.2, ?_⟩
    exact (List.take_prefix k _).isInfix.trans (List.drop_suffix i _).isInfix

/-- Counts identify equal strings; this is the original count, not an occurrence proxy. -/
theorem distinctLyndon_eq_scan {σ n : ℕ} (w : Fin n → Fin σ) :
    distinctLyndon w = (factorScan ((List.finRange n).map w)).card := by
  rw [factorScan_eq_occurrence_image]
  rfl

def mapWord (f : Fin 2 → List (Fin 2)) (w : List (Fin 2)) : List (Fin 2) :=
  w.flatMap f

def elementaryLeft (x : Fin 2) : List (Fin 2) := if x = 0 then [0] else [0, 1]

private theorem elementaryLeft_order {x y : List (Fin 2)} (h : x < y) :
    mapWord elementaryLeft x < mapWord elementaryLeft y := by
  change List.Lex (· < ·) x y at h
  change List.Lex (· < ·) _ _
  induction h with
  | nil =>
    rename_i a w
    fin_cases a <;> exact List.Lex.nil
  | @rel a x b y hab =>
    have ha : a = 0 := by omega
    have hb : b = 1 := by omega
    subst a; subst b
    apply List.Lex.cons
    cases x with
    | nil => exact List.Lex.nil
    | cons c x =>
      fin_cases c <;> exact List.Lex.rel (by decide)
  | @cons a x y h ih =>
    fin_cases a
    · exact List.Lex.cons ih
    · exact List.Lex.cons (List.Lex.cons ih)

open private list_lt_self_append from
  D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder

/-- The actual elementary left map preserves and reflects Lyndon words, including letters. -/
theorem elementaryLeft_lyndon_iff (w : List (Fin 2)) :
    IsLyndon (mapWord elementaryLeft w) ↔ IsLyndon w := by
  have hmono : StrictMono (mapWord elementaryLeft) := fun _ _ h => elementaryLeft_order h
  have hne (v : List (Fin 2)) (hv : v ≠ []) : mapWord elementaryLeft v ≠ [] := by
    have ht : ([] : List (Fin 2)) < v := by
      cases v with
      | nil => exact (hv rfl).elim
      | cons a v => exact List.Lex.nil
    have hh := hmono ht
    intro he
    change ([] : List (Fin 2)) < mapWord elementaryLeft v at hh
    rw [he] at hh
    exact lt_irrefl _ hh
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · intro he; subst w; exact hw.1 rfl
    · intro u v hu hv he
      apply hmono.lt_iff_lt.mp
      have hh := hw.2 (mapWord elementaryLeft u) (mapWord elementaryLeft v)
        (hne u hu) (hne v hv) (by simp only [mapWord, he, List.flatMap_append])
      simpa only [mapWord, List.flatMap_append] using hh
  · intro hw
    classical
    induction hn : w.length using Nat.strong_induction_on generalizing w with
    | h n ih =>
      by_cases hl : 2 ≤ w.length
      · open D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization in
        have hcut := @Nat.find_spec _ (Classical.decPred _)
          (exists_lyndon_suffix_cut w hl)
        let i := D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization.standardCut w hl
        have hi : 0 < i ∧ i < w.length ∧ IsLyndon (w.drop i) := hcut
        have hu : IsLyndon (w.take i) := by
          exact D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization.isLyndon_standardLeft w hl hw
        have hv := hi.2.2
        have huv : w.take i < w.drop i := by
          have hs := ((isLyndon_iff_lt_suffix w).mp hw).2 (w.drop i) hv.1
            (List.drop_suffix i w) (by
              intro he
              have hh := congrArg List.length he
              simp only [List.length_drop] at hh
              omega)
          have hp : w.take i < w := by
            simpa only [List.take_append_drop] using list_lt_self_append (w.take i) hv.1
          exact hp.trans hs
        have hut : (w.take i).length < n := by simp only [List.length_take]; omega
        have hvt : (w.drop i).length < n := by simp only [List.length_drop]; omega
        have hu' := ih _ hut _ hu rfl
        have hv' := ih _ hvt _ hv rfl
        have hh := isLyndon_append hu' hv' (hmono huv)
        simpa only [mapWord, ← List.flatMap_append, List.take_append_drop] using hh
      · have hlen : w.length = 1 := by
          have hp := List.length_pos_of_ne_nil hw.1
          omega
        cases w with
        | nil => simp at hlen
        | cons a w =>
          have : w = [] := by simpa using hlen
          subst w
          fin_cases a
          · simpa [mapWord, elementaryLeft] using hw
          · apply (isLyndon_iff_lt_suffix _).mpr
            refine ⟨by simp [mapWord, elementaryLeft], ?_⟩
            intro v hv hs hn
            simp only [mapWord, elementaryLeft, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), List.flatMap_cons,
              List.flatMap_nil, List.append_nil] at hs hn ⊢
            rcases List.suffix_cons_iff.mp hs with he | hs
            · exact (hn he).elim
            · rcases List.suffix_cons_iff.mp hs with rfl | hs
              · exact List.Lex.rel (by decide)
              · exact (hv (List.eq_nil_of_suffix_nil hs)).elim

/-- A letter b forces an additional distinct factor beyond all lambda-images. -/
theorem elementaryLeft_factor_growth (w : List (Fin 2)) (hb : (1 : Fin 2) ∈ w) :
    (factorScan w).card + 1 ≤ (factorScan (mapWord elementaryLeft w)).card := by
  classical
  let f := mapWord elementaryLeft
  have hf : Function.Injective f :=
    (show StrictMono f from fun _ _ h => elementaryLeft_order h).injective
  have hsub : (factorScan w).image f ⊆ factorScan (f w) := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
    rcases (mem_factorScan v w).mp hv with ⟨hvL, hvi⟩
    apply (mem_factorScan _ _).mpr
    exact ⟨(elementaryLeft_lyndon_iff v).mpr hvL, hvi.flatMap elementaryLeft⟩
  have hnot : [1] ∉ (factorScan w).image f := by
    intro h
    rcases Finset.mem_image.mp h with ⟨v, _, he⟩
    cases v with
    | nil => simp [f, mapWord] at he
    | cons a v => fin_cases a <;> simp [f, mapWord, elementaryLeft] at he
  have hletter : [1] ∈ factorScan (f w) := by
    apply (mem_factorScan _ _).mpr
    refine ⟨?_, ?_⟩
    · exact ⟨by simp, fun u v hu hv he => by
        have hlen := congrArg List.length he
        have hu' := List.length_pos_of_ne_nil hu
        have hv' := List.length_pos_of_ne_nil hv
        simp only [List.length_singleton, List.length_append] at hlen
        omega⟩
    · rcases List.mem_iff_append.mp hb with ⟨s, t, he⟩
      refine ⟨f s ++ [0], f t, ?_⟩
      simp [f, mapWord, he, elementaryLeft, List.append_assoc]
  calc
    (factorScan w).card + 1 = ((factorScan w).image f).card + 1 := by
      rw [Finset.card_image_of_injective _ hf]
    _ = (insert [1] ((factorScan w).image f)).card :=
      (Finset.card_insert_of_notMem hnot).symm
    _ ≤ (factorScan (f w)).card := Finset.card_le_card (by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hletter
      · exact hsub hu)

end D5.S1.Words.Complexity.LyndonFactorTransport
