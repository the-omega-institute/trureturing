/- GID: D5/S1/Words/RichWordOutputDecoder
   generality: I
   mirror-B: D5/B/S1/Words/RichWordOutputDecoder
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Literal four-letter marker reconstruction and actual occurrence transport. -/
import D5.S1.Words.RichWordTypeIIOccurrence
import D5.S1.Words.Complexity.SahasrabudheEvenAdditiveComplexityMorphism

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RichWordOutputDecoder

open RankOneMorphismIterationBound (subst subst_append)
open AbelianBorders.AbelianBorderQuestionDefs (factor)
open MBonacciSentinelDesubstitution (factor_len factor_add factor_get)

abbrev Input := Fin 7
abbrev Output := Fin 4
abbrev u := RichWordTypeIOccurrence.word

/-- The marker is 0; the other three letters are 1, 2 and 3. -/
def eta (c : Input) : List Output :=
  ![[0], [0,1], [0,1,1], [0,2], [0,2,2], [0,2,2,3,2,2],
    [0,2,2,3,2,2,3,3,2,2,3,2,2]] c

/-- Marker-free image tails, including the empty tail of source letter zero. -/
def q (c : Input) : List Output := (eta c).drop 1

private theorem eta_cons (c : Input) : eta c = 0 :: q c := by
  fin_cases c <;> rfl

private theorem eta_pos (c : Input) : 0 < (eta c).length := by
  rw [eta_cons]; simp

private theorem eta_injective : Function.Injective eta := by decide

private theorem eta_marker (c : Input) (i : ℕ) (hi : i < (eta c).length) :
    (eta c)[i] = 0 ↔ i = 0 := by
  fin_cases c <;> simp [eta] at hi ⊢ <;> interval_cases i <;> decide

/-- Cumulative image lengths of the actual source prefix. -/
def E : ℕ → ℕ
  | 0 => 0
  | j+1 => E j + (eta (u j)).length

private theorem E_strict : StrictMono E := by
  apply strictMono_nat_of_lt_succ
  intro j
  have := eta_pos (u j)
  simp only [E]
  omega

private theorem E_ge (j : ℕ) : j ≤ E j := by
  induction j with
  | zero => rfl
  | succ j ih => have := eta_pos (u j); simp only [E]; omega

private theorem window (p : ℕ) : ∃ j, E j ≤ p ∧ p < E (j+1) := by
  induction p with
  | zero => exact ⟨0, by simp [E], eta_pos (u 0)⟩
  | succ p ih =>
    obtain ⟨j,hj,hk⟩ := ih
    by_cases h : p+1 < E (j+1)
    · exact ⟨j, by omega, h⟩
    · exact ⟨j+1, by omega, by have := E_strict (Nat.lt_succ_self (j+1)); omega⟩

private def blockIndex (p : ℕ) : ℕ := Nat.find (window p)

private theorem blockIndex_spec (p : ℕ) :
    E (blockIndex p) ≤ p ∧ p < E (blockIndex p+1) := Nat.find_spec (window p)

private theorem window_unique {p j k : ℕ}
    (hj : E j ≤ p ∧ p < E (j+1)) (hk : E k ≤ p ∧ p < E (k+1)) : j = k := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have := E_strict.monotone (show j+1 ≤ k by omega); omega
  · have := E_strict.monotone (show k+1 ≤ j by omega); omega

/-- The actual one-sided infinite concatenation eta(u), at its unique image interval. -/
def x (p : ℕ) : Output :=
  (eta (u (blockIndex p)))[p-E (blockIndex p)]'(by
    have := blockIndex_spec p
    simp only [E] at this
    omega)

private theorem block_letter (j i : ℕ) (hi : i < (eta (u j)).length) :
    x (E j+i) = (eta (u j))[i] := by
  have he : blockIndex (E j+i) = j := window_unique (blockIndex_spec _)
    ⟨by omega, by simpa only [E] using Nat.add_lt_add_left hi (E j)⟩
  simp [x, he]

private theorem block_factor (j : ℕ) :
    factor x (E j) (eta (u j)).length = eta (u j) := by
  apply List.ext_getElem
  · exact factor_len _ _ _
  · intro i hi hj
    rw [factor_get _ _ _ _ (by simpa only [factor_len] using hi)]
    exact block_letter j i hj

private theorem at_boundary (j : ℕ) : x (E j) = 0 := by
  have h := block_letter j 0 (eta_pos _)
  simpa [eta_cons] using h

/-- Occurrences are literal windows, including the origin and all overlaps. -/
def Occ (v : List Output) (A : ℕ) : Prop := factor x A v.length = v

private theorem occ_append (v z : List Output) (A : ℕ) :
    Occ (v++z) A ↔ Occ v A ∧ Occ z (A+v.length) := by
  unfold Occ
  rw [List.length_append, factor_add]
  constructor
  · intro h
    exact ⟨by simpa [factor_len] using congrArg (List.take v.length) h,
      by simpa [factor_len] using congrArg (List.drop v.length) h⟩
  · rintro ⟨h,h'⟩; rw [h,h']

private theorem occ_singleton (c : Output) (A : ℕ) : Occ [c] A ↔ x A = c := by
  simp [Occ, factor]

private theorem occ_letter {v : List Output} {A i : ℕ}
    (h : Occ v A) (hi : i < v.length) : x (A+i) = v[i] := by
  have hh := congrArg (fun z : List Output => z[i]?) h
  simpa [List.getElem?_eq_getElem, factor_get, factor_len, hi] using hh

private theorem first_block_recovery (a : Input) (z : List Output) (j : ℕ)
    (h : Occ (eta a ++ [0] ++ z) (E j)) : u j = a := by
  have hend : x (E j+(eta a).length) = 0 := by
    have := occ_letter h (i := (eta a).length) (by simp)
    simpa using this
  have hlen : (eta (u j)).length = (eta a).length := by
    apply le_antisymm
    · by_contra hn
      have hd : (eta a).length < (eta (u j)).length := by omega
      have hz := (eta_marker (u j) _ hd).mp ((block_letter j _ hd).symm.trans hend)
      have := eta_pos a
      omega
    · by_contra hn
      have hd : (eta (u j)).length < (eta a).length := by omega
      have hh := occ_letter h (i := (eta (u j)).length) (by simp; omega)
      have he : x (E j+(eta (u j)).length) = 0 := at_boundary (j+1)
      have hz : (eta a)[(eta (u j)).length] = 0 := by
        simpa only [List.getElem_append_left hd] using hh.symm.trans he
      have := (eta_marker a _ hd).mp hz
      have := eta_pos (u j)
      omega
  apply eta_injective
  have hv := ((occ_append (eta a) ([0]++z) (E j)).mp (by simpa [List.append_assoc] using h)).1
  simpa only [Occ, ← hlen, block_factor] using hv

/-- All-length marker reconstruction, with no source context premise. -/
theorem marked_core_recovery (w : List Input) (j : ℕ)
    (h : Occ (subst eta w ++ [0]) (E j)) : RichWordTypeIOccurrence.Occ w j := by
  induction w generalizing j with
  | nil => simp [RichWordTypeIOccurrence.Occ, factor]
  | cons a w ih =>
    have ha : u j = a := first_block_recovery a (subst eta w) j (by
      simpa [RankOneMorphismIterationBound.subst_cons, List.append_assoc] using h)
    have ht := ((occ_append (eta a) (subst eta w++[0]) (E j)).mp (by
      simpa [RankOneMorphismIterationBound.subst_cons, List.append_assoc] using h)).2
    have hw := ih (j+1) (by simpa [E, ha] using ht)
    change factor u j (w.length+1) = a::w
    rw [show w.length+1 = 1+w.length by omega, factor_add]
    simpa [factor, ha] using congrArg (fun z : List Input => [a]++z) hw

end D5.S1.Words.RichWordOutputDecoder
