/- GID: D5/S1/Words/RichWordOutputDecoder
   generality: I
   mirror-B: D5/B/S1/Words/RichWordOutputDecoder
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Literal four-letter marker reconstruction and actual occurrence transport. -/
import D5.S1.Words.RichWordTypeIIOccurrence
import D5.S1.Words.Complexity.SahasrabudheEvenAdditiveComplexityMorphism

/-! Exact marker parsing for the literal image of the frozen seven-letter source. -/
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
  have ht : ∀ c : Input, ∀ i : Fin (eta c).length, (eta c)[i.val] = 0 ↔ i.val = 0 := by decide
  exact ht c ⟨i,hi⟩

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
    · have hh := E_strict (show j+1 < j+1+1 by omega)
      exact ⟨j+1, by omega, by omega⟩

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

private theorem marker_boundary (p : ℕ) : x p = 0 ↔ ∃! j, p = E j := by
  constructor
  · intro hp
    obtain ⟨hj,hk⟩ := blockIndex_spec p
    have hd : p-E (blockIndex p) < (eta (u (blockIndex p))).length := by
      simp only [E] at hk; omega
    have hz := (eta_marker _ _ hd).mp hp
    refine ⟨blockIndex p, by omega, ?_⟩
    intro j he
    exact E_strict.injective (by omega)
  · rintro ⟨j,rfl,_⟩
    exact at_boundary j

private theorem E_add (j m : ℕ) :
    E (j+m) = E j + (subst eta (factor u j m)).length := by
  induction m with
  | zero => simp [factor, subst]
  | succ m ih =>
    rw [show j+(m+1) = (j+m)+1 by omega, E, ih]
    rw [show m+1 = m+1 from rfl, factor_add, subst_append, List.length_append]
    simp [factor, subst, Nat.add_assoc]

private theorem factor_ofFn {m : ℕ} (y : ℕ → Fin m) (j n : ℕ) :
    factor y j n = List.ofFn (Complexity.wordFactor y n j) := by
  apply List.ext_getElem
  · simp [factor_len]
  · intro i hi hj
    rw [factor_get _ _ _ _ (by simpa only [factor_len] using hi)]
    rfl

private def encode (c : Output) : ℤ := c.val

private theorem encode_injective : Function.Injective encode := by
  intro a b h
  apply Fin.ext
  exact Int.ofNat_inj.mp h

private theorem image_interval (j m : ℕ) :
    factor x (E j) (E (j+m)-E j) = subst eta (factor u j m) := by
  apply List.map_injective_iff.mpr encode_injective
  have hh := Complexity.SahasrabudheEvenAdditiveComplexityMorphism.morphic_block
    u (fun a => (eta a).map encode) (fun p => encode (x p)) E E_strict.monotone
    (by intro i; simp [E])
    (by intro i k hk; simpa using congrArg encode (block_letter i k (by simpa using hk))) j m
  rw [factor_ofFn, List.map_ofFn]
  change List.ofFn (Complexity.wordFactor (fun p => encode (x p)) _ _) = _
  simpa only [factor_ofFn, subst, List.map_flatMap] using hh

private theorem factor_image (j m : ℕ) :
    factor x (E j) (subst eta (factor u j m)).length = subst eta (factor u j m) := by
  simpa only [E_add, Nat.add_sub_cancel_left] using image_interval j m

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
        simpa only [List.append_assoc, List.getElem_append_left hd] using hh.symm.trans he
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
    obtain ⟨z,hz⟩ : ∃ z, subst eta w++[0]=[0]++z := by
      cases w with
      | nil => exact ⟨[],rfl⟩
      | cons b w => exact ⟨q b++subst eta w++[0], by simp [subst,eta_cons,List.append_assoc]⟩
    have ha : u j = a := first_block_recovery a z j (by
      simpa only [RankOneMorphismIterationBound.subst_cons, hz, List.append_assoc] using h)
    have ht := ((occ_append (eta a) (subst eta w++[0]) (E j)).mp (by
      simpa [RankOneMorphismIterationBound.subst_cons, List.append_assoc] using h)).2
    have hw := ih (j+1) (by simpa [E, ha] using ht)
    change factor u j (w.length+1) = a::w
    rw [show w.length+1 = 1+w.length by omega, factor_add]
    simpa [factor, ha] using congrArg (fun z : List Input => [a]++z) hw

private theorem marked_core_iff (w : List Input) (j : ℕ) :
    Occ (subst eta w ++ [0]) (E j) ↔ RichWordTypeIOccurrence.Occ w j := by
  constructor
  · exact marked_core_recovery w j
  · intro h
    change factor u j w.length = w at h
    have he : E (j+w.length) = E j+(subst eta w).length := by
      simpa only [h] using E_add j w.length
    apply (occ_append _ _ _).mpr
    refine ⟨?_, (occ_singleton _ _).mpr (he ▸ at_boundary (j+w.length))⟩
    simpa only [Occ,h] using factor_image j w.length

/-- The left filter imposes no predecessor when the decoration is empty. -/
def Left (s : List Output) (j : ℕ) : Prop :=
  s = [] ∨ (0 < j ∧ s <:+ q (u (j-1)))

/-- The right decoration lies in the actual tail after the last core marker. -/
def Right (t : List Output) (w : List Input) (j : ℕ) : Prop :=
  t <+: q (u (j+w.length))

private theorem left_boundary_iff (s : List Output) (A j : ℕ)
    (hs : (0 : Output) ∉ s) (he : A+s.length = E j) :
    Occ s A ↔ Left s j := by
  by_cases hn : s = []
  · simp [hn, Left, Occ, factor]
  have hd : 0 < s.length := List.length_pos_iff.mpr hn
  constructor
  · intro h
    have hj : 0 < j := by
      by_contra hz
      have hj0 : j=0 := by omega
      rw [hj0,E] at he
      omega
    have hpj : j-1+1=j := by omega
    have hep : E (j-1) < E j := E_strict (by omega)
    have hpa : E (j-1) < A := by
      by_contra hz
      have hi : E (j-1)-A < s.length := by omega
      have hh := occ_letter h hi
      have hh' : s[E (j-1)-A] = 0 := by
        rw [show A+(E (j-1)-A)=E (j-1) by omega, at_boundary] at hh
        exact hh.symm
      exact hs (hh' ▸ List.getElem_mem hi)
    have hlen : (eta (u (j-1))).length = A-E (j-1)+s.length := by
      have := E (j-1+1); have hh := congrArg E hpj
      rw [E] at hh
      omega
    have hb := block_factor (j-1)
    rw [hlen, factor_add, show E (j-1)+(A-E (j-1))=A by omega, h] at hb
    have hsu : s <:+ eta (u (j-1)) := ⟨factor x (E (j-1)) (A-E (j-1)), hb⟩
    rw [eta_cons, List.suffix_cons_iff] at hsu
    rcases hsu with hsu | hsu
    · exact (hs (by simp [hsu])).elim
    · exact Or.inr ⟨hj,hsu⟩
  · rintro (h | ⟨hj,hq⟩)
    · exact (hn h).elim
    obtain ⟨p,hp⟩ := hq
    have hlen := congrArg List.length hp
    have hb := block_factor (j-1)
    rw [eta_cons, ← hp] at hb
    have hj' : j-1+1=j := by omega
    have hstep := congrArg E hj'
    rw [E,eta_cons,← hp] at hstep
    simp only [List.length_cons,List.length_append] at hstep
    have hA : A=E (j-1)+(1+p.length) := by omega
    have hh : Occ ((0::p)++s) (E (j-1)) := by simpa [Occ] using hb
    simpa [hA,Nat.add_comm] using ((occ_append (0::p) s (E (j-1))).mp hh).2

private theorem right_boundary_iff (t : List Output) (j : ℕ)
    (ht : (0 : Output) ∉ t) :
    Occ ([0]++t) (E j) ↔ t <+: q (u j) := by
  constructor
  · intro h
    have hlen : 1+t.length ≤ (eta (u j)).length := by
      by_contra hn
      have hi : (eta (u j)).length < ([0]++t).length := by simp; omega
      have hp := eta_pos (u j)
      have hh := occ_letter h hi
      have hz : ([0]++t)[(eta (u j)).length] = 0 := by
        rw [show E j+(eta (u j)).length=E (j+1) from rfl,at_boundary] at hh
        exact hh.symm
      have hz' : t[(eta (u j)).length-1]'(by simp at hi; omega) = 0 := by
        simpa only [List.singleton_append, List.getElem_cons, Nat.ne_of_gt hp, dite_false] using hz
      exact ht (hz' ▸ List.getElem_mem (by simp at hi; omega))
    have hh := congrArg (List.take (1+t.length)) (block_factor j)
    have hf : (factor x (E j) (eta (u j)).length).take (1+t.length) =
        factor x (E j) (1+t.length) := by
      simp [factor, ← List.map_take, List.take_range, Nat.min_eq_left hlen]
    rw [hf] at hh
    have heq : [0]++t = (eta (u j)).take (1+t.length) := by
      have h' : factor x (E j) (1+t.length)=[0]++t := by simpa [Occ,Nat.add_comm] using h
      exact h'.symm.trans hh
    have hpre : [0]++t <+: eta (u j) := List.prefix_iff_eq_take.mpr (by simpa [Nat.add_comm] using heq)
    simpa [eta_cons] using hpre
  · rintro ⟨z,hz⟩
    have hh : Occ (([0]++t)++z) (E j) := by
      simpa [Occ,eta_cons,← hz] using block_factor j
    exact ((occ_append ([0]++t) z (E j)).mp hh).1

/-- Exact filtered decoder for every core, including the empty core and origin. -/
theorem occurrence_decoder (w : List Input) (s t : List Output) (A : ℕ)
    (hs : (0 : Output) ∉ s) (ht : (0 : Output) ∉ t) :
    Occ (s++subst eta w++[0]++t) A ↔
      ∃! j, A+s.length=E j ∧ RichWordTypeIOccurrence.Occ w j ∧ Left s j ∧ Right t w j := by
  constructor
  · intro h
    obtain ⟨hl,hrest⟩ := (occ_append s (subst eta w++[0]++t) A).mp
      (by simpa [List.append_assoc] using h)
    have hcore := ((occ_append (subst eta w++[0]) t _).mp hrest).1
    have hz : x (A+s.length)=0 := by
      cases w with
      | nil => simpa [subst,occ_singleton] using hcore
      | cons a w =>
        have hh := occ_letter hcore (i := 0) (by simp [subst,eta_cons])
        simpa [subst,eta_cons] using hh
    obtain ⟨j,hj,hunique⟩ := (marker_boundary _).mp hz
    have hw := (marked_core_iff w j).mp (hj ▸ hcore)
    have hw' : factor u j w.length=w := hw
    have hend : E (j+w.length)=E j+(subst eta w).length := by
      simpa only [hw'] using E_add j w.length
    have hr : Occ ([0]++t) (E (j+w.length)) := by
      have := ((occ_append (subst eta w) ([0]++t) _).mp
        (by simpa [List.append_assoc] using hrest)).2
      simpa [hj,← hend] using this
    refine ⟨j, ⟨hj,hw,(left_boundary_iff s A j hs hj).mp hl,
      (right_boundary_iff t (j+w.length) ht).mp hr⟩, ?_⟩
    intro k hk
    exact hunique k hk.1
  · rintro ⟨j,⟨hj,hw,hl,hr⟩,_⟩
    have hw' : factor u j w.length=w := hw
    have hleft := (left_boundary_iff s A j hs hj).mpr hl
    have hcore := (marked_core_iff w j).mpr hw
    have hright := (right_boundary_iff t (j+w.length) ht).mpr hr
    have hend : E (j+w.length)=E j+(subst eta w).length := by
      simpa only [hw'] using E_add j w.length
    have he : Occ (subst eta w++([0]++t)) (E j) := by
      apply (occ_append (subst eta w) ([0]++t) (E j)).mpr
      refine ⟨((occ_append (subst eta w) [0] (E j)).mp hcore).1, ?_⟩
      simpa [← hend] using hright
    have hh := (occ_append s (subst eta w++[0]++t) A).mpr
      ⟨hleft, by simpa [hj,List.append_assoc] using he⟩
    simpa only [List.append_assoc] using hh

end D5.S1.Words.RichWordOutputDecoder
