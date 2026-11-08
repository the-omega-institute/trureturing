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

private theorem eta_marker_table :
    ∀ c : Input, ∀ i : Fin (eta c).length, (eta c)[i.val] = 0 ↔ i.val = 0 := by decide

private theorem eta_marker (c : Input) (i : ℕ) (hi : i < (eta c).length) :
    (eta c)[i] = 0 ↔ i = 0 := eta_marker_table c ⟨i,hi⟩

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

private theorem E_ge (j : ℕ) : j ≤ E j := E_strict.id_le j

private theorem window (p : ℕ) : ∃ j, E j ≤ p ∧ p < E (j+1) := by
  have hex : ∃ k, p < E k := ⟨p+1,lt_of_lt_of_le (Nat.lt_succ_self p) (E_ge (p+1))⟩
  have hh := Nat.find_spec hex
  have hp : 0 < Nat.find hex := by
    by_contra hn
    have hz : Nat.find hex=0 := by omega
    rw [hz,E] at hh
    omega
  refine ⟨Nat.find hex-1, ?_, ?_⟩
  · have := Nat.find_min hex (show Nat.find hex-1 < Nat.find hex by omega)
    omega
  · simpa only [show Nat.find hex-1+1=Nat.find hex by omega] using hh

private def blockIndex (p : ℕ) : ℕ := Nat.find (window p)

private theorem blockIndex_spec (p : ℕ) :
    E (blockIndex p) ≤ p ∧ p < E (blockIndex p+1) := Nat.find_spec (window p)

private theorem window_unique {p j k : ℕ}
    (hj : E j ≤ p ∧ p < E (j + 1)) (hk : E k ≤ p ∧ p < E (k + 1)) : j = k := by
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
    simp only [List.getElem_ofFn, Complexity.wordFactor]

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
    (hs : (0 : Output) ∉ s) (he : A + s.length = E j) :
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
    have hpre : [0]++t <+: eta (u j) :=
      List.prefix_iff_eq_take.mpr (by simpa [Nat.add_comm] using heq)
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

/-- Phase decorations for the original six cyclic source phases. -/
def r (n : ℕ) : List Output :=
  ![[],[],[],[2],[2,2],[2,2,3,2,2]] ⟨n%6,by omega⟩

private theorem r_free (n : ℕ) : (0 : Output) ∉ r n := by
  have h : ∀ i : Fin 6, (0 : Output) ∉ (![[],[],[],[2],[2,2],[2,2,3,2,2]] i) := by decide
  exact h ⟨n%6,by omega⟩

private theorem r_common (n : ℕ) (c : Input)
    (hc : c = RichWordTypeIOccurrence.phase n ∨ c = 6) :
    r n <:+ q c ∧ r n <+: q c := by
  have h : ∀ i : Fin 6, ∀ c : Input,
      (c.val=i.val ∨ c=6) →
      (![[],[],[],[2],[2,2],[2,2,3,2,2]] i : List Output) <:+ q c ∧
      (![[],[],[],[2],[2,2],[2,2,3,2,2]] i : List Output) <+: q c := by decide
  apply h ⟨n%6,by omega⟩ c
  rcases hc with rfl | hc
  · exact Or.inl rfl
  · exact Or.inr hc

private theorem typeI_paid (n j : ℕ)
    (hj : RichWordTypeIOccurrence.Occ (RichWordTypeIOccurrence.typeI n) j) :
    Left (r n) j ∧ Right (r n) (RichWordTypeIOccurrence.typeI n) j := by
  have hp : 0 < j := by
    by_contra hn
    have he : j=0 := by omega
    exact RichWordTypeIOccurrence.typeI_not_at_origin n (he ▸ hj)
  have hl := (RichWordTypeIOccurrence.lext_iff _ (u (j-1))).mpr ⟨j,hp,hj,rfl⟩
  have hr := (RichWordTypeIOccurrence.rext_iff _
    (u (j+(RichWordTypeIOccurrence.typeI n).length))).mpr
    ⟨j,hj,rfl⟩
  rw [(RichWordTypeIOccurrence.typeI_extensions n).1] at hl
  rw [(RichWordTypeIOccurrence.typeI_extensions n).2] at hr
  exact ⟨Or.inr ⟨hp,(r_common n _ (by simpa using hl)).1⟩,
    (r_common n _ (by simpa using hr)).2⟩

private theorem typeII_paid (n : ℕ) (hn : 6 ≤ n) (j : ℕ)
    (hj : RichWordTypeIOccurrence.Occ (RichWordTypeIIOccurrence.typeII n) j) :
    Left (r n) j ∧ Right (r n) (RichWordTypeIIOccurrence.typeII n) j := by
  have D := RichWordTypeIIOccurrence.actual_typeII n hn
  have hn' : n-6+6=n := by omega
  have ho := D.occurrence j
  rw [hn'] at ho
  obtain ⟨i,⟨hi,he⟩,_⟩ := ho.mp hj
  have hp : 0 < j := he ▸ D.positive i hi
  have hc := D.contexts i hi
  rw [hn',← he] at hc
  have hl : u (j-1)=RichWordTypeIOccurrence.phase n ∨ u (j-1)=6 := by
    change RichWordTypeIOccurrence.word (j-1)=_ ∨ RichWordTypeIOccurrence.word (j-1)=_
    rw [hc.1]; split_ifs <;> simp
  have hr : u (j+(RichWordTypeIIOccurrence.typeII n).length)=RichWordTypeIOccurrence.phase n ∨
      u (j+(RichWordTypeIIOccurrence.typeII n).length)=6 := by
    change RichWordTypeIOccurrence.word (j+(RichWordTypeIIOccurrence.typeII n).length)=_ ∨
      RichWordTypeIOccurrence.word (j+(RichWordTypeIIOccurrence.typeII n).length)=_
    rw [hc.2]; split_ifs <;> simp
  exact ⟨Or.inr ⟨hp,(r_common n _ hl).1⟩,(r_common n _ hr).2⟩

private theorem left_le {s : List Output} {j : ℕ} (h : Left s j) : s.length ≤ E j := by
  rcases h with rfl | ⟨hj,hq⟩
  · simp
  have hl := hq.length_le
  have he : E j = E (j-1)+(eta (u (j-1))).length := by
    have hh : E (j-1+1)=E (j-1)+(eta (u (j-1))).length := rfl
    simpa only [show j-1+1=j by omega] using hh
  rw [eta_cons] at he
  simp only [List.length_cons] at he
  omega

/-- The decorated output factor; the highlighted marker closes the source core. -/
def decorated (w : List Input) (s t : List Output) : List Output := s++subst eta w++[0]++t

/-- Consecutive output starts, with all overlapping windows retained. -/
def Consecutive (v : List Output) (A B : ℕ) : Prop :=
  A < B ∧ Occ v A ∧ Occ v B ∧ ∀ C, A < C → C < B → ¬ Occ v C

private theorem full_occurrence (w : List Input) (s t : List Output)
    (hs : (0 : Output) ∉ s) (ht : (0 : Output) ∉ t)
    (hpay : ∀ j, RichWordTypeIOccurrence.Occ w j → Left s j ∧ Right t w j) (A : ℕ) :
    Occ (decorated w s t) A ↔ ∃! j, A+s.length=E j ∧ RichWordTypeIOccurrence.Occ w j := by
  rw [decorated,occurrence_decoder w s t A hs ht]
  constructor
  · rintro ⟨j,hj,huniq⟩
    refine ⟨j,⟨hj.1,hj.2.1⟩,?_⟩
    intro k hk
    exact huniq k ⟨hk.1,hk.2,hpay k hk.2⟩
  · rintro ⟨j,hj,huniq⟩
    exact ⟨j,⟨hj.1,hj.2,hpay j hj.2⟩,fun k hk => huniq k ⟨hk.1,hk.2.1⟩⟩

private theorem output_at (w : List Input) (s t : List Output)
    (hs : (0 : Output) ∉ s) (ht : (0 : Output) ∉ t)
    (hpay : ∀ j, RichWordTypeIOccurrence.Occ w j → Left s j ∧ Right t w j)
    (j : ℕ) (hj : RichWordTypeIOccurrence.Occ w j) :
    Occ (decorated w s t) (E j-s.length) := by
  have hle := left_le (hpay j hj).1
  have heq := Nat.sub_add_cancel hle
  apply (full_occurrence w s t hs ht hpay _).mpr
  refine ⟨j,⟨heq,hj⟩,?_⟩
  intro k hk
  exact E_strict.injective (hk.1.symm.trans heq)

private theorem consecutive_transport (w : List Input) (s t : List Output)
    (hs : (0 : Output) ∉ s) (ht : (0 : Output) ∉ t)
    (hpay : ∀ j, RichWordTypeIOccurrence.Occ w j → Left s j ∧ Right t w j) (A B : ℕ) :
    Consecutive (decorated w s t) A B ↔ ∃ j k,
      A+s.length=E j ∧ B+s.length=E k ∧ RichWordTypeIOccurrence.Consecutive w j k := by
  constructor
  · rintro ⟨hAB,hA,hB,hno⟩
    obtain ⟨j,⟨hj,hoj⟩,_⟩ := (full_occurrence w s t hs ht hpay A).mp hA
    obtain ⟨k,⟨hk,hok⟩,_⟩ := (full_occurrence w s t hs ht hpay B).mp hB
    have hjk : j < k := E_strict.lt_iff_lt.mp (by omega)
    refine ⟨j,k,hj,hk,hjk,hoj,hok,?_⟩
    intro c hjc hck hoc
    have hc := left_le (hpay c hoc).1
    have hsc : E c-s.length+s.length=E c := Nat.sub_add_cancel hc
    have hjc' := E_strict hjc
    have hck' := E_strict hck
    exact hno (E c-s.length) (by omega) (by omega) (output_at w s t hs ht hpay c hoc)
  · rintro ⟨j,k,hj,hk,hjk,hoj,hok,hno⟩
    have hAB : A < B := by have := E_strict hjk; omega
    have hA := output_at w s t hs ht hpay j hoj
    have hB := output_at w s t hs ht hpay k hok
    have hAj : E j-s.length=A := by omega
    have hBk : E k-s.length=B := by omega
    refine ⟨hAB,hAj ▸ hA,hBk ▸ hB,?_⟩
    intro C hAC hCB hC
    obtain ⟨c,⟨hc,hoc⟩,_⟩ := (full_occurrence w s t hs ht hpay C).mp hC
    exact hno c (E_strict.lt_iff_lt.mp (by omega)) (E_strict.lt_iff_lt.mp (by omega)) hoc

/-- The positive letter weights are the literal image lengths. -/
def W (v : Input → ℕ) : ℕ := ∑ c, (eta c).length*v c

private theorem image_length (w : List Input) :
    (subst eta w).length = W (RichWordTypeIOccurrence.parikh w) := by
  classical
  simp only [subst,List.length_flatMap,Finset.sum_list_map_count]
  unfold W RichWordTypeIOccurrence.parikh AbelianBorders.AbelianBorderQuestionDefs.letterCount
  simp only [nsmul_eq_mul]
  rw [Finset.sum_subset (Finset.subset_univ w.toFinset)]
  · apply Finset.sum_congr rfl
    intro c hc
    exact Nat.mul_comm _ _
  · intro c _ hc
    simp [List.count_eq_zero_of_not_mem (by simpa using hc)]

private theorem W_mono {v z : Input → ℕ} (h : v ≤ z) : W v ≤ W z := by
  exact Finset.sum_le_sum (fun c _ => Nat.mul_le_mul_left _ (h c))

private theorem exact_gap (A B j k d : ℕ) (hj : A + d = E j) (hk : B + d = E k) (hjk : j ≤ k) :
    B-A = W (RichWordTypeIOccurrence.parikh (RichWordTypeIOccurrence.returnWord j k)) := by
  have he := E_add j (k-j)
  rw [Nat.add_sub_of_le hjk] at he
  have hl := image_length (factor u j (k-j))
  change B-A=W (RichWordTypeIOccurrence.parikh (factor u j (k-j)))
  omega

/-- Exact occurrences, consecutive pairs, weighted gaps and an attained return minimum. -/
structure Transport (w : List Input) (s t : List Output) (mu : Input → ℕ) : Prop where
  occurrence : ∀ A, Occ (decorated w s t) A ↔
    ∃! j, A+s.length=E j ∧ RichWordTypeIOccurrence.Occ w j
  consecutive : ∀ A B, Consecutive (decorated w s t) A B ↔ ∃ j k,
    A+s.length=E j ∧ B+s.length=E k ∧ RichWordTypeIOccurrence.Consecutive w j k
  gap : ∀ A B j k, A+s.length=E j → B+s.length=E k → j ≤ k →
    B-A=W (RichWordTypeIOccurrence.parikh (RichWordTypeIOccurrence.returnWord j k))
  minimum : (∃ A B j k, Consecutive (decorated w s t) A B ∧
    A+s.length=E j ∧ B+s.length=E k ∧ RichWordTypeIOccurrence.Consecutive w j k ∧
    RichWordTypeIOccurrence.parikh (RichWordTypeIOccurrence.returnWord j k)=mu ∧ B-A=W mu) ∧
    ∀ A B, Consecutive (decorated w s t) A B → W mu ≤ B-A

private theorem transport (w : List Input) (s t : List Output) (mu : Input → ℕ)
    (hs : (0 : Output) ∉ s) (ht : (0 : Output) ∉ t)
    (hpay : ∀ j, RichWordTypeIOccurrence.Occ w j → Left s j ∧ Right t w j)
    (hmin : (∃ j k, RichWordTypeIOccurrence.Consecutive w j k ∧
      RichWordTypeIOccurrence.parikh (RichWordTypeIOccurrence.returnWord j k) = mu) ∧
      ∀ j k, RichWordTypeIOccurrence.Consecutive w j k →
      mu ≤ RichWordTypeIOccurrence.parikh (RichWordTypeIOccurrence.returnWord j k)) :
    Transport w s t mu := by
  refine ⟨full_occurrence w s t hs ht hpay,consecutive_transport w s t hs ht hpay,
    fun A B j k => exact_gap A B j k s.length,?_,?_⟩
  · obtain ⟨j,k,hjk,he⟩ := hmin.1
    have hj := Nat.sub_add_cancel (left_le (hpay j hjk.2.1).1)
    have hk := Nat.sub_add_cancel (left_le (hpay k hjk.2.2.1).1)
    refine ⟨E j-s.length,E k-s.length,j,k,
      (consecutive_transport w s t hs ht hpay _ _).mpr ⟨j,k,hj,hk,hjk⟩,hj,hk,hjk,he,?_⟩
    rw [exact_gap _ _ j k s.length hj hk (Nat.le_of_lt hjk.1),he]
  · intro A B hAB
    obtain ⟨j,k,hj,hk,hjk⟩ := (consecutive_transport w s t hs ht hpay A B).mp hAB
    rw [exact_gap A B j k s.length hj hk (Nat.le_of_lt hjk.1)]
    exact W_mono (hmin.2 j k hjk)

private theorem paid_sub {w : List Input} {s t z : List Output} {j : ℕ}
    (h : Left z j ∧ Right z w j) (hs : s <:+ z) (ht : t <+: z) :
    Left s j ∧ Right t w j := by
  refine ⟨?_,ht.trans h.2⟩
  rcases h.1 with hz | ⟨hp,hq⟩
  · rw [hz] at hs
    exact Or.inl (List.suffix_nil.mp hs)
  · exact Or.inr ⟨hp,hs.trans hq⟩

/-- Every original Type-I index and every common decoration retain all occurrences. -/
theorem typeI_transport (n : ℕ) (s t : List Output) (hs : s <:+ r n) (ht : t <+: r n) :
    Transport (RichWordTypeIOccurrence.typeI n) s t
      ((RichWordTypeIOccurrence.M^n).mulVec (RichWordTypeIOccurrence.unit 6)) := by
  exact transport _ _ _ _ (fun h => r_free n (hs.sublist.mem h))
    (fun h => r_free n (ht.sublist.mem h)) (fun j hj => paid_sub (typeI_paid n j hj) hs ht)
    (RichWordTypeIOccurrence.typeI_return_minimum n)

/-- Original Type-II indices n at least six; the minimum column has exponent n. -/
theorem typeII_transport (n : ℕ) (hn : 6 ≤ n) (s t : List Output)
    (hs : s <:+ r n) (ht : t <+: r n) :
    Transport (RichWordTypeIIOccurrence.typeII n) s t
      ((RichWordTypeIOccurrence.M^n).mulVec (RichWordTypeIOccurrence.unit 0)) := by
  have D := RichWordTypeIIOccurrence.actual_typeII n hn
  have hh := D.minimum
  rw [show n-6+6=n by omega] at hh
  apply transport _ _ _ _ (fun h => r_free n (hs.sublist.mem h))
    (fun h => r_free n (ht.sublist.mem h)) (fun j hj => paid_sub (typeII_paid n hn j hj) hs ht)
  exact ⟨⟨_,_,hh.1,hh.2.1⟩,hh.2.2⟩

end D5.S1.Words.RichWordOutputDecoder
