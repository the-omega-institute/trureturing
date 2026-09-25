/- GID: D5/S3/Combinatorics/ArrowWilfTwelveInverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfTwelveInverse
   mirror-E: none(waiver:inverse-recovery-for-the-twelve-arrow-pattern)
   anchors: [mathlib/module/Mathlib.Data.List.SplitLengths]
   utility: none
   digest: Filtering a decorated twelve word recovers its upper skeleton. -/

import D5.S3.Combinatorics.ArrowWilfTwelveCount
import Mathlib.Data.List.SplitLengths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfTwelveInverse

noncomputable section

open D5.S3.Combinatorics.ArrowWilfCountingCore
open D5.S3.Combinatorics.ArrowWilfGapData
open D5.S3.Combinatorics.ArrowWilfTwelveCount
open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization
open D5.S3.Combinatorics.ArrowWilfFixedInsertion

/-- The block before a distinguished next skeleton entry is its maximal filler prefix. -/
theorem takeWhile_filler_prefix {α : Type*} (P : α → Bool)
    {b : List α} {a : α} {t : List α}
    (hb : ∀ x ∈ b, P x = false) (ha : P a = true) :
    (b ++ a :: t).takeWhile (fun x => !P x) = b := by
  induction b with
  | nil => simp [ha]
  | cons x xs ih =>
      have hx : P x = false := hb x (by simp)
      have hxs : ∀ y ∈ xs, P y = false := by
        intro y hy
        exact hb y (by simp [hy])
      simp [hx, ih hxs]

/-- An interleaving uniquely determines all its filler blocks. -/
theorem afterBlocks_injective_blocks {α : Type*} (P : α → Bool)
    {s : List α} {bs cs : List (List α)}
    (hblen : bs.length = s.length) (hclen : cs.length = s.length)
    (hs : ∀ x ∈ s, P x = true)
    (hb : ∀ b ∈ bs, ∀ x ∈ b, P x = false)
    (hc : ∀ c ∈ cs, ∀ x ∈ c, P x = false)
    (heq : afterBlocks s bs = afterBlocks s cs) : bs = cs := by
  induction s generalizing bs cs with
  | nil =>
      have hbn : bs = [] := List.eq_nil_of_length_eq_zero hblen
      have hcn : cs = [] := List.eq_nil_of_length_eq_zero hclen
      rw [hbn, hcn]
  | cons a s ih =>
      rcases bs with _ | ⟨b, bs⟩
      · simp at hblen
      rcases cs with _ | ⟨c, cs⟩
      · simp at hclen
      have ha : P a = true := hs a (by simp)
      have hb0 : ∀ x ∈ b, P x = false := hb b (by simp)
      have hc0 : ∀ x ∈ c, P x = false := hc c (by simp)
      have hbs : ∀ d ∈ bs, ∀ x ∈ d, P x = false := by
        intro d hd x hx
        exact hb d (by simp [hd]) x hx
      have hcs : ∀ d ∈ cs, ∀ x ∈ d, P x = false := by
        intro d hd x hx
        exact hc d (by simp [hd]) x hx
      have hss : ∀ x ∈ s, P x = true := by
        intro x hx
        exact hs x (by simp [hx])
      have hblen' : bs.length = s.length := by simpa using hblen
      have hclen' : cs.length = s.length := by simpa using hclen
      have heq' : b ++ afterBlocks s bs = c ++ afterBlocks s cs := by
        simpa [afterBlocks] using heq
      have hbc : b = c := by
        cases s with
        | nil =>
            have hbn : bs = [] := List.eq_nil_of_length_eq_zero hblen'
            have hcn : cs = [] := List.eq_nil_of_length_eq_zero hclen'
            simp [hbn, hcn, afterBlocks] at heq'
            exact heq'
        | cons x xs =>
            have hx : P x = true := hss x (by simp)
            have ht := congrArg (fun l => l.takeWhile (fun y => !P y)) heq'
            cases bs with
            | nil => simp at hblen'
            | cons d ds =>
                cases cs with
                | nil => simp at hclen'
                | cons e es =>
                    simpa [afterBlocks, takeWhile_filler_prefix P hb0 hx,
                      takeWhile_filler_prefix P hc0 hx] using ht
      subst c
      have htail : afterBlocks s bs = afterBlocks s cs := by
        exact List.append_cancel_left heq'
      have hrest := ih hblen' hclen' hss hbs hcs htail
      simp [hrest]

/-- The initial filler block and all later filler blocks are recoverable. -/
theorem interleaving_blocks_eq {α : Type*} (P : α → Bool)
    {a : α} {s : List α} {u v : List α} {bs cs : List (List α)}
    (ha : P a = true) (hs : ∀ x ∈ s, P x = true)
    (hu : ∀ x ∈ u, P x = false) (hv : ∀ x ∈ v, P x = false)
    (hb : ∀ b ∈ bs, ∀ x ∈ b, P x = false)
    (hc : ∀ c ∈ cs, ∀ x ∈ c, P x = false)
    (hblen : bs.length = s.length) (hclen : cs.length = s.length)
    (heq : u ++ a :: afterBlocks s bs = v ++ a :: afterBlocks s cs) :
    u = v ∧ bs = cs := by
  have huv : u = v := by
    have h := congrArg (fun l => l.takeWhile (fun x => !P x)) heq
    simpa [takeWhile_filler_prefix P hu ha,
      takeWhile_filler_prefix P hv ha] using h
  subst v
  have hrest : afterBlocks s bs = afterBlocks s cs := by
    have h := List.append_cancel_left heq
    simpa using h
  exact ⟨rfl, afterBlocks_injective_blocks P hblen hclen hs hb hc hrest⟩

/-- Every two-colour word splits into its skeleton and intervening filler blocks. -/
theorem exists_afterBlocks_decomposition {α : Type*} (P : α → Bool) (q : List α) :
    ∃ u s bs, q = u ++ afterBlocks s bs ∧ s = q.filter P ∧
      bs.length = s.length ∧
      (∀ x ∈ u, P x = false) ∧
      (∀ b ∈ bs, ∀ x ∈ b, P x = false) := by
  induction q with
  | nil =>
      exact ⟨[], [], [], by simp [afterBlocks], by simp, by simp,
        by simp, by simp⟩
  | cons a q ih =>
      obtain ⟨u, s, bs, hq, hs, hlen, hu, hb⟩ := ih
      by_cases ha : P a = true
      · refine ⟨[], a :: s, u :: bs, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hq, afterBlocks]
        · simp [ha, hs]
        · simp [hlen]
        · simp
        · intro b hbu x hx
          rcases List.mem_cons.mp hbu with rfl | hbu
          · exact hu x hx
          · exact hb b hbu x hx
      · have haf : P a = false := Bool.eq_false_iff.mpr ha
        refine ⟨a :: u, s, bs, ?_, ?_, hlen, ?_, hb⟩
        · simpa [hq] using rfl
        · simp [haf, hs]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact haf
          · exact hu x hx

/-- A singleton Foata block occurs after a smaller prefix and before a larger successor. -/
theorem fixedSyntax_decomposition {f : ℕ} {p : List ℕ} (h : FixedSyntax f p) :
    ∃ u q, p = u ++ f :: q ∧ (∀ x ∈ u, x < f) ∧
      (q = [] ∨ ∃ a t, q = a :: t ∧ f < a) := by
  induction p with
  | nil => simp [FixedSyntax] at h
  | cons a q ih =>
      cases q with
      | nil =>
          have ha : a = f := by simpa [FixedSyntax] using h
          subst a
          exact ⟨[], [], by simp, by simp, Or.inl rfl⟩
      | cons b t =>
          by_cases haf : a = f
          · subst a
            have hfb : f < b := by simpa [FixedSyntax] using h
            exact ⟨[], b :: t, by simp, by simp, Or.inr ⟨b, t, rfl, hfb⟩⟩
          · have halt : a < f ∧ FixedSyntax f (b :: t) := by
              simpa [FixedSyntax, haf] using h
            obtain ⟨u, r, hq, hu, hr⟩ := ih halt.2
            refine ⟨a :: u, r, ?_, ?_, hr⟩
            · simpa [hq]
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact halt.1
              · exact hu x hx

/-- The upper skeleton can be read directly from the decorated word. -/
theorem twelveList_upper_filter {n m k : ℕ} (d : TwelveData n m k) :
    (twelveList d).filter (fun x => decide (m < x)) = d.sigma.1.1 := by
  let H := upperSupport n m
  let sizes := gapSizes H d.sigma.1 d.gaps.1
  let blocks := sizes.splitLengths (lowerDescending m)
  let P : ℕ → Bool := fun x => decide (m < x)
  have hsigma : d.sigma.1.1.Perm H.toList := by
    simpa [words, List.mem_permutations] using d.sigma.1.2
  have hsizes := gapSizes_length_sum H d.sigma.1 d.gaps.1
  have hblocksLen : blocks.length = d.sigma.1.1.length + 1 := by
    rw [List.length_splitLengths, hsizes.1]
    simpa using hsigma.length_eq.symm
  have htailLen : blocks.tail.length = d.sigma.1.1.length := by
    rw [List.length_tail, hblocksLen]
    omega
  have hlowLen : (lowerDescending m).length = m - 1 := by
    simp [lowerDescending]
  have hflatten : blocks.flatten = lowerDescending m :=
    List.flatten_splitLengths _ _ (by rw [hlowLen, hsizes.2])
  have hblocks : blocks.headD [] ++ blocks.tail.flatten = lowerDescending m := by
    rw [← hflatten]
    cases blocks with
    | nil => simp
    | cons b bs => simp
  have hsmall : ∀ b ∈ blocks.tail, ∀ x ∈ b, ¬ P x := by
    intro b hb x hx
    have hxlow : x ∈ lowerDescending m := by
      rw [← hblocks]
      exact List.mem_append.mpr (Or.inr (List.mem_flatten.mpr ⟨b, hb, hx⟩))
    simp only [lowerDescending, List.mem_reverse, List.mem_range', one_mul] at hxlow
    rcases hxlow with ⟨i, hi, heq⟩
    simp [P]
    omega
  have hlarge : ∀ x ∈ d.sigma.1.1, P x := by
    intro x hx
    have hxH : x ∈ H := Finset.mem_toList.mp (hsigma.mem_iff.mp hx)
    simp only [H, upperSupport, List.mem_toFinset, List.mem_range', one_mul] at hxH
    rcases hxH with ⟨i, hi, heq⟩
    simp [P]
    omega
  have hhead : (blocks.headD []).filter P = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hxlow : x ∈ lowerDescending m := by
      rw [← hblocks]
      exact List.mem_append.mpr (Or.inl hx)
    simp only [lowerDescending, List.mem_reverse, List.mem_range', one_mul] at hxlow
    rcases hxlow with ⟨i, hi, heq⟩
    simp [P]
    omega
  have hafter := filter_afterBlocks_skeleton P htailLen hlarge hsmall
  change (blocks.headD [] ++ m :: afterBlocks d.sigma.1.1 blocks.tail).filter P = _
  have hPm : P m = false := by simp [P]
  rw [List.filter_append, hhead, List.nil_append, List.filter_cons, hPm]
  simpa using hafter

/-- Equal outputs have the same split of the decreasing lower word into gaps. -/
theorem twelveList_blocks_eq {n m k k' : ℕ}
    {d : TwelveData n m k} {e : TwelveData n m k'}
    (heq : twelveList d = twelveList e) :
    (gapSizes (upperSupport n m) d.sigma.1 d.gaps.1).splitLengths
        (lowerDescending m) =
      (gapSizes (upperSupport n m) e.sigma.1 e.gaps.1).splitLengths
        (lowerDescending m) := by
  let H := upperSupport n m
  let bd := (gapSizes H d.sigma.1 d.gaps.1).splitLengths (lowerDescending m)
  let be := (gapSizes H e.sigma.1 e.gaps.1).splitLengths (lowerDescending m)
  let P : ℕ → Bool := fun x => decide (m ≤ x)
  have hs : d.sigma.1.1 = e.sigma.1.1 := by
    rw [← twelveList_upper_filter d, ← twelveList_upper_filter e, heq]
  have hdata : ∀ {j : ℕ} (v : TwelveData n m j),
      let bs := (gapSizes H v.sigma.1 v.gaps.1).splitLengths (lowerDescending m)
      bs.tail.length = v.sigma.1.1.length ∧
      (∀ b ∈ bs, ∀ x ∈ b, P x = false) ∧
      (∀ x ∈ v.sigma.1.1, P x = true) := by
    intro j v bs
    have hvperm : v.sigma.1.1.Perm H.toList := by
      simpa [words, List.mem_permutations] using v.sigma.1.2
    have hlen : bs.length = v.sigma.1.1.length + 1 := by
      rw [List.length_splitLengths, (gapSizes_length_sum H v.sigma.1 v.gaps.1).1]
      simpa using hvperm.length_eq.symm
    have hflat : bs.flatten = lowerDescending m := by
      apply List.flatten_splitLengths
      rw [show (lowerDescending m).length = m - 1 by simp [lowerDescending]]
      rw [(gapSizes_length_sum H v.sigma.1 v.gaps.1).2]
    refine ⟨by rw [List.length_tail, hlen]; omega, ?_, ?_⟩
    · intro b hb x hx
      have hxlow : x ∈ lowerDescending m := by
        rw [← hflat]
        exact List.mem_flatten.mpr ⟨b, hb, hx⟩
      simp only [lowerDescending, List.mem_reverse, List.mem_range', one_mul] at hxlow
      rcases hxlow with ⟨i, hi, hi'⟩
      simp [P]
      omega
    · intro x hx
      have hxH : x ∈ H := Finset.mem_toList.mp (hvperm.mem_iff.mp hx)
      simp only [H, upperSupport, List.mem_toFinset, List.mem_range', one_mul] at hxH
      rcases hxH with ⟨i, hi, hi'⟩
      simp [P]
      omega
  obtain ⟨hdlen, hdsmall, hdlarge⟩ := hdata d
  obtain ⟨helen, hesmall, helarge⟩ := hdata e
  have hdprefix : ∀ x ∈ bd.headD [], P x = false := by
    cases hbd : bd with
    | nil => simp
    | cons b bs =>
        have hbmem : b ∈ bd := by rw [hbd]; simp
        simpa [hbd] using hdsmall b hbmem
  have heprefix : ∀ x ∈ be.headD [], P x = false := by
    cases hbe : be with
    | nil => simp
    | cons b bs =>
        have hbmem : b ∈ be := by rw [hbe]; simp
        simpa [hbe] using hesmall b hbmem
  have hdtail : ∀ b ∈ bd.tail, ∀ x ∈ b, P x = false := by
    intro b hb
    exact hdsmall b (List.mem_of_mem_tail hb)
  have hetail : ∀ b ∈ be.tail, ∀ x ∈ b, P x = false := by
    intro b hb
    exact hesmall b (List.mem_of_mem_tail hb)
  have hword : bd.headD [] ++ m :: afterBlocks d.sigma.1.1 bd.tail =
      be.headD [] ++ m :: afterBlocks e.sigma.1.1 be.tail := heq
  rw [← hs] at hword
  have hrec := interleaving_blocks_eq P (by simp [P]) hdlarge hdprefix heprefix
    hdtail hetail hdlen (by rw [hs]; exact helen) hword
  have hdnon : bd ≠ [] := by
    intro hn
    have hl : bd.length = d.sigma.1.1.length + 1 := by
      simp [bd, gapSizes]
    rw [hn] at hl
    simp at hl
  have henon : be ≠ [] := by
    intro hn
    have hl : be.length = e.sigma.1.1.length + 1 := by
      simp [be, gapSizes]
    rw [hn] at hl
    simp at hl
  have hblocks : bd = be := by
    cases hbd : bd with
    | nil => exact (hdnon hbd).elim
    | cons b bs =>
        cases hbe : be with
        | nil => exact (henon hbe).elim
        | cons c cs =>
            exact congrArg₂ List.cons (by simpa [hbd, hbe] using hrec.1)
              (by simpa [hbd, hbe] using hrec.2)
  simpa [bd, be] using hblocks

/-- Equal decorated outputs have equal labelled gap functions. -/
theorem twelveList_gap_raw_eq {n m k k' : ℕ}
    {d : TwelveData n m k} {e : TwelveData n m k'}
    (heq : twelveList d = twelveList e) : d.gaps.1.1 = e.gaps.1.1 := by
  let H := upperSupport n m
  let s := d.sigma.1.1
  have hs : s = e.sigma.1.1 := by
    change d.sigma.1.1 = e.sigma.1.1
    rw [← twelveList_upper_filter d, ← twelveList_upper_filter e, heq]
  have hdSum := (gapSizes_length_sum H d.sigma.1 d.gaps.1).2
  have heSum := (gapSizes_length_sum H e.sigma.1 e.gaps.1).2
  have hlen : (lowerDescending m).length = m - 1 := by simp [lowerDescending]
  have h := congrArg (List.map List.length) (twelveList_blocks_eq heq)
  rw [List.map_splitLengths_length (lowerDescending m) _ (by rw [hlen, hdSum]),
    List.map_splitLengths_length (lowerDescending m) _ (by rw [hlen, heSum])] at h
  have hnone : d.gaps.1.1 none = e.gaps.1.1 none := by
    have hh := congrArg List.head? h
    simpa [gapSizes] using hh
  have hmap : s.map (gapAt H d.gaps.1) = s.map (gapAt H e.gaps.1) := by
    have ht := congrArg List.tail h
    simpa [s, gapSizes, hs] using ht
  apply Finsupp.ext
  intro i
  cases i with
  | none => exact hnone
  | some x =>
      have hp : s.Perm H.toList := by
        simpa [s, words, List.mem_permutations] using d.sigma.1.2
      have hx : x.1 ∈ s := hp.mem_iff.mpr (by simpa using x.2)
      have hidx : s.idxOf x.1 < s.length := List.idxOf_lt_length_of_mem hx
      have hg := congrArg (fun l : List ℕ => l.getD (s.idxOf x.1) 0) hmap
      rw [List.getD_eq_getElem (l := s.map (gapAt H d.gaps.1)) 0 (by simpa using hidx),
        List.getElem_map,
        List.getD_eq_getElem (l := s.map (gapAt H e.gaps.1)) 0 (by simpa using hidx),
        List.getElem_map, List.getElem_idxOf hidx] at hg
      simpa [gapAt, x.2] using hg

/-- The recovered upper word determines which upper values belong to the deranged set. -/
theorem twelveList_K_eq {n m k k' : ℕ}
    {d : TwelveData n m k} {e : TwelveData n m k'}
    (heq : twelveList d = twelveList e) : d.K.1 = e.K.1 := by
  let H := upperSupport n m
  have hs : d.sigma.1.1 = e.sigma.1.1 := by
    rw [← twelveList_upper_filter d, ← twelveList_upper_filter e, heq]
  have hKd : d.K.1 ⊆ H := (Finset.mem_powersetCard.mp d.K.2).1
  have hKe : e.K.1 ⊆ H := (Finset.mem_powersetCard.mp e.K.2).1
  ext x
  by_cases hx : x ∈ H
  · have hd := d.sigma.2 x hx
    have he := e.sigma.2 x hx
    rw [← hs] at he
    simp only [Finset.mem_sdiff] at hd he
    constructor
    · intro hxd
      by_contra hxe
      exact (hd.mp (he.mpr ⟨hx, hxe⟩)).2 hxd
    · intro hxe
      by_contra hxd
      exact (he.mp (hd.mpr ⟨hx, hxd⟩)).2 hxe
  · constructor
    · intro hxd
      exact (hx (hKd hxd)).elim
    · intro hxe
      exact (hx (hKe hxe)).elim

/-- For fixed parameters, the decorated construction is injective. -/
theorem twelveList_injective {n m k : ℕ} :
    Function.Injective (twelveList : TwelveData n m k → List ℕ) := by
  intro d e heq
  have hKraw := twelveList_K_eq heq
  have hsraw : d.sigma.1.1 = e.sigma.1.1 := by
    rw [← twelveList_upper_filter d, ← twelveList_upper_filter e, heq]
  have hgraw := twelveList_gap_raw_eq heq
  have hK : d.K = e.K := Subtype.ext hKraw
  cases d with
  | mk Kd sd ed gd =>
      cases e with
      | mk Ke se ee ge =>
          dsimp at hK hsraw hgraw
          cases hK
          have hsd : sd = se := by
            apply Subtype.ext
            apply Subtype.ext
            exact hsraw
          cases hsd
          have hgd : gd = ge := by
            apply Subtype.ext
            apply Subtype.ext
            exact hgraw
          cases hgd
          rfl

/-- The distinguished value is uniquely determined by the decorated output. -/
theorem twelveList_m_eq {n m m' k k' : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hm' : 1 ≤ m') (hm'n : m' ≤ n)
    (d : TwelveData n m k) (e : TwelveData n m' k')
    (heq : twelveList d = twelveList e) : m = m' := by
  have hd : hat (twelveList d) m = m := twelveList_fixed_m hm hmn d
  have he : hat (twelveList e) m' = m' := twelveList_fixed_m hm' hm'n e
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmH : m' ∈ upperSupport n m := by
      simp only [upperSupport, List.mem_toFinset, List.mem_range', one_mul]
      refine ⟨m' - (m + 1), ?_, ?_⟩ <;> omega
    exact twelveList_no_upper_fixed hm hmn d hmH (by rw [heq]; exact he)
  · have hmH : m ∈ upperSupport n m' := by
      simp only [upperSupport, List.mem_toFinset, List.mem_range', one_mul]
      refine ⟨m - (m' + 1), ?_, ?_⟩ <;> omega
    exact twelveList_no_upper_fixed hm' hm'n e hmH (by rw [← heq]; exact hd)

/-- At a fixed point of a twelve avoider, all smaller values have their forced order. -/
theorem avoiding_lower_filter {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (p : Word (fullSupport n)) (hfixed : hat p.1 m = m)
    (havoid : ¬ Contains [1, 2] [(3, 3)] 3 p.1) :
    p.1.filter (fun x => decide (x < m)) = lowerDescending m := by
  let low := p.1.filter (fun x => decide (x < m))
  have hpperm : p.1.Perm (List.range' 1 n) := by
    have hp : p.1.Perm (fullSupport n).toList := by
      simpa [words, List.mem_permutations] using p.2
    apply hp.trans
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact (fullSupport n).nodup_toList
    · exact List.nodup_range'
    · simp [fullSupport]
  have hnodup : p.1.Nodup := hpperm.nodup_iff.mpr List.nodup_range'
  have hmem : ∀ x, x ∈ p.1 ↔ 1 ≤ x ∧ x ≤ n := by
    intro x
    rw [hpperm.mem_iff]
    simp only [List.mem_range', one_mul]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · rintro ⟨h1, hn⟩
      exact ⟨x - 1, by omega, by omega⟩
  have hmp : m ∈ p.1 := (hmem m).mpr ⟨hm, hmn⟩
  have hchar := (avoids_twelve_iff hnodup).mp havoid
  have hdesc : low.Pairwise (· > ·) := by
    rw [List.pairwise_iff_forall_sublist]
    intro a b hab
    have habp : [a, b].Sublist p.1 := hab.trans List.filter_sublist
    have ha : a ∈ p.1 := habp.subset (by simp)
    have hb : b ∈ p.1 := habp.subset (by simp)
    have halow : a < m := by
      have : a ∈ low := hab.subset (by simp)
      simpa using (List.mem_filter.mp this).2
    have hblow : b < m := by
      have : b ∈ low := hab.subset (by simp)
      simpa using (List.mem_filter.mp this).2
    have hne : a ≠ b := by
      intro he
      subst b
      have hbad := hnodup.sublist habp
      simpa using hbad
    by_contra hnot
    have halt : a < b := by omega
    have hbap := hchar m hmp hfixed a b halt hblow ha hb
    exact pair_sublist_asymm hnodup hne ⟨habp, hbap⟩
  have hperm : low.Perm (lowerDescending m) := by
    apply (List.perm_ext_iff_of_nodup (hnodup.filter _) (by
      simp [lowerDescending, List.nodup_range'])).mpr
    intro x
    simp only [low, List.mem_filter, decide_eq_true_eq,
      lowerDescending, List.mem_reverse, List.mem_range', one_mul]
    rw [hmem]
    constructor
    · rintro ⟨⟨h1, hn⟩, hxm⟩
      exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  exact hperm.eq_of_pairwise' hdesc (by
    rw [lowerDescending, List.pairwise_reverse]
    exact List.pairwise_lt_range')

/-- An avoiding word with a fixed point has a unique upper skeleton and lower-block shape. -/
theorem avoiding_twelve_normal_form {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (p : Word (fullSupport n)) (hfixed : hat p.1 m = m)
    (havoid : ¬ Contains [1, 2] [(3, 3)] 3 p.1) :
    ∃ u s bs, p.1 = u ++ m :: afterBlocks s bs ∧
      s = p.1.filter (fun x => decide (m < x)) ∧
      bs.length = s.length ∧
      (∀ x ∈ u, x < m) ∧
      (∀ b ∈ bs, ∀ x ∈ b, x < m) ∧
      u ++ bs.flatten = lowerDescending m := by
  let P : ℕ → Bool := fun x => decide (m < x)
  have hpperm : p.1.Perm (List.range' 1 n) := by
    have hp : p.1.Perm (fullSupport n).toList := by
      simpa [words, List.mem_permutations] using p.2
    apply hp.trans
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact (fullSupport n).nodup_toList
    · exact List.nodup_range'
    · simp [fullSupport]
  have hnodup : p.1.Nodup := hpperm.nodup_iff.mpr List.nodup_range'
  have hmp : m ∈ p.1 := hpperm.mem_iff.mpr (by
    simp only [List.mem_range', one_mul]
    exact ⟨m - 1, by omega, by omega⟩)
  obtain ⟨u, q, hp, hu, hqhead⟩ :=
    fixedSyntax_decomposition ((fixedSyntax_iff_hat_fixed hnodup hmp).mpr hfixed)
  have hqnot : m ∉ q := by
    have hsub : (m :: q).Sublist p.1 := by
      rw [hp]
      exact List.sublist_append_right _ _
    exact (List.nodup_cons.mp (hnodup.sublist hsub)).1
  obtain ⟨v, s, bs, hq, hs, hlen, hv, hb⟩ := exists_afterBlocks_decomposition P q
  have hvnil : v = [] := by
    rcases hqhead with hnil | ⟨a, t, hcons, hma⟩
    · rw [hnil] at hq
      cases v with
      | nil => rfl
      | cons x xs => simp at hq
    · cases v with
      | nil => rfl
      | cons x xs =>
          have hax : a = x := by
            have hh := hq
            rw [hcons] at hh
            simpa using congrArg List.head? hh
          have hxfalse := hv x (by simp)
          simp [P, ← hax, hma] at hxfalse
  subst v
  have hbsSmall : ∀ b ∈ bs, ∀ x ∈ b, x < m := by
    intro b hbmem x hx
    have hxfalse := hb b hbmem x hx
    have hxle : x ≤ m := by
      simp [P] at hxfalse
      omega
    have hxq : x ∈ q := by
      rw [hq]
      exact (afterBlocks_perm hlen).mem_iff.mpr (by
        exact List.mem_append.mpr (Or.inr (List.mem_flatten.mpr ⟨b, hbmem, hx⟩)))
    have hxne : x ≠ m := by rintro rfl; exact hqnot hxq
    omega
  have hsLarge : ∀ x ∈ s, P x = true := by
    intro x hx
    rw [hs] at hx
    exact (List.mem_filter.mp hx).2
  have hsfull : s = p.1.filter P := by
    rw [hp, hq]
    simp only [List.filter_append, List.filter_cons]
    have huFilter : u.filter P = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hxm := hu x hx
      simp [P]
      omega
    have hPm : P m = false := by simp [P]
    have hafter : (afterBlocks s bs).filter P = s :=
      filter_afterBlocks_skeleton P hlen hsLarge (by
        intro b hbmem x hx
        simpa [hb b hbmem x hx])
    simp only [List.filter_append, huFilter, List.nil_append,
      List.filter_cons, hPm, Bool.false_eq_true, ↓reduceIte, hafter]
    simp
  have hlow := avoiding_lower_filter hm hmn p hfixed havoid
  have hlowShape : u ++ bs.flatten = p.1.filter (fun x => decide (x < m)) := by
    rw [hp, hq]
    have huFilter : u.filter (fun x => decide (x < m)) = u := by
      apply List.filter_eq_self.mpr
      intro x hx
      simpa using hu x hx
    have hafter : (afterBlocks s bs).filter (fun x => decide (x < m)) = bs.flatten := by
      have hP : (fun x : ℕ => !decide (m ≤ x)) = (fun x => decide (x < m)) := by
        funext x
        by_cases hx : x < m
        · simp [hx, Nat.not_le.mpr hx]
        · have hmx : m ≤ x := by omega
          simp [hx, hmx]
      rw [← hP]
      apply filter_afterBlocks_fillers (fun x => decide (m ≤ x)) hlen
      · intro x hx
        have := hsLarge x hx
        simp [P] at this
        simp [this.le]
      · intro b hbmem x hx
        simp
        exact hbsSmall b hbmem x hx
    simp [List.filter_append, huFilter, hafter]
  exact ⟨u, s, bs, by simpa [hq] using hp, hsfull, hlen,
    hu, hbsSmall, by rw [hlowShape, hlow]⟩

end

end D5.S3.Combinatorics.ArrowWilfTwelveInverse
