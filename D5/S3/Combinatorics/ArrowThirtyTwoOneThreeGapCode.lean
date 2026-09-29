/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode
   mirror-E: none(waiver:independent-gap-words-of-the-arrow-pattern-32-1-to-3)
   anchors: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps]
   utility: none
   digest: The canonical first-gap construction and extraction are inverse, giving independent avoider words on all selected-value gaps. -/

import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijectionGaps
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeGapCode

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijectionGaps

noncomputable section

/-- A selected set in increasing order, together with its complementary prefix.
The complete edge condition forces each prefix cycle into one value gap. -/
def GapData (n k : ℕ) :=
  {z : List ℕ × List ℕ // z.1.Pairwise (· < ·) ∧ z.1.length = k ∧
    (z.2 ++ z.1).Perm (List.range' 1 n) ∧ ClosedEdges z.2}

/-- Insert the first selected letter after a gap of length `i`, translating the
remaining selected letters and gap words upwards by `i + 1`. -/
def joinGap (n k : ℕ) :
    (Σ i : Fin (n + 1), avoiders i.val [3, 2] [(1, 3)] 3 ×
      GapData (n - i.val + k) k) → GapData (n + k + 1) (k + 1) := by
  have edgeCriterion (n : ℕ) (p : List ℕ) :
      p ∈ avoiders n [3, 2] [(1, 3)] 3 ↔
        p.Perm (List.range' 1 n) ∧
          ∀ a c : ℕ, a ∈ p → a < c → c < hat p a →
            [c, hat p a].Sublist p := by
    have hcontains : Contains [3, 2] [(1, 3)] 3 p ↔
        ∃ a c : ℕ, a ∈ p ∧ c ∈ p ∧ a < c ∧ c < hat p a ∧
          [hat p a, c].Sublist p := by
      constructor
      · rintro ⟨x, hxlt, hxmem, hxsub, hxhat⟩
        refine ⟨x 1, x 2, hxmem 1 (by omega) (by omega),
          hxmem 2 (by omega) (by omega),
          hxlt 1 (by omega) (by omega), ?_, ?_⟩
        · rw [hxhat (1, 3) (by simp)]
          exact hxlt 2 (by omega) (by omega)
        · simpa [hxhat (1, 3) (by simp)] using hxsub
      · rintro ⟨a, c, ha, hc, hac, hcb, hsub⟩
        let x : ℕ → ℕ := fun i => if i = 1 then a else if i = 2 then c else hat p a
        refine ⟨x, ?_, ?_, ?_, ?_⟩
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 := by omega
          rcases hi_cases with rfl | rfl <;> simp [x, hac, hcb]
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases hi_cases with rfl | rfl | rfl
          · simpa [x] using ha
          · simpa [x] using hc
          · exact hsub.subset (by simp [x])
        · simpa [x] using hsub
        · intro bc hbc
          simp only [List.mem_singleton] at hbc
          subst bc
          simp [x]
    constructor
    · intro hp
      have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
      refine ⟨hp.1, ?_⟩
      intro a c ha hac hcb
      have hb : hat p a ∈ p := by
        change (if p.idxOf a + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf a + 1)
          then p.getD (p.idxOf a + 1) 0
          else p.getD (Nat.findGreatest (IsLtrMax p) (p.idxOf a)) 0) ∈ p
        split_ifs with hbranch
        · rw [List.getD_eq_getElem (l := p) 0 hbranch.1]
          exact List.getElem_mem hbranch.1
        · have hi : p.idxOf a < p.length := List.idxOf_lt_length_of_mem ha
          have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf a) < p.length :=
            lt_of_le_of_lt (Nat.findGreatest_le _) hi
          rw [List.getD_eq_getElem (l := p) 0 hg]
          exact List.getElem_mem hg
      have hc : c ∈ p := by
        have hra : a ∈ List.range' 1 n := hp.1.mem_iff.mp ha
        have hrb : hat p a ∈ List.range' 1 n := hp.1.mem_iff.mp hb
        have ha1 : 1 ≤ a := List.left_le_of_mem_range' hra
        rcases List.mem_range'.mp hrb with ⟨j, hj, hjb⟩
        apply hp.1.mem_iff.mpr
        apply List.mem_range'.mpr
        refine ⟨c - 1, ?_, ?_⟩ <;> omega
      rcases pair_sublist_total hnd (Nat.ne_of_lt hcb) hc hb with h | h
      · exact h
      · exact (hp.2 (hcontains.mpr ⟨a, c, ha, hc, hac, hcb, h⟩)).elim
    · rintro ⟨hperm, hedge⟩
      refine ⟨hperm, ?_⟩
      intro h
      rcases hcontains.mp h with ⟨a, c, ha, hc, hac, hcb, hbad⟩
      have hnd : p.Nodup := hperm.nodup_iff.mpr List.nodup_range'
      exact pair_sublist_asymm hnd (Nat.ne_of_lt hcb)
        ⟨hedge a c ha hac hcb, hbad⟩
  intro z
  let i := z.1
  let L := z.2.1.val
  let T := z.2.2.val.1
  let R := z.2.2.val.2
  have hL := z.2.1.property
  have hsort := z.2.2.property.1
  have hlen := z.2.2.property.2.1
  have hperm := z.2.2.property.2.2.1
  have hedge := z.2.2.property.2.2.2
  let s := i.val + 1
  let f : ℕ → ℕ := fun x => s + x
  have hf : StrictMono f := by intro a b h; dsimp [f]; omega
  have hpos (x : ℕ) (hx : x ∈ R ++ T) : 1 ≤ x :=
    List.left_le_of_mem_range' (hperm.mem_iff.mp hx)
  have hLbound (x : ℕ) (hx : x ∈ L) : x < s := by
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hL.1.mem_iff.mp hx)
    dsimp [s]; omega
  refine ⟨⟨s :: T.map f, L ++ R.map f⟩, ?_, ?_, ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hpos y (List.mem_append.mpr (Or.inr hy))
      dsimp [f]; omega
    · exact hsort.map f (fun _ _ h => hf h)
  · simp only [List.length_cons, List.length_map]
    exact congrArg (· + 1) hlen
  · have hmove : ((L ++ R.map f) ++ (s :: T.map f)).Perm
        (L ++ s :: ((R ++ T).map f)) := by
      simp only [List.append_assoc, List.map_append]
      exact List.Perm.append_left L List.perm_middle
    have hrest := hperm.map f
    have hmain := hL.1.append_cons s hrest
    have hrange : List.range' 1 i.val ++ s :: (List.range' 1 (n - i.val + k)).map f =
        List.range' 1 (n + k + 1) := by
      rw [List.map_add_range']
      change List.range' 1 i.val ++ List.range' s (n - i.val + k + 1) = _
      have hs : s = 1 + i.val := by dsimp [s]; omega
      rw [hs, List.range'_append_1]
      congr 1
      have := i.isLt
      omega
    exact hmove.trans (hrange ▸ hmain)
  · apply (closedEdges_append_ordered L (R.map f) ?_).mpr
    · exact ⟨(edgeCriterion i.val L).mp hL |>.2,
        (closedEdges_translate R s).mpr hedge⟩
    · intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
      have := hpos x (List.mem_append.mpr (Or.inl hx))
      have := hLbound a ha
      dsimp [f]; omega

/-- The first gap is recovered by filtering below the first selected letter;
the upper words are recovered by filtering above it and subtracting its value. -/
theorem joinGap_bijective (n k : ℕ) : Function.Bijective (joinGap n k) := by
  have edgeCriterion (n : ℕ) (p : List ℕ) :
      p ∈ avoiders n [3, 2] [(1, 3)] 3 ↔
        p.Perm (List.range' 1 n) ∧
          ∀ a c : ℕ, a ∈ p → a < c → c < hat p a →
            [c, hat p a].Sublist p := by
    have hcontains : Contains [3, 2] [(1, 3)] 3 p ↔
        ∃ a c : ℕ, a ∈ p ∧ c ∈ p ∧ a < c ∧ c < hat p a ∧
          [hat p a, c].Sublist p := by
      constructor
      · rintro ⟨x, hxlt, hxmem, hxsub, hxhat⟩
        refine ⟨x 1, x 2, hxmem 1 (by omega) (by omega),
          hxmem 2 (by omega) (by omega),
          hxlt 1 (by omega) (by omega), ?_, ?_⟩
        · rw [hxhat (1, 3) (by simp)]
          exact hxlt 2 (by omega) (by omega)
        · simpa [hxhat (1, 3) (by simp)] using hxsub
      · rintro ⟨a, c, ha, hc, hac, hcb, hsub⟩
        let x : ℕ → ℕ := fun i => if i = 1 then a else if i = 2 then c else hat p a
        refine ⟨x, ?_, ?_, ?_, ?_⟩
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 := by omega
          rcases hi_cases with rfl | rfl <;> simp [x, hac, hcb]
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases hi_cases with rfl | rfl | rfl
          · simpa [x] using ha
          · simpa [x] using hc
          · exact hsub.subset (by simp [x])
        · simpa [x] using hsub
        · intro bc hbc
          simp only [List.mem_singleton] at hbc
          subst bc
          simp [x]
    constructor
    · intro hp
      have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
      refine ⟨hp.1, ?_⟩
      intro a c ha hac hcb
      have hb : hat p a ∈ p := by
        change (if p.idxOf a + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf a + 1)
          then p.getD (p.idxOf a + 1) 0
          else p.getD (Nat.findGreatest (IsLtrMax p) (p.idxOf a)) 0) ∈ p
        split_ifs with hbranch
        · rw [List.getD_eq_getElem (l := p) 0 hbranch.1]
          exact List.getElem_mem hbranch.1
        · have hi : p.idxOf a < p.length := List.idxOf_lt_length_of_mem ha
          have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf a) < p.length :=
            lt_of_le_of_lt (Nat.findGreatest_le _) hi
          rw [List.getD_eq_getElem (l := p) 0 hg]
          exact List.getElem_mem hg
      have hc : c ∈ p := by
        have hra : a ∈ List.range' 1 n := hp.1.mem_iff.mp ha
        have hrb : hat p a ∈ List.range' 1 n := hp.1.mem_iff.mp hb
        have ha1 : 1 ≤ a := List.left_le_of_mem_range' hra
        rcases List.mem_range'.mp hrb with ⟨j, hj, hjb⟩
        apply hp.1.mem_iff.mpr
        apply List.mem_range'.mpr
        refine ⟨c - 1, ?_, ?_⟩ <;> omega
      rcases pair_sublist_total hnd (Nat.ne_of_lt hcb) hc hb with h | h
      · exact h
      · exact (hp.2 (hcontains.mpr ⟨a, c, ha, hc, hac, hcb, h⟩)).elim
    · rintro ⟨hperm, hedge⟩
      refine ⟨hperm, ?_⟩
      intro h
      rcases hcontains.mp h with ⟨a, c, ha, hc, hac, hcb, hbad⟩
      have hnd : p.Nodup := hperm.nodup_iff.mpr List.nodup_range'
      exact pair_sublist_asymm hnd (Nat.ne_of_lt hcb)
        ⟨hedge a c ha hac hcb, hbad⟩
  classical
  have hLlen (i : Fin (n + 1)) (L : avoiders i.val [3, 2] [(1, 3)] 3) :
      L.val.length = i.val := by simpa using L.property.1.length_eq
  have hLsmall (i : Fin (n + 1)) (L : avoiders i.val [3, 2] [(1, 3)] 3) :
      ∀ x ∈ L.val, x < i.val + 1 := by
    intro x hx
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (L.property.1.mem_iff.mp hx)
    omega
  have hRlarge (i : Fin (n + 1)) (d : GapData (n - i.val + k) k) :
      ∀ x ∈ d.val.2.map (fun x => i.val + 1 + x), i.val + 1 < x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hpos := List.left_le_of_mem_range'
      (d.property.2.2.1.mem_iff.mp (List.mem_append.mpr (Or.inl hy)))
    omega
  constructor
  · intro z z' heq
    obtain ⟨i, L, d⟩ := z
    obtain ⟨j, L', d'⟩ := z'
    have hs := congrArg (fun z : GapData (n + k + 1) (k + 1) => z.val.1.headD 0) heq
    change i.val + 1 = j.val + 1 at hs
    have hij : i = j := Fin.ext (by omega)
    subst j
    have hpre := congrArg (fun z : GapData (n + k + 1) (k + 1) => z.val.2) heq
    change L.val ++ d.val.2.map (fun x => i.val + 1 + x) =
      L'.val ++ d'.val.2.map (fun x => i.val + 1 + x) at hpre
    have hLL : L = L' := by
      apply Subtype.ext
      have h := congrArg (List.take i.val) hpre
      simpa [hLlen] using h
    subst L'
    have hR : d.val.2 = d'.val.2 :=
      (List.map_injective_iff.mpr (show Function.Injective (fun x : ℕ => i.val + 1 + x) by
        intro a b h; dsimp at h; omega)) (List.append_cancel_left hpre)
    have hT := congrArg (fun z : GapData (n + k + 1) (k + 1) => z.val.1.tail) heq
    change d.val.1.map (fun x => i.val + 1 + x) =
      d'.val.1.map (fun x => i.val + 1 + x) at hT
    have hTT : d.val.1 = d'.val.1 :=
      (List.map_injective_iff.mpr (show Function.Injective (fun x : ℕ => i.val + 1 + x) by
        intro a b h; dsimp at h; omega)) hT
    have hdd : d = d' := Subtype.ext (Prod.ext hTT hR)
    subst d'
    rfl
  · rintro ⟨⟨S, p⟩, hsort, hlen, hperm, hedge⟩
    cases S with
    | nil => simp at hlen
    | cons s T =>
        have hnd : (p ++ s :: T).Nodup := hperm.nodup_iff.mpr List.nodup_range'
        have hpnd := hnd.of_append_left
        have hsnot : s ∉ p := fun h => (List.nodup_append'.mp hnd).2.2 h (by simp)
        have hTlarge : ∀ x ∈ T, s < x := (List.pairwise_cons.mp hsort).1
        have hsrange : s ∈ List.range' 1 (n + k + 1) :=
          hperm.mem_iff.mp (by simp)
        have hspos := List.left_le_of_mem_range' hsrange
        have hsle : s ≤ n + k + 1 := by
          obtain ⟨j, hj, heq⟩ := List.mem_range'.mp hsrange
          omega
        let L := p.filter (fun x => x < s)
        let H := p.filter (fun x => s < x)
        let Q := H.map (fun x => x - s)
        let U := T.map (fun x => x - s)
        have hsplit : p = L ++ H := closedEdges_value_cut p s hpnd hsnot hedge
        have hLmem : ∀ x, x ∈ L ↔ 1 ≤ x ∧ x < s := by
          intro x
          constructor
          · intro hx
            obtain ⟨hxp, hxs⟩ := List.mem_filter.mp hx
            exact ⟨List.left_le_of_mem_range' (hperm.mem_iff.mp
              (List.mem_append.mpr (Or.inl hxp))), by simpa using hxs⟩
          · rintro ⟨hxpos, hxs⟩
            have hxrange : x ∈ List.range' 1 (n + k + 1) := by
              apply List.mem_range'.mpr
              exact ⟨x - 1, by omega, by omega⟩
            have hxp : x ∈ p := by
              rcases List.mem_append.mp (hperm.mem_iff.mpr hxrange) with h | h
              · exact h
              · rcases List.mem_cons.mp h with rfl | h
                · omega
                · have := hTlarge x h; omega
            exact List.mem_filter.mpr ⟨hxp, by simpa using hxs⟩
        have hLperm : L.Perm (List.range' 1 (s - 1)) := by
          apply (List.perm_ext_iff_of_nodup (hpnd.filter _) List.nodup_range').mpr
          intro x
          rw [hLmem]
          constructor
          · rintro ⟨h1, h2⟩; exact List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
          · intro h; obtain ⟨j, hj, heq⟩ := List.mem_range'.mp h; omega
        have hLlength : L.length = s - 1 := by simpa using hLperm.length_eq
        have hpLength : p.length + (k + 1) = n + k + 1 := by
          simpa [hlen] using hperm.length_eq
        have hi : s - 1 < n + 1 := by
          have hle := List.length_filter_le (fun x => decide (x < s)) p
          change L.length ≤ p.length at hle
          omega
        let i : Fin (n + 1) := ⟨s - 1, hi⟩
        have hsi : i.val + 1 = s := by dsimp [i]; omega
        have horder : ∀ a ∈ L, ∀ b ∈ H, a < b := by
          intro a ha b hb
          have ha' := (hLmem a).mp ha
          have hb' : s < b := by simpa using (List.mem_filter.mp hb).2
          omega
        have hparts : ClosedEdges L ∧ ClosedEdges H :=
          (closedEdges_append_ordered L H horder).mp (hsplit ▸ hedge)
        have hLavoid : L ∈ avoiders i.val [3, 2] [(1, 3)] 3 :=
          (edgeCriterion i.val L).mpr ⟨hLperm, hparts.1⟩
        have hHlarge : ∀ x ∈ H, s < x := by
          intro x hx; simpa using (List.mem_filter.mp hx).2
        have hmapH : Q.map (fun x => s + x) = H := by
          simp only [Q, List.map_map]
          calc
            _ = H.map id := List.map_congr_left (fun x hx => by
              dsimp; have := hHlarge x hx; omega)
            _ = H := List.map_id H
        have hmapT : U.map (fun x => s + x) = T := by
          simp only [U, List.map_map]
          calc
            _ = T.map id := List.map_congr_left (fun x hx => by
              dsimp; have := hTlarge x hx; omega)
            _ = T := List.map_id T
        have hQUnd : (Q ++ U).Nodup := by
          have hHTnd : (H ++ T).Nodup := by
            apply (List.nodup_append'.mpr ⟨hpnd.filter _,
              hnd.of_append_right.of_cons, ?_⟩)
            intro x hxH hxT
            exact (List.nodup_append'.mp hnd).2.2 (List.mem_filter.mp hxH).1 (by simp [hxT])
          have hmap : (Q ++ U).map (fun x => s + x) = H ++ T := by
            rw [List.map_append, hmapH, hmapT]
          exact (List.nodup_map_iff (show Function.Injective (fun x : ℕ => s + x) by
            intro a b h; dsimp at h; omega)).mp (hmap.symm ▸ hHTnd)
        have hQUperm : (Q ++ U).Perm (List.range' 1 (n - i.val + k)) := by
          apply (List.perm_ext_iff_of_nodup hQUnd List.nodup_range').mpr
          intro x
          have hmemQU : x ∈ Q ++ U ↔ s + x ∈ H ++ T := by
            have hmap : (Q ++ U).map (fun x => s + x) = H ++ T := by
              rw [List.map_append, hmapH, hmapT]
            rw [← hmap, List.mem_map]
            constructor
            · intro hx; exact ⟨x, hx, rfl⟩
            · rintro ⟨y, hy, heq⟩
              have hyx : y = x := by omega
              simpa [hyx] using hy
          rw [hmemQU]
          constructor
          · intro hx
            have hlarge : s < s + x := by
              rcases List.mem_append.mp hx with hx | hx
              · exact hHlarge _ hx
              · exact hTlarge _ hx
            have hrange : s + x ∈ List.range' 1 (n + k + 1) := by
              apply hperm.mem_iff.mp
              rcases List.mem_append.mp hx with hx | hx
              · exact List.mem_append.mpr (Or.inl (List.mem_filter.mp hx).1)
              · exact List.mem_append.mpr (Or.inr (by simp [hx]))
            obtain ⟨j, hj, heq⟩ := List.mem_range'.mp hrange
            apply List.mem_range'.mpr
            refine ⟨x - 1, ?_, ?_⟩ <;> have := i.isLt <;> omega
          · intro hx
            obtain ⟨j, hj, heq⟩ := List.mem_range'.mp hx
            have hlarge : s < s + x := by omega
            have hrange : s + x ∈ List.range' 1 (n + k + 1) := by
              apply List.mem_range'.mpr
              exact ⟨s + x - 1, by have := i.isLt; omega, by omega⟩
            rcases List.mem_append.mp (hperm.mem_iff.mpr hrange) with hx | hx
            · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hx, by simpa using hlarge⟩))
            · rcases List.mem_cons.mp hx with hx | hx
              · omega
              · exact List.mem_append.mpr (Or.inr hx)
        have hUsort : U.Pairwise (· < ·) := by
          apply List.pairwise_map.mpr
          exact (List.pairwise_cons.mp hsort).2.imp_of_mem
            (fun {a b} ha hb hab => by
              have := hTlarge a ha
              have := hTlarge b hb
              omega)
        have hQedge : ClosedEdges Q :=
          (closedEdges_translate Q s).mp (hmapH.symm ▸ hparts.2)
        let d : GapData (n - i.val + k) k :=
          ⟨⟨U, Q⟩, hUsort, by simpa [U] using hlen, hQUperm, hQedge⟩
        refine ⟨⟨i, ⟨L, hLavoid⟩, d⟩, ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · change (i.val + 1) :: U.map (fun x => i.val + 1 + x) = s :: T
          rw [hsi, hmapT]
        · change L ++ Q.map (fun x => i.val + 1 + x) = p
          rw [hsi, hmapH, ← hsplit]

/-- Summing independent translated gap words gives exactly the coefficient of
the corresponding power of the avoider series. -/
theorem gapData_card (n k : ℕ) :
    (Nat.card (GapData (n + k) k) : ℤ) = PowerSeries.coeff n (series ^ (k + 1)) := by
  have edgeCriterion (n : ℕ) (p : List ℕ) :
      p ∈ avoiders n [3, 2] [(1, 3)] 3 ↔
        p.Perm (List.range' 1 n) ∧
          ∀ a c : ℕ, a ∈ p → a < c → c < hat p a →
            [c, hat p a].Sublist p := by
    have hcontains : Contains [3, 2] [(1, 3)] 3 p ↔
        ∃ a c : ℕ, a ∈ p ∧ c ∈ p ∧ a < c ∧ c < hat p a ∧
          [hat p a, c].Sublist p := by
      constructor
      · rintro ⟨x, hxlt, hxmem, hxsub, hxhat⟩
        refine ⟨x 1, x 2, hxmem 1 (by omega) (by omega),
          hxmem 2 (by omega) (by omega),
          hxlt 1 (by omega) (by omega), ?_, ?_⟩
        · rw [hxhat (1, 3) (by simp)]
          exact hxlt 2 (by omega) (by omega)
        · simpa [hxhat (1, 3) (by simp)] using hxsub
      · rintro ⟨a, c, ha, hc, hac, hcb, hsub⟩
        let x : ℕ → ℕ := fun i => if i = 1 then a else if i = 2 then c else hat p a
        refine ⟨x, ?_, ?_, ?_, ?_⟩
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 := by omega
          rcases hi_cases with rfl | rfl <;> simp [x, hac, hcb]
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases hi_cases with rfl | rfl | rfl
          · simpa [x] using ha
          · simpa [x] using hc
          · exact hsub.subset (by simp [x])
        · simpa [x] using hsub
        · intro bc hbc
          simp only [List.mem_singleton] at hbc
          subst bc
          simp [x]
    constructor
    · intro hp
      have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
      refine ⟨hp.1, ?_⟩
      intro a c ha hac hcb
      have hb : hat p a ∈ p := by
        change (if p.idxOf a + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf a + 1)
          then p.getD (p.idxOf a + 1) 0
          else p.getD (Nat.findGreatest (IsLtrMax p) (p.idxOf a)) 0) ∈ p
        split_ifs with hbranch
        · rw [List.getD_eq_getElem (l := p) 0 hbranch.1]
          exact List.getElem_mem hbranch.1
        · have hi : p.idxOf a < p.length := List.idxOf_lt_length_of_mem ha
          have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf a) < p.length :=
            lt_of_le_of_lt (Nat.findGreatest_le _) hi
          rw [List.getD_eq_getElem (l := p) 0 hg]
          exact List.getElem_mem hg
      have hc : c ∈ p := by
        have hra : a ∈ List.range' 1 n := hp.1.mem_iff.mp ha
        have hrb : hat p a ∈ List.range' 1 n := hp.1.mem_iff.mp hb
        have ha1 : 1 ≤ a := List.left_le_of_mem_range' hra
        rcases List.mem_range'.mp hrb with ⟨j, hj, hjb⟩
        apply hp.1.mem_iff.mpr
        apply List.mem_range'.mpr
        refine ⟨c - 1, ?_, ?_⟩ <;> omega
      rcases pair_sublist_total hnd (Nat.ne_of_lt hcb) hc hb with h | h
      · exact h
      · exact (hp.2 (hcontains.mpr ⟨a, c, ha, hc, hac, hcb, h⟩)).elim
    · rintro ⟨hperm, hedge⟩
      refine ⟨hperm, ?_⟩
      intro h
      rcases hcontains.mp h with ⟨a, c, ha, hc, hac, hcb, hbad⟩
      have hnd : p.Nodup := hperm.nodup_iff.mpr List.nodup_range'
      exact pair_sublist_asymm hnd (Nat.ne_of_lt hcb)
        ⟨hedge a c ha hac hcb, hbad⟩
  classical
  have (m j : ℕ) : Finite (GapData m j) := by
    let Perms := {p : List ℕ // p.Perm (List.range' 1 m)}
    have hfinite : {p : List ℕ | p.Perm (List.range' 1 m)}.Finite := by
      apply (List.permutations (List.range' 1 m)).finite_toSet.subset
      intro p hp
      exact List.mem_permutations.mpr hp
    have : Finite Perms := hfinite.to_subtype
    let f : GapData m j → Perms := fun d => ⟨d.val.2 ++ d.val.1, d.property.2.2.1⟩
    apply Finite.of_injective f
    intro a b hab
    have hlen (d : GapData m j) : d.val.2.length = m - j := by
      have h := d.property.2.2.1.length_eq
      simp only [List.length_append, List.length_range', d.property.2.1] at h
      omega
    have hw : a.val.2 ++ a.val.1 = b.val.2 ++ b.val.1 := congrArg Subtype.val hab
    have hpre : a.val.2 = b.val.2 := by
      have h := congrArg (List.take (m - j)) hw
      simpa [hlen] using h
    have hsel : a.val.1 = b.val.1 := by
      rw [hpre] at hw
      exact List.append_cancel_left hw
    exact Subtype.ext (Prod.ext hsel hpre)
  have (m : ℕ) : Finite (avoiders m [3, 2] [(1, 3)] 3) := by
    have hfinite : (avoiders m [3, 2] [(1, 3)] 3).Finite := by
      apply (List.permutations (List.range' 1 m)).finite_toSet.subset
      intro p hp
      exact List.mem_permutations.mpr hp.1
    exact hfinite.to_subtype
  induction k generalizing n with
  | zero =>
      let f : avoiders n [3, 2] [(1, 3)] 3 → GapData (n + 0) 0 := fun p =>
        ⟨⟨[], p.val⟩, by simp, rfl, by simpa using p.property.1,
          (edgeCriterion n p.val).mp p.property |>.2⟩
      have hinj : Function.Injective f := by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun d : GapData (n + 0) 0 => d.val.2) hpq
      have hsurj : Function.Surjective f := by
        rintro ⟨⟨S, p⟩, hs, hlen, hperm, hedge⟩
        have hS : S = [] := List.eq_nil_of_length_eq_zero hlen
        subst S
        have hp : p ∈ avoiders n [3, 2] [(1, 3)] 3 :=
          (edgeCriterion n p).mpr ⟨by simpa using hperm, hedge⟩
        exact ⟨⟨p, hp⟩, rfl⟩
      rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_coe_set_eq]
      simp [series, count]
  | succ k ih =>
      have hcard : Nat.card (GapData (n + (k + 1)) (k + 1)) =
          ∑ i : Fin (n + 1), count i.val * Nat.card (GapData (n - i.val + k) k) := by
        have e := Equiv.ofBijective (joinGap n k) (joinGap_bijective n k)
        have h := Nat.card_congr e
        rw [Nat.card_sigma] at h
        simp only [Nat.card_prod, Nat.card_coe_set_eq] at h
        simpa [Nat.add_assoc, count] using h.symm
      rw [hcard, Nat.cast_sum]
      simp_rw [Nat.cast_mul, ih]
      conv_rhs => rw [show k + 1 + 1 = 1 + (k + 1) by omega, pow_add, pow_one,
        PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [series]

end
end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeGapCode

#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeGapCode.gapData_card
