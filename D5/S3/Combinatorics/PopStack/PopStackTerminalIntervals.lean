/- GID: D5/S3/Combinatorics/PopStack/PopStackTerminalIntervals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackTerminalIntervals
   mirror-E: none(waiver:terminal-family-intervals)
   anchors: []
   utility: none
   digest: The terminal family has only its proper prefix and its exceptional upper bond. -/
import D5.S3.Combinatorics.PopStack.PopStackTerminalGap
import D5.S3.Combinatorics.PopStack.PopStackMinimum
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.PopStack.PopStackTerminalIntervals
open PopStackDefs PopStackChains PopStackParallel PopStackExtra PopStackTerminalGap
def Y (size : ℕ) : List ℕ := ((R (size - 1)).map Nat.succ).insertIdx 2 1
theorem terminal_family_intervals (size : ℕ) (hsize : 4 ≤ size) :
    (R size).Perm (List.range' 1 size) ∧ InC (R size) ∧ (R size).length = size ∧
      (R size).getD (size - 1) 0 = 1 ∧
      (∀ start count lower, 2 ≤ count → count < size → start + count ≤ size →
        ((((R size).drop start).take count).Perm (List.range' lower count) ↔
          (start = 0 ∧ count = size - 1 ∧ lower = 2) ∨
          (size % 2 = 0 ∧ start = 1 ∧ count = 2 ∧ lower = size - 1))) ∧
      Y (size + 1) ∈ simples (size + 1) := by
  have minimum_insertion_simple (permutation : List ℕ)
      (hpositive : ∀ value ∈ permutation, 1 ≤ value)
      (gap : ℕ) (hinterior : 0 < gap ∧ gap < permutation.length) :
      (∀ index size lower, 2 ≤ size → size < permutation.length →
        index + size ≤ permutation.length →
        ((permutation.drop index).take size).Perm (List.range' lower size) →
        index < gap ∧ gap < index + size ∧ 2 ≤ lower) ∧
      permutation.getD (gap - 1) 0 ≠ 1 ∧ permutation.getD gap 0 ≠ 1 →
      IsSimple ((permutation.map Nat.succ).insertIdx gap 1) := by
    let expanded := (permutation.map Nat.succ).insertIdx gap 1
    have hlength : expanded.length = permutation.length + 1 := by
      simp [expanded, List.length_insertIdx, hinterior.2.le]
    have hsegments : ∀ index size, index + size ≤ expanded.length →
        ((expanded.drop index).take size) =
          if index + size ≤ gap then ((permutation.drop index).take size).map Nat.succ
          else if gap < index then ((permutation.drop (index - 1)).take size).map Nat.succ
          else (((permutation.drop index).take (size - 1)).map Nat.succ).insertIdx
            (gap - index) 1 := by
      intro index size hbound
      rw [hlength] at hbound
      split_ifs with hbefore hafter <;> apply List.ext_getElem? <;> intro offset
      all_goals
        simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_map,
          expanded, List.getElem?_insertIdx, List.length_map, List.length_take,
          List.length_drop]
        split_ifs <;> first | rfl | (congr 2 <;> omega) | omega
    have hpredRange : ∀ lower size, 1 ≤ lower →
        (List.range' lower size).map Nat.pred = List.range' (lower - 1) size := by
      intro lower size hlower
      simpa only [← Nat.pred_eq_sub_one] using (List.map_sub_range' hlower size)
    have hpredSucc : ∀ segment : List ℕ, (segment.map Nat.succ).map Nat.pred = segment := by
      intro segment; simp [List.map_map, Function.comp_def]
    have hget : ∀ index, permutation.getD index 0 = 1 ↔
        ((permutation.drop index).take 1) = [1] := by
      intro index
      simp only [List.take_one, List.head?_eq_getElem?, List.getElem?_drop,
        List.getD_eq_getElem?_getD]
      cases permutation[index]? <;> simp
    rintro ⟨hintervals, hleft, hright⟩ index size lower hsize hproper hbound hperm
    change ((expanded.drop index).take size).Perm (List.range' lower size) at hperm
    change size < expanded.length at hproper; change index + size ≤ expanded.length at hbound
    have hpositiveNew : ∀ value ∈ expanded, 1 ≤ value := by
      intro value hmem; rw [List.mem_insertIdx (show gap ≤ (permutation.map Nat.succ).length by
        simpa using hinterior.2.le)] at hmem
      rcases hmem with heq | hmem
      · omega
      · obtain ⟨old, _, rfl⟩ := List.mem_map.mp hmem; omega
    have hlower : 1 ≤ lower := by
      have hm : lower ∈ List.range' lower size := List.mem_range'_1.mpr ⟨by omega, by omega⟩
      exact hpositiveNew lower
        (List.mem_of_mem_drop (List.mem_of_mem_take (hperm.mem_iff.mpr hm)))
    by_cases hbefore : index + size ≤ gap
    · rw [hsegments index size hbound, if_pos hbefore] at hperm
      have hold : ((permutation.drop index).take size).Perm (List.range' (lower - 1) size) := by
        simpa only [hpredSucc, hpredRange lower size hlower] using hperm.map Nat.pred
      have hh := hintervals index size (lower - 1) hsize (by omega) (by omega) hold; omega
    · by_cases hafter : gap < index
      · rw [hsegments index size hbound, if_neg hbefore, if_pos hafter] at hperm
        have hold : ((permutation.drop (index - 1)).take size).Perm
            (List.range' (lower - 1) size) := by
          simpa only [hpredSucc, hpredRange lower size hlower] using hperm.map Nat.pred
        have hh := hintervals (index - 1) size (lower - 1) hsize
          (by rw [hlength] at hbound; omega) (by rw [hlength] at hbound; omega) hold
        omega
      · rw [hsegments index size hbound, if_neg hbefore, if_neg hafter] at hperm
        have hinsert : gap - index ≤
            (((permutation.drop index).take (size - 1)).map Nat.succ).length := by
          simp only [List.length_map, List.length_take, List.length_drop]; rw [hlength] at hbound
          omega
        have hone : 1 ∈ List.range' lower size := hperm.mem_iff.mp
          ((List.mem_insertIdx hinsert).mpr (Or.inl rfl))
        have heq : lower = 1 := by have hh := List.mem_range'_1.mp hone; omega
        subst lower; have hshift : (((permutation.drop index).take (size - 1)).map Nat.succ).Perm
            (List.range' 2 (size - 1)) := by
          have hh := (List.perm_insertIdx _ _ hinsert).symm.trans hperm
          rw [show size = (size - 1) + 1 by omega, List.range'_succ] at hh; exact hh.cons_inv
        have hold : ((permutation.drop index).take (size - 1)).Perm
            (List.range' 1 (size - 1)) := by
          simpa only [hpredSucc, hpredRange 2 (size - 1) (by omega)] using hshift.map Nat.pred
        by_cases hlong : 3 ≤ size
        · have hh := hintervals index (size - 1) 1 (by omega)
            (by rw [hlength] at hproper; omega) (by rw [hlength] at hbound; omega) hold
          omega
        · have heq : size = 2 := by omega
          subst size; have hsingle : ((permutation.drop index).take 1) = [1] := by
            simpa only [show 2 - 1 = 1 by omega, List.range'_succ, List.range'_zero]
              using List.perm_singleton.mp hold
          have hv := (hget index).mpr hsingle
          by_cases hsame : index = gap
          · subst index; exact hright hv
          · have heq : index = gap - 1 := by omega
            subst index; exact hleft hv
  classical
  have hcore : (R size).Perm (List.range' 1 size) ∧ InC (R size) ∧
      (R size).length = size ∧ (R size).getD (size - 1) 0 = 1 ∧
      (∀ start count lower, 2 ≤ count → count < size → start + count ≤ size →
        ((((R size).drop start).take count).Perm (List.range' lower count) ↔
          (start = 0 ∧ count = size - 1 ∧ lower = 2) ∨
          (size % 2 = 0 ∧ start = 1 ∧ count = 2 ∧ lower = size - 1))) := by
    by_cases hodd : size % 2 = 1
    · have hh : 2 ≤ size / 2 := by omega
      obtain ⟨hp, hc, _, hi⟩ := odd_extra (size / 2) (by omega)
      have heq : 2 * (size / 2) + 1 = size := by omega
      have hr : R size = E (size / 2) := by rw [R, if_pos hodd]
      have hl : (R size).length = size := by
        simp only [hr, E, P, List.length_append, List.length_map, List.length_ofFn,
          List.length_cons, List.length_nil, heq]
      refine ⟨by simpa only [hr, heq] using hp, hr ▸ hc, hl, ?_, ?_⟩
      · rw [hr]
        have hindex : size - 1 = (P (size / 2)).length := by simp only [P, List.length_ofFn]; omega
        simp [E, hindex]
      · intro start count lower hcount hproper hbound
        simpa only [hr, heq, show size - 1 = 2 * (size / 2) by omega,
          show size % 2 ≠ 0 by omega, false_and, or_false] using
          hi start count lower hcount (by simpa only [← hr, hl] using hproper)
            (by simpa only [← hr, hl] using hbound)
    · have heven : size % 2 = 0 := by omega
      let half := size / 2; have hhalf : 2 ≤ half := by dsimp only [half]; omega
      have hsizeHalf : size = 2 * half := (by dsimp only [half]; omega); let entry := fun index =>
        if index = 0 then half else if index = 1 then size
        else if index % 2 = 0 then size - index / 2 else half - index / 2
      have hlength : (R size).length = size := by simp only [R, if_neg hodd, List.length_ofFn]
      have hget : ∀ index, index < size → (R size).getD index 0 = entry index := by
        intro index hindex; rw [List.getD_eq_getElem _ _ (by omega)]
        simp only [R, if_neg hodd, List.getElem_ofFn, entry, half]
      have hbounds : ∀ index, index < size → 1 ≤ entry index ∧ entry index ≤ size := by
        intro index hindex; dsimp only [entry]
        split_ifs <;> omega
      have hinjective : ∀ first second, first < size → second < size →
          entry first = entry second → first = second := by
        intro first second hfirst hsecond heq; dsimp only [entry] at heq
        split_ifs at heq <;> omega
      have hnodup : (R size).Nodup := by
        apply List.nodup_iff_injective_get.mpr; intro first second heq; apply Fin.ext
        apply hinjective first.val second.val (by omega) (by omega)
        rw [← hget first.val (by omega), ← hget second.val (by omega)]
        simpa only [List.getD_eq_getElem _ _ first.isLt,
          List.getD_eq_getElem _ _ second.isLt, List.get_eq_getElem] using heq
      have hmem : ∀ value, value ∈ R size ↔ 1 ≤ value ∧ value ≤ size := by
        intro value
        constructor
        · intro hv
          obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp hv; have hh := hbounds index (by omega)
          rw [← List.getD_eq_getElem _ _ hi, hget index (by omega)] at heq; omega
        · rintro ⟨hpositive, hupper⟩
          have hchoose : ∃ index, index < size ∧ entry index = value := by
            by_cases hlower : value ≤ half
            · by_cases htop : value = half
              · refine ⟨0, by omega, ?_⟩
                simp only [entry, if_pos rfl]; omega
              · refine ⟨2 * (half - value) + 1, by omega, ?_⟩
                have hsub : half - value + value = half := Nat.sub_add_cancel (by omega)
                have hz : 2 * (half - value) + 1 ≠ 0 := by omega
                have ho : 2 * (half - value) + 1 ≠ 1 := by omega
                have hp : (2 * (half - value) + 1) % 2 ≠ 0 := by omega
                have hd : (2 * (half - value) + 1) / 2 = half - value := by omega
                simp only [entry, if_neg hz, if_neg ho, if_neg hp, hd]; omega
            · by_cases htop : value = size
              · refine ⟨1, by omega, ?_⟩
                simpa [entry] using htop.symm
              · refine ⟨2 * (size - value), by omega, ?_⟩
                have hsub : size - value + value = size := Nat.sub_add_cancel hupper
                dsimp only [entry]
                split_ifs <;> omega
          obtain ⟨index, hi, heq⟩ := hchoose; apply List.mem_iff_getElem.mpr
          refine ⟨index, by omega, ?_⟩
          rw [← List.getD_eq_getElem _ _ (by omega), hget index hi, heq]
      have hperm : (R size).Perm (List.range' 1 size) := by
        apply List.perm_ext_iff_of_nodup hnodup (List.nodup_range' _) |>.mpr
        intro value; rw [hmem, List.mem_range'_1]; omega
      have hchain : (R size).Pairwise (fun first second =>
          (first ≤ half ↔ second ≤ half) → second < first) := by
        apply List.pairwise_iff_getElem.mpr; intro first second hf hs horder hsame
        rw [← List.getD_eq_getElem _ _ hf, ← List.getD_eq_getElem _ _ hs,
          hget first (by omega), hget second (by omega)] at hsame ⊢
        have hf' : first < size := (by omega); have hs' : second < size := by omega
        dsimp only [entry] at hsame ⊢
        split_ifs at hsame ⊢ <;> omega
      have hD : InD (R size) := (two_decreasing_chains (R size) hnodup).1.mpr ⟨half, hchain⟩
      have hC : InC (R size) := (two_decreasing_chains (R size) hnodup).2 hD
      have hfirst : entry 0 = half := by simp [entry]
      have hsecond : entry 1 = size := by simp [entry]
      have hpenultimate : entry (size - 2) = half + 1 := by
        dsimp only [entry]
        split_ifs <;> omega
      have hlast : entry (size - 1) = 1 := by
        dsimp only [entry]
        split_ifs <;> omega
      have hsliceMem : ∀ start count, start + count ≤ size →
          ∀ value, value ∈ ((R size).drop start).take count ↔
            ∃ position, start ≤ position ∧ position < start + count ∧ entry position = value := by
        intro start count hbound value
        constructor
        · intro hvalue; obtain ⟨offset, hgetValue⟩ := List.mem_iff_getElem?.mp hvalue
          have hoffset : offset < count := by
            have hh := (List.getElem?_eq_some_iff.mp hgetValue).1
            simp only [List.length_take, List.length_drop, hlength] at hh; omega
          rw [List.getElem?_take_of_lt hoffset, List.getElem?_drop] at hgetValue
          refine ⟨start + offset, by omega, by omega, ?_⟩; rw [← hget (start + offset) (by omega)]
          simp only [List.getD_eq_getElem?_getD, hgetValue, Option.getD_some]
        · rintro ⟨position, hstart, hend, hgetValue⟩
          apply List.mem_iff_getElem?.mpr; refine ⟨position - start, ?_⟩
          rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hstart]
          rw [List.getElem?_eq_getElem (by omega),
            ← List.getD_eq_getElem _ _ (by omega), hget position (by omega), hgetValue]
      have hprefixPerm : ((R size).take (size - 1)).Perm (List.range' 2 (size - 1)) := by
        have htail : (R size).drop (size - 1) = [1] := by
          apply List.ext_getElem
          · simp only [List.length_drop, hlength, List.length_cons, List.length_nil]; omega
          · intro index hl hr
            have hz : index = 0 := by simp only [List.length_singleton] at hr; omega
            subst index; simp only [List.getElem_drop, Nat.add_zero, List.getElem_cons_zero]
            rw [← List.getD_eq_getElem _ _ (by omega), hget (size - 1) (by omega), hlast]
        have hh := hperm
        conv_lhs at hh => rw [← List.take_append_drop (size - 1) (R size), htail]
        have hrange : List.range' 1 size = 1 :: List.range' 2 (size - 1) := by
          conv_lhs => rw [show size = (size - 1) + 1 by omega, List.range'_succ]
        rw [hrange] at hh; exact ((List.perm_append_singleton 1 _).symm.trans hh).cons_inv
      have hpair : ((R size).drop 1).take 2 = [size, size - 1] := by
        apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, hlength, List.length_cons, List.length_nil]
          omega
        · intro index hl hr; have hi : index = 0 ∨ index = 1 := by
            simp only [List.length_cons, List.length_nil] at hr; omega
          rcases hi with rfl | rfl <;>
            simp only [List.getElem_take, List.getElem_drop, List.getElem_cons_zero,
              List.getElem_cons_succ] <;>
            rw [← List.getD_eq_getElem _ _ (by omega), hget _ (by omega)]
          · exact hsecond
          · simp [entry]
      refine ⟨hperm, hC, hlength, by rw [hget _ (by omega), hlast], ?_⟩
      intro start count lower hcount hproper hbound
      constructor
      · intro hinterval
        have hentryBound : ∀ position, start ≤ position → position < start + count →
            lower ≤ entry position ∧ entry position < lower + count := by
          intro position hs he; exact List.mem_range'_1.mp (hinterval.mem_iff.mp
            ((hsliceMem start count hbound _).mpr ⟨position, hs, he, rfl⟩))
        have hstraddles : (start = 1 ∧ count = 2) ∨ (lower ≤ half ∧ half + 1 < lower + count) := by
          by_cases hs : start = 1
          · by_cases hc : count = 2
            · exact Or.inl ⟨hs, hc⟩
            · have hu := hentryBound 1 (by omega) (by omega)
              have hl := hentryBound 3 (by omega) (by omega); rw [hsecond] at hu
              have he : entry 3 = half - 1 := (by simp [entry]); rw [he] at hl
              right; omega
          · have hf := hentryBound start le_rfl (by omega)
            have hn := hentryBound (start + 1) (by omega) (by omega)
            have hside : ∀ index, index < size →
                (entry index ≤ half ↔ index = 0 ∨ (index ≠ 1 ∧ index % 2 = 1)) := by
              intro index hindex; dsimp only [entry]
              split_ifs <;> omega
            have hfSide := hside start (by omega); have hnSide := hside (start + 1) (by omega)
            have ht : ¬ (entry start ≤ half ↔ entry (start + 1) ≤ half) := by omega
            right
            omega
        rcases hstraddles with ⟨hs, hc⟩ | ⟨hlow, hhigh⟩
        · right
          have hm := hentryBound 1 (by omega) (by omega); rw [hsecond, hc] at hm
          have hn := hentryBound 2 (by omega) (by omega)
          have he : entry 2 = size - 1 := by simp [entry]
          rw [he] at hn; exact ⟨heven, hs, hc, by omega⟩
        · have hlowMem : half ∈ ((R size).drop start).take count :=
            hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
          have hhighMem : half + 1 ∈ ((R size).drop start).take count :=
            hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
          obtain ⟨lowPosition, hlowStart, hlowEnd, hlowValue⟩ :=
            (hsliceMem start count hbound half).mp hlowMem
          obtain ⟨highPosition, hhighStart, hhighEnd, hhighValue⟩ :=
            (hsliceMem start count hbound (half + 1)).mp hhighMem
          have hl : lowPosition = 0 := hinjective lowPosition 0 (by omega) (by omega)
            (hlowValue.trans hfirst.symm)
          have hh : highPosition = size - 2 := hinjective highPosition (size - 2)
            (by omega) (by omega) (hhighValue.trans hpenultimate.symm)
          have hs : start = 0 := (by omega); have hc : count = size - 1 := by omega
          have hprefix := hinterval; rw [hs, hc, List.drop_zero] at hprefix
          have htwo := hprefixPerm.mem_iff.mpr
            (show 2 ∈ List.range' 2 (size - 1) from List.mem_range'_1.mpr (by omega))
          have hbottom := List.mem_range'_1.mp (hprefix.mem_iff.mp htwo)
          have hlow' := List.mem_range'_1.mp (hprefixPerm.mem_iff.mp
            (hprefix.mem_iff.mpr (show lower ∈ List.range' lower (size - 1) from
              List.mem_range'_1.mpr (by omega))))
          exact Or.inl ⟨hs, hc, by omega⟩
      · rintro (⟨rfl, rfl, rfl⟩ | ⟨_, rfl, rfl, rfl⟩)
        · simpa only [List.drop_zero] using hprefixPerm
        · rw [hpair]
          simpa only [List.range'_succ, List.range'_zero, show size - 1 + 1 = size by omega] using
            List.Perm.swap (size - 1) size []
  obtain ⟨hperm, hC, hlength, hlast, hintervals⟩ := hcore
  have hpositive : ∀ entry ∈ R size, 1 ≤ entry := by
    intro entry hentry; exact (List.mem_range'_1.mp (hperm.mem_iff.mp hentry)).1
  have hneighbors : (R size).getD 1 0 ≠ 1 ∧ (R size).getD 2 0 ≠ 1 := by
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hinj := List.nodup_iff_injective_get.mp hnodup
    constructor <;> intro heq
    · have hh := hinj (a₁ := ⟨1, by omega⟩) (a₂ := ⟨size - 1, by omega⟩) (by
        simp only [List.get_eq_getElem]; rw [← List.getD_eq_getElem _ 0 (by omega),
          ← List.getD_eq_getElem _ 0 (by omega)]
        exact heq.trans hlast.symm)
      have hh := congrArg Fin.val hh; simp only at hh; omega
    · have hh := hinj (a₁ := ⟨2, by omega⟩) (a₂ := ⟨size - 1, by omega⟩) (by
        simp only [List.get_eq_getElem]; rw [← List.getD_eq_getElem _ 0 (by omega),
          ← List.getD_eq_getElem _ 0 (by omega)]
        exact heq.trans hlast.symm)
      have hh := congrArg Fin.val hh; simp only at hh; omega
  have hsimple : IsSimple (((R size).map Nat.succ).insertIdx 2 1) := by
    apply (minimum_insertion_simple (R size) hpositive 2 ⟨by omega, by omega⟩)
    refine ⟨?_, by simpa using hneighbors.1, hneighbors.2⟩; intro start count lower hc hp hb hi
    rcases (hintervals start count lower hc (by omega) (by omega)).mp hi with
      ⟨rfl, rfl, rfl⟩ | ⟨_, rfl, rfl, rfl⟩ <;> omega
  have hnewC : InC (((R size).map Nat.succ).insertIdx 2 1) :=
    (PopStackMinimum.minimum_insertion_inC (R size) hpositive 2 (by omega) (by omega)).mpr hC
  have hnewPerm : (((R size).map Nat.succ).insertIdx 2 1).Perm (List.range' 1 (size + 1)) := by
    have hh : ((R size).map Nat.succ).Perm (List.range' 2 size) := by
      have hr : (List.range' 1 size).map Nat.succ = List.range' 2 size := by
        simpa only [Nat.succ_eq_add_one] using (List.range'_succ_left ..).symm
      simpa only [hr] using hperm.map Nat.succ
    exact (List.perm_insertIdx _ _ (by simp only [List.length_map, hlength]; omega)).trans
      (by simpa only [List.range'_succ] using hh.cons 1)
  exact ⟨hperm, hC, hlength, hlast, hintervals, by
    simpa only [Y, Nat.add_sub_cancel, simples, Set.mem_ofPred_eq] using
      And.intro hnewPerm (And.intro hnewC hsimple)⟩
end D5.S3.Combinatorics.PopStack.PopStackTerminalIntervals
