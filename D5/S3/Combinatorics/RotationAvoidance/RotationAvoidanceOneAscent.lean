/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceOneAscent
   mirror-E: none(waiver:unique-ascent-partition-bijection)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Unique ascents recover partitions and endpoint obstructions order the color runs. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceEnumeration
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceOneAscent

open D5.S3.Combinatorics Nonnesting.NonnestingDefs

theorem one_ascent_count (size : ℕ) :
    let words : Set (List ℕ) := {word | word.Perm (List.range' 1 size) ∧
      ¬ word.Pairwise (· > ·) ∧ ∃ cut ≤ size,
        (word.take cut).Pairwise (· > ·) ∧ (word.drop cut).Pairwise (· > ·)}
    words.ncard = 2 ^ size - size - 1 ∧
      ∀ word ∈ words, ¬ Occurs [1, 2, 3] word ∧ ¬ Occurs [3, 4, 1, 2] word := by
  classical
  dsimp only
  let words : Set (List ℕ) := {word | word.Perm (List.range' 1 size) ∧
    ¬ word.Pairwise (· > ·) ∧ ∃ cut ≤ size,
      (word.take cut).Pairwise (· > ·) ∧ (word.drop cut).Pairwise (· > ·)}
  let base := (List.range' 1 size).reverse
  let subsets : Set (Finset ℕ) := ↑base.toFinset.powerset
  let first := fun selected : Finset ℕ => base.filter (fun value => decide (value ∈ selected))
  let last := fun selected : Finset ℕ => base.filter (fun value => !decide (value ∈ selected))
  let emit := fun selected : Finset ℕ => first selected ++ last selected
  let rejected := {selected ∈ subsets | (emit selected).Pairwise (· > ·)}
  let accepted := subsets \ rejected
  have baseLength : base.length = size := by simp [base]
  have baseNodup : base.Nodup := List.nodup_reverse.mpr List.nodup_range'
  have baseDescending : base.Pairwise (· > ·) :=
    List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
  have emitPerm (selected : Finset ℕ) : (emit selected).Perm (List.range' 1 size) :=
    (List.filter_append_perm _ base).trans (List.reverse_perm _)
  have selectedRecovered (selected : Finset ℕ) (hselected : selected ∈ subsets) :
      (first selected).toFinset = selected := by
    have hsubset : selected ⊆ base.toFinset := Finset.mem_powerset.mp hselected
    ext value
    simp only [first, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hvalue => ⟨List.mem_toFinset.mp (hsubset hvalue), hvalue⟩⟩
  have uniqueCut (word : List ℕ) (hnot : ¬ word.Pairwise (· > ·))
      (cut other : ℕ) (hcut : (word.take cut).Pairwise (· > ·) ∧
        (word.drop cut).Pairwise (· > ·))
      (hother : (word.take other).Pairwise (· > ·) ∧
        (word.drop other).Pairwise (· > ·)) : cut = other := by
    have hnotChain : ¬ word.IsChain (· > ·) := fun hh =>
      hnot (List.isChain_iff_pairwise.mp hh)
    obtain ⟨index, hindex, hbad⟩ := List.exists_not_getElem_of_not_isChain hnotChain
    have forced (boundary : ℕ)
        (hboundary : (word.take boundary).Pairwise (· > ·) ∧
          (word.drop boundary).Pairwise (· > ·)) : boundary = index + 1 := by
      by_contra hne
      by_cases hbefore : index + 1 < boundary
      · have hlo : index < (word.take boundary).length := by simp; omega
        have hhi : index + 1 < (word.take boundary).length := by simp; omega
        have hh := List.pairwise_iff_getElem.mp hboundary.1 index (index + 1)
          hlo hhi (by omega)
        exact hbad (by simpa only [List.getElem_take] using hh)
      · have hafter : boundary ≤ index := by omega
        have hlo : index - boundary < (word.drop boundary).length := by simp; omega
        have hhi : index + 1 - boundary < (word.drop boundary).length := by simp; omega
        have hh := List.pairwise_iff_getElem.mp hboundary.2 (index - boundary)
          (index + 1 - boundary) hlo hhi (by omega)
        simp only [List.getElem_drop] at hh
        have hfirst : boundary + (index - boundary) = index := by omega
        have hlast : boundary + (index + 1 - boundary) = index + 1 := by omega
        simp only [hfirst, hlast] at hh
        exact hbad hh
    exact (forced cut hcut).trans (forced other hother).symm
  have recoverHalves (word : List ℕ) (hperm : word.Perm (List.range' 1 size))
      (cut : ℕ) (hcut : (word.take cut).Pairwise (· > ·) ∧
        (word.drop cut).Pairwise (· > ·)) :
      (word.take cut).toFinset ∈ subsets ∧
        first (word.take cut).toFinset = word.take cut ∧
        last (word.take cut).toFinset = word.drop cut := by
    have hnodup := hperm.nodup_iff.mpr List.nodup_range'
    have hbase : word.Perm base := hperm.trans (List.reverse_perm _).symm
    have hsubset : (word.take cut).toFinset ∈ subsets := by
      apply Finset.mem_powerset.mpr
      intro value hvalue
      exact List.mem_toFinset.mpr (hbase.mem_iff.mp
        (List.take_sublist cut word |>.subset (List.mem_toFinset.mp hvalue)))
    have hfirst : first (word.take cut).toFinset = word.take cut := by
      have hp : (first (word.take cut).toFinset).Perm (word.take cut) := by
        apply (List.perm_ext_iff_of_nodup (baseNodup.filter _) hnodup.take).mpr
        intro value
        simp only [List.mem_filter, decide_eq_true_eq, List.mem_toFinset]
        exact ⟨And.right, fun hvalue => ⟨hbase.mem_iff.mp
          (List.take_sublist cut word |>.subset hvalue), hvalue⟩⟩
      exact hp.eq_of_pairwise (by intro lower upper hlo hhi; omega)
        (baseDescending.filter _) hcut.1
    have hlast : last (word.take cut).toFinset = word.drop cut := by
      have hp : (last (word.take cut).toFinset).Perm (word.drop cut) := by
        apply (List.perm_ext_iff_of_nodup (baseNodup.filter _) hnodup.drop).mpr
        intro value
        simp only [List.mem_filter, List.mem_toFinset,
          Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
        have hdisjoint := (List.nodup_append.mp
          (show (word.take cut ++ word.drop cut).Nodup by simpa using hnodup)).2.2
        constructor
        · rintro ⟨hvalue, hnot⟩
          have hm := hbase.mem_iff.mpr hvalue
          rw [← List.take_append_drop cut word, List.mem_append] at hm
          exact hm.resolve_left hnot
        · intro hvalue
          exact ⟨hbase.mem_iff.mp (List.drop_sublist cut word |>.subset hvalue),
            fun hl => hdisjoint value hl value hvalue rfl⟩
      exact hp.eq_of_pairwise (by intro lower upper hlo hhi; omega)
        (baseDescending.filter _) hcut.2
    exact ⟨hsubset, hfirst, hlast⟩
  have finiteSubsets : subsets.Finite := Finset.finite_toSet _
  have rejectedSubset : rejected ⊆ subsets := fun _ hh => hh.1
  have rejectedCount : rejected.ncard = size + 1 := by
    let choose := fun cut : ℕ => (base.take cut).toFinset
    have chooseMember (cut : ℕ) (hcut : cut < size + 1) : choose cut ∈ rejected := by
      have hp : base.Perm (List.range' 1 size) := List.reverse_perm _
      obtain ⟨hsubset, hfirst, hlast⟩ := recoverHalves base hp cut
        ⟨baseDescending.take, baseDescending.drop⟩
      refine ⟨hsubset, ?_⟩
      simpa only [emit, choose, hfirst, hlast, List.take_append_drop] using baseDescending
    have chooseSurjective (selected : Finset ℕ) (hselected : selected ∈ rejected) :
        ∃ cut, ∃ hcut : cut < size + 1, choose cut = selected := by
      have heq : emit selected = base :=
        ((emitPerm selected).trans (List.reverse_perm _).symm).eq_of_pairwise
          (by intro lower upper hlo hhi; omega) hselected.2 baseDescending
      have hlength : (first selected).length ≤ size := by
        have hh := List.length_filter_le (fun value => decide (value ∈ selected)) base
        simpa only [first, baseLength] using hh
      refine ⟨(first selected).length, by omega, ?_⟩
      have ht := congrArg (List.take (first selected).length) heq
      have htake : base.take (first selected).length = first selected := by
        simpa only [emit, List.take_left] using ht.symm
      simp only [choose, htake, selectedRecovered selected hselected.1]
    have chooseInjective (cut other : ℕ) (hcut : cut < size + 1)
        (hother : other < size + 1) (heq : choose cut = choose other) : cut = other := by
      have hh := congrArg Finset.card heq
      simp only [choose, List.toFinset_card_of_nodup baseNodup.take,
        List.length_take, baseLength] at hh
      omega
    exact Set.ncard_eq_of_bijective (fun cut _ => choose cut)
      chooseSurjective chooseMember chooseInjective
  have emitMember (selected : Finset ℕ) (hselected : selected ∈ accepted) :
      emit selected ∈ words := by
    have hnot : ¬ (emit selected).Pairwise (· > ·) := by
      intro hh
      exact hselected.2 ⟨hselected.1, hh⟩
    have hlength : (first selected).length ≤ size := by
      have hh := List.length_filter_le (fun value => decide (value ∈ selected)) base
      simpa only [first, baseLength] using hh
    refine ⟨emitPerm selected, hnot, (first selected).length, hlength, ?_, ?_⟩
    · simpa only [emit, List.take_left] using baseDescending.filter
        (fun value => decide (value ∈ selected))
    · simpa only [emit, List.drop_left] using baseDescending.filter
        (fun value => !decide (value ∈ selected))
  have emitInjective (selected other : Finset ℕ) (hselected : selected ∈ accepted)
      (hother : other ∈ accepted) (heq : emit selected = emit other) : selected = other := by
    have hcuts := uniqueCut (emit selected) (emitMember selected hselected).2.1
      (first selected).length (first other).length
      (by
        simp only [emit, List.take_left, List.drop_left]
        exact ⟨baseDescending.filter _, baseDescending.filter _⟩)
      (by
        rw [heq]
        simp only [emit, List.take_left, List.drop_left]
        exact ⟨baseDescending.filter _, baseDescending.filter _⟩)
    have hfirst : first selected = first other := by
      calc
        first selected = (emit selected).take (first selected).length := by simp [emit]
        _ = (emit other).take (first selected).length := congrArg _ heq
        _ = first other := by rw [hcuts]; simp [emit]
    have hh := congrArg List.toFinset hfirst
    simpa only [selectedRecovered selected hselected.1, selectedRecovered other hother.1] using hh
  have emitSurjective (word : List ℕ) (hword : word ∈ words) :
      ∃ selected ∈ accepted, emit selected = word := by
    obtain ⟨hperm, hnot, cut, hbound, hcut⟩ := hword
    obtain ⟨hsubset, hfirst, hlast⟩ := recoverHalves word hperm cut hcut
    have heq : emit (word.take cut).toFinset = word := by
      simp only [emit, hfirst, hlast, List.take_append_drop]
    refine ⟨(word.take cut).toFinset, ⟨hsubset, ?_⟩, heq⟩
    rintro ⟨_, hh⟩
    exact hnot (heq ▸ hh)
  have hcard := Set.ncard_congr (s := accepted) (t := words)
    (fun selected _ => emit selected) emitMember emitInjective (by
      intro word hword
      obtain ⟨selected, hselected, heq⟩ := emitSurjective word hword
      exact ⟨selected, hselected, heq⟩)
  have subsetsCount : subsets.ncard = 2 ^ size := by
    simp only [subsets, Set.ncard_coe_finset, Finset.card_powerset,
      List.toFinset_card_of_nodup baseNodup, baseLength]
  have acceptedCount : accepted.ncard = 2 ^ size - size - 1 := by
    have hh := Set.ncard_sdiff_add_ncard_of_subset rejectedSubset finiteSubsets
    change accepted.ncard + rejected.ncard = subsets.ncard at hh
    rw [rejectedCount, subsetsCount] at hh
    omega
  constructor
  · exact hcard.symm.trans acceptedCount
  · intro word hword
    obtain ⟨_, _, cut, _, hleft, hright⟩ := hword
    have hsplit (selected : List ℕ) (hsub : selected.Sublist word) :
        ∃ boundary ≤ selected.length,
          (selected.take boundary).Pairwise (· > ·) ∧
          (selected.drop boundary).Pairwise (· > ·) := by
      rw [← List.take_append_drop cut word] at hsub
      obtain ⟨left, right, heq, hl, hr⟩ := List.sublist_append_iff.mp hsub
      refine ⟨left.length, ?_, ?_, ?_⟩
      · rw [heq, List.length_append]; omega
      · simpa only [heq, List.take_left] using hleft.sublist hl
      · simpa only [heq, List.drop_left] using hright.sublist hr
    constructor
    · rintro ⟨witness, hi, _, hsub, _⟩
      have h12 : witness 1 < witness 2 := hi 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hi 2 (by omega) (by decide)
      obtain ⟨boundary, hbound, hl, hr⟩ := hsplit _ hsub
      simp only [List.length_map, List.length_cons, List.length_nil] at hbound
      interval_cases boundary
      · have hh := List.pairwise_iff_forall_sublist.mp hr
          (by simp : [witness 1, witness 2].Sublist
            (([1, 2, 3].map witness).drop 0))
        omega
      · have hh := List.pairwise_iff_forall_sublist.mp hr
          (by simp : [witness 2, witness 3].Sublist
            (([1, 2, 3].map witness).drop 1))
        omega
      · have hh := List.pairwise_iff_forall_sublist.mp hl
          (by simp : [witness 1, witness 2].Sublist
            (([1, 2, 3].map witness).take 2))
        omega
      · have hh := List.pairwise_iff_forall_sublist.mp hl
          (by simp : [witness 1, witness 2].Sublist
            (([1, 2, 3].map witness).take 3))
        omega
    · rintro ⟨witness, hi, _, hsub, _⟩
      have h12 : witness 1 < witness 2 := hi 1 (by omega) (by decide)
      have h34 : witness 3 < witness 4 := hi 3 (by omega) (by decide)
      obtain ⟨boundary, hbound, hl, hr⟩ := hsplit _ hsub
      simp only [List.length_map, List.length_cons, List.length_nil] at hbound
      interval_cases boundary
      · have hh := List.pairwise_iff_forall_sublist.mp hr
          ((by decide : [1, 2].Sublist [3, 4, 1, 2]).map witness)
        simp only [List.drop_zero] at hr
        omega
      · have hh := List.pairwise_iff_forall_sublist.mp hr
          (by simp : [witness 1, witness 2].Sublist
            (([3, 4, 1, 2].map witness).drop 1))
        omega
      · have hh := List.pairwise_iff_forall_sublist.mp hl
          (by simp : [witness 3, witness 4].Sublist
            (([3, 4, 1, 2].map witness).take 2))
        omega
      · have hh := List.pairwise_iff_forall_sublist.mp hl
          (by simp : [witness 3, witness 4].Sublist
            (([3, 4, 1, 2].map witness).take 3))
        omega
      · have hh := List.pairwise_iff_forall_sublist.mp hl
          (by simp : [witness 3, witness 4].Sublist
            (([3, 4, 1, 2].map witness).take 4))
        omega

theorem paired_endpoint_color_order (size first last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size)
    (hperm : (first :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [2, 1, 4, 3] ((first :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    first < last ∧
      (interior.filter (fun value => decide (value < first))).Pairwise (· < ·) ∧
      (interior.filter (fun value => decide (last < value))).Pairwise (· < ·) ∧
      ∃ lower upper, [lower, upper].Sublist interior ∧ lower < first ∧ last < upper := by
  classical
  let word := first :: interior ++ [last]
  have hcriterion := (RotationAvoidanceCircular.unique_bad_cut_iff size hsize
    [2, 1, 4, 3] word (by decide) hperm).mp hcuts
  have hdrop : word.dropLast = first :: interior := by
    change ((first :: interior) ++ [last]).dropLast = first :: interior
    rw [List.dropLast_append_cons]
    simp
  have build (pattern selected : List ℕ) (witness : ℕ → ℕ)
      (hp : pattern.Perm [1, 2, 3, 4]) (hletters : letters pattern = 4)
      (hi : ∀ rank, 1 ≤ rank → rank < 4 → witness rank < witness (rank + 1))
      (hs : (pattern.map witness).Sublist selected) : Occurs pattern selected := by
    refine ⟨witness, ?_, ?_, hs, by simp⟩
    · simpa only [hletters] using hi
    · intro rank hlo hhi
      rw [hletters] at hhi
      apply hs.subset
      apply List.mem_map_of_mem
      apply hp.mem_iff.mpr
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨witness, hi, _, hsub, _⟩ := hcriterion.1
  have h12 : witness 1 < witness 2 := hi 1 (by omega) (by decide)
  have h23 : witness 2 < witness 3 := hi 2 (by omega) (by decide)
  have h34 : witness 3 < witness 4 := hi 3 (by omega) (by decide)
  have hfirst : witness 2 = first := by
    by_contra hne
    have hs : ([2, 1, 4, 3].map witness).Sublist (interior ++ [last]) :=
      List.Sublist.of_cons_of_ne hne hsub
    exact hcriterion.2.2.1 (build _ word.tail witness (by decide) rfl hi hs)
  have hlast : witness 3 = last := by
    by_contra hne
    have hs : [witness 3, witness 4, witness 1, witness 2].Sublist
        (last :: interior.reverse ++ [first]) := by
      simpa [word] using hsub.reverse
    have hwithoutLast := List.Sublist.of_cons_of_ne hne hs
    have hselected : ([2, 1, 4, 3].map witness).Sublist (first :: interior) := by
      simpa using hwithoutLast.reverse
    exact hcriterion.2.2.2 (build _ word.dropLast witness (by decide) rfl hi
      (hdrop.symm ▸ hselected))
  have endpointOrder : first < last := by omega
  have hselected : [witness 1, witness 4].Sublist interior := by
    have hs : [witness 1, witness 4, last].Sublist (interior ++ [last]) := by
      apply (List.cons_sublist_cons (a := first)).mp
      simpa [word, hfirst, hlast] using hsub
    have hr : (last :: [witness 4, witness 1]).Sublist (last :: interior.reverse) := by
      simpa using hs.reverse
    have hh := List.cons_sublist_cons.mp hr
    simpa using hh.reverse
  have hnodup : interior.Nodup :=
    ((List.nodup_cons.mp (hperm.nodup_iff.mpr List.nodup_range')).2).sublist
      (List.sublist_append_left _ _)
  have selectedWithEndpoints (lower upper : ℕ) (hs : [lower, upper].Sublist interior) :
      [first, lower, upper, last].Sublist word := by
    exact (hs.append (List.Sublist.refl [last])).cons_cons first
  have rotatedForbidden (pattern : List ℕ) (shift : ℕ)
      (hshift : 0 < shift) (hbound : shift < 4)
      (heq : ([2, 1, 4, 3] : List ℕ).rotate shift = pattern) : ¬ Occurs pattern word := by
    simpa only [heq] using hcriterion.2.1 shift hshift hbound
  refine ⟨endpointOrder, ?_, ?_, witness 1, witness 4, hselected, by omega, by omega⟩
  · apply List.pairwise_iff_forall_sublist.mpr
    intro lower upper hs
    have hl : lower < first := (List.mem_filter.mp (hs.subset (by simp))).2 |> of_decide_eq_true
    have hu : upper < first := (List.mem_filter.mp (hs.subset (by simp))).2 |> of_decide_eq_true
    have hsInterior := hs.trans (List.filter_sublist (p := fun value => decide (value < first)))
    have hne : lower ≠ upper := by
      have hh := hnodup.sublist hsInterior
      simpa only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, not_false_eq_true, and_true] using hh
    by_contra hnot
    have hdesc : upper < lower := by omega
    let chosen := fun rank : ℕ => if rank = 1 then upper else if rank = 2 then lower
      else if rank = 3 then first else last
    apply rotatedForbidden [3, 2, 1, 4] 3 (by omega) (by omega) (by decide)
    apply build [3, 2, 1, 4] word chosen (by decide) rfl
    · intro rank hlo hhi
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases this with rfl | rfl | rfl
      · simpa [chosen] using hdesc
      · simpa [chosen] using hl
      · simpa [chosen] using endpointOrder
    · simpa [chosen] using
        selectedWithEndpoints lower upper hsInterior
  · apply List.pairwise_iff_forall_sublist.mpr
    intro lower upper hs
    have hl : last < lower := (List.mem_filter.mp (hs.subset (by simp))).2 |> of_decide_eq_true
    have hu : last < upper := (List.mem_filter.mp (hs.subset (by simp))).2 |> of_decide_eq_true
    have hsInterior := hs.trans (List.filter_sublist (p := fun value => decide (last < value)))
    have hne : lower ≠ upper := by
      have hh := hnodup.sublist hsInterior
      simpa only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, not_false_eq_true, and_true] using hh
    by_contra hnot
    have hdesc : upper < lower := by omega
    let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then last
      else if rank = 3 then upper else lower
    apply rotatedForbidden [1, 4, 3, 2] 1 (by omega) (by omega) (by decide)
    apply build [1, 4, 3, 2] word chosen (by decide) rfl
    · intro rank hlo hhi
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases this with rfl | rfl | rfl
      · simpa [chosen] using endpointOrder
      · simpa [chosen] using hu
      · simpa [chosen] using hdesc
    · simpa [chosen] using
        selectedWithEndpoints lower upper hsInterior

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceOneAscent
