import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding

/-! Relabel cube axes in their order of first use along the search tree. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourAxisOrder

open private eraseDups_spec from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding

private theorem eraseDups_prefix (xs ys : List Nat) : xs.eraseDups <+: (xs ++ ys).eraseDups := by
  rw [List.eraseDups_append]
  exact List.prefix_append _ _

private theorem eraseDups_append_singleton (xs : List Nat) (a : Nat) :
    (xs ++ [a]).eraseDups = if a ∈ xs then xs.eraseDups else xs.eraseDups ++ [a] := by
  rw [List.eraseDups_append, List.cons_removeAll]
  by_cases h : a ∈ xs <;> simp [h, List.eraseDups_cons]

/-- A single axis permutation puts each newly encountered axis immediately
after those used so far. The number of axes used by a prefix is its number
of distinct entries. -/
private theorem normalize_axis_order (axes : List (Fin 8)) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ i (hi : i < axes.length),
      let used := ((axes.take i).map Fin.val).eraseDups.length
      let next := ((axes.take (i + 1)).map Fin.val).eraseDups.length
      (σ axes[i]).val < min (used + 1) 8 ∧
        max used ((σ axes[i]).val + 1) = next := by
  let raw := axes.map Fin.val
  let complete := raw.eraseDups ++ (List.range 8).filter (fun j => j ∉ raw)
  have hmem (j : Nat) : j ∈ complete ↔ j < 8 := by
    simp only [complete, List.mem_append, List.mem_eraseDups, List.mem_filter, List.mem_range,
      decide_eq_true_iff]
    constructor
    · rintro (h | h)
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
        exact a.isLt
      · exact h.1
    · intro h
      by_cases hm : j ∈ raw
      · exact Or.inl hm
      · exact Or.inr ⟨h, hm⟩
  have hnd : complete.Nodup := by
    refine (eraseDups_spec raw).2.append ((List.nodup_range).filter _) ?_
    intro a ha hb
    exact (of_decide_eq_true (List.mem_filter.mp hb).2) (List.mem_eraseDups.mp ha)
  have hlen : complete.length = 8 := by
    have hn := List.toFinset_card_of_nodup hnd
    have hf : complete.toFinset = Finset.range 8 := by
      ext j
      simp [hmem]
    rw [hf, Finset.card_range] at hn
    exact hn.symm
  let f (a : Fin 8) : Fin 8 := ⟨complete.idxOf a.val,
    (List.idxOf_lt_length_of_mem ((hmem a.val).mpr a.isLt)).trans_eq hlen⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    have eq : complete.idxOf a.val = complete.idxOf b.val := congrArg Fin.val h
    have ha := List.getElem?_idxOf ((hmem a.val).mpr a.isLt)
    have hb := List.getElem?_idxOf ((hmem b.val).mpr b.isLt)
    rw [eq, hb] at ha
    exact (Option.some.inj ha).symm
  let σ := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨σ, fun i hi => ?_⟩
  let pre := (axes.take i).map Fin.val
  let a := axes[i].val
  let used := pre.eraseDups.length
  have hp : pre.eraseDups <+: complete := by
    have hraw : pre ++ (axes.drop i).map Fin.val = raw := by
      rw [← List.map_append, List.take_append_drop]
    exact ((eraseDups_prefix pre ((axes.drop i).map Fin.val)).trans
      (hraw.symm ▸ List.prefix_append _ _))
  have htake : (axes.take (i + 1)).map Fin.val = pre ++ [a] := by
    rw [List.take_succ_eq_append_getElem hi, List.map_append]
    rfl
  have hNext : (pre ++ [a]).eraseDups <+: complete := by
    rw [← htake]
    have hraw : (axes.take (i + 1)).map Fin.val ++ (axes.drop (i + 1)).map Fin.val = raw := by
      rw [← List.map_append, List.take_append_drop]
    exact ((eraseDups_prefix _ ((axes.drop (i + 1)).map Fin.val)).trans
      (hraw.symm ▸ List.prefix_append _ _))
  change complete.idxOf a < min (used + 1) 8 ∧
    max used (complete.idxOf a + 1) = ((axes.take (i + 1)).map Fin.val).eraseDups.length
  rw [htake, eraseDups_append_singleton pre a]
  have hbound : complete.idxOf a < 8 := (f axes[i]).isLt
  by_cases h : a ∈ pre
  · rw [ite_eq_left h]
    have hlt := (hp.mem_iff_idxOf_lt_length a).mp (List.mem_eraseDups.mpr h)
    exact ⟨lt_min (by omega) hbound, max_eq_left (by omega)⟩
  · rw [ite_eq_right h]
    have hnew : complete.idxOf a = used := by
      rw [eraseDups_append_singleton, ite_eq_right h] at hNext
      have hcurrent : a ∈ pre.eraseDups ++ [a] := by simp
      rw [← hNext.idxOf_eq_of_mem hcurrent, List.idxOf_append_of_notMem]
      · simp [used]
      · exact fun hm => h (List.mem_eraseDups.mp hm)
    exact ⟨lt_min (by omega) hbound, by rw [hnew]; simp [used]⟩

#print axioms normalize_axis_order

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourAxisOrder
