/- UNCOMPILED snippet for NativeJ2SurvivingEdges after the five full-word
   theorem and ActualPieceComponents / ActualSurvivingPartition helpers.
   Open private j2_native_survives j2_a_not_marked from SurvivingRows.
   Open private actual_port_leaf surviving_adj_iff from SurvivingModel.
   No component coverage, connectedness, or nil exclusion is assumed. -/

private theorem actual_port_a_neighbor {m : ℕ} (hm : 5 ≤ m)
    (q : Fin 3 × Bool × Bool) :
    (survivingGraph m).Adj (port m q) (port m q * a m) := by
  apply j2_native_survives hm (port m q) (a m)
    (native_j2_port_domain hm q) (Or.inl rfl) _ (j2_a_not_marked hm _)
  intro hd
  have hl := native_j2_port_last hm q
  rcases (native_f2_a_cut_classification (by omega : 4 ≤ m) (port m q)).mp hd with he | he
  · have hx : port m q ∈ s(1, a m) := he ▸ Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.mp hx with hx | hx
    all_goals
      rw [hx] at hl
      simp (disch := omega) [Equiv.Perm.one_apply, a_apply] at hl
      omega
  · have hx : port m q ∈
        s(Equiv.swap (0 : Fin (m + 1)) (Fin.last m),
          Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * a m) :=
      he ▸ Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.mp hx with hx | hx
    all_goals
      rw [hx] at hl
      simp (disch := omega) [Equiv.Perm.mul_apply, a_apply,
        Equiv.swap_apply_def, Fin.ext_iff] at hl
      omega

/-- The sixth actual component runs from L₁ to bar L₀. Its actual path and
full component inventory are obtained from the genuine six-cut slicing. -/
private theorem actual_sixth_full_component {m : ℕ} (hm : 5 ≤ m) :
    ∃ w : (survivingGraph m).Walk (port m (1, false, true)) (port m (0, true, true)),
      w.IsPath ∧
      (∀ x, x ∈ w.support ↔ (survivingGraph m).Reachable (port m (1, false, true)) x) ∧
      ∀ x y, (survivingGraph m).Adj x y ∧
        (survivingGraph m).Reachable (port m (1, false, true)) x ↔ s(x, y) ∈ w.edges := by
  classical
  let first : Fin 5 → Fin 3 × Bool × Bool := fun i =>
    match i.val with
    | 0 => (0, false, false)
    | 1 => (0, false, true)
    | 2 => (1, false, false)
    | 3 => (2, false, true)
    | _ => (0, true, false)
  let last : Fin 5 → Fin 3 × Bool × Bool := fun i =>
    match i.val with
    | 0 => (2, false, false)
    | 1 => (1, true, true)
    | 2 => (2, true, true)
    | 3 => (2, true, false)
    | _ => (1, true, false)
  have hfirst (i : Fin 5) : wordStart m i = port m (first i) := by
    fin_cases i <;> rfl
  have hlast (i : Fin 5) : wordFinish m i = port m (last i) := by
    fin_cases i <;> rfl
  have hfirst_ne (i : Fin 5) : (1, false, true) ≠ first i := by
    fin_cases i <;> decide
  have hlast_ne (i : Fin 5) : (1, false, true) ≠ last i := by
    fin_cases i <;> decide
  have hremaining : ∀ q : Fin 3 × Bool × Bool,
      q = (1, false, true) ∨ q = (0, true, true) ∨
        ∃ i : Fin 5, q = first i ∨ q = last i := by
    decide
  have hnotfirst (i : Fin 5) :
      ¬ (survivingGraph m).Reachable (port m (1, false, true)) (wordStart m i) := by
    intro hr
    obtain ⟨w, hp, _, _, hvertices, _⟩ := native_j2_word_full_component hm i
    have ha := (hvertices (port m (1, false, true))).mpr hr.symm
    rcases leaf_in_path_is_endpoint w hp ha (actual_port_leaf hm (1, false, true)) with he | he
    · exact hfirst_ne i (native_j2_port_injective hm (he.trans (hfirst i)))
    · exact hlast_ne i (native_j2_port_injective hm (he.trans (hlast i)))
  have hnotlast (i : Fin 5) :
      ¬ (survivingGraph m).Reachable (port m (1, false, true)) (wordFinish m i) := by
    intro hr
    obtain ⟨w, _, _, _, _, _⟩ := native_j2_word_full_component hm i
    exact hnotfirst i (hr.trans w.reachable.symm)
  obtain ⟨pieces, hpaths, hn, hdomain, hinventory, _, hendpoints⟩ :=
    actual_surviving_path_partition hm
  have ha : port m (1, false, true) ∈ (pieces.flatMap fun z => z.walk.support) :=
    (hdomain _).mpr (native_j2_port_domain hm (1, false, true))
  obtain ⟨p, hp, hap⟩ := List.mem_flatMap.mp ha
  have hall : ∀ x y, (survivingGraph m).Adj x y →
      s(x, y) ∈ (pieces.flatMap fun z => z.walk.edges) := by
    intro x y hxy
    exact (hinventory _).mpr ((surviving_adj_iff m x y).mp hxy).1
  obtain ⟨hvertices, hedges⟩ := partition_piece_full_component pieces hn hall p hp
  have haroot := (hvertices _).mp hap
  have hroots (x : Configuration m) :
      (survivingGraph m).Reachable p.start x ↔
        (survivingGraph m).Reachable (port m (1, false, true)) x :=
    ⟨fun h => haroot.symm.trans h, fun h => haroot.trans h⟩
  have hne : p.start ≠ p.finish := by
    intro heq
    have hnil := (hpaths p hp).nil_iff_eq.mpr heq
    have hedge := (hedges _ _).mp ⟨actual_port_a_neighbor hm (1, false, true), haroot⟩
    rw [SimpleGraph.Walk.edges_eq_nil.mpr hnil] at hedge
    exact List.not_mem_nil hedge
  have hother (v : Configuration m)
      (hv : ∃ q : Fin 3 × Bool × Bool, v = port m q)
      (hr : (survivingGraph m).Reachable (port m (1, false, true)) v)
      (hne : v ≠ port m (1, false, true)) : v = port m (0, true, true) := by
    obtain ⟨q, rfl⟩ := hv
    rcases hremaining q with hq | hq | ⟨i, hq | hq⟩
    · exact (hne (congrArg (port m) hq)).elim
    · exact congrArg (port m) hq
    · exact (hnotfirst i (by simpa only [hq, ← hfirst i] using hr)).elim
    · exact (hnotlast i (by simpa only [hq, ← hlast i] using hr)).elim
  rcases leaf_in_path_is_endpoint p.walk (hpaths p hp) hap
      (actual_port_leaf hm (1, false, true)) with has | haf
  · have hfinish : p.finish = port m (0, true, true) :=
      hother p.finish (hendpoints p hp).2
        (haroot.symm.trans p.walk.reachable) (fun h => hne (has.symm.trans h.symm))
    refine ⟨p.walk.copy has.symm hfinish, ?_, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.isPath_copy] using hpaths p hp
    · intro x
      simpa only [SimpleGraph.Walk.support_copy] using (hvertices x).trans (hroots x)
    · intro x y
      simpa only [SimpleGraph.Walk.edges_copy] using
        (show (survivingGraph m).Adj x y ∧
          (survivingGraph m).Reachable (port m (1, false, true)) x ↔ s(x, y) ∈ p.walk.edges by
          rw [← hroots x]; exact hedges x y)
  · have hstart : p.start = port m (0, true, true) :=
      hother p.start (hendpoints p hp).1 haroot.symm
        (fun h => hne (h.trans haf))
    refine ⟨p.walk.reverse.copy haf.symm hstart, ?_, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.isPath_copy] using (hpaths p hp).reverse
    · intro x
      simpa only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using (hvertices x).trans (hroots x)
    · intro x y
      simpa only [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse,
        List.mem_reverse] using
        (show (survivingGraph m).Adj x y ∧
          (survivingGraph m).Reachable (port m (1, false, true)) x ↔ s(x, y) ∈ p.walk.edges by
          rw [← hroots x]; exact hedges x y)

#print axioms actual_port_a_neighbor
#print axioms actual_sixth_full_component
