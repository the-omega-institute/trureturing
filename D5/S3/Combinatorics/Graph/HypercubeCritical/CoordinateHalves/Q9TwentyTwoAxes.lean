import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbedding

/-! Relabel the cut, the three solid root axes, and the at most two remaining
axes in the first subdivided edge. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoAxes

/-- Prescribe the axes of the cut and the three root edges. Any other axes
used in the first two-step move then occupy consecutive indices starting at
four. -/
theorem normalize_first_axes (first : Fin 3 ↪ Fin 9) (hzero : ∀ i, first i ≠ 0)
    (a b : Fin 9) :
    let fixed : Fin 4 → Fin 9 := Fin.cases 0 first
    let extra := ({a, b} : Finset (Fin 9)) \ (Finset.univ.image fixed)
    ∃ σ : Equiv.Perm (Fin 9),
      (∀ i : Fin 4, (σ (fixed i)).val = i.val) ∧
      extra.image σ =
        Finset.univ.filter (fun i : Fin 9 => 4 ≤ i.val ∧ i.val < 4 + extra.card) := by
  classical
  let fixed : Fin 4 → Fin 9 := Fin.cases 0 first
  let extra := ({a, b} : Finset (Fin 9)) \ (Finset.univ.image fixed)
  have hfixed : Function.Injective fixed := by
    intro i j h
    revert h
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      rfl
    · exact fun h => (hzero j h.symm).elim
    · exact fun h => (hzero i h).elim
    · exact fun h => congrArg Fin.succ (first.injective h)
  have hcard : extra.card ≤ 2 := by
    calc
      _ ≤ ({a, b} : Finset (Fin 9)).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ 2 := Finset.card_insert_le _ _
  let e := Fintype.equivFinOfCardEq (Fintype.card_coe extra)
  let new (i : (extra : Set (Fin 9))) : Fin 9 := ⟨4 + (e i).val, by have h := (e i).isLt; omega⟩
  let oldLabel : Fin 4 ⊕ (extra : Set (Fin 9)) → Fin 9 := Sum.elim fixed Subtype.val
  let newLabel : Fin 4 ⊕ (extra : Set (Fin 9)) → Fin 9 :=
    Sum.elim (Fin.castLE (by decide : 4 ≤ 9)) new
  have hold : Function.Injective oldLabel := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (hfixed h)
    · have hj : j.val ∉ Finset.univ.image fixed := (Finset.mem_sdiff.mp j.property).2
      exact (hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)).elim
    · have hi : i.val ∉ Finset.univ.image fixed := (Finset.mem_sdiff.mp i.property).2
      exact (hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h.symm⟩)).elim
    · exact congrArg Sum.inr (Subtype.ext h)
  have hnew : Function.Injective newLabel := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (Fin.ext (congrArg (fun x : Fin 9 => x.val) h))
    · have hv := congrArg Fin.val h
      change i.val = 4 + (e j).val at hv
      omega
    · have hv := congrArg Fin.val h
      change 4 + (e i).val = j.val at hv
      omega
    · have hv := congrArg Fin.val h
      change 4 + (e i).val = 4 + (e j).val at hv
      exact congrArg Sum.inr (e.injective (Fin.ext (by omega)))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair oldLabel newLabel hold hnew
  have hmap (i : (extra : Set (Fin 9))) : σ i.val = new i := hσ (Sum.inr i)
  refine ⟨σ, fun i => congrArg Fin.val (hσ (Sum.inl i)), ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    rw [← hji, hmap ⟨j, hj⟩]
    change 4 ≤ 4 + (e ⟨j, hj⟩).val ∧ 4 + (e ⟨j, hj⟩).val < 4 + extra.card
    exact ⟨by omega, Nat.add_lt_add_left (e ⟨j, hj⟩).isLt 4⟩
  · rintro ⟨hi, himax⟩
    change i.val < 4 + extra.card at himax
    let j : Fin extra.card := ⟨i.val - 4, by omega⟩
    refine Finset.mem_image.mpr ⟨(e.symm j).val, (e.symm j).property, ?_⟩
    rw [hmap (e.symm j)]
    apply Fin.ext
    change 4 + (e (e.symm j)).val = i.val
    rw [e.apply_symm_apply]
    dsimp [j]
    omega

#print axioms normalize_first_axes

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoAxes
