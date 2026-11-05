/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/TwoRunRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical-coordinate refinement for two positive runs with type-dependent lengths. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialRefinement

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.TwoRunRefinement

/-- Literal upper words; both run multiplicities may depend on the upper type. -/
def word (W : Bool → List Bool) (l r : Bool → ℕ) (a : Bool) : List Bool :=
  repeatWord (W false) (l a) ++ repeatWord (W true) (r a)

@[simp] theorem word_length (W : Bool → List Bool) (l r : Bool → ℕ) (a : Bool) :
    (word W l r a).length = l a * (W false).length + r a * (W true).length := by
  simp [word]

theorem word_length_pos (W : Bool → List Bool) (hW : ∀ a, 0 < (W a).length)
    (l r : Bool → ℕ) (hl : ∀ a, 0 < l a) (a : Bool) :
    0 < (word W l r a).length := by
  have hp := Nat.mul_pos (hl a) (hW false)
  rw [word_length]
  omega

/-- At each physical offset select its actual child and the offset inside that child. -/
def refineState (W : Bool → List Bool) (hW : ∀ a, 0 < (W a).length)
    (l r : Bool → ℕ) (s : TileState (word W l r)) : TileState W :=
  if s.2.val < l s.1 * (W false).length then
    cyclicState W false (hW false) s.2.val
  else
    cyclicState W true (hW true) (s.2.val - l s.1 * (W false).length)

private theorem refineState_of_lt (W : Bool → List Bool) (hW : ∀ a, 0 < (W a).length)
    (l r : Bool → ℕ) (s : TileState (word W l r))
    (h : s.2.val < l s.1 * (W false).length) :
    refineState W hW l r s = cyclicState W false (hW false) s.2.val := by
  simp only [refineState, if_pos h]

private theorem refineState_of_not_lt (W : Bool → List Bool)
    (hW : ∀ a, 0 < (W a).length) (l r : Bool → ℕ) (s : TileState (word W l r))
    (h : ¬ s.2.val < l s.1 * (W false).length) :
    refineState W hW l r s =
      cyclicState W true (hW true) (s.2.val - l s.1 * (W false).length) := by
  simp only [refineState, if_neg h]

private theorem refineState_type_false_iff (W : Bool → List Bool)
    (hW : ∀ a, 0 < (W a).length) (l r : Bool → ℕ) (s : TileState (word W l r)) :
    (refineState W hW l r s).1 = false ↔ s.2.val < l s.1 * (W false).length := by
  simp only [refineState]
  split <;> simp_all [cyclicState]

private theorem refineState_type_true_iff (W : Bool → List Bool)
    (hW : ∀ a, 0 < (W a).length) (l r : Bool → ℕ) (s : TileState (word W l r)) :
    (refineState W hW l r s).1 = true ↔ ¬ s.2.val < l s.1 * (W false).length := by
  simp only [refineState]
  split <;> simp_all [cyclicState]

/-- Every actual upper edge refines to an actual lower edge, including both kinds of seam. -/
theorem refineState_next (W : Bool → List Bool) (hW : ∀ a, 0 < (W a).length)
    (l r : Bool → ℕ) (hl : ∀ a, 0 < l a) (hr : ∀ a, 0 < r a)
    {s t : TileState (word W l r)} (hst : TileNext (word W l r) s t) :
    TileNext W (refineState W hW l r s) (refineState W hW l r t) := by
  let c := l s.1 * (W false).length
  have hc : 0 < c := Nat.mul_pos (hl s.1) (hW false)
  have hslen : (word W l r s.1).length = c + r s.1 * (W true).length :=
    word_length W l r s.1
  have htail : 0 < r s.1 * (W true).length := Nat.mul_pos (hr s.1) (hW true)
  rcases hst with ⟨htype, hoff⟩ | ⟨hlast, hstart⟩
  · have hcut : l t.1 * (W false).length = c := by rw [← htype]
    by_cases hs : s.2.val < c
    · by_cases ht : t.2.val < c
      · rw [refineState_of_lt W hW l r s hs,
          refineState_of_lt W hW l r t (by simpa only [hcut] using ht)]
        simpa only [hoff] using cyclicState_next W false (hW false) s.2.val
      · have hcross : t.2.val = c := by omega
        have hmod : (s.2.val + 1) % (W false).length = 0 := by
          rw [← hoff, hcross]
          exact Nat.mul_mod_left _ _
        have hbefore := mod_before_multiple (hW false) hmod
        rw [refineState_of_lt W hW l r s hs,
          refineState_of_not_lt W hW l r t (by simpa only [hcut] using ht)]
        right
        change s.2.val % (W false).length + 1 = (W false).length ∧
          (t.2.val - l t.1 * (W false).length) % (W true).length = 0
        exact ⟨hbefore, by rw [hcut, hcross]; simp⟩
    · have ht : ¬ t.2.val < c := by omega
      have hdiff : t.2.val - c = s.2.val - c + 1 := by omega
      rw [refineState_of_not_lt W hW l r s hs,
        refineState_of_not_lt W hW l r t (by simpa only [hcut] using ht)]
      change TileNext W (cyclicState W true (hW true) (s.2.val - c))
        (cyclicState W true (hW true) (t.2.val - l t.1 * (W false).length))
      rw [hcut, hdiff]
      exact cyclicState_next W true (hW true) (s.2.val - c)
  · have hs : ¬ s.2.val < c := by omega
    have ht : t.2.val < l t.1 * (W false).length := by
      have := Nat.mul_pos (hl t.1) (hW false)
      omega
    have hdiff : s.2.val - c + 1 = r s.1 * (W true).length := by omega
    have hmod : (s.2.val - c + 1) % (W true).length = 0 := by
      rw [hdiff]
      exact Nat.mul_mod_left _ _
    have hbefore := mod_before_multiple (hW true) hmod
    rw [refineState_of_not_lt W hW l r s hs, refineState_of_lt W hW l r t ht]
    right
    change (s.2.val - c) % (W true).length + 1 = (W true).length ∧
      t.2.val % (W false).length = 0
    exact ⟨hbefore, by rw [hstart]; simp⟩

/-- Refinement of the actual bi-infinite marked configuration. -/
def refineTiling (W : Bool → List Bool) (hW : ∀ a, 0 < (W a).length)
    (l r : Bool → ℕ) (hl : ∀ a, 0 < l a) (hr : ∀ a, 0 < r a)
    (x : MarkedTiling (word W l r)) : MarkedTiling W :=
  ⟨fun i => refineState W hW l r (x.1 i),
    fun i => refineState_next W hW l r hl hr (x.2 i)⟩

/-- The lower type transition 10 identifies exactly the parent boundaries. -/
theorem refineTiling_boundary_iff (W : Bool → List Bool)
    (hW : ∀ a, 0 < (W a).length) (l r : Bool → ℕ)
    (hl : ∀ a, 0 < l a) (hr : ∀ a, 0 < r a)
    (x : MarkedTiling (word W l r)) (i : ℤ) :
    (x.1 i).2.val = 0 ↔
      ((refineTiling W hW l r hl hr x).1 (i - 1)).1 = true ∧
      ((refineTiling W hW l r hl hr x).1 i).1 = false := by
  have hnext : TileNext (word W l r) (x.1 (i - 1)) (x.1 i) := by
    simpa using x.2 (i - 1)
  have hlen := word_length W l r (x.1 (i - 1)).1
  have htail := Nat.mul_pos (hr (x.1 (i - 1)).1) (hW true)
  have hc := Nat.mul_pos (hl (x.1 i).1) (hW false)
  change (x.1 i).2.val = 0 ↔
    (refineState W hW l r (x.1 (i - 1))).1 = true ∧
      (refineState W hW l r (x.1 i)).1 = false
  rw [refineState_type_true_iff, refineState_type_false_iff]
  rcases hnext with ⟨htype, hoff⟩ | ⟨hlast, hstart⟩
  · have hcut : l (x.1 (i - 1)).1 * (W false).length =
        l (x.1 i).1 * (W false).length := by rw [htype]
    omega
  · constructor
    · intro _
      exact ⟨by omega, by omega⟩
    · exact fun _ => hstart

/-- Reading commutes with refinement at each physical state. -/
theorem readTile_refineState (W : Bool → List Bool) (hW : ∀ a, 0 < (W a).length)
    (l r : Bool → ℕ) (s : TileState (word W l r)) :
    readTile W (refineState W hW l r s) = readTile (word W l r) s := by
  rcases s with ⟨a, ⟨i, hiBound⟩⟩
  by_cases hs : i < l a * (W false).length
  · have hi : i < (repeatWord (W false) (l a)).length := by simpa using hs
    rw [refineState_of_lt W hW l r ⟨a, ⟨i, hiBound⟩⟩ hs]
    simp only [readTile, cyclicState, List.get_eq_getElem, word, List.getElem_append_left hi]
    exact (repeatWord_getElem (W false) (hW false) hs).symm
  · have hi : (repeatWord (W false) (l a)).length ≤ i := by
      simpa using Nat.le_of_not_gt hs
    have hlt : i < l a * (W false).length + r a * (W true).length := by
      simpa only [word_length] using hiBound
    have hj : i - l a * (W false).length < r a * (W true).length := by omega
    rw [refineState_of_not_lt W hW l r ⟨a, ⟨i, hiBound⟩⟩ hs]
    simp only [readTile, cyclicState, List.get_eq_getElem, word, List.getElem_append_right hi]
    simpa only [length_repeatWord] using
      (repeatWord_getElem (W true) (hW true) hj).symm

theorem readTiling_refineTiling (W : Bool → List Bool) (hW : ∀ a, 0 < (W a).length)
    (l r : Bool → ℕ) (hl : ∀ a, 0 < l a) (hr : ∀ a, 0 < r a)
    (x : MarkedTiling (word W l r)) :
    readTiling W (refineTiling W hW l r hl hr x) = readTiling (word W l r) x := by
  funext i
  exact readTile_refineState W hW l r (x.1 i)

/-- An upper boundary at the physical origin is also a lower boundary there. -/
theorem refineTiling_aligned_zero (W : Bool → List Bool)
    (hW : ∀ a, 0 < (W a).length) (l r : Bool → ℕ)
    (hl : ∀ a, 0 < l a) (hr : ∀ a, 0 < r a)
    (x : MarkedTiling (word W l r)) (hx : (x.1 0).2.val = 0) :
    ((refineTiling W hW l r hl hr x).1 0).2.val = 0 := by
  have hc := Nat.mul_pos (hl (x.1 0).1) (hW false)
  change (refineState W hW l r (x.1 0)).2.val = 0
  rw [refineState_of_lt W hW l r (x.1 0) (by omega)]
  simp [cyclicState, hx]

/-- Every upper tiled configuration has an actual lower tiling with the same readout. -/
theorem tiledSubshift_subset (W : Bool → List Bool) (hW : ∀ a, 0 < (W a).length)
    (l r : Bool → ℕ) (hl : ∀ a, 0 < l a) (hr : ∀ a, 0 < r a) :
    (tiledSubshift (word W l r)).carrier ⊆ (tiledSubshift W).carrier := by
  rintro y ⟨x, rfl⟩
  exact ⟨refineTiling W hW l r hl hr x, readTiling_refineTiling W hW l r hl hr x⟩

/-- Visible configurations admitting an actual tile boundary at physical zero. -/
def alignedConfigurations (W : Bool → List Bool) : Set (ℤ → Bool) :=
  readTiling W '' {x : MarkedTiling W | (x.1 0).2.val = 0}

/-- The origin constraint has a nonempty compact visible image, without recognizability. -/
theorem alignedConfigurations_compact_nonempty (W : Bool → List Bool)
    (hW : ∀ a, 0 < (W a).length) :
    IsCompact (alignedConfigurations W) ∧ (alignedConfigurations W).Nonempty := by
  have hc : Continuous (fun x : MarkedTiling W => (x.1 0).2.val) :=
    (continuous_of_discreteTopology : Continuous (fun s : TileState W => s.2.val)).comp
      ((continuous_apply (0 : ℤ)).comp continuous_subtype_val)
  refine ⟨(isClosed_eq hc continuous_const).isCompact.image (continuous_readTiling W), ?_⟩
  let x : MarkedTiling W :=
    ⟨periodicTile W false (hW false), periodicTile_tiled W false (hW false)⟩
  refine ⟨readTiling W x, x, ?_, rfl⟩
  change (periodicTile W false (hW false) (0 : ℤ)).2.val = 0
  simp [periodicTile]

/-- Refinement preserves the compact origin constraint as well as the visible configuration. -/
theorem alignedConfigurations_subset (W : Bool → List Bool)
    (hW : ∀ a, 0 < (W a).length) (l r : Bool → ℕ)
    (hl : ∀ a, 0 < l a) (hr : ∀ a, 0 < r a) :
    alignedConfigurations (word W l r) ⊆ alignedConfigurations W := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨refineTiling W hW l r hl hr x,
    refineTiling_aligned_zero W hW l r hl hr x hx,
    readTiling_refineTiling W hW l r hl hr x⟩

end D5.S1.Dynamics.Symbolic.PermutativeLifts.TwoRunRefinement
