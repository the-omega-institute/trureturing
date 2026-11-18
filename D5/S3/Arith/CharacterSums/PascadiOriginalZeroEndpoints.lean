/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalZeroEndpoints
   generality: G
   mirror-B: none(waiver:actual-original-zero-endpoint-count)
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Original zero-endpoint returns are counted by their actual middle pairs. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalChartPieces

/-! A zero physical endpoint makes both original row sums vanish modulo the
modulus. Thus the actual middle pair determines the other endpoint uniquely
in a small literal box. No unit-middle or geometric chart is required. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem zero_endpoint_row_sums {c : ℕ} [NeZero c]
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (h : ReturnRows) (i : Fin 3) (hi : i = 0 ∨ i = 1)
    (hword : sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hz : (h.1 i, h.2 i) = (0 : Coordinate)) :
    (h.1 0 : ZMod c) + h.1 1 + h.1 2 = 0 ∧
      (h.2 2 : ZMod c) + h.2 0 + h.2 1 = 0 := by
  have hz₁ : h.1 i = 0 := congrArg Prod.fst hz
  have hz₂ : h.2 i = 0 := congrArg Prod.snd hz
  have he := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp hword
  rcases hi with rfl | rfl
  · constructor
    · simpa only [hz₁, Int.cast_zero, zero_add, add_zero, mul_zero, zero_mul] using he.1
    · simpa only [hz₂, Int.cast_zero, zero_add, add_zero, mul_zero, zero_mul] using he.2.1
  · constructor
    · simpa only [hz₁, Int.cast_zero, zero_add, add_zero, mul_zero, zero_mul] using he.1
    · simpa only [hz₂, Int.cast_zero, zero_add, add_zero, mul_zero, zero_mul] using he.2.1

private theorem zero_endpoint_middle_injective {c : ℕ} [NeZero c]
    {X Y : ℝ} (hXsmall : 2 * X < c) (hYsmall : 2 * Y < c)
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (S : Finset ReturnRows) (i : Fin 3) (hi : i = 0 ∨ i = 1)
    (hbox : ∀ h ∈ S, ∀ j, |(h.1 j : ℝ)| ≤ X ∧ |(h.2 j : ℝ)| ≤ Y)
    (hword : ∀ h ∈ S, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hzero : ∀ h ∈ S, (h.1 i, h.2 i) = (0 : Coordinate)) :
    Set.InjOn originalMiddle (S : Set ReturnRows) := by
  intro h hh h' hh' hm
  have hsum := zero_endpoint_row_sums a₁ a₂ ha₁ ha₂ h i hi (hword h hh) (hzero h hh)
  have hsum' := zero_endpoint_row_sums a₁ a₂ ha₁ ha₂ h' i hi (hword h' hh') (hzero h' hh')
  have hxmid : h.1 2 = h'.1 2 := congrArg Prod.fst hm
  have hymid : h.2 2 = h'.2 2 := congrArg Prod.snd hm
  have hxm : (h.1 2 : ZMod c) = h'.1 2 := by rw [hxmid]
  have hym : (h.2 2 : ZMod c) = h'.2 2 := by rw [hymid]
  have hzx : (h.1 i : ZMod c) = 0 := by
    rw [show h.1 i = 0 from congrArg Prod.fst (hzero h hh), Int.cast_zero]
  have hzx' : (h'.1 i : ZMod c) = 0 := by
    rw [show h'.1 i = 0 from congrArg Prod.fst (hzero h' hh'), Int.cast_zero]
  have hzy : (h.2 i : ZMod c) = 0 := by
    rw [show h.2 i = 0 from congrArg Prod.snd (hzero h hh), Int.cast_zero]
  have hzy' : (h'.2 i : ZMod c) = 0 := by
    rw [show h'.2 i = 0 from congrArg Prod.snd (hzero h' hh'), Int.cast_zero]
  have hx (j : Fin 3) : (h.1 j : ZMod c) = h'.1 j := by
    rcases hi with rfl | rfl
    · fin_cases j
      · exact hzx.trans hzx'.symm
      · change (h.1 1 : ZMod c) = h'.1 1
        linear_combination hsum.1 - hsum'.1 - hzx + hzx' - hxm
      · exact hxm
    · fin_cases j
      · change (h.1 0 : ZMod c) = h'.1 0
        linear_combination hsum.1 - hsum'.1 - hzx + hzx' - hxm
      · exact hzx.trans hzx'.symm
      · exact hxm
  have hy (j : Fin 3) : (h.2 j : ZMod c) = h'.2 j := by
    rcases hi with rfl | rfl
    · fin_cases j
      · exact hzy.trans hzy'.symm
      · change (h.2 1 : ZMod c) = h'.2 1
        linear_combination hsum.2 - hsum'.2 - hzy + hzy' - hym
      · exact hym
    · fin_cases j
      · change (h.2 0 : ZMod c) = h'.2 0
        linear_combination hsum.2 - hsum'.2 - hzy + hzy' - hym
      · exact hzy.trans hzy'.symm
      · exact hym
  apply Prod.ext
  · funext j
    exact integer_eq_of_box_residue (hbox h hh j).1 (hbox h' hh' j).1 hXsmall (hx j)
  · funext j
    exact integer_eq_of_box_residue (hbox h hh j).2 (hbox h' hh' j).2 hYsmall (hy j)

private theorem zero_endpoint_single_count {c : ℕ} [NeZero c]
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hXsmall : 2 * X < c) (hYsmall : 2 * Y < c)
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (S : Finset ReturnRows) (i : Fin 3) (hi : i = 0 ∨ i = 1)
    (hbox : ∀ h ∈ S, ∀ j, |(h.1 j : ℝ)| ≤ X ∧ |(h.2 j : ℝ)| ≤ Y)
    (hword : ∀ h ∈ S, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hzero : ∀ h ∈ S, (h.1 i, h.2 i) = (0 : Coordinate)) :
    (S.card : ℝ) ≤ 9*X*Y := by
  classical
  let box : Finset Coordinate :=
    (Finset.Icc (-⌊X⌋) ⌊X⌋) ×ˢ (Finset.Icc (-⌊Y⌋) ⌊Y⌋)
  have hmaps (h : ReturnRows) (hh : h ∈ S) : originalMiddle h ∈ box := by
    change (h.1 2, h.2 2) ∈ box
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      have hn : -(h.1 2) ≤ ⌊X⌋ := Int.le_floor.mpr (by
        push_cast
        linarith [abs_le.mp (hbox h hh 2).1])
      exact ⟨by omega, Int.le_floor.mpr (abs_le.mp (hbox h hh 2).1).2⟩
    · apply Finset.mem_Icc.mpr
      have hn : -(h.2 2) ≤ ⌊Y⌋ := Int.le_floor.mpr (by
        push_cast
        linarith [abs_le.mp (hbox h hh 2).2])
      exact ⟨by omega, Int.le_floor.mpr (abs_le.mp (hbox h hh 2).2).2⟩
  have hcard : S.card ≤ box.card := Finset.card_le_card_of_injOn originalMiddle hmaps
    (zero_endpoint_middle_injective hXsmall hYsmall a₁ a₂ ha₁ ha₂ S i hi hbox hword hzero)
  have hinterval (U : ℝ) (hU : 1 ≤ U) :
      ((Finset.Icc (-(⌊U⌋ : ℤ)) ⌊U⌋).card : ℝ) ≤ 3*U := by
    have hN : 0 ≤ ⌊U⌋ := Int.floor_nonneg.mpr (by linarith)
    have hc := Int.card_Icc_of_le (a := -(⌊U⌋ : ℤ)) (b := ⌊U⌋) (by omega)
    have hcR : ((Finset.Icc (-(⌊U⌋ : ℤ)) ⌊U⌋).card : ℝ) =
        (⌊U⌋ : ℝ)+1-(-(⌊U⌋ : ℤ)) := by exact_mod_cast hc
    push_cast at hcR
    linarith [Int.floor_le U]
  calc
    (S.card : ℝ) ≤ (box.card : ℝ) := by exact_mod_cast hcard
    _ = ((Finset.Icc (-(⌊X⌋ : ℤ)) ⌊X⌋).card : ℝ)*
        ((Finset.Icc (-(⌊Y⌋ : ℤ)) ⌊Y⌋).card : ℝ) := by
      dsimp only [box]
      rw [Finset.card_product, Nat.cast_mul]
    _ ≤ (3*X)*(3*Y) := mul_le_mul (hinterval X hX) (hinterval Y hY)
      (Nat.cast_nonneg _) (by linarith)
    _ = 9*X*Y := by ring

/-- Actual original returns with either physical endpoint zero contribute at
most eighteen times the literal area. The two zero-endpoint branches are
counted by their original integer middle pairs, without a chart hypothesis. -/
theorem actual_zero_endpoint_tuple_count {c : ℕ} [NeZero c]
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hXsmall : 2 * X < c) (hYsmall : 2 * Y < c)
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (T : Finset ReturnRows)
    (hbox : ∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y)
    (hword : ∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hzero : ∀ h ∈ T, (h.1 0, h.2 0) = (0 : Coordinate) ∨
      (h.1 1, h.2 1) = (0 : Coordinate)) : (T.card : ℝ) ≤ 18*X*Y := by
  classical
  let P := fun h : ReturnRows => (h.1 0, h.2 0) = (0 : Coordinate)
  let L := T.filter P
  let R := T.filter fun h => ¬ P h
  have hL := zero_endpoint_single_count hX hY hXsmall hYsmall a₁ a₂ ha₁ ha₂ L 0
    (Or.inl rfl)
    (fun h hh => hbox h (Finset.mem_filter.mp hh).1)
    (fun h hh => hword h (Finset.mem_filter.mp hh).1)
    (fun _ hh => (Finset.mem_filter.mp hh).2)
  have hR := zero_endpoint_single_count hX hY hXsmall hYsmall a₁ a₂ ha₁ ha₂ R 1
    (Or.inr rfl)
    (fun h hh => hbox h (Finset.mem_filter.mp hh).1)
    (fun h hh => hword h (Finset.mem_filter.mp hh).1)
    (fun h hh => (hzero h (Finset.mem_filter.mp hh).1).resolve_left
      (Finset.mem_filter.mp hh).2)
  have hsplit : (T.card : ℝ) = (L.card : ℝ)+(R.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := T) P).symm
  linarith

end
end D5.S3.Arith.CharacterSums.Original
