/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalNonunitEndpoints
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalNonunitEndpoints
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Actual original rows with a nonzero nonunit endpoint obey the outer error bound. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalNonunitIncidence
import D5.S3.Arith.CharacterSums.PascadiOriginalLinearFibers

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private def firstEndpointIncidence (h : ReturnRows) : Coordinate × Coordinate :=
  ((h.1 2, h.2 2), (h.1 0, h.2 0))

private theorem original_rows_first_endpoint_injective {c : ℕ} [NeZero c]
    {X Y : ℝ} (hXsmall : 2*X < c) (hYsmall : 2*Y < c)
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (h h' : ReturnRows)
    (hb : ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y)
    (hb' : ∀ i, |(h'.1 i : ℝ)| ≤ X ∧ |(h'.2 i : ℝ)| ≤ Y)
    (he : sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (he' : sixReturnWord a₁ a₂ (h'.1 0) (h'.2 2) (h'.1 1)
      (h'.2 0) (h'.1 2) (h'.2 1) = scalarReturn (-1))
    (hw : IsUnit (h.1 2 : ZMod c))
    (hk : IsUnit (1+a₁*a₂*(h.2 2 : ZMod c)*(h.1 2 : ZMod c)))
    (hcode : firstEndpointIncidence h = firstEndpointIncidence h') : h = h' := by
  have hm := congrArg Prod.fst hcode
  have hp := congrArg Prod.snd hcode
  have hew : h.1 2 = h'.1 2 := congrArg Prod.fst hm
  have het : h.2 2 = h'.2 2 := congrArg Prod.snd hm
  have hea : h.1 0 = h'.1 0 := congrArg Prod.fst hp
  have hed : h.2 0 = h'.2 0 := congrArg Prod.snd hp
  have hminus := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp he
  have hminus' := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp he'
  rw [← hew, ← het, ← hea, ← hed] at hminus'
  have hbmod := unit_right_side_second_residue hminus hminus' hk
  have heb : h.1 1 = h'.1 1 :=
    integer_eq_of_box_residue (hb 1).1 (hb' 1).1 hXsmall hbmod
  have hvmod : (h.2 1 : ZMod c) = h'.2 1 := by
    apply hw.mul_left_cancel
    have hh := hminus.2.2.2
    have hh' := hminus'.2.2.2
    rw [← heb] at hh'
    exact hh.trans hh'.symm
  have hev : h.2 1 = h'.2 1 :=
    integer_eq_of_box_residue (hb 1).2 (hb' 1).2 hYsmall hvmod
  apply Prod.ext
  · funext i
    fin_cases i
    · exact hea
    · exact heb
    · exact hew
  · funext i
    fin_cases i
    · exact hed
    · exact hev
    · exact het

private theorem first_nonunit_original_rows_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ),
      0 < X → 0 < Y → X ≤ Y → 2*Y < (p : ℝ)^2 →
      0 < H → H^2 = X*Y → (p : ℝ)^2 ≤ X*Y →
      ∀ (a₁ a₂ : ZMod (p^3)), IsUnit a₁ → IsUnit a₂ → ∀ T : Finset ReturnRows,
      (∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y) →
      (∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
        (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1)) →
      (∀ h ∈ T, IsUnit (h.2 2 : ZMod (p^3)) ∧ IsUnit (h.1 2 : ZMod (p^3))) →
      (∀ h ∈ T, IsUnit (1+a₁*a₂*(h.2 2 : ZMod (p^3))*(h.1 2 : ZMod (p^3)))) →
      (∀ h ∈ T, (h.1 0, h.2 0) ≠ (0 : Coordinate) ∧
        ¬ IsUnit (h.1 0 : ZMod (p^3))) →
      (T.card : ℝ) ≤ C*(p : ℝ)^ε*(X*Y/p+(X*Y)^2/(p : ℝ)^4) := by
  classical
  obtain ⟨C, hC, hinc⟩ := actual_nonunit_endpoint_incidence_count ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp X Y H hX hY hXY hYsmall hH hHsq harea a₁ a₂ ha₁ ha₂
    T hbox hword hunit hrhs hbad
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hYcube : 2*Y < (p^3 : ℕ) := by
    have hh := hYsmall.trans_le (pow_le_pow_right₀ hp1 (by decide : 2 ≤ 3))
    exact_mod_cast hh
  have hXcube : 2*X < (p^3 : ℕ) := (by linarith : 2*X ≤ 2*Y).trans_lt hYcube
  let I := T.image firstEndpointIncidence
  have hcard : T.card ≤ I.card := by
    apply Finset.card_le_card_of_injOn firstEndpointIncidence
    · intro h hh
      exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
    · intro h hh h' hh' he
      exact original_rows_first_endpoint_injective hXcube hYcube a₁ a₂ ha₁ ha₂
        h h' (hbox h hh) (hbox h' hh') (hword h hh) (hword h' hh')
        (hunit h hh).2 (hrhs h hh) he
  have hIbox (i : Coordinate × Coordinate) (hi : i ∈ I) :
      i.1 ∈ literalBox X Y ∧ i.2 ∈ literalBox X Y := by
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨hbox h hh 2, hbox h hh 0⟩
  have hIunit (i : Coordinate × Coordinate) (hi : i ∈ I) :
      IsUnit (i.1.2 : ZMod (p^3)) ∧ IsUnit (i.1.1 : ZMod (p^3)) := by
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
    exact hunit h hh
  have hImem (i : Coordinate × Coordinate) (hi : i ∈ I) :
      i.2 ∈ middleLattice (p^3) i.1.2 i.1.1 := by
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
    have he := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp (hword h hh)
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [firstEndpointIncidence, Int.cast_sub, Int.cast_mul] using
      sub_eq_zero.mpr he.2.2.1
  have hIbad (i : Coordinate × Coordinate) (hi : i ∈ I) :
      i.2 ≠ 0 ∧ ¬ IsUnit (i.2.1 : ZMod (p^3)) := by
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
    exact hbad h hh
  exact (show (T.card : ℝ) ≤ (I.card : ℝ) by exact_mod_cast hcard).trans
    (hinc p hp X Y H hX hY hXY hYsmall hH hHsq harea I hIbox hIunit hImem hIbad)

private def swapOriginalEndpoints (h : ReturnRows) : ReturnRows :=
  (fun i => h.1 (Equiv.swap (0 : Fin 3) 1 i),
    fun i => h.2 (Equiv.swap (0 : Fin 3) 1 i))

private theorem swapOriginalEndpoints_involutive : Function.Involutive swapOriginalEndpoints := by
  intro h
  apply Prod.ext <;> funext i <;> simp [swapOriginalEndpoints]

private theorem swapOriginalEndpoints_word {c : ℕ} [NeZero c]
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂) (h : ReturnRows)
    (he : sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1)) :
    sixReturnWord a₁ a₂ ((swapOriginalEndpoints h).1 0) ((swapOriginalEndpoints h).2 2)
      ((swapOriginalEndpoints h).1 1) ((swapOriginalEndpoints h).2 0)
      ((swapOriginalEndpoints h).1 2) ((swapOriginalEndpoints h).2 1) =
        scalarReturn (-1) := by
  have hh := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp he
  apply (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mpr
  simp only [swapOriginalEndpoints, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
  refine ⟨?_, ?_, hh.2.2.2, hh.2.2.1⟩
  · linear_combination hh.1
  · linear_combination hh.2.1

/-- All actual original rows in the unit-middle, unit-right-side chart with
either nonzero endpoint nonunit have the outer bound. No longness or unit
shortest-vector assumption is needed for this stronger incidence estimate. -/
theorem actual_nonunit_endpoint_tuple_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ),
      0 < X → 0 < Y → X ≤ Y → 2*Y < (p : ℝ)^2 →
      0 < H → H^2 = X*Y → (p : ℝ)^2 ≤ X*Y →
      ∀ (a₁ a₂ : ZMod (p^3)), IsUnit a₁ → IsUnit a₂ → ∀ T : Finset ReturnRows,
      (∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y) →
      (∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
        (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1)) →
      (∀ h ∈ T, IsUnit (h.2 2 : ZMod (p^3)) ∧ IsUnit (h.1 2 : ZMod (p^3))) →
      (∀ h ∈ T, IsUnit (1+a₁*a₂*(h.2 2 : ZMod (p^3))*(h.1 2 : ZMod (p^3)))) →
      (∀ h ∈ T, ((h.1 0, h.2 0) ≠ (0 : Coordinate) ∧
        ¬ IsUnit (h.1 0 : ZMod (p^3))) ∨
        ((h.1 1, h.2 1) ≠ (0 : Coordinate) ∧ ¬ IsUnit (h.1 1 : ZMod (p^3)))) →
      (T.card : ℝ) ≤ C*(p : ℝ)^ε*(X*Y/p+(X*Y)^2/(p : ℝ)^4) := by
  classical
  obtain ⟨C, hC, hfirst⟩ := first_nonunit_original_rows_count ε hε
  refine ⟨2*C, by positivity, ?_⟩
  intro p hp X Y H hX hY hXY hYsmall hH hHsq harea a₁ a₂ ha₁ ha₂
    T hbox hword hunit hrhs hbad
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let P := fun h : ReturnRows => (h.1 0, h.2 0) ≠ (0 : Coordinate) ∧
    ¬ IsUnit (h.1 0 : ZMod (p^3))
  let L := T.filter P
  let R := T.filter fun h => ¬ P h
  let S := R.image swapOriginalEndpoints
  have hL := hfirst p hp X Y H hX hY hXY hYsmall hH hHsq harea a₁ a₂ ha₁ ha₂ L
    (fun h hh => hbox h (Finset.mem_filter.mp hh).1)
    (fun h hh => hword h (Finset.mem_filter.mp hh).1)
    (fun h hh => hunit h (Finset.mem_filter.mp hh).1)
    (fun h hh => hrhs h (Finset.mem_filter.mp hh).1)
    (fun _ hh => (Finset.mem_filter.mp hh).2)
  have hSbox (h : ReturnRows) (hh : h ∈ S) :
      ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y := by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    intro i
    exact hbox g (Finset.mem_filter.mp hg).1 (Equiv.swap (0 : Fin 3) 1 i)
  have hSword (h : ReturnRows) (hh : h ∈ S) :
      sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
        (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1) := by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    exact swapOriginalEndpoints_word a₁ a₂ ha₁ ha₂ g (hword g (Finset.mem_filter.mp hg).1)
  have hSunit (h : ReturnRows) (hh : h ∈ S) :
      IsUnit (h.2 2 : ZMod (p^3)) ∧ IsUnit (h.1 2 : ZMod (p^3)) := by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    simpa only [swapOriginalEndpoints, Equiv.swap_apply_of_ne_of_ne
      (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
      using hunit g (Finset.mem_filter.mp hg).1
  have hSrhs (h : ReturnRows) (hh : h ∈ S) :
      IsUnit (1+a₁*a₂*(h.2 2 : ZMod (p^3))*(h.1 2 : ZMod (p^3))) := by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    simpa only [swapOriginalEndpoints, Equiv.swap_apply_of_ne_of_ne
      (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
      using hrhs g (Finset.mem_filter.mp hg).1
  have hSbad (h : ReturnRows) (hh : h ∈ S) :
      (h.1 0, h.2 0) ≠ (0 : Coordinate) ∧ ¬ IsUnit (h.1 0 : ZMod (p^3)) := by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hg, hn⟩ := Finset.mem_filter.mp hg
    have hb := (hbad g hg).resolve_left hn
    simpa [swapOriginalEndpoints] using hb
  have hS := hfirst p hp X Y H hX hY hXY hYsmall hH hHsq harea a₁ a₂ ha₁ ha₂ S
    hSbox hSword hSunit hSrhs hSbad
  have hRS : R.card = S.card :=
    (Finset.card_image_of_injective R swapOriginalEndpoints_involutive.injective).symm
  have hcard : (T.card : ℝ) = (L.card : ℝ)+(R.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := T) P).symm
  rw [hRS] at hcard
  nlinarith

end
end D5.S3.Arith.CharacterSums.Original
