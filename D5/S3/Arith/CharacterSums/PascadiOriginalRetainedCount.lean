/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalRetainedCount
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalRetainedCount
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Actual retained original rows obey the averaged long-chart bound. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalRetainedRows
import D5.S3.Arith.CharacterSums.PascadiOriginalBadDegreeAverage

/-! The original rows themselves supply every moment fiber. Their actual
bad degrees are averaged before applying the finite second-moment bound. -/

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem parameter_box_count {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (s : Finset Coordinate) (hbox : ∀ wt ∈ s, wt ∈ literalBox X Y) :
    (s.card : ℝ) ≤ 9*(X*Y) := by
  let F := (Finset.Icc (-⌊X⌋) ⌊X⌋) ×ˢ (Finset.Icc (-⌊Y⌋) ⌊Y⌋)
  have hsub : s ⊆ F := by
    intro wt hw
    have hb := hbox wt hw
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      have hlo : -wt.1 ≤ ⌊X⌋ := Int.le_floor.mpr (by
        push_cast
        linarith [(abs_le.mp hb.1).1])
      exact ⟨by omega, Int.le_floor.mpr (abs_le.mp hb.1).2⟩
    · apply Finset.mem_Icc.mpr
      have hlo : -wt.2 ≤ ⌊Y⌋ := Int.le_floor.mpr (by
        push_cast
        linarith [(abs_le.mp hb.2).1])
      exact ⟨by omega, Int.le_floor.mpr (abs_le.mp hb.2).2⟩
  have hinterval (U : ℝ) (hU : 1 ≤ U) :
      ((Finset.Icc (-⌊U⌋) ⌊U⌋).card : ℝ) ≤ 3*U := by
    have hfloor : 0 ≤ ⌊U⌋ := Int.floor_nonneg.mpr (by linarith)
    have hh := Int.card_Icc_of_le (a := -⌊U⌋) (b := ⌊U⌋) (by omega)
    have he : ((Finset.Icc (-⌊U⌋) ⌊U⌋).card : ℝ) =
        (⌊U⌋ : ℝ)+1-(-⌊U⌋ : ℤ) := by exact_mod_cast hh
    push_cast at he
    linarith [Int.floor_le U]
  calc
    (s.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = ((Finset.Icc (-⌊X⌋) ⌊X⌋).card : ℝ)*
        ((Finset.Icc (-⌊Y⌋) ⌊Y⌋).card : ℝ) := by
      dsimp only [F]
      rw [Finset.card_product, Nat.cast_mul]
    _ ≤ (3*X)*(3*Y) := mul_le_mul (hinterval X hX) (hinterval Y hY)
      (Nat.cast_nonneg _) (by linarith)
    _ = 9*(X*Y) := by ring

/-- The complete retained long-chart count for actual original tuples.
Actual coordinate reconstruction, parameter cardinality and the bad-degree
average are proved internally. Only the explicit numerical separation
conditions remain to be supplied from the original asymptotic range. -/
theorem actual_retained_long_tuple_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (M X Y H : ℝ)
      (a₁ a₂ : ZMod (p^3)) (T : Finset ReturnRows)
      (B : ∀ wt : Coordinate, wt ∈ T.image originalMiddle →
        ReducedMiddleBasis (p^3) wt.2 wt.1 X Y),
      1 ≤ X → X ≤ Y → 3*Y < (p : ℝ)^2 → X*Y < 2*(p : ℝ)^4 →
      0 < H → H^2 = X*Y → (p : ℝ) ≤ H → IsUnit a₁ → IsUnit a₂ →
      (∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y) →
      (∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
        (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1)) →
      (∀ h ∈ T, IsUnit (h.1 2 : ZMod (p^3)) ∧ IsUnit (h.2 2 : ZMod (p^3))) →
      (∀ h ∈ T, IsUnit (h.1 0 : ZMod (p^3)) ∧ IsUnit (h.1 1 : ZMod (p^3))) →
      (∀ wt (hw : wt ∈ T.image originalMiddle),
        (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (B wt hw).R) →
      (∀ wt (hw : wt ∈ T.image originalMiddle), IsUnit ((B wt hw).R.1 : ZMod (p^3))) →
      (∀ wt ∈ T.image originalMiddle,
        IsUnit (1+a₁*a₂*(wt.2 : ZMod (p^3))*(wt.1 : ZMod (p^3)))) →
      (32*(X*Y/(p : ℝ)^3))^5 ≤ M^5*(p : ℝ)^3 →
      (10368*(3 : ℝ)^9)^5*M^35 < (p : ℝ)^4 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (T.card : ℝ) ≤
        C*(p : ℝ)^ε*(X*Y+(X*Y/p)*(1+Real.log (2*p)/Real.log 2)+
          (X*Y)^2/(p : ℝ)^4) +
        Real.sqrt (C*(p : ℝ)^ε*(X*Y)^6/(p : ℝ)^15*
          (1+Real.log (2*p)/Real.log 2)) := by
  classical
  obtain ⟨C₁, hC₁, hrows⟩ := actual_retained_rows_dyadic_count ε hε
  obtain ⟨C₂, hC₂, haverage⟩ := actual_long_bad_degree_average ε hε
  refine ⟨2*C₂+9*C₁, by positivity, ?_⟩
  intro p hp M X Y H a₁ a₂ T B hX1 hXY hsmall hAcut hH hHsq hHp ha₁ ha₂
    hbox hword hunit hendunit hlong hr hrhs hcap hlargeR hlargeQ
  let A := X*Y
  let L := 1+Real.log (2*p)/Real.log 2
  let F := A+(A/p)*L+A^2/(p : ℝ)^4
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hY1 : 1 ≤ Y := hX1.trans hXY
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hA : 0 < A := mul_pos hX hY
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (2*p) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 2*p)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hp23 : (p : ℝ)^2 ≤ (p : ℝ)^3 := pow_le_pow_right₀ hp1 (by decide : 2 ≤ 3)
  have hYcube : 2*Y < (p : ℝ)^3 := (by linarith : 2*Y < (p : ℝ)^2).trans_le hp23
  obtain ⟨q, RV, E, hRV, hanchor, himage, hinj, heword, heunit, hebox, hcount, hbound⟩ :=
    hrows p hp X Y H a₁ a₂ T B hX hXY hsmall hH hHsq ha₁ ha₂
      hbox hword hunit hendunit hlong hr
  have hsbox : ∀ wt ∈ T.image originalMiddle, wt ∈ literalBox X Y := by
    intro wt hw
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hw
    exact hbox h hh 2
  have hsunit : ∀ wt ∈ T.image originalMiddle,
      IsUnit (wt.2 : ZMod (p^3)) ∧ IsUnit (wt.1 : ZMod (p^3)) := by
    intro wt hw
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨(hunit h hh).2, (hunit h hh).1⟩
  have hred : ∀ wt ∈ T.image originalMiddle,
      ∃ B' : ReducedMiddleBasis (p^3) wt.2 wt.1 X Y,
        B'.R = (RV wt).1 ∧ B'.V = (RV wt).2 := by
    intro wt hw
    refine ⟨B wt hw, ?_, ?_⟩ <;> rw [hRV wt hw]
  have hlong' : ∀ wt ∈ T.image originalMiddle,
      (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (RV wt).1 := by
    intro wt hw
    rw [hRV wt hw]
    exact hlong wt hw
  have hr' : ∀ wt ∈ T.image originalMiddle,
      IsUnit ((RV wt).1.1 : ZMod (p^3)) := by
    intro wt hw
    rw [hRV wt hw]
    exact hr wt hw
  have hD : (∑ wt ∈ T.image originalMiddle,
      (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ)) ≤
      C₂*(p : ℝ)^ε*F := by
    exact haverage p hp M X Y H a₁ a₂ q RV (T.image originalMiddle) E
      hX1 hXY hYcube hAcut hH hHsq hHp ha₁ ha₂ hsbox hred hanchor hlong' hr'
      hsunit hrhs heword heunit hebox hcap hlargeR hlargeQ
  have hcard : ((T.image originalMiddle).card : ℝ) ≤ 9*A :=
    parameter_box_count hX1 hY1 _ hsbox
  have hdefect : 2*(∑ wt ∈ T.image originalMiddle,
      (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ)) ≤
      (2*C₂+9*C₁)*(p : ℝ)^ε*F := by
    calc
      _ ≤ 2*(C₂*(p : ℝ)^ε*F) := mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = (2*C₂)*((p : ℝ)^ε*F) := by ring
      _ ≤ (2*C₂+9*C₁)*((p : ℝ)^ε*F) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have harg : ((T.image originalMiddle).card : ℝ)*C₁*(p : ℝ)^ε*
      (A/(p : ℝ)^3)^5*L ≤ (2*C₂+9*C₁)*(p : ℝ)^ε*A^6/(p : ℝ)^15*L := by
    calc
      _ = ((T.image originalMiddle).card : ℝ)*(C₁*(p : ℝ)^ε*(A/(p : ℝ)^3)^5*L) := by ring
      _ ≤ (9*A)*(C₁*(p : ℝ)^ε*(A/(p : ℝ)^3)^5*L) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (9*C₁)*((p : ℝ)^ε*A^6/(p : ℝ)^15*L) := by
        field_simp [hpR.ne'] <;> ring
      _ ≤ (2*C₂+9*C₁)*((p : ℝ)^ε*A^6/(p : ℝ)^15*L) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  exact hbound.trans (add_le_add hdefect (Real.sqrt_le_sqrt harg))

end
end D5.S3.Arith.CharacterSums.Original
