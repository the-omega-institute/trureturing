/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalUnitMiddleCount
   generality: G
   mirror-B: none(waiver:complete-original-unit-middle-count)
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Six actual original row subsets give the complete unit-middle count. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalNonunitShortest
import D5.S3.Arith.CharacterSums.PascadiOriginalUnitShortestShort
import D5.S3.Arith.CharacterSums.PascadiOriginalNonunitEndpoints
import D5.S3.Arith.CharacterSums.PascadiOriginalZeroEndpoints
import D5.S3.Arith.CharacterSums.PascadiOriginalRetainedCount

/-! All six subsets are filtered from the original integer rows. One actual
reduced basis is chosen for each occupied original middle pair and reused in
every branch. No shortness, unit-shortest, right-side or endpoint restriction
is an input to the resulting unit-middle estimate. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem primeCube_nonunit_dvd {p : ℕ} (hp : p.Prime) {z : ℤ}
    (hz : ¬ IsUnit (z : ZMod (p^3))) : (p : ℤ) ∣ z := by
  by_contra hn
  have hn' : ¬ p ∣ z.natAbs := by simpa only [← Int.natCast_dvd] using hn
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 3)).mpr hn'
  rw [Nat.cast_natAbs] at hu
  apply hz
  by_cases hpos : 0 ≤ z
  · simpa only [abs_of_nonneg hpos] using hu
  · have hneg : IsUnit (-(z : ZMod (p^3))) := by
      simpa only [abs_of_neg (lt_of_not_ge hpos), Int.cast_neg] using hu
    simpa only [neg_neg] using hneg.neg

private theorem primeCube_nonunit_reduction_zero {p : ℕ} (hp : p.Prime)
    {a : ZMod (p^3)} (ha : ¬ IsUnit a) :
    (ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)) a = 0 := by
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let ρ : ZMod (p^3) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  have hn : p ∣ a.val := by
    by_contra hn
    apply ha
    rw [← ZMod.natCast_zmod_val a]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 3)).mpr hn
  change ρ a = 0
  calc
    ρ a = ρ (a.val : ZMod (p^3)) := congrArg ρ (ZMod.natCast_zmod_val a).symm
    _ = (a.val : ZMod p) := map_natCast ρ a.val
    _ = 0 := (ZMod.natCast_eq_zero_iff a.val p).mpr hn

/-- Count every original unit-middle row. The six filtered subsets cover the
actual integer solution set; their counts use the same chosen reduced basis
at every occurrence of an original middle pair. Only three explicit numerical
long-chart separations remain, for later consumption of the original range. -/
theorem actual_unit_middle_tuple_count_seventh (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ)
      (a₁ a₂ : ZMod (p^3)) (T : Finset ReturnRows),
      1 ≤ X → X ≤ Y → 3*Y < (p : ℝ)^2 →
      (p : ℝ)^3 ≤ X*Y → X*Y ≤ (p : ℝ)^4 →
      0 < H → H^2 = X*Y → IsUnit a₁ → IsUnit a₂ →
      (∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y) →
      (∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
        (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1)) →
      (∀ h ∈ T, IsUnit (h.1 2 : ZMod (p^3)) ∧ IsUnit (h.2 2 : ZMod (p^3))) →
      seventhHeightConstant*(32*(X*Y/(p : ℝ)^3))^7 < (p : ℝ)^5 →
      (T.card : ℝ) ≤
        K*(p : ℝ)^ε*(X*Y*(1+(1+Real.log (2*p)/Real.log 2))+
          (X*Y)^2/(p : ℝ)^4) +
        Real.sqrt (K*(p : ℝ)^ε*(X*Y)^6/(p : ℝ)^15*
          (1+Real.log (2*p)/Real.log 2)) := by
  classical
  obtain ⟨Crhs, hCrhs, hunrhs⟩ := actual_long_nonunit_rhs_tuple_count ε hε
  obtain ⟨Cend, hCend, hendpoint⟩ := actual_nonunit_endpoint_tuple_count ε hε
  obtain ⟨Cret, hCret, hretained⟩ := actual_retained_long_tuple_count_seventh ε hε
  let K := 66048+148992+18+Crhs+Cend+Cret
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro p hp X Y H a₁ a₂ T hX1 hXY hsmall harea hupper hH hHsq ha₁ ha₂
    hbox hword hunit hgap
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hY1 : 1 ≤ Y := hX1.trans hXY
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hp23 : (p : ℝ)^2 ≤ (p : ℝ)^3 := pow_le_pow_right₀ hp1 (by decide : 2 ≤ 3)
  have hXsmallR : 2*X < (p : ℝ)^2 := by linarith
  have hYsmallR : 2*Y < (p : ℝ)^2 := by linarith
  have hXsmall : 2*X < (p^2 : ℕ) := by exact_mod_cast hXsmallR
  have hYcubeR : 2*Y < (p : ℝ)^3 := hYsmallR.trans_le hp23
  have hYsmall : 2*Y < (p^3 : ℕ) := by exact_mod_cast hYcubeR
  have hXcube : 2*X < (p^3 : ℕ) := (by linarith : 2*X ≤ 2*Y).trans_lt hYsmall
  have hYsquare : Y < (p : ℝ)^2 := by linarith
  have hAcut : X*Y < 2*(p : ℝ)^4 := by nlinarith [pow_pos hpR 4]
  have harea2 : (p : ℝ)^2 ≤ X*Y := hp23.trans harea
  have hHp : (p : ℝ) ≤ H :=
    (sq_le_sq₀ hpR.le hH.le).mp (by nlinarith [harea2, hHsq])
  have hp6 : ((p : ℝ)^3)^2 = (p : ℝ)^6 := by ring
  let s := T.image originalMiddle
  have hmid (h : ReturnRows) (hh : h ∈ T) : originalMiddle h ∈ s :=
    Finset.mem_image.mpr ⟨h, hh, rfl⟩
  have hB (wt : Coordinate) (hw : wt ∈ s) :
      Nonempty (ReducedMiddleBasis (p^3) wt.2 wt.1 X Y) := by
    obtain ⟨h, hh, hm⟩ := Finset.mem_image.mp hw
    apply exists_reduced_middle_basis (p^3) wt.2 wt.1 X Y (pow_pos hp.pos _) hX hY
    have hhunit := (hunit h hh).1
    have hm₁ : h.1 2 = wt.1 := congrArg Prod.fst hm
    simpa only [hm₁] using hhunit
  let B : ∀ wt : Coordinate, wt ∈ s → ReducedMiddleBasis (p^3) wt.2 wt.1 X Y :=
    fun wt hw => Classical.choice (hB wt hw)
  let R : Coordinate → Coordinate := fun wt => if hw : wt ∈ s then (B wt hw).R else 0
  have hR (wt : Coordinate) (hw : wt ∈ s) : R wt = (B wt hw).R := by
    simp only [R, dif_pos hw]
  let UR := fun h : ReturnRows => IsUnit ((R (originalMiddle h)).1 : ZMod (p^3))
  let Sh := fun h : ReturnRows => H^2*weightedSq X Y (R (originalMiddle h)) ≤ (p : ℝ)^6
  let Rh := fun h : ReturnRows =>
    IsUnit (1+a₁*a₂*(h.2 2 : ZMod (p^3))*(h.1 2 : ZMod (p^3)))
  let Ze := fun h : ReturnRows => (h.1 0, h.2 0) = (0 : Coordinate) ∨
    (h.1 1, h.2 1) = (0 : Coordinate)
  let En := fun h : ReturnRows => IsUnit (h.1 0 : ZMod (p^3)) ∧ IsUnit (h.1 1 : ZMod (p^3))
  let Bad := fun h : ReturnRows =>
    ((h.1 0, h.2 0) ≠ (0 : Coordinate) ∧ ¬ IsUnit (h.1 0 : ZMod (p^3))) ∨
    ((h.1 1, h.2 1) ≠ (0 : Coordinate) ∧ ¬ IsUnit (h.1 1 : ZMod (p^3)))
  let N := T.filter fun h => ¬ UR h
  let S := T.filter fun h => UR h ∧ Sh h
  let U := T.filter fun h => UR h ∧ ¬ Sh h ∧ ¬ Rh h
  let Z := T.filter Ze
  let D := T.filter fun h => Rh h ∧ Bad h
  let G := T.filter fun h => UR h ∧ ¬ Sh h ∧ Rh h ∧ En h
  have hN : (N.card : ℝ) ≤ 66048*(X*Y)^2/(p : ℝ)^4 := by
    let BN : ∀ h ∈ N, ReducedMiddleBasis (p^3) (h.2 2) (h.1 2) X Y :=
      fun h hh => B (originalMiddle h) (hmid h (Finset.mem_filter.mp hh).1)
    apply actual_nonunit_shortest_tuple_count hp hX hY hXY hH hHsq harea
      hXsmall hYsmall hYsquare a₁ a₂ ha₁ ha₂ N
      (fun h hh => hbox h (Finset.mem_filter.mp hh).1)
      (fun h hh => hword h (Finset.mem_filter.mp hh).1)
      (fun h hh => hunit h (Finset.mem_filter.mp hh).1) BN
    intro h hh
    apply primeCube_nonunit_dvd hp
    change ¬ IsUnit ((B (originalMiddle h) (hmid h (Finset.mem_filter.mp hh).1)).R.1 :
      ZMod (p^3))
    rw [← hR (originalMiddle h) (hmid h (Finset.mem_filter.mp hh).1)]
    exact (Finset.mem_filter.mp hh).2
  have hS : (S.card : ℝ) ≤ 148992*(X*Y)*(1+Real.log (2*p)/Real.log 2) := by
    apply actual_unit_shortest_short_tuple_count hp hX hY hH hHsq harea hXsmall hYsmall
      a₁ a₂ ha₁ ha₂ S (fun h => R (originalMiddle h))
      (fun h hh => hbox h (Finset.mem_filter.mp hh).1)
      (fun h hh => hword h (Finset.mem_filter.mp hh).1)
      (fun h hh => hunit h (Finset.mem_filter.mp hh).1)
    · intro h hh
      exact ⟨B (originalMiddle h) (hmid h (Finset.mem_filter.mp hh).1),
        (hR (originalMiddle h) (hmid h (Finset.mem_filter.mp hh).1)).symm⟩
    · intro h hh
      exact (Finset.mem_filter.mp hh).2.1
    · intro h hh
      exact (Finset.mem_filter.mp hh).2.2
  have hU : (U.card : ℝ) ≤ Crhs*(p : ℝ)^ε*(X*Y)^2/(p : ℝ)^4 := by
    apply hunrhs p hp X Y H hX hY hH hHsq harea hupper hXsmall hYsmall
      a₁ a₂ ha₁ ha₂ U
      (fun h hh => hbox h (Finset.mem_filter.mp hh).1)
      (fun h hh => hword h (Finset.mem_filter.mp hh).1)
      (fun h hh => hunit h (Finset.mem_filter.mp hh).1)
    · intro h hh
      exact primeCube_nonunit_reduction_zero hp (Finset.mem_filter.mp hh).2.2.2
    · intro h hh
      let Bh := B (originalMiddle h) (hmid h (Finset.mem_filter.mp hh).1)
      refine ⟨Bh, ?_⟩
      have hn : (p : ℝ)^6 < H^2*weightedSq X Y (R (originalMiddle h)) :=
        lt_of_not_ge (Finset.mem_filter.mp hh).2.2.1
      rw [hR (originalMiddle h) (hmid h (Finset.mem_filter.mp hh).1)] at hn
      apply (sq_le_sq₀ (by positivity : 0 ≤ (p : ℝ)^3)
        (by positivity : 0 ≤ H*Real.sqrt (weightedSq X Y Bh.R))).mp
      rw [mul_pow, Real.sq_sqrt (weightedSq_nonneg hX hY Bh.R), hp6]
      exact hn.le
  have hZ : (Z.card : ℝ) ≤ 18*X*Y :=
    actual_zero_endpoint_tuple_count hX1 hY1 hXcube hYsmall a₁ a₂ ha₁ ha₂ Z
      (fun h hh => hbox h (Finset.mem_filter.mp hh).1)
      (fun h hh => hword h (Finset.mem_filter.mp hh).1)
      (fun _ hh => (Finset.mem_filter.mp hh).2)
  have hD : (D.card : ℝ) ≤ Cend*(p : ℝ)^ε*(X*Y/p+(X*Y)^2/(p : ℝ)^4) := by
    apply hendpoint p hp X Y H hX hY hXY hYsmallR hH hHsq harea2 a₁ a₂ ha₁ ha₂ D
      (fun h hh => hbox h (Finset.mem_filter.mp hh).1)
      (fun h hh => hword h (Finset.mem_filter.mp hh).1)
    · intro h hh
      exact ⟨(hunit h (Finset.mem_filter.mp hh).1).2,
        (hunit h (Finset.mem_filter.mp hh).1).1⟩
    · intro h hh
      exact (Finset.mem_filter.mp hh).2.1
    · intro h hh
      exact (Finset.mem_filter.mp hh).2.2
  have hGsub : G.image originalMiddle ⊆ s :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  let BG : ∀ wt : Coordinate, wt ∈ G.image originalMiddle →
      ReducedMiddleBasis (p^3) wt.2 wt.1 X Y := fun wt hw => B wt (hGsub hw)
  have hBG (wt : Coordinate) (hw : wt ∈ G.image originalMiddle) : R wt = (BG wt hw).R :=
    hR wt (hGsub hw)
  have hG : (G.card : ℝ) ≤
      Cret*(p : ℝ)^ε*(X*Y+(X*Y/p)*(1+Real.log (2*p)/Real.log 2)+(X*Y)^2/(p : ℝ)^4) +
      Real.sqrt (Cret*(p : ℝ)^ε*(X*Y)^6/(p : ℝ)^15*(1+Real.log (2*p)/Real.log 2)) := by
    apply hretained p hp X Y H a₁ a₂ G BG hX1 hXY hsmall hAcut hH hHsq hHp ha₁ ha₂
      (fun h hh => hbox h (Finset.mem_filter.mp hh).1)
      (fun h hh => hword h (Finset.mem_filter.mp hh).1)
      (fun h hh => hunit h (Finset.mem_filter.mp hh).1)
      (fun _ hh => (Finset.mem_filter.mp hh).2.2.2.2)
    · intro wt hw
      obtain ⟨h, hh, hm⟩ := Finset.mem_image.mp hw
      have hn : (p : ℝ)^6 < H^2*weightedSq X Y (R (originalMiddle h)) :=
        lt_of_not_ge (Finset.mem_filter.mp hh).2.2.1
      rw [hm, hBG wt hw, hHsq] at hn
      simpa only [hp6] using hn
    · intro wt hw
      obtain ⟨h, hh, hm⟩ := Finset.mem_image.mp hw
      have hu : IsUnit ((R (originalMiddle h)).1 : ZMod (p^3)) :=
        (Finset.mem_filter.mp hh).2.1
      rw [hm, hBG wt hw] at hu
      exact hu
    · intro wt hw
      obtain ⟨h, hh, hm⟩ := Finset.mem_image.mp hw
      have hm₁ : h.1 2 = wt.1 := congrArg Prod.fst hm
      have hm₂ : h.2 2 = wt.2 := congrArg Prod.snd hm
      simpa only [Rh, hm₁, hm₂] using (Finset.mem_filter.mp hh).2.2.2.1
    · exact hgap
  have hcover : T ⊆ N ∪ S ∪ U ∪ Z ∪ D ∪ G := by
    intro h hh
    have hor : h ∈ N ∨ h ∈ S ∨ h ∈ U ∨ h ∈ Z ∨ h ∈ D ∨ h ∈ G := by
      by_cases hu : UR h
      · right
        by_cases hs : Sh h
        · left
          exact Finset.mem_filter.mpr ⟨hh, hu, hs⟩
        · right
          by_cases hrhs : Rh h
          · right
            by_cases hz : Ze h
            · left
              exact Finset.mem_filter.mpr ⟨hh, hz⟩
            · right
              by_cases he : En h
              · right
                exact Finset.mem_filter.mpr ⟨hh, hu, hs, hrhs, he⟩
              · left
                apply Finset.mem_filter.mpr
                refine ⟨hh, hrhs, ?_⟩
                have hz' : (h.1 0, h.2 0) ≠ (0 : Coordinate) ∧
                    (h.1 1, h.2 1) ≠ (0 : Coordinate) := not_or.mp hz
                by_cases ha : IsUnit (h.1 0 : ZMod (p^3))
                · exact Or.inr ⟨hz'.2, fun hb => he ⟨ha, hb⟩⟩
                · exact Or.inl ⟨hz'.1, ha⟩
          · left
            exact Finset.mem_filter.mpr ⟨hh, hu, hs, hrhs⟩
      · left
        exact Finset.mem_filter.mpr ⟨hh, hu⟩
    simpa only [Finset.mem_union, or_assoc] using hor
  have hcard : T.card ≤ N.card+S.card+U.card+Z.card+D.card+G.card := by
    have hc := Finset.card_le_card hcover
    have h₁ := Finset.card_union_le N S
    have h₂ := Finset.card_union_le (N ∪ S) U
    have h₃ := Finset.card_union_le (N ∪ S ∪ U) Z
    have h₄ := Finset.card_union_le (N ∪ S ∪ U ∪ Z) D
    have h₅ := Finset.card_union_le (N ∪ S ∪ U ∪ Z ∪ D) G
    omega
  let A := X*Y
  let L := 1+Real.log (2*p)/Real.log 2
  let P := (p : ℝ)^ε
  let F := A*(1+L)+A^2/(p : ℝ)^4
  let W := P*F
  have hA : 0 ≤ A := (mul_pos hX hY).le
  have hP : 1 ≤ P := Real.one_le_rpow hp1 hε.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (2*p) :=
    Real.log_nonneg (by nlinarith only [hp1] : (1 : ℝ) ≤ 2*p)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hFW : F ≤ W := by
    change F ≤ P*F
    calc
      F = 1*F := (one_mul F).symm
      _ ≤ P*F := mul_le_mul_of_nonneg_right hP hF
  have hAL : 0 ≤ A*L := mul_nonneg hA hL
  have hV : 0 ≤ A^2/(p : ℝ)^4 := div_nonneg (sq_nonneg A) (pow_nonneg hpR.le 4)
  have hAF : A ≤ F := by
    dsimp only [F]
    nlinarith only [hAL, hV]
  have hALF : A*L ≤ F := by
    dsimp only [F]
    nlinarith only [hA, hV]
  have hA2F : A^2/(p : ℝ)^4 ≤ F := by
    dsimp only [F]
    nlinarith only [hA, hAL]
  have hAp : A/p ≤ A := by
    calc
      A/p ≤ A/1 := div_le_div_of_nonneg_left hA zero_lt_one hp1
      _ = A := div_one A
  have hDF : A/p+A^2/(p : ℝ)^4 ≤ F := by
    dsimp only [F]
    nlinarith only [hAp, hAL]
  have hGF : A+(A/p)*L+A^2/(p : ℝ)^4 ≤ F := by
    have hh := mul_le_mul_of_nonneg_right hAp hL
    dsimp only [F]
    nlinarith only [hh]
  have hNW : (N.card : ℝ) ≤ 66048*W := by
    calc
      _ ≤ 66048*A^2/(p : ℝ)^4 := hN
      _ = 66048*(A^2/(p : ℝ)^4) := by ring
      _ ≤ 66048*W := mul_le_mul_of_nonneg_left (hA2F.trans hFW) (by norm_num)
  have hSW : (S.card : ℝ) ≤ 148992*W := by
    calc
      _ ≤ 148992*A*L := hS
      _ = 148992*(A*L) := by ring
      _ ≤ 148992*W := mul_le_mul_of_nonneg_left (hALF.trans hFW) (by norm_num)
  have hUW : (U.card : ℝ) ≤ Crhs*W := by
    calc
      _ ≤ Crhs*P*A^2/(p : ℝ)^4 := hU
      _ = Crhs*P*(A^2/(p : ℝ)^4) := by ring
      _ ≤ Crhs*P*F := mul_le_mul_of_nonneg_left hA2F (by positivity)
      _ = _ := by dsimp only [W]; ring
  have hZW : (Z.card : ℝ) ≤ 18*W := by
    calc
      _ ≤ 18*A := by simpa only [A, mul_assoc] using hZ
      _ ≤ 18*W := mul_le_mul_of_nonneg_left (hAF.trans hFW) (by norm_num)
  have hDW : (D.card : ℝ) ≤ Cend*W := by
    calc
      _ ≤ Cend*P*(A/p+A^2/(p : ℝ)^4) := hD
      _ ≤ Cend*P*F := mul_le_mul_of_nonneg_left hDF (by positivity)
      _ = _ := by dsimp only [W]; ring
  have hCG : Cret ≤ K := by dsimp only [K]; linarith only [hCrhs, hCend]
  have hGW : (G.card : ℝ) ≤ Cret*W+Real.sqrt (K*P*A^6/(p : ℝ)^15*L) := by
    apply hG.trans
    apply add_le_add
    · calc
        _ ≤ Cret*P*F := mul_le_mul_of_nonneg_left hGF (by positivity)
        _ = _ := by dsimp only [W]; ring
    · apply Real.sqrt_le_sqrt
      calc
        _ = Cret*(P*A^6/(p : ℝ)^15*L) := by ring
        _ ≤ K*(P*A^6/(p : ℝ)^15*L) := mul_le_mul_of_nonneg_right hCG (by positivity)
        _ = _ := by ring
  have hcardR : (T.card : ℝ) ≤
      (N.card : ℝ)+(S.card : ℝ)+(U.card : ℝ)+(Z.card : ℝ)+(D.card : ℝ)+(G.card : ℝ) := by
    exact_mod_cast hcard
  change (T.card : ℝ) ≤ K*P*F+Real.sqrt (K*P*A^6/(p : ℝ)^15*L)
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hNW hSW) hUW) hZW) hDW) hGW
  apply hcardR.trans (hsum.trans_eq ?_)
  dsimp only [K, W]
  ring

/-- Preserve the original numerical-cutoff statement. -/
theorem actual_unit_middle_tuple_count (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : ℕ) (hp : p.Prime) (M X Y H : ℝ)
      (a₁ a₂ : ZMod (p^3)) (T : Finset ReturnRows),
      1 ≤ X → X ≤ Y → 3*Y < (p : ℝ)^2 →
      (p : ℝ)^3 ≤ X*Y → X*Y ≤ (p : ℝ)^4 →
      0 < H → H^2 = X*Y → IsUnit a₁ → IsUnit a₂ →
      (∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y) →
      (∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
        (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1)) →
      (∀ h ∈ T, IsUnit (h.1 2 : ZMod (p^3)) ∧ IsUnit (h.2 2 : ZMod (p^3))) →
      (32*(X*Y/(p : ℝ)^3))^5 ≤ M^5*(p : ℝ)^3 →
      (10368*(3 : ℝ)^9)^5*M^35 < (p : ℝ)^4 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (T.card : ℝ) ≤
        K*(p : ℝ)^ε*(X*Y*(1+(1+Real.log (2*p)/Real.log 2))+
          (X*Y)^2/(p : ℝ)^4) +
        Real.sqrt (K*(p : ℝ)^ε*(X*Y)^6/(p : ℝ)^15*
          (1+Real.log (2*p)/Real.log 2)) := by
  obtain ⟨K, hK, hcount⟩ := actual_unit_middle_tuple_count_seventh ε hε
  refine ⟨K, hK, ?_⟩
  intro p hp M X Y H a₁ a₂ T hX1 hXY hsmall harea hupper hH hHsq ha₁ ha₂
    hbox hword hunit hcap _hsepR hsepQ
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hB : 1 ≤ 32*(X*Y/(p : ℝ)^3) := by
    have hh : 1 ≤ X*Y/(p : ℝ)^3 := (le_div_iff₀ (pow_pos hpR 3)).mpr (by simpa using harea)
    linarith only [hh]
  have hgap := seventh_height_gap_of_old_cutoffs (32*(X*Y/(p : ℝ)^3)) M (p : ℝ)
    hpR hB hcap hsepQ
  exact hcount p hp X Y H a₁ a₂ T hX1 hXY hsmall harea hupper hH hHsq ha₁ ha₂
    hbox hword hunit hgap

end
end D5.S3.Arith.CharacterSums.Original
