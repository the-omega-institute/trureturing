/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalNonunitIncidence
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalNonunitIncidence
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Actual nonzero nonunit endpoint incidences cost A/p plus A squared over p fourth. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalShortWeight

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem weightedSq_rescale (X Y r : ℝ) (hr : r ≠ 0) (z : Coordinate) :
    weightedSq (r*X) (r*Y) z = weightedSq X Y z := by
  simp only [weightedSq, mul_div_mul_left _ _ hr]

private theorem weightedDot_rescale (X Y r : ℝ) (hr : r ≠ 0) (z v : Coordinate) :
    weightedDot (r*X) (r*Y) z v = weightedDot X Y z v := by
  simp only [weightedDot, mul_div_mul_left _ _ hr]

private def rescaleReduced {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y) (r : ℝ) (hr : r ≠ 0) :
    ReducedMiddleBasis c t w (r*X) (r*Y) where
  toMiddleBasis := B.toMiddleBasis
  shortest := by
    simp only [weightedSq_rescale X Y r hr]
    exact B.shortest
  centered := by
    simpa only [weightedSq_rescale X Y r hr, weightedDot_rescale X Y r hr]
      using B.centered

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

private def normalizedPoint (p : ℕ) (z : Coordinate) : Coordinate :=
  (z.1/(p : ℤ), z.2/(p : ℤ))

private theorem nonunit_endpoint_normalization {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y : ℝ} (hw : IsUnit (w : ZMod (p^3)))
    {z : Coordinate} (hmem : z ∈ middleLattice (p^3) t w)
    (hbox : z ∈ literalBox X Y) (hzero : z ≠ 0)
    (hbad : ¬ IsUnit (z.1 : ZMod (p^3))) :
    let v := normalizedPoint p z
    (p : ℤ)*v.1 = z.1 ∧ (p : ℤ)*v.2 = z.2 ∧ v ≠ 0 ∧
      v ∈ middleLattice (p^2) t w ∧ v ∈ literalBox (X/p) (Y/p) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpa := primeCube_nonunit_dvd hp hbad
  have hpd : (p : ℤ) ∣ z.2 := by
    let f : ZMod (p^3) →+* ZMod p :=
      ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
    have hwu : IsUnit (w : ZMod p) := by
      simpa only [map_intCast] using hw.map f
    have hpc : (p : ℤ) ∣ (p^3 : ℕ) := by
      exact_mod_cast dvd_pow_self p (by decide : 3 ≠ 0)
    have hd : (p : ℤ) ∣ w*z.2-t*z.1 := dvd_trans hpc hmem
    apply integer_unit_cancel_dvd hwu
    convert dvd_add hd (dvd_mul_of_dvd_right hpa t) using 1 <;> ring
  let v := normalizedPoint p z
  have hv₁ : (p : ℤ)*v.1 = z.1 := by
    simpa only [v, normalizedPoint, mul_comm] using Int.ediv_mul_cancel hpa
  have hv₂ : (p : ℤ)*v.2 = z.2 := by
    simpa only [v, normalizedPoint, mul_comm] using Int.ediv_mul_cancel hpd
  have hv0 : v ≠ 0 := by
    intro hz
    apply hzero
    apply Prod.ext
    · simpa only [hz, Prod.fst_zero, mul_zero] using hv₁.symm
    · simpa only [hz, Prod.snd_zero, mul_zero] using hv₂.symm
  have hvmem : v ∈ middleLattice (p^2) t w := by
    have hh : (p : ℤ)*(p : ℤ)^2 ∣ (p : ℤ)*(w*v.2-t*v.1) := by
      have he : w*z.2-t*z.1 = (p : ℤ)*(w*v.2-t*v.1) := by
        rw [← hv₁, ← hv₂]
        ring
      have hd : (p : ℤ)^3 ∣ (p : ℤ)*(w*v.2-t*v.1) := by
        simpa only [middleLattice, Set.mem_setOf_eq, Nat.cast_pow, he] using hmem
      convert hd using 1 <;> ring
    simpa only [middleLattice, Set.mem_setOf_eq, Nat.cast_pow] using
      (mul_dvd_mul_iff_left hpZ).mp hh
  have hb (a n : ℤ) (U : ℝ) (he : (p : ℤ)*n = a) (ha : |(a : ℝ)| ≤ U) :
      |(n : ℝ)| ≤ U/p := by
    have heR : (p : ℝ)*(n : ℝ) = (a : ℝ) := by exact_mod_cast he
    rw [← heR, abs_mul, abs_of_pos hpR] at ha
    exact (le_div_iff₀ hpR).mpr (by simpa only [mul_comm] using ha)
  exact ⟨hv₁, hv₂, hv0, hvmem, hb _ _ _ hv₁ hbox.1, hb _ _ _ hv₂ hbox.2⟩

/-- Count original unit-middle parameter/nonzero nonunit endpoint incidences.
No lattice, line, gcd or point-count supplier appears in the hypotheses. -/
theorem actual_nonunit_endpoint_incidence_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ),
      0 < X → 0 < Y → X ≤ Y → 2*Y < (p : ℝ)^2 →
      0 < H → H^2 = X*Y → (p : ℝ)^2 ≤ X*Y →
      ∀ I : Finset (Coordinate × Coordinate),
      (∀ i ∈ I, i.1 ∈ literalBox X Y ∧ i.2 ∈ literalBox X Y) →
      (∀ i ∈ I, IsUnit (i.1.2 : ZMod (p^3)) ∧ IsUnit (i.1.1 : ZMod (p^3))) →
      (∀ i ∈ I, i.2 ∈ middleLattice (p^3) i.1.2 i.1.1) →
      (∀ i ∈ I, i.2 ≠ 0 ∧ ¬ IsUnit (i.2.1 : ZMod (p^3))) →
      (I.card : ℝ) ≤ C*(p : ℝ)^ε*(X*Y/p+(X*Y)^2/(p : ℝ)^4) := by
  classical
  obtain ⟨C, hC, hweight⟩ := actual_short_physical_weight_subpower ε hε
  refine ⟨512*C, by positivity, ?_⟩
  intro p hp X Y H hX hY hXY hYsmall hH hHsq harea I hbox hunit hmem hbad
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp2 : 0 < p^2 := pow_pos hp.pos _
  letI : NeZero (p^2) := ⟨hp2.ne'⟩
  let f : ZMod (p^3) →+* ZMod (p^2) :=
    ZMod.castHom (pow_dvd_pow p (by decide : 2 ≤ 3)) (ZMod (p^2))
  let s := I.image Prod.fst
  have hs (wt : Coordinate) (hw : wt ∈ s) :
      wt ∈ literalBox X Y ∧ IsUnit (wt.2 : ZMod (p^2)) ∧
        IsUnit (wt.1 : ZMod (p^2)) := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨(hbox i hi).1,
      by simpa only [map_intCast] using (hunit i hi).1.map f,
      by simpa only [map_intCast] using (hunit i hi).2.map f⟩
  have hex (wt : Coordinate) (hw : wt ∈ s) :
      Nonempty (ReducedMiddleBasis (p^2) wt.2 wt.1 X Y) :=
    exists_reduced_middle_basis (p^2) wt.2 wt.1 X Y hp2 hX hY (hs wt hw).2.2
  let U := fun wt => if hw : wt ∈ s then (Classical.choice (hex wt hw)).R else 0
  have hB (wt : Coordinate) (hw : wt ∈ s) :
      ∃ B : ReducedMiddleBasis (p^2) wt.2 wt.1 X Y, U wt = B.R := by
    exact ⟨Classical.choice (hex wt hw), dif_pos hw⟩
  have hnorm (i : Coordinate × Coordinate) (hi : i ∈ I) :=
    nonunit_endpoint_normalization hp (hunit i hi).2 (hmem i hi)
      (hbox i hi).2 (hbad i hi).1 (hbad i hi).2
  have hshort (wt : Coordinate) (hw : wt ∈ s) :
      weightedSq X Y (U wt) ≤ 2*(X*Y)/(p : ℝ)^2 := by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hw
    obtain ⟨B, hBU⟩ := hB wt hw
    have hn := hnorm i hi
    have hmember : normalizedPoint p i.2 ∈ middleLattice (p^2) wt.2 wt.1 := by
      simpa only [he] using hn.2.2.2.1
    have hh := B.shortest _ hmember hn.2.2.1
    have hb := literalBox_weightedSq (div_pos hX hpR) (div_pos hY hpR) hn.2.2.2.2
    have hemetric : weightedSq (X/(p : ℝ)) (Y/(p : ℝ)) (normalizedPoint p i.2) =
        weightedSq X Y (normalizedPoint p i.2) := by
      simpa only [div_eq_mul_inv, mul_comm] using
        weightedSq_rescale X Y (p : ℝ)⁻¹ (inv_ne_zero hpR.ne') (normalizedPoint p i.2)
    rw [hemetric] at hb
    rw [hBU]
    exact hh.trans (by
      convert hb using 1 <;> simp only [div_eq_mul_inv, inv_pow] <;> ring)
  have hA : 4*(X*Y) < (p : ℝ)^4 := by
    have hy2 := (sq_lt_sq₀ (by positivity : 0 ≤ 2*Y)
      (by positivity : 0 ≤ (p : ℝ)^2)).mpr hYsmall
    nlinarith [mul_le_mul_of_nonneg_right hXY hY.le]
  have hHp : (p : ℝ) ≤ H := by nlinarith
  let W := fun wt => 1+2*H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt)))
  have hfiber (wt : Coordinate) (hw : wt ∈ s) :
      ((I.filter (fun i => i.1 = wt)).card : ℝ) ≤ 32*W wt := by
    let F := I.filter fun i => i.1 = wt
    let G := F.image fun i => normalizedPoint p i.2
    obtain ⟨B, hBU⟩ := hB wt hw
    let B' := rescaleReduced B (p : ℝ)⁻¹ (inv_ne_zero hpR.ne')
    have hgmem (z : Coordinate) (hz : z ∈ G) : z ∈ middleLattice (p^2) wt.2 wt.1 := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hi, he⟩ := Finset.mem_filter.mp hi
      simpa only [he] using (hnorm i hi).2.2.2.1
    have hgbox (z : Coordinate) (hz : z ∈ G) :
        z ∈ literalBox ((p : ℝ)⁻¹*X) ((p : ℝ)⁻¹*Y) := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hb := (hnorm i (Finset.mem_filter.mp hi).1).2.2.2.2
      simpa only [div_eq_mul_inv, mul_comm] using hb
    have hcard : F.card ≤ G.card := by
      apply Finset.card_le_card_of_injOn (fun i => normalizedPoint p i.2)
      · intro i hi
        exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
      · intro i hi j hj hij
        obtain ⟨hi, hei⟩ := Finset.mem_filter.mp hi
        obtain ⟨hj, hej⟩ := Finset.mem_filter.mp hj
        apply Prod.ext (hei.trans hej.symm)
        have hni := hnorm i hi
        have hnj := hnorm j hj
        exact Prod.ext
          (hni.1.symm.trans ((congrArg (fun z : Coordinate => (p : ℤ)*z.1) hij).trans hnj.1))
          (hni.2.1.symm.trans
            ((congrArg (fun z : Coordinate => (p : ℤ)*z.2) hij).trans hnj.2.1))
    have hsection := actual_middle_box_section_count B' hp2
      (mul_pos (inv_pos.mpr hpR) hX) (mul_pos (inv_pos.mpr hpR) hY)
      (H/p) (div_pos hH hpR) (by
        rw [div_pow, hHsq]
        simp only [div_eq_mul_inv, inv_pow]
        ring) G hgmem hgbox
    have hsR : (G.card : ℝ) ≤
        16*(1+H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt)))+
          (X*Y)/(p : ℝ)^4) := by
      change (G.card : ℝ) ≤ 16*(1+(H/p)/Real.sqrt
        (weightedSq ((p : ℝ)⁻¹*X) ((p : ℝ)⁻¹*Y) B'.R)+
        ((p : ℝ)⁻¹*X)*((p : ℝ)⁻¹*Y)/(p^2 : ℕ)) at hsection
      have hm : weightedSq ((p : ℝ)⁻¹*X) ((p : ℝ)⁻¹*Y) B'.R =
          weightedSq X Y (U wt) := by
        rw [weightedSq_rescale X Y (p : ℝ)⁻¹ (inv_ne_zero hpR.ne')]
        exact congrArg (weightedSq X Y) hBU.symm
      rw [hm] at hsection
      convert hsection using 1 <;>
        simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, Nat.cast_pow] <;> ring
    have hv : (X*Y)/(p : ℝ)^4 ≤ 1 :=
      (div_le_one₀ (by positivity)).mpr (by linarith)
    have hn : 0 ≤ H/((p : ℝ)*Real.sqrt (weightedSq X Y (U wt))) := by positivity
    have hcR : (F.card : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hcard
    change (F.card : ℝ) ≤ 32*W wt
    dsimp [W]
    simp only [mul_div_assoc] at hsR hv hn ⊢
    linarith only [hsR, hv, hn, hcR]
  have hsum := hweight p hp (2*X) (2*Y) (2*H) (by positivity) (by positivity)
    (by linarith) (by nlinarith [pow_le_pow_right₀ hp1 (by decide : 2 ≤ 3)])
    (by nlinarith) (by positivity) (by nlinarith) (by linarith) s U
    (fun wt hw => ⟨(hs wt hw).1.1.trans (by linarith),
      (hs wt hw).1.2.trans (by linarith)⟩)
    (fun wt hw => (hs wt hw).2)
    (by
      intro wt hw
      obtain ⟨B, hb⟩ := hB wt hw
      exact ⟨rescaleReduced B 2 (by norm_num), hb⟩)
    (by
      intro wt hw
      rw [weightedSq_rescale X Y 2 (by norm_num)]
      have hh := hshort wt hw
      have hbase : 0 ≤ X*Y/(p : ℝ)^2 := by positivity
      simp only [mul_div_assoc] at hh hbase ⊢
      nlinarith only [hh, hbase])
  have hsum' : (∑ wt ∈ s, W wt) ≤
      16*C*(p : ℝ)^ε*(X*Y/p+(X*Y)^2/(p : ℝ)^4) := by
    simp only [weightedSq_rescale X Y 2 (by norm_num)] at hsum
    have h1 : 0 ≤ X*Y/p := by positivity
    have h2 : 0 ≤ (X*Y)^2/(p : ℝ)^4 := by positivity
    have hCp : 0 ≤ C*(p : ℝ)^ε := by positivity
    change (∑ wt ∈ s, W wt) ≤ _ at hsum ⊢
    apply hsum.trans
    calc
      _ = (C*(p : ℝ)^ε)*(4*(X*Y/p)+16*((X*Y)^2/(p : ℝ)^4)) := by ring
      _ ≤ (C*(p : ℝ)^ε)*(16*(X*Y/p)+16*((X*Y)^2/(p : ℝ)^4)) := by
        apply mul_le_mul_of_nonneg_left _ hCp
        exact add_le_add (mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 16) h1) le_rfl
      _ = _ := by ring
  calc
    (I.card : ℝ) = ∑ wt ∈ s, ((I.filter (fun i => i.1=wt)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image Prod.fst I
    _ ≤ ∑ wt ∈ s, 32*W wt := Finset.sum_le_sum hfiber
    _ = 32*(∑ wt ∈ s, W wt) := (Finset.mul_sum _ _ _).symm
    _ ≤ 32*(16*C*(p : ℝ)^ε*(X*Y/p+(X*Y)^2/(p : ℝ)^4)) :=
      mul_le_mul_of_nonneg_left hsum' (by norm_num)
    _ = _ := by ring

end
end D5.S3.Arith.CharacterSums.Original
