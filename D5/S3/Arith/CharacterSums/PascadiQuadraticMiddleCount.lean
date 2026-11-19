/- GID: D5/S3/Arith/CharacterSums/PascadiQuadraticMiddleCount
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiQuadraticMiddleCount
   mirror-E: none(waiver:physical-kernel-average-in-progress)
   anchors: []
   utility: none
   digest: Quantized quadratic values control nonzero middle-lattice sections. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalWeightAverage

/-! The zero directions of a split quadratic form must be removed before
estimating the boundary contribution. No count estimate is a hypothesis. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private def symmetricInterval (T : ℝ) : Finset ℤ := Finset.Icc (-⌊T⌋) ⌊T⌋

private theorem symmetricInterval_mem {T : ℝ} {n : ℤ} (hn : |(n : ℝ)| ≤ T) :
    n ∈ symmetricInterval T := by
  have h := abs_le.mp hn
  have hu : n ≤ ⌊T⌋ := Int.le_floor.mpr h.2
  have hl : -n ≤ ⌊T⌋ := Int.le_floor.mpr (by push_cast; linarith [h.1])
  exact Finset.mem_Icc.mpr ⟨by omega, hu⟩

private theorem symmetricInterval_card {T : ℝ} (hT : 0 ≤ T) :
    ((symmetricInterval T).card : ℝ) ≤ 2*T+1 := by
  have hN : 0 ≤ ⌊T⌋ := Int.floor_nonneg.mpr hT
  have hh := Int.card_Icc_of_le (a := -⌊T⌋) (b := ⌊T⌋) (by omega)
  have he : ((symmetricInterval T).card : ℝ) = 2*(⌊T⌋ : ℝ)+1 := by
    unfold symmetricInterval
    exact_mod_cast (show ((Finset.Icc (-⌊T⌋) ⌊T⌋).card : ℤ) = 2*⌊T⌋+1 by omega)
  rw [he]
  linarith [Int.floor_le T]

private theorem symmetricInterval_erase_card {T : ℝ} (hT : 0 ≤ T) :
    (((symmetricInterval T).erase 0).card : ℝ) ≤ 2*T := by
  have hz : (0 : ℤ) ∈ symmetricInterval T := symmetricInterval_mem (by simpa using hT)
  have hh := Finset.card_erase_add_one hz
  have hc := symmetricInterval_card hT
  have he : (((symmetricInterval T).erase 0).card : ℝ)+1 =
      ((symmetricInterval T).card : ℝ) := by exact_mod_cast hh
  linarith

/-- A homogeneous integer quadratic value, quantized on the congruence lattice,
bounds all original box points away from its zero set. In particular a null
shortest direction contributes no unbounded boundary term. -/
theorem quadratic_nonzero_middle_box_count {c q : ℕ} {t w : ℤ} {X Y H M : ℝ}
    (B : ReducedMiddleBasis c t w X Y) (hc : 0 < c) (hq : 0 < q)
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 < H) (hHsq : H^2 = X*Y)
    (hM : 0 ≤ M) (Q : Coordinate → ℤ)
    (hzero : Q 0 = 0)
    (hhom : ∀ (n : ℤ) (z : Coordinate), Q (n • z) = n^2 * Q z)
    (hquant : ∀ z ∈ middleLattice c t w, (q : ℤ) ∣ Q z)
    (hbound : ∀ z, |(Q z : ℝ)| ≤ M * weightedSq X Y z)
    (s : Finset Coordinate)
    (hmem : ∀ z ∈ s, z ∈ middleLattice c t w)
    (hbox : ∀ z ∈ s, z ∈ literalBox X Y)
    (hnonzero : ∀ z ∈ s, Q z ≠ 0) :
    (s.card : ℝ) ≤ 1 + 4*H*Real.sqrt (M/q) + 24*(X*Y)/c := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hs
    have hz₀ne : z₀ ≠ 0 := by
      intro hz
      exact hnonzero z₀ hz₀ (by rw [hz, hzero])
    let σ := Real.sqrt (weightedSq X Y B.R)
    have hσ : 0 < σ := Real.sqrt_pos.mpr
      (weightedSq_pos hX hY (B.first_ne_zero hc))
    have hσsq : σ^2 = weightedSq X Y B.R :=
      Real.sq_sqrt (weightedSq_nonneg hX hY _)
    have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have hshort : σ ≤ 2*H := by
      have hh := (B.shortest z₀ (hmem z₀ hz₀) hz₀ne).trans
        (literalBox_weightedSq hX hY (hbox z₀ hz₀))
      rw [← hσsq, ← hHsq] at hh
      nlinarith [sq_nonneg (σ + 2*H)]
    let U := 2*H/σ
    let V := 2*H*σ/c
    let T := 2*H*Real.sqrt (M/q)
    have hU : 0 ≤ U := by dsimp [U]; positivity
    have hV : 0 ≤ V := by dsimp [V]; positivity
    have hT : 0 ≤ T := by dsimp [T]; positivity
    let off := symmetricInterval U ×ˢ (symmetricInterval V).erase 0
    let center := symmetricInterval T ×ˢ ({0} : Finset ℤ)
    have hcoord (z : Coordinate) (hz : physical B.R B.V z ∈ literalBox X Y) :
        |(z.1 : ℝ)| ≤ U ∧ |(z.2 : ℝ)| ≤ V := by
      obtain ⟨hi, hj⟩ := B.coordinate_sq_bounds hc hX hY z hz
      have hfirst : |(z.1 : ℝ)| * σ ≤ 2*H := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).mp
        rw [mul_pow, sq_abs, hσsq]
        nlinarith
      have hsecond : |(z.2 : ℝ)| * (c : ℝ) ≤ 2*H*σ := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).mp
        rw [mul_pow, sq_abs]
        nlinarith [sq_nonneg H, sq_nonneg σ]
      exact ⟨(le_div_iff₀ hσ).mpr hfirst, (le_div_iff₀ hcR).mpr hsecond⟩
    have hcentral (n : ℤ) (hz : physical B.R B.V (n,0) ∈ s) :
        |(n : ℝ)| ≤ T := by
      have he : physical B.R B.V (n,0) = n • B.R := by
        ext <;> simp [physical] <;> ring
      have hqn : Q B.R ≠ 0 := by
        intro h
        apply hnonzero _ hz
        rw [he, hhom, h, mul_zero]
      have hqabs : (q : ℝ) ≤ |(Q B.R : ℝ)| := by
        have hh := Int.natAbs_le_of_dvd_ne_zero (hquant B.R B.memR) hqn
        have hn : q ≤ (Q B.R).natAbs := by simpa only [Int.natAbs_natCast] using hh
        have hz : (q : ℤ) ≤ ((Q B.R).natAbs : ℤ) := by exact_mod_cast hn
        rw [Int.natCast_natAbs] at hz
        exact_mod_cast hz
      have hlow : (q : ℝ) ≤ M*σ^2 := by
        rw [hσsq]
        exact hqabs.trans (hbound B.R)
      have hu := B.coordinate_sq_bounds hc hX hY (n,0) (hbox _ hz)
      have hnsq : (n : ℝ)^2*σ^2 ≤ 4*H^2 := by
        rw [hσsq]
        nlinarith [hu.1]
      have hnq : (n : ℝ)^2*(q : ℝ) ≤ 4*H^2*M := by
        have hh := mul_le_mul_of_nonneg_left hlow (sq_nonneg (n : ℝ))
        have hh' := mul_le_mul_of_nonneg_left hnsq hM
        nlinarith
      have hsqrt : (Real.sqrt (M/q))^2 = M/q := Real.sq_sqrt (by positivity)
      have hTq : T^2*(q : ℝ) = 4*H^2*M := by
        dsimp [T]
        rw [mul_pow, mul_pow, hsqrt]
        field_simp
        <;> ring
      have hnT : (n : ℝ)^2 ≤ T^2 := by nlinarith [hqR]
      exact (sq_le_sq₀ (abs_nonneg _) hT).mp (by simpa only [sq_abs] using hnT)
    have hsub : s ⊆ (center.image (physical B.R B.V)) ∪
        (off.image (physical B.R B.V)) := by
      intro z hz
      obtain ⟨i,j,hij⟩ := B.decompose z (hmem z hz)
      have hb := hcoord (i,j) (by simpa only [hij] using hbox z hz)
      by_cases hj : j = 0
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨(i,j), ?_, hij⟩
        have hij0 : physical B.R B.V (i,0) = z := by simpa only [hj] using hij
        have hh := hcentral i (by rw [hij0]; exact hz)
        exact Finset.mem_product.mpr ⟨symmetricInterval_mem hh, by simp [hj]⟩
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨(i,j), Finset.mem_product.mpr
          ⟨symmetricInterval_mem hb.1, Finset.mem_erase.mpr
            ⟨hj, symmetricInterval_mem hb.2⟩⟩, hij⟩
    have hcount : (s.card : ℝ) ≤ (center.card : ℝ)+(off.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add
          (Finset.card_image_le) (Finset.card_image_le)))
    have hcenter : (center.card : ℝ) ≤ 2*T+1 := by
      simpa only [center, Finset.card_product, Finset.card_singleton, mul_one] using
        symmetricInterval_card hT
    have hoff : (off.card : ℝ) ≤ 24*(X*Y)/c := by
      have hh : (off.card : ℝ) ≤ (2*U+1)*(2*V) := by
        simp only [off, Finset.card_product, Nat.cast_mul]
        exact mul_le_mul (symmetricInterval_card hU)
          (symmetricInterval_erase_card hV) (Nat.cast_nonneg _) (by positivity)
      have hexpand : (2*U+1)*(2*V) = (16*H^2+4*H*σ)/c := by
        dsimp [U,V]
        field_simp
        <;> ring
      rw [hexpand] at hh
      apply hh.trans
      apply (div_le_div_iff_of_pos_right hcR).mpr
      nlinarith [hHsq]
    dsimp only [T] at hcenter
    linarith
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty, Nat.cast_zero]
    positivity

end
end D5.S3.Arith.CharacterSums.Original
