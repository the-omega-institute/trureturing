/- GID: D5/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/CalibratedArithmeticSmallBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A monotone moving center has a finite arithmetic small-ball bound. -/

import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

open scoped BigOperators Topology
open Finset Filter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
noncomputable section

/-- Finite conditional mass for an integer-valued count variable. -/
def eventMass (p : ℤ → ℝ) (S : Finset ℤ) : ℝ := ∑ t ∈ S, p t

/-- A lattice band uses the same center for every integer target. -/
def latticeBand (g : ℤ → ℝ) (h : ℝ) (z : ℤ) (I : Finset ℤ) : Finset ℤ :=
  I.filter (fun t => |g t - z| ≤ h)

/-- The finite central small-ball event. The outer set contains the full
integer range attainable by the moving center on the central interval. -/
def arithmeticEvent (g : ℤ → ℝ) (h : ℝ) (I Z : Finset ℤ) : Finset ℤ :=
  I.filter (fun t => ∃ z ∈ Z, |g t - z| ≤ h)

private theorem integer_set_card_le_width (S : Finset ℤ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ x ∈ S, ∀ y ∈ S, ((y - x : ℤ) : ℝ) ≤ W) :
    (S.card : ℝ) ≤ W + 1 := by
  classical
  by_cases hn : S.Nonempty
  · let a := S.min' hn
    let b := S.max' hn
    have ha : a ∈ S := S.min'_mem hn
    have hb : b ∈ S := S.max'_mem hn
    have hab : a ≤ b := S.min'_le b hb
    have hsub : S ⊆ Icc a b := by
      intro t ht
      exact mem_Icc.mpr ⟨S.min'_le t ht, S.le_max' t ht⟩
    have hc : (S.card : ℝ) ≤ ((Icc a b).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have hi : ((Icc a b).card : ℝ) = (b : ℝ) + 1 - a := by
      exact_mod_cast Int.card_Icc_of_le a b (by omega : a ≤ b + 1)
    rw [hi] at hc
    have hd := hw a ha b hb
    push_cast at hd
    linarith
  · simp only [not_nonempty_iff_eq_empty.mp hn, card_empty, Nat.cast_zero]
    linarith

private theorem lattice_band_card_le (g : ℤ → ℝ) (s h : ℝ) (I : Finset ℤ)
    (hs : 0 < s) (hh : 0 ≤ h)
    (hg : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → s * ((y - x : ℤ) : ℝ) ≤ g y - g x)
    (z : ℤ) :
    ((latticeBand g h z I).card : ℝ) ≤ 2 * h / s + 1 := by
  apply integer_set_card_le_width _ _ (by positivity)
  intro x hx y hy
  have hx' := mem_filter.mp hx
  have hy' := mem_filter.mp hy
  by_cases hxy : x ≤ y
  · have hd := hg x hx'.1 y hy'.1 hxy
    have hxlo := (abs_le.mp hx'.2).1
    have hyhi := (abs_le.mp hy'.2).2
    apply (le_div_iff₀ hs).mpr
    nlinarith
  · have hn : ((y - x : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (by omega : y - x ≤ 0)
    exact hn.trans (by positivity)

/-- The central event is covered by the individual integer bands. This
retains the same count realization and never replaces it by independent phases. -/
theorem arithmetic_central_mass_bound (p g : ℤ → ℝ) (I Z : Finset ℤ)
    (s h a : ℝ) (hs : 0 < s) (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hmax : ∀ t ∈ I, p t ≤ a)
    (hg : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → s * ((y - x : ℤ) : ℝ) ≤ g y - g x) :
    eventMass p (arithmeticEvent g h I Z) ≤
      a * (Z.card : ℝ) * (2 * h / s + 1) := by
  classical
  have he : arithmeticEvent g h I Z = Z.biUnion (fun z => latticeBand g h z I) := by
    ext t
    simp only [arithmeticEvent, latticeBand, mem_filter, mem_biUnion]
    aesop
  calc
    eventMass p (arithmeticEvent g h I Z) ≤
        ((arithmeticEvent g h I Z).card : ℝ) * a := by
      unfold eventMass
      exact (sum_le_sum fun t ht => hmax t (mem_filter.mp ht).1).trans_eq
        (by simp only [sum_const, nsmul_eq_mul]; rfl)
    _ ≤ (∑ z ∈ Z, ((latticeBand g h z I).card : ℝ)) * a := by
      apply mul_le_mul_of_nonneg_right _ ha
      rw [he]
      exact_mod_cast card_biUnion_le
    _ = ∑ z ∈ Z, ((latticeBand g h z I).card : ℝ) * a := by rw [sum_mul]
    _ ≤ ∑ _z ∈ Z, (2 * h / s + 1) * a := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_right (lattice_band_card_le g s h I hs hh hg z) ha
    _ = a * (Z.card : ℝ) * (2 * h / s + 1) := by simp; ring

/-- A closed real band restricts its integer targets to this exact interval. -/
def integerTargets (a b : ℝ) : Finset ℤ := Icc ⌈a⌉ ⌊b⌋

private theorem integer_targets_card_le (a b : ℝ) (hab : a ≤ b) :
    ((integerTargets a b).card : ℝ) ≤ b - a + 1 := by
  apply integer_set_card_le_width _ _ (by linarith)
  intro x hx y hy
  have hxa : a ≤ (x : ℝ) := (Int.le_ceil a).trans (by exact_mod_cast (mem_Icc.mp hx).1)
  have hycast : (y : ℝ) ≤ (⌊b⌋ : ℤ) := by exact_mod_cast (mem_Icc.mp hy).2
  have hyb : (y : ℝ) ≤ b :=
    hycast.trans (Int.floor_le b)
  push_cast
  linarith

open scoped Classical in
/-- The same moving center gives both the number of possible integer bands
and the number of count values in each band. A posterior approximation is
paid only by widening the small-ball event. -/
theorem moving_center_small_ball (p f g : ℤ → ℝ) (T : Finset ℤ) (a b : ℤ)
    (s K τ err A tail : ℝ) (hab : a ≤ b) (hs : 0 < s) (hK : 0 ≤ K)
    (hτ : 0 ≤ τ) (herr : 0 ≤ err) (hA : 0 ≤ A)
    (hp : ∀ t, 0 ≤ p t) (hmax : ∀ t ∈ Icc a b, p t ≤ A)
    (hlower : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      x ≤ y → s * ((y - x : ℤ) : ℝ) ≤ g y - g x)
    (hupper : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      x ≤ y → g y - g x ≤ K * s * ((y - x : ℤ) : ℝ))
    (happrox : ∀ t ∈ Icc a b, |f t - g t| ≤ err)
    (htail : eventMass p (T \ Icc a b) ≤ tail) :
    eventMass p (T.filter fun t => ∃ z : ℤ, |f t - z| ≤ τ) ≤
      A * (K * s * ((b - a : ℤ) : ℝ) + 2 * (τ + err) + 1) *
        (2 * (τ + err) / s + 1) + tail := by
  classical
  let I := Icc a b
  let h := τ + err
  let Z := integerTargets (g a - h) (g b + h)
  have ha : a ∈ I := mem_Icc.mpr ⟨le_refl _, hab⟩
  have hb : b ∈ I := mem_Icc.mpr ⟨hab, le_refl _⟩
  have hnonneg : 0 ≤ h := add_nonneg hτ herr
  have hgmono : g a ≤ g b := by
    have hd := hlower a ha b hb hab
    have hba : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hab
    nlinarith
  have hZ : (Z.card : ℝ) ≤ K * s * ((b - a : ℤ) : ℝ) + 2 * h + 1 := by
    have hc := integer_targets_card_le (g a - h) (g b + h) (by linarith)
    have hu := hupper a ha b hb hab
    dsimp [Z] at *
    linarith
  have hsub : T.filter (fun t => ∃ z : ℤ, |f t - z| ≤ τ) ⊆
      arithmeticEvent g h I Z ∪ (T \ I) := by
    intro t ht
    have htf := mem_filter.mp ht
    by_cases hti : t ∈ I
    · rcases htf.2 with ⟨z, hz⟩
      have hgz : |g t - z| ≤ h := by
        have hi := abs_add_le (g t - f t) (f t - z)
        have he := happrox t hti
        rw [abs_sub_comm (f t)] at he
        have ha : g t - f t + (f t - z) = g t - z := by ring
        rw [ha] at hi
        dsimp [h]; linarith
      have hlo := hlower a ha t hti (mem_Icc.mp hti).1
      have hhi := hlower t hti b hb (mem_Icc.mp hti).2
      have hat : (0 : ℝ) ≤ ((t - a : ℤ) : ℝ) := by
        exact_mod_cast sub_nonneg.mpr (mem_Icc.mp hti).1
      have htb : (0 : ℝ) ≤ ((b - t : ℤ) : ℝ) := by
        exact_mod_cast sub_nonneg.mpr (mem_Icc.mp hti).2
      have hzt : z ∈ Z := by
        apply mem_Icc.mpr
        constructor
        · apply Int.ceil_le.mpr
          nlinarith [(abs_le.mp hgz).2]
        · apply Int.le_floor.mpr
          nlinarith [(abs_le.mp hgz).1]
      exact mem_union_left _ (mem_filter.mpr ⟨hti, z, hzt, hgz⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨htf.1, hti⟩)
  have hm : eventMass p (T.filter fun t => ∃ z : ℤ, |f t - z| ≤ τ) ≤
      eventMass p (arithmeticEvent g h I Z) + eventMass p (T \ I) := by
    have hpart := sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hp t)
    have hu : (∑ t ∈ arithmeticEvent g h I Z ∪ (T \ I), p t) ≤
        eventMass p (arithmeticEvent g h I Z) + eventMass p (T \ I) := by
      unfold eventMass
      rw [← sum_union_inter]
      exact le_add_of_nonneg_right (sum_nonneg (fun t _ => hp t))
    exact hpart.trans hu
  have hc := arithmetic_central_mass_bound p g I Z s h A hs hnonneg hA hmax hlower
  have hzbound : A * (Z.card : ℝ) * (2 * h / s + 1) ≤
      A * (K * s * ((b - a : ℤ) : ℝ) + 2 * h + 1) * (2 * h / s + 1) := by
    gcongr
  exact hm.trans (add_le_add (hc.trans hzbound) htail)


open scoped Classical in
/-- A uniform feedback hypothesis for the same shared calibration yields a
small-ball bound for its compensated group mean. The native conditional mass,
posterior approximation, and uniform feedback bounds are explicit inputs. -/
theorem shared_calibration_small_ball {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q bg : ℝ) (θ : ℝ → ℝ) (p f : ℤ → ℝ)
    (T : Finset ℤ) (a b : ℤ) (s K τ err A tail : ℝ)
    (hab : a ≤ b) (hs : 0 < s) (hK : 0 ≤ K)
    (hτ : 0 ≤ τ) (herr : 0 ≤ err) (hA : 0 ≤ A) (hp : ∀ t, 0 ≤ p t)
    (hmax : ∀ t ∈ Icc a b, p t ≤ A)
    (hcurve : ∀ x ∈ Set.Icc (a : ℝ) (b : ℝ), DifferentiableAt ℝ θ x ∧
      (∀ᶠ u in 𝓝 x, SharedRectangleCalibration.calibratedMean outside r ε N R U u (θ u) = q) ∧
      0 < SharedRectangleCalibration.calibratedVariance outside r ε N R U x (θ x))
    (hfeedback : ∀ x ∈ interior (Set.Icc (a : ℝ) (b : ℝ)),
      s ≤ Real.sigmoid (θ x) - 1 / 2 -
        (bg + x) * Real.sigmoid (θ x) * (1 - Real.sigmoid (θ x)) *
          SharedRectangleCalibration.checkerboard r ε (θ x) /
            SharedRectangleCalibration.calibratedVariance outside r ε N R U x (θ x) ∧
      Real.sigmoid (θ x) - 1 / 2 -
        (bg + x) * Real.sigmoid (θ x) * (1 - Real.sigmoid (θ x)) *
          SharedRectangleCalibration.checkerboard r ε (θ x) /
            SharedRectangleCalibration.calibratedVariance outside r ε N R U x (θ x) ≤ K * s)
    (happrox : ∀ t ∈ Icc a b,
      |f t - ((bg + t) * Real.sigmoid (θ t) - t / 2)| ≤ err)
    (htail : eventMass p (T \ Icc a b) ≤ tail) :
    eventMass p (T.filter fun t => ∃ z : ℤ, |f t - z| ≤ τ) ≤
      A * (K * s * ((b - a : ℤ) : ℝ) + 2 * (τ + err) + 1) *
        (2 * (τ + err) / s + 1) + tail := by
  classical
  let G : ℝ → ℝ := fun x => (bg + x) * Real.sigmoid (θ x) - x / 2
  have hder (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
      HasDerivAt G (Real.sigmoid (θ x) - 1 / 2 -
        (bg + x) * Real.sigmoid (θ x) * (1 - Real.sigmoid (θ x)) *
          SharedRectangleCalibration.checkerboard r ε (θ x) /
            SharedRectangleCalibration.calibratedVariance outside r ε N R U x (θ x)) x := by
    exact SharedRectangleCalibration.compensated_group_deriv outside r ε N R U q bg
      x (θ x) (deriv θ x) θ (hcurve x hx).1.hasDerivAt rfl (hcurve x hx).2.1
        (ne_of_gt (hcurve x hx).2.2)
  have hcont : ContinuousOn G (Set.Icc (a : ℝ) (b : ℝ)) :=
    fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ G (interior (Set.Icc (a : ℝ) (b : ℝ))) :=
    fun x hx => (hder x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hl := (convex_Icc (a : ℝ) (b : ℝ)).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun x hx => by rw [(hder x (interior_subset hx)).deriv]; exact (hfeedback x hx).1)
  have hu := (convex_Icc (a : ℝ) (b : ℝ)).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun x hx => by rw [(hder x (interior_subset hx)).deriv]; exact (hfeedback x hx).2)
  apply moving_center_small_ball p f (fun t => G t) T a b s K τ err A tail hab hs hK
    hτ herr hA hp hmax
  · intro x hx y hy hxy
    have hxR : (x : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := by
      exact ⟨by exact_mod_cast (mem_Icc.mp hx).1, by exact_mod_cast (mem_Icc.mp hx).2⟩
    have hyR : (y : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := by
      exact ⟨by exact_mod_cast (mem_Icc.mp hy).1, by exact_mod_cast (mem_Icc.mp hy).2⟩
    simpa only [Int.cast_sub] using hl x hxR y hyR (by exact_mod_cast hxy)
  · intro x hx y hy hxy
    have hxR : (x : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := by
      exact ⟨by exact_mod_cast (mem_Icc.mp hx).1, by exact_mod_cast (mem_Icc.mp hx).2⟩
    have hyR : (y : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := by
      exact ⟨by exact_mod_cast (mem_Icc.mp hy).1, by exact_mod_cast (mem_Icc.mp hy).2⟩
    simpa only [Int.cast_sub] using hu x hxR y hyR (by exact_mod_cast hxy)
  · exact happrox
  · exact htail

end
end D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall

-- Temporary closure probes.
#print axioms D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall.eventMass
#print axioms D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall.latticeBand
#print axioms D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall.arithmeticEvent
#print axioms D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall.arithmetic_central_mass_bound
#print axioms D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall.integerTargets
#print axioms D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall.moving_center_small_ball
#print axioms D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall.shared_calibration_small_ball
