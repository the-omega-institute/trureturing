/- GID: D5/S3/DivergenceSupport/Equality/PetzRecovery
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/Equality/PetzRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize zero DPI defect by recovery through the Bayesian reverse channel. -/

/- Repository-derived. This closes only the Bayesian reverse-recovery clause of residual atom
sha256:11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574. The
permutation-channel zero-defect specialization REMAINS OPEN, so the residual atom as a whole is
not discharged. -/

import D5.S3.DivergenceSupport.ZeroSupportDefectEquality

namespace D5.S3.DivergenceSupport.Equality.PetzRecovery

open D5.S3.Divergence.ClassicalDPI
open D5.S3.DivergenceSupport.ZeroSupportDPI
open D5.S3.DivergenceSupport.ZeroSupportDefect
open D5.S3.DivergenceSupport.ZeroSupportDefectEquality

/-- Zero general-support DPI defect is equivalent to recovery by the Bayesian reverse channel. -/
theorem dpi_defect_eq_zero_iff_exists_bayes_recovery {X Y : Type*}
    [Fintype X] [Fintype Y]
    (p q : X -> Real) (W : X -> Y -> Real)
    (hp : (forall x, 0 <= p x) /\ ∑ x, p x = 1)
    (hq : (forall x, 0 <= q x) /\ ∑ x, q x = 1)
    (hac : forall x, q x = 0 -> p x = 0)
    (hW : (forall x y, 0 <= W x y) /\ forall x, ∑ y, W x y = 1) :
    klDivergence p q -
        klDivergence (channelOutput W p) (channelOutput W q) = 0 <->
      exists R : Y -> X -> Real,
        (forall y x, R y x =
          if channelOutput W q y = 0 then q x else posterior W q y x) /\
        (forall y x, 0 <= R y x) /\
        (forall y, ∑ x, R y x = 1) /\
        channelOutput R (channelOutput W p) = p /\
        channelOutput R (channelOutput W q) = q := by
  classical
  have hOutputPNonneg (y : Y) : 0 <= channelOutput W p y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp.1 x) (hW.1 x y)
  have hOutputQNonneg (y : Y) : 0 <= channelOutput W q y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hq.1 x) (hW.1 x y)
  have hOutputAC (y : Y) (hy : channelOutput W q y = 0) :
      channelOutput W p y = 0 :=
    channel_output_absolute_continuity p q W hq.1 hac hW.1 y hy
  have hOutputPSum : ∑ y, channelOutput W p y = 1 := by
    simp only [channelOutput]
    rw [Finset.sum_comm]
    calc
      (∑ x, ∑ y, p x * W x y) = ∑ x, p x * (∑ y, W x y) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      _ = ∑ x, p x := by simp_rw [hW.2, mul_one]
      _ = 1 := hp.2
  have hOutputQSum : ∑ y, channelOutput W q y = 1 := by
    simp only [channelOutput]
    rw [Finset.sum_comm]
    calc
      (∑ x, ∑ y, q x * W x y) = ∑ x, q x * (∑ y, W x y) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      _ = ∑ x, q x := by simp_rw [hW.2, mul_one]
      _ = 1 := hq.2
  constructor
  · intro hzero
    have hposteriors :=
      (dpi_defect_eq_zero_iff_zero_output_or_posteriors_eq
        p q W hp hq hac hW).mp hzero
    let R : Y -> X -> Real := fun y x =>
      if channelOutput W q y = 0 then q x else posterior W q y x
    have hRNonneg (y : Y) (x : X) : 0 <= R y x := by
      dsimp [R]
      split_ifs with hy
      · exact hq.1 x
      · exact div_nonneg (mul_nonneg (hq.1 x) (hW.1 x y)) (hOutputQNonneg y)
    have hRSum (y : Y) : ∑ x, R y x = 1 := by
      dsimp [R]
      split_ifs with hy
      · exact hq.2
      · simp only [posterior, <- Finset.sum_div, channelOutput]
        exact div_self hy
    have hRecoverQ : channelOutput R (channelOutput W q) = q := by
      funext x
      rw [channelOutput]
      calc
        (∑ y, channelOutput W q y * R y x) = ∑ y, q x * W x y := by
          apply Finset.sum_congr rfl
          intro y _
          dsimp [R]
          split_ifs with hy
          · have hJointZero : q x * W x y = 0 := by
              have hsum : (∑ z, q z * W z y) = 0 := by
                simpa only [channelOutput] using hy
              exact (Finset.sum_eq_zero_iff_of_nonneg fun z _ =>
                mul_nonneg (hq.1 z) (hW.1 z y)).mp hsum x (Finset.mem_univ x)
            simp [hy, hJointZero]
          · simp only [posterior]
            field_simp
        _ = q x * ∑ y, W x y := by rw [Finset.mul_sum]
        _ = q x := by rw [hW.2 x, mul_one]
    have hRecoverP : channelOutput R (channelOutput W p) = p := by
      funext x
      rw [channelOutput]
      calc
        (∑ y, channelOutput W p y * R y x) = ∑ y, p x * W x y := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hpy : channelOutput W p y = 0
          · have hJointZero : p x * W x y = 0 := by
              have hsum : (∑ z, p z * W z y) = 0 := by
                simpa only [channelOutput] using hpy
              exact (Finset.sum_eq_zero_iff_of_nonneg fun z _ =>
                mul_nonneg (hp.1 z) (hW.1 z y)).mp hsum x (Finset.mem_univ x)
            simp [hpy, hJointZero]
          · have hqy : channelOutput W q y ≠ 0 := by
              intro hqzero
              exact hpy (hOutputAC y hqzero)
            have hposterior : posterior W p y = posterior W q y :=
              (hposteriors y).resolve_left hpy
            dsimp [R]
            rw [if_neg hqy, <- hposterior]
            simp only [posterior]
            field_simp
        _ = p x * ∑ y, W x y := by rw [Finset.mul_sum]
        _ = p x := by rw [hW.2 x, mul_one]
    exact ⟨R, fun y x => rfl, hRNonneg, hRSum, hRecoverP, hRecoverQ⟩
  · rintro ⟨R, _hRFormula, hRNonneg, hRSum, hRecoverP, hRecoverQ⟩
    have hForward := dpi_defect_nonneg_zero_support p q W hp hq hac hW
    have hReverse := dpi_defect_nonneg_zero_support
      (channelOutput W p) (channelOutput W q) R
      ⟨hOutputPNonneg, hOutputPSum⟩ ⟨hOutputQNonneg, hOutputQSum⟩ hOutputAC
      ⟨hRNonneg, hRSum⟩
    rw [hRecoverP, hRecoverQ] at hReverse
    linarith

end D5.S3.DivergenceSupport.Equality.PetzRecovery
