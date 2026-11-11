/- GID: D5/S3/Quantum/Analysis/FractionalPowerHolder
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/FractionalPowerHolder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dimension-free fractional-power continuity for noncommuting positive elements. -/

module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.MeanInequalitiesPow

/-! Fractional-power continuity on the positive cone of an arbitrary unital C-star algebra. -/

@[expose] public section

noncomputable section

namespace QuantumFractionalPower

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem rpow_add_scalar_le {x : A} (hx : 0 ≤ x) {t p : ℝ}
    (ht : 0 ≤ t) (hp : 0 < p) (hp1 : p ≤ 1) :
    CFC.rpow (x + algebraMap ℝ A t) p ≤
      CFC.rpow x p + algebraMap ℝ A (t ^ p) := by
  have hxsa : IsSelfAdjoint x := .of_nonneg hx
  have hscalar : 0 ≤ algebraMap ℝ A t := by
    simpa only [cfc_const t x hxsa] using
      (cfc_nonneg (a := x) (f := fun _ : ℝ => t) (fun _ _ => ht))
  have hsum : 0 ≤ x + algebraMap ℝ A t := add_nonneg hx hscalar
  have hc : Continuous (fun r : ℝ => r ^ p) := Real.continuous_rpow_const hp.le
  have hshift : cfc (fun r : ℝ => r + t) x = x + algebraMap ℝ A t := by
    have h := cfc_add_const t (fun r : ℝ => r) x continuousOn_id hxsa
    rw [cfc_id' ℝ x hxsa] at h
    exact h
  change (x + algebraMap ℝ A t) ^ p ≤ x ^ p + algebraMap ℝ A (t ^ p)
  rw [CFC.rpow_eq_cfc_real hsum, CFC.rpow_eq_cfc_real hx]
  calc
    cfc (fun r : ℝ => r ^ p) (x + algebraMap ℝ A t) =
        cfc ((fun r : ℝ => r ^ p) ∘ (fun r : ℝ => r + t)) x := by
      rw [cfc_comp _ _ x hxsa hc.continuousOn (by fun_prop), hshift]
    _ ≤ cfc (fun r : ℝ => r ^ p + t ^ p) x := by
      apply cfc_mono _ ((hc.comp (continuous_id.add continuous_const)).continuousOn)
        ((hc.add continuous_const).continuousOn)
      intro r hr
      exact Real.rpow_add_le_add_rpow (spectrum_nonneg_of_nonneg hx hr) ht hp.le hp1
    _ = cfc (fun r : ℝ => r ^ p) x + algebraMap ℝ A (t ^ p) :=
      cfc_add_const (t ^ p) _ x hc.continuousOn hxsa

/-- The sharp dimension-free Hölder estimate on the positive cone. The inputs need not
commute, be invertible, or act on a finite-dimensional space. -/
theorem norm_rpow_sub_rpow_le {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ‖CFC.rpow a p - CFC.rpow b p‖ ≤ ‖a - b‖ ^ p := by
  rcases subsingleton_or_nontrivial A with hs | hn
  · rw [show CFC.rpow a p - CFC.rpow b p = 0 from @Subsingleton.elim A hs _ _, norm_zero]
    exact Real.rpow_nonneg (norm_nonneg _) p
  let _ := hn
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  have hsb : IsSelfAdjoint b := .of_nonneg hb
  have hab : a ≤ b + algebraMap ℝ A ‖a - b‖ := by
    simpa only [add_comm] using
      (sub_le_iff_le_add).mp ((hsa.sub hsb).le_algebraMap_norm_self)
  have hba : b ≤ a + algebraMap ℝ A ‖a - b‖ := by
    have h := (hsb.sub hsa).le_algebraMap_norm_self
    rw [norm_sub_rev b a] at h
    simpa only [add_comm] using (sub_le_iff_le_add).mp h
  have hup : CFC.rpow a p ≤ CFC.rpow b p + algebraMap ℝ A (‖a - b‖ ^ p) :=
    (CFC.monotone_rpow ⟨hp.le, hp1⟩ hab).trans
      (rpow_add_scalar_le hb (norm_nonneg _) hp hp1)
  have hdown : CFC.rpow b p ≤ CFC.rpow a p + algebraMap ℝ A (‖a - b‖ ^ p) :=
    (CFC.monotone_rpow ⟨hp.le, hp1⟩ hba).trans
      (rpow_add_scalar_le ha (norm_nonneg _) hp hp1)
  have hupper : CFC.rpow a p - CFC.rpow b p ≤ algebraMap ℝ A (‖a - b‖ ^ p) :=
    sub_le_iff_le_add.mpr (by simpa only [add_comm] using hup)
  have hlower : -(algebraMap ℝ A (‖a - b‖ ^ p)) ≤ CFC.rpow a p - CFC.rpow b p := by
    have h : CFC.rpow b p - CFC.rpow a p ≤ algebraMap ℝ A (‖a - b‖ ^ p) :=
      sub_le_iff_le_add.mpr (by simpa only [add_comm] using hdown)
    simpa only [neg_sub] using neg_le_neg h
  have hdiff : IsSelfAdjoint (CFC.rpow a p - CFC.rpow b p) :=
    (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).sub (.of_nonneg CFC.rpow_nonneg)
  have hnorm := IsSelfAdjoint.norm_le_max_of_le_of_le hlower hupper hdiff
  simpa only [norm_neg, max_self, norm_algebraMap', Real.norm_of_nonneg
    (Real.rpow_nonneg (norm_nonneg _) p)] using hnorm

end QuantumFractionalPower
