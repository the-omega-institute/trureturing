/- GID: D5/S3/Weil/TestFunctions/ExternalSupportInvisibility
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/ExternalSupportInvisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: External distributional support cannot change a compactly supported Weil pairing. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.Analysis.Distribution.Support
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite

namespace D5.S3.Weil.TestFunctions.ExternalSupportInvisibility

open Complex Function MeasureTheory Set Zeta23
open scoped Convolution ContDiff Manifold Pointwise SchwartzMap

noncomputable section

private theorem apply_eq_zero_of_dsupport_subset_compl
    (kappa : 𝓢'(ℝ, ℂ)) {U : Set ℝ}
    {phi : ℝ → ℂ} (hphiSmooth : ContDiff ℝ ∞ phi)
    (hphiCompact : HasCompactSupport phi) (hphiSupport : tsupport phi ⊆ U)
    (hkappa : Distribution.dsupport kappa ⊆ Uᶜ) :
    kappa (hphiCompact.toSchwartzMap hphiSmooth) = 0 := by
  classical
  have hnot : ∀ x : tsupport phi, x.1 ∉ Distribution.dsupport kappa := by
    intro x hx
    exact hkappa hx (hphiSupport x.2)
  choose V hvan hopen hmem using fun x : tsupport phi =>
    (Distribution.notMem_dsupport_iff x.1).mp (hnot x)
  have hcover : tsupport phi ⊆ ⋃ x : tsupport phi, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩
  obtain ⟨rho, hrho⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ℝ)) (isClosed_tsupport phi) V hopen hcover
  have hfinite : {i | (support (rho i) ∩ tsupport phi).Nonempty}.Finite :=
    rho.locallyFinite.finite_nonempty_inter_compact hphiCompact
  let indices := hfinite.toFinset
  let piece : (tsupport phi) → 𝓢(ℝ, ℂ) := fun i =>
    ((hphiCompact.mul_left : HasCompactSupport (fun x => (rho i x : ℂ) * phi x)).toSchwartzMap
      (by
        have hrhoSmooth : ContDiff ℝ ∞ (rho i : ℝ → ℝ) := (rho i).contMDiff.contDiff
        exact (Complex.ofRealCLM.contDiff.comp hrhoSmooth).mul hphiSmooth))
  have hpieceSupport (i : tsupport phi) : tsupport (piece i) ⊆ V i := by
    have hcast : tsupport (fun x => (rho i x : ℂ)) = tsupport (rho i) := by
      unfold tsupport
      congr 1
      ext x
      simp only [mem_support, ne_eq, ofReal_eq_zero]
    exact tsupport_mul_subset_left.trans (hcast.trans_le (hrho i))
  have hpieceZero (i : tsupport phi) : kappa (piece i) = 0 :=
    hvan i (piece i) (hpieceSupport i)
  have hdecomp : hphiCompact.toSchwartzMap hphiSmooth = ∑ i ∈ indices, piece i := by
    ext x
    by_cases hx : phi x = 0
    · change phi x = _
      rw [sum_apply]
      change phi x = ∑ i ∈ indices, (rho i x : ℂ) * phi x
      simp [hx]
    · have hxSupport : x ∈ tsupport phi := subset_tsupport phi hx
      have hsum : ∑ i ∈ indices, rho i x = 1 := by
        rw [← rho.sum_eq_one hxSupport]
        apply (finsum_eq_sum_of_support_subset _ ?_).symm
        intro i hi
        apply hfinite.mem_toFinset.mpr
        exact ⟨x, hi, hxSupport⟩
      have hsumComplex : ∑ i ∈ indices, (rho i x : ℂ) = 1 := by
        exact_mod_cast hsum
      change phi x = _
      rw [sum_apply]
      change phi x = ∑ i ∈ indices, (rho i x : ℂ) * phi x
      rw [← Finset.sum_mul, hsumComplex, one_mul]
  rw [hdecomp, map_sum]
  simp [hpieceZero]

/-- A tempered distribution supported outside `(-2L, 2L)` is invisible to every Weil
correlation of smooth compact tests supported in `(-L, L)`. -/
theorem external_support_invisibility
    (L : ℝ) (weilSource kappa : 𝓢'(ℝ, ℂ))
    (hkappa : Distribution.dsupport kappa ⊆ (Ioo (-(2 * L)) (2 * L))ᶜ)
    (f h : ℝ → ℂ) (hfSmooth : ContDiff ℝ ∞ f) (hhSmooth : ContDiff ℝ ∞ h)
    (hfCompact : HasCompactSupport f) (hhCompact : HasCompactSupport h)
    (hfSupport : tsupport f ⊆ Ioo (-L) L) (hhSupport : tsupport h ⊆ Ioo (-L) L) :
    let correlation := EF.weilTest f h
    let hcorrelationCompact : HasCompactSupport correlation :=
      EF.weilTest_hasCompactSupport hfCompact hhCompact
    let hcorrelationSmooth : ContDiff ℝ ∞ correlation :=
      (by
        have htildeSmooth : ContDiff ℝ ∞ (EF.tilde h) := by
          exact Complex.conjCLE.contDiff.comp (hhSmooth.comp contDiff_neg)
        exact (EF.hasCompactSupport_tilde hhCompact).contDiff_convolution_right
          (n := (⊤ : ℕ∞)) (ContinuousLinearMap.mul ℝ ℂ)
          hfSmooth.continuous.locallyIntegrable htildeSmooth)
    let correlationTest := hcorrelationCompact.toSchwartzMap hcorrelationSmooth
    (weilSource + kappa) correlationTest = weilSource correlationTest := by
  dsimp only
  have hcorrelationSmooth : ContDiff ℝ ∞ (EF.weilTest f h) := by
    have htildeSmooth : ContDiff ℝ ∞ (EF.tilde h) := by
      exact Complex.conjCLE.contDiff.comp (hhSmooth.comp contDiff_neg)
    exact (EF.hasCompactSupport_tilde hhCompact).contDiff_convolution_right
      (n := (⊤ : ℕ∞)) (ContinuousLinearMap.mul ℝ ℂ)
      hfSmooth.continuous.locallyIntegrable htildeSmooth
  have hcorrelationSupport : tsupport (EF.weilTest f h) ⊆ Ioo (-(2 * L)) (2 * L) := by
    have hclosed : IsClosed (tsupport f + -tsupport h) :=
      (hfCompact.isCompact.add hhCompact.isCompact.neg).isClosed
    refine (closure_minimal ((support_convolution_subset _).trans ?_) hclosed).trans ?_
    · rintro x ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, subset_tsupport f ha, b, EF.support_tilde_subset h hb, rfl⟩
    · rintro x ⟨a, ha, b, hb, rfl⟩
      have ha' := hfSupport ha
      have hb' := hhSupport (Set.mem_neg.mp hb)
      simp only [mem_Ioo] at ha' hb' ⊢
      constructor <;> linarith
  have hkappaZero := apply_eq_zero_of_dsupport_subset_compl kappa
    hcorrelationSmooth (EF.weilTest_hasCompactSupport hfCompact hhCompact)
    hcorrelationSupport hkappa
  change weilSource _ + kappa _ = weilSource _
  rw [hkappaZero, add_zero]

#print axioms external_support_invisibility

end

end D5.S3.Weil.TestFunctions.ExternalSupportInvisibility
