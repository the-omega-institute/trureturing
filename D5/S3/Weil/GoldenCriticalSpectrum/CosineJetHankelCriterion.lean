/- GID: D5/S3/Weil/GoldenCriticalSpectrum/CosineJetHankelCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/GoldenCriticalSpectrum/CosineJetHankelCriterion
   mirror-E: none(waiver:finite-spectral-criterion)
   anchors: []
   utility: none
   digest: A cosine and its first scale derivative remove even-sampling aliases in the finite Newton-Hankel critical-line criterion. -/

import OmegaMath.Analysis.CosineScaleJet
import D5.S3.Constants.NewtonHankelRealRootCriterion
import D5.S3.Weil.ZeroSum

/-!
# Paired cosine and scale-jet Hankel matrices

For a finite conjugation-stable spectrum, use the actual Weil spectral parameter
and any nonzero real sampling scale. Simultaneous positivity of the cosine and
scale-jet Newton-Hankel matrices is equivalent to critical-line or real-axis
location. Repeated nodes and arbitrary multiplicities are allowed.

The real-axis alternative is essential. No infinite zero sum, smooth-test
realization, or positivity of the complete Weil form is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.GoldenCriticalSpectrum.CosineJetHankelCriterion

open D5.S3.Weil.ZeroSum D5.S3.Weil.Convention
open D5.S3.Constants.NewtonHankelRealRootCriterion
open Omega.CosineScaleJet
open scoped ComplexConjugate

/-- A paired finite moment criterion retaining the real-axis degeneracy.
For a spectrum without real points the right side is exactly critical-line location. -/
theorem cosine_jet_hankel_iff_critical_or_real {d : ℕ}
    (rho : Fin d → ℂ) (t : ℝ) (ht : t ≠ 0)
    (hconj : ∀ w, w ∈ Finset.univ.image rho ↔
      conj w ∈ Finset.univ.image rho) :
    ((newtonHankel (fun j => value ((t : ℂ) * spectralParameter (rho j)))).PosSemidef ∧
      (newtonHankel (fun j => scaleJet ((t : ℂ) * spectralParameter (rho j)))).PosSemidef) ↔
      ∀ j, (rho j).re = criticalAbscissa ∨ (rho j).im = 0 := by
  classical
  have harg (w : ℂ) : (t : ℂ) * spectralParameter (conj w) =
      -conj ((t : ℂ) * spectralParameter w) := by
    simp [spectralParameter_conjugation]
  have hvalue (w : ℂ) :
      value ((t : ℂ) * spectralParameter (conj w)) =
        conj (value ((t : ℂ) * spectralParameter w)) := by
    rw [harg]
    simp [value, Complex.cos_conj]
  have hjet (w : ℂ) :
      scaleJet ((t : ℂ) * spectralParameter (conj w)) =
        conj (scaleJet ((t : ℂ) * spectralParameter w)) := by
    rw [harg]
    simp [scaleJet_eq, Complex.sin_conj] <;> ring
  have transport (f : ℂ → ℂ) (hf : ∀ w, f (conj w) = conj (f w)) :
      ∀ w, w ∈ Finset.univ.image (fun j => f (rho j)) ↔
        conj w ∈ Finset.univ.image (fun j => f (rho j)) := by
    have step : ∀ w, w ∈ Finset.univ.image (fun j => f (rho j)) →
        conj w ∈ Finset.univ.image (fun j => f (rho j)) := by
      intro w hw
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp
        ((hconj (rho j)).mp (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
      exact Finset.mem_image.mpr ⟨k, hk, by rw [heq, hf]⟩
    intro w
    exact ⟨step w, fun h => by simpa using step (conj w) h⟩
  rw [newtonHankel_posSemidef_iff_roots_real _
      (transport (fun w => value ((t : ℂ) * spectralParameter w)) hvalue),
    newtonHankel_posSemidef_iff_roots_real _
      (transport (fun w => scaleJet ((t : ℂ) * spectralParameter w)) hjet)]
  constructor
  · rintro ⟨hC, hJ⟩ j
    obtain ⟨a, ha⟩ := hC j
    obtain ⟨b, hb⟩ := hJ j
    have haxes := (real_iff_axes ((t : ℂ) * spectralParameter (rho j))).mp
      ⟨by rw [ha]; rfl, by rw [hb]; rfl⟩
    rcases haxes with hx | hy
    · right
      have h : t * (rho j).im = 0 := by
        simpa [spectralParameter, Complex.mul_re] using hx
      exact (mul_eq_zero.mp h).resolve_left ht
    · left
      have h : t * ((rho j).re - criticalAbscissa) = 0 := by
        simpa [spectralParameter, Complex.mul_im] using congrArg Neg.neg hy
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ht)
  · intro h
    have hreal (j : Fin d) :
        (value ((t : ℂ) * spectralParameter (rho j))).im = 0 ∧
        (scaleJet ((t : ℂ) * spectralParameter (rho j))).im = 0 := by
      apply (real_iff_axes _).mpr
      rcases h j with hj | hj
      · right
        simp [spectralParameter, hj, Complex.mul_im]
      · left
        simp [spectralParameter, hj, Complex.mul_re]
    constructor
    · intro j
      refine ⟨(value ((t : ℂ) * spectralParameter (rho j))).re, ?_⟩
      apply Complex.ext <;> simp [(hreal j).1]
    · intro j
      refine ⟨(scaleJet ((t : ℂ) * spectralParameter (rho j))).re, ?_⟩
      apply Complex.ext <;> simp [(hreal j).2]

#print axioms cosine_jet_hankel_iff_critical_or_real

end D5.S3.Weil.GoldenCriticalSpectrum.CosineJetHankelCriterion
