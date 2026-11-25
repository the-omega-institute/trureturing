/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumProduct
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-degree four-copy refined BMV bound for singular three-value spectra. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumSigns

/-! The singular four-copy comparison obtained by applying the five uniform signs. -/

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV.ThreeBlockGram.ZeroSpectrum

private theorem signs_at_root (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Signs (p : ℝ) r (root p r) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  obtain ⟨ha, hb, h1, h2, h3⟩ := RefinedBMV.ZeroSpectrum.all_signs (p : ℝ) r hp' hr hr1
  exact ⟨ha, hb, h1, h2, h3⟩

/-- The refined four-copy lower bound for spectra contained in `{0,r,1}`
and every positive integral first degree. Spectral multiplicities are arbitrary. -/
theorem product_bound_zero_spectrum {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hspectrum : ∀ a, ∃ i : Fin 3, hA.isHermitian.eigenvalues a =
      (![0,r,1] : Fin 3 → ℝ) i) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B :=
  product_bound_of_signs p hp hr hr1 A B hA hB hspectrum (signs_at_root p hp hr hr1.le)

/-- The same comparison with arbitrary positive top spectral value. -/
theorem product_bound_scaled_zero_spectrum {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (hp : 0 < p) {r t : ℝ} (hr : 0 < r) (hrt : r < t) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hspectrum : ∀ a, ∃ i : Fin 3, hA.isHermitian.eigenvalues a =
      (![0,r,t] : Fin 3 → ℝ) i) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B :=
  have ht := hr.trans hrt
  have hratio : r/t ≤ 1 := (div_le_iff₀ ht).mpr (by simpa using hrt.le)
  scaled_product_bound_of_signs p hp hr hrt A B hA hB hspectrum
    (signs_at_root p hp (div_pos hr ht) hratio)

#print axioms product_bound_zero_spectrum
#print axioms product_bound_scaled_zero_spectrum

end RefinedBMV.ThreeBlockGram.ZeroSpectrum
