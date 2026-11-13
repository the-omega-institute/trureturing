/- GID: D5/S3/Fourier/GoldenModelSetFibreBridge
   generality: I
   mirror-B: D5/B/S3/Fourier/GoldenModelSetFibreBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=gid:D5/S3/Fourier/GoldenModelSetFibreBridge.golden_modelSet_fiber_witness
   digest: Floor-selected fibres connect the golden model set to its mechanical word. -/

import D5.S0.Carrier.Euclidean
import D5.S3.Fourier.GoldenModelSetDelone
import D5.S1.Words.GoldenMechanicalWord

/-!
This open bridge module keeps the frozen Delone certificate unchanged while
exhibiting an explicit floor lift in every internal fibre. On natural fibres,
the integral coordinate is the Beatty floor and its successive difference is
the corresponding golden mechanical letter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Fourier.GoldenModelSetFibreBridge

open D5.S0.Carrier D5.S1.Scale
open D5.S1.Deficit.GoldenModelSetSelfSimilar
open D5.S1.Words
open D5.S3.Fourier.GoldenModelSetDelone
open GoldenCutProjectSchemeAdapter DeloneModelSetCertificate

/- The canonical floor-selected lift in the fibre with internal coordinate `b`. -/
noncomputable def goldenWindowFiberLift (b : ℤ) : GoldenInt :=
  ⟨⌊Real.goldenRatio - 1 - (b : ℝ) * (1 - Real.goldenRatio)⌋, b⟩

/- Every integer fibre has an explicit lift in the closed golden window. -/
theorem golden_window_fiber_lift_mem (b : ℤ) :
    embedding (conj (goldenWindowFiberLift b)) ∈ goldenWindow := by
  let a : ℤ := ⌊Real.goldenRatio - 1 - (b : ℝ) * (1 - Real.goldenRatio)⌋
  let u : GoldenInt := ⟨a, b⟩
  have ha₀ := Int.floor_le
    (Real.goldenRatio - 1 - (b : ℝ) * (1 - Real.goldenRatio))
  have ha₁ := Int.lt_floor_add_one
    (Real.goldenRatio - 1 - (b : ℝ) * (1 - Real.goldenRatio))
  have hc : embedding (conj u) = (a : ℝ) + (b : ℝ) * (1 - Real.goldenRatio) := by
    simp [u, embedding_apply, conj]
    ring
  have hlow : Real.goldenRatio - 2 ≤ embedding (conj u) := by
    rw [hc]
    change (a : ℝ) ≤ _ at ha₀
    change _ < (a : ℝ) + 1 at ha₁
    linarith
  have hupp : embedding (conj u) ≤ Real.goldenRatio - 1 := by
    rw [hc]
    change (a : ℝ) ≤ _ at ha₀
    linarith
  have hu : u = goldenWindowFiberLift b := by
    simp [u, a, goldenWindowFiberLift]
  rw [goldenWindow_eq]
  simpa [hu] using (show Real.goldenRatio - 2 ≤ embedding (conj u) ∧
    embedding (conj u) ≤ Real.goldenRatio - 1 from ⟨hlow, hupp⟩)

/- The floor-selected lift gives a point of the physical golden model set. -/
theorem golden_modelSet_fiber_witness (b : ℤ) :
    embedding (goldenWindowFiberLift b) ∈ modelSet goldenWindow := by
  exact ⟨goldenWindowFiberLift b, rfl, golden_window_fiber_lift_mem b⟩

/- On nonnegative fibres the selected integral coordinate is a Beatty floor. -/
theorem golden_window_fiber_lift_a_nat (n : ℕ) :
    (goldenWindowFiberLift (n : ℤ)).a =
      ⌊((n + 1 : ℕ) : ℝ) * goldenMechanicalSlope⌋ := by
  have hslope : goldenMechanicalSlope = Real.goldenRatio - 1 := by
    rw [goldenMechanicalSlope, Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
    ring
  change ⌊Real.goldenRatio - 1 - (n : ℝ) * (1 - Real.goldenRatio)⌋ =
    ⌊((n + 1 : ℕ) : ℝ) * goldenMechanicalSlope⌋
  rw [hslope]
  congr 1
  push_cast
  ring

/- Consecutive natural fibres change by exactly the corresponding mechanical letter. -/
theorem golden_window_fiber_step (n : ℕ) :
    (goldenWindowFiberLift ((n + 1 : ℕ) : ℤ)).a -
        (goldenWindowFiberLift (n : ℤ)).a =
      goldenMechanicalLetter (n + 1) := by
  rw [golden_window_fiber_lift_a_nat, golden_window_fiber_lift_a_nat]
  simp only [goldenMechanicalLetter, add_assoc]

end D5.S3.Fourier.GoldenModelSetFibreBridge
