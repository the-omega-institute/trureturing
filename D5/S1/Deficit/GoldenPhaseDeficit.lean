/- GID: D5/S1/Deficit/GoldenPhaseDeficit
   generality: I
   mirror-B: D5/B/S1/Deficit/GoldenPhaseDeficit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden Beatty deficit is classified exactly by two phase-sum thresholds. -/

import Mathlib.NumberTheory.Real.GoldenRatio

/- Provenance: a new floor-arithmetic proof over pinned mathlib's
   `Int.floor_add_fract`, `Int.floor_intCast_add`, and `Int.floor_eq_iff`.
   Mathlib supplies the fractional-part and golden-ratio identities but no
   declaration that performs this two-threshold classification. -/

namespace D5.S1.Deficit.GoldenPhaseDeficit

/-- The canonical integer reading obtained by shifting the golden Beatty sequence. -/
noncomputable def goldenShift (v : ℕ) : ℤ :=
  ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ - 1

/-- The fractional phase of the shifted golden orbit. -/
noncomputable def goldenPhase (v : ℕ) : ℝ :=
  Int.fract (((v : ℝ) + 1) * Real.goldenRatio)

/-- The additive coboundary of the golden Beatty shift. -/
noncomputable def beattyDeficit (v₁ v₂ : ℕ) : ℤ :=
  goldenShift v₁ + goldenShift v₂ - goldenShift (v₁ + v₂)

private theorem beattyDeficit_floor_formula (v₁ v₂ : ℕ) :
    beattyDeficit v₁ v₂ =
      -1 - ⌊goldenPhase v₁ + goldenPhase v₂ - Real.goldenRatio⌋ := by
  let x : ℝ := ((v₁ : ℝ) + 1) * Real.goldenRatio
  let y : ℝ := ((v₂ : ℝ) + 1) * Real.goldenRatio
  let z : ℝ := (((v₁ + v₂ : ℕ) : ℝ) + 1) * Real.goldenRatio
  have hz : z = x + y - Real.goldenRatio := by
    dsimp [x, y, z]
    push_cast
    ring
  have hdecomp :
      z = (((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) +
        (Int.fract x + Int.fract y - Real.goldenRatio)) := by
    rw [hz]
    have hx := Int.floor_add_fract x
    have hy := Int.floor_add_fract y
    push_cast
    linarith
  have hfloor :
      ⌊z⌋ = ⌊x⌋ + ⌊y⌋ +
        ⌊Int.fract x + Int.fract y - Real.goldenRatio⌋ := by
    rw [hdecomp, Int.floor_intCast_add]
  rw [beattyDeficit, goldenShift, goldenPhase]
  change (⌊x⌋ - 1) + (⌊y⌋ - 1) - (⌊z⌋ - 1) =
    -1 - ⌊Int.fract x + Int.fract y - Real.goldenRatio⌋
  rw [hfloor]
  omega

/-- The Beatty deficit is positive below the lower phase threshold, negative
at or above the upper threshold, and zero throughout the intervening band. -/
theorem golden_phase_deficit (v₁ v₂ : ℕ) :
    (beattyDeficit v₁ v₂ = 1 ↔
      goldenPhase v₁ + goldenPhase v₂ < Real.goldenRatio⁻¹) ∧
    (beattyDeficit v₁ v₂ = -1 ↔
      Real.goldenRatio ≤ goldenPhase v₁ + goldenPhase v₂) ∧
    (beattyDeficit v₁ v₂ = 0 ↔
      Real.goldenRatio⁻¹ ≤ goldenPhase v₁ + goldenPhase v₂ ∧
        goldenPhase v₁ + goldenPhase v₂ < Real.goldenRatio) := by
  let q : ℝ := goldenPhase v₁ + goldenPhase v₂
  have hq_nonneg : 0 ≤ q := by
    dsimp [q, goldenPhase]
    exact add_nonneg (Int.fract_nonneg _) (Int.fract_nonneg _)
  have hq_lt_two : q < 2 := by
    dsimp [q, goldenPhase]
    linarith [Int.fract_lt_one (((v₁ : ℝ) + 1) * Real.goldenRatio),
      Int.fract_lt_one (((v₂ : ℝ) + 1) * Real.goldenRatio)]
  have hinv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hformula : beattyDeficit v₁ v₂ =
      -1 - ⌊q - Real.goldenRatio⌋ := by
    simpa [q] using beattyDeficit_floor_formula v₁ v₂
  constructor
  · constructor
    · intro hc
      have hfloor : ⌊q - Real.goldenRatio⌋ = -2 := by omega
      have hupper := (Int.floor_eq_iff.mp hfloor).2
      rw [hinv]
      norm_num at hupper
      linarith
    · intro hq
      change q < Real.goldenRatio⁻¹ at hq
      have hlower : ((-2 : ℤ) : ℝ) ≤ q - Real.goldenRatio := by
        norm_num
        linarith [Real.goldenRatio_lt_two]
      have hupper : q - Real.goldenRatio < (-2 : ℤ) + 1 := by
        rw [hinv] at hq
        norm_num
        linarith
      have hfloor : ⌊q - Real.goldenRatio⌋ = -2 :=
        Int.floor_eq_iff.mpr ⟨hlower, hupper⟩
      omega
  constructor
  · constructor
    · intro hc
      have hfloor : ⌊q - Real.goldenRatio⌋ = 0 := by omega
      have hlower := (Int.floor_eq_iff.mp hfloor).1
      norm_num at hlower
      linarith
    · intro hq
      change Real.goldenRatio ≤ q at hq
      have hlower : ((0 : ℤ) : ℝ) ≤ q - Real.goldenRatio := by
        norm_num
        linarith
      have hupper : q - Real.goldenRatio < (0 : ℤ) + 1 := by
        norm_num
        linarith [Real.one_lt_goldenRatio]
      have hfloor : ⌊q - Real.goldenRatio⌋ = 0 :=
        Int.floor_eq_iff.mpr ⟨hlower, hupper⟩
      omega
  · constructor
    · intro hc
      have hfloor : ⌊q - Real.goldenRatio⌋ = -1 := by omega
      obtain ⟨hlower, hupper⟩ := Int.floor_eq_iff.mp hfloor
      rw [hinv]
      norm_num at hlower hupper
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hlower, hupper⟩
      change Real.goldenRatio⁻¹ ≤ q at hlower
      change q < Real.goldenRatio at hupper
      have hlower' : ((-1 : ℤ) : ℝ) ≤ q - Real.goldenRatio := by
        rw [hinv] at hlower
        norm_num
        linarith
      have hupper' : q - Real.goldenRatio < (-1 : ℤ) + 1 := by
        norm_num
        linarith
      have hfloor : ⌊q - Real.goldenRatio⌋ = -1 :=
        Int.floor_eq_iff.mpr ⟨hlower', hupper'⟩
      omega

end D5.S1.Deficit.GoldenPhaseDeficit
