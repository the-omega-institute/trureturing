/- GID: D5/S3/Zeros/FirstOffLineMahlerJump
   generality: G
   mirror-B: D5/B/S3/Zeros/FirstOffLineMahlerJump
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite off-line root-pair filtration has a positive Mahler jump at its first height. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace D5.S3.Zeros.FirstOffLineMahlerJump

/-- The Mahler free energy of the representative off-line root pairs visible by height `T`. -/
noncomputable def mahlerFreeEnergy {ι : Type*} (roots : Finset ι)
    (height radius : ι → Real) (multiplicity : ι → Nat) (T : Real) : Real :=
  ∑ i ∈ roots.filter (fun i => height i ≤ T), (multiplicity i : Real) * Real.log (radius i)

/-- Before the first off-line height the Mahler free energy is zero, at the first height it is
strictly positive, and a unique representative pair contributes exactly `m * log r`. -/
theorem first_off_line_mahler_jump {ι : Type*} (roots : Finset ι)
    (height radius : ι → Real) (multiplicity : ι → Nat) (T0 : Real)
    (hT0 : 0 < T0) (firstRoot : ι) (hFirstMem : firstRoot ∈ roots)
    (hFirstHeight : height firstRoot = T0)
    (hLeast : ∀ i ∈ roots, T0 ≤ height i)
    (hRadius : ∀ i ∈ roots, 1 < radius i)
    (hMultiplicity : ∀ i ∈ roots, 0 < multiplicity i) :
    (∀ T, T < T0 → mahlerFreeEnergy roots height radius multiplicity T = 0) ∧
      0 < mahlerFreeEnergy roots height radius multiplicity T0 ∧
      ((∀ i ∈ roots, height i = T0 → i = firstRoot) →
        mahlerFreeEnergy roots height radius multiplicity T0 =
          (multiplicity firstRoot : Real) * Real.log (radius firstRoot)) := by
  have hBefore : ∀ T, T < T0 → mahlerFreeEnergy roots height radius multiplicity T = 0 := by
    intro T hT
    rw [mahlerFreeEnergy, Finset.sum_eq_zero]
    intro i hi
    obtain ⟨hiRoots, hiHeight⟩ := Finset.mem_filter.mp hi
    exact (not_le_of_gt (hT.trans_le (hLeast i hiRoots)) hiHeight).elim

  have hPositive : 0 < mahlerFreeEnergy roots height radius multiplicity T0 := by
    rw [mahlerFreeEnergy]
    apply Finset.sum_pos'
    · intro i hi
      have hiRoots := (Finset.mem_filter.mp hi).1
      exact (mul_pos (Nat.cast_pos.mpr (hMultiplicity i hiRoots))
        (Real.log_pos (hRadius i hiRoots))).le
    · refine ⟨firstRoot, Finset.mem_filter.mpr ⟨hFirstMem, ?_⟩, ?_⟩
      · rw [hFirstHeight]
      · exact mul_pos (Nat.cast_pos.mpr (hMultiplicity firstRoot hFirstMem))
          (Real.log_pos (hRadius firstRoot hFirstMem))

  refine ⟨hBefore, hPositive, ?_⟩
  intro hUnique
  classical
  have hFilter : roots.filter (fun i => height i ≤ T0) = {firstRoot} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hiRoots, hiHeight⟩
      exact hUnique i hiRoots (le_antisymm hiHeight (hLeast i hiRoots))
    · rintro rfl
      exact ⟨hFirstMem, hFirstHeight.le⟩
  simp [mahlerFreeEnergy, hFilter]

end D5.S3.Zeros.FirstOffLineMahlerJump
