/- GID: D5/S3/Weil/ZetaGamma/ObserverModeConfinement
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/ObserverModeConfinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Confine low observer-mode multipliers to finite modes and a bounded frequency window. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenVerticalSampling
import D5.S3.Weil.ZetaCore.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Compactness.Compact

/-!
# Observer-mode confinement

The concrete completed-zeta digamma multiplier grows jointly along the
observer-mode and frequency directions.  Subtracting a uniformly bounded
fixed-support prime multiplier preserves that growth, so strict sublevels
have only finitely many integer modes and bounded frequency sections.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaGamma.ObserverModeConfinement

open Bornology Filter Set Topology
open D5.S3.Observer.GoldenPrimeCircle.GoldenVerticalSampling

/-- Joint proper growth of the symmetric Archimedean mode, together with a
uniform bound on the fixed-support prime multiplier, confines every strict
sublevel to finitely many modes with bounded frequency sections.  In
particular, all negative values lie in one finite-mode, bounded-frequency
box. -/
theorem two_direction_archimedean_confinement
    (primeMultiplier : ℝ → ℤ → ℝ → ℝ) (L A B : ℝ)
    (primeBound : ∀ n t, |primeMultiplier L n t| ≤ B) :
    let modeShift : ℤ → ℝ := fun n =>
      (n : ℝ) * goldenAngularFrequency
    let archimedeanMode : ℤ × ℝ → ℝ := fun nt =>
      (1 / 2) *
        (2 * Real.pi * Zeta23.mu (nt.2 + modeShift nt.1) +
          2 * Real.pi * Zeta23.mu (nt.2 - modeShift nt.1))
    Tendsto archimedeanMode (cocompact (ℤ × ℝ)) atTop →
      let jointMultiplier : ℤ × ℝ → ℝ := fun nt =>
        archimedeanMode nt - primeMultiplier L nt.1 nt.2
      let dangerousSet : Set (ℤ × ℝ) :=
        {nt | jointMultiplier nt < A}
      Set.Finite {n : ℤ | ∃ t : ℝ, (n, t) ∈ dangerousSet} ∧
        (∀ n : ℤ, IsBounded {t : ℝ | (n, t) ∈ dangerousSet}) ∧
        ∃ modes : Finset ℤ, ∃ radius : ℝ, 0 ≤ radius ∧
          ∀ n : ℤ, ∀ t : ℝ, jointMultiplier (n, t) < 0 →
            n ∈ modes ∧ |t| ≤ radius := by
  dsimp only
  intro archimedeanGrowth
  have hLarge :
      {nt : ℤ × ℝ |
        max A 0 + B ≤
          (1 / 2) *
            (2 * Real.pi * Zeta23.mu
                (nt.2 + (nt.1 : ℝ) * goldenAngularFrequency) +
              2 * Real.pi * Zeta23.mu
                (nt.2 - (nt.1 : ℝ) * goldenAngularFrequency))} ∈
        cocompact (ℤ × ℝ) :=
    archimedeanGrowth (eventually_ge_atTop (max A 0 + B))
  obtain ⟨K, hKCompact, hKLarge⟩ := mem_cocompact.mp hLarge
  have hOutside (nt : ℤ × ℝ) (hnt : nt ∉ K) :
      max A 0 ≤
        (1 / 2) *
            (2 * Real.pi * Zeta23.mu
                (nt.2 + (nt.1 : ℝ) * goldenAngularFrequency) +
              2 * Real.pi * Zeta23.mu
                (nt.2 - (nt.1 : ℝ) * goldenAngularFrequency)) -
          primeMultiplier L nt.1 nt.2 := by
    have hArch := hKLarge hnt
    change max A 0 + B ≤
      (1 / 2) *
        (2 * Real.pi * Zeta23.mu
            (nt.2 + (nt.1 : ℝ) * goldenAngularFrequency) +
          2 * Real.pi * Zeta23.mu
            (nt.2 - (nt.1 : ℝ) * goldenAngularFrequency)) at hArch
    have hPrime := primeBound nt.1 nt.2
    have hPrimeUpper : primeMultiplier L nt.1 nt.2 ≤ B :=
      (le_abs_self _).trans hPrime
    linarith
  have hDangerousSubset :
      {nt : ℤ × ℝ |
        (1 / 2) *
              (2 * Real.pi * Zeta23.mu
                  (nt.2 + (nt.1 : ℝ) * goldenAngularFrequency) +
                2 * Real.pi * Zeta23.mu
                  (nt.2 - (nt.1 : ℝ) * goldenAngularFrequency)) -
            primeMultiplier L nt.1 nt.2 < A} ⊆ K := by
    intro nt hnt
    by_contra hntK
    exact (not_lt_of_ge ((le_max_left A 0).trans (hOutside nt hntK))) hnt
  have hNegativeSubset :
      {nt : ℤ × ℝ |
        (1 / 2) *
              (2 * Real.pi * Zeta23.mu
                  (nt.2 + (nt.1 : ℝ) * goldenAngularFrequency) +
                2 * Real.pi * Zeta23.mu
                  (nt.2 - (nt.1 : ℝ) * goldenAngularFrequency)) -
            primeMultiplier L nt.1 nt.2 < 0} ⊆ K := by
    intro nt hnt
    by_contra hntK
    exact (not_lt_of_ge ((le_max_right A 0).trans (hOutside nt hntK))) hnt
  have hModeProjectionFinite : (Prod.fst '' K).Finite :=
    (hKCompact.image continuous_fst).finite_of_discrete
  have hFrequencyProjectionBounded : IsBounded (Prod.snd '' K) :=
    (hKCompact.image continuous_snd).isBounded
  have hDangerousModes :
      Set.Finite {n : ℤ | ∃ t : ℝ,
        (1 / 2) *
              (2 * Real.pi * Zeta23.mu
                  (t + (n : ℝ) * goldenAngularFrequency) +
                2 * Real.pi * Zeta23.mu
                  (t - (n : ℝ) * goldenAngularFrequency)) -
            primeMultiplier L n t < A} := by
    apply hModeProjectionFinite.subset
    rintro n ⟨t, hnt⟩
    exact ⟨(n, t), hDangerousSubset hnt, rfl⟩
  have hDangerousSections : ∀ n : ℤ, IsBounded {t : ℝ |
      (1 / 2) *
            (2 * Real.pi * Zeta23.mu
                (t + (n : ℝ) * goldenAngularFrequency) +
              2 * Real.pi * Zeta23.mu
                (t - (n : ℝ) * goldenAngularFrequency)) -
          primeMultiplier L n t < A} := by
    intro n
    apply hFrequencyProjectionBounded.subset
    intro t hnt
    exact ⟨(n, t), hDangerousSubset hnt, rfl⟩
  obtain ⟨r, hr⟩ := hFrequencyProjectionBounded.subset_closedBall 0
  refine ⟨hDangerousModes, hDangerousSections,
    hModeProjectionFinite.toFinset, max r 0, le_max_right _ _, ?_⟩
  intro n t hnt
  have hntK : (n, t) ∈ K := hNegativeSubset hnt
  constructor
  · rw [hModeProjectionFinite.mem_toFinset]
    exact ⟨(n, t), hntK, rfl⟩
  · have htProjection : t ∈ Prod.snd '' K := ⟨(n, t), hntK, rfl⟩
    have htBall := hr htProjection
    rw [Metric.mem_closedBall, Real.dist_eq] at htBall
    simpa only [sub_zero] using htBall.trans (le_max_left r 0)

#print axioms two_direction_archimedean_confinement

end D5.S3.Weil.ZetaGamma.ObserverModeConfinement
