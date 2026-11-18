/- GID: D5/S3/Entropy/LopesOliveiraSource
   generality: G
   mirror-B: D5/B/S3/Entropy/LopesOliveiraSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-index full shifts and the all-law transport functionals. -/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory
noncomputable section
namespace D5.S3.Entropy.LopesOliveiraSource

abbrev Symbol (d : ℕ) := {j : ℕ // j ∈ Finset.Icc 1 d}
abbrev Omega (d : ℕ) := ℕ+ → Symbol d

def shift {d : ℕ} (x : Omega d) : Omega d := fun i => x ⟨i.val + 1, by omega⟩
def tailSigma {d : ℕ} : MeasurableSpace (Omega d) :=
  (inferInstance : MeasurableSpace (Omega d)).comap shift

def firstIndicator {d : ℕ} (j : Symbol d) (x : Omega d) : ℝ :=
  if x 1 = j then 1 else 0

def niEntropy {d : ℕ} (rho : Measure (Omega d)) : ℝ :=
  ∫ x, ∑ j : Symbol d, Real.negMulLog ((rho[firstIndicator j | tailSigma]) x) ∂rho

def niPressure {d : ℕ} (phi : Omega d → ℝ) : ℝ :=
  sSup {v | ∃ rho : Measure (Omega d), IsProbabilityMeasure rho ∧
    v = (∫ x, phi x ∂rho) + niEntropy rho}

private def indexEquiv (d : ℕ) : (ℕ → Symbol d) ≃ₜ Omega d where
  toEquiv := Equiv.arrowCongr Equiv.pnatEquivNat.symm (Equiv.refl _)
  continuous_toFun := continuous_pi fun i => continuous_apply (Equiv.pnatEquivNat i)
  continuous_invFun := continuous_pi fun n => continuous_apply (Nat.succPNat n)

local instance (d : ℕ) : MetricSpace (ℕ → Symbol d) :=
  PiNat.metricSpace (E := fun _ => Symbol d)

def distance {d : ℕ} (x y : Omega d) : ℝ :=
  dist (indexEquiv d |>.symm x) (indexEquiv d |>.symm y) / 2

def sourceMetric (d : ℕ) : MetricSpace (Omega d) :=
  MetricSpace.ofDistTopology distance
    (fun x => by simp [distance])
    (fun x y => by simp only [distance, dist_comm])
    (fun x y z => by
      have h := dist_triangle ((indexEquiv d).symm x) ((indexEquiv d).symm y)
        ((indexEquiv d).symm z)
      dsimp [distance]
      linarith)
    (fun s => by
      rw [← (indexEquiv d).isOpen_preimage, Metric.isOpen_iff]
      constructor
      · intro h x hx
        have hx2 : (indexEquiv d).symm x ∈ indexEquiv d ⁻¹' s := by simpa using hx
        obtain ⟨ε, hε, hball⟩ := h _ hx2
        refine ⟨ε / 2, by positivity, ?_⟩
        intro y hy
        have hn : (indexEquiv d).symm y ∈ Metric.ball ((indexEquiv d).symm x) ε := by
          simp only [Metric.mem_ball, dist_comm]
          dsimp [distance] at hy
          linarith
        simpa using hball hn
      · intro h z hz
        obtain ⟨ε, hε, hball⟩ := h (indexEquiv d z) hz
        refine ⟨2 * ε, by positivity, ?_⟩
        intro w hw
        apply hball (indexEquiv d w)
        dsimp [distance]
        simp only [Homeomorph.symm_apply_apply]
        have hn : dist z w < 2 * ε := by simpa [Metric.mem_ball, dist_comm] using hw
        linarith)
    (fun x y h => (indexEquiv d).symm.injective (by
      apply eq_of_dist_eq_zero
      dsimp [distance] at h
      linarith))

def couplings {d : ℕ} (eta xi : Measure (Omega d)) : Set (Measure (Omega d × Omega d)) :=
  {pi | IsProbabilityMeasure pi ∧ Measure.map Prod.fst pi = eta ∧
    Measure.map Prod.snd pi = xi}

def wassersteinOne {d : ℕ} (eta xi : Measure (Omega d)) : ℝ :=
  sInf {v | ∃ pi ∈ couplings eta xi, v = ∫ p, distance p.1 p.2 ∂pi}

def IsHolder {d : ℕ} (phi : Omega d → ℝ) : Prop :=
  ∃ alpha : ℝ, 0 < alpha ∧ ∃ H : ℝ, 0 ≤ H ∧
    ∀ x y, |phi x - phi y| ≤ H * (distance x y) ^ alpha

end D5.S3.Entropy.LopesOliveiraSource
