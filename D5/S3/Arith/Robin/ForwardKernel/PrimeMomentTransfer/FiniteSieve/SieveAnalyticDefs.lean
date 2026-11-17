/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real sieve weights specify scalar and smoothed interval moment hypotheses. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.FiniteSieveDefs
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Real-weight moments and shifted smooth interval averages for finite sieves. -/

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

def sieveWeightedSum (Q : ℕ+) (H : ℝ) (f : ℝ → ℝ) (x : ZMod (Q : ℕ)) : ℝ :=
  ∑ᶠ d : ℕ, f ((d : ℝ) / H) * sieveVariable Q d x
def sieveScale (H : ℝ) : ℝ := Real.sqrt (H * Real.log H)
def sieveNorm4 (Q : ℕ+) (F : ZMod (Q : ℕ) → ℝ) : ℝ :=
  (sieveExpectation Q (fun x => |F x| ^ 4)) ^ (1 / 4 : ℝ)
def sieveUniformMeasure (Q : ℕ+) : Measure (ZMod (Q : ℕ)) := (Q : ENNReal)⁻¹ • Measure.count
def sieveProductMoment {k : ℕ} (Q : ℕ+) (F : Fin k → ZMod (Q : ℕ) → ℝ) : ℝ :=
  sieveExpectation Q (fun x => ∏ i, F i x)
def sieveWickPairing (Q : ℕ+) (F : Fin 4 → ZMod (Q : ℕ) → ℝ) : ℝ :=
  sieveProductMoment Q ![F 0,F 1] * sieveProductMoment Q ![F 2,F 3] +
  sieveProductMoment Q ![F 0,F 2] * sieveProductMoment Q ![F 1,F 3] +
  sieveProductMoment Q ![F 0,F 3] * sieveProductMoment Q ![F 1,F 2]
def sieveWickDefect (Q : ℕ+) (F : Fin 4 → ZMod (Q : ℕ) → ℝ) : ℝ := sieveProductMoment Q F - sieveWickPairing Q F
def normalizedIntervalSum (Q : ℕ+) (H a b : ℝ) : ZMod (Q : ℕ) → ℝ := fun x => sieveIntervalSum Q H a b x / sieveScale H
def normalizedWeightedSum (Q : ℕ+) (H : ℝ) (f : ℝ → ℝ) : ZMod (Q : ℕ) → ℝ := fun x => sieveWeightedSum Q H f x / sieveScale H
def MSFinite : Prop := ∃ C₂ C₄ : ℝ, 0 ≤ C₂ ∧ 0 ≤ C₄ ∧
  (∀ Q : ℕ+, ∀ n : ℕ, 1 ≤ n →
    sieveExpectation Q (fun x => sieveIntervalSum Q 1 0 n x ^ 2) ≤ C₂ * n * sieveDensity Q) ∧
  (∀ Q : ℕ+, ∀ n : ℕ, 1 ≤ n →
    |sieveExpectation Q (fun x => sieveIntervalSum Q 1 0 n x ^ 4) -
      3 * (sieveExpectation Q (fun x => sieveIntervalSum Q 1 0 n x ^ 2)) ^ 2| ≤
      C₄ * (n : ℝ) ^ (2 - 1 / 28 : ℝ) * sieveDensity Q ^ 18)


def sieveSmoothingBump (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (2*δ : ℝ) where
  rIn := δ/2
  rOut := δ
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def smoothingKernel (δ : ℝ) (hδ : 0 < δ) : ℝ → ℝ := (sieveSmoothingBump δ hδ).normed volume


def smoothedInterval (δ : ℝ) (hδ : 0 < δ) (a b x : ℝ) : ℝ :=
  ∫ r, smoothingKernel δ hδ r * (Ioc (a+r) (b+r)).indicator (fun _ : ℝ => (1 : ℝ)) x

structure KuperbergSmoothed : Prop where
  third : ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ a b : Fin 3 → ℝ,
    (∀ i, 0 ≤ a i ∧ a i ≤ b i) → ∃ C : ℝ, 0 ≤ C ∧
    ∀ Q : ℕ+, Squarefree (Q : ℕ) → ∀ h : ℕ, 3 ≤ h →
      |sieveProductMoment Q (fun i => sieveWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)))| ≤
        C * (h : ℝ)^(3/2-1/21 : ℝ) * sieveDensity Q^(19/2 : ℝ)
  fourth : ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ a b : Fin 4 → ℝ,
    (∀ i, 0 ≤ a i ∧ a i ≤ b i) → ∃ C : ℝ, 0 ≤ C ∧
    ∀ Q : ℕ+, Squarefree (Q : ℕ) → ∀ h : ℕ, 3 ≤ h →
      |sieveWickDefect Q (fun i => sieveWeightedSum Q h (smoothedInterval δ hδ (a i) (b i)))| ≤
        C * (h : ℝ)^(2-1/28 : ℝ) * sieveDensity Q^18


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
