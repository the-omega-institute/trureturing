/- GID: D5/S3/Arith/Lattices/Klartag/State/StepGlue
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/StepGlue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.StepInputs
import D5.S3.Arith.Lattices.Klartag.Walk.StepInputs2

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.StepGlue

open MeasureTheory
open ProbabilityTheory
open Matrix
open Finset
open Module
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StepInputs2

set_option linter.unusedSectionVars false

noncomputable section

section Currency

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι]

/-- Each coordinate of a standard Gaussian on `EuclideanSpace ℝ ι` is `N(0,1)`. -/
theorem stdGaussian_coord_law (p : ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x p) = gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian (ι := ι), Measure.map_map (by fun_prop) (by fun_prop),
    show ((fun x : EuclideanSpace ℝ ι => x p) ∘ (WithLp.toLp 2))
      = fun (x : ι → ℝ) => x p from rfl]
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) p).map_eq

/-- A random variable with the standard Gaussian law has `N(0,1)` coordinates. -/
theorem coord_law {ξ : Ω → EuclideanSpace ℝ ι} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι)) (p : ι) :
    P.map (fun ω => ξ ω p) = gaussianReal 0 1 := by
  rw [show (fun ω => ξ ω p) = (fun x : EuclideanSpace ℝ ι => x p) ∘ ξ from rfl,
    ← Measure.map_map (by fun_prop) hξ, hlaw, stdGaussian_coord_law]

/-- …and independent coordinates. -/
theorem coord_indep {ξ : Ω → EuclideanSpace ℝ ι} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι)) :
    iIndepFun (fun (p : ι) (ω : Ω) => ξ ω p) P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun p => (Measurable.aemeasurable (by fun_prop)))]
  have hofLp : (stdGaussian (EuclideanSpace ℝ ι)).map WithLp.ofLp
      = Measure.pi (fun _ : ι => gaussianReal 0 1) := by
    rw [← map_pi_eq_stdGaussian (ι := ι), Measure.map_map (by fun_prop) (by fun_prop),
      show (WithLp.ofLp ∘ (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)) = id from rfl,
      Measure.map_id]
  have h1 : P.map (fun ω p => ξ ω p) = Measure.pi (fun _ : ι => gaussianReal 0 1) := by
    rw [show (fun (ω : Ω) (p : ι) => ξ ω p) = WithLp.ofLp ∘ ξ from rfl,
      ← Measure.map_map (by fun_prop) hξ, hlaw, hofLp]
  rw [h1]
  congr 1
  funext p
  rw [coord_law hξ hlaw]

/-- The chain's increment is `r • ξ` with `ξ` standard, so its coordinates are `N(0, r²)`. -/
theorem coord_law_smul {ξ : Ω → EuclideanSpace ℝ ι} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι)) (r : ℝ) (p : ι) :
    P.map (fun ω => (r • ξ ω) p) = gaussianReal 0 (Real.toNNReal (r ^ 2)) := by
  have hfun : (fun ω => (r • ξ ω) p) = (fun t : ℝ => r * t) ∘ (fun ω => ξ ω p) := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), coord_law hξ hlaw,
    show (fun t : ℝ => r * t) = (r * ·) from rfl, gaussianReal_map_const_mul]
  refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg r)]
  simp

/-- …and they stay independent. -/
theorem coord_indep_smul {ξ : Ω → EuclideanSpace ℝ ι} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι)) (r : ℝ) :
    iIndepFun (fun (p : ι) (ω : Ω) => (r • ξ ω) p) P :=
  (coord_indep hξ hlaw).comp (fun _ => fun t : ℝ => r * t) (fun _ => by fun_prop)

end Currency

section H3Chain

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end H3Chain

section GoodEvent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

def chainGood (r : ℝ) (W : Ω → EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ) (N : ℕ) (η : ℝ) : Set Ω :=
  D5.S3.Arith.Lattices.Klartag.Walk.StepInputs.goodEventUT r W thr ∩ stepGood ξ N η

/-- **The failure probability of the full good event**, the two costs added. -/
theorem measureReal_compl_chainGood_le {r : ℝ} (hr : 0 < r)
    {W : Ω → EuclideanSpace ℝ (UT n)} (hW : Measurable W)
    (hWlaw : P.map W = stdGaussian (EuclideanSpace ℝ (UT n)))
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {v : ℝ≥0}
    (hlaw : ∀ k, ∀ p : UT n, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    {η : ℝ} (hη : 0 < η) (N : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    P.real (chainGood r W ξ (6 * r * s * Real.sqrt n) N η)ᶜ
      ≤ 4 * Real.exp (-(s ^ 2 * n))
        + (N : ℝ) * ((Fintype.card (UT n) : ℝ)
            * (2 * Real.exp (-(η ^ 2 / (Fintype.card (UT n) : ℝ)) / (2 * v)))) := by
  have hcompl : (chainGood r W ξ (6 * r * s * Real.sqrt n) N η)ᶜ
      = (D5.S3.Arith.Lattices.Klartag.Walk.StepInputs.goodEventUT r W (6 * r * s * Real.sqrt n))ᶜ
        ∪ (stepGood ξ N η)ᶜ := by
    rw [chainGood, Set.compl_inter]
  rw [hcompl]
  refine (measureReal_union_le _ _).trans ?_
  exact add_le_add
    (D5.S3.Arith.Lattices.Klartag.Walk.StepInputs.measureReal_compl_goodEventUT_le hr hW hWlaw s hs)
    (measureReal_compl_stepGood_le hlaw hη N)

end GoodEvent

end

end D5.S3.Arith.Lattices.Klartag.State.StepGlue
