/- GID: D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/PaddedLawSetup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup

open MeasureTheory
open ProbabilityTheory
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA

noncomputable section

section ValueType

variable (E G : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

/-- **The value-type fact.**  The standard Gaussian on the `L²` product *is* the product of the two
standard Gaussians — so adjoining the fresh coordinate to the value type is exactly adjoining an
independent `N(0,1)`, with no second factor and no reshuffling. -/
theorem stdGaussian_prodL2 :
    ((stdGaussian E).prod (stdGaussian G)).map (WithLp.toLp 2)
      = stdGaussian (WithLp 2 (E × G)) := by
  refine Measure.ext_of_charFun ?_
  funext t
  have hmeas : Measurable (WithLp.toLp 2 : E × G → WithLp 2 (E × G)) :=
    WithLp.measurable_toLp _ _
  have hcont : Continuous fun y : WithLp 2 (E × G) =>
      Complex.exp ((⟪y, t⟫ : ℝ) * Complex.I) := by
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp
      (continuous_inner.comp (continuous_id.prodMk continuous_const))
  rw [charFun_apply, integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
  have hsplit : ∀ p : E × G,
      Complex.exp ((⟪(WithLp.toLp 2 p : WithLp 2 (E × G)), t⟫ : ℝ) * Complex.I)
        = Complex.exp ((⟪p.1, (WithLp.ofLp t).1⟫ : ℝ) * Complex.I)
          * Complex.exp ((⟪p.2, (WithLp.ofLp t).2⟫ : ℝ) * Complex.I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    have h : (⟪(WithLp.toLp 2 p : WithLp 2 (E × G)), t⟫ : ℝ)
        = ⟪p.1, (WithLp.ofLp t).1⟫ + ⟪p.2, (WithLp.ofLp t).2⟫ := by
      simp [WithLp.prod_inner_apply]
    rw [h]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  rw [integral_prod_mul (μ := stdGaussian E) (ν := stdGaussian G)
      (fun x : E => Complex.exp ((⟪x, (WithLp.ofLp t).1⟫ : ℝ) * Complex.I))
      (fun y : G => Complex.exp ((⟪y, (WithLp.ofLp t).2⟫ : ℝ) * Complex.I)),
    ← charFun_apply, ← charFun_apply, charFun_stdGaussian, charFun_stdGaussian,
    charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have hn : ‖t‖ ^ 2 = ‖(WithLp.ofLp t).1‖ ^ 2 + ‖(WithLp.ofLp t).2‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 t
  rw [show ((‖t‖ : ℝ) : ℂ) ^ 2 = ((‖t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, hn]
  push_cast
  ring

end ValueType

section Carrier

variable {n : ℕ}

end Carrier

section External

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end External

section Padded

variable {n : ℕ}

end Padded

section Composition

/-- **The one probabilistic input of `chainRaw2_of_walk`, on `chainSetup`.** -/
def TailSideHyp (n : ℕ) (c α : ℝ) (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n))
    (W : Finset (Fin n → ℤ)) (A₀ : EuclideanSpace ℝ (UT n)) : Prop :=
  ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
    (gaussPath (EuclideanSpace ℝ (UT n)))
        {ω | ∃ i ≤ k, constraintM q W A₀ (step c) y i ω ≤ 0}
      ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
          ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))

end Composition

end

end D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
