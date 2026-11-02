/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Math.MeasureTheory.IntegralReal
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Measure-theoretic probability distributions

`ProbDist α` is an abbreviation for Mathlib's `ProbabilityMeasure α`. It is the unifying type that
sees finite, countable, continuous, and singular laws through one measure-theoretic interface, and
carries the weak-* topology that concrete types (`FinDist`, `ContDist`) lack.

Consumers that need only `∑` or `∫` over a fixed type should use `FinDist`, `ContDist`, or
`CountDist` directly; `ProbDist` is for type-polymorphic code, topology on distributions, and
cross-type composition. This file provides the core operations: Expectation, the Dirac point mass,
pushforward along a measurable map, and the independent product.

## Main definitions

* `ProbDist α` — abbreviation for `ProbabilityMeasure α`.
* `ProbDist.expect` — expected value `∫ x, f x ∂d.toMeasure`.
* `ProbDist.dirac` — point mass at a point.
* `ProbDist.map` — pushforward along a measurable map.
* `ProbDist.prod` — independent product coupling.

## Main statements

* `ProbDist.expect_lt`, `ProbDist.lt_expect` — strict expectation bounds.
* `ProbDist.expect_map` — change of variables for pushforward expectation.

## Tags

probability measure, expectation, dirac, pushforward, product
-/

@[expose] public section

open MeasureTheory

namespace Econlib.Probability

/-- A probability distribution on a measurable space `α`. Abbreviation for Mathlib's
`ProbabilityMeasure α`. -/
abbrev ProbDist (α : Type*) [MeasurableSpace α] := ProbabilityMeasure α

namespace ProbDist

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### Expectation -/

/-- Expected value of `f` under `d`.

This is Mathlib's (Bochner) integral `∫ x, f x ∂d.toMeasure`, hence **totalized**: It equals the
mathematical expectation `E_d[f]` exactly when `f` is `Integrable d.toMeasure`, and silently
returns `0` when it is not (the convention of `MeasureTheory.integral`). Linearity and order laws
that fail without integrability carry the corresponding `Integrable` hypotheses, which is where the
contract is discharged. -/
noncomputable def expect (d : ProbDist α) (f : α → ℝ) : ℝ :=
  ∫ x, f x ∂d.toMeasure

/-- A pointwise-nonnegative function has nonnegative expectation. -/
lemma expect_nonneg (d : ProbDist α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ d.expect f :=
  integral_nonneg hf

/-- Strict upper bound on expectation: If `f ≤ c` a.e. and `f < c` on a set of positive measure,
then `𝔼[f] < c`. -/
lemma expect_lt (d : ProbDist α) (f : α → ℝ) (c : ℝ)
    (hle : ∀ᵐ x ∂d.toMeasure, f x ≤ c)
    (hf : Integrable f d.toMeasure)
    {s : Set α} (hμs : 0 < d.toMeasure s)
    (hlt : ∀ x ∈ s, f x < c) :
    d.expect f < c := by
  -- `g := c - f` is ae-nonneg and strictly positive on `s`, so `0 < ∫ g = c - 𝔼[f]`.
  have hpos : 0 < ∫ x, (c - f x) ∂d.toMeasure :=
    integral_pos_of_pos_on
      (by filter_upwards [hle] with x hx; simp only [Pi.zero_apply]; linarith)
      ((integrable_const c).sub hf) hμs (fun x hx => by linarith [hlt x hx])
  have hexp : d.expect f = c - ∫ x, (c - f x) ∂d.toMeasure := by
    rw [expect, integral_sub (integrable_const c) hf, integral_const, probReal_univ, one_smul]
    ring
  linarith

/-- Strict lower bound on expectation: If `c ≤ f` a.e. and `c < f` on a set of positive measure,
then `c < 𝔼[f]`. -/
lemma lt_expect (d : ProbDist α) (f : α → ℝ) (c : ℝ)
    (hle : ∀ᵐ x ∂d.toMeasure, c ≤ f x)
    (hf : Integrable f d.toMeasure)
    {s : Set α} (hμs : 0 < d.toMeasure s)
    (hlt : ∀ x ∈ s, c < f x) :
    c < d.expect f := by
  -- `g := f - c` is ae-nonneg and strictly positive on `s`, so `0 < ∫ g = 𝔼[f] - c`.
  have hpos : 0 < ∫ x, (f x - c) ∂d.toMeasure :=
    integral_pos_of_pos_on
      (by filter_upwards [hle] with x hx; simp only [Pi.zero_apply]; linarith)
      (hf.sub (integrable_const c)) hμs (fun x hx => by linarith [hlt x hx])
  have hexp : d.expect f = c + ∫ x, (f x - c) ∂d.toMeasure := by
    rw [expect, integral_sub hf (integrable_const c), integral_const, probReal_univ, one_smul]
    ring
  linarith

/-! ### Dirac point mass -/

/-- Point mass at `a`. -/
noncomputable def dirac [MeasurableSingletonClass α] (a : α) : ProbDist α :=
  ⟨Measure.dirac a, Measure.dirac.isProbabilityMeasure⟩

/-- The measure underlying `dirac a` is Mathlib's `Measure.dirac a`. -/
@[simp] lemma dirac_toMeasure [MeasurableSingletonClass α] (a : α) :
    (dirac a : ProbDist α).toMeasure = Measure.dirac a := rfl

/-- Expectation under a point mass evaluates the integrand at the point. -/
@[simp] lemma expect_dirac [MeasurableSingletonClass α] (a : α) (f : α → ℝ) :
    (dirac a).expect f = f a := by
  simp [expect, dirac, integral_dirac]

/-! ### Pushforward -/

/-- Push a probability distribution forward along a measurable map. -/
noncomputable def map (d : ProbDist α) (f : α → β) (hf : Measurable f) : ProbDist β :=
  ProbabilityMeasure.map d f

/-- The measure underlying `map d f hf` is the Mathlib pushforward `Measure.map f d.toMeasure`. -/
@[simp] lemma map_toMeasure (d : ProbDist α) (f : α → β) (hf : Measurable f) :
    ((map d f hf : ProbDist β) : Measure β) = Measure.map f d.toMeasure := rfl

/-- **Change of variables:** Expectation of `g` under the pushforward equals expectation of `g ∘ f`
under `d`. -/
lemma expect_map (d : ProbDist α) (f : α → β) (hf : Measurable f) (g : β → ℝ)
    (hg : AEStronglyMeasurable g ((map d f hf : ProbDist β).toMeasure)) :
    (map d f hf).expect g = d.expect (fun x => g (f x)) := by
  simp [expect, map, MeasureTheory.integral_map hf.aemeasurable hg]

/-! ### Independent product -/

/-- The **product (independent) coupling** `μ ⊗ ν`, viewed as a `ProbDist (α × β)`. -/
noncomputable def prod (μ : ProbDist α) (ν : ProbDist β) : ProbDist (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, Measure.prod.instIsProbabilityMeasure _ _⟩

/-- The measure underlying `prod μ ν` is the product measure `μ.toMeasure.prod ν.toMeasure`. -/
@[simp] lemma prod_toMeasure (μ : ProbDist α) (ν : ProbDist β) :
    (prod μ ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl

end ProbDist

end Econlib.Probability
