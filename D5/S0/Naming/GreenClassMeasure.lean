/- GID: D5/S0/Naming/GreenClassMeasure
   generality: G
   mirror-B: D5/B/S0/Naming/GreenClassMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Under the uniform product measure on infinite strings over a finite nonempty alphabet O with n = card O, the green class G(S,t) = {x : x|_S = t|_S} (strings agreeing with a target t on a finite support S of size m = |S|) has measure exactly n^(−m), and in particular strictly positive measure. The residual uncertainty of a finite certificate depends only on the budget m, not on the pinned content t. Proof: the green class is the cylinder Set.pi ↑S (fun i => {t i}); Measure.infinitePi_pi evaluates it as the product over i∈S of the per-coordinate uniform singleton mass (card O)⁻¹, which Finset.prod_const folds to (card O)⁻¹^m. This is the green-class positive-measure clause (定理 4.4 clause (a)); the constant-way conservation clause (b) is covered elsewhere (NamingSystem.dark_side_conservation), and the varying-marginal generalization (non-uniform coordinate marginals, the value becoming the product ∏_{i∈S} μᵢ({t i}) of the pinned singleton masses, positive exactly when each pinned singleton has positive marginal mass) and the sibling metric diameter formula are not covered. -/

import Mathlib

open MeasureTheory Measure
open scoped ENNReal

namespace D5.S0.Naming.GreenClassMeasure

noncomputable section

variable {O : Type*} [Fintype O] [Nonempty O] [MeasurableSpace O] [MeasurableSingletonClass O]

/-- The per-coordinate uniform probability measure on a finite nonempty alphabet `O`. -/
noncomputable def uniformAlphabet (O : Type*) [Fintype O] [Nonempty O] [MeasurableSpace O] :
    Measure O := (PMF.uniformOfFintype O).toMeasure

instance : IsProbabilityMeasure (uniformAlphabet O) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- The uniform product measure on the space of infinite strings `ℕ → O` over the alphabet `O`. -/
noncomputable def stringMeasure (O : Type*) [Fintype O] [Nonempty O] [MeasurableSpace O] :
    Measure (ℕ → O) := Measure.infinitePi (fun _ : ℕ => uniformAlphabet O)

/-- The **green class**: the cylinder of infinite strings agreeing with the target `t` on the finite
support `S` (a finite test suite pins these coordinates; the rest are free). -/
def greenClass (S : Finset ℕ) (t : ℕ → O) : Set (ℕ → O) :=
  Set.pi (↑S) (fun i => {t i})

/-- The per-coordinate uniform measure of a singleton is `(card O)⁻¹`. -/
theorem uniformAlphabet_singleton (a : O) :
    uniformAlphabet O {a} = ((Fintype.card O : ℝ≥0∞))⁻¹ := by
  rw [uniformAlphabet, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
    PMF.uniformOfFintype_apply]

/-- **Green class positive measure (定理 4.4, clause (a)).** Under the uniform product measure on
infinite strings over a finite nonempty alphabet `O` with `n = card O`, the green class pinning
`m = |S|` coordinates has measure exactly `n^(−m)`:
`stringMeasure O (greenClass S t) = (card O)⁻¹ ^ S.card`.

The value depends only on the budget `m = |S|`, not on the pinned content `t` — the residual
uncertainty of a finite certificate is content-independent. The green class is the cylinder
`Set.pi ↑S (fun i => {t i})`; `Measure.infinitePi_pi` evaluates it as `∏_{i ∈ S} μ({t i})` under the
infinite product measure, each per-coordinate singleton contributing `(card O)⁻¹`, folded by
`Finset.prod_const` to `(card O)⁻¹ ^ S.card`.

This records the green-class positive-measure clause. The constant-way conservation clause (b) of the
source is covered elsewhere (`NamingSystem.dark_side_conservation`); the varying-marginal
generalization (non-uniform coordinate marginals, the value becoming the product `∏_{i∈S} μᵢ({t i})`
of the pinned singleton masses — positive exactly when each pinned singleton has positive marginal
mass) and the sibling metric diameter formula `diam G = 2^(−γ(S))` are not covered. -/
theorem greenClass_measure (S : Finset ℕ) (t : ℕ → O) :
    stringMeasure O (greenClass S t) = ((Fintype.card O : ℝ≥0∞))⁻¹ ^ S.card := by
  rw [stringMeasure, greenClass,
    Measure.infinitePi_pi (fun _ : ℕ => uniformAlphabet O)
      (fun i _ => measurableSet_singleton (t i))]
  rw [Finset.prod_congr rfl (fun i _ => uniformAlphabet_singleton (t i)),
    Finset.prod_const]

/-- The green class has strictly positive measure (the "正测" of clause (a)). -/
theorem greenClass_measure_pos (S : Finset ℕ) (t : ℕ → O) :
    0 < stringMeasure O (greenClass S t) := by
  rw [greenClass_measure]
  exact ENNReal.pow_pos (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)) _

end

end D5.S0.Naming.GreenClassMeasure
