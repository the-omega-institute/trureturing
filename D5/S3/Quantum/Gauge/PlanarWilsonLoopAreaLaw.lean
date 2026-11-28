/- GID: D5/S3/Quantum/Gauge/PlanarWilsonLoopAreaLaw
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/PlanarWilsonLoopAreaLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact planar Z₂ Wilson-loop area law on open cubical boxes. -/

import OmegaBuild.Commands
import D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion
import OmegaMath.Topology.CubicalBox
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Exact planar Wilson-loop area law

The mod-two plaquette expansion and injectivity of the open planar boundary give
the exact normalized Wilson-loop expectation for every real coupling.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
noncomputable section

namespace D5.S3.Quantum.Gauge.PlanarWilsonLoopAreaLaw

section WilsonLoops

open Matrix
open D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion

/-- The Boltzmann factor of a single sign. -/
private theorem ising_boltzmann_expansion (β s : ℝ) (hs : s = 1 ∨ s = -1) :
    Real.exp (β * s) = Real.cosh β * (1 + Real.tanh β * s) := by
  have h : Real.cosh β * Real.tanh β = Real.sinh β := by
    rw [Real.tanh_eq_sinh_div_cosh, mul_comm, div_mul_cancel₀ _ (Real.cosh_pos β).ne']
  rw [mul_add, mul_one, ← mul_assoc, h]
  rcases hs with rfl | rfl <;> simp [← sub_eq_add_neg]

variable {P E : Type*} [Fintype P] [Fintype E] [DecidableEq P] [DecidableEq E]

/-- The plaquettes where the bit surface is nonzero. -/
def plaquetteSupport (S : P → ZMod 2) : Finset P :=
  Finset.univ.filter (fun p => S p ≠ 0)

/-- Bit surfaces with the prescribed boundary. -/
def fillings (M : Matrix P E (ZMod 2)) (c : E → ZMod 2) : Finset (P → ZMod 2) :=
  Finset.univ.filter (fun S => Mᵀ *ᵥ S = c)

def surfaceSum (M : Matrix P E (ZMod 2)) (t : ℝ) (c : E → ZMod 2) : ℝ :=
  ∑ S ∈ fillings M c, t ^ (plaquetteSupport S).card

/-- The normalized finite Wilson expectation with parity insertion `c`. -/
def wilsonExpectation (M : Matrix P E (ZMod 2)) (β : ℝ) (c : E → ZMod 2) : ℝ :=
  (∑ σ : E → ZMod 2, sgn ℝ (c ⬝ᵥ σ) * Real.exp (β * ∑ p, sgn ℝ ((M *ᵥ σ) p))) /
    (∑ σ : E → ZMod 2, Real.exp (β * ∑ p, sgn ℝ ((M *ᵥ σ) p)))

private theorem wilsonSpinSum_eq (M : Matrix P E (ZMod 2)) (β : ℝ) (c : E → ZMod 2) :
    (∑ σ : E → ZMod 2, sgn ℝ (c ⬝ᵥ σ) * Real.exp (β * ∑ p, sgn ℝ ((M *ᵥ σ) p))) =
      (Real.cosh β ^ Fintype.card P * 2 ^ Fintype.card E) * surfaceSum M (Real.tanh β) c := by
  have h (σ : E → ZMod 2) :
      Real.exp (β * ∑ p, sgn ℝ ((M *ᵥ σ) p)) =
        Real.cosh β ^ Fintype.card P * ∏ p, (1 + Real.tanh β * sgn ℝ ((M *ᵥ σ) p)) := by
    rw [Finset.mul_sum, Real.exp_sum, ← Finset.card_univ (α := P), ← Finset.prod_const,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ising_boltzmann_expansion _ _ ?_
    by_cases hp : (M *ᵥ σ) p = 0 <;> simp [sgn, hp]
  simp_rw [h, mul_left_comm (sgn ℝ _) (Real.cosh β ^ Fintype.card P), ← Finset.mul_sum]
  rw [sum_sgn_mul_prod_one_add_eq M (fun _ => Real.tanh β) c, mul_assoc]
  simp only [surfaceSum, fillings, plaquetteSupport, Finset.prod_const]

private theorem wilsonExpectation_eq_surfaceRatio (M : Matrix P E (ZMod 2)) (β : ℝ)
    (c : E → ZMod 2) :
    wilsonExpectation M β c = surfaceSum M (Real.tanh β) c / surfaceSum M (Real.tanh β) 0 := by
  have hzero := wilsonSpinSum_eq M β 0
  have hsign : sgn ℝ 0 = 1 := by simp [sgn]
  simp only [zero_dotProduct, hsign, one_mul] at hzero
  rw [wilsonExpectation, wilsonSpinSum_eq, hzero, mul_div_mul_left]
  exact mul_ne_zero (pow_ne_zero _ (Real.cosh_pos β).ne') (pow_ne_zero _ two_ne_zero)

omit [DecidableEq P] in
/-- With injective boundary there is a unique filling and the only closed surface is zero. -/
private theorem wilsonExpectation_eq_pow_of_injective (M : Matrix P E (ZMod 2))
    (hM : Function.Injective (Mᵀ *ᵥ ·)) (β : ℝ) (S : P → ZMod 2) :
    wilsonExpectation M β (Mᵀ *ᵥ S) = (Real.tanh β) ^ (plaquetteSupport S).card := by
  classical
  have hf : ∀ U, fillings M (Mᵀ *ᵥ U) = {U} := by
    intro U
    ext V
    simp [fillings, hM.eq_iff]
  have hz : fillings M 0 = {0} := by simpa using hf 0
  simp [wilsonExpectation_eq_surfaceRatio, surfaceSum, hf, hz, plaquetteSupport]

open Omega.CubicalBox in
/-- On an open planar box the four sides of a rectangle have a unique filling. -/
theorem wilson_loop_2d_exact_area_law {w : Fin 2 → ℕ} (r : Rectangle w) (β : ℝ) :
    wilsonExpectation (incidence w) β r.perimeter = Real.tanh β ^ (r.width * r.height) ∧
      (0 < β → 0 < -Real.log (Real.tanh β) ∧
        wilsonExpectation (incidence w) β r.perimeter =
          Real.exp (-(-Real.log (Real.tanh β)) * ((r.width * r.height : ℕ) : ℝ))) := by
  rw [← r.loop_eq_perimeter]
  have hpow : wilsonExpectation (incidence w) β r.loop = Real.tanh β ^ (r.width * r.height) := by
    simpa only [Rectangle.loop, plaquetteSupport, r.filling_support_card] using
      wilsonExpectation_eq_pow_of_injective (incidence w) (boundary_injective_2d w) β r.filling
  refine ⟨hpow, fun hβ => ?_⟩
  have ht : 0 < Real.tanh β := by
    rw [Real.tanh_eq]
    exact div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr ((neg_neg_of_pos hβ).trans hβ)))
      (add_pos (Real.exp_pos _) (Real.exp_pos _))
  refine ⟨neg_pos.mpr (Real.log_neg ht (Real.tanh_lt_one _)), ?_⟩
  rw [hpow, neg_neg, mul_comm (Real.log (Real.tanh β)), Real.exp_nat_mul, Real.exp_log ht]

end WilsonLoops

end D5.S3.Quantum.Gauge.PlanarWilsonLoopAreaLaw
