/- GID: D5/S3/Quantum/Thermal/FiniteModeGibbsProduct
   generality: G
   mirror-B: D5/B/S3/Quantum/Thermal/FiniteModeGibbsProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct arbitrary finite-mode occupation spaces, prove the actual infinite Gibbs sum factorization, and construct the resulting nuclear diagonal operator. -/

import D5.S3.Quantum.Thermal.CountableDiagonalGibbs
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Thermal.FiniteModeGibbsProduct

open D5.S3.Quantum.Thermal.CountableDiagonalGibbs
open scoped BigOperators

/-- Arbitrarily large occupation numbers in each of a finite list of modes. -/
def Occupation : List ℝ → Type
  | [] => Unit
  | _ :: ωs => ℕ × Occupation ωs

instance occupationDecidableEq (ωs : List ℝ) : DecidableEq (Occupation ωs) := by
  induction ωs with
  | nil => exact inferInstanceAs (DecidableEq Unit)
  | cons ω ωs ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (ℕ × Occupation ωs))

/-- The actual additive oscillator energy, including every zero-point contribution. -/
def totalEnergy : (ωs : List ℝ) → Occupation ωs → ℝ
  | [], _ => 0
  | ω :: ωs, x => energy ω x.1 + totalEnergy ωs x.2

def totalWeight (β : ℝ) (ωs : List ℝ) (x : Occupation ωs) : ℝ :=
  Real.exp (-β * totalEnergy ωs x)

def productPartition (β : ℝ) (ωs : List ℝ) : ℝ :=
  (ωs.map (partition β)).prod

theorem totalWeight_pos (β : ℝ) (ωs : List ℝ) (x : Occupation ωs) :
    0 < totalWeight β ωs x := Real.exp_pos _

/-- Factorization is derived from the defined additive energy, not assumed. -/
theorem totalWeight_cons (β ω : ℝ) (ωs : List ℝ) (x : Occupation (ω :: ωs)) :
    totalWeight β (ω :: ωs) x = weight β ω x.1 * totalWeight β ωs x.2 := by
  simp only [totalWeight, totalEnergy, mul_add, Real.exp_add, weight]

/-- The infinite occupation sum factorizes for every finite number of modes. -/
theorem finite_modes_hasSum (β : ℝ) (hβ : 0 < β) (ωs : List ℝ)
    (hω : ∀ ω ∈ ωs, 0 < ω) :
    HasSum (totalWeight β ωs) (productPartition β ωs) := by
  revert hω
  induction ωs with
  | nil =>
      intro hω
      simpa [Occupation, totalWeight, totalEnergy, productPartition] using
        (hasSum_fintype (fun _ : Unit => (1 : ℝ)))
  | cons ω ωs ih =>
      intro hω
      have hhead : 0 < ω := hω ω (by simp)
      have htail : ∀ v ∈ ωs, 0 < v := by
        intro v hv
        exact hω v (by simp [hv])
      have h1 := oscillator_hasSum β ω hβ hhead
      have h2 := ih htail
      have habs : Summable (fun x : ℕ × Occupation ωs =>
          weight β ω x.1 * totalWeight β ωs x.2) :=
        summable_mul_of_summable_norm h1.summable.norm h2.summable.norm
      simpa only [← totalWeight_cons, productPartition, List.map_cons, List.prod_cons] using
        h1.mul h2 habs

theorem finite_modes_absolute_sum (β : ℝ) (hβ : 0 < β) (ωs : List ℝ)
    (hω : ∀ ω ∈ ωs, 0 < ω) :
    Summable (fun x : Occupation ωs => ‖(totalWeight β ωs x : ℂ)‖) := by
  have hnorm (x : Occupation ωs) : ‖(totalWeight β ωs x : ℂ)‖ = totalWeight β ωs x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (totalWeight_pos β ωs x)]
  simpa only [hnorm] using (finite_modes_hasSum β hβ ωs hω).summable

/-- The Gibbs operator acts on the full infinite occupation Hilbert space. -/
def finiteModeGibbs (β : ℝ) (ωs : List ℝ) :
    Hilbert (Occupation ωs) →L[ℂ] Hilbert (Occupation ωs) :=
  diagonalNuclear (fun x => (totalWeight β ωs x : ℂ))

theorem finiteModeGibbs_coordinates (β : ℝ) (hβ : 0 < β) (ωs : List ℝ)
    (hω : ∀ ω ∈ ωs, 0 < ω) (ψ : Hilbert (Occupation ωs)) (x : Occupation ωs) :
    finiteModeGibbs β ωs ψ x = (Real.exp (-β * totalEnergy ωs x) : ℂ) * ψ x :=
  diagonalNuclear_apply _ (finite_modes_absolute_sum β hβ ωs hω) ψ x

/-- An explicit absolutely summable rank-one operator expansion, for all modes. -/
theorem finiteModeGibbs_nuclear (β : ℝ) (hβ : 0 < β) (ωs : List ℝ)
    (hω : ∀ ω ∈ ωs, 0 < ω) :
    HasSum (fun x : Occupation ωs => (totalWeight β ωs x : ℂ) • coordinateProjection x)
      (finiteModeGibbs β ωs) ∧
    Summable (fun x : Occupation ωs =>
      ‖(totalWeight β ωs x : ℂ) • coordinateProjection x‖) :=
  diagonal_nuclear_expansion _ (finite_modes_absolute_sum β hβ ωs hω)

theorem finiteModeGibbs_trace (β : ℝ) (hβ : 0 < β) (ωs : List ℝ)
    (hω : ∀ ω ∈ ωs, 0 < ω) :
    canonicalTrace (finiteModeGibbs β ωs) = (productPartition β ωs : ℂ) := by
  rw [finiteModeGibbs, canonicalTrace_diagonal _ (finite_modes_absolute_sum β hβ ωs hω)]
  exact ((finite_modes_hasSum β hβ ωs hω).map Complex.ofRealCLM
    Complex.ofRealCLM.continuous).tsum_eq

#print axioms finite_modes_hasSum
#print axioms finiteModeGibbs_nuclear
#print axioms finiteModeGibbs_trace
end D5.S3.Quantum.Thermal.FiniteModeGibbsProduct
