/- GID: D5/S3/Observer/NymanBeurlingShellMassDecomposition
   generality: G
   mirror-B: D5/B/S3/Observer/NymanBeurlingShellMassDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hilbert shell tails satisfy the mass recurrence and detect the Nyman-Beurling defect. -/

import D5.S3.Observer.Hilbert.NymanBeurlingTargetQuotientCriterion
import D5.S3.Observer.Tomography.VectorShellEnergy

/- Library-search audit trail (2026-09-02):
   * Six-way repository, receipt, digest, generalized-owner, and in-flight searches found no
     equal-or-stronger shell-tail recurrence joined to the Nyman-Beurling residual criterion.
     `VectorShellEnergy.vector_shell_energy_decomposition` and
     `NymanBeurlingTargetQuotientCriterion.nyman_beurling_target_quotient_criterion` are the
     canonical owners and are reused directly.
   * Pinned Mathlib supplies `Summable.sum_add_tsum_nat_add`, `Real.sq_sqrt`,
     `sq_eq_zero_iff`, and `norm_eq_zero`; no exact packaged theorem joins these facts.
   * The source omitted definitions and compatibility assumptions for `d_N`, `Q_k`, `Q_infty`,
     and `RH`. Here extracted Hilbert-sum coordinate `n` represents `Q_(n+1)`, the terminal
     coordinate is explicitly identified with the Nyman-Beurling orthogonal defect, and the
     missing unit-vector and zero-initial-mass assumptions are stated. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.NymanBeurlingShellMassDecomposition

noncomputable section

open scoped lp
open D5.S3.Observer.Hilbert.NymanBeurlingTargetQuotientCriterion
open D5.S3.Observer.Tomography.VectorShellEnergy
open D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {G : Fin 2 ⊕ ℕ → Type v}
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℝ (G i)]

/-- Squared mass of source shell `Q_(n+1)`. -/
noncomputable def shellMass
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (chi : H) (n : ℕ) : ℝ :=
  ‖extractedComponent V hV n chi‖ ^ 2

/-- Squared mass of the component surviving every finite shell. -/
noncomputable def terminalMass
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (chi : H) : ℝ :=
  ‖residualComponent V hV chi‖ ^ 2

/-- Mass after stage `N`: all shells with source index greater than `N`, plus the terminal mass. -/
noncomputable def remainingMass
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (chi : H) (N : ℕ) : ℝ :=
  ∑' j : ℕ, shellMass V hV chi (j + N) + terminalMass V hV chi

/-- The canonical nonnegative distance associated with the remaining squared mass. -/
noncomputable def shellDistance
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (chi : H) (N : ℕ) : ℝ :=
  Real.sqrt (remainingMass V hV chi N)

private theorem shellMass_summable
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (chi : H) :
    Summable (shellMass V hV chi) := by
  let w : lp G 2 := hV.linearIsometryEquiv chi
  let energy : Fin 2 ⊕ ℕ → ℝ := fun i ↦ ‖w i‖ ^ 2
  have htwo : 0 < (2 : ENNReal).toReal := by norm_num
  have hsummable : Summable energy := by
    simpa [energy] using (lp.memℓp w).summable htwo
  have hshell : Summable (energy ∘ Sum.inr) :=
    hsummable.comp_injective Sum.inr_injective
  change Summable (fun n : ℕ ↦ ‖extractedComponent V hV n chi‖ ^ 2)
  simpa [Function.comp_def, energy, extractedComponent, hilbertSumComponent, w] using hshell

private theorem remainingMass_nonneg
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (chi : H) (N : ℕ) :
    0 ≤ remainingMass V hV chi N := by
  exact add_nonneg (tsum_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg _)

private theorem shellDistance_sq
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (chi : H) (N : ℕ) :
    shellDistance V hV chi N ^ 2 = remainingMass V hV chi N := by
  exact Real.sq_sqrt (remainingMass_nonneg V hV chi N)

private theorem remainingMass_step
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (chi : H) (N : ℕ) :
    remainingMass V hV chi N =
      remainingMass V hV chi (N + 1) + shellMass V hV chi N := by
  let f : ℕ → ℝ := shellMass V hV chi
  have hf : Summable f := shellMass_summable V hV chi
  have hN := hf.sum_add_tsum_nat_add N
  have hN1 := hf.sum_add_tsum_nat_add (N + 1)
  rw [Finset.sum_range_succ] at hN1
  have htail : (∑' j : ℕ, f (j + N)) = f N + (∑' j : ℕ, f (j + (N + 1))) := by
    linarith
  change (∑' j : ℕ, f (j + N)) + terminalMass V hV chi =
    ((∑' j : ℕ, f (j + (N + 1))) + terminalMass V hV chi) + f N
  rw [htail]
  ring

/-- Shell-tail recurrence, total mass, and the exact RH/terminal-mass criterion.

Coordinate `n` is source shell `Q_(n+1)`. Thus `shellDistance N` contains precisely the
source shells with index greater than `N`, together with the terminal component. -/
theorem nyman_beurling_shell_mass_decomposition
    (V : ∀ i, G i →ₗᵢ[ℝ] H) (hV : IsHilbertSum ℝ G V) (chi : H)
    (S : ℕ → Submodule ℝ H) (hS : Monotone S) (RH : Prop)
    (unitChi : ‖chi‖ = 1)
    (initialZero : initialComponent V hV chi = 0)
    (terminalCompatibility :
      residualComponent V hV chi = ((cumulativeSpace S)ᗮ).starProjection chi)
    (nymanBeurling : RH ↔ chi ∈ cumulativeSpace S) :
    (∀ N : ℕ,
      shellDistance V hV chi N ^ 2 =
        shellDistance V hV chi (N + 1) ^ 2 + shellMass V hV chi N) ∧
      (∀ N : ℕ,
        shellDistance V hV chi N ^ 2 =
          (∑' j : ℕ, shellMass V hV chi (j + N)) + terminalMass V hV chi) ∧
      (∑' n : ℕ, shellMass V hV chi n) + terminalMass V hV chi = 1 ∧
      (RH ↔ terminalMass V hV chi = 0) ∧
      (RH ↔ ∑' n : ℕ, shellMass V hV chi n = 1) := by
  have hsquares := vector_shell_energy_decomposition V hV chi
  have htotal :
      (∑' n : ℕ, shellMass V hV chi n) + terminalMass V hV chi = 1 := by
    have hunitMass := hsquares.2 unitChi
    rw [initialZero, norm_zero, zero_pow (by norm_num), zero_add] at hunitMass
    simpa only [shellMass, terminalMass] using hunitMass.2.2.2
  have hcriteria := nyman_beurling_target_quotient_criterion RH S hS chi nymanBeurling
  have hRHProjection : RH ↔ ((cumulativeSpace S)ᗮ).starProjection chi = 0 :=
    hcriteria.out 0 3
  have hRHTerminal : RH ↔ terminalMass V hV chi = 0 := by
    rw [hRHProjection]
    simp only [terminalMass, terminalCompatibility, sq_eq_zero_iff, norm_eq_zero]
  have hRHShells : RH ↔ ∑' n : ℕ, shellMass V hV chi n = 1 := by
    rw [hRHTerminal]
    constructor
    · intro hterminal
      linarith
    · intro hshells
      linarith
  refine ⟨?_, ?_, htotal, hRHTerminal, hRHShells⟩
  · intro N
    rw [shellDistance_sq, shellDistance_sq]
    exact remainingMass_step V hV chi N
  · intro N
    rw [shellDistance_sq]
    rfl

#print axioms nyman_beurling_shell_mass_decomposition

end

end D5.S3.Observer.NymanBeurlingShellMassDecomposition
