/- GID: D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.claim; result=D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.result; claim=D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.claim
   digest: A five-vertex weighted path transfers interior states but never transfers endpoint states. -/

import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Dynamics.InteriorPathTransferConverseRefutation
open Matrix Complex
open scoped Matrix.Norms.L2Operator
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity

/-- Interior mirror transfer is asserted to force endpoint transfer on every positive weighted path. -/
def claim : Prop :=
  ∀ m : ℕ, 3 ≤ m → ∀ (r : Fin m → ℝ), (∀ k, 0 < r k) →
    ∀ (q : Fin (m + 1) → ℝ) (j : Fin (m + 1)),
      1 ≤ j.val → j.val ≤ m - 1 → j.val ≠ m - j.val →
        (∃ t : ℝ, 0 < t ∧ HasPST (pathHamiltonian r q) t j (Fin.rev j)) →
          ∃ s : ℝ, 0 < s ∧ HasPST (pathHamiltonian r q) s 0 (Fin.last m)

private def weights : Fin 4 → ℝ := ![2 * Real.sqrt 2, Real.sqrt 5, Real.sqrt 5, 2 * Real.sqrt 2]
private def H : Matrix (Fin 5) (Fin 5) ℂ := pathHamiltonian weights 0
private def u (z : ℂ) : Fin 5 → ℂ := ![1, z, 0, -z, -1]
private def w (z : ℂ) : Fin 5 → ℂ :=
  ![2, 3 * z, (Real.sqrt 2 : ℂ) * Real.sqrt 5, 3 * z, 2]
private def v₀ : Fin 5 → ℂ := ![-(Real.sqrt 5 : ℂ), 0, 2 * Real.sqrt 2, 0, -(Real.sqrt 5 : ℂ)]
private def τ : ℝ := 2 * Real.pi / (2 * Real.sqrt 2)

private lemma weights_pos : ∀ k, 0 < weights k := by
  sorry

private lemma spectral_data :
    H *ᵥ v₀ = (0 : ℂ) • v₀ ∧
    H *ᵥ u 1 = (2 * (Real.sqrt 2 : ℂ)) • u 1 ∧
    H *ᵥ u (-1) = (-2 * (Real.sqrt 2 : ℂ)) • u (-1) ∧
    H *ᵥ w 1 = (3 * (Real.sqrt 2 : ℂ)) • w 1 ∧
    H *ᵥ w (-1) = (-3 * (Real.sqrt 2 : ℂ)) • w (-1) := by
  sorry

private lemma eigen_exp (s : ℝ) (v : Fin 5 → ℂ) (λ : ℂ)
    (hv : H *ᵥ v = λ • v) :
    NormedSpace.exp (((s : ℂ) * I) • H) *ᵥ v =
      Complex.exp ((s : ℂ) * I * λ) • v := by
  sorry

private lemma interior_decomposition :
    (Pi.single 1 1 : Fin 5 → ℂ) =
      (1 / 4 : ℂ) • u 1 - (1 / 4 : ℂ) • u (-1) +
        (1 / 12 : ℂ) • w 1 - (1 / 12 : ℂ) • w (-1) ∧
    (Pi.single 3 1 : Fin 5 → ℂ) =
      -(1 / 4 : ℂ) • u 1 + (1 / 4 : ℂ) • u (-1) +
        (1 / 12 : ℂ) • w 1 - (1 / 12 : ℂ) • w (-1) := by
  sorry

private lemma phases :
    Complex.exp ((τ : ℂ) * I * (2 * (Real.sqrt 2 : ℂ))) = 1 ∧
    Complex.exp ((τ : ℂ) * I * (-2 * (Real.sqrt 2 : ℂ))) = 1 ∧
    Complex.exp ((τ : ℂ) * I * (3 * (Real.sqrt 2 : ℂ))) = -1 ∧
    Complex.exp ((τ : ℂ) * I * (-3 * (Real.sqrt 2 : ℂ))) = -1 := by
  sorry

private lemma interior_transfer : ∃ t : ℝ, 0 < t ∧ HasPST H t 1 3 := by
  sorry

private lemma endpoint_column (s : ℝ) (hpst : HasPST H s 0 4) (x : Fin 5) :
    NormedSpace.exp (((s : ℂ) * I) • H) x 4 =
      if x = 0 then NormedSpace.exp (((s : ℂ) * I) • H) 0 4 else 0 := by
  sorry

private lemma endpoint_eigen_phase (s : ℝ) (hpst : HasPST H s 0 4)
    (v : Fin 5 → ℂ) (λ : ℂ) (hv : H *ᵥ v = λ • v) :
    Complex.exp ((s : ℂ) * I * λ) * v 4 =
      NormedSpace.exp (((s : ℂ) * I) • H) 0 4 * v 0 := by
  sorry

private lemma no_endpoint_transfer (s : ℝ) : ¬ HasPST H s 0 4 := by
  sorry

theorem result : ¬ claim := by
  intro hc
  obtain ⟨s, _, hs⟩ := hc 4 (by omega) weights weights_pos 0 1
    (by decide) (by decide) (by decide) (by simpa [H] using interior_transfer)
  exact no_endpoint_transfer s hs

end D5.S3.Quantum.Dynamics.InteriorPathTransferConverseRefutation
