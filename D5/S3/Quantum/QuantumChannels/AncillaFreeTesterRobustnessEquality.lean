/- GID: D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Ancilla-free testers with a common state have canonical POVM robustness. -/

import D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality

open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation (IsPOVM)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (partialTraceRight_smul)

/-- Positive tester effects sum to the output identity tensored with a density matrix. -/
def IsTester {y x j : Type} [Fintype y] [DecidableEq y] [Fintype x] [Fintype j]
    (t : j → Matrix (y × x) (y × x) ℂ) : Prop :=
  (∀ a, (t a).PosSemidef) ∧
    ∃ σ : Matrix x x ℂ, IsDensity σ ∧ ∑ a, t a = Matrix.kronecker 1 σ

/-- Separate noise testers make the two mixtures marginals of one joint tester. -/
def TesterCompatibleAt {y x j k : Type} [Fintype y] [DecidableEq y]
    [Fintype x] [Fintype j] [Fintype k] (lam : ℝ)
    (a : j → Matrix (y × x) (y × x) ℂ) (b : k → Matrix (y × x) (y × x) ℂ) : Prop :=
  ∃ (e : j → Matrix (y × x) (y × x) ℂ) (f : k → Matrix (y × x) (y × x) ℂ)
    (c : j × k → Matrix (y × x) (y × x) ℂ),
    IsTester e ∧ IsTester f ∧ IsTester c ∧
      (∀ u, ∑ v, c (u, v) = (1 - lam) • a u + lam • e u) ∧
      (∀ v, ∑ u, c (u, v) = (1 - lam) • b v + lam • f v)

/-- Infimum of the admissible mixing parameters in the unit interval. -/
def testerRobustness {y x j k : Type} [Fintype y] [DecidableEq y]
    [Fintype x] [Fintype j] [Fintype k]
    (a : j → Matrix (y × x) (y × x) ℂ) (b : k → Matrix (y × x) (y × x) ℂ) : ℝ :=
  sInf {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ TesterCompatibleAt lam a b}

/-- Separate noise POVMs make the two mixtures marginals of one joint POVM. -/
def POVMCompatibleAt {z j k : Type} [Fintype z] [DecidableEq z]
    [Fintype j] [Fintype k] (lam : ℝ)
    (p : j → Matrix z z ℂ) (q : k → Matrix z z ℂ) : Prop :=
  ∃ (u : j → Matrix z z ℂ) (v : k → Matrix z z ℂ)
    (g : j × k → Matrix z z ℂ),
    IsPOVM u ∧ IsPOVM v ∧ IsPOVM g ∧
      (∀ a, ∑ b, g (a, b) = (1 - lam) • p a + lam • u a) ∧
      (∀ b, ∑ a, g (a, b) = (1 - lam) • q b + lam • v b)

/-- Infimum of the POVM mixing parameters in the unit interval. -/
def povmRobustness {z j k : Type} [Fintype z] [DecidableEq z]
    [Fintype j] [Fintype k]
    (p : j → Matrix z z ℂ) (q : k → Matrix z z ℂ) : ℝ :=
  sInf {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ POVMCompatibleAt lam p q}

/-- The canonical POVMs act on the output and the support of the common input state. -/
def claim : Prop :=
  ∀ (y x j k : Type) [Fintype y] [DecidableEq y] [Fintype x] [DecidableEq x]
    [Fintype j] [DecidableEq j] [Fintype k] [DecidableEq k]
    (ρ : Matrix x x ℂ) (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ),
    IsDensity ρ → IsPOVM m → IsPOVM n →
      testerRobustness (fun a => Matrix.kronecker (m a) ρ)
        (fun b => Matrix.kronecker (n b) ρ) =
      povmRobustness (fun a => Matrix.kronecker (m a)
        (1 : Matrix (Fin ρ.rank) (Fin ρ.rank) ℂ))
        (fun b => Matrix.kronecker (n b) (1 : Matrix (Fin ρ.rank) (Fin ρ.rank) ℂ))

private theorem povm_tensor_tester {y x j : Type} [Fintype y] [DecidableEq y]
    [Fintype x] [Fintype j] (ρ : Matrix x x ℂ) (hρ : IsDensity ρ)
    (m : j → Matrix y y ℂ) (hm : IsPOVM m) :
    IsTester (fun a => Matrix.kronecker (m a) ρ) := by
  sorry

private theorem partialTraceRight_sum {y x j : Type} [Fintype x] [Fintype j]
    (t : j → Matrix (y × x) (y × x) ℂ) :
    partialTraceRight (∑ a, t a) = ∑ a, partialTraceRight (t a) := by
  sorry

private theorem tester_partialTrace_povm {y x j : Type} [Fintype y] [DecidableEq y]
    [Fintype x] [Fintype j] (t : j → Matrix (y × x) (y × x) ℂ)
    (ht : IsTester t) : IsPOVM (fun a => partialTraceRight (t a)) := by
  sorry

private theorem povm_to_tester_compatible {y x j k : Type}
    [Fintype y] [DecidableEq y] [Fintype x] [Fintype j] [Fintype k]
    (ρ : Matrix x x ℂ) (hρ : IsDensity ρ) (lam : ℝ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ)
    (h : POVMCompatibleAt lam m n) :
    TesterCompatibleAt lam (fun a => Matrix.kronecker (m a) ρ)
      (fun b => Matrix.kronecker (n b) ρ) := by
  sorry

private theorem tester_to_povm_compatible {y x j k : Type}
    [Fintype y] [DecidableEq y] [Fintype x] [Fintype j] [Fintype k]
    (ρ : Matrix x x ℂ) (hρ : IsDensity ρ) (lam : ℝ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ)
    (h : TesterCompatibleAt lam (fun a => Matrix.kronecker (m a) ρ)
      (fun b => Matrix.kronecker (n b) ρ)) : POVMCompatibleAt lam m n := by
  sorry

private theorem povm_tensor_identity {y j : Type} [Fintype y] [DecidableEq y]
    [Fintype j] (r : ℕ) (m : j → Matrix y y ℂ) (hm : IsPOVM m) :
    IsPOVM (fun a => Matrix.kronecker (m a) (1 : Matrix (Fin r) (Fin r) ℂ)) := by
  sorry

private theorem povm_to_ancilla_compatible {y j k : Type} [Fintype y] [DecidableEq y]
    [Fintype j] [Fintype k] (r : ℕ) (lam : ℝ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ)
    (h : POVMCompatibleAt lam m n) :
    POVMCompatibleAt lam (fun a => Matrix.kronecker (m a)
      (1 : Matrix (Fin r) (Fin r) ℂ))
      (fun b => Matrix.kronecker (n b) (1 : Matrix (Fin r) (Fin r) ℂ)) := by
  sorry

private theorem compression_povm {y j : Type} [Fintype y] [DecidableEq y]
    [Fintype j] (r : ℕ) (hr : 0 < r)
    (m : j → Matrix (y × Fin r) (y × Fin r) ℂ) (hm : IsPOVM m) :
    IsPOVM (fun a => (m a).submatrix (fun b => (b, ⟨0, hr⟩))
      (fun b => (b, ⟨0, hr⟩))) := by
  sorry

private theorem ancilla_to_povm_compatible {y j k : Type} [Fintype y] [DecidableEq y]
    [Fintype j] [Fintype k] (r : ℕ) (hr : 0 < r) (lam : ℝ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ)
    (h : POVMCompatibleAt lam (fun a => Matrix.kronecker (m a)
      (1 : Matrix (Fin r) (Fin r) ℂ))
      (fun b => Matrix.kronecker (n b) (1 : Matrix (Fin r) (Fin r) ℂ))) :
    POVMCompatibleAt lam m n := by
  sorry

private theorem density_rank_pos {x : Type} [Fintype x] [DecidableEq x]
    (ρ : Matrix x x ℂ) (hρ : IsDensity ρ) : 0 < ρ.rank := by
  sorry

private theorem tester_feasible_eq {y x j k : Type}
    [Fintype y] [DecidableEq y] [Fintype x] [Fintype j] [Fintype k]
    (ρ : Matrix x x ℂ) (hρ : IsDensity ρ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ) :
    {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ TesterCompatibleAt lam
      (fun a => Matrix.kronecker (m a) ρ) (fun b => Matrix.kronecker (n b) ρ)} =
    {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ POVMCompatibleAt lam m n} := by
  ext lam
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨tester_to_povm_compatible ρ hρ lam m n, povm_to_tester_compatible ρ hρ lam m n⟩

private theorem ancilla_feasible_eq {y j k : Type} [Fintype y] [DecidableEq y]
    [Fintype j] [Fintype k] (r : ℕ) (hr : 0 < r)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ) :
    {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ POVMCompatibleAt lam m n} =
    {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ POVMCompatibleAt lam
      (fun a => Matrix.kronecker (m a) (1 : Matrix (Fin r) (Fin r) ℂ))
      (fun b => Matrix.kronecker (n b) (1 : Matrix (Fin r) (Fin r) ℂ))} := by
  ext lam
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨povm_to_ancilla_compatible r lam m n, ancilla_to_povm_compatible r hr lam m n⟩

/-- Tester and canonical measurement robustness agree for a common ancilla-free state. -/
theorem result : claim := by
  intro y x j k _ _ _ _ _ _ _ _ ρ m n hρ _hm _hn
  change sInf _ = sInf _
  exact congrArg sInf ((tester_feasible_eq ρ hρ m n).trans
    (ancilla_feasible_eq ρ.rank (density_rank_pos ρ hρ) m n))

end D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
