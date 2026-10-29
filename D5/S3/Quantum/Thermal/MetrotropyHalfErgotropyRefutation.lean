/- GID: D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.claim; result=D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.result; claim=D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.claim
   digest: A non-stationary pure state has metrotropy greater than half its ergotropy. -/

import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation

open scoped BigOperators ComplexOrder Matrix

/-- The non-selective rank-one projective measurement in the columns of a unitary. -/
def measured {d : ℕ} (u : Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ k : Fin d,
    (Matrix.vecMulVec (fun i => (u : Matrix (Fin d) (Fin d) ℂ) i k)
      (star (fun j => (u : Matrix (Fin d) (Fin d) ℂ) j k))) * ρ *
      star (Matrix.vecMulVec (fun i => (u : Matrix (Fin d) (Fin d) ℂ) i k)
        (star (fun j => (u : Matrix (Fin d) (Fin d) ℂ) j k)))

/-- The energy expectation of a matrix in a Hamiltonian. -/
def energy {d : ℕ} (h σ : Matrix (Fin d) (Fin d) ℂ) : ℝ := (h * σ).trace.re

/-- Energy extracted by an optimal rank-one projective measurement. -/
def metrotropy {d : ℕ} (h ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  energy h ρ - sInf {e : ℝ | ∃ u : Matrix.unitaryGroup (Fin d) ℂ,
    e = energy h (measured u ρ)}

/-- Energy extracted by an optimal unitary operation. -/
def ergotropy {d : ℕ} (h ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  energy h ρ - sInf {e : ℝ | ∃ v : Matrix.unitaryGroup (Fin d) ℂ,
    e = energy h ((v : Matrix (Fin d) (Fin d) ℂ) * ρ * star v)}

/-- The proposed half-ergotropy inequality for non-stationary density matrices. -/
def claim : Prop :=
  ∀ (d : ℕ) (h ρ : Matrix (Fin d) (Fin d) ℂ),
    h.IsHermitian → ρ.PosSemidef → ρ.trace = 1 → h * ρ ≠ ρ * h →
      metrotropy h ρ ≤ ergotropy h ρ / 2

private def h4 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![(0 : ℂ), 1, 2, 10]

private def psi4 : Fin 4 → ℂ := ![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5]

private def rho4 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.vecMulVec psi4 (star psi4)

private def u4 : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]

private lemma rho4_pos : rho4.PosSemidef := by sorry
private lemma rho4_trace : rho4.trace = 1 := by sorry
private lemma h4_hermitian : h4.IsHermitian := by sorry
private lemma h4_commutator : h4 * rho4 ≠ rho4 * h4 := by sorry
private lemma u4_unitary : u4 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by sorry
private lemma measured_u4 : measured ⟨u4, u4_unitary⟩ rho4 = (1 / 4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
private lemma energy_rho4 : energy h4 rho4 = 178 / 25 := by sorry
private lemma energy_measured_u4 : energy h4 (measured ⟨u4, u4_unitary⟩ rho4) = 13 / 4 := by sorry
private lemma measured_posSemidef {d : ℕ} (u : Matrix.unitaryGroup (Fin d) ℂ)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef) : (measured u ρ).PosSemidef := by sorry
private lemma conjugated_posSemidef {d : ℕ} (v : Matrix.unitaryGroup (Fin d) ℂ)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef) :
    ((v : Matrix (Fin d) (Fin d) ℂ) * ρ * star v).PosSemidef := by sorry
private lemma energy_nonneg {d : ℕ} {h σ : Matrix (Fin d) (Fin d) ℂ}
    (hh : h = Matrix.diagonal (fun i => h i i)) (hσ : σ.PosSemidef)
    (hn : ∀ i, 0 ≤ (h i i).re) : 0 ≤ energy h σ := by sorry
private lemma metrotropy_lower : 387 / 100 ≤ metrotropy h4 rho4 := by sorry
private lemma ergotropy_upper : ergotropy h4 rho4 ≤ 178 / 25 := by sorry
private lemma instance_violates : ¬ metrotropy h4 rho4 ≤ ergotropy h4 rho4 / 2 := by sorry

theorem result : ¬ claim := by
  sorry

end D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
