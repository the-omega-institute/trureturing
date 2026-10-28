/- GID: D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.claim; result=D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.result; claim=D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.claim
   digest: A rational qutrit measurement beats both error-disturbance endpoints. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation
import D5.S3.Weil.ZetaLinear.RankTrace

set_option autoImplicit false
set_option linter.style.longLine false
open scoped BigOperators ComplexOrder Matrix
open Matrix
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation (measurementProjector)

namespace D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation

noncomputable section

/-- The infinity distance between the two labeled outcome distributions. -/
def errorAt {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (a c : unitaryGroup (Fin d) ℂ) : ℝ :=
  ⨆ i, |(trace (ρ * (measurementProjector a i - measurementProjector c i))).re|

/-- The infinity distance before and after the nonselective intermediate measurement. -/
def disturbanceAt {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (c b : unitaryGroup (Fin d) ℂ) : ℝ :=
  ⨆ j, |(trace (ρ * (measurementProjector b j -
    ∑ k, measurementProjector c k * measurementProjector b j * measurementProjector c k))).re|

/-- The supremum of the sum, over one common density matrix. -/
def overallError {d : ℕ} (a c b : unitaryGroup (Fin d) ℂ) : ℝ :=
  sSup {t | ∃ ρ, IsDensity ρ ∧ t = errorAt ρ a c + disturbanceAt ρ c b}

/-- The worst state-dependent labeled error. -/
def error {d : ℕ} (a c : unitaryGroup (Fin d) ℂ) : ℝ :=
  sSup {t | ∃ ρ, IsDensity ρ ∧ t = errorAt ρ a c}

/-- The worst state-dependent disturbance. -/
def disturbance {d : ℕ} (c b : unitaryGroup (Fin d) ℂ) : ℝ :=
  sSup {t | ∃ ρ, IsDensity ρ ∧ t = disturbanceAt ρ c b}

/-- Relabel the columns of a measurement basis. -/
def relabel {d : ℕ} (b : unitaryGroup (Fin d) ℂ) (π : Equiv.Perm (Fin d)) :
    unitaryGroup (Fin d) ℂ :=
  ⟨b.val.submatrix (Equiv.refl _) π, Matrix.submatrix_equiv_mem_unitary.mpr b.property⟩

/-- The minimum error over all outcome relabelings. -/
def relaxedError {d : ℕ} (a b : unitaryGroup (Fin d) ℂ) : ℝ :=
  ⨅ π : Equiv.Perm (Fin d), error a (relabel b π)

/-- The second inequality of Zhou, Wu and Chau's Conjecture 3. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ a c b : unitaryGroup (Fin d) ℂ,
    min (relaxedError a b) (disturbance a b) ≤ overallError a c b

private def u : Matrix (Fin 3) (Fin 3) ℂ :=
  !![312/313, -25/313, 0; 25/313, 312/313, 0; 0, 0, 1]

private def v : Matrix (Fin 3) (Fin 3) ℂ :=
  !![32976/33205, -3757/33205, -1020/33205;
     3893/33205, 31824/33205, 8640/33205; 0, -8700/33205, 32045/33205]

private lemma u_unitary : u ∈ unitaryGroup (Fin 3) ℂ := by
  sorry

private lemma v_unitary : v ∈ unitaryGroup (Fin 3) ℂ := by
  sorry

private def c : unitaryGroup (Fin 3) ℂ := ⟨u, u_unitary⟩
private def b : unitaryGroup (Fin 3) ℂ := ⟨v, v_unitary⟩

private def e (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  measurementProjector 1 i - measurementProjector c i

private def f (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  measurementProjector b j -
    ∑ k, measurementProjector c k * measurementProjector b j * measurementProjector c k

private lemma signed_certificate (i j : Fin 3) (ε δ : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    ((71/250 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (ε • e i + δ • f j)).PosSemidef := by
  sorry

private lemma signed_expectation (ρ : Matrix (Fin 3) (Fin 3) ℂ) (hρ : IsDensity ρ)
    (i j : Fin 3) (ε δ : ℝ) (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    ε * (trace (ρ * e i)).re + δ * (trace (ρ * f j)).re ≤ 71/250 := by
  sorry

private lemma state_overall_bound (ρ : Matrix (Fin 3) (Fin 3) ℂ)
    (hρ : IsDensity ρ) : errorAt ρ 1 c + disturbanceAt ρ c b ≤ 71/250 := by
  sorry

private lemma density_exists : ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ, IsDensity ρ := by
  sorry

private lemma overall_bound : overallError 1 c b ≤ 71/250 := by
  sorry

private lemma disturbance_bdd : BddAbove
    {t | ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ, IsDensity ρ ∧ t = disturbanceAt ρ 1 b} := by
  sorry

private lemma error_bdd (π : Equiv.Perm (Fin 3)) : BddAbove
    {t | ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ,
      IsDensity ρ ∧ t = errorAt ρ 1 (relabel b π)} := by
  sorry

private lemma disturbance_witness : ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ,
    IsDensity ρ ∧ (57/200 : ℝ) < disturbanceAt ρ 1 b := by
  sorry

private lemma error_witness (π : Equiv.Perm (Fin 3)) :
    ∃ ρ : Matrix (Fin 3) (Fin 3) ℂ,
      IsDensity ρ ∧ (57/200 : ℝ) < errorAt ρ 1 (relabel b π) := by
  sorry

private lemma disturbance_lower : (57/200 : ℝ) < disturbance 1 b := by
  obtain ⟨ρ, hρ, ht⟩ := disturbance_witness
  exact ht.trans_le (le_csSup disturbance_bdd ⟨ρ, hρ, rfl⟩)

private lemma relaxed_lower : (57/200 : ℝ) < relaxedError 1 b := by
  apply (lt_ciInf_iff).2
  intro π
  obtain ⟨ρ, hρ, ht⟩ := error_witness π
  exact ht.trans_le (le_csSup (error_bdd π) ⟨ρ, hρ, rfl⟩)

theorem result : ¬ claim := by
  intro h
  have hh := h 3 (by norm_num) 1 c b
  have hl := lt_min relaxed_lower disturbance_lower
  have hu := overall_bound
  norm_num at *
  linarith

end
end D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation
