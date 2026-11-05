/- GID: D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar
   generality: I
   mirror-B: D5/B/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The star-graph evolution maps are conjugate by the unitary propagation matrix. -/

import D5.S3.Weil.ZetaCore.PaperFT

/-! Unitary similarity in Andrade–Severini, arXiv:1808.01154v2, Claim 1. -/

namespace D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar

noncomputable section

/-- The vertex-scattering matrix in the amplitude order `(a12, b12, ..., a1n, b1n)`. -/
def scatteringMatrix {n : ℕ} (r : Fin (n - 1) → ℂ) (r1 t1 : ℂ) :
    Matrix (Fin (n - 1) × Fin 2) (Fin (n - 1) × Fin 2) ℂ :=
  fun p q =>
    if p.2 = 0 then
      if q.1 = p.1 ∧ q.2 = 1 then r p.1 else 0
    else if q.2 = 1 then 0 else if q.1 = p.1 then r1 else t1

/-- Propagation along each edge multiplies both amplitudes by `exp (I * k * ℓ)`. -/
def propagationMatrix {n : ℕ} (k : ℝ) (ℓ : Fin (n - 1) → ℝ) :
    Matrix (Fin (n - 1) × Fin 2) (Fin (n - 1) × Fin 2) ℂ :=
  Matrix.diagonal fun p => Complex.exp (Complex.I * k * ℓ p.1)

/-- Andrade–Severini Claim 1 for every star graph and all vertex amplitudes. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (r : Fin (n - 1) → ℂ) (r1 t1 : ℂ) (k : ℝ)
    (ℓ : Fin (n - 1) → ℝ),
    ∃ w ∈ Matrix.unitaryGroup (Fin (n - 1) × Fin 2) ℂ,
      w * (scatteringMatrix r r1 t1 * propagationMatrix k ℓ) * star w =
        propagationMatrix k ℓ * scatteringMatrix r r1 t1

private lemma phase_norm (k l : ℝ) : ‖Complex.exp (Complex.I * k * l)‖ = 1 := by
  simpa only [Complex.ofReal_im, zero_mul, neg_zero, Real.exp_zero] using
    Zeta23.norm_cexp_I_mul (k : ℂ) l

private lemma propagation_unitary {n : ℕ} (k : ℝ) (ℓ : Fin (n - 1) → ℝ) :
    propagationMatrix k ℓ ∈ Matrix.unitaryGroup (Fin (n - 1) × Fin 2) ℂ := by
  change Matrix.diagonal (fun p : Fin (n - 1) × Fin 2 =>
    Complex.exp (Complex.I * k * ℓ p.1)) ∈ unitary _
  rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
  intro p
  rw [Unitary.mem_iff]
  simp only [Complex.star_def, Complex.conj_mul', Complex.mul_conj',
    phase_norm, one_pow, Complex.ofReal_one, and_self]

private lemma evolution_conjugation {n : ℕ} (r : Fin (n - 1) → ℂ) (r1 t1 : ℂ)
    (k : ℝ) (ℓ : Fin (n - 1) → ℝ) :
    propagationMatrix k ℓ * (scatteringMatrix r r1 t1 * propagationMatrix k ℓ) *
      star (propagationMatrix k ℓ) = propagationMatrix k ℓ * scatteringMatrix r r1 t1 := by
  simpa only [mul_assoc] using!
    Units.mul_inv_cancel_right (propagationMatrix k ℓ * scatteringMatrix r r1 t1)
      (Unitary.toUnits ⟨propagationMatrix k ℓ, propagation_unitary k ℓ⟩)

/-- The propagation matrix itself witnesses unitary similarity. -/
theorem result : claim := by
  intro n _ r r1 t1 k ℓ
  exact ⟨propagationMatrix k ℓ, propagation_unitary k ℓ,
    evolution_conjugation r r1 t1 k ℓ⟩

end

end D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar
