/- GID: D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.claim; result=D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.result; claim=D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.claim
   digest: Nonstationary two-qutrit dephasing can preserve positive negativity. -/

import D5.S3.QuantumBounds.NegativityReductionInclusionRefutation

/-! A two-qubit corner of the qutrit space supports a nonstationary state whose
positive negativity remains constant under collective dephasing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Decoherence.QutritCollectiveDephasingInvariantNegativityRefutation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.QuantumBounds.NegativityReductionInclusionRefutation (negativity)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_sub_orthogonal)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

/-- The damping factor in Ali's collective dephasing channel. -/
def gammaFactor (Γ t : ℝ) : ℝ := Real.exp (-(Γ * t) / 2)

def omega1 (Γ t : ℝ) : ℝ := Real.sqrt (1 - gammaFactor Γ t ^ 2)

def omega2 (Γ t : ℝ) : ℝ := -gammaFactor Γ t ^ 2 * Real.sqrt (1 - gammaFactor Γ t ^ 2)

def omega3 (Γ t : ℝ) : ℝ :=
  (1 - gammaFactor Γ t ^ 2) * Real.sqrt (1 + gammaFactor Γ t ^ 2)

def kraus1 (Γ t : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.diagonal (fun p => if p.1 = p.2 then (gammaFactor Γ t : ℂ) else 1)

def kraus2 (Γ t : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.diagonal (fun p => if p = (0, 0) then (omega1 Γ t : ℂ)
    else if p = (1, 1) ∨ p = (2, 2) then (omega2 Γ t : ℂ) else 0)

def kraus3 (Γ t : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.diagonal (fun p => if p = (1, 1) ∨ p = (2, 2)
    then (omega3 Γ t : ℂ) else 0)

def evolve (Γ t : ℝ) (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (kraus1 Γ t)ᴴ * ρ * kraus1 Γ t + (kraus2 Γ t)ᴴ * ρ * kraus2 Γ t +
    (kraus3 Γ t)ᴴ * ρ * kraus3 Γ t

def claim : Prop :=
  ∀ (Γ : ℝ), 0 < Γ → ∀ ρ₀ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
    ρ₀.PosSemidef → ρ₀.trace = 1 → 0 < negativity ρ₀ →
    (∀ t : ℝ, 0 ≤ t → negativity (evolve Γ t ρ₀) = negativity ρ₀) →
    ∀ t : ℝ, 0 ≤ t → evolve Γ t ρ₀ = ρ₀

private def uPlus : Fin 3 × Fin 3 → ℂ := Pi.single (0, 0) 1 + Pi.single (1, 1) 1
private def uMinus : Fin 3 × Fin 3 → ℂ := Pi.single (0, 0) 1 - Pi.single (1, 1) 1
private def wPlus : Fin 3 × Fin 3 → ℂ := Pi.single (0, 1) 1 + Pi.single (1, 0) 1
private def wMinus : Fin 3 × Fin 3 → ℂ := Pi.single (0, 1) 1 - Pi.single (1, 0) 1

private def rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (3 / 8 : ℝ) • rankOneDensity wPlus + (1 / 8 : ℝ) • rankOneDensity uPlus

private def state (g : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (3 / 8 : ℝ) • rankOneDensity wPlus +
    ((1 + g ^ 4) / 16) • rankOneDensity uPlus +
    ((1 - g ^ 4) / 16) • rankOneDensity uMinus

private def positivePart (g : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 4 : ℝ) • rankOneDensity uPlus +
    ((3 + g ^ 4) / 16) • rankOneDensity wPlus +
    ((3 - g ^ 4) / 16) • rankOneDensity wMinus

private def negativePart : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 8 : ℝ) • rankOneDensity uMinus

private theorem rho_posSemidef : rho.PosSemidef := by
  exact ((Matrix.posSemidef_vecMulVec_self_star wPlus).smul (show (0 : ℝ) ≤ 3 / 8 by
    norm_num)).add ((Matrix.posSemidef_vecMulVec_self_star uPlus).smul
      (show (0 : ℝ) ≤ 1 / 8 by norm_num))

private theorem rho_trace : rho.trace = 1 := by
  norm_num [rho, rankOneDensity, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_vecMulVec, dotProduct, wPlus, uPlus, Pi.star_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three, Pi.single_apply]

private theorem state_one : state 1 = rho := by
  norm_num [state, rho]

private theorem gamma_bounds (t : ℝ) (ht : 0 ≤ t) :
    0 < gammaFactor 2 t ∧ gammaFactor 2 t ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    linarith

private theorem kraus_coefficients (t : ℝ) (ht : 0 ≤ t) :
    gammaFactor 2 t ^ 2 + omega1 2 t ^ 2 = 1 ∧
    gammaFactor 2 t ^ 2 + omega2 2 t ^ 2 + omega3 2 t ^ 2 = 1 ∧
    gammaFactor 2 t ^ 2 + omega1 2 t * omega2 2 t = gammaFactor 2 t ^ 4 := by
  obtain ⟨hg0, hg1⟩ := gamma_bounds t ht
  have hgsq : gammaFactor 2 t ^ 2 ≤ 1 := pow_le_one₀ hg0.le hg1
  have h1 := Real.sq_sqrt (show 0 ≤ 1 - gammaFactor 2 t ^ 2 by linarith)
  have h2 := Real.sq_sqrt (show 0 ≤ 1 + gammaFactor 2 t ^ 2 by positivity)
  dsimp [omega1, omega2, omega3]
  constructor
  · linarith
  constructor
  · simp only [mul_pow, neg_sq, h1, h2]
    ring
  · calc
      gammaFactor 2 t ^ 2 + Real.sqrt (1 - gammaFactor 2 t ^ 2) *
          (-gammaFactor 2 t ^ 2 * Real.sqrt (1 - gammaFactor 2 t ^ 2)) =
          gammaFactor 2 t ^ 2 - gammaFactor 2 t ^ 2 *
            Real.sqrt (1 - gammaFactor 2 t ^ 2) ^ 2 := by ring
      _ = _ := by rw [h1]; ring

set_option maxRecDepth 4096 in
private theorem evolve_rho (t : ℝ) (ht : 0 ≤ t) :
    evolve 2 t rho = state (gammaFactor 2 t) := by
  obtain ⟨h1, h2, h3⟩ := kraus_coefficients t ht
  have hc1 : (gammaFactor 2 t : ℂ) ^ 2 + (omega1 2 t : ℂ) ^ 2 = 1 := by
    exact_mod_cast h1
  have hc2 : (gammaFactor 2 t : ℂ) ^ 2 + (omega2 2 t : ℂ) ^ 2 +
      (omega3 2 t : ℂ) ^ 2 = 1 := by exact_mod_cast h2
  have hc3 : (gammaFactor 2 t : ℂ) ^ 2 + (omega1 2 t : ℂ) * (omega2 2 t : ℂ) =
      (gammaFactor 2 t : ℂ) ^ 4 := by exact_mod_cast h3
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [evolve, kraus1, kraus2, kraus3, Matrix.add_apply,
    Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [rho, state, rankOneDensity, uPlus, uMinus, wPlus,
      Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, Pi.star_apply,
      Pi.single_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_div, Complex.ofReal_pow] <;>
    first | linear_combination (1 / 8 : ℂ) * hc1 |
      linear_combination (1 / 8 : ℂ) * hc2 | linear_combination (1 / 8 : ℂ) * hc3

private theorem positivePart_posSemidef (g : ℝ) (hg : 0 ≤ g) (hg1 : g ≤ 1) :
    (positivePart g).PosSemidef := by
  have hg4 : g ^ 4 ≤ 1 := pow_le_one₀ hg hg1
  exact (((Matrix.posSemidef_vecMulVec_self_star uPlus).smul
    (show (0 : ℝ) ≤ 1 / 4 by norm_num)).add
    ((Matrix.posSemidef_vecMulVec_self_star wPlus).smul
      (show 0 ≤ (3 + g ^ 4) / 16 by positivity))).add
    ((Matrix.posSemidef_vecMulVec_self_star wMinus).smul
      (show 0 ≤ (3 - g ^ 4) / 16 by linarith))

private theorem negativePart_posSemidef : negativePart.PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star uMinus).smul
    (show (0 : ℝ) ≤ 1 / 8 by norm_num)

set_option maxRecDepth 4096 in
private theorem partialTranspose_state (g : ℝ) :
    partialTranspose (state g) = positivePart g - negativePart := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [partialTranspose, state, positivePart, negativePart, rankOneDensity,
      uPlus, uMinus, wPlus, wMinus, Matrix.vecMulVec_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Pi.star_apply, Pi.single_apply,
      smul_eq_mul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_pow] <;> ring

private theorem parts_orthogonal (g : ℝ) : positivePart g * negativePart = 0 := by
  have hU : star uPlus ⬝ᵥ uMinus = 0 := by
    norm_num [dotProduct, uPlus, uMinus, Pi.star_apply, Pi.single_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three]
  have hW : star wPlus ⬝ᵥ uMinus = 0 := by
    norm_num [dotProduct, wPlus, uMinus, Pi.star_apply, Pi.single_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three]
  have hM : star wMinus ⬝ᵥ uMinus = 0 := by
    norm_num [dotProduct, wMinus, uMinus, Pi.star_apply, Pi.single_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [positivePart, negativePart, add_mul,
    rankOneDensity, Matrix.vecMulVec_mul_vecMulVec, hU, hW, hM]

private theorem parts_trace (g : ℝ) :
    (positivePart g).trace.re + negativePart.trace.re = 3 / 2 := by
  norm_num [positivePart, negativePart, rankOneDensity, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_vecMulVec, dotProduct, uPlus, uMinus, wPlus, wMinus, Pi.star_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three, Pi.single_apply, Complex.add_re,
    Complex.real_smul, smul_eq_mul]
  ring

private theorem negativity_state (g : ℝ) (hg : 0 ≤ g) (hg1 : g ≤ 1) :
    negativity (state g) = 1 / 4 := by
  rw [negativity, partialTranspose_state,
    traceNorm_sub_orthogonal _ _ (positivePart_posSemidef g hg hg1)
      negativePart_posSemidef (parts_orthogonal g), parts_trace]
  norm_num

private theorem negativity_rho : negativity rho = 1 / 4 := by
  rw [← state_one]
  exact negativity_state 1 (by norm_num) (by norm_num)

private theorem negativity_evolve (t : ℝ) (ht : 0 ≤ t) :
    negativity (evolve 2 t rho) = negativity rho := by
  rw [evolve_rho t ht, negativity_rho]
  obtain ⟨hg0, hg1⟩ := gamma_bounds t ht
  exact negativity_state _ hg0.le hg1

private theorem evolve_ne : evolve 2 1 rho ≠ rho := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ =>
    (M (0, 0) (1, 1)).re) h
  rw [evolve_rho 1 (by norm_num)] at he
  have hg0 := (gamma_bounds 1 (by norm_num)).1.le
  have hg1 : gammaFactor 2 1 < 1 := by
    apply Real.exp_lt_one_iff.mpr
    norm_num
  have hg4 := pow_lt_one₀ hg0 hg1 (by decide : (4 : ℕ) ≠ 0)
  norm_num [state, rho, rankOneDensity, uPlus, uMinus, wPlus,
    Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, Pi.star_apply,
    Pi.single_apply, smul_eq_mul] at he
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at he
  linarith

theorem result : ¬ claim := by
  intro h
  exact evolve_ne (h 2 (by norm_num) rho rho_posSemidef rho_trace
    (by rw [negativity_rho]; norm_num) negativity_evolve 1 (by norm_num))

end D5.S3.Quantum.Decoherence.QutritCollectiveDephasingInvariantNegativityRefutation
