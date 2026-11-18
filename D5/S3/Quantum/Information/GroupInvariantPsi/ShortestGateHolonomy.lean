/- GID: D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shortest qubit rotor gates and the return phase of a triangle of Bloch directions. -/

import D5.S3.Quantum.Information.GroupInvariantPsi.C129QubitBargmann

/-! # Shortest gates and the return phase of a Bloch triangle

Vectors of `ℝ³` are represented in the Pauli model of `Cl(3,0)`: the vector `r` is the
matrix `pauliCombination r = r₀σ_x + r₁σ_y + r₂σ_z`, the geometric product is the matrix
product, and reversion is the conjugate transpose. For unit vectors `a, b` with `b ≠ -a`
the gate is `rotor a b = (1 + (b·σ)(a·σ)) / √(2(1 + a·b))`. It is unitary, carries
`a·σ` to `b·σ` by conjugation, and acts on a unit spinor with Bloch vector `a` as the
normalized projection `ψ ↦ P_b ψ / √⟨ψ|P_b|ψ⟩`. For unit `a, b, c`, pairwise
non-antipodal, with `S = 1 + a·b + b·c + c·a` and `D = a·(b×c)`, the product of the three
gates along `a → b → c → a` is
`(S − iD(a·σ)) / √(S² + D²)`. Applied to a unit spinor with Bloch vector `a`, the three
sequential normalized projections return `ψ` multiplied by `(S − iD) / √(S² + D²)`. The
Gram identity `D² = 1 + 2(a·b)(b·c)(c·a) − (a·b)² − (b·c)² − (c·a)²` gives
`S² + D² = 2(1 + a·b)(1 + b·c)(1 + c·a)`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open D5.S3.Quantum.Information.GroupInvariantPsi.C129QubitBargmann

namespace D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy

/-- The rotor gate from Bloch direction `a` to `b`:
`(1 + (b·σ)(a·σ)) / √(2(1 + a·b))`. "Shortest" is a name only; no minimality is stated. -/
def rotor (a b : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((Real.sqrt (2 * (1 + a ⬝ᵥ b)) : ℝ) : ℂ))⁻¹ •
    (1 + pauliCombination b * pauliCombination a)

/-- The normalized projection of the current input onto Bloch direction `b`:
`P_b ψ / √⟨ψ|P_b|ψ⟩`, with the square root taken of the real part of `⟨ψ|P_b|ψ⟩`. -/
def shortestGate (b : Fin 3 → ℝ) (ψ : QubitState) : QubitState :=
  (((Real.sqrt (star ψ ⬝ᵥ (qubitProjector b *ᵥ ψ)).re : ℝ) : ℂ))⁻¹ •
    (qubitProjector b *ᵥ ψ)

/-- `S = 1 + a·b + b·c + c·a`. -/
def triangleS (a b c : Fin 3 → ℝ) : ℝ := 1 + a ⬝ᵥ b + b ⬝ᵥ c + c ⬝ᵥ a

/-- `D = a·(b×c)`. -/
def triangleD (a b c : Fin 3 → ℝ) : ℝ := a ⬝ᵥ (b ⨯₃ c)

private lemma unit_coords {a : Fin 3 → ℝ} (ha : a ⬝ᵥ a = 1) :
    a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1 := by
  rw [← ha]
  simp [dotProduct, Fin.sum_univ_three, sq]

private lemma one_add_dot_pos {a b : Fin 3 → ℝ} (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1)
    (hab : b ≠ -a) : 0 < 1 + a ⬝ᵥ b := by
  have hne : a + b ≠ 0 := by
    intro h0
    apply hab
    ext i
    have := congrFun h0 i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    simp only [Pi.neg_apply]
    linarith
  have hnn : 0 ≤ (a + b) ⬝ᵥ (a + b) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg ((a + b) i))
  have hpos : 0 < (a + b) ⬝ᵥ (a + b) :=
    lt_of_le_of_ne hnn (Ne.symm (fun h => hne (dotProduct_self_eq_zero.mp h)))
  have hexp : (a + b) ⬝ᵥ (a + b) = 2 * (1 + a ⬝ᵥ b) := by
    simp only [add_dotProduct, dotProduct_add, ha, hb, dotProduct_comm b a]
    ring
  linarith

private lemma qubitProjector_conjTranspose (a : Fin 3 → ℝ) :
    (qubitProjector a)ᴴ = qubitProjector a := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [qubitProjector, pauliCombination, Matrix.conjTranspose_apply] <;>
    ring

private lemma trace_projector_mul (a b : Fin 3 → ℝ) :
    trace (qubitProjector a * qubitProjector b) = (((1 + a ⬝ᵥ b) / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [qubitProjector, pauliCombination, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, dotProduct, Fin.sum_univ_three] <;> ring

private lemma num_mul_conjTranspose (a b : Fin 3 → ℝ)
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (hb : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 = 1) :
    (1 + pauliCombination b * pauliCombination a) *
        (1 + pauliCombination b * pauliCombination a)ᴴ =
      ((2 * (1 + a ⬝ᵥ b) : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      linear_combination ((b 0)^2 + (b 1)^2 + (b 2)^2) * ha + (1) * hb
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      ring
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      ring
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      ring
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      ring
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      ring
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      linear_combination ((b 0)^2 + (b 1)^2 + (b 2)^2) * ha + (1) * hb
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      ring

private lemma num_transport (a b : Fin 3 → ℝ)
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (hb : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 = 1) :
    (1 + pauliCombination b * pauliCombination a) * pauliCombination a *
        (1 + pauliCombination b * pauliCombination a)ᴴ =
      ((2 * (1 + a ⬝ᵥ b) : ℝ) : ℂ) • pauliCombination b := by
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      linear_combination (2*(a 0)*(b 0)*(b 2) + 2*(a 1)*(b 1)*(b 2) - (a 2)*(b 0)^2 - (a 2)*(b 1)^2 + (a 2)*(b 2)^2 + 2*(b 2)) * ha + (-(a 2)) * hb
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      ring
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      linear_combination ((a 0)*(b 0)^2 - (a 0)*(b 1)^2 - (a 0)*(b 2)^2 + 2*(a 1)*(b 0)*(b 1) + 2*(a 2)*(b 0)*(b 2) + 2*(b 0)) * ha + (-(a 0)) * hb
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      linear_combination (-2*(a 0)*(b 0)*(b 1) + (a 1)*(b 0)^2 - (a 1)*(b 1)^2 + (a 1)*(b 2)^2 - 2*(a 2)*(b 1)*(b 2) - 2*(b 1)) * ha + ((a 1)) * hb
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      linear_combination ((a 0)*(b 0)^2 - (a 0)*(b 1)^2 - (a 0)*(b 2)^2 + 2*(a 1)*(b 0)*(b 1) + 2*(a 2)*(b 0)*(b 2) + 2*(b 0)) * ha + (-(a 0)) * hb
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      linear_combination (2*(a 0)*(b 0)*(b 1) - (a 1)*(b 0)^2 + (a 1)*(b 1)^2 - (a 1)*(b 2)^2 + 2*(a 2)*(b 1)*(b 2) + 2*(b 1)) * ha + (-(a 1)) * hb
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      linear_combination (-2*(a 0)*(b 0)*(b 2) - 2*(a 1)*(b 1)*(b 2) + (a 2)*(b 0)^2 + (a 2)*(b 1)^2 - (a 2)*(b 2)^2 - 2*(b 2)) * ha + ((a 2)) * hb
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_three]
      ring

private lemma num_triangle (a b c : Fin 3 → ℝ)
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (hb : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 = 1)
    (hc : c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 = 1) :
    (1 + pauliCombination a * pauliCombination c) *
        (1 + pauliCombination c * pauliCombination b) *
        (1 + pauliCombination b * pauliCombination a) =
      ((2 * triangleS a b c : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        ((2 * triangleD a b c : ℝ) : ℂ) • (Complex.I • pauliCombination a) := by
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, dotProduct, Fin.sum_univ_three, triangleS, triangleD, cross_apply]
      linear_combination ((b 0)^2*(c 0)^2 + (b 0)^2*(c 1)^2 + (b 0)^2*(c 2)^2 + (b 0)*(c 0) + (b 1)^2*(c 0)^2 + (b 1)^2*(c 1)^2 + (b 1)^2*(c 2)^2 + (b 1)*(c 1) + (b 2)^2*(c 0)^2 + (b 2)^2*(c 1)^2 + (b 2)^2*(c 2)^2 + (b 2)*(c 2)) * ha + ((a 0)*(c 0) + (a 1)*(c 1) + (a 2)*(c 2) + (c 0)^2 + (c 1)^2 + (c 2)^2) * hb + ((a 0)*(b 0) + (a 1)*(b 1) + (a 2)*(b 2) + 1) * hc
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, dotProduct, Fin.sum_univ_three, triangleS, triangleD, cross_apply]
      linear_combination ((b 0)*(c 1) - (b 1)*(c 0)) * ha + (-(a 0)*(c 1) + (a 1)*(c 0)) * hb + ((a 0)*(b 1) - (a 1)*(b 0)) * hc
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, dotProduct, Fin.sum_univ_three, triangleS, triangleD, cross_apply]
      linear_combination (-(b 0)*(c 2) + (b 2)*(c 0)) * ha + ((a 0)*(c 2) - (a 2)*(c 0)) * hb + (-(a 0)*(b 2) + (a 2)*(b 0)) * hc
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, dotProduct, Fin.sum_univ_three, triangleS, triangleD, cross_apply]
      linear_combination ((b 1)*(c 2) - (b 2)*(c 1)) * ha + (-(a 1)*(c 2) + (a 2)*(c 1)) * hb + ((a 1)*(b 2) - (a 2)*(b 1)) * hc
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, dotProduct, Fin.sum_univ_three, triangleS, triangleD, cross_apply]
      linear_combination ((b 0)*(c 2) - (b 2)*(c 0)) * ha + (-(a 0)*(c 2) + (a 2)*(c 0)) * hb + ((a 0)*(b 2) - (a 2)*(b 0)) * hc
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, dotProduct, Fin.sum_univ_three, triangleS, triangleD, cross_apply]
      linear_combination ((b 1)*(c 2) - (b 2)*(c 1)) * ha + (-(a 1)*(c 2) + (a 2)*(c 1)) * hb + ((a 1)*(b 2) - (a 2)*(b 1)) * hc
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, dotProduct, Fin.sum_univ_three, triangleS, triangleD, cross_apply]
      linear_combination ((b 0)^2*(c 0)^2 + (b 0)^2*(c 1)^2 + (b 0)^2*(c 2)^2 + (b 0)*(c 0) + (b 1)^2*(c 0)^2 + (b 1)^2*(c 1)^2 + (b 1)^2*(c 2)^2 + (b 1)*(c 1) + (b 2)^2*(c 0)^2 + (b 2)^2*(c 1)^2 + (b 2)^2*(c 2)^2 + (b 2)*(c 2)) * ha + ((a 0)*(c 0) + (a 1)*(c 1) + (a 2)*(c 2) + (c 0)^2 + (c 1)^2 + (c 2)^2) * hb + ((a 0)*(b 0) + (a 1)*(b 1) + (a 2)*(b 2) + 1) * hc
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, dotProduct, Fin.sum_univ_three, triangleS, triangleD, cross_apply]
      linear_combination (-(b 0)*(c 1) + (b 1)*(c 0)) * ha + ((a 0)*(c 1) - (a 1)*(c 0)) * hb + (-(a 0)*(b 1) + (a 1)*(b 0)) * hc

private lemma projector_sandwich (a : Fin 3 → ℝ) (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    qubitProjector a * X * qubitProjector a =
      trace (qubitProjector a * X) • qubitProjector a := by
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, qubitProjector, Matrix.trace, Matrix.diag, Matrix.smul_apply]
      linear_combination ((X 1 1).re/4) * ha
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, qubitProjector, Matrix.trace, Matrix.diag, Matrix.smul_apply]
      linear_combination ((X 1 1).im/4) * ha
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, qubitProjector, Matrix.trace, Matrix.diag, Matrix.smul_apply]
      linear_combination (-(X 0 1).re/4) * ha
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, qubitProjector, Matrix.trace, Matrix.diag, Matrix.smul_apply]
      linear_combination (-(X 0 1).im/4) * ha
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, qubitProjector, Matrix.trace, Matrix.diag, Matrix.smul_apply]
      linear_combination (-(X 1 0).re/4) * ha
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, qubitProjector, Matrix.trace, Matrix.diag, Matrix.smul_apply]
      linear_combination (-(X 1 0).im/4) * ha
  · apply Complex.ext
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, qubitProjector, Matrix.trace, Matrix.diag, Matrix.smul_apply]
      linear_combination ((X 0 0).re/4) * ha
    · simp [pauliCombination, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, qubitProjector, Matrix.trace, Matrix.diag, Matrix.smul_apply]
      linear_combination ((X 0 0).im/4) * ha

private lemma pauli_mulVec_of_projector {a : Fin 3 → ℝ} {ψ : QubitState}
    (h : qubitProjector a *ᵥ ψ = ψ) : pauliCombination a *ᵥ ψ = ψ := by
  funext i
  have hi := congrFun h i
  simp only [qubitProjector, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hi
  linear_combination 2 * hi

private lemma expectation_eq_trace {a : Fin 3 → ℝ} (ha : a ⬝ᵥ a = 1) {ψ : QubitState}
    (hψa : qubitProjector a *ᵥ ψ = ψ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    star ψ ⬝ᵥ (X *ᵥ ψ) = trace (qubitProjector a * X) := by
  calc star ψ ⬝ᵥ (X *ᵥ ψ)
      = star (qubitProjector a *ᵥ ψ) ⬝ᵥ (X *ᵥ (qubitProjector a *ᵥ ψ)) := by rw [hψa]
    _ = star ψ ⬝ᵥ ((qubitProjector a * X * qubitProjector a) *ᵥ ψ) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, qubitProjector_conjTranspose,
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = trace (qubitProjector a * X) * (star ψ ⬝ᵥ (qubitProjector a *ᵥ ψ)) := by
        rw [projector_sandwich a (unit_coords ha), Matrix.smul_mulVec, dotProduct_smul,
          smul_eq_mul]
    _ = trace (qubitProjector a * X) := by rw [hψa, hψ, mul_one]

private lemma inv_sqrt_sq {q : ℝ} (hq : 0 < q) :
    (((Real.sqrt q : ℝ) : ℂ))⁻¹ * (((Real.sqrt q : ℝ) : ℂ))⁻¹ * ((q : ℝ) : ℂ) = 1 := by
  have hs : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  have hs0 : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have hq' : ((q : ℝ) : ℂ) = ((Real.sqrt q : ℝ) : ℂ) * ((Real.sqrt q : ℝ) : ℂ) := by
    exact_mod_cast hs.symm
  rw [hq']
  field_simp

/-- The gate from `a` to `b`. For unit `a, b` with `b ≠ -a`, `rotor a b` is unitary,
conjugates `a·σ` to `b·σ`, and on a unit spinor `ψ` with Bloch vector `a` (`P_a ψ = ψ`)
equals the normalized projection `P_b ψ / √⟨ψ|P_b|ψ⟩`. -/
theorem rotor_shortest_gate (a b : Fin 3 → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1)
    (hab : b ≠ -a) :
    rotor a b * (rotor a b)ᴴ = 1 ∧
      rotor a b * pauliCombination a * (rotor a b)ᴴ = pauliCombination b ∧
      ∀ ψ : QubitState, star ψ ⬝ᵥ ψ = 1 → qubitProjector a *ᵥ ψ = ψ →
        rotor a b *ᵥ ψ = shortestGate b ψ := by
  have hpos : 0 < 2 * (1 + a ⬝ᵥ b) := by linarith [one_add_dot_pos ha hb hab]
  have hk := inv_sqrt_sq hpos
  refine ⟨?_, ?_, ?_⟩
  · simp only [rotor, Matrix.conjTranspose_smul, star_inv₀, Complex.star_def,
      Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [num_mul_conjTranspose a b (unit_coords ha) (unit_coords hb)]
    simp only [smul_smul]
    rw [hk, one_smul]
  · simp only [rotor, Matrix.conjTranspose_smul, star_inv₀, Complex.star_def,
      Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [num_transport a b (unit_coords ha) (unit_coords hb)]
    simp only [smul_smul]
    rw [hk, one_smul]
  · intro ψ hψ hψa
    have hborn : star ψ ⬝ᵥ (qubitProjector b *ᵥ ψ) = (((1 + a ⬝ᵥ b) / 2 : ℝ) : ℂ) := by
      rw [expectation_eq_trace ha hψa hψ, trace_projector_mul]
    have hAψ := pauli_mulVec_of_projector hψa
    have hsq : Real.sqrt (2 * (1 + a ⬝ᵥ b)) = 2 * Real.sqrt ((1 + a ⬝ᵥ b) / 2) := by
      rw [show 2 * (1 + a ⬝ᵥ b) = 2 ^ 2 * ((1 + a ⬝ᵥ b) / 2) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have hpos' : 0 < Real.sqrt ((1 + a ⬝ᵥ b) / 2) := Real.sqrt_pos.mpr (by linarith)
    have hne : ((Real.sqrt ((1 + a ⬝ᵥ b) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos'.ne'
    rw [shortestGate, hborn, Complex.ofReal_re, rotor, hsq, Matrix.smul_mulVec,
      Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hAψ, qubitProjector,
      Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, smul_smul]
    congr 1
    push_cast
    field_simp

/-- The Gram identity for three unit vectors: with `D = a·(b×c)`,
`D² = 1 + 2(a·b)(b·c)(c·a) − (a·b)² − (b·c)² − (c·a)²`. -/
theorem triangle_gram (a b c : Fin 3 → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1)
    (hc : c ⬝ᵥ c = 1) :
    triangleD a b c ^ 2 =
        1 + 2 * (a ⬝ᵥ b) * (b ⬝ᵥ c) * (c ⬝ᵥ a) - (a ⬝ᵥ b) ^ 2 - (b ⬝ᵥ c) ^ 2 -
          (c ⬝ᵥ a) ^ 2 := by
  have ha' := unit_coords ha
  have hb' := unit_coords hb
  have hc' := unit_coords hc
  simp only [triangleD, dotProduct, Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination
    ((b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) * (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) -
        (b 0 * c 0 + b 1 * c 1 + b 2 * c 2) ^ 2) * ha' +
      ((c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) - (c 0 * a 0 + c 1 * a 1 + c 2 * a 2) ^ 2) * hb' +
      (1 - (a 0 * b 0 + a 1 * b 1 + a 2 * b 2) ^ 2) * hc'

/-- Return phase of the gates around a Bloch triangle. For unit `a, b, c`, pairwise
non-antipodal, with `S = triangleS a b c` and `D = triangleD a b c`:
`S² + D² = 2(1 + a·b)(1 + b·c)(1 + c·a) > 0`; the
three gates compose to `(S − iD(a·σ)) / √(S² + D²)`; and the
sequential normalized projections `a → b → c → a` return a unit spinor with Bloch vector
`a` multiplied by `h(a,b,c) = (S − iD) / √(S² + D²)`. -/
theorem shortest_gate_triangle_holonomy (a b c : Fin 3 → ℝ) (ha : a ⬝ᵥ a = 1)
    (hb : b ⬝ᵥ b = 1) (hc : c ⬝ᵥ c = 1) (hab : b ≠ -a) (hbc : c ≠ -b) (hca : a ≠ -c) :
    triangleS a b c ^ 2 + triangleD a b c ^ 2 =
        2 * (1 + a ⬝ᵥ b) * (1 + b ⬝ᵥ c) * (1 + c ⬝ᵥ a) ∧
      0 < triangleS a b c ^ 2 + triangleD a b c ^ 2 ∧
      rotor c a * rotor b c * rotor a b =
        (((Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) : ℝ) : ℂ))⁻¹ •
          (((triangleS a b c : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
            (((triangleD a b c : ℝ) : ℂ) * Complex.I) • pauliCombination a) ∧
      ∀ ψ : QubitState, star ψ ⬝ᵥ ψ = 1 → qubitProjector a *ᵥ ψ = ψ →
        shortestGate a (shortestGate c (shortestGate b ψ)) =
          ((((triangleS a b c : ℝ) : ℂ) - ((triangleD a b c : ℝ) : ℂ) * Complex.I) /
              ((Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) : ℝ) : ℂ)) • ψ := by
  have pab := one_add_dot_pos ha hb hab
  have pbc := one_add_dot_pos hb hc hbc
  have pca := one_add_dot_pos hc ha hca
  have hnorm : triangleS a b c ^ 2 + triangleD a b c ^ 2 =
      2 * (1 + a ⬝ᵥ b) * (1 + b ⬝ᵥ c) * (1 + c ⬝ᵥ a) := by
    have hD := triangle_gram a b c ha hb hc
    simp only [triangleS]
    linear_combination hD
  have hQ : 0 < triangleS a b c ^ 2 + triangleD a b c ^ 2 := by
    rw [hnorm]; positivity
  have ht : 0 < Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) := Real.sqrt_pos.mpr hQ
  have hprod : Real.sqrt (2 * (1 + c ⬝ᵥ a)) * Real.sqrt (2 * (1 + b ⬝ᵥ c)) *
      Real.sqrt (2 * (1 + a ⬝ᵥ b)) = 2 * Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) := by
    rw [← Real.sqrt_mul (by linarith), ← Real.sqrt_mul (by positivity),
      show 2 * (1 + c ⬝ᵥ a) * (2 * (1 + b ⬝ᵥ c)) * (2 * (1 + a ⬝ᵥ b)) =
          2 ^ 2 * (triangleS a b c ^ 2 + triangleD a b c ^ 2) by
        linear_combination (-4) * hnorm,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hrot : rotor c a * rotor b c * rotor a b =
      (((Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) : ℝ) : ℂ))⁻¹ •
        (((triangleS a b c : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
          (((triangleD a b c : ℝ) : ℂ) * Complex.I) • pauliCombination a) := by
    simp only [rotor, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [num_triangle a b c (unit_coords ha) (unit_coords hb) (unit_coords hc)]
    have hs0 : ((Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hprodC : ((Real.sqrt (2 * (1 + c ⬝ᵥ a)) : ℝ) : ℂ) *
        ((Real.sqrt (2 * (1 + b ⬝ᵥ c)) : ℝ) : ℂ) *
        ((Real.sqrt (2 * (1 + a ⬝ᵥ b)) : ℝ) : ℂ) = 2 * ((Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) : ℝ) : ℂ) := by
      exact_mod_cast hprod
    have hscal : ((Real.sqrt (2 * (1 + a ⬝ᵥ b)) : ℝ) : ℂ)⁻¹ *
        (((Real.sqrt (2 * (1 + b ⬝ᵥ c)) : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (2 * (1 + c ⬝ᵥ a)) : ℝ) : ℂ)⁻¹) =
        (2 * ((Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) : ℝ) : ℂ))⁻¹ := by
      rw [← hprodC]; ring
    rw [hscal]
    push_cast
    module
  refine ⟨hnorm, hQ, hrot, ?_⟩
  intro ψ hψ hψa
  obtain ⟨hU1, hT1, hG1⟩ := rotor_shortest_gate a b ha hb hab
  obtain ⟨hU2, hT2, hG2⟩ := rotor_shortest_gate b c hb hc hbc
  have hG3 := (rotor_shortest_gate c a hc ha hca).2.2
  have step : ∀ (u v : Fin 3 → ℝ) (φ : QubitState),
      rotor u v * (rotor u v)ᴴ = 1 → rotor u v * pauliCombination u * (rotor u v)ᴴ =
        pauliCombination v → star φ ⬝ᵥ φ = 1 → qubitProjector u *ᵥ φ = φ →
      star (rotor u v *ᵥ φ) ⬝ᵥ (rotor u v *ᵥ φ) = 1 ∧
        qubitProjector v *ᵥ (rotor u v *ᵥ φ) = rotor u v *ᵥ φ := by
    intro u v φ hU hT hφ hφu
    have hU' : (rotor u v)ᴴ * rotor u v = 1 := mul_eq_one_comm.mp hU
    have hcomm : pauliCombination v * rotor u v = rotor u v * pauliCombination u := by
      rw [← hT, Matrix.mul_assoc, hU', Matrix.mul_one]
    constructor
    · rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU',
        Matrix.one_mulVec, hφ]
    · have hAφ := pauli_mulVec_of_projector hφu
      rw [qubitProjector, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hAφ, ← two_smul ℂ]
      rw [smul_smul]
      norm_num
  obtain ⟨u1, p1⟩ := step a b ψ hU1 hT1 hψ hψa
  obtain ⟨u2, p2⟩ := step b c _ hU2 hT2 u1 p1
  rw [← hG1 ψ hψ hψa, ← hG2 _ u1 p1, ← hG3 _ u2 p2, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hrot, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, pauli_mulVec_of_projector hψa]
  have hs0 : ((Real.sqrt (triangleS a b c ^ 2 + triangleD a b c ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [← sub_smul, smul_smul, div_eq_inv_mul]

end D5.S3.Quantum.Information.GroupInvariantPsi.ShortestGateHolonomy
