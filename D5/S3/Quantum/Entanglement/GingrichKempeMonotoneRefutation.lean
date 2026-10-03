/- GID: D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.claim; result=D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.result; claim=D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.claim
   digest: A diagonal measurement on one qubit raises Gingrich's sigma_ABC on average. -/

/-
proof_shape: polyInvariant, sigmaABC: definition (the paper's polynomial invariants, Eq. (8), and
  its proposed monotone 3 - (I_1 + I_2 + I_3) I_4)
proof_shape: claim: definition (published proposal, arXiv:quant-ph/0106042, read for every
  normalized three-qubit vector and every local instrument on qubit A)
proof_shape: psi, instrument: definition (the counterexample state and measurement)
proof_shape: w3, threeEquiv, tripleEquiv: private definition (three-qubit vectors supported on
  000, 011, 110, and coordinate equivalences of the index sets)
proof_shape: result: bind-only (as local steps: the expansion of Eq. (8) on vectors supported on
  000, 011, 110, the coordinate form of the frozen localOp on qubit A, the action of a diagonal
  operator and of scalars on such vectors, and rational evaluation of the squared amplitudes)
escape_witness: none (the settlement of the external named proposal is the new content)
admission_basis: open-problem-resolution (issue #12508; Refuted)
Direct frozen dependencies (GID, statement_id):
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.localOp
    sha256:a8376a57b9d3e52109fea12f73db0ab84164e4cb061792f870b54843e0dedb67
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.tensorOp
    sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
-/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.GingrichKempeMonotoneRefutation

/-!
R. M. Gingrich, *Properties of entanglement monotones for three-qubit pure states*,
arXiv:quant-ph/0106042 (Phys. Rev. A 65 (2002) 052302), writes a three-qubit state as
`∑ t_{ijk} |ijk⟩` and uses the polynomial invariants `P_{σ,τ}` of Eq. (8), the sums over
`n` index triples `(i_r, j_r, k_r)` of `∏ r, t_{i_r j_r k_r} t̄_{i_r j_{σ(r)} k_{τ(r)}}`,
with `I_1 = P_{e,(12)}`, `I_2 = P_{(12),e}`, `I_3 = P_{(12),(12)}` and the Kempe invariant
`I_4 = P_{(123),(132)}`. He proposes `σ_ABC = 3 - (I_1 + I_2 + I_3) I_4` as a fifth entanglement
monotone, reports that numerical results suggest it is one and assumes it for the rest of the
paper. It is not. For `ψ = (5|000⟩ + 5|011⟩ + 2|110⟩)/(3√6)` and the measurement
`K₀ = diag(3/5, 0)`, `K₁ = diag(4/5, 1)` on qubit A, the outcomes are
`(|000⟩ + |011⟩)/√2` with probability `1/3` and `(2|000⟩ + 2|011⟩ + |110⟩)/3` with probability
`2/3`. On a vector `a|000⟩ + b|011⟩ + c|110⟩` the invariants are `I_1 = (x + z)² + y²`,
`I_2 = x² + (y + z)²`, `I_3 = (x + y)² + z²` and `I_4 = x³ + y³ + z³ + 3xyz`, with `x = |a|²`,
`y = |b|²`, `z = |c|²`; hence `σ_ABC(ψ) = 8097475/3188646`, the outcomes have `5/2` and
`16792/6561`, and the average after the measurement exceeds `σ_ABC(ψ)` by `169/1594323`.
-/

open Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (localOp tensorOp)

/-- The polynomial invariant `P_{σ,τ}` of Eq. (8), for a three-qubit vector `ψ` with amplitudes
`t_{ijk} = ψ ![i, j, k]`: the sum over the `n` index triples `x r = (i_r, j_r, k_r)` of
`∏ r, t_{i_r j_r k_r} t̄_{i_r j_{σ r} k_{τ r}}`. -/
noncomputable def polyInvariant {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (ψ : (Fin 3 → Fin 2) → ℂ) : ℂ :=
  ∑ x : Fin n → (Fin 3 → Fin 2), ∏ r, ψ (x r) * star (ψ ![x r 0, x (σ r) 1, x (τ r) 2])

/-- Gingrich's proposed monotone `σ_ABC = 3 - (I_1 + I_2 + I_3) I_4`, with `I_1 = P_{e,(12)}`,
`I_2 = P_{(12),e}`, `I_3 = P_{(12),(12)}` and `I_4 = P_{(123),(132)}`; `finRotate 3` is the cycle
`(123)` and its inverse is `(132)`. -/
noncomputable def sigmaABC (ψ : (Fin 3 → Fin 2) → ℂ) : ℂ :=
  3 - (polyInvariant 1 (Equiv.swap (0 : Fin 2) 1) ψ + polyInvariant (Equiv.swap (0 : Fin 2) 1) 1 ψ +
      polyInvariant (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1) ψ) *
    polyInvariant (finRotate 3) (finRotate 3).symm ψ

/-- `σ_ABC` does not increase on average under any complete instrument on qubit `A`, the
defining inequality of an entanglement monotone in the paper; outcomes of probability zero are
omitted. -/
def claim : Prop :=
  ∀ ψ : (Fin 3 → Fin 2) → ℂ, ∑ w, ‖ψ w‖ ^ 2 = 1 →
    ∀ (n : ℕ) (K : Fin n → Matrix (Fin 2) (Fin 2) ℂ), ∑ k, (K k)ᴴ * K k = 1 →
      ∑ k, (if ∑ w, ‖(localOp (0 : Fin 3) (K k) *ᵥ ψ) w‖ ^ 2 = 0 then 0 else
        (∑ w, ‖(localOp (0 : Fin 3) (K k) *ᵥ ψ) w‖ ^ 2) *
          (sigmaABC (((Real.sqrt (∑ w, ‖(localOp (0 : Fin 3) (K k) *ᵥ ψ) w‖ ^ 2))⁻¹ : ℂ) •
            (localOp (0 : Fin 3) (K k) *ᵥ ψ))).re) ≤
        (sigmaABC ψ).re

/-- The counterexample state `(5|000⟩ + 5|011⟩ + 2|110⟩)/(3√6)`. -/
noncomputable def psi : (Fin 3 → Fin 2) → ℂ := fun w =>
  if (w 0, w 1, w 2) = (0, 0, 0) then ((5 / (3 * Real.sqrt 6) : ℝ) : ℂ)
  else if (w 0, w 1, w 2) = (0, 1, 1) then ((5 / (3 * Real.sqrt 6) : ℝ) : ℂ)
  else if (w 0, w 1, w 2) = (1, 1, 0) then ((2 / (3 * Real.sqrt 6) : ℝ) : ℂ) else 0

/-- The measurement `K₀ = diag(3/5, 0)`, `K₁ = diag(4/5, 1)` on qubit `A`. -/
noncomputable def instrument : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![3 / 5, 0; 0, 0], !![4 / 5, 0; 0, 1]]

/-- The vector `a|000⟩ + b|011⟩ + c|110⟩`. -/
private def w3 (a b c : ℂ) : (Fin 3 → Fin 2) → ℂ := fun w =>
  if (w 0, w 1, w 2) = (0, 0, 0) then a else if (w 0, w 1, w 2) = (0, 1, 1) then b
  else if (w 0, w 1, w 2) = (1, 1, 0) then c else 0

/-- The configurations of three qubits as `Fin 2 × Fin 2 × Fin 2`. -/
private def threeEquiv : (Fin 3 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 where
  toFun w := (w 0, w 1, w 2)
  invFun x := ![x.1, x.2.1, x.2.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

/-- Triples of three-qubit configurations as a product. -/
private def tripleEquiv :
    (Fin 3 → (Fin 3 → Fin 2)) ≃ (Fin 3 → Fin 2) × (Fin 3 → Fin 2) × (Fin 3 → Fin 2) where
  toFun x := (x 0, x 1, x 2)
  invFun y := ![y.1, y.2.1, y.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

set_option maxHeartbeats 8000000 in -- the explicit invariant expansions share this declaration
/-- The proposal fails for `psi` and `instrument`. -/
theorem result : ¬ claim := by
  intro h
  have hsum3 : ∀ f : (Fin 3 → Fin 2) → ℂ, ∑ w, f w = ∑ a, ∑ b, ∑ c, f ![a, b, c] := by
    intro f
    rw [← Equiv.sum_comp threeEquiv.symm]
    simp only [Fintype.sum_prod_type]
    rfl
  have hsum3R : ∀ f : (Fin 3 → Fin 2) → ℝ, ∑ w, f w = ∑ a, ∑ b, ∑ c, f ![a, b, c] := by
    intro f
    rw [← Equiv.sum_comp threeEquiv.symm]
    simp only [Fintype.sum_prod_type]
    rfl
  have hpi2 : ∀ g : (Fin 2 → (Fin 3 → Fin 2)) → ℂ, ∑ x, g x = ∑ y, ∑ z, g ![y, z] := by
    intro g
    rw [← Equiv.sum_comp (finTwoArrowEquiv _).symm, Fintype.sum_prod_type]
    rfl
  have hpi3 : ∀ g : (Fin 3 → (Fin 3 → Fin 2)) → ℂ, ∑ x, g x = ∑ y, ∑ z, ∑ v, g ![y, z, v] := by
    intro g
    rw [← Equiv.sum_comp tripleEquiv.symm]
    simp only [Fintype.sum_prod_type]
    rfl
  have hI1 : ∀ a b c : ℂ, polyInvariant 1 (Equiv.swap (0 : Fin 2) 1) (w3 a b c) =
      (a * star a + c * star c) ^ 2 + (b * star b) ^ 2 := by
    intro a b c
    simp only [polyInvariant]
    rw [hpi2]
    simp only [hsum3, Fin.sum_univ_two, Fin.prod_univ_two]
    simp [w3]
    ring
  have hI2 : ∀ a b c : ℂ, polyInvariant (Equiv.swap (0 : Fin 2) 1) 1 (w3 a b c) =
      (a * star a) ^ 2 + (b * star b + c * star c) ^ 2 := by
    intro a b c
    simp only [polyInvariant]
    rw [hpi2]
    simp only [hsum3, Fin.sum_univ_two, Fin.prod_univ_two]
    simp [w3]
    ring
  have hI3 : ∀ a b c : ℂ,
      polyInvariant (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1) (w3 a b c) =
        (a * star a + b * star b) ^ 2 + (c * star c) ^ 2 := by
    intro a b c
    simp only [polyInvariant]
    rw [hpi2]
    simp only [hsum3, Fin.sum_univ_two, Fin.prod_univ_two]
    simp [w3]
    ring
  have r0 : finRotate 3 0 = 1 := by decide
  have r1 : finRotate 3 1 = 2 := by decide
  have r2 : finRotate 3 2 = 0 := by decide
  have s0 : (finRotate 3).symm 0 = 2 := by decide
  have s1 : (finRotate 3).symm 1 = 0 := by decide
  have s2 : (finRotate 3).symm 2 = 1 := by decide
  have hI4 : ∀ a b c : ℂ, polyInvariant (finRotate 3) (finRotate 3).symm (w3 a b c) =
      (a * star a) ^ 3 + (b * star b) ^ 3 + (c * star c) ^ 3 +
        3 * (a * star a) * (b * star b) * (c * star c) := by
    intro a b c
    simp only [polyInvariant]
    rw [hpi3]
    simp only [hsum3, Fin.sum_univ_two, Fin.prod_univ_three, r0, r1, r2, s0, s1, s2]
    simp [w3]
    ring
  -- the value of σ_ABC on a real three-term state, in terms of the squared amplitudes
  have hσ : ∀ x y z : ℝ, sigmaABC (w3 x y z) =
      ((3 - (((x ^ 2 + z ^ 2) ^ 2 + (y ^ 2) ^ 2) + ((x ^ 2) ^ 2 + (y ^ 2 + z ^ 2) ^ 2) +
        ((x ^ 2 + y ^ 2) ^ 2 + (z ^ 2) ^ 2)) *
        ((x ^ 2) ^ 3 + (y ^ 2) ^ 3 + (z ^ 2) ^ 3 + 3 * x ^ 2 * y ^ 2 * z ^ 2) : ℝ) : ℂ) := by
    intro x y z
    simp only [sigmaABC, hI1, hI2, hI3, hI4, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  have hupd : ∀ x0 x1 x2 a : Fin 2, Function.update ![x0, x1, x2] 0 a = ![a, x1, x2] := by
    intro x0 x1 x2 a
    funext i
    fin_cases i <;> rfl
  have hloc : ∀ (K : Matrix (Fin 2) (Fin 2) ℂ) (ψ : (Fin 3 → Fin 2) → ℂ) (w : Fin 3 → Fin 2),
      (localOp (0 : Fin 3) K *ᵥ ψ) w = ∑ a, K (w 0) a * ψ (Function.update w 0 a) := by
    intro K ψ w
    obtain ⟨⟨x0, x1, x2⟩, rfl⟩ : ∃ x : Fin 2 × Fin 2 × Fin 2, ![x.1, x.2.1, x.2.2] = w :=
      ⟨(w 0, w 1, w 2), by funext i; fin_cases i <;> rfl⟩
    simp only [Matrix.mulVec, dotProduct, localOp, tensorOp, Matrix.of_apply, hupd]
    rw [hsum3]
    fin_cases x1 <;> fin_cases x2 <;>
      simp [Fin.prod_univ_three, Fin.sum_univ_two, Function.update_apply, Matrix.one_apply]
  have hdiag : ∀ (k0 k1 : ℂ) (a b c : ℂ),
      localOp (0 : Fin 3) !![k0, 0; 0, k1] *ᵥ w3 a b c = w3 (k0 * a) (k0 * b) (k1 * c) := by
    intro k0 k1 a b c
    funext w
    rw [hloc]
    obtain ⟨⟨x0, x1, x2⟩, rfl⟩ : ∃ x : Fin 2 × Fin 2 × Fin 2, ![x.1, x.2.1, x.2.2] = w :=
      ⟨(w 0, w 1, w 2), by funext i; fin_cases i <;> rfl⟩
    fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;>
      simp [w3]
  have hsmul : ∀ (s : ℂ) (a b c : ℂ), s • w3 a b c = w3 (s * a) (s * b) (s * c) := by
    intro s a b c
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, w3]
    split_ifs <;> simp
  have hnormsq : ∀ a b c : ℂ, ∑ w, ‖w3 a b c w‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 := by
    intro a b c
    rw [hsum3R]
    simp [w3, Fin.sum_univ_two]
  have hpsi : psi = w3 ((5 / (3 * Real.sqrt 6) : ℝ) : ℂ) ((5 / (3 * Real.sqrt 6) : ℝ) : ℂ)
      ((2 / (3 * Real.sqrt 6) : ℝ) : ℂ) := rfl
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h6p : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hsmulR : ∀ s x y z : ℝ, ((s : ℂ))⁻¹ • w3 (x : ℂ) (y : ℂ) (z : ℂ) =
      w3 ((s⁻¹ * x : ℝ) : ℂ) ((s⁻¹ * y : ℝ) : ℂ) ((s⁻¹ * z : ℝ) : ℂ) := by
    intro s x y z
    rw [hsmul]
    push_cast
    rfl
  have hnormR : ∀ x y z : ℝ, ∑ w, ‖w3 (x : ℂ) (y : ℂ) (z : ℂ) w‖ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
    intro x y z
    rw [hnormsq]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have ea : (5 / (3 * Real.sqrt 6)) ^ 2 = 25 / 54 := by
    rw [div_pow, mul_pow, h6]; norm_num
  have ec : (2 / (3 * Real.sqrt 6)) ^ 2 = 2 / 27 := by
    rw [div_pow, mul_pow, h6]; norm_num
  have hnorm : ∑ w, ‖psi w‖ ^ 2 = 1 := by
    rw [hpsi, hnormR, ea, ec]; norm_num
  have hK : ∑ k, (instrument k)ᴴ * instrument k = 1 := by
    simp only [Fin.sum_univ_two, instrument]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat, map_div₀]
  have hout0 : localOp (0 : Fin 3) (instrument 0) *ᵥ psi =
      w3 ((3 / 5 * (5 / (3 * Real.sqrt 6)) : ℝ) : ℂ) ((3 / 5 * (5 / (3 * Real.sqrt 6)) : ℝ) : ℂ)
        ((0 * (2 / (3 * Real.sqrt 6)) : ℝ) : ℂ) := by
    rw [hpsi, show instrument 0 = !![(3 / 5 : ℂ), 0; 0, 0] from rfl, hdiag]
    push_cast
    rfl
  have hout1 : localOp (0 : Fin 3) (instrument 1) *ᵥ psi =
      w3 ((4 / 5 * (5 / (3 * Real.sqrt 6)) : ℝ) : ℂ) ((4 / 5 * (5 / (3 * Real.sqrt 6)) : ℝ) : ℂ)
        ((1 * (2 / (3 * Real.sqrt 6)) : ℝ) : ℂ) := by
    rw [hpsi, show instrument 1 = !![(4 / 5 : ℂ), 0; 0, 1] from rfl, hdiag]
    push_cast
    rfl
  have hp0 : ∑ w, ‖(localOp (0 : Fin 3) (instrument 0) *ᵥ psi) w‖ ^ 2 = 1 / 3 := by
    rw [hout0, hnormR, mul_pow, ea]; norm_num
  have hp1 : ∑ w, ‖(localOp (0 : Fin 3) (instrument 1) *ᵥ psi) w‖ ^ 2 = 2 / 3 := by
    rw [hout1, hnormR, mul_pow, mul_pow, ea, ec]; norm_num
  have e0 : ((Real.sqrt (1 / 3))⁻¹ * (3 / 5 * (5 / (3 * Real.sqrt 6)))) ^ 2 = 1 / 2 := by
    rw [mul_pow, mul_pow, ea, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have e0z : ((Real.sqrt (1 / 3))⁻¹ * (0 * (2 / (3 * Real.sqrt 6)))) ^ 2 = 0 := by
    simp
  have e1 : ((Real.sqrt (2 / 3))⁻¹ * (4 / 5 * (5 / (3 * Real.sqrt 6)))) ^ 2 = 4 / 9 := by
    rw [mul_pow, mul_pow, ea, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have e1z : ((Real.sqrt (2 / 3))⁻¹ * (1 * (2 / (3 * Real.sqrt 6)))) ^ 2 = 1 / 9 := by
    rw [mul_pow, mul_pow, ec, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have key := h psi hnorm 2 instrument hK
  rw [Fin.sum_univ_two, hp0, hp1, if_neg (by norm_num), if_neg (by norm_num), hout0, hout1,
    hsmulR, hsmulR, hσ, hσ, hpsi, hσ] at key
  simp only [Complex.ofReal_re] at key
  rw [e0, e0z, e1, e1z, ea, ec] at key
  norm_num at key

end D5.S3.Quantum.Entanglement.GingrichKempeMonotoneRefutation
