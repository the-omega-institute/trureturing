/- GID: D5/S3/Quantum/Information/SignedPauliSumNormRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SignedPauliSumNormRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SignedPauliSumNormRefutation.claim; result=D5/S3/Quantum/Information/SignedPauliSumNormRefutation.result; claim=D5/S3/Quantum/Information/SignedPauliSumNormRefutation.claim
   digest: A signed sum of the 63 three-qubit Pauli words has norm 21 > (√3+1)^3-1 (1607.02667). -/

/-
proof_shape: result: bind-only (evaluation of the definitions at one explicit sign function:
  `decide` checks that the base-4 digits of `1, …, 63` enumerate the non-identity words and,
  over the Gaussian integers, `S v = 21 v`; the ring map to `ℂ` transfers it, and
  `Matrix.l2_opNorm_mulVec` with `norm_num` and `nlinarith` compares `21` with `(√3+1)³-1`)
escape_witness: null
admission_basis: open-problem-resolution (issue #11468; Refuted)
Direct frozen dependencies: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence
  (`Pauli`, `pauliMatrix`, `tensorOp`, `wordOp`, and the `Fintype Pauli` instance),
  D5/S3/Quantum/FiniteDimensional (`qubitX`, `qubitZ`),
  D5/S3/Quantum/Measurement/HoggarSicSumNegativity (`orbitG`, the fiducial of Hoggar's lines)
-/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.Quantum.Measurement.HoggarSicSumNegativity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.SignedPauliSumNormRefutation

/-!
O. Liabøtrø, *Improved classical and quantum random access codes*, arXiv:1607.02667
(Phys. Rev. A 95, 052315 (2017)). For maximal `(4^m - 1, m, p)` quantum random access codes the
worst-case success probability is governed by the matrices
`Σ(β) = ∑_{k=1}^{4^m-1} (-1)^{β(k)} σ_{c_1(k)} ⊗ ⋯ ⊗ σ_{c_m(k)}`, the signed sums of all
non-identity Pauli words, for arbitrary signs `β`. The paper checks `m = 1, 2` exhaustively and
conjectures `‖Σ(β)‖ ≤ (√3 + 1)^m - 1` for all `m` (its Eq. (78)). The conjecture fails for
`m = 3`: for `v = (-1 + 2i, 1, 1, 1, 1, 1, 1, 1)` every non-identity word `P` has `v* P v = ±4`,
and the signs `v* P v / 4` give `Σ(β) = 2 v v* - 3`, with eigenvalue `21 > 9 + 6√3`.
-/

open Matrix D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open scoped Matrix.Norms.L2Operator

/-- The Pauli label `σ̃_c` of a base-4 digit `c`: `σ̃_0 = I`, `σ̃_1 = X`, `σ̃_2 = Y`,
`σ̃_3 = Z`. -/
def sigmaOfDigit : ℕ → Pauli
  | 0 => .I
  | 1 => .X
  | 2 => .Y
  | _ => .Z

/-- The paper's matrix `Σ(β) = ∑_{k=1}^{4^m-1} (-1)^{β(k)} σ̃_{c_1(k)} ⊗ ⋯ ⊗ σ̃_{c_m(k)}`, where
`c_i(k)` is the `i`-th base-4 digit of `k`; the qubit `i : Fin m` carries the digit
`k / 4^i % 4`. -/
noncomputable def signedPauliSum {m : ℕ} (β : ℕ → Fin 2) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  ∑ k ∈ Finset.Ico 1 (4 ^ m),
    ((-1 : ℂ) ^ (β k : ℕ)) • wordOp fun i : Fin m => sigmaOfDigit (k / 4 ^ (i : ℕ) % 4)

/-- The conjecture of arXiv:1607.02667, Eq. (78): for every number `m` of qubits and every sign
function `β`, the operator norm of `Σ(β)` is at most `(√3 + 1)^m - 1`. -/
def claim : Prop :=
  ∀ (m : ℕ) (β : ℕ → Fin 2), ‖signedPauliSum (m := m) β‖ ≤ (Real.sqrt 3 + 1) ^ m - 1

/-! The counterexample, computed over the Gaussian integers. -/

private def pauliZ : Pauli → Matrix (Fin 2) (Fin 2) GaussianInt
  | .I => !![1, 0; 0, 1]
  | .X => !![0, 1; 1, 0]
  | .Y => !![0, ⟨0, -1⟩; ⟨0, 1⟩, 0]
  | .Z => !![1, 0; 0, -1]

private def wordZ (g : Fin 3 → Pauli) : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) GaussianInt :=
  Matrix.of fun x y => ∏ i, pauliZ (g i) (x i) (y i)

/-- The fiducial `(-1 + 2i, 1, …, 1)` of Hoggar's lines, read on the three-qubit labels through the
binary expansion `x ↦ x₀ + 2 x₁ + 4 x₂`. -/
private def vZ : (Fin 3 → Fin 2) → GaussianInt :=
  fun x => D5.S3.Quantum.Measurement.HoggarSicSumNegativity.orbitG 0
    ⟨(x 0 : ℕ) + 2 * (x 1 : ℕ) + 4 * (x 2 : ℕ), by omega⟩

private def βw (g : Fin 3 → Pauli) : Fin 2 :=
  if star vZ ⬝ᵥ (wordZ g *ᵥ vZ) = 4 then 0 else 1

/-- The base-4 digit of a Pauli label, inverse to `sigmaOfDigit` on `{0, 1, 2, 3}`. -/
private def pauliDigit : Pauli → ℕ
  | .I => 0
  | .X => 1
  | .Y => 2
  | .Z => 3

private def SZ : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) GaussianInt :=
  ∑ g ∈ Finset.univ.filter (fun g : Fin 3 → Pauli => g ≠ fun _ => Pauli.I),
    ((-1 : GaussianInt) ^ (βw g : ℕ)) • wordZ g

/-- The conjecture fails for three qubits: one sign function gives `‖Σ(β)‖ ≥ 21 > (√3+1)³ - 1`. -/
theorem result : ¬ claim := by
  intro h
  -- `S v = 21 v` over the Gaussian integers.
  have heig : SZ *ᵥ vZ = (21 : GaussianInt) • vZ := by decide +kernel
  -- Transfer to `ℂ` along `GaussianInt.toComplex`.
  have hpauli : ∀ p : Pauli, pauliMatrix p = (pauliZ p).map GaussianInt.toComplex := by
    intro p
    cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliMatrix, pauliZ, qubitX, qubitZ, GaussianInt.toComplex_def]
  have hword : ∀ g : Fin 3 → Pauli, wordOp g = (wordZ g).map GaussianInt.toComplex := by
    intro g
    ext x y
    simp only [wordOp, tensorOp, wordZ, of_apply, map_apply, map_prod, hpauli]
  -- The sign function on the paper's index `k`: the sign of the word of its base-4 digits.
  set βk : ℕ → Fin 2 := fun k => βw fun i : Fin 3 => sigmaOfDigit (k / 4 ^ (i : ℕ) % 4)
    with hβk
  have hsum : signedPauliSum (m := 3) βk = SZ.map GaussianInt.toComplex := by
    have e : SZ.map GaussianInt.toComplex = GaussianInt.toComplex.mapMatrix SZ := rfl
    rw [e, SZ, map_sum, signedPauliSum]
    -- `k ↦` its base-4 digits is a bijection from `[1, 64)` onto the non-identity words.
    refine Finset.sum_nbij' (fun k => fun i : Fin 3 => sigmaOfDigit (k / 4 ^ (i : ℕ) % 4))
      (fun g => pauliDigit (g 0) + 4 * pauliDigit (g 1) + 16 * pauliDigit (g 2))
      (by decide) (by decide) (by decide) (by decide) fun k _ => ?_
    rw [RingHom.mapMatrix_apply, hword]
    ext x y
    simp [Matrix.map_apply, hβk]
  set vC : (Fin 3 → Fin 2) → ℂ := fun x => GaussianInt.toComplex (vZ x) with hvC
  have hSv : signedPauliSum (m := 3) βk *ᵥ vC = (21 : ℂ) • vC := by
    rw [hsum]
    have := congrArg (fun w => fun x => GaussianInt.toComplex (w x)) heig
    simp only [RingHom.map_mulVec] at this
    ext x
    have hx := congrFun this x
    simp only [Function.comp_def, Pi.smul_apply, smul_eq_mul, map_mul, map_ofNat] at hx
    simpa [hvC] using hx
  have hv0 : vC ≠ 0 := by
    intro h0
    have := congrFun h0 (fun _ => 1)
    rw [hvC] at this
    have h1 : vZ (fun _ => 1) = 1 := by decide
    simp only [h1, map_one, Pi.zero_apply] at this
    exact one_ne_zero this
  -- The operator norm is at least the eigenvalue `21`.
  set x := (EuclideanSpace.equiv (Fin 3 → Fin 2) ℂ).symm vC
  have hx0 : 0 < ‖x‖ := by
    rw [norm_pos_iff]
    intro hx
    apply hv0
    simpa [x] using congrArg (EuclideanSpace.equiv (Fin 3 → Fin 2) ℂ) hx
  have hle := Matrix.l2_opNorm_mulVec (signedPauliSum (m := 3) βk) x
  have hEq : (EuclideanSpace.equiv (Fin 3 → Fin 2) ℂ).symm (signedPauliSum (m := 3) βk *ᵥ x) =
      (21 : ℂ) • x := by
    simp [x, hSv]
  rw [hEq, norm_smul] at hle
  have h21 : (21 : ℝ) ≤ ‖signedPauliSum (m := 3) βk‖ := by
    have : ‖(21 : ℂ)‖ = 21 := by norm_num
    rw [this] at hle
    exact le_of_mul_le_mul_right hle hx0
  -- `(√3 + 1)³ - 1 = 9 + 6√3 < 21`.
  have hs : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hs0 := Real.sqrt_nonneg 3
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [h 3 βk, h21]

end D5.S3.Quantum.Information.SignedPauliSumNormRefutation
