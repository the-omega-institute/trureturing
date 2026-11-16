/- GID: D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.claim; result=D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.result; claim=D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation.claim
   digest: A mixed midpoint violates the triangle inequality for pure-decomposition transport. -/

import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction

/-! admission_basis: open-problem-resolution; preregistered as issue #30966.
The pure-state reduction of equation (12) is explained, not formalized, in the Scribe.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.longLine false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)

namespace D5.S3.Quantum.QuantumChannels.SeparableDecompositionTriangleRefutation

def expectation {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) : ℝ :=
  (star ψ ⬝ᵥ H *ᵥ ψ).re

def pureCost {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (ψ φ : Fin d → ℂ) : ℝ :=
  (1 / 2) * ∑ n, (expectation (H n) ψ - expectation (H n) φ) ^ 2

structure Decomposition {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) where
  K : ℕ
  p : Fin K → ℝ
  ψ : Fin K → Fin d → ℂ
  φ : Fin K → Fin d → ℂ
  nonneg : ∀ k, 0 ≤ p k
  mass : ∑ k, p k = 1
  unit_left : ∀ k, star (ψ k) ⬝ᵥ ψ k = 1
  unit_right : ∀ k, star (φ k) ⬝ᵥ φ k = 1
  left : ∑ k, (p k : ℂ) • rankOneDensity (ψ k) = ρ
  right : ∑ k, (p k : ℂ) • rankOneDensity (φ k) = σ

def costs {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) : Set ℝ :=
  {c | ∃ q : Decomposition ρ σ, c = ∑ k, q.p k * pureCost H (q.ψ k) (q.φ k)}

def decompSq {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ := sInf (costs H ρ σ)

def decomp {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ := Real.sqrt (decompSq H ρ σ)

def claim : Prop :=
  ∀ (d N : ℕ) (H : Fin N → Matrix (Fin d) (Fin d) ℂ),
    (∀ n, (H n).IsHermitian) → ∀ ρ ω τ,
    IsDensity ρ → IsDensity ω → IsDensity τ →
    decomp H ρ τ ≤ decomp H ρ ω + decomp H ω τ

private theorem costs_nonneg {d N : ℕ} (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ∀ c ∈ costs H ρ σ, 0 ≤ c := by
  rintro _ ⟨q, rfl⟩
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (q.nonneg k) (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun n _ => sq_nonneg _))

private def block (b : Fin 3) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 6) (Fin 6) ℂ := fun i j =>
  if i.val / 2 = b.val ∧ j.val / 2 = b.val then
    M ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩ ⟨j.val % 2, Nat.mod_lt _ (by omega)⟩
  else 0

private theorem block_hermitian (b : Fin 3) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h : M.IsHermitian) : (block b M).IsHermitian := by
  let F : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := fun c => if c = b then M else 0
  let f : Fin 6 → Fin 2 × Fin 3 := fun i =>
    (⟨i.val % 2, Nat.mod_lt _ (by omega)⟩, ⟨i.val / 2, by omega⟩)
  have hF : (blockDiagonal F).IsHermitian := by
    apply Matrix.isHermitian_blockDiagonal_iff.mpr
    intro c
    dsimp [F]
    split_ifs
    · exact h
    · exact Matrix.isHermitian_zero
  have he : block b M = (blockDiagonal F).submatrix f f := by
    ext i j
    simp only [block, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, F, f,
      Fin.ext_iff, Matrix.zero_apply]
    split_ifs <;> simp_all
  rw [he]
  exact hF.submatrix f

private def H : Fin 7 → Matrix (Fin 6) (Fin 6) ℂ :=
  ![block 0 (pauli 0) + block 1 (pauli 0),
    block 0 (pauli 1) + block 1 (pauli 2), block 0 (pauli 2),
    block 1 (pauli 1) + block 2 (pauli 0), block 2 (pauli 1), block 2 (pauli 2),
    diagonal ![0,0,1,1,2,2]]

private theorem H_hermitian : ∀ n, (H n).IsHermitian := by
  have hp := QubitWassersteinCouplings.pauli_hermitian
  intro n
  fin_cases n
  · exact (block_hermitian 0 _ (hp 0)).add (block_hermitian 1 _ (hp 0))
  · exact (block_hermitian 0 _ (hp 1)).add (block_hermitian 1 _ (hp 2))
  · exact block_hermitian 0 _ (hp 2)
  · exact (block_hermitian 1 _ (hp 1)).add (block_hermitian 2 _ (hp 0))
  · exact block_hermitian 2 _ (hp 1)
  · exact block_hermitian 2 _ (hp 2)
  · change (diagonal (![0,0,1,1,2,2] : Fin 6 → ℂ)).IsHermitian
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [IsSelfAdjoint]

private def ρ (b : Fin 3) : Matrix (Fin 6) (Fin 6) ℂ :=
  diagonal (fun i => if i.val / 2 = b.val then 1/2 else 0)

private theorem rho_density (b : Fin 3) : IsDensity (ρ b) := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ if i.val / 2 = b.val then 1/2 else 0
    split_ifs <;> norm_num [Complex.le_def]
  · fin_cases b <;> norm_num [ρ, Matrix.trace, Fin.sum_univ_succ]

private theorem component_zero {d K : ℕ} (p : Fin K → ℝ)
    (v : Fin K → Fin d → ℂ) (hp : ∀ k, 0 ≤ p k)
    (M : Matrix (Fin d) (Fin d) ℂ)
    (hm : ∑ k, (p k : ℂ) • rankOneDensity (v k) = M)
    (i : Fin d) (hi : M i i = 0) (k : Fin K) (hk : 0 < p k) : v k i = 0 := by
  have hm' : ∑ j, p j • rankOneDensity (v j) = M := by
    convert hm using 1
  have hz : star (Pi.single i (1 : ℂ)) ⬝ᵥ
      ((∑ j, p j • rankOneDensity (v j)) *ᵥ Pi.single i 1) = 0 := by
    rw [hm']
    simpa using hi
  have he := D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.ensemble_kernel
    v p hp (Pi.single i 1) hz k hk
  simpa using he

private theorem qubit_energy (u : Fin 2 → ℂ) (hu : star u ⬝ᵥ u = 1) :
    ∑ n : Fin 3, (expectation (pauli n) u) ^ 2 = 1 := by
  let M := rankOneDensity u
  have ht : M.trace = 1 := by
    change trace (rankOneDensity u) = 1
    rw [rankOneDensity, Matrix.trace_vecMulVec, dotProduct_comm, hu]
  have hn := (D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian
    M (Matrix.posSemidef_vecMulVec_self_star u).isHermitian).2 ht
    (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake u hu 1).1
  have he (n : Fin 3) : expectation (pauli n) u =
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch M n := by
    fin_cases n <;>
      simp [expectation, pauli, pauliMatrix, qubitX, qubitZ, M, rankOneDensity,
        D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch,
        Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Pi.star_apply,
        Fin.sum_univ_succ, Matrix.mul_apply, Complex.mul_re, Complex.mul_im,
        Complex.star_def] <;> ring
  simp_rw [he]
  rw [← EuclideanSpace.real_norm_sq_eq, hn]
  norm_num

private theorem long_cost (u v : Fin 6 → ℂ)
    (hu : star u ⬝ᵥ u = 1) (hv : star v ⬝ᵥ v = 1)
    (u2 : u 2 = 0) (u3 : u 3 = 0) (u4 : u 4 = 0) (u5 : u 5 = 0)
    (v0 : v 0 = 0) (v1 : v 1 = 0) (v2 : v 2 = 0) (v3 : v 3 = 0) :
    pureCost H u v = 3 := by
  have hua : star (![u 0, u 1]) ⬝ᵥ (![u 0, u 1]) = (1 : ℂ) := by
    simpa [dotProduct, Pi.star_apply, Fin.sum_univ_succ, u2,u3,u4,u5] using hu
  have hvc : star (![v 4, v 5]) ⬝ᵥ (![v 4, v 5]) = (1 : ℂ) := by
    simpa [dotProduct, Pi.star_apply, Fin.sum_univ_succ, v0,v1,v2,v3] using hv
  have ha := qubit_energy (![u 0, u 1]) hua
  have hc := qubit_energy (![v 4, v 5]) hvc
  have hvr := congrArg Complex.re hvc
  simp [pureCost, H, block, expectation, pauli, pauliMatrix, qubitX, qubitZ,
    Matrix.mulVec, dotProduct, Pi.star_apply, Fin.sum_univ_succ, Matrix.mul_apply,
    Matrix.diagonal, Complex.mul_re, Complex.mul_im, Complex.star_def,
    u2,u3,u4,u5,v0,v1,v2,v3] at ha hc hvr ⊢
  nlinarith [sq_nonneg ((v 4).re ^ 2 + (v 4).im ^ 2 + (v 5).re ^ 2 + (v 5).im ^ 2 - 1)]

private theorem long_decomposition (q : Decomposition (ρ 0) (ρ 2)) :
    ∑ k, q.p k * pureCost H (q.ψ k) (q.φ k) = 3 := by
  have he (k : Fin q.K) : q.p k * pureCost H (q.ψ k) (q.φ k) = q.p k * 3 := by
    by_cases hk : q.p k = 0
    · simp [hk]
    have hp : 0 < q.p k := lt_of_le_of_ne (q.nonneg k) (Ne.symm hk)
    have hl (i : Fin 6) (hi : (ρ 0) i i = 0) :=
      component_zero q.p q.ψ q.nonneg (ρ 0) q.left i hi k hp
    have hr (i : Fin 6) (hi : (ρ 2) i i = 0) :=
      component_zero q.p q.φ q.nonneg (ρ 2) q.right i hi k hp
    rw [long_cost _ _ (q.unit_left k) (q.unit_right k)
      (hl 2 (by norm_num [ρ])) (hl 3 (by norm_num [ρ]))
      (hl 4 (by norm_num [ρ])) (hl 5 (by norm_num [ρ]))
      (hr 0 (by norm_num [ρ])) (hr 1 (by norm_num [ρ]))
      (hr 2 (by norm_num [ρ])) (hr 3 (by norm_num [ρ]))]
  simp_rw [he]
  rw [← Finset.sum_mul, q.mass]
  norm_num

private def s : ℝ := Real.sqrt (1/2)
private def sign (k : Fin 2) : ℝ := if k = 0 then 1 else -1
private def ket (a : Fin 4) (k : Fin 2) : Fin 6 → ℂ :=
  ![![(s : ℂ), (sign k * s : ℝ), 0,0,0,0],
    ![0,0,(s : ℂ),(sign k * s : ℝ),0,0],
    ![0,0,(s : ℂ),(sign k * s : ℝ) * Complex.I,0,0],
    ![0,0,0,0,(s : ℂ),(sign k * s : ℝ)]] a
private def sector : Fin 4 → Fin 3 := ![0,1,1,2]

private theorem s_sq : s ^ 2 = 1/2 := Real.sq_sqrt (by norm_num)

private theorem ket_unit (a : Fin 4) (k : Fin 2) : star (ket a k) ⬝ᵥ ket a k = 1 := by
  have hs := s_sq
  fin_cases a <;> fin_cases k <;> apply Complex.ext <;>
    norm_num [ket, sign, dotProduct, Pi.star_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;> nlinarith

private theorem ket_ensemble (a : Fin 4) :
    ∑ k : Fin 2, (1/2 : ℂ) • rankOneDensity (ket a k) = ρ (sector a) := by
  have hs := s_sq
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply]
  fin_cases a <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [ket, sector, sign, ρ, Fin.sum_univ_succ, Matrix.diagonal,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;> nlinarith

private def readings (a : Fin 4) (k : Fin 2) : Fin 7 → ℝ :=
  ![![sign k,0,0,0,0,0,0], ![sign k,0,0,0,0,0,1],
    ![0,0,0,sign k,0,0,1], ![0,0,0,sign k,0,0,2]] a

private theorem ket_readings (a : Fin 4) (k : Fin 2) (n : Fin 7) :
    expectation (H n) (ket a k) = readings a k n := by
  have hs := s_sq
  fin_cases a <;> fin_cases k <;> fin_cases n <;>
    norm_num [expectation, H, block, ket, readings, sign, pauli, pauliMatrix,
      qubitX, qubitZ, Matrix.mulVec, dotProduct, Pi.star_apply, Fin.sum_univ_succ,
      Matrix.mul_apply, Matrix.diagonal, Complex.mul_re, Complex.mul_im,
      Complex.star_def] <;> nlinarith

private def plan (a b : Fin 4) : Decomposition (ρ (sector a)) (ρ (sector b)) where
  K := 2
  p := fun _ => 1/2
  ψ := ket a
  φ := ket b
  nonneg := by intro k; norm_num
  mass := by norm_num [Fin.sum_univ_succ]
  unit_left := ket_unit a
  unit_right := ket_unit b
  left := by simpa using ket_ensemble a
  right := by simpa using ket_ensemble b

private theorem plan_cost (a b : Fin 4) :
    ∑ k, (plan a b).p k * pureCost H ((plan a b).ψ k) ((plan a b).φ k) =
      (1/2) * ∑ k : Fin 2, ((1/2) * ∑ n : Fin 7, (readings a k n - readings b k n)^2) := by
  change (∑ k : Fin 2, (1/2 : ℝ) * pureCost H (ket a k) (ket b k)) = _
  simp only [pureCost, ket_readings]
  exact (Finset.mul_sum _ _ _).symm

private theorem short_ab : decompSq H (ρ 0) (ρ 1) ≤ 1/2 := by
  apply le_trans (csInf_le ⟨0, costs_nonneg H _ _⟩
    (show (∑ k, (plan 0 1).p k * pureCost H ((plan 0 1).ψ k) ((plan 0 1).φ k)) ∈
      costs H (ρ 0) (ρ 1) from ⟨plan 0 1, rfl⟩))
  rw [plan_cost]
  norm_num [readings, sign, Fin.sum_univ_succ]

private theorem short_bc : decompSq H (ρ 1) (ρ 2) ≤ 1/2 := by
  apply le_trans (csInf_le ⟨0, costs_nonneg H _ _⟩
    (show (∑ k, (plan 2 3).p k * pureCost H ((plan 2 3).ψ k) ((plan 2 3).φ k)) ∈
      costs H (ρ 1) (ρ 2) from ⟨plan 2 3, rfl⟩))
  rw [plan_cost]
  norm_num [readings, sign, Fin.sum_univ_succ]

private theorem long_eq : decompSq H (ρ 0) (ρ 2) = 3 := by
  have hmem : (3 : ℝ) ∈ costs H (ρ 0) (ρ 2) :=
    ⟨plan 0 3, (long_decomposition (plan 0 3)).symm⟩
  apply le_antisymm
  · exact csInf_le ⟨0, costs_nonneg H _ _⟩ hmem
  · apply le_csInf ⟨3, hmem⟩
    rintro c ⟨q, rfl⟩
    exact le_of_eq (long_decomposition q).symm

theorem result : ¬ claim := by
  intro h
  have ht := h 6 7 H H_hermitian (ρ 0) (ρ 1) (ρ 2)
    (rho_density 0) (rho_density 1) (rho_density 2)
  have ha := Real.sqrt_le_sqrt short_ab
  have hb := Real.sqrt_le_sqrt short_bc
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)
  have hl := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  change Real.sqrt (decompSq H (ρ 0) (ρ 2)) ≤
    Real.sqrt (decompSq H (ρ 0) (ρ 1)) + Real.sqrt (decompSq H (ρ 1) (ρ 2)) at ht
  rw [long_eq] at ht
  have hle : Real.sqrt 3 ≤ 2 * Real.sqrt (1/2) := by linarith
  nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (1/2)]

#print axioms result
end D5.S3.Quantum.QuantumChannels.SeparableDecompositionTriangleRefutation
