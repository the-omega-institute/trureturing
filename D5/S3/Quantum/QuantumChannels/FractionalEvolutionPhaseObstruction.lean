/- GID: D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.claim; result=D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.result; claim=D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.claim
   digest: Ordinary oracle circuits cannot implement the prescribed fractional branch uniformly. -/

import D5.S3.Quantum.QuantumChannels.HarrowParallelChernoffExponentRefutation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Definitions 1--3 and Appendix B of arXiv:2610.01940v1, with the Section V
uncontrolled-access substitution. The result refutes the uniform ordinary-query upper bound.
`true` denotes sigma = -1 and `false` denotes sigma = +1.
-/

noncomputable section

namespace Trureturing.OpenProblems.FractionalEvolutionPhase

open Matrix
open scoped Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (conj)
open D5.S3.Quantum.QuantumChannels.HarrowParallelChernoffExponentRefutation (diamondNorm)

/-- U^sigma for sigma in {-1,+1}; The unitary-oracle promise makes adjoint the inverse. -/
def query {d : ℕ} (negative : Bool) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  if negative then U.conjTranspose else U

/-- Definition 1's controlled query, with control 0 activating the call. -/
def controlledQuery {d : ℕ} (negative : Bool) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  fun p q => if p.1 = q.1 then
    if p.1 = 0 then query negative U p.2 q.2 else (1 : Matrix (Fin d) (Fin d) ℂ) p.2 q.2
  else 0

/-- Definition 1's fixed inter-query unitaries and signs; m+1 is the finite workspace dimension. -/
structure Circuit (d m N : ℕ) where
  W : Fin (N + 1) → Matrix.unitaryGroup (Fin (m + 1) × Fin d) ℂ
  negative : Fin N → Bool

/-- Section V: every slot uses ordinary U or U-adjoint, with identity on the workspace. -/
def run {d m N : ℕ} (A : Circuit d m N) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (m + 1) × Fin d) (Fin (m + 1) × Fin d) ℂ :=
  (List.ofFn (fun j : Fin N => j)).foldl
    (fun acc j => (A.W j.succ).val *
      ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) U) * acc)
    (A.W 0).val

/-- Appendix B's fixed initialization isometry J|psi> = |0> tensor |psi>. -/
def initialization (d m : ℕ) : Matrix (Fin (m + 1) × Fin d) (Fin d) ℂ :=
  fun p j => if p.1 = 0 ∧ p.2 = j then 1 else 0

/-- Definition 3 with its literal Appendix B isometric embedding: compare A_U J and J U^t.
The existing diamondNorm is unhalved, reference stabilized, and valued in ENNReal.
All oracles and logarithms are quantified; the spectral branch is the half-open [delta, 2*pi).
-/
def Successful {d m N : ℕ} (A : Circuit d m N) (t δ ε : ℝ) : Prop :=
  ∀ (U H : Matrix (Fin d) (Fin d) ℂ),
    U = NormedSpace.exp (Complex.I • H) →
    H.IsHermitian →
    (∀ x : ℝ, x ∈ spectrum ℝ H → δ ≤ x ∧ x < 2 * Real.pi) →
    diamondNorm
      (conj (run A U * initialization d m) -
        conj (initialization d m * NormedSpace.exp (((t : ℂ) * Complex.I) • H))) ≤
      ENNReal.ofReal ε

/-- Positive answer to the unnumbered Section V uncontrolled-access question:
Theorem 1's uniform O(delta^-1 log(1/epsilon)) upper bound with ordinary queries.
The universal constant is independent of the dimension and of t, delta, epsilon.
-/
def claim : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (t δ ε : ℝ), 0 < t → t < 1 → 0 < δ → δ < 1 → 0 < ε → ε < 1 / 2 →
      ∀ d : ℕ, 0 < d →
        ∃ (m N : ℕ) (A : Circuit d m N),
          (N : ℝ) ≤ C * (δ⁻¹ * Real.log (ε⁻¹)) ∧ Successful A t δ ε


private theorem query_neg {d : ℕ} (negative : Bool) (U : Matrix (Fin d) (Fin d) ℂ) :
    query negative (-U) = -query negative U := by
  cases negative <;> simp [query]

private theorem fold_neg {d m N : ℕ} (A : Circuit d m N)
    (U : Matrix (Fin d) (Fin d) ℂ) (L : List (Fin N))
    (B : Matrix (Fin (m + 1) × Fin d) (Fin (m + 1) × Fin d) ℂ) :
    L.foldl (fun acc j => (A.W j.succ).val *
      ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) (-U)) * acc) B =
    ((-1 : ℂ) ^ L.length) • L.foldl (fun acc j => (A.W j.succ).val *
      ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) U) * acc) B := by
  induction L generalizing B with
  | nil => simp
  | cons j L ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    have hq (j : Fin N) :
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) (-U) =
        -((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) U) := by
      rw [query_neg]
      ext p q
      simp [Matrix.kroneckerMap_apply]
    simp only [hq, Matrix.mul_neg, Matrix.neg_mul]
    have hs : ∀ (L : List (Fin N)) (z : ℂ) B,
        L.foldl (fun acc j => (A.W j.succ).val *
          ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) U) * acc) (z • B) =
        z • L.foldl (fun acc j => (A.W j.succ).val *
          ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) U) * acc) B := by
      intro K z B
      exact List.foldl_hom (fun B => z • B) (by
        intro X j
        simp only [Matrix.mul_smul])
    rw [show -(↑(A.W j.succ) * (1 ⊗ₖ query (A.negative j) U) * B) =
      (-1 : ℂ) • (↑(A.W j.succ) * (1 ⊗ₖ query (A.negative j) U) * B) by simp,
      hs, smul_smul, pow_succ]

private theorem run_neg {d m N : ℕ} (A : Circuit d m N)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    run A (-U) = ((-1 : ℂ) ^ N) • run A U := by
  simpa [run] using fold_neg A U (List.ofFn (fun j : Fin N => j)) (A.W 0).val

private theorem channel_neg {d m N : ℕ} (A : Circuit d m N)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    conj (run A (-U) * initialization d m) = conj (run A U * initialization d m) := by
  rw [run_neg, Matrix.smul_mul]
  apply LinearMap.ext
  intro X
  change (((-1 : ℂ) ^ N) • (run A U * initialization d m)) * X *
    (((-1 : ℂ) ^ N) • (run A U * initialization d m))ᴴ = _
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ]
  norm_num
  simp [← mul_pow]


private def logarithm (swapped : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun j => ((if (j = 0) = (!swapped) then Real.pi / 2 else
    3 * Real.pi / 2 : ℝ) : ℂ))

private def oracle : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun j => if j = 0 then Complex.I else -Complex.I)

private theorem logarithm_admissible (swapped : Bool) :
    (logarithm swapped).IsHermitian ∧
    ∀ x : ℝ, x ∈ spectrum ℝ (logarithm swapped) → 1 / 2 ≤ x ∧ x < 2 * Real.pi := by
  constructor
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro j
    simp [isSelfAdjoint_iff]
  · intro x hx
    rw [← spectrum.algebraMap_mem_iff ℂ, logarithm, spectrum_diagonal] at hx
    obtain ⟨j, hj⟩ := hx
    have hr := congrArg Complex.re hj
    simp only [Complex.ofReal_re, Algebra.algebraMap_eq_smul_one, Complex.real_smul,
      mul_one] at hr
    have hp := Real.pi_gt_three
    split_ifs at hr <;> constructor <;> linarith

private theorem logarithm_exp (swapped : Bool) :
    NormedSpace.exp (Complex.I • logarithm swapped) =
      if swapped then -oracle else oracle := by
  have h3 : Complex.exp ((3 * (Real.pi : ℂ) / 2) * Complex.I) = -Complex.I := by
    have he : 3 * (Real.pi : ℂ) / 2 * Complex.I =
        (Real.pi : ℂ) / 2 * Complex.I + (Real.pi : ℂ) * Complex.I := by ring
    rw [he, Complex.exp_add, Complex.exp_pi_div_two_mul_I, Complex.exp_pi_mul_I]
    ring
  rw [logarithm, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> cases swapped <;>
    simp [oracle, Pi.smul_apply, smul_eq_mul,
      ← Complex.exp_eq_exp_ℂ, mul_comm Complex.I, Complex.exp_pi_div_two_mul_I, h3]


open scoped ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (kron kron_def)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_add_le
  traceNorm_neg traceNorm_sub_orthogonal)

private def inputVector : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.2 = 0 then 1 else 0

private def inputDensity : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℝ) • Matrix.vecMulVec inputVector (star inputVector)

private theorem input_density : inputDensity.PosSemidef ∧ inputDensity.trace = 1 := by
  constructor
  · exact (Matrix.posSemidef_vecMulVec_self_star inputVector).smul (by norm_num)
  · norm_num [inputDensity, inputVector, Matrix.trace, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.vecMulVec, Pi.star_apply]

private def outputVector (m : ℕ) (swapped : Bool) : (Fin (m + 1) × Fin 2) × Fin 2 → ℂ :=
  fun p => if p.1.1 = 0 ∧ p.2 = 0 then
    if p.1.2 = 0 then 1 else if swapped then -Complex.I else Complex.I
    else 0

private def outputDensity (m : ℕ) (swapped : Bool) :
    Matrix ((Fin (m + 1) × Fin 2) × Fin 2) ((Fin (m + 1) × Fin 2) × Fin 2) ℂ :=
  (1 / 2 : ℝ) • Matrix.vecMulVec (outputVector m swapped) (star (outputVector m swapped))

private theorem output_density (m : ℕ) (swapped : Bool) :
    (outputDensity m swapped).PosSemidef ∧ (outputDensity m swapped).trace = 1 := by
  constructor
  · exact (Matrix.posSemidef_vecMulVec_self_star (outputVector m swapped)).smul (by norm_num)
  · cases swapped <;> simp [outputDensity, outputVector, Matrix.trace, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.vecMulVec, Pi.star_apply] <;> norm_num

private theorem output_orthogonal (m : ℕ) :
    outputDensity m false * outputDensity m true = 0 := by
  ext p q
  simp [outputDensity, outputVector, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.vecMulVec, Pi.star_apply]
  split_ifs <;> simp_all <;> ring_nf <;> simp

private theorem output_separation (m : ℕ) :
    traceNorm (outputDensity m false - outputDensity m true) = 2 := by
  rw [traceNorm_sub_orthogonal _ _ (output_density m false).1
    (output_density m true).1 (output_orthogonal m),
    (output_density m false).2, (output_density m true).2]
  norm_num


private def halfDiagonal (swapped : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun j => if j = 0 then (if swapped then Complex.I else 1)
    else if swapped then 1 else Complex.I)

private def commonPhase : ℂ := Complex.exp ((Real.pi : ℂ) / 4 * Complex.I)

private theorem half_exp (swapped : Bool) :
    NormedSpace.exp ((((1 / 2 : ℝ) : ℂ) * Complex.I) • logarithm swapped) =
      commonPhase • halfDiagonal swapped := by
  have h3 : Complex.exp ((3 * (Real.pi : ℂ) / 4) * Complex.I) = commonPhase * Complex.I := by
    have he : 3 * (Real.pi : ℂ) / 4 * Complex.I =
        (Real.pi : ℂ) / 4 * Complex.I + (Real.pi : ℂ) / 2 * Complex.I := by ring
    rw [he, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
    rfl
  have hsmall : NormedSpace.exp (((1 / 2 : ℝ) : ℂ) * Complex.I *
      ((Real.pi / 2 : ℝ) : ℂ)) = commonPhase := by
    rw [← Complex.exp_eq_exp_ℂ]
    congr 1
    push_cast
    ring
  have hlarge : NormedSpace.exp (((1 / 2 : ℝ) : ℂ) * Complex.I *
      ((3 * Real.pi / 2 : ℝ) : ℂ)) = commonPhase * Complex.I := by
    rw [← Complex.exp_eq_exp_ℂ]
    convert h3 using 1 <;> congr 1 <;> push_cast <;> ring
  have hs' : NormedSpace.exp ((Real.pi : ℂ) / 2 * (Complex.I * 2⁻¹)) = commonPhase := by
    calc
      _ = NormedSpace.exp (((1 / 2 : ℝ) : ℂ) * Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
        congr 1
        push_cast
        ring
      _ = _ := hsmall
  have hl' : NormedSpace.exp (Complex.I * 2⁻¹ * ((Real.pi : ℂ) * 3 / 2)) =
      Complex.I * commonPhase := by
    calc
      _ = NormedSpace.exp (((1 / 2 : ℝ) : ℂ) * Complex.I * ((3 * Real.pi / 2 : ℝ) : ℂ)) := by
        congr 1
        push_cast
        ring
      _ = commonPhase * Complex.I := hlarge
      _ = _ := mul_comm _ _
  rw [logarithm, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> cases swapped <;>
    simp [halfDiagonal, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  all_goals first
    | simpa only [mul_comm, mul_left_comm, mul_assoc] using hs'
    | simpa only [mul_comm, mul_left_comm, mul_assoc] using hl' 

private theorem common_phase_unit : commonPhase * star commonPhase = 1 := by
  change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  norm_num [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I]
  simp only [map_ofNat]
  ring_nf
  simp

private theorem half_channel (m : ℕ) (swapped : Bool) :
    conj (initialization 2 m * NormedSpace.exp
      ((((1 / 2 : ℝ) : ℂ) * Complex.I) • logarithm swapped)) =
    conj (initialization 2 m * halfDiagonal swapped) := by
  rw [half_exp, Matrix.mul_smul]
  apply LinearMap.ext
  intro X
  change (commonPhase • (initialization 2 m * halfDiagonal swapped)) * X *
    (commonPhase • (initialization 2 m * halfDiagonal swapped))ᴴ =
    (initialization 2 m * halfDiagonal swapped) * X *
      (initialization 2 m * halfDiagonal swapped)ᴴ
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (star commonPhase), common_phase_unit, one_smul]

-- Expanding the fixed two-dimensional reference sums produces many scalar terms.
set_option maxHeartbeats 1600000 in
private theorem amplified_target (m : ℕ) (swapped : Bool) :
    kron (conj (initialization 2 m * NormedSpace.exp
      ((((1 / 2 : ℝ) : ℂ) * Complex.I) • logarithm swapped)))
      (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) inputDensity =
    outputDensity m swapped := by
  rw [half_channel]
  ext ⟨⟨a, i⟩, r⟩ ⟨⟨b, j⟩, s⟩
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;> cases swapped <;>
    simp [kron_def, conj, initialization, halfDiagonal, inputDensity, inputVector,
      outputDensity, outputVector, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMulVec, Pi.star_apply, Matrix.conjTranspose_apply,
      Matrix.single_apply] <;>
    (try split_ifs) <;> (try simp_all) <;> ring


private theorem amplified_sub {m : ℕ}
    (φ ψ : MatrixMap (Fin 2) (Fin (m + 1) × Fin 2) ℂ) :
    kron (φ - ψ) (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) inputDensity =
    kron φ (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) inputDensity -
      kron ψ (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) inputDensity := by
  ext ⟨p, r⟩ ⟨q, s⟩
  simp only [kron_def, LinearMap.sub_apply, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

private theorem no_success {m N : ℕ} (A : Circuit 2 m N) :
    ¬ Successful A (1 / 2) (1 / 2) (1 / 4) := by
  intro hs
  have h0 := hs oracle (logarithm false)
    (by simpa using (logarithm_exp false).symm)
    (logarithm_admissible false).1 (logarithm_admissible false).2
  have h1 := hs (-oracle) (logarithm true)
    (by simpa using (logarithm_exp true).symm)
    (logarithm_admissible true).1 (logarithm_admissible true).2
  rw [channel_neg] at h1
  have bound (φ : MatrixMap (Fin 2) (Fin (m + 1) × Fin 2) ℂ)
      (hφ : diamondNorm φ ≤ ENNReal.ofReal (1 / 4 : ℝ)) :
      traceNorm (kron φ (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) inputDensity) ≤ 1 / 4 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 4)).mp
    have hl : ENNReal.ofReal (traceNorm
        (kron φ (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) inputDensity)) ≤ diamondNorm φ := by
      apply le_sSup
      exact ⟨inputDensity, input_density.1, input_density.2, rfl⟩
    exact hl.trans hφ
  have b0 := bound _ h0
  have b1 := bound _ h1
  rw [amplified_sub, amplified_target] at b0 b1
  let X := kron (conj (run A oracle * initialization 2 m))
    (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) inputDensity
  change traceNorm (X - outputDensity m false) ≤ 1 / 4 at b0
  change traceNorm (X - outputDensity m true) ≤ 1 / 4 at b1
  have he : -(X - outputDensity m false) + (X - outputDensity m true) =
      outputDensity m false - outputDensity m true := by abel
  have ht := traceNorm_add_le (-(X - outputDensity m false)) (X - outputDensity m true)
  rw [he, output_separation, traceNorm_neg] at ht
  linarith

/-- The prescribed-branch matching upper bound fails for ordinary queries. -/
theorem result : ¬ claim := by
  rintro ⟨C, hC, h⟩
  obtain ⟨m, N, A, _, hs⟩ := h (1 / 2) (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 2 (by norm_num)
  exact no_success A hs

end Trureturing.OpenProblems.FractionalEvolutionPhase
