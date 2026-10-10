/- GID: D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Product-SIC zero fidelity and the sharp process-fidelity bound on qubit channels. -/

import D5.S3.Resource.CompositeConeProperness
import D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.QuantumBounds.PeritoTsirelson

open scoped BigOperators Kronecker ComplexOrder
open Matrix D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Resource.CompositeConeProperness

namespace D5.S3.Quantum.QuantumChannels.MayerZeroFidelityTightness
noncomputable section

def IsQubitSIC (s : Fin 4 → Fin 2 → ℂ) : Prop :=
  (∀ k, star (s k) ⬝ᵥ s k = 1) ∧
    ∀ k l, k ≠ l → ‖star (s k) ⬝ᵥ s l‖ ^ 2 = (1 / 3 : ℝ)

set_option maxHeartbeats 800000 in
-- The finite tensor-coordinate checks accompany the symbolic trace calculation.
/-- Four unit qubit vectors with SIC overlaps have the symmetric second moment. -/
theorem sic_frame (s : Fin 4 → Fin 2 → ℂ) (hs : IsQubitSIC s) :
    ∑ k, rankOneDensity (s k) ⊗ₖ rankOneDensity (s k) =
      (2 / 3 : ℂ) • (1 + swapMatrix) := by
  classical
  let P := fun k => rankOneDensity (s k)
  let B := ∑ k, P k ⊗ₖ P k
  let T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1 + swapMatrix
  have hP (k : Fin 4) : (P k)ᴴ = P k := by
    simp only [P, rankOneDensity, conjTranspose_vecMulVec, star_star]
  have htrace (k : Fin 4) : trace (P k) = 1 := by
    simpa only [P, rankOneDensity, trace_vecMulVec, dotProduct_comm] using hs.1 k
  have hpair (k l : Fin 4) : trace (P k * P l) =
      if k = l then 1 else (1 / 3 : ℂ) := by
    have heq : trace (P k * P l) = (Complex.normSq (star (s k) ⬝ᵥ s l) : ℂ) := by
      simp only [P, rankOneDensity, vecMulVec_mul_vecMulVec, trace_vecMulVec,
        dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm (s k), star_dotProduct (s k) (s l)]
      simpa using Complex.mul_conj (star (star (s l) ⬝ᵥ s k))
    rw [heq]
    split_ifs with h
    · subst l; rw [hs.1, Complex.normSq_one]; rfl
    · rw [Complex.normSq_eq_norm_sq, hs.2 k l h]; norm_num
  have hswap : swapMatrixᴴ = swapMatrix := by
    ext ⟨a,b⟩ ⟨c,d⟩
    simp [swapMatrix, conjTranspose_apply, Prod.mk.injEq, and_comm, eq_comm]
  have hswap_sq : swapMatrix * swapMatrix = 1 := by
    ext ⟨a,b⟩ ⟨c,d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [swapMatrix, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hswap_fixed (k : Fin 4) : (P k ⊗ₖ P k) * swapMatrix = P k ⊗ₖ P k := by
    ext ⟨a,b⟩ ⟨c,d⟩
    fin_cases c <;> fin_cases d <;>
      simp [P, rankOneDensity, swapMatrix, mul_apply,
        Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Pi.star_apply] <;> ring
  have hB : Bᴴ = B := by
    simp only [B, conjTranspose_sum, conjTranspose_kronecker, hP]
  have hT : Tᴴ = T := by simp only [T, conjTranspose_add, conjTranspose_one, hswap]
  have hBB : trace (B * B) = (16 / 3 : ℂ) := by
    simp only [B, Matrix.sum_mul, Matrix.mul_sum, trace_sum, ← mul_kronecker_mul,
      trace_kronecker, hpair]
    have ht (k l : Fin 4) :
        (if k = l then (1 : ℂ) else 1 / 3) * (if k = l then (1 : ℂ) else 1 / 3) =
          (if k = l then (8 / 9 : ℂ) else 0) + 1 / 9 := by
      split_ifs <;> norm_num
    simp_rw [ht]
    norm_num [Finset.sum_add_distrib]
  have hBT : trace (B * T) = 8 := by
    simp only [B, T, Matrix.sum_mul, Matrix.mul_add, Matrix.mul_one, hswap_fixed,
      trace_sum, trace_add, trace_kronecker, htrace]
    norm_num
  have hTT : trace (T * T) = 12 := by
    have hsq : T * T = (2 : ℂ) • T := by
      dsimp [T]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hswap_sq]
      module
    rw [hsq, trace_smul]
    norm_num [T, trace_add, swapMatrix, trace, diag, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hz : B - (2 / 3 : ℂ) • T = 0 := by
    apply trace_conjTranspose_mul_self_eq_zero_iff.mp
    have hstar : (B - (2 / 3 : ℂ) • T)ᴴ = B - (2 / 3 : ℂ) • T := by
      simp only [conjTranspose_sub, conjTranspose_smul, hB, hT]
      norm_num
    rw [hstar]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      trace_sub, trace_smul, hBB, hBT, trace_mul_comm T B, hTT]
    norm_num
  exact sub_eq_zero.mp hz

/-- The complex bilinear second moment of a qubit SIC. -/
theorem sic_bilinear (s : Fin 4 → Fin 2 → ℂ) (hs : IsQubitSIC s)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ k, trace (rankOneDensity (s k) * A) * trace (rankOneDensity (s k) * B) =
      (2 / 3 : ℂ) * (trace A * trace B + trace (A * B)) := by
  have h := congrArg (fun M => trace (M * (A ⊗ₖ B))) (sic_frame s hs)
  simpa only [Matrix.sum_mul, trace_sum, ← mul_kronecker_mul, trace_kronecker,
    Matrix.smul_mul, trace_smul, Matrix.add_mul, Matrix.one_mul, trace_add, hswap_trace,
    smul_eq_mul] using h

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Kronecker
open Matrix D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
open D5.S3.QuantumBounds.PeritoTsirelson (maxEntangledVector maxEntangled max_entangled_trace)

/-- The product of independently chosen single-qubit SIC states. -/
def productState {n : ℕ} (s : Fin n → Fin 4 → Fin 2 → ℂ) (κ : Fin n → Fin 4) :
    (Fin n → Fin 2) → ℂ := fun x => ∏ i, s i (κ i) (x i)

/-- The source's average survival probability on its product SIC states. -/
def zeroFidelity {n r : ℕ} (s : Fin n → Fin 4 → Fin 2 → ℂ)
    (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∑ κ : Fin n → Fin 4,
    (star (productState s κ) ⬝ᵥ
      MatrixMap.of_kraus K K (rankOneDensity (productState s κ)) *ᵥ productState s κ).re

/-- The source's entangled-state definition of process fidelity for a Kraus channel. -/
def processFidelity {n r : ℕ}
    (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ :=
  let L := fun j => (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ⊗ₖ K j
  (star (maxEntangledVector (Fin n → Fin 2)) ⬝ᵥ
    MatrixMap.of_kraus L L (maxEntangled (Fin n → Fin 2)) *ᵥ
      maxEntangledVector (Fin n → Fin 2)).re

/-- All Pauli coefficients of weight at least two vanish. -/
def HasWeightOneSupport {n r : ℕ}
    (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  ∀ j β, 2 ≤ (hammingDist β (fun _ => Pauli.I)) → trace ((wordOp β)ᴴ * K j) = 0

set_option maxHeartbeats 800000 in
-- Products over arbitrary registers are converted to sums over their coordinates.
theorem product_pauli_covariance {n : ℕ} (s : Fin n → Fin 4 → Fin 2 → ℂ)
    (hs : ∀ i, IsQubitSIC (s i)) (β γ : Fin n → Pauli) :
    ∑ κ : Fin n → Fin 4,
      trace (rankOneDensity (productState s κ) * wordOp β) *
      trace (rankOneDensity (productState s κ) * wordOp γ) =
        if β = γ then (4 : ℂ) ^ n * (1 / 3 : ℂ) ^ (hammingDist β (fun _ => Pauli.I)) else 0 := by
  classical
  have hprojector (κ : Fin n → Fin 4) : rankOneDensity (productState s κ) =
      tensorOp (fun i => rankOneDensity (s i (κ i))) := by
    ext x y
    simp only [rankOneDensity, productState, vecMulVec_apply, Pi.star_apply,
      tensorOp, Matrix.of_apply, star_prod, Finset.prod_mul_distrib]
  have hexpect (κ : Fin n → Fin 4) (β : Fin n → Pauli) :
      trace (rankOneDensity (productState s κ) * wordOp β) =
        ∏ i, trace (rankOneDensity (s i (κ i)) * pauliMatrix (β i)) := by
    rw [hprojector, wordOp, tensor_mul, tensor_trace]
  have local_moment (i : Fin n) (a b : Pauli) :
      ∑ k, trace (rankOneDensity (s i k) * pauliMatrix a) *
        trace (rankOneDensity (s i k) * pauliMatrix b) =
          if a = b then (if a = Pauli.I then (4 : ℂ) else 4 / 3) else 0 := by
    rw [sic_bilinear (s i) (hs i)]
    cases a <;> cases b <;>
      norm_num [pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, trace, diag, Matrix.mul_apply,
        Fin.sum_univ_two] <;> intro h <;> cases h
  simp_rw [hexpect, ← Finset.prod_mul_distrib]
  have hsum := Finset.prod_univ_sum (fun i : Fin n => (Finset.univ : Finset (Fin 4)))
    (fun i k => trace (rankOneDensity (s i k) * pauliMatrix (β i)) *
      trace (rankOneDensity (s i k) * pauliMatrix (γ i)))
  rw [Fintype.piFinset_univ] at hsum
  rw [← hsum]
  simp_rw [local_moment]
  by_cases heq : β = γ
  · subst γ
    simp only [if_true]
    have ht (i : Fin n) : (if β i = Pauli.I then (4 : ℂ) else 4 / 3) =
        4 * (if β i ≠ Pauli.I then (1 / 3 : ℂ) else 1) := by
      split_ifs <;> simp_all <;> ring
    simp_rw [ht]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [← Finset.prod_filter]
    simp [hammingDist]
  · rw [if_neg heq]
    obtain ⟨i, hi⟩ : ∃ i, β i ≠ γ i := Function.ne_iff.mp heq
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)


set_option maxHeartbeats 1000000 in
-- The double sum over Pauli words is reduced by the product covariance identity.
theorem product_pauli_parseval {n : ℕ} (s : Fin n → Fin 4 → Fin 2 → ℂ)
    (hs : ∀ i, IsQubitSIC (s i)) (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    ∑ κ : Fin n → Fin 4, ‖trace (rankOneDensity (productState s κ) * A)‖ ^ 2 =
      ∑ β : Fin n → Pauli,
        (1 / 3 : ℝ) ^ (hammingDist β (fun _ => Pauli.I)) * ‖trace (wordOp β * A)‖ ^ 2 := by
  classical
  let d : ℂ := (2 : ℂ) ^ n
  let c := fun β : Fin n → Pauli => d⁻¹ * trace (wordOp β * A)
  let e := fun (κ : Fin n → Fin 4) (β : Fin n → Pauli) =>
    trace (rankOneDensity (productState s κ) * wordOp β)
  have hd : d ≠ 0 := pow_ne_zero _ (by norm_num)
  have hword := @word_hermitian n
  have he (κ : Fin n → Fin 4) (β : Fin n → Pauli) : star (e κ β) = e κ β := by
    change star (trace (rankOneDensity (productState s κ) * wordOp β)) =
      trace (rankOneDensity (productState s κ) * wordOp β)
    rw [← trace_conjTranspose, conjTranspose_mul, hword]
    have hp : (rankOneDensity (productState s κ))ᴴ = rankOneDensity (productState s κ) := by
      simp only [rankOneDensity, conjTranspose_vecMulVec, star_star]
    rw [hp, trace_mul_comm]
  have hexp (κ : Fin n → Fin 4) : trace (rankOneDensity (productState s κ) * A) =
      ∑ β, c β * e κ β := by
    conv_lhs => rw [word_expansion A]
    simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]
    rfl
  have hc (β : Fin n → Pauli) :
      c β * star (c β) * ((4 : ℂ) ^ n * (1 / 3 : ℂ) ^ (hammingDist β (fun _ => Pauli.I))) =
        (1 / 3 : ℂ) ^ (hammingDist β (fun _ => Pauli.I)) * trace (wordOp β * A) *
          star (trace (wordOp β * A)) := by
    have hreal : star d = d := by simp [d]
    have hfour : (4 : ℂ) ^ n = d * d := by dsimp [d]; rw [← mul_pow]; norm_num
    change d⁻¹ * trace (wordOp β * A) * star (d⁻¹ * trace (wordOp β * A)) *
      ((4 : ℂ) ^ n * (1 / 3 : ℂ) ^ (hammingDist β (fun _ => Pauli.I))) =
        (1 / 3 : ℂ) ^ (hammingDist β (fun _ => Pauli.I)) * trace (wordOp β * A) *
          star (trace (wordOp β * A))
    rw [star_mul, star_inv₀, hreal, hfour]
    field_simp
  have heq :
      (∑ κ : Fin n → Fin 4, ‖trace (rankOneDensity (productState s κ) * A)‖ ^ 2 : ℝ) =
        ∑ β : Fin n → Pauli,
        (1 / 3 : ℝ) ^ (hammingDist β (fun _ => Pauli.I)) * ‖trace (wordOp β * A)‖ ^ 2 := by
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      ← Complex.normSq_eq_norm_sq]
    simp_rw [← Complex.mul_conj]
    change (∑ κ, trace (rankOneDensity (productState s κ) * A) *
      star (trace (rankOneDensity (productState s κ) * A))) =
        ∑ β, (1 / 3 : ℂ) ^ (hammingDist β (fun _ => Pauli.I)) *
          (trace (wordOp β * A) * star (trace (wordOp β * A)))
    simp_rw [hexp]
    simp only [star_sum, star_mul', he, Finset.sum_mul, Finset.mul_sum]
    have hrearr (κ : Fin n → Fin 4) (β γ : Fin n → Pauli) :
        c β * e κ β * (star (c γ) * e κ γ) =
          (c β * star (c γ)) * (e κ β * e κ γ) := by ring
    simp_rw [hrearr]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp only [e, product_pauli_covariance s hs, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [hc]
    ring
  exact heq

theorem kraus_survival {a : Type*} [Fintype a] {r : ℕ}
    (ψ : a → ℂ) (K : Fin r → Matrix a a ℂ) :
    (star ψ ⬝ᵥ MatrixMap.of_kraus K K (rankOneDensity ψ) *ᵥ ψ).re =
      ∑ j, ‖star ψ ⬝ᵥ K j *ᵥ ψ‖ ^ 2 := by
  classical
  have hp (A : Matrix a a ℂ) : A * rankOneDensity ψ * Aᴴ = rankOneDensity (A *ᵥ ψ) := by
    simpa only [one_smul] using
      D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.hsandwich A ψ 1
  have hs (v : a → ℂ) : star ψ ⬝ᵥ rankOneDensity v *ᵥ ψ =
      (Complex.normSq (star ψ ⬝ᵥ v) : ℂ) := by
    simp only [rankOneDensity, vecMulVec_mulVec, dotProduct_smul, op_smul_eq_smul,
      smul_eq_mul]
    change (star v ⬝ᵥ ψ) * (star ψ ⬝ᵥ v) = _
    rw [star_dotProduct v ψ]
    rw [mul_comm]
    exact Complex.mul_conj _
  unfold MatrixMap.of_kraus
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, hp]
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp only [hs, Complex.re_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem bell_amplitude {n : ℕ} (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    star (maxEntangledVector (Fin n → Fin 2)) ⬝ᵥ
      ((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ⊗ₖ A) *ᵥ
        maxEntangledVector (Fin n → Fin 2) = ((2 : ℂ) ^ n)⁻¹ * trace A := by
  calc
    _ = trace (maxEntangled (Fin n → Fin 2) * (1 ⊗ₖ A)) := by
      rw [maxEntangled, vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec,
        dotProduct_comm]
    _ = _ := by
      rw [max_entangled_trace, transpose_one, one_mul]
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
        div_eq_mul_inv, mul_comm]

theorem pauli_total_mass {n r : ℕ} (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hTP : ∑ j, (K j)ᴴ * K j = 1) :
    ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∑ β : Fin n → Pauli,
      ∑ j, ‖trace (wordOp β * K j)‖ ^ 2 = 1 := by
  classical
  let d : ℂ := (2 : ℂ)^n
  have hd : d ≠ 0 := pow_ne_zero _ (by norm_num)
  have hword := @word_hermitian n
  have ha (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
      ((∑ β : Fin n → Pauli, ‖trace (wordOp β * A)‖^2 : ℝ) : ℂ) =
        d * trace (Aᴴ * A) := by
    have ht (β : Fin n → Pauli) : trace (Aᴴ * wordOp β) =
        star (trace (wordOp β * A)) := by
      rw [← trace_conjTranspose, conjTranspose_mul, hword]
    conv_rhs => arg 2; arg 1; arg 2; rw [word_expansion A]
    simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul, ht]
    rw [Finset.mul_sum]
    simp only [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro β _
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    change trace (wordOp β * A) * star (trace (wordOp β * A)) =
      d * (d⁻¹ * trace (wordOp β * A) * star (trace (wordOp β * A)))
    field_simp
  have hsum : ((∑ β : Fin n → Pauli, ∑ j, ‖trace (wordOp β * K j)‖ ^ 2 : ℝ) : ℂ) = d*d := by
    rw [Finset.sum_comm]
    rw [Complex.ofReal_sum]
    simp_rw [ha]
    rw [← Finset.mul_sum, ← trace_sum, hTP]
    simp only [trace_one, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    rfl
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
    Complex.ofReal_ofNat, Complex.ofReal_one, hsum]
  change d⁻¹ ^ 2 * (d*d) = 1
  field_simp

theorem weight_bound {n : ℕ} (q : (Fin n → Pauli) → ℝ) (hq : ∀ β, 0 ≤ q β)
    (hsum : ∑ β, q β = 1) :
    let F := q (fun _ => Pauli.I)
    let F0 := ∑ β, (1 / 3 : ℝ) ^ (hammingDist β (fun _ => Pauli.I)) * q β
    1 - (3 / 2 : ℝ) * (1 - F0) ≤ F ∧
      (F = 1 - (3 / 2 : ℝ) * (1 - F0) ↔ ∀ β, 2 ≤ (hammingDist β (fun _ => Pauli.I)) → q β = 0) := by
  classical
  dsimp only
  let z : Fin n → Pauli := fun _ => Pauli.I
  let a := fun β : Fin n → Pauli =>
    (if β = z then (1 : ℝ) else 0) + 1 / 2 - 3 / 2 * (1 / 3) ^ (hammingDist β (fun _ => Pauli.I))
  have hw0 (β : Fin n → Pauli) : (hammingDist β (fun _ => Pauli.I)) = 0 ↔ β = z := by
    exact hammingDist_eq_zero
  have ha0 (β : Fin n → Pauli) (h : (hammingDist β (fun _ => Pauli.I)) ≤ 1) : a β = 0 := by
    by_cases h0 : (hammingDist β (fun _ => Pauli.I)) = 0
    · rw [hw0] at h0
      subst β
      have hz : (hammingDist z (fun _ => Pauli.I)) = 0 := (hw0 z).2 rfl
      simp only [a, if_true, hz, pow_zero]
      norm_num
    · have h1 : (hammingDist β (fun _ => Pauli.I)) = 1 := by omega
      have hb : β ≠ z := by intro he; exact h0 ((hw0 β).2 he)
      simp only [a, if_neg hb, h1, pow_one]
      norm_num
  have hapos (β : Fin n → Pauli) (h : 2 ≤ (hammingDist β (fun _ => Pauli.I))) : 0 < a β := by
    have hb : β ≠ z := by intro he; have := (hw0 β).2 he; omega
    have hp : (1 / 3 : ℝ) ^ (hammingDist β (fun _ => Pauli.I)) ≤ (1 / 3 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    simp only [a, if_neg hb]
    norm_num at hp ⊢
    linarith
  have hanon (β : Fin n → Pauli) : 0 ≤ a β := by
    by_cases h : 2 ≤ (hammingDist β (fun _ => Pauli.I))
    · exact (hapos β h).le
    · rw [ha0 β (by omega)]
  have hgap : q z - 1 + 3 / 2 * (1 - ∑ β, (1 / 3 : ℝ)^(hammingDist β (fun _ => Pauli.I)) * q β) =
      ∑ β, a β * q β := by
    simp only [a, add_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ite_mul, zero_mul, one_mul]
    rw [Finset.sum_ite_eq', ← Finset.mul_sum, hsum]
    simp only [Finset.mem_univ, if_true]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  have hnon : 0 ≤ ∑ β, a β * q β :=
    Finset.sum_nonneg fun β _ => mul_nonneg (hanon β) (hq β)
  constructor
  · change 1 - 3 / 2 * (1 - ∑ β, (1 / 3 : ℝ)^(hammingDist β (fun _ => Pauli.I)) * q β) ≤ q z
    linarith
  · change q z = 1 - 3 / 2 * (1 - ∑ β, (1 / 3 : ℝ)^(hammingDist β (fun _ => Pauli.I)) * q β) ↔ _
    constructor
    · intro he β hβ
      have hz : ∑ β, a β * q β = 0 := by linarith [hgap]
      have ht := (Finset.sum_eq_zero_iff_of_nonneg
        (fun β _ => mul_nonneg (hanon β) (hq β))).mp hz β (Finset.mem_univ β)
      exact (mul_eq_zero.mp ht).resolve_left (ne_of_gt (hapos β hβ))
    · intro he
      have hz : ∑ β, a β * q β = 0 := by
        apply Finset.sum_eq_zero
        intro β _
        by_cases h : 2 ≤ (hammingDist β (fun _ => Pauli.I))
        · rw [he β h, mul_zero]
        · rw [ha0 β (by omega), zero_mul]
      linarith [hgap]

theorem process_trace {n r : ℕ} (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    processFidelity K = ((2 : ℝ)^n)⁻¹ ^ 2 * ∑ j, ‖trace (K j)‖ ^ 2 := by
  change (star (maxEntangledVector (Fin n → Fin 2)) ⬝ᵥ
    MatrixMap.of_kraus (fun j => 1 ⊗ₖ K j) (fun j => 1 ⊗ₖ K j)
      (rankOneDensity (maxEntangledVector (Fin n → Fin 2))) *ᵥ
        maxEntangledVector (Fin n → Fin 2)).re = _
  rw [kraus_survival]
  have h (j : Fin r) :
      ‖star (maxEntangledVector (Fin n → Fin 2)) ⬝ᵥ (1 ⊗ₖ K j) *ᵥ
        maxEntangledVector (Fin n → Fin 2)‖ ^ 2 =
          ‖((2 : ℂ) ^ n)⁻¹ * trace (K j)‖ ^ 2 := by
    rw [bell_amplitude]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  simp only [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat, mul_pow]
  rw [← Finset.mul_sum]

theorem zero_trace {n r : ℕ} (s : Fin n → Fin 4 → Fin 2 → ℂ) (hs : ∀ i, IsQubitSIC (s i))
    (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    zeroFidelity s K = ∑ β : Fin n → Pauli,
      (1 / 3 : ℝ)^(hammingDist β (fun _ => Pauli.I)) *
        (((2 : ℝ)^n)⁻¹ ^ 2 * ∑ j, ‖trace (wordOp β * K j)‖ ^ 2) := by
  have ht (ψ : (Fin n → Fin 2) → ℂ) (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
      star ψ ⬝ᵥ A *ᵥ ψ = trace (rankOneDensity ψ * A) := by
    rw [rankOneDensity, vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec,
      dotProduct_comm]
  unfold zeroFidelity
  simp_rw [kraus_survival, ht]
  rw [Finset.sum_comm]
  simp_rw [product_pauli_parseval s hs]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [← Finset.mul_sum]
  ring

theorem channel_bound {n r : ℕ} (s : Fin n → Fin 4 → Fin 2 → ℂ)
    (hs : ∀ i, IsQubitSIC (s i))
    (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hTP : ∑ j, (K j)ᴴ * K j = 1) :
    1 - (3 / 2 : ℝ) * (1 - zeroFidelity s K) ≤ processFidelity K ∧
      (processFidelity K = 1 - (3 / 2 : ℝ) * (1 - zeroFidelity s K) ↔ HasWeightOneSupport K) := by
  classical
  let z : Fin n → Pauli := fun _ => Pauli.I
  let q := fun β : Fin n → Pauli =>
    ((2 : ℝ)^n)⁻¹ ^ 2 * ∑ j, ‖trace (wordOp β * K j)‖ ^ 2
  have hq (β : Fin n → Pauli) : 0 ≤ q β := by
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hsum : ∑ β, q β = 1 := by
    dsimp only [q]
    rw [← Finset.mul_sum]
    exact pauli_total_mass K hTP
  have hword := @word_hermitian n
  have hz : wordOp z = 1 := word_one
  have hp : processFidelity K = q z := by
    rw [process_trace]
    simp only [q, hz, one_mul]
  have h0 : zeroFidelity s K =
      ∑ β, (1 / 3 : ℝ)^(hammingDist β (fun _ => Pauli.I)) * q β := zero_trace s hs K
  have hsupport :
      (∀ β, 2 ≤ (hammingDist β (fun _ => Pauli.I)) → q β = 0) ↔ HasWeightOneSupport K := by
    have hc : ((2 : ℝ)^n)⁻¹ ^ 2 ≠ 0 := by positivity
    constructor
    · intro h j β hw
      have he : ∑ j, ‖trace (wordOp β * K j)‖ ^ 2 = 0 :=
        (mul_eq_zero.mp (h β hw)).resolve_left hc
      have hj := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg ‖trace (wordOp β * K j)‖)).mp he j (Finset.mem_univ j)
      rw [hword]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
    · intro h β hw
      dsimp only [q]
      have hj (j : Fin r) : trace (wordOp β * K j) = 0 := by
        simpa only [hword] using h j β hw
      simp only [hj, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]
  have hb := weight_bound q hq hsum
  dsimp only at hb
  rw [← hp, ← h0] at hb
  exact ⟨hb.1, hb.2.trans hsupport⟩


set_option maxHeartbeats 800000 in
-- Tensor products over arbitrary registers require expanded finite coordinate sums.
theorem tight_channel {n : ℕ} (hn : 1 ≤ n) (s : Fin n → Fin 4 → Fin 2 → ℂ)
    (hs : ∀ i, IsQubitSIC (s i)) (f : ℝ) (hf : 1 / 3 ≤ f) (hf1 : f ≤ 1) :
    ∃ (r : ℕ) (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
      (∑ j, (K j)ᴴ * K j) = 1 ∧ zeroFidelity s K = f ∧
        processFidelity K = 1 - (3 / 2 : ℝ) * (1 - f) := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let p : ℝ := (3*f-1)/2
  let t : ℝ := (1-p)/3
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  let a : Fin 4 → Pauli := ![Pauli.I, Pauli.X, Pauli.Y, Pauli.Z]
  let w := fun k : Fin 4 => fun i : Fin n => if i = i0 then a k else Pauli.I
  let c : Fin 4 → ℝ := ![Real.sqrt p, Real.sqrt t, Real.sqrt t, Real.sqrt t]
  let K := fun k : Fin 4 => (c k : ℂ) • wordOp (w k)
  have hsq (β : Fin n → Pauli) : wordOp β * wordOp β = 1 :=
    (wordUnit β).inv_mul
  have hTP : ∑ k, (K k)ᴴ * K k = 1 := by
    have hk (k : Fin 4) : (K k)ᴴ * K k =
        ((c k)^2 : ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
      simp only [K, conjTranspose_smul, word_hermitian, Complex.star_def,
        Complex.conj_ofReal, smul_mul_smul, hsq, pow_two]
    simp_rw [hk]
    rw [← Finset.sum_smul]
    have hc : ∑ k, ((c k)^2 : ℂ) = 1 := by
      simp only [c, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero]
      simp only [← Complex.ofReal_pow, Real.sq_sqrt hp, Real.sq_sqrt ht]
      dsimp only [t]
      push_cast
      ring
    rw [hc, one_smul]
  have local_trace (b : Pauli) (hb : b ≠ Pauli.I) : trace (pauliMatrix b) = 0 := by
    simpa only [show pauliMatrix Pauli.I = 1 from rfl, mul_one, if_neg hb] using
      pauli_trace_pair b Pauli.I
  have hsupp : HasWeightOneSupport K := by
    intro k β hw
    have hi : ∃ i : Fin n, i ≠ i0 ∧ β i ≠ Pauli.I := by
      by_contra! h
      have hsub : (Finset.univ.filter fun i => β i ≠ Pauli.I) ⊆ {i0} := by
        intro i hi
        have hb := (Finset.mem_filter.mp hi).2
        have : i = i0 := by by_contra hne; exact hb (h i hne)
        simpa only [Finset.mem_singleton] using this
      have hc := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hc
      change 2 ≤ (Finset.univ.filter fun i => β i ≠ Pauli.I).card at hw
      omega
    obtain ⟨i, hi, hβ⟩ := hi
    change trace ((wordOp β)ᴴ * ((c k : ℂ) • wordOp (w k))) = 0
    rw [word_hermitian, Matrix.mul_smul, trace_smul]
    have htr : trace (wordOp β * wordOp (w k)) = 0 := by
      unfold wordOp
      rw [tensor_mul, tensor_trace]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [w, if_neg hi, show pauliMatrix Pauli.I = 1 from rfl, mul_one]
      exact local_trace (β i) hβ
    rw [htr, smul_zero]
  have hw0 : wordOp (w 0) = 1 := by
    simpa only [w, a, Matrix.cons_val_zero, ite_self] using (@word_one n)
  have htr (k : Fin 4) : trace (wordOp (w k)) = if k = 0 then (2 : ℂ)^n else 0 := by
    by_cases hk : k = 0
    · subst k
      rw [hw0]
      simp only [if_true, trace_one, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
        Nat.cast_ofNat]
    · rw [if_neg hk]
      unfold wordOp
      rw [tensor_trace]
      apply Finset.prod_eq_zero (Finset.mem_univ i0)
      simp only [w, if_true]
      apply local_trace
      fin_cases k <;> simp_all [a]
  have hF : processFidelity K = p := by
    rw [process_trace]
    simp only [K, trace_smul, smul_eq_mul, htr]
    simp only [Fin.sum_univ_succ, c, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero]
    norm_num [Fin.ext_iff]
    rw [abs_of_nonneg (Real.sqrt_nonneg p), mul_pow, Real.sq_sqrt hp]
    field_simp
  have he := (channel_bound s hs K hTP).2.mpr hsupp
  refine ⟨4, K, hTP, ?_, ?_⟩
  · rw [hF] at he
    dsimp [p] at he
    linarith
  · rw [hF]
    dsimp [p]
    ring


/-- The lower inequality in Mayer's Theorem 1. -/
theorem lower_bound {n r : ℕ} (s : Fin n → Fin 4 → Fin 2 → ℂ)
    (hs : ∀ i, IsQubitSIC (s i))
    (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hTP : ∑ j, (K j)ᴴ * K j = 1) :
    1 - (3 / 2 : ℝ) * (1 - zeroFidelity s K) ≤ processFidelity K :=
  (channel_bound s hs K hTP).1

/-- The universal lower bound, its equality cases, and attainability at every permitted fidelity. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ s : Fin n → Fin 4 → Fin 2 → ℂ,
    (∀ i, IsQubitSIC (s i)) →
      (∀ (r : ℕ) (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
        (∑ j, (K j)ᴴ * K j) = 1 →
          1 - (3 / 2 : ℝ) * (1 - zeroFidelity s K) ≤ processFidelity K ∧
          (processFidelity K = 1 - (3 / 2 : ℝ) * (1 - zeroFidelity s K) ↔
            HasWeightOneSupport K)) ∧
      ∀ f : ℝ, (1 / 3 : ℝ) ≤ f → f ≤ 1 →
        ∃ (r : ℕ) (K : Fin r → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
          (∑ j, (K j)ᴴ * K j) = 1 ∧ zeroFidelity s K = f ∧
          processFidelity K = 1 - (3 / 2 : ℝ) * (1 - f)

/-- Mayer's tightness conjecture and the complete Kraus equality characterization. -/
theorem result : claim := by
  intro n hn s hs
  constructor
  · intro r K hTP
    exact ⟨lower_bound s hs K hTP, (channel_bound s hs K hTP).2⟩
  · intro f hf hf1
    exact tight_channel hn s hs f hf hf1

#print axioms result

end
end D5.S3.Quantum.QuantumChannels.MayerZeroFidelityTightness
