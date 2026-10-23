/- GID: D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp worst-case fidelity of the product of process-matrix marginals. -/

import D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The product of single-site process marginals has squared Uhlmann fidelity at least
`4⁻ᴺ`. Cyclic wire permutations give equality when there are at least two wires. -/

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (Pauli pauliMatrix wordOp tensorOp)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (word_trace_pair word_expansion word_hermitian)
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma)
open D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation (uhlmann)
open D5.S3.Quantum.Foundation.FiniteTraceDistance

noncomputable section
namespace D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity

/-- A tensor product of Pauli matrices, in the order identity, X, Y, Z. -/
def pauliString {N : ℕ} (a : Fin N → Fin 4) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  fun x y => ∏ i, sigma (a i) (x i) (y i)

/-- Positivity and trace preservation in the unnormalized Pauli basis. -/
def IsProcessCPTP {N : ℕ} (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) : Prop :=
  χ.PosSemidef ∧ ∑ a, ∑ b, χ a b • (pauliString b * pauliString a) = 1

/-- The partial trace onto one four-dimensional site. -/
def marginal {N : ℕ} (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (k : Fin N) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => ∑ y, if y k = i then χ y (Function.update y k j) else 0

/-- The tensor product of all single-site process-matrix marginals. -/
def marginalApprox {N : ℕ} (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) :
    Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ :=
  fun a b => ∏ k, marginal χ k (a k) (b k)

/-- Squared Uhlmann root fidelity. -/
def fidelity {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : ℝ :=
  (uhlmann ρ σ) ^ 2

/-- The wire permutation with entry one exactly when `x = y ∘ finRotate N`. -/
def cyclicShift (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  fun x y => if x = y ∘ finRotate N then 1 else 0

/-- Pauli expansion coefficients of the cyclic wire permutation. -/
def shiftCoeff (N : ℕ) (a : Fin N → Fin 4) : ℂ :=
  (2 ^ N : ℂ)⁻¹ * Matrix.trace (pauliString a * cyclicShift N)

/-- The rank-one process matrix of the cyclic wire permutation. -/
def shiftProcess (N : ℕ) : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ :=
  Matrix.vecMulVec (shiftCoeff N) (star (shiftCoeff N))

/-- The universal lower bound and its cyclic-shift attainment. -/
def claim : Prop :=
  (∀ N, 1 ≤ N → ∀ χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ,
    IsProcessCPTP χ → (1 / 4 ^ N : ℝ) ≤ fidelity χ (marginalApprox χ)) ∧
  (∀ N, 2 ≤ N →
    (∑ a, shiftCoeff N a • pauliString a = cyclicShift N) ∧
    IsProcessCPTP (shiftProcess N) ∧
    (∀ k, marginal (shiftProcess N) k = (1 / 4 : ℂ) • 1) ∧
    fidelity (shiftProcess N) (marginalApprox (shiftProcess N)) = 1 / 4 ^ N)

private def pauliLabelEquiv : Fin 4 ≃ Pauli where
  toFun := ![.I, .X, .Y, .Z]
  invFun := fun | .I => 0 | .X => 1 | .Y => 2 | .Z => 3
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

private lemma pauliString_word {N : ℕ} (a : Fin N → Fin 4) :
    pauliString a = wordOp (fun k => pauliLabelEquiv (a k)) := by
  ext x y
  simp only [pauliString, wordOp, tensorOp, Matrix.of_apply]
  apply Finset.prod_congr rfl
  intro k _
  generalize a k = j
  fin_cases j <;> rfl

private lemma pauliString_trace_pair {N : ℕ} (a b : Fin N → Fin 4) :
    Matrix.trace (pauliString a * pauliString b) = if a = b then (2 : ℂ) ^ N else 0 := by
  have he : (fun k => pauliLabelEquiv (a k)) = (fun k => pauliLabelEquiv (b k)) ↔
      a = b := by
    constructor
    · intro h
      exact funext fun k => pauliLabelEquiv.injective (congrFun h k)
    · rintro rfl; rfl
  simpa only [pauliString_word, he] using
    word_trace_pair (fun k => pauliLabelEquiv (a k)) (fun k => pauliLabelEquiv (b k))

private lemma classical_overlap {N : ℕ} (p : (Fin N → Fin 4) → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) :
    (1 / 4 ^ N : ℝ) ≤
      ∑ x, p x * ∏ k, ∑ y, if y k = x k then p y else 0 := by
  classical
  let q (k : Fin N) (j : Fin 4) : ℝ := ∑ y, if y k = j then p y else 0
  have hq (k : Fin N) (j : Fin 4) : 0 ≤ q k j := by
    exact Finset.sum_nonneg fun y _ => by split_ifs <;> simp_all
  have hqs (k : Fin N) : ∑ j, q k j = 1 := by
    dsimp [q]
    rw [Finset.sum_comm]
    simpa using hs
  have hlocal (k : Fin N) : (1 / 4 : ℝ) ≤ ∏ j, (q k j) ^ (q k j) := by
    have hpos : 0 < ∏ j, (q k j) ^ (q k j) := by
      apply Finset.prod_pos
      intro j _
      by_cases hj : q k j = 0
      · simp [hj]
      · exact Real.rpow_pos_of_pos (lt_of_le_of_ne (hq k j) (Ne.symm hj)) _
    have ham := Real.geom_mean_le_arith_mean_weighted Finset.univ (q k)
      (fun j => (q k j)⁻¹) (fun j _ => hq k j) (hqs k)
      (fun j _ => inv_nonneg.mpr (hq k j))
    have hsum : (∑ j, q k j * (q k j)⁻¹) ≤ 4 := by
      calc
        _ ≤ ∑ _j : Fin 4, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : q k j = 0 <;> simp [hj]
        _ = 4 := by norm_num
    simp_rw [Real.inv_rpow (hq k _)] at ham
    rw [Finset.prod_inv_distrib] at ham
    have hmul := (inv_le_iff_one_le_mul₀ hpos).mp (ham.trans hsum)
    linarith
  have hfactor : (∏ x, (∏ k, q k (x k)) ^ p x) =
      ∏ k, ∏ j, (q k j) ^ (q k j) := by
    calc
      _ = ∏ x, ∏ k, (q k (x k)) ^ p x := by
        apply Finset.prod_congr rfl
        intro x _
        exact (Real.finsetProd_rpow Finset.univ (fun k => q k (x k))
          (fun k _ => hq k (x k)) (p x)).symm
      _ = ∏ k, ∏ x, (q k (x k)) ^ p x := Finset.prod_comm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro k _
        rw [← Finset.prod_fiberwise Finset.univ (fun x : Fin N → Fin 4 => x k)]
        apply Finset.prod_congr rfl
        intro j _
        have he : q k j = ∑ x ∈ Finset.univ.filter (fun x => x k = j), p x := by
          simp [q, Finset.sum_filter]
        calc
          _ = ∏ x ∈ Finset.univ.filter (fun x => x k = j), (q k j) ^ p x := by
            apply Finset.prod_congr rfl
            intro x hx
            rw [(Finset.mem_filter.mp hx).2]
          _ = (q k j) ^ (∑ x ∈ Finset.univ.filter (fun x => x k = j), p x) :=
            (Real.rpow_sum_of_nonneg (hq k j) (fun x _ => hp x)).symm
          _ = _ := by rw [← he]
  have ham := Real.geom_mean_le_arith_mean_weighted Finset.univ p
    (fun x => ∏ k, q k (x k)) (fun x _ => hp x) hs
    (fun x _ => Finset.prod_nonneg fun k _ => hq k (x k))
  rw [hfactor] at ham
  calc
    (1 / 4 ^ N : ℝ) = ∏ _k : Fin N, (1 / 4 : ℝ) := by simp [div_pow]
    _ ≤ ∏ k, ∏ j, (q k j) ^ (q k j) := by
      exact Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun k _ => hlocal k)
    _ ≤ _ := ham

private lemma process_trace {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (hχ : IsProcessCPTP χ) :
    Matrix.trace χ = 1 := by
  classical
  have ht := congrArg Matrix.trace hχ.2
  simp only [Matrix.trace_sum, Matrix.trace_smul, pauliString_trace_pair, smul_eq_mul,
    mul_ite, mul_zero] at ht
  have ht' : Matrix.trace χ * (2 : ℂ) ^ N = 1 * (2 : ℂ) ^ N := by
    simpa [Matrix.trace, ← Finset.sum_mul, Fintype.card_fun] using ht
  exact mul_right_cancel₀ (pow_ne_zero N (by norm_num : (2 : ℂ) ≠ 0)) ht' 

private lemma marginal_split {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (k : Fin N) (i j : Fin 4) :
    marginal χ k i j = ∑ z : {l : Fin N // l ≠ k} → Fin 4,
      χ ((Equiv.funSplitAt k (Fin 4)).symm (i, z))
        ((Equiv.funSplitAt k (Fin 4)).symm (j, z)) := by
  classical
  let e := Equiv.funSplitAt k (Fin 4)
  have hcoord (t : Fin 4) (z : {l : Fin N // l ≠ k} → Fin 4) :
      (e.symm (t, z)) k = t := congrArg Prod.fst (e.apply_symm_apply (t, z))
  have hupdate (t : Fin 4) (z : {l : Fin N // l ≠ k} → Fin 4) :
      Function.update (e.symm (t, z)) k j = e.symm (j, z) := by
    funext l
    by_cases hl : l = k
    · subst l
      simp only [Function.update_self, hcoord]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hl, Function.update_of_ne hl]
  unfold marginal
  rw [← e.symm.sum_comp (fun y => if y k = i then χ y (Function.update y k j) else 0),
    Fintype.sum_prod_type]
  simp_rw [hcoord, hupdate]
  rw [Finset.sum_comm]
  simp [e]

private lemma marginal_psd {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (hχ : χ.PosSemidef) (k : Fin N) :
    (marginal χ k).PosSemidef := by
  classical
  have he : marginal χ k = ∑ z : {l : Fin N // l ≠ k} → Fin 4,
      χ.submatrix (fun i => (Equiv.funSplitAt k (Fin 4)).symm (i, z))
        (fun i => (Equiv.funSplitAt k (Fin 4)).symm (i, z)) := by
    ext i j
    simpa only [Matrix.sum_apply, Matrix.submatrix_apply] using marginal_split χ k i j
  rw [he]
  exact Matrix.posSemidef_sum Finset.univ fun z _ => hχ.submatrix _

private lemma marginalApprox_psd {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (hχ : χ.PosSemidef) :
    (marginalApprox χ).PosSemidef := by
  classical
  have hprod (s : Finset (Fin N)) :
      Matrix.PosSemidef
        (fun a b : Fin N → Fin 4 => ∏ k ∈ s, marginal χ k (a k) (b k)) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun a b : Fin N → Fin 4 =>
          ∏ k ∈ (∅ : Finset (Fin N)), marginal χ k (a k) (b k)) =
          Matrix.vecMulVec (fun _ : Fin N → Fin 4 => (1 : ℂ))
            (star (fun _ : Fin N → Fin 4 => (1 : ℂ))) := by
        ext a b
        simp [Matrix.vecMulVec_apply]
      rw [he]
      exact Matrix.posSemidef_vecMulVec_self_star _
    | @insert k s hk ih =>
      have he : (fun a b : Fin N → Fin 4 =>
          ∏ l ∈ insert k s, marginal χ l (a l) (b l)) =
          Matrix.hadamard ((marginal χ k).submatrix (fun a => a k) (fun a => a k))
            (fun a b => ∏ l ∈ s, marginal χ l (a l) (b l)) := by
        ext a b
        simp only [Finset.prod_insert hk]
        rfl
      rw [he]
      exact ((marginal_psd χ hχ k).submatrix (fun a : Fin N → Fin 4 => a k)).hadamard ih
  exact hprod Finset.univ

private lemma quantum_overlap {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ)
    (hχ : χ.PosSemidef) (ht : Matrix.trace χ = 1)
    (hc : ∀ p : (Fin N → Fin 4) → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
      (1 / 4 ^ N : ℝ) ≤
        ∑ x, p x * ∏ k, ∑ y, if y k = x k then p y else 0) :
    (1 / 4 ^ N : ℝ) ≤ (Matrix.trace (χ * marginalApprox χ)).re := by
  sorry

private lemma fidelity_overlap {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    (Matrix.trace (ρ * σ)).re ≤ fidelity ρ σ := by
  classical
  let X := CFC.sqrt ρ * CFC.sqrt σ
  let S := CFC.sqrt (Xᴴ * X)
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  let D := Matrix.diagonal (fun i => (hS.1.eigenvalues i : ℂ))
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hS.1.eigenvectorUnitary
  have hspec : S = φ D := hS.1.spectral_theorem
  have hsquare : (Matrix.trace (S * S)).re = ∑ i, (hS.1.eigenvalues i) ^ 2 := by
    calc
      _ = (Matrix.trace (φ (D * D))).re := by rw [map_mul, ← hspec]
      _ = (Matrix.trace (D * D)).re := by
        dsimp [φ]
        rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
      _ = _ := by
        simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
          Complex.mul_re, pow_two]
  have htrace : (Matrix.trace S).re = ∑ i, hS.1.eigenvalues i := by
    rw [hS.1.trace_eq_sum_eigenvalues]
    simp
  have hρs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).1.eq
  have hσs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).1.eq
  have hgram : Matrix.trace (Xᴴ * X) = Matrix.trace (ρ * σ) := by
    dsimp [X]
    rw [Matrix.conjTranspose_mul, hρs, hσs]
    calc
      _ = Matrix.trace (CFC.sqrt σ * (CFC.sqrt ρ * CFC.sqrt ρ) * CFC.sqrt σ) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (CFC.sqrt σ * ρ * CFC.sqrt σ) := by
        rw [CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
      _ = Matrix.trace (CFC.sqrt σ * CFC.sqrt σ * ρ) := Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (ρ * σ) := by
        rw [CFC.sqrt_mul_sqrt_self σ hσ.nonneg, Matrix.trace_mul_comm]
  calc
    (Matrix.trace (ρ * σ)).re = (Matrix.trace (S * S)).re := by
      rw [show S * S = Xᴴ * X from CFC.sqrt_mul_sqrt_self _
        (Matrix.posSemidef_conjTranspose_mul_self X).nonneg, hgram]
    _ ≤ (Matrix.trace S).re ^ 2 := by
      rw [hsquare, htrace]
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hS.eigenvalues_nonneg i)
    _ = fidelity ρ σ := rfl

private lemma shift_expansion (N : ℕ) :
    ∑ a, shiftCoeff N a • pauliString a = cyclicShift N := by
  classical
  simp only [shiftCoeff, pauliString_word]
  let e : (Fin N → Fin 4) ≃ (Fin N → Pauli) :=
    Equiv.piCongrRight fun _ => pauliLabelEquiv
  exact (e.sum_comp (fun a => (((2 : ℂ) ^ N)⁻¹ *
    Matrix.trace (wordOp a * cyclicShift N)) • wordOp a)).trans
    (word_expansion (cyclicShift N)).symm

private lemma shift_unitary (N : ℕ) : (cyclicShift N)ᴴ * cyclicShift N = 1 := by
  classical
  ext x y
  have hrot : (x ∘ finRotate N = y ∘ finRotate N) ↔ x = y := by
    constructor
    · intro h
      funext i
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        congrFun h ((finRotate N).symm i)
    · rintro rfl; rfl
  have hc (z : Fin N → Fin 2) :
      star (if z = x ∘ finRotate N then (1 : ℂ) else 0) =
        if z = x ∘ finRotate N then (1 : ℂ) else 0 := by
    split_ifs <;> simp
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cyclicShift,
    hc, ite_mul, one_mul, zero_mul, Matrix.one_apply]
  rw [Finset.sum_ite_eq' Finset.univ (x ∘ finRotate N)]
  simp only [Finset.mem_univ, ite_true, hrot, Matrix.one_apply]

private lemma shift_cptp (N : ℕ)
    (he : ∑ a, shiftCoeff N a • pauliString a = cyclicShift N)
    (hu : (cyclicShift N)ᴴ * cyclicShift N = 1) : IsProcessCPTP (shiftProcess N) := by
  classical
  refine ⟨Matrix.posSemidef_vecMulVec_self_star (shiftCoeff N), ?_⟩
  have hstar : (∑ a, star (shiftCoeff N a) • pauliString a) = (cyclicShift N)ᴴ := by
    have h := congrArg (fun A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ => Aᴴ) he
    simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      pauliString_word, word_hermitian] using h
  calc
    _ = (∑ b, star (shiftCoeff N b) • pauliString b) *
        (∑ a, shiftCoeff N a • pauliString a) := by
      rw [Matrix.sum_mul]
      simp only [Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum,
        smul_smul, shiftProcess, Matrix.vecMulVec_apply, Pi.star_apply]
      rw [Finset.sum_comm]
    _ = 1 := by rw [hstar, he, hu]

private lemma shift_marginals (N : ℕ) (hN : 2 ≤ N) :
    ∀ k, marginal (shiftProcess N) k = (1 / 4 : ℂ) • 1 := by
  sorry

private lemma shift_fidelity (N : ℕ)
    (hχ : IsProcessCPTP (shiftProcess N))
    (hm : ∀ k, marginal (shiftProcess N) k = (1 / 4 : ℂ) • 1) :
    fidelity (shiftProcess N) (marginalApprox (shiftProcess N)) = 1 / 4 ^ N := by
  classical
  let c : ℝ := 1 / 4 ^ N
  have hc : 0 ≤ c := by positivity
  have ht : Matrix.trace (shiftProcess N) = 1 := process_trace _ hχ
  have hnorm : star (shiftCoeff N) ⬝ᵥ shiftCoeff N = 1 := by
    rw [dotProduct_comm]
    simpa only [shiftProcess, Matrix.trace_vecMulVec] using ht
  have hidem : shiftProcess N * shiftProcess N = shiftProcess N := by
    simp only [shiftProcess, Matrix.vecMulVec_mul_vecMulVec, hnorm, one_smul]
  have hroot : CFC.sqrt (shiftProcess N) = shiftProcess N :=
    CFC.sqrt_unique hidem hχ.1.nonneg
  have hmarg : marginalApprox (shiftProcess N) = (c : ℂ) • 1 := by
    ext a b
    simp only [marginalApprox, hm, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    by_cases hab : a = b
    · subst b
      simp [c, div_pow]
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
      rw [if_neg hab]
      simp only [mul_zero]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
  have hdiag (r : ℝ) :
      Matrix.diagonal (fun _ : Fin N → Fin 4 => (r : ℂ)) = (r : ℂ) • 1 := by
    ext a b
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs <;> simp
  have hsqrt := D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.sqrt_diagonal
    (fun _ : Fin N → Fin 4 => c) (fun _ => hc)
  rw [hdiag c, hdiag (Real.sqrt c)] at hsqrt
  have hprod : CFC.sqrt (shiftProcess N) * CFC.sqrt (marginalApprox (shiftProcess N)) =
      (Real.sqrt c : ℂ) • shiftProcess N := by
    rw [hroot, hmarg, hsqrt, Matrix.mul_smul, Matrix.mul_one]
  have hp : ((Real.sqrt c : ℂ) • shiftProcess N).PosSemidef :=
    hχ.1.smul (Complex.zero_le_real.mpr (Real.sqrt_nonneg c))
  have htn := congrArg Complex.re (traceNorm_of_posSemidef hp)
  have hu : uhlmann (shiftProcess N) (marginalApprox (shiftProcess N)) = Real.sqrt c := by
    unfold uhlmann
    rw [hprod]
    simpa [Matrix.trace_smul, ht] using htn
  rw [fidelity, hu, Real.sq_sqrt hc]

/-- The bound holds for every process matrix; cyclic shifts attain it for at least two qubits. -/
theorem result : claim := by
  constructor
  · intro N _ χ hχ
    exact (quantum_overlap χ hχ.1 (process_trace χ hχ) classical_overlap).trans
      (fidelity_overlap χ (marginalApprox χ) hχ.1 (marginalApprox_psd χ hχ.1))
  · intro N hN
    have he := shift_expansion N
    have hχ := shift_cptp N he (shift_unitary N)
    have hm := shift_marginals N hN
    exact ⟨he, hχ, hm, shift_fidelity N hχ hm⟩

end D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity
