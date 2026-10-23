/- GID: D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp worst-case fidelity of the product of process-matrix marginals. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation

/-! The product of single-site process marginals has squared Uhlmann fidelity at least
`4⁻ᴺ`. Cyclic wire permutations give equality when there are at least two wires. -/

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (productMap)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (Pauli pauliMatrix wordOp tensorOp qubitPermutation)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (word_trace_pair word_expansion word_hermitian)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma)
open D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation (sqFidelity)

noncomputable section
namespace D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity

/-- Positivity and trace preservation in the unnormalized Pauli basis. -/
def IsProcessCPTP {N : ℕ} (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) : Prop :=
  χ.PosSemidef ∧
    ∑ a, ∑ b, χ a b •
      (tensorOp (fun k => sigma (b k)) * tensorOp (fun k => sigma (a k))) = 1

/-- The partial trace onto one four-dimensional site. -/
def marginal {N : ℕ} (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (k : Fin N) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => ∑ y, if y k = i then χ y (Function.update y k j) else 0

/-- Pauli expansion coefficients of the cyclic wire permutation. -/
def shiftCoeff (N : ℕ) (a : Fin N → Fin 4) : ℂ :=
  (2 ^ N : ℂ)⁻¹ * Matrix.trace (tensorOp (fun k => sigma (a k)) * (qubitPermutation (finRotate N))ᵀ)

/-- The universal lower bound and its cyclic-shift attainment. -/
def claim : Prop :=
  (∀ N, 1 ≤ N → ∀ χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ,
    IsProcessCPTP χ → (1 / 4 ^ N : ℝ) ≤ sqFidelity χ (productMap (fun _ => Fin 4) (marginal χ))) ∧
  (∀ N, 2 ≤ N →
    (∑ a, shiftCoeff N a • tensorOp (fun k => sigma (a k)) = (qubitPermutation (finRotate N))ᵀ) ∧
    IsProcessCPTP (rankOneDensity (shiftCoeff N)) ∧
    (∀ k, marginal (rankOneDensity (shiftCoeff N)) k = (1 / 4 : ℂ) • 1) ∧
    sqFidelity (rankOneDensity (shiftCoeff N))
      (productMap (fun _ => Fin 4) (marginal (rankOneDensity (shiftCoeff N)))) = 1 / 4 ^ N)

private def pauliLabelEquiv : Fin 4 ≃ Pauli where
  toFun := ![.I, .X, .Y, .Z]
  invFun := fun | .I => 0 | .X => 1 | .Y => 2 | .Z => 3
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

private lemma pauliString_word {N : ℕ} (a : Fin N → Fin 4) :
    tensorOp (fun k => sigma (a k)) = wordOp (fun k => pauliLabelEquiv (a k)) := by
  ext x y
  simp only [wordOp, tensorOp, Matrix.of_apply]
  apply Finset.prod_congr rfl
  intro k _
  generalize a k = j
  fin_cases j <;> rfl

private lemma pauliString_trace_pair {N : ℕ} (a b : Fin N → Fin 4) :
    Matrix.trace (tensorOp (fun k => sigma (a k)) * tensorOp (fun k => sigma (b k))) =
      if a = b then (2 : ℂ) ^ N else 0 := by
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
    (1 / 4 ^ N : ℝ) = ∏ _k : Fin N, (1 / 4 : ℝ) := by simp
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
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hl]
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
  have he : marginal χ k =
      D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
        (χ.submatrix (Equiv.funSplitAt k (Fin 4)).symm
          (Equiv.funSplitAt k (Fin 4)).symm) := by
    ext i j
    exact marginal_split χ k i j
  rw [he]
  exact D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
    (hχ.submatrix (Equiv.funSplitAt k (Fin 4)).symm)

private lemma marginalApprox_psd {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (hχ : χ.PosSemidef) :
    (productMap (fun _ => Fin 4) (marginal χ)).PosSemidef := by
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

private lemma productMatrix_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M L : ι → Matrix (Fin 4) (Fin 4) ℂ) :
    productMap (fun _ => Fin 4) M * productMap (fun _ => Fin 4) L =
      productMap (fun _ => Fin 4) (fun k => M k * L k) := by
  classical
  ext a b
  simp only [productMap, Matrix.mul_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

private lemma productMatrix_star {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Matrix (Fin 4) (Fin 4) ℂ) :
    (productMap (fun _ => Fin 4) M)ᴴ = productMap (fun _ => Fin 4) (fun k => (M k)ᴴ) := by
  ext a b
  simp [productMap, Matrix.conjTranspose_apply]

private lemma productMatrix_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → Fin 4 → ℂ) :
    productMap (fun _ => Fin 4) (fun k => Matrix.diagonal (d k)) =
      Matrix.diagonal (fun a => ∏ k, d k (a k)) := by
  classical
  ext a b
  simp only [productMap, Matrix.diagonal_apply]
  rw [Fintype.prod_ite_zero]
  simp only [← funext_iff]

private lemma productMatrix_one (ι : Type*) [Fintype ι] [DecidableEq ι] :
    productMap (fun _ => Fin 4) (fun _ : ι => (1 : Matrix (Fin 4) (Fin 4) ℂ)) = 1 := by
  simpa only [Matrix.diagonal_one, Finset.prod_const_one] using
    productMatrix_diagonal (fun _ : ι => fun _ : Fin 4 => (1 : ℂ))

private lemma productMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → Matrix.unitaryGroup (Fin 4) ℂ) :
    (productMap (fun _ => Fin 4) (fun k => (U k : Matrix (Fin 4) (Fin 4) ℂ)))ᴴ *
      productMap (fun _ => Fin 4) (fun k => (U k : Matrix (Fin 4) (Fin 4) ℂ)) = 1 := by
  rw [productMatrix_star, productMatrix_mul]
  have he (k : ι) : (U k : Matrix (Fin 4) (Fin 4) ℂ)ᴴ * U k = 1 :=
    Unitary.coe_star_mul_self (U k)
  simp_rw [he]
  exact productMatrix_one ι

set_option maxHeartbeats 1000000 in
-- Splitting a tensor coordinate elaborates dependent finite-product instances.
private lemma marginal_product_unitary {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ)
    (U : Fin N → Matrix.unitaryGroup (Fin 4) ℂ) (k : Fin N) :
    marginal ((productMap (fun _ => Fin 4) (fun l => (U l : Matrix (Fin 4) (Fin 4) ℂ)))ᴴ * χ *
      productMap (fun _ => Fin 4) (fun l => (U l : Matrix (Fin 4) (Fin 4) ℂ))) k =
      (U k : Matrix (Fin 4) (Fin 4) ℂ)ᴴ * marginal χ k * U k := by
  classical
  let B := {l : Fin N // l ≠ k}
  let e := Equiv.funSplitAt k (Fin 4)
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  let W := productMap (fun _ => Fin 4) (fun l : B => (U l : Matrix (Fin 4) (Fin 4) ℂ))
  have hm (A : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) :
      D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight (E A) =
        marginal A k := by
    ext i j
    exact (marginal_split A k i j).symm
  have hs (A : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) :
      E Aᴴ = (E A)ᴴ := rfl
  have hprod : E (productMap (fun _ => Fin 4) (fun l => (U l : Matrix (Fin 4) (Fin 4) ℂ))) =
      Matrix.kronecker (U k : Matrix (Fin 4) (Fin 4) ℂ) W := by
    ext ⟨i, z⟩ ⟨j, w⟩
    change (∏ l, (U l : Matrix (Fin 4) (Fin 4) ℂ)
      ((e.symm (i,z)) l) ((e.symm (j,w)) l)) =
      (U k : Matrix (Fin 4) (Fin 4) ℂ) i j *
        ∏ l : B, (U l : Matrix (Fin 4) (Fin 4) ℂ) (z l) (w l)
    rw [Fintype.prod_eq_mul_prod_compl k]
    have hcoord (t : Fin 4) (v : B → Fin 4) : (e.symm (t,v)) k = t :=
      congrArg Prod.fst (e.apply_symm_apply (t,v))
    rw [hcoord, hcoord]
    congr 1
    rw [Finset.prod_subtype _ (p := fun l : Fin N => l ≠ k) (by simp)]
    apply Finset.prod_congr rfl
    intro l _
    have hrest (t : Fin 4) (v : B → Fin 4) : (e.symm (t,v)) l = v l :=
      congrFun (congrArg Prod.snd (e.apply_symm_apply (t,v))) l
    rw [hrest, hrest]
  have hW : W * Wᴴ = 1 :=
    mul_eq_one_comm.mp (productMatrix_unitary (fun l : B => U l))
  rw [← hm, map_mul, map_mul, hs, hprod]
  simpa only [Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose, hm] using
    D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.trace_local_right
      (E χ) (U k : Matrix (Fin 4) (Fin 4) ℂ)ᴴ Wᴴ
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hW)

private lemma quantum_overlap {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ)
    (hχ : χ.PosSemidef) (ht : Matrix.trace χ = 1)
    (hc : ∀ p : (Fin N → Fin 4) → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
      (1 / 4 ^ N : ℝ) ≤
        ∑ x, p x * ∏ k, ∑ y, if y k = x k then p y else 0) :
    (1 / 4 ^ N : ℝ) ≤ (Matrix.trace (χ * (productMap (fun _ => Fin 4) (marginal χ)))).re := by
  classical
  let U (k : Fin N) := (marginal_psd χ hχ k).1.eigenvectorUnitary
  let lam (k : Fin N) := (marginal_psd χ hχ k).1.eigenvalues
  let V := productMap (fun _ => Fin 4) (fun k => (U k : Matrix (Fin 4) (Fin 4) ℂ))
  let Ψ := Vᴴ * χ * V
  have hVV : V * Vᴴ = 1 := mul_eq_one_comm.mp (productMatrix_unitary U)
  have hΨ : Ψ.PosSemidef := hχ.conjTranspose_mul_mul_same V
  have htΨ : Matrix.trace Ψ = 1 := by
    dsimp [Ψ]
    rw [Matrix.trace_mul_cycle, hVV, Matrix.one_mul, ht]
  have hdiag (k : Fin N) : (U k : Matrix (Fin 4) (Fin 4) ℂ)ᴴ * marginal χ k * U k =
      Matrix.diagonal (fun j => (lam k j : ℂ)) := by
    simpa only [U, lam, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
      using (marginal_psd χ hχ k).1.conjStarAlgAut_star_eigenvectorUnitary
  have hmg (k : Fin N) : marginal Ψ k = Matrix.diagonal (fun j => (lam k j : ℂ)) := by
    exact (marginal_product_unitary χ U k).trans (hdiag k)
  let p (x : Fin N → Fin 4) := (Ψ x x).re
  have hp (x) : 0 ≤ p x := (Complex.nonneg_iff.mp hΨ.diag_nonneg).1
  have hps : ∑ x, p x = 1 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Complex.one_re, p] using
      congrArg Complex.re htΨ
  have hq (k : Fin N) (j : Fin 4) : (∑ y, if y k = j then p y else 0) = lam k j := by
    have he : (∑ y, if y k = j then p y else 0) = (marginal Ψ k j j).re := by
      simp only [marginal, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y k = j
      · simp only [ite_eq_left hy]
        rw [← hy, Function.update_eq_self]
      · simp [hy]
    rw [he, hmg, Matrix.diagonal_apply_eq, Complex.ofReal_re]
  have hA : Vᴴ * (productMap (fun _ => Fin 4) (marginal χ)) * V =
      Matrix.diagonal (fun x => ((∏ k, lam k (x k) : ℝ) : ℂ)) := by
    change (productMap (fun _ => Fin 4) (fun k => (U k : Matrix (Fin 4) (Fin 4) ℂ)))ᴴ *
      productMap (fun _ => Fin 4) (fun k => marginal χ k) *
      productMap (fun _ => Fin 4) (fun k => U k) = _
    rw [productMatrix_star, productMatrix_mul, productMatrix_mul]
    simp_rw [hdiag]
    rw [productMatrix_diagonal]
    simp only [Complex.ofReal_prod]
  have htr : Matrix.trace (Ψ * (Vᴴ * (productMap (fun _ => Fin 4) (marginal χ)) * V)) =
      Matrix.trace (χ * (productMap (fun _ => Fin 4) (marginal χ))) := by
    have he : Ψ * (Vᴴ * productMap (fun _ => Fin 4) (marginal χ) * V) =
        Vᴴ * (χ * productMap (fun _ => Fin 4) (marginal χ)) * V := by
      dsimp [Ψ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc V Vᴴ, hVV, Matrix.one_mul]
    rw [he, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]
  have hb := hc p hp hps
  simp_rw [hq] at hb
  calc
    _ ≤ ∑ x, p x * ∏ k, lam k (x k) := hb
    _ = _ := by
      rw [← htr, hA]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal,
        Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, p]

private lemma sqFidelity_overlap {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    (Matrix.trace (ρ * σ)).re ≤ sqFidelity ρ σ := by
  classical
  let A := CFC.sqrt ρ * σ * CFC.sqrt ρ
  let S := CFC.sqrt A
  have hρs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).1.eq
  have hA : A.PosSemidef := by
    simpa only [hρs] using hσ.conjTranspose_mul_mul_same (CFC.sqrt ρ)
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hgram : Matrix.trace A = Matrix.trace (ρ * σ) := by
    dsimp [A]
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
  calc
    (Matrix.trace (ρ * σ)).re = (Matrix.trace (S * S)).re := by
      rw [show S * S = A from CFC.sqrt_mul_sqrt_self _ hA.nonneg, hgram]
    _ ≤ (Matrix.trace S).re ^ 2 :=
      D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.psd_trace_sq S hS
    _ = sqFidelity ρ σ := rfl

private lemma shift_expansion (N : ℕ) :
    ∑ a, shiftCoeff N a • tensorOp (fun k => sigma (a k)) = (qubitPermutation (finRotate N))ᵀ := by
  classical
  simp only [shiftCoeff, pauliString_word]
  let e : (Fin N → Fin 4) ≃ (Fin N → Pauli) :=
    Equiv.piCongrRight fun _ => pauliLabelEquiv
  exact (e.sum_comp (fun a => (((2 : ℂ) ^ N)⁻¹ *
    Matrix.trace (wordOp a * (qubitPermutation (finRotate N))ᵀ)) • wordOp a)).trans
    (word_expansion ((qubitPermutation (finRotate N))ᵀ)).symm

private lemma shift_unitary (N : ℕ) :
    ((qubitPermutation (finRotate N))ᵀ)ᴴ * (qubitPermutation (finRotate N))ᵀ = 1 := by
  classical
  let e : Equiv.Perm (Fin N → Fin 2) := (finRotate N).symm.arrowCongr (Equiv.refl (Fin 2))
  have he : (qubitPermutation (finRotate N))ᵀ = (e.permMatrix ℂ)ᵀ := by
    ext x y
    simp [qubitPermutation, Matrix.transpose_apply, Matrix.of_apply, e,
      Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.arrowCongr, eq_comm]
  rw [he, Matrix.transpose_permMatrix]
  exact Unitary.coe_star_mul_self
    (D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.permutationUnitary e⁻¹)

private lemma shift_cptp (N : ℕ)
    (he : ∑ a, shiftCoeff N a • tensorOp (fun k => sigma (a k)) = (qubitPermutation (finRotate N))ᵀ)
    (hu : ((qubitPermutation (finRotate N))ᵀ)ᴴ * (qubitPermutation (finRotate N))ᵀ = 1) :
    IsProcessCPTP (rankOneDensity (shiftCoeff N)) := by
  classical
  refine ⟨Matrix.posSemidef_vecMulVec_self_star (shiftCoeff N), ?_⟩
  have hstar : (∑ a, star (shiftCoeff N a) • tensorOp (fun k => sigma (a k))) =
      ((qubitPermutation (finRotate N))ᵀ)ᴴ := by
    have h := congrArg (fun A : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ => Aᴴ) he
    simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      pauliString_word, word_hermitian] using h
  calc
    _ = (∑ b, star (shiftCoeff N b) • tensorOp (fun k => sigma (b k))) *
        (∑ a, shiftCoeff N a • tensorOp (fun k => sigma (a k))) := by
      rw [Matrix.sum_mul]
      simp only [Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply]
      rw [Finset.sum_comm]
    _ = 1 := by rw [hstar, he, hu]

private def shiftTrace (N : ℕ) (a : Fin N → Fin 4) : ℂ :=
  ∑ x : Fin N → Fin 2, ∏ l, sigma (a l) (x l) (x (finRotate N l))

private lemma shiftCoeff_trace (N : ℕ) (a : Fin N → Fin 4) :
    shiftCoeff N a = (2 ^ N : ℂ)⁻¹ * shiftTrace N a := by
  classical
  simp only [shiftCoeff, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, qubitPermutation,
    Matrix.transpose_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, shiftTrace, tensorOp, Function.comp_apply]

set_option maxHeartbeats 1000000 in
-- The coordinate sums combine Pauli completeness with two distinct wire coordinates.
private lemma shift_trace_contraction (N : ℕ) (hN : 2 ≤ N) (k : Fin N) (i j : Fin 4) :
    (∑ z : {l : Fin N // l ≠ k} → Fin 4,
      shiftTrace N ((Equiv.funSplitAt k (Fin 4)).symm (i, z)) *
        star (shiftTrace N ((Equiv.funSplitAt k (Fin 4)).symm (j, z)))) =
      ((2 : ℂ) ^ N) ^ 2 * (if i = j then (1 / 4 : ℂ) else 0) := by
  classical
  let B := {l : Fin N // l ≠ k}
  let e := Equiv.funSplitAt k (Fin 4)
  let A (i : Fin 4) (z : B → Fin 4) (x : Fin N → Fin 2) :=
    ∏ l, sigma ((e.symm (i,z)) l) (x l) (x (finRotate N l))
  have hm : finRotate N k ≠ k := Equiv.Perm.mem_support.mp (by
    rw [support_finRotate_of_le hN]
    exact Finset.mem_univ k)
  have hB : Fintype.card B = N - 1 := by
    simp [B]
  have hcomplete (u v u' v' : Fin 2) :
      (∑ a : Fin 4, sigma a u v * star (sigma a u' v')) =
        if u = u' ∧ v = v' then (2 : ℂ) else 0 := by
    fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v' <;>
      norm_num [sigma, pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Fin.sum_univ_succ]
  have horth (i j : Fin 4) :
      (∑ u : Fin 2, ∑ v : Fin 2, sigma i u v * star (sigma j u v)) =
        if i = j then (2 : ℂ) else 0 := by
    have hi : sigma i = pauliMatrix (pauliLabelEquiv i) := by fin_cases i <;> rfl
    have hj : sigma j = pauliMatrix (pauliLabelEquiv j) := by fin_cases j <;> rfl
    have hs := D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian
      (pauliLabelEquiv j)
    have hh (u v : Fin 2) : star (sigma j u v) = sigma j v u := by
      rw [hj]
      exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M v u) hs
    simp_rw [hh]
    change Matrix.trace (sigma i * sigma j) = _
    rw [hi, hj,
      D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_trace_pair]
    simp only [Equiv.apply_eq_iff_eq]
  have hprod (i : Fin 4) (z : B → Fin 4) (x : Fin N → Fin 2) :
      A i z x = sigma i (x k) (x (finRotate N k)) *
        ∏ l : B, sigma (z l) (x l) (x (finRotate N l)) := by
    dsimp [A]
    rw [Fintype.prod_eq_mul_prod_compl k]
    have hc : (e.symm (i,z)) k = i := congrArg Prod.fst (e.apply_symm_apply (i,z))
    rw [hc]
    congr 1
    rw [Finset.prod_subtype _ (p := fun l : Fin N => l ≠ k) (by simp)]
    apply Finset.prod_congr rfl
    intro l _
    have hr : (e.symm (i,z)) l = z l :=
      congrFun (congrArg Prod.snd (e.apply_symm_apply (i,z))) l
    rw [hr]
  have hconstraint (x y : Fin N → Fin 2) :
      (∀ l : B, x l = y l ∧ x (finRotate N l) = y (finRotate N l)) ↔ x = y := by
    constructor
    · intro h
      funext l
      by_cases hl : l = k
      · subst l
        have hp : (finRotate N).symm k ≠ k := by
          intro h'
          apply hm
          calc
            finRotate N k = finRotate N ((finRotate N).symm k) := congrArg _ h'.symm
            _ = k := (finRotate N).apply_symm_apply k
        simpa only [Equiv.apply_symm_apply] using (h ⟨(finRotate N).symm k,hp⟩).2
      · exact (h ⟨l,hl⟩).1
    · rintro rfl l
      exact ⟨rfl,rfl⟩
  have hgram (x y : Fin N → Fin 2) :
      (∑ z : B → Fin 4, A i z x * star (A j z y)) =
        (sigma i (x k) (x (finRotate N k)) * star (sigma j (y k) (y (finRotate N k)))) *
          (2 : ℂ) ^ (N - 1) * (if x = y then 1 else 0) := by
    have hsum := Finset.prod_univ_sum (fun _ : B => (Finset.univ : Finset (Fin 4)))
      (fun l a => sigma a (x l) (x (finRotate N l)) *
        star (sigma a (y l) (y (finRotate N l))))
    rw [Fintype.piFinset_univ] at hsum
    calc
      _ = (sigma i (x k) (x (finRotate N k)) * star (sigma j (y k) (y (finRotate N k)))) *
          (∑ z : B → Fin 4, ∏ l : B, sigma (z l) (x l) (x (finRotate N l)) *
            star (sigma (z l) (y l) (y (finRotate N l)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        rw [hprod, hprod, star_mul, star_prod, Finset.prod_mul_distrib]
        ring
      _ = _ := by
        rw [← hsum]
        simp_rw [hcomplete]
        rw [Fintype.prod_ite_zero]
        simp only [hconstraint, Finset.prod_const, Finset.card_univ, hB]
        split_ifs <;> ring
  let t : B := ⟨finRotate N k, hm⟩
  let C := {l : B // l ≠ t}
  let ex := Equiv.funSplitAt k (Fin 2)
  let ey := Equiv.funSplitAt t (Fin 2)
  have hC : Fintype.card C = N - 2 := by
    simp [C, hB, Nat.sub_sub]
  have hpairs : (∑ x : Fin N → Fin 2,
      sigma i (x k) (x (finRotate N k)) * star (sigma j (x k) (x (finRotate N k)))) =
      (2 : ℂ) ^ (N - 2) * (if i = j then 2 else 0) := by
    have hx0 (u : Fin 2) (z : B → Fin 2) : (ex.symm (u,z)) k = u :=
      congrArg Prod.fst (ex.apply_symm_apply (u,z))
    have hx1 (u : Fin 2) (z : B → Fin 2) : (ex.symm (u,z)) (finRotate N k) = z t :=
      congrFun (congrArg Prod.snd (ex.apply_symm_apply (u,z))) t
    have hy (v : Fin 2) (w : C → Fin 2) : (ey.symm (v,w)) t = v :=
      congrArg Prod.fst (ey.apply_symm_apply (v,w))
    calc
      _ = ∑ u : Fin 2, ∑ v : Fin 2, ∑ _w : C → Fin 2,
          sigma i u v * star (sigma j u v) := by
        rw [← ex.symm.sum_comp, Fintype.sum_prod_type]
        simp only [hx0, hx1]
        apply Finset.sum_congr rfl
        intro u _
        rw [← ey.symm.sum_comp, Fintype.sum_prod_type]
        simp only [hy]
        rfl
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, hC, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        simp_rw [← Finset.mul_sum]
        rw [horth]
  have hpow : (2 : ℂ) ^ N = (2 : ℂ) ^ (N - 2) * 4 := by
    conv_lhs => rw [← Nat.sub_add_cancel hN]
    rw [pow_add]
    norm_num
  have hpowB : (2 : ℂ) ^ (N - 1) = (2 : ℂ) ^ (N - 2) * 2 := by
    rw [show N - 1 = N - 2 + 1 by omega, pow_succ]
  change (∑ z : B → Fin 4, (∑ x, A i z x) * star (∑ y, A j z y)) = _
  simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ x, ∑ y, ∑ z : B → Fin 4, A i z x * star (A j z y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = (2 : ℂ) ^ (N - 1) *
        (∑ x : Fin N → Fin 2, sigma i (x k) (x (finRotate N k)) *
          star (sigma j (x k) (x (finRotate N k)))) := by
      simp_rw [hgram, mul_ite, mul_one, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [← Finset.sum_mul]
      ring
    _ = _ := by
      rw [hpairs, hpow, hpowB]
      split_ifs <;> ring

private lemma shift_marginals (N : ℕ) (hN : 2 ≤ N) :
    ∀ k, marginal (rankOneDensity (shiftCoeff N)) k = (1 / 4 : ℂ) • 1 := by
  classical
  intro k
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [marginal_split]
  have hstar : star ((2 ^ N : ℂ)⁻¹) = (2 ^ N : ℂ)⁻¹ := by simp
  simp only [rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply, shiftCoeff_trace,
    star_mul, hstar]
  have he (z : {l : Fin N // l ≠ k} → Fin 4) :
      (2 ^ N : ℂ)⁻¹ * shiftTrace N ((Equiv.funSplitAt k (Fin 4)).symm (i, z)) *
        (star (shiftTrace N ((Equiv.funSplitAt k (Fin 4)).symm (j, z))) *
          (2 ^ N : ℂ)⁻¹) =
      ((2 ^ N : ℂ)⁻¹) ^ 2 *
        (shiftTrace N ((Equiv.funSplitAt k (Fin 4)).symm (i, z)) *
          star (shiftTrace N ((Equiv.funSplitAt k (Fin 4)).symm (j, z)))) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, shift_trace_contraction N hN k i j]
  have hd : (2 ^ N : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  split_ifs <;> field_simp [hd]

private lemma shift_fidelity (N : ℕ)
    (hχ : IsProcessCPTP (rankOneDensity (shiftCoeff N)))
    (hm : ∀ k, marginal (rankOneDensity (shiftCoeff N)) k = (1 / 4 : ℂ) • 1) :
    sqFidelity (rankOneDensity (shiftCoeff N))
      (productMap (fun _ => Fin 4) (marginal (rankOneDensity (shiftCoeff N)))) = 1 / 4 ^ N := by
  classical
  let c : ℝ := 1 / 4 ^ N
  have hc : 0 ≤ c := by positivity
  have ht : Matrix.trace (rankOneDensity (shiftCoeff N)) = 1 := process_trace _ hχ
  have hnorm : star (shiftCoeff N) ⬝ᵥ shiftCoeff N = 1 := by
    rw [dotProduct_comm]
    simpa only [rankOneDensity, Matrix.trace_vecMulVec] using ht
  have hidem : rankOneDensity (shiftCoeff N) * rankOneDensity (shiftCoeff N) =
      rankOneDensity (shiftCoeff N) :=
    (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake (shiftCoeff N) hnorm 1).1
  have hroot : CFC.sqrt (rankOneDensity (shiftCoeff N)) = (rankOneDensity (shiftCoeff N)) :=
    CFC.sqrt_unique hidem hχ.1.nonneg
  have hmarg : productMap (fun _ => Fin 4) (marginal (rankOneDensity (shiftCoeff N))) =
      (c : ℂ) • 1 := by
    ext a b
    simp only [productMap, hm, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    by_cases hab : a = b
    · subst b
      simp [c]
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
      rw [ite_eq_right hab]
      simp only [mul_zero]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
  have hsqrt : CFC.sqrt ((c : ℂ) • (rankOneDensity (shiftCoeff N))) =
      (Real.sqrt c : ℂ) • (rankOneDensity (shiftCoeff N)) := by
    apply CFC.sqrt_unique
    · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hidem,
        ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
    · exact (hχ.1.smul (Complex.zero_le_real.mpr (Real.sqrt_nonneg c))).nonneg
  rw [sqFidelity, hroot, hmarg, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    hidem, hsqrt, Matrix.trace_smul, ht, smul_eq_mul, mul_one, Complex.ofReal_re,
    Real.sq_sqrt hc]

/-- The bound holds for every process matrix; cyclic shifts attain it for at least two qubits. -/
theorem result : claim := by
  constructor
  · intro N _ χ hχ
    exact (quantum_overlap χ hχ.1 (process_trace χ hχ) classical_overlap).trans
      (sqFidelity_overlap χ (productMap (fun _ => Fin 4) (marginal χ)) hχ.1
        (marginalApprox_psd χ hχ.1))
  · intro N hN
    have he := shift_expansion N
    have hχ := shift_cptp N he (shift_unitary N)
    have hm := shift_marginals N hN
    exact ⟨he, hχ, hm, shift_fidelity N hχ hm⟩


end D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity
