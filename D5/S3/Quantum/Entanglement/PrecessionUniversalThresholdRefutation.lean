/- GID: D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.claim; result=D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.result; claim=D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation.claim
   digest: Singlet padding refutes the universal precession threshold for genuine entanglement. -/
/-
proof_shape: site_hermitian: bind-only (consumers: ensemble_hermitian)
proof_shape: spin_hermitian: bind-only (consumers: ensemble_hermitian, padded_precession_score)
proof_shape: ensemble_hermitian: bind-only (consumers: ensembleQ, singlet_padding_ensemble_score, padded_precession_score)
proof_shape: cfc_eigenmatrix: bind-only (consumers: cfc_intertwining, spin_three_score)
proof_shape: cfc_intertwining: bind-only (consumers: singlet_padding_pos_trace, pos_submatrix_equiv)
proof_shape: singlet_padding_pos_trace: bind-only (consumers: singlet_padding_score)
proof_shape: singlet_padding_score: bind-only (consumers: singlet_padding_ensemble_score)
proof_shape: pos_submatrix_equiv: bind-only (consumers: singlet_padding_ensemble_score, padded_precession_score)
proof_shape: spin_three_Jx: bind-only (consumers: spin_three_score)
proof_shape: spin_three_Jy: bind-only (consumers: spin_three_score)
proof_shape: four_gram: bind-only (consumers: spin_three_score)
proof_shape: four_eigenbasis: bind-only (consumers: spin_three_score)
proof_shape: four_positive_matrix: bind-only (consumers: spin_three_score)
proof_shape: spin_three_rotation: bind-only (consumers: spin_three_score)
proof_shape: spin_three_score: bind-only (consumers: padded_precession_score)
proof_shape: pair_singlet_annihilation: bind-only (consumers: singlet_padding_ensemble_score)
proof_shape: site_cons: bind-only (consumers: padded_ensemble_entry)
proof_shape: padded_ensemble_entry: bind-only (consumers: singlet_padding_ensemble_score)
proof_shape: singlet_padding_ensemble_score: bind-only (consumers: padded_precession_score; result live path)
proof_shape: pair_rest_product: bind-only (consumers: result)
proof_shape: pos_congr: bind-only (consumers: singlet_padding_ensemble_score, padded_precession_score)
proof_shape: padded_precession_score: bind-only (consumers: result)
proof_shape: result: bind-only
escape_witness: none
The expanded helper proofs instantiate the frozen spin and state definitions,
  Mathlib spectral decompositions and tensor laws. Spectral-support coefficients
  follow by scalar cancellation; the remaining steps construct finite convex
  witnesses or normalize finite site sums, matrix identities and scores.
The general bridge identifies the literal padded observables for every
  spin list, every K and every matrix sigma; its tuple splitting, identity
  products, sum decomposition and spectral transport use only these laws.
admission_basis: open-problem-resolution (#13586; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound; module statement_id sha256:67dfbfec9f7079cdab0c268ebc937dd2e98663e2b481056b9f040d347de75cda
    D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound.IsDensity: sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448
  D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound; module statement_id sha256:fbc446c4314bd47628ff448ec274cb3001f13b9b713e94a7d3a6298d898e2f08
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.positiveWeight: sha256:d9dd1bb6c83470a26764f2a3e6356a58bab1d9c341fba0078562bdab2bbf8926
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.c: sha256:7f19041ac051a19e442a44b180bb9fd67d4dbf9b8de8e2103b65f1b9f2b48d9f
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jx: sha256:b8a9852c9ba582ad29adb067f1a840ffc760c07c89a3da47991448382d636b76
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jy: sha256:132cb309f9fc2fc02d367f6e1279f55f2dbe0b717b0380885ffd578ba342be5c
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.pos: sha256:5576d7ed01cccb09aa2a2ee4877c87fe491ebf8f4ce54507ff957d524db83402
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.Jplus: sha256:4cc1a59229cda4db37af848514692a4da6ca1cbdf9af77250b7776f9bf491024
    D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.theta: sha256:c09c51ad8712aabc11ac4a582e5f2a69a066c99a0a56fa10192ead6a10f497ef
  D5/S3/Resource/CompositeConeProperness; module statement_id sha256:3243cde25ee505dd46503acdcf41b259db2a9d66757344fdd34f006445473595
    D5.S3.Resource.CompositeConeProperness.singletMatrix: sha256:90b05a599831d848967126f78bd545bed12b84382b4318acbeec3f558111c74a
    D5.S3.Resource.CompositeConeProperness.antisymmetricVector: sha256:cc5a9c7bd56057ff53fe5833c62d958f31795a36c8b3413a349daf6a93275d9c
    D5.S3.Resource.CompositeConeProperness.singletMatrix_posSemidef: sha256:e5de16539b2f92231f69ec6414837470e3ec36c028c4a88eb0c77b527c519f53
Escape-audit registration is paused under CLAUDE.md §3.9.
-/
import D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
import D5.S3.Resource.CompositeConeProperness
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound

noncomputable section
open Matrix Complex
open scoped BigOperators Matrix Kronecker ComplexOrder
namespace D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
open D5.S3.Resource.CompositeConeProperness
open D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound (IsDensity)

/-- A local spin operator tensored with the identity at every other site. -/
def siteOperator {N : ℕ} (j : Fin N → ℕ) (n : Fin N)
    (A : Matrix (Fin (j n + 1)) (Fin (j n + 1)) ℂ) :
    Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ :=
  fun x y => A (x n) (y n) * ∏ r ∈ Finset.univ.erase n,
    if x r = y r then 1 else 0

private theorem site_hermitian {N : ℕ} (j : Fin N → ℕ) (n : Fin N)
    (A : Matrix (Fin (j n + 1)) (Fin (j n + 1)) ℂ) (hA : A.IsHermitian) :
    (siteOperator j n A).IsHermitian := by
  ext x y
  have he : star (A (y n) (x n)) = A (x n) (y n) :=
    congrArg (fun M : Matrix _ _ ℂ => M (x n) (y n)) hA.eq
  simp [conjTranspose_apply, siteOperator, map_mul, map_prod, he, eq_comm]

private theorem spin_hermitian (n : ℕ) :
    (Jx n).IsHermitian ∧ (Jy n).IsHermitian := by
  constructor
  · exact (isHermitian_add_transpose_self (Jplus n)).smul (by simp)
  · change ((1 / (2 * I) : ℂ) • (Jplus n - (Jplus n)ᴴ))ᴴ = _
    rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    have hc : star (1 / (2 * I) : ℂ) = -(1 / (2 * I) : ℂ) := by simp
    rw [hc, ← neg_sub (Jplus n) (Jplus n)ᴴ, neg_smul, smul_neg, neg_neg]
    rfl

/-- The literal total angular momentum in the k-th precession direction. -/
def ensembleJ {N : ℕ} (j : Fin N → ℕ) (K : ℕ) (k : Fin K) :
    Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ :=
  (Real.cos (theta K k) : ℂ) • ∑ n, siteOperator j n (Jx (j n)) +
    (Real.sin (theta K k) : ℂ) • ∑ n, siteOperator j n (Jy (j n))

private theorem ensemble_hermitian {N : ℕ} (j : Fin N → ℕ) (K : ℕ) (k : Fin K) :
    (ensembleJ j K k).IsHermitian := by
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.smul
    · exact isSelfAdjoint_sum _ (fun n _ => site_hermitian j n _ (spin_hermitian _).1)
    · simp only [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
  · apply Matrix.IsHermitian.smul
    · exact isSelfAdjoint_sum _ (fun n _ => site_hermitian j n _ (spin_hermitian _).2)
    · simp only [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]

/-- The finite average of the source's positive spectral weights. -/
def ensembleQ {N : ℕ} (j : Fin N → ℕ) (K : ℕ) :
    Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ :=
  (1 / K : ℂ) • ∑ k : Fin K, pos (ensemble_hermitian j K k)

/-- The piecewise threshold printed immediately before Conjecture 3. -/
def conjecturedThreshold (K : ℕ) : ℝ :=
  if K = 3 then 23 / 32 else if K = 5 then (69 + Real.sqrt 181) / 128
    else 1 / 2 * (1 + c K * (K - 1 : ℕ) / (K + 1 : ℕ))

/-- A normalized finite convex combination of products across one bipartition. -/
def SeparableAcross {N : ℕ} (j : Fin N → ℕ) (S : Finset (Fin N))
    (rho : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ) : Prop :=
  ∃ (m : ℕ) (p : Fin m → ℝ)
    (A : Fin m → Matrix (∀ n : S, Fin (j n + 1)) (∀ n : S, Fin (j n + 1)) ℂ)
    (B : Fin m → Matrix (∀ n : ↥Sᶜ, Fin (j n + 1)) (∀ n : ↥Sᶜ, Fin (j n + 1)) ℂ),
    (∀ r, 0 ≤ p r) ∧ (∑ r, p r) = 1 ∧
    (∀ r, IsDensity (A r) ∧ IsDensity (B r)) ∧
    ∀ x y, rho x y = ∑ r, (p r : ℂ) *
      A r (fun n => x n) (fun n => y n) * B r (fun n => x n) (fun n => y n)

/-- GME excludes convex mixtures of states separable across nontrivial cuts. -/
def SpinGME {N : ℕ} (j : Fin N → ℕ)
    (rho : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ) : Prop :=
  ¬ ∃ (m : ℕ) (p : Fin m → ℝ) (S : Fin m → Finset (Fin N))
    (sigma : Fin m → Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ),
    (∀ r, 0 ≤ p r) ∧ (∑ r, p r) = 1 ∧
    (∀ r, (S r).Nonempty ∧ ((S r)ᶜ).Nonempty ∧
      IsDensity (sigma r) ∧ SeparableAcross j (S r) (sigma r)) ∧
    rho = ∑ r, (p r : ℂ) • sigma r

/-- Huynh-Vu–Zaw–Scarani Conjecture 3, for arbitrary positive half-integer spins. -/
def claim : Prop :=
  ∀ (K : ℕ), Odd K → 3 ≤ K → ∀ (N : ℕ), 2 ≤ N →
    ∀ (j : Fin N → ℕ), (∀ n, 1 ≤ j n) →
    ∀ (rho : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ),
    IsDensity rho → conjecturedThreshold K < (trace (rho * ensembleQ j K)).re → SpinGME j rho

private theorem cfc_eigenmatrix {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (V : Matrix ι κ ℂ) (lam : κ → ℝ)
    (hAV : A * V = V * diagonal (fun i => (lam i : ℂ))) (f : ℝ → ℝ) :
    hA.cfc f * V = V * diagonal (fun i => (f (lam i) : ℂ)) := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hs : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose, U]
      using hA.spectral_theorem
  have hR : diagonal (fun i => (hA.eigenvalues i : ℂ)) * (Uᴴ * V) =
      (Uᴴ * V) * diagonal (fun i => (lam i : ℂ)) := by
    have h := congrArg (fun M => Uᴴ * M) hAV
    rw [hs] at h
    simp only [Matrix.mul_assoc] at h
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul] at h
    simpa only [Matrix.mul_assoc] using h
  have hfR : diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * (Uᴴ * V) =
      (Uᴴ * V) * diagonal (fun i => (f (lam i) : ℂ)) := by
    ext i j
    have h := congrArg (fun M : Matrix ι κ ℂ => M i j) hR
    simp only [diagonal_mul, mul_diagonal] at h ⊢
    by_cases he : hA.eigenvalues i = lam j
    · rw [he, mul_comm]
    · have hn : (hA.eigenvalues i : ℂ) - (lam j : ℂ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast he)
      have hz : (Uᴴ * V) i j = 0 :=
        (mul_eq_zero.mp (show ((hA.eigenvalues i : ℂ) - (lam j : ℂ)) * (Uᴴ * V) i j = 0
          by linear_combination h)).resolve_left hn
      rw [hz, mul_zero, zero_mul]
  have h := congrArg (fun M => U * M) hfR
  simp only [Matrix.mul_assoc] at h
  rw [← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul] at h
  simpa only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose,
    U, Matrix.mul_assoc] using h

private theorem cfc_intertwining {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (V : Matrix ι κ ℂ)
    (hAV : A * V = V * B) (f : ℝ → ℝ) : hA.cfc f * V = V * hB.cfc f := by
  let W : Matrix κ κ ℂ := hB.eigenvectorUnitary
  have hW : Wᴴ * W = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hW' : W * Wᴴ = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hsB : B = W * diagonal (fun i => (hB.eigenvalues i : ℂ)) * Wᴴ := by
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose, W]
      using hB.spectral_theorem
  have hBW : B * W = W * diagonal (fun i => (hB.eigenvalues i : ℂ)) := by
    calc
      B * W = (W * diagonal (fun i => (hB.eigenvalues i : ℂ)) * Wᴴ) * W :=
        congrArg (fun M => M * W) hsB
      _ = W * diagonal (fun i => (hB.eigenvalues i : ℂ)) := by
        rw [Matrix.mul_assoc, hW, Matrix.mul_one]
  have hAVW : A * (V * W) = (V * W) * diagonal (fun i => (hB.eigenvalues i : ℂ)) := by
    rw [← Matrix.mul_assoc, hAV, Matrix.mul_assoc, hBW, ← Matrix.mul_assoc]
  have h := cfc_eigenmatrix hA (V * W) hB.eigenvalues hAVW f
  have hh := congrArg (fun M => M * Wᴴ) h
  simp only [Matrix.mul_assoc] at hh
  rw [hW', Matrix.mul_one] at hh
  simpa only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose,
    W, Matrix.mul_assoc] using hh

private theorem singlet_padding_pos_trace {κ : Type} [Fintype κ] [DecidableEq κ]
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (B sigma : Matrix κ κ ℂ) (hB : B.IsHermitian)
    (hzero : P *ᵥ antisymmetricVector = 0)
    (hA : (P ⊗ₖ (1 : Matrix κ κ ℂ) +
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ B).IsHermitian) :
    trace ((((1 / 2 : ℂ) • singletMatrix) ⊗ₖ sigma) * pos hA) = trace (sigma * pos hB) := by
  let V : Matrix ((Fin 2 × Fin 2) × κ) κ ℂ :=
    fun i r => antisymmetricVector i.1 * (1 : Matrix κ κ ℂ) i.2 r
  have hV : Vᴴ * V = (2 : ℂ) • (1 : Matrix κ κ ℂ) := by
    ext i j
    simp only [Matrix.mul_apply, conjTranspose_apply]
    by_cases h : i = j
    all_goals simp [V, Fintype.sum_prod_type, Fin.sum_univ_two,
      antisymmetricVector, Matrix.one_apply, h, eq_comm] <;> norm_num
  have hAV : (P ⊗ₖ (1 : Matrix κ κ ℂ) +
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ B) * V = V * B := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, kroneckerMap_apply]
    have hz := congrFun hzero i.1
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hz
    simp [V, Matrix.mul_apply, kroneckerMap, Fintype.sum_prod_type,
      Finset.sum_add_distrib, Matrix.one_apply, mul_add, add_mul,
      Finset.mul_sum, Finset.sum_mul, hz]
    ring
  have hrho : (((1 / 2 : ℂ) • singletMatrix) ⊗ₖ sigma) =
      (1 / 2 : ℂ) • (V * sigma * Vᴴ) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.mul_apply, conjTranspose_apply]
    simp [V, singletMatrix, vecMulVec, Matrix.mul_apply, kroneckerMap,
      Fintype.sum_prod_type, conjTranspose_apply, Matrix.one_apply,
      Finset.mul_sum, Finset.sum_mul, mul_assoc, apply_ite]
    left
    ring
  have ht := cfc_intertwining hA hB V hAV positiveWeight
  change _ = trace (sigma * hB.cfc positiveWeight)
  rw [hrho, Matrix.smul_mul, trace_smul]
  change (1 / 2 : ℂ) * trace (V * sigma * Vᴴ * hA.cfc positiveWeight) = _
  rw [trace_mul_cycle, ← Matrix.mul_assoc, ht, Matrix.mul_assoc,
    trace_mul_cycle, Matrix.mul_assoc sigma Vᴴ, hV]
  simp [Matrix.mul_assoc]

private theorem singlet_padding_score {κ : Type} [Fintype κ] [DecidableEq κ]
    (K : ℕ) (P : Fin K → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (B : Fin K → Matrix κ κ ℂ) (sigma : Matrix κ κ ℂ)
    (hB : ∀ k, (B k).IsHermitian)
    (hzero : ∀ k, P k *ᵥ antisymmetricVector = 0)
    (hA : ∀ k, (P k ⊗ₖ (1 : Matrix κ κ ℂ) +
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ B k).IsHermitian) :
    trace ((((1 / 2 : ℂ) • singletMatrix) ⊗ₖ sigma) *
      ((1 / K : ℂ) • ∑ k, pos (hA k))) =
      trace (sigma * ((1 / K : ℂ) • ∑ k, pos (hB k))) := by
  simp only [Matrix.mul_smul, trace_smul, Finset.mul_sum, trace_sum]
  simp only [singlet_padding_pos_trace (P _) (B _) sigma (hB _) (hzero _) (hA _)]

private theorem pos_submatrix_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix κ κ ℂ} (hA : A.IsHermitian)
    (e : ι ≃ κ) : pos (hA.submatrix e) = (pos hA).submatrix e e := by
  let E : Matrix ι κ ℂ := fun i r => if e i = r then 1 else 0
  have he : A.submatrix e e * E = E * A := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply]
    have hs (q : ι) : e q = j ↔ q = e.symm j := e.eq_symm_apply.symm
    simp [E, hs, mul_ite, ite_mul]
  have h := cfc_intertwining (hA.submatrix e) hA E he positiveWeight
  ext i j
  have hh := congrArg (fun M : Matrix ι κ ℂ => M i (e j)) h
  simp only [Matrix.mul_apply] at hh
  simpa [E, pos, e.injective.eq_iff, mul_ite, ite_mul] using hh

private theorem spin_three_Jx : Jx 3 = !![0, (Real.sqrt 3 : ℂ) / 2, 0, 0; (Real.sqrt 3 : ℂ) / 2, 0, 1, 0;
      0, 1, 0, (Real.sqrt 3 : ℂ) / 2; 0, 0, (Real.sqrt 3 : ℂ) / 2, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Jx, Jplus, Matrix.conjTranspose_apply, Matrix.smul_apply] <;> ring

private theorem spin_three_Jy : Jy 3 = !![0, -I * (Real.sqrt 3 : ℂ) / 2, 0, 0; I * (Real.sqrt 3 : ℂ) / 2, 0, -I, 0;
      0, I, 0, -I * (Real.sqrt 3 : ℂ) / 2; 0, 0, I * (Real.sqrt 3 : ℂ) / 2, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Jy, Jplus, Matrix.conjTranspose_apply, Matrix.smul_apply] <;> ring

private theorem four_gram (a : ℂ) (ha : a ^ 2 = 3) (hca : (starRingEnd ℂ) a = a) :
    let W : Matrix (Fin 4) (Fin 4) ℂ :=
      !![1, a, a, 1; a, 1, -1, -a; a, -1, -1, a; 1, -a, a, -1]
    W * ((1 / 8 : ℂ) • Wᴴ) = 1 := by
    dsimp only

    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, conjTranspose_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_succ, diagonal, Complex.star_def, hca] <;> ring_nf <;> norm_num [ha]

private theorem four_eigenbasis (a : ℂ) (ha : a ^ 2 = 3)
    (hJx : Jx 3 = !![0, a / 2, 0, 0; a / 2, 0, 1, 0;
      0, 1, 0, a / 2; 0, 0, a / 2, 0]) :
    let W : Matrix (Fin 4) (Fin 4) ℂ :=
      !![1, a, a, 1; a, 1, -1, -a; a, -1, -1, a; 1, -a, a, -1]
    let lam : Fin 4 → ℝ := ![3 / 2, 1 / 2, -1 / 2, -3 / 2]
    Jx 3 * W = W * diagonal (fun i => (lam i : ℂ)) := by
  dsimp only
  ext i j
  rw [mul_diagonal, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [hJx, Fin.sum_univ_succ, diagonal] <;> ring_nf <;> norm_num [ha]

private theorem four_positive_matrix (a : ℂ) (ha : a ^ 2 = 3)
    (hca : (starRingEnd ℂ) a = a) :
    let W : Matrix (Fin 4) (Fin 4) ℂ :=
      !![1, a, a, 1; a, 1, -1, -a; a, -1, -1, a; 1, -a, a, -1]
    W * diagonal (![1, 1, 0, 0] : Fin 4 → ℂ) * ((1 / 8 : ℂ) • Wᴴ) =
      !![1 / 2, a / 4, 0, -1 / 4; a / 4, 1 / 2, 1 / 4, 0;
        0, 1 / 4, 1 / 2, a / 4; -1 / 4, 0, a / 4, 1 / 2] := by
  dsimp only
  ext i j
  simp only [Matrix.mul_apply, mul_diagonal, Matrix.smul_apply, conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, diagonal, Complex.star_def, hca] <;> ring_nf <;> norm_num [ha]

private theorem spin_three_rotation (angle : ℝ) (a w : ℂ)
    (hw : w = (Real.cos angle : ℂ) + I * (Real.sin angle : ℂ))
    (hws : star w = w⁻¹) (hw0 : w ≠ 0)
    (hJx : Jx 3 = !![0, a / 2, 0, 0; a / 2, 0, 1, 0;
      0, 1, 0, a / 2; 0, 0, a / 2, 0])
    (hJy : Jy 3 = !![0, -I * a / 2, 0, 0; I * a / 2, 0, -I, 0;
      0, I, 0, -I * a / 2; 0, 0, I * a / 2, 0]) :
    let R : Matrix (Fin 4) (Fin 4) ℂ := diagonal fun i => w ^ i.val
    ((Real.cos angle : ℂ) • Jx 3 + (Real.sin angle : ℂ) • Jy 3) * R =
      R * Jx 3 := by
  dsimp only
  have hBd : (Real.cos angle : ℂ) • Jx 3 + (Real.sin angle : ℂ) • Jy 3 =
      !![0, star w * a / 2, 0, 0; w * a / 2, 0, star w, 0;
        0, w, 0, star w * a / 2; 0, 0, w * a / 2, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hJx, hJy, hw, star_add, star_mul, Complex.star_def,
        -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring
  rw [hBd, hJx]
  ext i j
  simp only [mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> norm_num [hws]
  all_goals try field_simp [hw0]
  all_goals ring

private theorem spin_three_score (angle : ℝ) (hc : Real.cos (3 * angle) = 1)
    (hB : ((Real.cos angle : ℂ) • Jx 3 + (Real.sin angle : ℂ) • Jy 3).IsHermitian) :
    trace (((1 / 2 : ℂ) • vecMulVec (![1, 0, 0, -1] : Fin 4 → ℂ)
      (star (![1, 0, 0, -1] : Fin 4 → ℂ))) * pos hB) = 3 / 4 := by
  let a : ℂ := Real.sqrt 3
  have ha : a ^ 2 = 3 := by
    dsimp [a]
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hsa : star a = a := by simp [a]
  have hca : (starRingEnd ℂ) a = a := hsa
  have hJx := spin_three_Jx
  have hJy := spin_three_Jy
  change Jx 3 = !![0, a / 2, 0, 0; a / 2, 0, 1, 0;
    0, 1, 0, a / 2; 0, 0, a / 2, 0] at hJx
  change Jy 3 = !![0, -I * a / 2, 0, 0; I * a / 2, 0, -I, 0;
    0, I, 0, -I * a / 2; 0, 0, I * a / 2, 0] at hJy
  let w : ℂ := (Real.cos angle : ℂ) + I * (Real.sin angle : ℂ)
  have hw : w * star w = 1 := by
    calc w * star w = ((Real.cos angle ^ 2 + Real.sin angle ^ 2 : ℝ) : ℂ) := by
           simp only [w, star_add, star_mul, Complex.star_def, map_mul,
             Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_add, Complex.ofReal_pow]
           ring_nf
           simp only [Complex.I_sq]
           ring
         _ = 1 := by rw [add_comm, Real.sin_sq_add_cos_sq]; rfl
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hws : star w = w⁻¹ := eq_inv_of_mul_eq_one_right hw
  let R : Matrix (Fin 4) (Fin 4) ℂ := diagonal fun i => w ^ i.val
  have hRR : R * Rᴴ = 1 := by
    simp only [R, diagonal_conjTranspose, diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp only [diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, star_pow, ← mul_pow]
      change (w * star w) ^ i.val = 1
      rw [hw, one_pow]
    · simp [diagonal, h, Matrix.one_apply]
  let W : Matrix (Fin 4) (Fin 4) ℂ :=
    !![1, a, a, 1; a, 1, -1, -a; a, -1, -1, a; 1, -a, a, -1]
  have hWW := four_gram a ha hca
  let lam : Fin 4 → ℝ := ![3 / 2, 1 / 2, -1 / 2, -3 / 2]
  have hXW := four_eigenbasis a ha hJx
  have hBR := spin_three_rotation angle a w rfl hws hw0 hJx hJy
  have hBW : ((Real.cos angle : ℂ) • Jx 3 + (Real.sin angle : ℂ) • Jy 3) *
      (R * W) = (R * W) * diagonal (fun i => (lam i : ℂ)) := by
    rw [← Matrix.mul_assoc, hBR, Matrix.mul_assoc, hXW, ← Matrix.mul_assoc]
  have hInv : (R * W) * (((1 / 8 : ℂ) • Wᴴ) * Rᴴ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W, hWW, Matrix.one_mul, hRR]
  have hp := cfc_eigenmatrix hB (R * W) lam hBW positiveWeight
  have hD : diagonal (fun i => (positiveWeight (lam i) : ℂ)) =
      diagonal (![1, 1, 0, 0] : Fin 4 → ℂ) := by
    congr 1
    funext i
    fin_cases i <;> norm_num [positiveWeight, lam]
  have hpos : pos hB = R * (W * diagonal (![1, 1, 0, 0] : Fin 4 → ℂ) *
      ((1 / 8 : ℂ) • Wᴴ)) * Rᴴ := by
    have h := congrArg (fun M => M * (((1 / 8 : ℂ) • Wᴴ) * Rᴴ)) hp
    rw [Matrix.mul_assoc, hInv, Matrix.mul_one, hD] at h
    simpa only [pos, Matrix.mul_assoc] using h
  have hM := four_positive_matrix a ha hca
  rw [hpos, hM, Matrix.smul_mul, trace_smul, vecMulVec_mul, trace_vecMulVec]
  simp only [Matrix.vecMul, dotProduct, R, diagonal_mul, mul_diagonal,
    diagonal_conjTranspose, Pi.star_apply, star_pow]
  norm_num [Fin.sum_univ_succ]
  have hw3 : w ^ 3 * star w ^ 3 = 1 := by rw [← mul_pow, hw, one_pow]
  have hre : (w ^ 3).re = 1 := by
    dsimp only [w]
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp only [zero_mul, mul_zero, zero_add, add_zero, sub_zero, one_mul]
    have hc3 := Real.cos_three_mul angle
    have hs := Real.sin_sq_add_cos_sq angle
    calc
      _ = 4 * Real.cos angle ^ 3 - 3 * Real.cos angle := by
        nlinarith [congrArg (fun t => t * Real.cos angle) hs]
      _ = 1 := by linarith
  have hsum : w ^ 3 + star w ^ 3 = 2 := by
    change w ^ 3 + (starRingEnd ℂ) w ^ 3 = 2
    rw [← map_pow]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
        hre] <;> norm_num
  calc
    _ = (1 / 2 : ℂ) * (1 / 2 + (w ^ 3 + star w ^ 3) / 4 +
      (w ^ 3 * star w ^ 3) / 2) := by simp only [Complex.star_def]; ring
    _ = 3 / 4 := by rw [hsum, hw3]; norm_num

private theorem pair_singlet_annihilation (cx cy : ℂ) :
    (cx • (Jx 1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Jx 1) +
    cy • (Jy 1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Jy 1)) *ᵥ antisymmetricVector = 0 := by
  funext i
  rcases i with ⟨i, r⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases r <;>
    norm_num [Jx, Jy, Jplus, antisymmetricVector, kroneckerMap,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply] <;> ring


set_option backward.isDefEq.respectTransparency false in
private theorem site_cons {N : ℕ} (j : Fin N → ℕ) (s : ℕ)
    (T : ∀ t : ℕ, Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ)
    (x y : ∀ n : Fin (N + 1), Fin ((Fin.cons (α := fun _ => ℕ) s j) n + 1)) :
    (∑ n, siteOperator (Fin.cons (α := fun _ => ℕ) s j) n (T ((Fin.cons (α := fun _ => ℕ) s j) n)) x y) =
    T s (x 0) (y 0) * (1 : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ)
        (fun n : Fin N => x n.succ) (fun n : Fin N => y n.succ) +
    (if x 0 = y 0 then 1 else 0) *
      ∑ n, siteOperator j n (T (j n)) (fun n : Fin N => x n.succ) (fun n : Fin N => y n.succ) := by
  classical
  have hp {L : ℕ} (n : Fin L) (f : Fin L → ℂ) :
      (∏ r ∈ Finset.univ.erase n, f r) = ∏ r, if r = n then 1 else f r := by
    rw [Finset.prod_ite]
    simp [Finset.filter_ne']
  have hi (u v : ∀ n, Fin (j n + 1)) :
      (∏ n, if u n = v n then (1 : ℂ) else 0) =
        (1 : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ) u v := by
    by_cases h : u = v
    · subst v; simp
    · have hn : ∃ n, u n ≠ v n := Function.ne_iff.mp h
      obtain ⟨n, hn⟩ := hn
      rw [Finset.prod_eq_zero (Finset.mem_univ n) (by simp [hn])]
      simp [h]
  rw [Fin.sum_univ_succ]
  simp only [siteOperator, hp, Fin.prod_univ_succ, Fin.cons, Fin.cases_zero, Fin.cases_succ,
    Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _), ↓reduceIte, one_mul, Fin.succ_inj]
  rw [hi]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring
private theorem pair_rest_product
    (H : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (G : Matrix (Fin 4) (Fin 4) ℂ) (hH : IsDensity H) (hG : IsDensity G)
    (e : (∀ n : Fin 3, Fin ((![1, 1, 3] : Fin 3 → ℕ) n + 1)) ≃
      ((Fin 2 × Fin 2) × Fin 4))
    (he : ∀ x, e x = ((x 0, x 1), x 2)) :
    IsDensity ((H ⊗ₖ G).submatrix e e) ∧
    ¬ SpinGME ![1, 1, 3] ((H ⊗ₖ G).submatrix e e) := by
  let j : Fin 3 → ℕ := ![1, 1, 3]
  let rho : Matrix (∀ n : Fin 3, Fin (j n + 1)) (∀ n : Fin 3, Fin (j n + 1)) ℂ :=
    (H ⊗ₖ G).submatrix e e
  have hrho : IsDensity rho := by
    constructor
    · exact (hH.1.kronecker hG.1).submatrix e
    · change ∑ x, (H ⊗ₖ G) (e x) (e x) = 1
      rw [e.sum_comp (fun t => (H ⊗ₖ G) t t)]
      change trace (H ⊗ₖ G) = 1
      rw [trace_kronecker, hH.2, hG.2, mul_one]
  let S : Finset (Fin 3) := {0, 1}
  let eL : (∀ n : S, Fin (j n + 1)) ≃ (Fin 2 × Fin 2) :=
    { toFun := fun x => (x ⟨0, by decide⟩, x ⟨1, by decide⟩)
      invFun := fun x n => (Fin.cons x.1 (Fin.cons x.2 (Fin.cons 0 (fun i => Fin.elim0 i))) : ∀ r : Fin 3, Fin (j r + 1)) n
      left_inv := by
        intro x
        funext n
        rcases n with ⟨n, hn⟩
        fin_cases n
        · rfl
        · rfl
        · exact False.elim ((show (2 : Fin 3) ∉ S by decide) hn)
      right_inv := by intro x; rfl }
  let eR : (∀ n : ↥Sᶜ, Fin (j n + 1)) ≃ Fin 4 :=
    { toFun := fun x => x ⟨2, by decide⟩
      invFun := fun x n => (Fin.cons 0 (Fin.cons 0 (Fin.cons x (fun i => Fin.elim0 i))) : ∀ r : Fin 3, Fin (j r + 1)) n
      left_inv := by
        intro x
        funext n
        rcases n with ⟨n, hn⟩
        fin_cases n
        · exact False.elim ((show (0 : Fin 3) ∉ Sᶜ by decide) hn)
        · exact False.elim ((show (1 : Fin 3) ∉ Sᶜ by decide) hn)
        · rfl
      right_inv := by intro x; rfl }
  have hDL : IsDensity (H.submatrix eL eL) := by
    refine ⟨hH.1.submatrix eL, ?_⟩
    change ∑ x, H (eL x) (eL x) = 1
    rw [eL.sum_comp (fun t => H t t)]
    exact hH.2
  have hDR : IsDensity (G.submatrix eR eR) := by
    refine ⟨hG.1.submatrix eR, ?_⟩
    change ∑ x, G (eR x) (eR x) = 1
    rw [eR.sum_comp (fun t => G t t)]
    exact hG.2
  have hSep : SeparableAcross j S rho := by
    refine ⟨1, fun _ => 1, fun _ => H.submatrix eL eL,
      fun _ => G.submatrix eR eR, ?_, ?_, ?_, ?_⟩
    · intro r; norm_num
    · norm_num
    · intro r; exact ⟨hDL, hDR⟩
    · intro x y
      simp only [Fin.sum_univ_one, Complex.ofReal_one, one_mul, Matrix.submatrix_apply]
      change (H ⊗ₖ G) (e x) (e y) = H (x 0, x 1) (y 0, y 1) * G (x 2) (y 2)
      rw [he x, he y]
      rfl
  have hnGME : ¬ SpinGME j rho := by
    intro h
    apply h
    refine ⟨1, fun _ => 1, fun _ => S, fun _ => rho, ?_, ?_, ?_, ?_⟩
    · intro r; norm_num
    · norm_num
    · intro r
      exact ⟨by change S.Nonempty; decide, by change (Sᶜ).Nonempty; decide, hrho, hSep⟩
    · simp
  exact ⟨hrho, hnGME⟩

private theorem pos_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    pos hA = pos hB := by
  subst B
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem padded_ensemble_entry {N : ℕ} (j : Fin N → ℕ) (K : ℕ) (k : Fin K)
    (x y : ∀ n : Fin (N + 2),
      Fin ((Fin.cons (α := fun _ => ℕ) 1 (Fin.cons (α := fun _ => ℕ) 1 j)) n + 1)) :
    let angle : ℝ := theta K k
    let P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      (Real.cos angle : ℂ) • (Jx 1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Jx 1) +
      (Real.sin angle : ℂ) • (Jy 1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Jy 1)
    ensembleJ (Fin.cons 1 (Fin.cons 1 j)) K k x y =
      P (x 0, x 1) (y 0, y 1) *
        (1 : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ)
          (fun n => x n.succ.succ) (fun n => y n.succ.succ) +
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x 0, x 1) (y 0, y 1) *
        ensembleJ j K k (fun n => x n.succ.succ) (fun n => y n.succ.succ) := by
  classical
  dsimp only
  have hi {M : ℕ} (l : Fin M → ℕ) (s : ℕ)
      (u v : ∀ n : Fin (M + 1), Fin ((Fin.cons (α := fun _ => ℕ) s l) n + 1)) :
      (1 : Matrix (∀ n, Fin ((Fin.cons (α := fun _ => ℕ) s l) n + 1)) (∀ n, Fin ((Fin.cons (α := fun _ => ℕ) s l) n + 1)) ℂ) u v =
      (if u 0 = v 0 then 1 else 0) *
        (1 : Matrix (∀ n, Fin (l n + 1)) (∀ n, Fin (l n + 1)) ℂ)
          (fun n => u n.succ) (fun n => v n.succ) := by
    have heq : u = v ↔ u 0 = v 0 ∧ (fun n : Fin M => u n.succ) = (fun n : Fin M => v n.succ) := by
      constructor
      · intro h
        exact ⟨congrFun h 0, congrArg (fun z => fun n : Fin M => z n.succ) h⟩
      · rintro ⟨hzero, htail⟩
        exact (Fin.consEquiv (fun n => Fin ((Fin.cons (α := fun _ => ℕ) s l) n + 1))).symm.injective
          (Prod.ext hzero htail)
    simp only [Matrix.one_apply, heq]
    split_ifs <;> simp_all
  have hc (T : ∀ t : ℕ, Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ) :
      (∑ n, siteOperator (Fin.cons 1 (Fin.cons 1 j)) n
        (T ((Fin.cons (α := fun _ => ℕ) 1 (Fin.cons (α := fun _ => ℕ) 1 j)) n)) x y) =
      (T 1 (x 0) (y 0) * (if x 1 = y 1 then 1 else 0) +
        (if x 0 = y 0 then 1 else 0) * T 1 (x 1) (y 1)) *
        (1 : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ)
          (fun n => x n.succ.succ) (fun n => y n.succ.succ) +
      ((if x 0 = y 0 then 1 else 0) * (if x 1 = y 1 then 1 else 0)) *
        ∑ n, siteOperator j n (T (j n))
          (fun n => x n.succ.succ) (fun n => y n.succ.succ) := by
    rw [site_cons (Fin.cons 1 j) 1 T x y,
      site_cons j 1 T (fun n => x n.succ) (fun n => y n.succ),
      hi j 1 (fun n => x n.succ) (fun n => y n.succ)]
    simp only [Fin.succ_zero_eq_one]
    ring
  simp only [ensembleJ, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, hc,
    kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  have hd (p q : Prop) [Decidable p] [Decidable q] :
      (if p ∧ q then (1 : ℂ) else 0) =
        (if p then (1 : ℂ) else 0) * (if q then (1 : ℂ) else 0) := by
    split_ifs <;> simp_all
  rw [hd]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem singlet_padding_ensemble_score {N : ℕ} (j : Fin N → ℕ) (K : ℕ)
    (sigma : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ)
    (e : (∀ n : Fin (N + 2),
      Fin ((Fin.cons (α := fun _ => ℕ) 1 (Fin.cons (α := fun _ => ℕ) 1 j)) n + 1)) ≃
      ((Fin 2 × Fin 2) × (∀ n, Fin (j n + 1))))
    (he : ∀ x, e x = ((x 0, x 1), fun n : Fin N => x n.succ.succ)) :
    trace (((((1 / 2 : ℂ) • singletMatrix) ⊗ₖ sigma).submatrix e e) *
      ensembleQ (Fin.cons 1 (Fin.cons 1 j)) K) = trace (sigma * ensembleQ j K) := by
  let P : Fin K → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun k =>
    (Real.cos (theta K k) : ℂ) • (Jx 1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Jx 1) +
    (Real.sin (theta K k) : ℂ) • (Jy 1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Jy 1)
  let B := ensembleJ j K
  have hJ (k : Fin K) : ensembleJ (Fin.cons 1 (Fin.cons 1 j)) K k =
      (P k ⊗ₖ (1 : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ) +
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ B k).submatrix e e := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.add_apply, kroneckerMap_apply, he]
    exact padded_ensemble_entry j K k x y
  have ha (k : Fin K) :
      (P k ⊗ₖ (1 : Matrix (∀ n, Fin (j n + 1)) (∀ n, Fin (j n + 1)) ℂ) +
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ B k).IsHermitian := by
    rw [← isHermitian_submatrix_equiv e, ← hJ k]
    exact ensemble_hermitian _ _ _
  have hpos (k : Fin K) : pos (ensemble_hermitian (Fin.cons 1 (Fin.cons 1 j)) K k) =
      (pos (ha k)).submatrix e e :=
    (pos_congr _ _ (hJ k)).trans (pos_submatrix_equiv (ha k) e)
  have hQ : ensembleQ (Fin.cons 1 (Fin.cons 1 j)) K =
      ((1 / K : ℂ) • ∑ k : Fin K, pos (ha k)).submatrix e e := by
    ext x y
    simp [ensembleQ, hpos, Matrix.submatrix, Matrix.of_apply, Matrix.sum_apply]
  rw [hQ, submatrix_mul_equiv]
  change ∑ x, (((((1 / 2 : ℂ) • singletMatrix) ⊗ₖ sigma) *
    ((1 / K : ℂ) • ∑ k : Fin K, pos (ha k))) (e x) (e x)) = _
  rw [e.sum_comp (fun t => (((((1 / 2 : ℂ) • singletMatrix) ⊗ₖ sigma) *
    ((1 / K : ℂ) • ∑ k : Fin K, pos (ha k))) t t))]
  exact singlet_padding_score K P B sigma (ensemble_hermitian j K)
    (fun k => pair_singlet_annihilation _ _) ha

set_option backward.isDefEq.respectTransparency false in
private theorem padded_precession_score
    (e : (∀ n : Fin 3, Fin ((![1, 1, 3] : Fin 3 → ℕ) n + 1)) ≃
      ((Fin 2 × Fin 2) × Fin 4))
    (he : ∀ x, e x = ((x 0, x 1), x 2)) :
    trace (((((1 / 2 : ℂ) • singletMatrix) ⊗ₖ
      ((1 / 2 : ℂ) • vecMulVec (![1, 0, 0, -1] : Fin 4 → ℂ)
        (star (![1, 0, 0, -1] : Fin 4 → ℂ)))).submatrix e e) *
      ensembleQ ![1, 1, 3] 3) = 3 / 4 := by
  let j : Fin 1 → ℕ := ![3]
  let G : Matrix (Fin 4) (Fin 4) ℂ :=
    (1 / 2 : ℂ) • vecMulVec (![1, 0, 0, -1] : Fin 4 → ℂ)
      (star (![1, 0, 0, -1] : Fin 4 → ℂ))
  let H : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := (1 / 2 : ℂ) • singletMatrix
  let f : (∀ n : Fin 1, Fin (j n + 1)) ≃ Fin 4 :=
    { toFun := fun x => x 0
      invFun := fun x => Fin.cons x (fun n => Fin.elim0 n)
      left_inv := by intro x; funext n; fin_cases n; rfl
      right_inv := by intro x; rfl }
  let ep := e.trans ((Equiv.refl (Fin 2 × Fin 2)).prodCongr f.symm)
  have hep : ∀ x, ep x = ((x 0, x 1), fun n : Fin 1 => x n.succ.succ) := by
    intro x
    change ((e x).1, f.symm (e x).2) = _
    rw [he x]
    congr 1
    funext n
    fin_cases n
    rfl
  have hrho : (H ⊗ₖ G).submatrix e e =
      (H ⊗ₖ (G.submatrix f f)).submatrix ep ep := by
    ext x y
    change H (e x).1 (e y).1 * G (e x).2 (e y).2 =
      H (e x).1 (e y).1 * G (f (f.symm (e x).2)) (f (f.symm (e y).2))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hpad := singlet_padding_ensemble_score j 3 (G.submatrix f f) ep hep
  change trace (((H ⊗ₖ (G.submatrix f f)).submatrix ep ep) * ensembleQ ![1, 1, 3] 3) = _ at hpad
  rw [← hrho] at hpad
  rw [hpad]
  let B : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ := fun k =>
    (Real.cos (theta 3 k) : ℂ) • Jx 3 + (Real.sin (theta 3 k) : ℂ) • Jy 3
  have hb (k : Fin 3) : (B k).IsHermitian :=
    ((spin_hermitian 3).1.smul (by
      simp only [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal])).add
    ((spin_hermitian 3).2.smul (by
      simp only [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]))
  have hJ (k : Fin 3) : ensembleJ j 3 k = (B k).submatrix f f := by
    ext x y
    simp [ensembleJ, siteOperator, j, B, f, Fin.sum_univ_one]
  have hpos (k : Fin 3) : pos (ensemble_hermitian j 3 k) =
      (pos (hb k)).submatrix f f :=
    (pos_congr _ _ (hJ k)).trans (pos_submatrix_equiv (hb k) f)
  have hQ : ensembleQ j 3 = ((1 / 3 : ℂ) • ∑ k : Fin 3, pos (hb k)).submatrix f f := by
    ext x y
    simp [ensembleQ, hpos, Matrix.submatrix, Matrix.of_apply, Fin.sum_univ_three]
  rw [hQ, submatrix_mul_equiv]
  change ∑ x, (G * ((1 / 3 : ℂ) • ∑ k : Fin 3, pos (hb k))) (f x) (f x) = _
  rw [f.sum_comp (fun t => (G * ((1 / 3 : ℂ) • ∑ k : Fin 3, pos (hb k))) t t)]
  change trace (G * ((1 / 3 : ℂ) • ∑ k : Fin 3, pos (hb k))) = 3 / 4
  have hScore (k : Fin 3) : trace (G * pos (hb k)) = 3 / 4 := by
    apply spin_three_score
    change Real.cos (3 * (2 * Real.pi * k.val / 3)) = 1
    convert Real.cos_nat_mul_two_pi k.val using 1 <;> congr 1 <;> ring
  simp only [Matrix.mul_smul, trace_smul, Finset.mul_sum, trace_sum, hScore]
  norm_num

/-- The singlet-padded spin-3/2 endpoint state violates Conjecture 3. -/
theorem result : ¬ claim := by
  let j : Fin 3 → ℕ := ![1, 1, 3]
  let e : (∀ n : Fin 3, Fin (j n + 1)) ≃ ((Fin 2 × Fin 2) × Fin 4) :=
    { toFun := fun x => ((x 0, x 1), x 2)
      invFun := fun x => Fin.cons x.1.1 (Fin.cons x.1.2 (Fin.cons x.2 (fun i => Fin.elim0 i)))
      left_inv := by intro x; funext n; fin_cases n <;> rfl
      right_inv := by intro x; rfl }
  let G : Matrix (Fin 4) (Fin 4) ℂ :=
    (1 / 2 : ℂ) • vecMulVec (![1, 0, 0, -1] : Fin 4 → ℂ)
      (star (![1, 0, 0, -1] : Fin 4 → ℂ))
  let H : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := (1 / 2 : ℂ) • singletMatrix
  let rho : Matrix (∀ n : Fin 3, Fin (j n + 1)) (∀ n : Fin 3, Fin (j n + 1)) ℂ :=
    (H ⊗ₖ G).submatrix e e
  have hH : IsDensity H := by
    constructor
    · exact singletMatrix_posSemidef.smul (by
        rw [Complex.nonneg_iff]
        norm_num)
    · norm_num [H, trace_smul, singletMatrix, trace_vecMulVec, dotProduct,
        antisymmetricVector, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hG : IsDensity G := by
    constructor
    · exact (posSemidef_vecMulVec_self_star (![1, 0, 0, -1] : Fin 4 → ℂ)).smul (by
        rw [Complex.nonneg_iff]
        norm_num)
    · change trace ((1 / 2 : ℂ) • vecMulVec _ _) = 1
      rw [trace_smul, trace_vecMulVec]
      norm_num [dotProduct, Fin.sum_univ_succ, Pi.star_apply]
  have hrhoGME := pair_rest_product H G hH hG e (by intro x; rfl)
  have hrho : IsDensity rho := hrhoGME.1
  have hnGME : ¬ SpinGME j rho := hrhoGME.2
  have ht : trace (rho * ensembleQ j 3) = 3 / 4 :=
    padded_precession_score e (by intro x; rfl)
  intro h
  apply hnGME
  apply h 3 (by decide) (by norm_num) 3 (by norm_num) j
    (by intro n; fin_cases n <;> norm_num [j]) rho hrho
  rw [ht]
  norm_num [conjecturedThreshold]

#print axioms result
end D5.S3.Quantum.Entanglement.PrecessionUniversalThresholdRefutation
