/- GID: D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC
   generality: I
   mirror-B: D5/B/S3/Quantum/GuoJinMaxMarginalEntropyLOCC
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.claim; result=D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.result; claim=D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.claim
   digest: A four-party local measurement increases maximum marginal entropy. -/

/-
result
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#20726; Refuted)
Direct frozen dependencies:
  F3 = D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.entropy2
  F1 = D5/S3/Weil/BurnolGram/QuantitativeMultiOrbitWeilNegativeCertificate.finiteComplexEnergy
    declaration statement_id: sha256:9345d32a628ed0b2ff4f3fbfc24cf58621f8fc6ce965226bf491f4ea8a12877b
  F4 = D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.entropy_diagonal
  F5 = D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy.entropy_eq_spectrum
  F6 = D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.entropy
  F7 = D5/S3/Quantum/Information/PartialTraceMutualInformation.spectralEntropy
  F3p2 = F3._proof_2; F3p3 = F3._proof_3.
The squared norm in claim is the literal finite sum; proofs use finiteComplexEnergy.
The entropy in maxMarginalEntropy is the literal trace expression; proofs use entropy2
through CStarMatrix.ofMatrix.symm and the public diagonal and spectral entropy laws.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The public result refutes the unrestricted entropy conjecture. Each outcome maximum
is proved at least 3; exact upper bounds for the outcome maxima are not asserted.
All theorem declarations below have proof_shape: bind-only and escape_witness: none.
Declaration inventory; escape_witness is none throughout; the module basis above applies.
  marginal: proof_shape=bind-only; frozen=none;
    consumers=maxMarginalEntropy,marginal_sparse,psi_marginal,psi_max,branch_marginal,branch_max_lower.
  maxMarginalEntropy: proof_shape=bind-only; frozen=none;
    consumers=claim,psi_max,branch_max_lower,outcome_term,result.
  applyLocal: proof_shape=bind-only; frozen=none;
    consumers=claim,local_diagonal,local_diagonal_sparse,apply_K,outcome_term,result.
  claim: proof_shape=bind-only; frozen=none;
    consumers=result.
  sparse_at: proof_shape=bind-only; frozen=none;
    consumers=norm_sparse,marginal_sparse,psi_sparse.
  sparse_zero: proof_shape=bind-only; frozen=none;
    consumers=norm_sparse,marginal_sparse,psi_sparse.
  sum_support: proof_shape=bind-only; frozen=none;
    consumers=norm_sparse,marginal_sparse.
  norm_sparse: proof_shape=bind-only; frozen=F1;
    consumers=psi_normalized,branch_norm.
  sparse_update: proof_shape=bind-only; frozen=none;
    consumers=marginal_sparse.
  marginal_sparse: proof_shape=bind-only; frozen=none;
    consumers=psi_marginal,branch_marginal.
  sparse_smul: proof_shape=bind-only; frozen=none;
    consumers=branch_marginal.
  local_diagonal: proof_shape=bind-only; frozen=none;
    consumers=local_diagonal_sparse.
  local_diagonal_sparse: proof_shape=bind-only; frozen=none;
    consumers=apply_K.
  entropy_diagonal: proof_shape=bind-only; frozen=F3,F3p2,F3p3,F4,F5,F6,F7;
    consumers=entropy_initial,entropy_uniform.
  log_inv_pow_two: proof_shape=bind-only; frozen=none;
    consumers=entropy_initial,entropy_uniform.
  entropy_initial: proof_shape=bind-only; frozen=F3,F3p2,F3p3,F4,F5,F6,F7;
    consumers=psi_max.
  entropy_uniform: proof_shape=bind-only; frozen=F3,F3p2,F3p3,F4,F5,F6,F7;
    consumers=branch_max_lower.
  basis: proof_shape=bind-only; frozen=none;
    consumers=basis_separated,basis_injective,psi,psi_sparse,psi_normalized,psi_marginal,branch,apply_K,branch_norm,branch_marginal.
  basis_separated: proof_shape=bind-only; frozen=none;
    consumers=basis_injective,psi_marginal,branch_marginal.
  basis_injective: proof_shape=bind-only; frozen=none;
    consumers=psi_sparse,psi_normalized,psi_marginal,branch_norm,branch_marginal.
  psi: proof_shape=bind-only; frozen=none;
    consumers=psi_sparse,psi_normalized,psi_marginal,psi_max,apply_K,outcome_term,result.
  psi_sparse: proof_shape=bind-only; frozen=none;
    consumers=psi_normalized,psi_marginal,apply_K.
  psi_normalized: proof_shape=bind-only; frozen=F1;
    consumers=result.
  psi_marginal: proof_shape=bind-only; frozen=none;
    consumers=psi_max.
  psi_max: proof_shape=bind-only; frozen=F3,F3p2,F3p3,F4,F5,F6,F7;
    consumers=result.
  K: proof_shape=bind-only; frozen=none;
    consumers=K_diagonal,K_complete,apply_K,outcome_term,result.
  K_diagonal: proof_shape=bind-only; frozen=none;
    consumers=K_complete,apply_K.
  K_complete: proof_shape=bind-only; frozen=none;
    consumers=result.
  coefficient: proof_shape=bind-only; frozen=none;
    consumers=branch,apply_K,branch_norm,branch_marginal.
  branch: proof_shape=bind-only; frozen=none;
    consumers=apply_K,branch_norm,branch_marginal,branch_max_lower,outcome_term,result.
  apply_K: proof_shape=bind-only; frozen=none;
    consumers=outcome_term.
  branch_norm: proof_shape=bind-only; frozen=F1;
    consumers=outcome_term.
  q: proof_shape=bind-only; frozen=none;
    consumers=q_product,branch_marginal,branch_max_lower,outcome_term,result.
  q_product: proof_shape=bind-only; frozen=none;
    consumers=branch_marginal.
  branch_marginal: proof_shape=bind-only; frozen=none;
    consumers=branch_max_lower.
  branch_max_lower: proof_shape=bind-only; frozen=F3,F3p2,F3p3,F4,F5,F6,F7;
    consumers=result.
  outcome_term: proof_shape=bind-only; frozen=F1;
    consumers=result.
  result: proof_shape=bind-only; frozen=F3,F3p2,F3p3,F4,F5,F6,F7,F1;
    consumers=none (settling result).
-/

import D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation
import D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy
import D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate


/-! Binding conventions for Y. Guo and Z.-X. Jin, "Measure of entanglement and the monogamy relation: a topical review",
arXiv:2512.21992v1 (26 December 2025).

* Section 2: "S(ρ) = −Tr(ρ log₂ ρ) is the von Neumann entropy of the state ρ". Here log₂ ρ is `CFC.log ρ / Real.log 2` on
  the C*-algebra carrier `CStarMatrix`, as in the D5 owner `VonNeumannEntropyPinching.vonNeumannEntropy`, which takes a
  `DensityState` (a subtype carrying positivity and trace proofs).
* Section 9.4, (189): "E′^(n)(|ψ⟩) = max_i h(ρ^{A_i})", with ρ^{A_i} the reduced state of party A_i; Table 16 lists h = S.
  "we conjecture that E′^(n) does not increase on average under LOCC for these cases mentioned above."
* An n-party pure state on (ℂ^d)^{⊗n} is its amplitude function on basis tuples `Fin n → Fin d`. A local measurement on
  party i with Kraus operators K_r (∑_r K_r† K_r = 1) is an LOCC operation; outcome r has probability
  p_r = ‖(K_r)_i ψ‖² and post-measurement state (K_r)_i ψ / √p_r. The claim below is the conjecture's consequence for
  one such measurement. -/

namespace D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC

open _root_.Matrix
open D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation (entropy2)
open D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate (finiteComplexEnergy)
open scoped ComplexOrder CStarAlgebra


/-- The reduced state `ρ^{A_i} = Tr_{all parties but i} |ψ⟩⟨ψ|`. -/
noncomputable def marginal {n d : ℕ} (ψ : ((Fin n → Fin d) → ℂ)) (i : Fin n) : CStarMatrix (Fin d) (Fin d) ℂ :=
  CStarMatrix.ofMatrix fun a b => ∑ x : Fin n → Fin d, if x i = a then ψ x * star (ψ (Function.update x i b)) else 0

/-- (189) with `h = S`: `E′^(n)(|ψ⟩) = max_i S(ρ^{A_i})`. -/
noncomputable def maxMarginalEntropy {n d : ℕ} (ψ : ((Fin n → Fin d) → ℂ)) : ℝ :=
  ⨆ i : Fin n, -(Matrix.trace (marginal ψ i * CFC.log (marginal ψ i))).re / Real.log 2

/-- The operator `K` applied to party `i`: `(K_i ψ)(x) = ∑_a K_{x_i, a} ψ(x[i ↦ a])`. -/
noncomputable def applyLocal {n d : ℕ} (K : Matrix (Fin d) (Fin d) ℂ) (i : Fin n) (ψ : ((Fin n → Fin d) → ℂ)) : ((Fin n → Fin d) → ℂ) :=
  fun x => ∑ a, K (x i) a * ψ (Function.update x i a)

/-- Section 9.4, for one local measurement: the average of `E′^(n)` over the normalized outcomes does not exceed its
initial value. -/
def claim : Prop :=
  ∀ (n d m : ℕ) (ψ : ((Fin n → Fin d) → ℂ)) (i : Fin n) (K : Fin m → Matrix (Fin d) (Fin d) ℂ),
    (∑ x, Complex.normSq (ψ x)) = 1 → ∑ r, (K r)ᴴ * K r = 1 →
      (∑ r, if (∑ x, Complex.normSq (applyLocal (K r) i ψ x)) = 0 then 0 else
        (∑ x, Complex.normSq (applyLocal (K r) i ψ x)) *
          maxMarginalEntropy (((Real.sqrt ((∑ x, Complex.normSq (applyLocal (K r) i ψ x))))⁻¹ : ℂ) • applyLocal (K r) i ψ))
        ≤ maxMarginalEntropy ψ

end D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC

namespace D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC
open _root_.Matrix
open D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation (entropy2)
open D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate (finiteComplexEnergy)
open scoped ComplexOrder CStarAlgebra
noncomputable section

variable {J : Type*} [Fintype J] {n d : ℕ}

private lemma sparse_at (f : J → (Fin n → Fin d)) (hf : Function.Injective f)
    (c : J → ℂ) (k : J) : (Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) c (f k) = c k := by
  classical
  simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [show f k ≠ f l from fun h => hl (hf h).symm]
  · simp

private lemma sparse_zero (f : J → (Fin n → Fin d)) (c : J → ℂ)
    (x : Fin n → Fin d) (hx : ∀ k, x ≠ f k) : (Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) c x = 0 := by
  simp [Fintype.linearCombination_apply, Finset.sum_apply, hx]

private lemma sum_support (f : J → (Fin n → Fin d)) (hf : Function.Injective f)
    {R : Type*} [AddCommMonoid R] (g : (Fin n → Fin d) → R)
    (hg : ∀ x, (∀ k, x ≠ f k) → g x = 0) : ∑ x, g x = ∑ k, g (f k) := by
  classical
  symm
  apply Fintype.sum_of_injective f hf _ g
  · intro x hx
    apply hg x
    simpa only [Set.mem_range, not_exists, eq_comm] using hx
  · intro k; rfl

private lemma norm_sparse (f : J → (Fin n → Fin d)) (hf : Function.Injective f)
    (c : J → ℂ) : finiteComplexEnergy ((Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) c) = ∑ k, Complex.normSq (c k) := by
  unfold finiteComplexEnergy
  rw [sum_support f hf _ (by intro x hx; rw [sparse_zero f c x hx]; simp)]
  simp_rw [sparse_at f hf]

private lemma sparse_update (f : J → (Fin n → Fin d)) (c : J → ℂ) (i : Fin n)
    (hs : ∀ k l b, Function.update (f k) i b = f l → k = l)
    (k : J) (b : Fin d) : (Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) c (Function.update (f k) i b) =
      if b = f k i then c k else 0 := by
  classical
  have he : Function.update (f k) i b = f k ↔ b = f k i := Function.update_eq_self_iff
  simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp only [he]
  · intro l _ hl
    simp [show Function.update (f k) i b ≠ f l from fun h => hl (hs k l b h).symm]
  · simp

private lemma marginal_sparse (f : J → (Fin n → Fin d)) (hf : Function.Injective f)
    (c : J → ℂ) (i : Fin n)
    (hs : ∀ k l b, Function.update (f k) i b = f l → k = l) :
    marginal ((Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) c) i = CStarMatrix.ofMatrix (diagonal fun a =>
      ∑ k, if f k i = a then c k * star (c k) else 0) := by
  classical
  ext a b
  change (∑ x, if x i = a then (Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) c x * star ((Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) c (Function.update x i b)) else 0) =
    (diagonal fun a => ∑ k, if f k i = a then c k * star (c k) else 0) a b
  rw [sum_support f hf _ (by intro x hx; rw [sparse_zero f c x hx]; simp)]
  simp_rw [sparse_at f hf, sparse_update f c i hs]
  by_cases hab : a = b
  · subst b
    simp only [diagonal_apply_eq]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : f k i = a
    · simp [hk]
    · simp [hk]
  · rw [diagonal_apply_ne _ hab]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : f k i = a
    · simp [hk, Ne.symm hab]
    · simp [hk]

private lemma sparse_smul (f : J → (Fin n → Fin d)) (c : J → ℂ) (z : ℂ) :
    z • (Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) c = (Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) (fun k => z * c k) := by
  exact (map_smul (Fintype.linearCombination ℂ
    (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) z c).symm

private lemma local_diagonal (v : Fin d → ℂ) (i : Fin n) (ψ : ((Fin n → Fin d) → ℂ)) (x : Fin n → Fin d) :
    applyLocal (diagonal v) i ψ x = v (x i) * ψ x := by
  classical
  change ((diagonal v) *ᵥ (fun a => ψ (Function.update x i a))) (x i) = _
  rw [Matrix.mulVec_diagonal]
  simp

private lemma local_diagonal_sparse (f : J → (Fin n → Fin d)) (c : J → ℂ)
    (v : Fin d → ℂ) (i : Fin n) :
    applyLocal (diagonal v) i ((Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) c) = (Fintype.linearCombination ℂ (fun k => (Pi.single (f k) (1 : ℂ) : (Fin n → Fin d) → ℂ))) (fun k => v (f k i) * c k) := by
  funext x
  rw [local_diagonal]
  simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : x = f k
  · subst x; simp
  · simp [h]

end
end D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC

namespace D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC
open _root_.Matrix
open D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation (entropy2)
open D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate (finiteComplexEnergy)
open scoped ComplexOrder CStarAlgebra
noncomputable section

variable {d : ℕ}

open scoped Matrix.Norms.L2Operator

private lemma entropy_diagonal (w : Fin d → ℝ) :
    entropy2 (diagonal fun j => (w j : ℂ)) =
      -(∑ j, w j * Real.log (w j)) / Real.log 2 := by
  let M : Matrix (Fin d) (Fin d) ℂ := diagonal fun j => (w j : ℂ)
  have hM : M.IsHermitian := by
    apply isHermitian_diagonal_of_self_adjoint
    ext j; simp
  have hm : CStarMatrix.ofMatrix (cfc Real.log M) = CFC.log (CStarMatrix.ofMatrix M) :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log M
      (M.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hM hM
  have hdiag := D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.entropy_diagonal w
  change D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.entropy M = _ at hdiag
  rw [D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.entropy, dif_pos hM,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy] at hdiag
  have htrace := D5.S3.Quantum.Divergence.ThreeByThreeModulusEntropy.entropy_eq_spectrum M hM
  have ht : -(Matrix.trace (M * CFC.log M)).re = ∑ j, Real.negMulLog (w j) :=
    htrace.trans (by simpa only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib] using hdiag)
  calc
    entropy2 (diagonal fun j => (w j : ℂ)) = -(Matrix.trace (M * CFC.log M)).re / Real.log 2 := by
      unfold entropy2
      change -(Matrix.trace (CStarMatrix.ofMatrix M * CFC.log (CStarMatrix.ofMatrix M))).re / Real.log 2 = _
      rw [← hm]
      rfl
    _ = (∑ j, Real.negMulLog (w j)) / Real.log 2 := congrArg (fun x : ℝ => x / Real.log 2) ht
    _ = -(∑ j, w j * Real.log (w j)) / Real.log 2 := by
      simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]

private lemma log_inv_pow_two (k : ℕ) : Real.log ((2 ^ k : ℝ)⁻¹) = -(k * Real.log 2) := by
  rw [Real.log_inv, Real.log_pow]

private lemma entropy_initial : entropy2 (diagonal fun j : Fin 9 =>
    if j = 0 then (1/2 : ℂ) else 1/16) = 5/2 := by
  let w : Fin 9 → ℝ := fun j => if j = 0 then 1/2 else 1/16
  have he : (fun j : Fin 9 => if j = 0 then (1/2 : ℂ) else 1/16) =
      fun j => (w j : ℂ) := by
    funext j; dsimp [w]; split_ifs <;> norm_num
  rw [he, entropy_diagonal]
  have hsmall : Real.log (1/16) = -4 * Real.log 2 := by
    convert log_inv_pow_two 4 using 1 <;> norm_num
  have hn : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [w, Fin.sum_univ_succ, Real.log_div, hsmall]
  field_simp [hn]
  <;> ring

private lemma entropy_uniform : entropy2 (diagonal fun j : Fin 9 =>
    if j = 0 then (0 : ℂ) else 1/8) = 3 := by
  let w : Fin 9 → ℝ := fun j => if j = 0 then 0 else 1/8
  have he : (fun j : Fin 9 => if j = 0 then (0 : ℂ) else 1/8) =
      fun j => (w j : ℂ) := by
    funext j; dsimp [w]; split_ifs <;> norm_num
  rw [he, entropy_diagonal]
  have hsmall : Real.log (1/8) = -3 * Real.log 2 := by
    convert log_inv_pow_two 3 using 1 <;> norm_num
  have hn : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [w, Fin.sum_univ_succ, hsmall]
  field_simp [hn]
  <;> ring

end
end D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC


namespace D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC
open _root_.Matrix
open D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation (entropy2)
open D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate (finiteComplexEnergy)
open scoped ComplexOrder CStarAlgebra
noncomputable section


private def basis (k : (Fin 2 × Fin 8)) : Fin 4 → Fin 9 :=
  if k.1 = 0 then ![0, 0, k.2.succ, k.2.succ] else ![k.2.succ, k.2.succ, 0, 0]

private lemma basis_separated (i : Fin 4) (k l : (Fin 2 × Fin 8)) (b : Fin 9)
    (h : Function.update (basis k) i b = basis l) : k = l := by
  obtain ⟨r,j⟩ := k
  obtain ⟨s,t⟩ := l
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  fin_cases i <;> fin_cases r <;> fin_cases s <;>
    simp_all [basis, Function.update]
  all_goals exact (Fin.succ_ne_zero t) (by symm; assumption)

private lemma basis_injective : Function.Injective basis := by
  intro k l h
  apply basis_separated 0 k l (basis k 0)
  simpa using h

private def psi : ((Fin 4 → Fin 9) → ℂ) := fun x => if ∃ k : (Fin 2 × Fin 8), x = basis k then 1/4 else 0

private lemma psi_sparse : psi = (Fintype.linearCombination ℂ (fun k => (Pi.single (basis k) (1 : ℂ) : (Fin 4 → Fin 9) → ℂ))) (fun _ => 1/4) := by
  funext x
  by_cases hx : ∃ k : (Fin 2 × Fin 8), x = basis k
  · obtain ⟨k,rfl⟩ := hx
    rw [sparse_at basis basis_injective]
    simp [psi]
  · rw [sparse_zero basis _ x (by simpa only [not_exists] using hx)]
    simp [psi, hx]

private lemma psi_normalized : finiteComplexEnergy psi = 1 := by
  rw [psi_sparse, norm_sparse basis basis_injective]
  norm_num [Fintype.card_prod]

private lemma psi_marginal (i : Fin 4) : marginal psi i =
    CStarMatrix.ofMatrix (diagonal fun a : Fin 9 => if a = 0 then (1/2 : ℂ) else 1/16) := by
  rw [psi_sparse, marginal_sparse basis basis_injective _ i (basis_separated i)]
  congr 1
  apply congrArg diagonal
  funext a
  fin_cases i <;> fin_cases a <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, basis]

private lemma psi_max : maxMarginalEntropy psi = 5/2 := by
  change (⨆ i : Fin 4, entropy2 (CStarMatrix.ofMatrix.symm (marginal psi i))) = 5/2
  have h : ∀ i : Fin 4, entropy2 (CStarMatrix.ofMatrix.symm (marginal psi i)) = 5/2 := by
    intro i
    rw [psi_marginal]
    simpa only [Equiv.symm_apply_apply] using entropy_initial
  simp_rw [h]
  exact ciSup_const

private def K (r : Fin 2) : Matrix (Fin 9) (Fin 9) ℂ :=
  if r = 0 then diagonal (Pi.single 0 1) else 1 - diagonal (Pi.single 0 1)

private lemma K_diagonal (r : Fin 2) : K r = diagonal (fun a =>
    if r = 0 then (if a = 0 then (1 : ℂ) else 0) else (if a = 0 then 0 else 1)) := by
  fin_cases r <;> ext a b <;> by_cases hab : a = b <;>
    simp [K, diagonal, hab, Pi.single_apply]
  split_ifs <;> simp

private lemma K_complete : ∑ r, (K r)ᴴ * K r = 1 := by
  simp_rw [K_diagonal]
  simp only [Fin.sum_univ_two, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_add]
  ext a b
  by_cases hab : a = b
  · subst b; by_cases ha : a = 0 <;> simp [ha]
  · simp [diagonal, hab, Matrix.one_apply]

end
end D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC


namespace D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC
open _root_.Matrix
open D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation (entropy2)
open D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate (finiteComplexEnergy)
open scoped ComplexOrder CStarAlgebra
noncomputable section

private def coefficient (r : Fin 2) (k : (Fin 2 × Fin 8)) : ℂ := if k.1 = r then 1/4 else 0

private def branch (r : Fin 2) : ((Fin 4 → Fin 9) → ℂ) := (Fintype.linearCombination ℂ (fun k => (Pi.single (basis k) (1 : ℂ) : (Fin 4 → Fin 9) → ℂ))) (coefficient r)

private lemma apply_K (r : Fin 2) : applyLocal (K r) 0 psi = branch r := by
  rw [K_diagonal, psi_sparse, local_diagonal_sparse, branch]
  apply congrArg ((Fintype.linearCombination ℂ (fun k => (Pi.single (basis k) (1 : ℂ) : (Fin 4 → Fin 9) → ℂ))))
  funext k
  obtain ⟨s,j⟩ := k
  fin_cases r <;> fin_cases s <;> norm_num [basis, coefficient]

private lemma branch_norm (r : Fin 2) : finiteComplexEnergy (branch r) = 1/2 := by
  rw [branch, norm_sparse basis basis_injective]
  fin_cases r <;> norm_num [coefficient, Fintype.sum_prod_type, Fin.sum_univ_succ]

private def q : ℂ := ((Real.sqrt (1/2))⁻¹ : ℝ)

private lemma q_product : (q * (1/4 : ℂ)) * star (q * (1/4 : ℂ)) = 1/8 := by
  have hs : (Real.sqrt (1/2)) ^ 2 = (1/2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr : ((Real.sqrt (1/2))⁻¹ / 4) ^ 2 = (1/8 : ℝ) := by
    rw [div_pow, inv_pow, hs]
    norm_num
  have he : q * (1/4 : ℂ) = (((Real.sqrt (1/2))⁻¹ / 4 : ℝ) : ℂ) := by
    simp [q, div_eq_mul_inv]
  rw [he]
  rw [show star ((((Real.sqrt (1/2))⁻¹ / 4 : ℝ) : ℂ)) =
    ((((Real.sqrt (1/2))⁻¹ / 4 : ℝ) : ℂ)) from Complex.conj_ofReal _]
  rw [← Complex.ofReal_mul]
  have hr' : ((Real.sqrt (1/2))⁻¹ / 4) * ((Real.sqrt (1/2))⁻¹ / 4) = (1/8 : ℝ) := by
    simpa only [pow_two] using hr
  rw [hr']
  norm_num

private lemma branch_marginal (r : Fin 2) : marginal (q • branch r) (if r = 0 then 2 else 0) =
    CStarMatrix.ofMatrix (diagonal fun a : Fin 9 => if a = 0 then (0 : ℂ) else 1/8) := by
  rw [branch, sparse_smul, marginal_sparse basis basis_injective _ _ (basis_separated _)]
  have hc (k : (Fin 2 × Fin 8)) : (q * coefficient r k) * star (q * coefficient r k) =
      if k.1 = r then (1/8 : ℂ) else 0 := by
    by_cases h : k.1 = r
    · simpa [coefficient, h] using q_product
    · simp [coefficient, h]
  simp_rw [hc]
  congr 1
  apply congrArg diagonal
  funext a
  fin_cases r <;> fin_cases a <;>
    norm_num [basis, Fintype.sum_prod_type, Fin.sum_univ_succ]

private lemma branch_max_lower (r : Fin 2) : 3 ≤ maxMarginalEntropy (q • branch r) := by
  change 3 ≤ ⨆ i : Fin 4, entropy2 (CStarMatrix.ofMatrix.symm (marginal (q • branch r) i))
  rw [← entropy_uniform]
  change entropy2 (CStarMatrix.ofMatrix.symm (CStarMatrix.ofMatrix (diagonal fun j : Fin 9 => if j = 0 then (0 : ℂ) else 1/8))) ≤ _
  rw [← branch_marginal r]
  exact le_ciSup (f := fun i : Fin 4 => entropy2 (CStarMatrix.ofMatrix.symm (marginal (q • branch r) i)))
    (Finite.bddAbove_range _) _

private lemma outcome_term (r : Fin 2) :
    (if finiteComplexEnergy (applyLocal (K r) 0 psi) = 0 then 0 else
      finiteComplexEnergy (applyLocal (K r) 0 psi) *
        maxMarginalEntropy (((Real.sqrt (finiteComplexEnergy (applyLocal (K r) 0 psi)))⁻¹ : ℂ) •
          applyLocal (K r) 0 psi)) =
      (1/2 : ℝ) * maxMarginalEntropy (q • branch r) := by
  rw [apply_K, branch_norm]
  rw [if_neg (by norm_num : (1/2 : ℝ) ≠ 0)]
  simp only [q, Complex.ofReal_inv]

end
end D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC

namespace D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC

open D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate (finiteComplexEnergy)

theorem result : ¬ D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC.claim := by
  intro H
  have h := H 4 9 2 psi 0 K psi_normalized K_complete
  change (∑ r : Fin 2, if finiteComplexEnergy (applyLocal (K r) 0 psi) = 0 then 0 else
    finiteComplexEnergy (applyLocal (K r) 0 psi) * maxMarginalEntropy
      (((Real.sqrt (finiteComplexEnergy (applyLocal (K r) 0 psi)))⁻¹ : ℂ) • applyLocal (K r) 0 psi)) ≤ maxMarginalEntropy psi at h
  simp only [outcome_term] at h
  rw [psi_max, Fin.sum_univ_two] at h
  have h0 := branch_max_lower 0
  have h1 := branch_max_lower 1
  linarith

end D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC
