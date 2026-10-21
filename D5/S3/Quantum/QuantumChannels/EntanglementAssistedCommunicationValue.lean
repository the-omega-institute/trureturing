/- GID: D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Entanglement-assisted communication value is bounded by the output dimension times cv. -/

import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages

/-! Operational communication values and their output-dimension comparison. -/

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Resource.CompositeCones
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages
  (separable_rankOne_add_reduced reduced)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue

/-- Complete positivity and preservation of the trace on every matrix. -/
def IsChannel {a b : ℕ} (N : MatrixMap (Fin a) (Fin b) ℂ) : Prop :=
  MatrixMap.IsCompletelyPositive N ∧ ∀ X, trace (N X) = trace X

/-- The sum, over outputs, of the largest conditional probability over inputs. -/
def classicalCV {n n' : ℕ} (hn : 1 ≤ n) (P : Fin n' → Fin n → ℝ) : ℝ :=
  ∑ y, Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (P y)

/-- Values of all finite state encodings and finite POVM decodings. -/
def commValues {a b : ℕ} (N : MatrixMap (Fin a) (Fin b) ℂ) : Set ℝ :=
  {v | ∃ (n n' : ℕ) (hn : 1 ≤ n), 1 ≤ n' ∧
    ∃ (ρ : Fin n → Matrix (Fin a) (Fin a) ℂ)
      (M : Fin n' → Matrix (Fin b) (Fin b) ℂ),
      (∀ x, (ρ x).PosSemidef ∧ trace (ρ x) = 1) ∧
      (∀ y, (M y).PosSemidef) ∧ ∑ y, M y = 1 ∧
      v = classicalCV hn (fun y x => (trace (M y * N (ρ x))).re)}

/-- The operational communication value of a quantum channel. -/
def commValue {a b : ℕ} (N : MatrixMap (Fin a) (Fin b) ℂ) : ℝ :=
  sSup (commValues N)

/-- Assisted values over all shared density matrices and local encoding channels. -/
def eaCommValues {a b : ℕ} (N : MatrixMap (Fin a) (Fin b) ℂ) : Set ℝ :=
  {v | ∃ (a' b' n n' : ℕ) (hn : 1 ≤ n), 1 ≤ n' ∧
    ∃ (φ : Matrix (Fin a' × Fin b') (Fin a' × Fin b') ℂ)
      (E : Fin n → MatrixMap (Fin a') (Fin a) ℂ)
      (M : Fin n' → Matrix (Fin b × Fin b') (Fin b × Fin b') ℂ),
      (φ.PosSemidef ∧ trace φ = 1) ∧ (∀ x, IsChannel (E x)) ∧
      (∀ y, (M y).PosSemidef) ∧ ∑ y, M y = 1 ∧
      v = classicalCV hn (fun y x =>
        (trace (M y * MatrixMap.kron (N ∘ₗ E x) (MatrixMap.id (Fin b') ℂ) φ)).re)}

/-- The supremum of all finite entanglement-assisted protocols. -/
def eaCommValue {a b : ℕ} (N : MatrixMap (Fin a) (Fin b) ℂ) : ℝ :=
  sSup (eaCommValues N)

/-- The output dimension bounds the multiplicative advantage of shared entanglement. -/
def claim : Prop :=
  ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → ∀ N : MatrixMap (Fin a) (Fin b) ℂ,
    IsChannel N → eaCommValue N ≤ (b : ℝ) * commValue N

private theorem cv_argmax {n n' : ℕ} (hn : 1 ≤ n) (P : Fin n' → Fin n → ℝ) :
    ∃ f : Fin n' → Fin n, classicalCV hn P = ∑ y, P y (f y) := by
  classical
  have h (y : Fin n') := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin n))) ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (P y)
  choose f _ hf using h
  exact ⟨f, Finset.sum_congr rfl (fun y _ => hf y)⟩

private theorem diagonal_sum_le_cv {n : ℕ} (hn : 1 ≤ n) (P : Fin n → Fin n → ℝ) :
    (∑ y, P y y) ≤ classicalCV hn P := by
  apply Finset.sum_le_sum
  intro y _
  exact Finset.le_sup' (P y) (Finset.mem_univ y)

private theorem state_effect_upper {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (htr : trace B = 1) :
    (trace (A * B)).re ≤ (trace A).re := by
  let U : Matrix (Fin d) (Fin d) ℂ := hA.1.eigenvectorUnitary
  let C := Uᴴ * B * U
  have hC : C.PosSemidef := hB.conjTranspose_mul_mul_same U
  have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.1.eigenvectorUnitary
  have hCt : trace C = 1 := by
    change trace (Uᴴ * B * U) = 1
    rw [trace_mul_cycle, hUU, Matrix.one_mul, htr]
  have hd (i : Fin d) : (C i i).re ≤ 1 := by
    have hs := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) =>
        (Complex.nonneg_iff.mp (hC.diag_nonneg (i := j))).1)
      (Finset.mem_univ i)
    have ht : ∑ j, (C j j).re = 1 := by
      rw [← Complex.re_sum]
      exact congrArg Complex.re hCt
    exact hs.trans_eq ht
  have hp : trace (A * B) =
      ∑ i, (hA.1.eigenvalues i : ℂ) * C i i := by
    have hspectral : A = U * diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * Uᴴ :=
      hA.1.spectral_theorem
    calc
      _ = trace ((U * diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * Uᴴ) * B) := by
        rw [← hspectral]
      _ = trace (C * diagonal (fun i => (hA.1.eigenvalues i : ℂ))) := by
        rw [Matrix.mul_assoc (U * diagonal _) Uᴴ B, trace_mul_cycle]
      _ = _ := by
        simp only [trace, diag_apply, Matrix.mul_diagonal]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
  rw [hp, hA.1.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact Finset.sum_le_sum fun i _ =>
    (mul_le_mul_of_nonneg_left (hd i) (hA.eigenvalues_nonneg i)).trans_eq (mul_one _)

private theorem comm_value_bounds {a b : ℕ} (ha : 1 ≤ a)
    (N : MatrixMap (Fin a) (Fin b) ℂ) (hN : IsChannel N) :
    (commValues N).Nonempty ∧ BddAbove (commValues N) ∧
      1 ≤ commValue N ∧ commValue N ≤ b := by
  have hu : ∀ v ∈ commValues N, v ≤ b := by
    rintro v ⟨n, n', hn, _, ρ, M, hρ, hM, hs, rfl⟩
    obtain ⟨f, hf⟩ := cv_argmax hn (fun y x => (trace (M y * N (ρ x))).re)
    rw [hf]
    calc
      _ ≤ ∑ y, (trace (M y)).re := Finset.sum_le_sum fun y _ =>
        state_effect_upper (M y) (N (ρ (f y))) (hM y)
          (hN.1.IsPositive (hρ (f y)).1) ((hN.2 _).trans (hρ (f y)).2)
      _ = b := by rw [← Complex.re_sum, ← trace_sum, hs]; simp
  have hm : (1 : ℝ) ∈ commValues N := by
    let i : Fin a := ⟨0, ha⟩
    let ρ : Fin 1 → Matrix (Fin a) (Fin a) ℂ := fun _ => single i i 1
    let M : Fin 1 → Matrix (Fin b) (Fin b) ℂ := fun _ => 1
    refine ⟨1, 1, le_rfl, le_rfl, ρ, M, ?_, ?_, ?_, ?_⟩
    · intro x
      constructor
      · convert Matrix.posSemidef_vecMulVec_self_star (Pi.single i (1 : ℂ)) using 1
        ext j l
        change single i i (1 : ℂ) j l = _
        by_cases hj : j = i <;> by_cases hl : l = i <;>
          simp [Matrix.single, vecMulVec_apply, Pi.single_apply, hj, hl, eq_comm]
      · exact Matrix.trace_single_eq_same i 1
    · intro y
      exact Matrix.PosSemidef.one
    · exact Fin.sum_univ_one M
    · have ht : trace (N (single i i 1)) = 1 :=
        (hN.2 _).trans (Matrix.trace_single_eq_same i 1)
      unfold classicalCV
      rw [Fin.sum_univ_one]
      symm
      apply Finset.sup'_eq_of_forall
      intro x _
      change (trace (1 * N (single i i 1))).re = 1
      rw [Matrix.one_mul, ht]
      rfl
  have hbdd : BddAbove (commValues N) := ⟨b, hu⟩
  exact ⟨⟨1, hm⟩, hbdd, le_csSup hbdd hm, csSup_le ⟨1, hm⟩ hu⟩

private theorem depolarized_separable {a b : ℕ}
    (Ω : Matrix (Fin b × Fin a) (Fin b × Fin a) ℂ) (hΩ : Ω.PosSemidef) :
    separableCone (Ω + (1 : Matrix (Fin b) (Fin b) ℂ) ⊗ₖ partialTraceLeft Ω) := by
  obtain ⟨k, ψ, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hΩ
  have hs := D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks.separableCone_sum _
    (fun i : Fin k =>
      separable_rankOne_add_reduced (ψ i))
  convert hs using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    partialTraceLeft,
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages.reduced]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem choi_tensor_pair {a b : ℕ} (N : MatrixMap (Fin a) (Fin b) ℂ)
    (Q : Matrix (Fin b) (Fin b) ℂ) (P : Matrix (Fin a) (Fin a) ℂ) :
    trace (MatrixMap.choi_matrix N * (Q ⊗ₖ P)) = trace (Q * N Pᵀ) := by
  have hN : N Pᵀ = fun i j => ∑ r, ∑ s, P s r * N (single r s 1) i j :=
    congrArg (fun L : MatrixMap (Fin a) (Fin b) ℂ => L Pᵀ)
      (MatrixMap.choi_map_inv N).symm
  rw [hN]
  simp only [trace, diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    MatrixMap.choi_matrix, kroneckerMap_apply, Finset.mul_sum]
  let e : (Fin b × Fin a × Fin b × Fin a) ≃ (Fin b × Fin b × Fin a × Fin a) :=
    { toFun := fun ⟨i, r, j, s⟩ => (j, i, r, s)
      invFun := fun ⟨j, i, r, s⟩ => (i, r, j, s)
      left_inv := by rintro ⟨i, r, j, s⟩; rfl
      right_inv := by rintro ⟨j, i, r, s⟩; rfl }
  have he := Fintype.sum_equiv e
    (fun ⟨i, r, j, s⟩ => N (single r s 1) i j * (Q j i * P s r))
    (fun ⟨j, i, r, s⟩ => Q j i * (P s r * N (single r s 1) i j))
    (by rintro ⟨i, r, j, s⟩; dsimp only [e, Equiv.coe_fn_mk]; ring)
  simpa only [Fintype.sum_prod_type] using he

private theorem separable_value_upper {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (N : MatrixMap (Fin a) (Fin b) ℂ) (hN : IsChannel N)
    (Ω : Matrix (Fin b × Fin a) (Fin b × Fin a) ℂ)
    (hsep : separableCone Ω) (hmarg : partialTraceRight Ω = 1) :
    (trace (MatrixMap.choi_matrix N * Ω)).re ≤ commValue N := by
  classical
  have hbdd := (comm_value_bounds ha N hN).2.1
  obtain ⟨w, hw⟩ := (comm_value_bounds ha N hN).1
  obtain ⟨n₀, n₀', hn₀, _, ρ₀, M₀, hρ₀, _⟩ := hw
  let R := ρ₀ ⟨0, hn₀⟩
  have hR : R.PosSemidef ∧ trace R = 1 := hρ₀ _
  obtain ⟨k, Q, P, hQP, hΩ⟩ := hsep
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    have hz : Ω = 0 := by simpa using hΩ
    rw [hz] at hmarg
    have he := congrFun (congrFun hmarg (⟨0, hb⟩ : Fin b)) (⟨0, hb⟩ : Fin b)
    simp [partialTraceRight] at he
  let t : Fin k → ℝ := fun i => (trace (P i)).re
  have ht (i : Fin k) : 0 ≤ t i := (Complex.nonneg_iff.mp (hQP i).2.trace_nonneg).1
  have htc (i : Fin k) : trace (P i) = (t i : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (hQP i).2.trace_nonneg).2.symm
  let ρ (i : Fin k) : Matrix (Fin a) (Fin a) ℂ :=
    if t i = 0 then R else (t i)⁻¹ • (P i)ᵀ
  let M (i : Fin k) : Matrix (Fin b) (Fin b) ℂ := t i • Q i
  have hρ (i : Fin k) : (ρ i).PosSemidef ∧ trace (ρ i) = 1 := by
    dsimp only [ρ]
    split_ifs with hi
    · exact hR
    · constructor
      · exact (hQP i).2.transpose.smul (inv_nonneg.mpr (ht i))
      · rw [trace_smul, trace_transpose, htc]
        rw [Complex.real_smul]
        change (((t i)⁻¹ : ℝ) : ℂ) * (t i : ℂ) = 1
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ hi, Complex.ofReal_one]
  have hM (i : Fin k) : (M i).PosSemidef := (hQP i).1.smul (ht i)
  have hsM : ∑ i, M i = 1 := by
    rw [← hmarg, hΩ]
    ext u v
    simp only [M, partialTraceRight, Matrix.sum_apply, Matrix.smul_apply,
      kroneckerMap_apply, Complex.real_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]
    change (t i : ℂ) * Q i u v = Q i u v * trace (P i)
    rw [htc]
    exact mul_comm _ _
  have hterm (i : Fin k) : trace (Q i * N (P i)ᵀ) = trace (M i * N (ρ i)) := by
    by_cases hi : t i = 0
    · have hP : P i = 0 := (hQP i).2.trace_eq_zero_iff.mp (by rw [htc, hi]; rfl)
      simp only [M, hi, zero_smul, hP, transpose_zero, map_zero, Matrix.mul_zero,
        Matrix.zero_mul, trace_zero]
    · have hscale : t i • ρ i = (P i)ᵀ := by
        dsimp only [ρ]
        rw [if_neg hi, smul_smul, mul_inv_cancel₀ hi, one_smul]
      change trace (Q i * N (P i)ᵀ) = trace ((t i • Q i) * N (ρ i))
      rw [Matrix.smul_mul, ← Matrix.mul_smul, ← N.map_smul_of_tower, hscale]
  have hv : classicalCV hk (fun y x => (trace (M y * N (ρ x))).re) ∈ commValues N :=
    ⟨k, k, hk, hk, ρ, M, hρ, hM, hsM, rfl⟩
  calc
    _ = ∑ i, (trace (M i * N (ρ i))).re := by
      rw [hΩ, Matrix.mul_sum, trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [choi_tensor_pair, hterm]
    _ ≤ classicalCV hk (fun y x => (trace (M y * N (ρ x))).re) :=
      diagonal_sum_le_cv hk (fun y x => (trace (M y * N (ρ x))).re)
    _ ≤ commValue N := le_csSup hbdd hv

private def contraction (a b r : ℕ) :
    Matrix (Fin b × Fin a) ((Fin a × Fin r) × (Fin b × Fin r)) ℂ :=
  fun i j => if i.2 = j.1.1 ∧ i.1 = j.2.1 ∧ j.1.2 = j.2.2 then 1 else 0

private def linkOp {a b r : ℕ}
    (σ : Matrix (Fin a × Fin r) (Fin a × Fin r) ℂ)
    (M : Matrix (Fin b × Fin r) (Fin b × Fin r) ℂ) :
    Matrix (Fin b × Fin a) (Fin b × Fin a) ℂ :=
  contraction a b r * (σᵀ ⊗ₖ M) * (contraction a b r)ᴴ

private theorem link_entry {a b r : ℕ}
    (σ : Matrix (Fin a × Fin r) (Fin a × Fin r) ℂ)
    (M : Matrix (Fin b × Fin r) (Fin b × Fin r) ℂ) (i j : Fin b × Fin a) :
    linkOp σ M i j = ∑ u, ∑ v, σ (j.2, v) (i.2, u) * M (i.1, u) (j.1, v) := by
  classical
  simp [linkOp, contraction, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, kroneckerMap_apply,
    ite_and, mul_ite, ite_mul, apply_ite]
  rw [Finset.sum_comm]

private theorem encoding_marginal {a a' r : ℕ}
    (E : MatrixMap (Fin a') (Fin a) ℂ) (hE : IsChannel E)
    (φ : Matrix (Fin a' × Fin r) (Fin a' × Fin r) ℂ) :
    partialTraceLeft (MatrixMap.kron E (MatrixMap.id (Fin r) ℂ) φ) =
      partialTraceLeft φ := by
  sorry

private theorem links_marginal {a b r n n' : ℕ}
    (σ : Fin n → Matrix (Fin a × Fin r) (Fin a × Fin r) ℂ)
    (M : Fin n' → Matrix (Fin b × Fin r) (Fin b × Fin r) ℂ)
    (τ : Matrix (Fin r) (Fin r) ℂ)
    (hσ : ∀ x, partialTraceLeft (σ x) = τ) (hτ : trace τ = 1)
    (hM : ∑ y, M y = 1) (f : Fin n' → Fin n) :
    partialTraceRight (∑ y, linkOp (σ (f y)) (M y)) = 1 := by
  ext i j
  change (∑ p, (∑ y, linkOp (σ (f y)) (M y)) (i, p) (j, p)) = _
  simp only [Matrix.sum_apply, link_entry]
  rw [Finset.sum_comm]
  have he : (∑ y, ∑ p, ∑ u, ∑ v, σ (f y) (p, v) (p, u) * M y (i, u) (j, v)) =
      ∑ y, ∑ u, ∑ v, τ v u * M y (i, u) (j, v) := by
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.sum_mul]
    change partialTraceLeft (σ (f y)) v u * _ = _
    rw [hσ]
  rw [he, Finset.sum_comm]
  have he' : (∑ u, ∑ y, ∑ v, τ v u * M y (i, u) (j, v)) =
      ∑ u, ∑ v, τ v u * (∑ y, M y) (i, u) (j, v) := by
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    simp only [Matrix.sum_apply, Finset.mul_sum]
  rw [he', hM]
  by_cases hij : i = j
  · subst j
    simpa [Matrix.one_apply, Prod.mk.injEq, trace] using hτ
  · simp [Matrix.one_apply, Prod.mk.injEq, hij]

private theorem link_pair_composed {a a' b r : ℕ}
    (N : MatrixMap (Fin a) (Fin b) ℂ) (E : MatrixMap (Fin a') (Fin a) ℂ)
    (φ : Matrix (Fin a' × Fin r) (Fin a' × Fin r) ℂ)
    (M : Matrix (Fin b × Fin r) (Fin b × Fin r) ℂ) :
    trace (MatrixMap.choi_matrix N *
      linkOp (MatrixMap.kron E (MatrixMap.id (Fin r) ℂ) φ) M) =
      trace (M * MatrixMap.kron (N ∘ₗ E) (MatrixMap.id (Fin r) ℂ) φ) := by
  sorry

private theorem assisted_operator {a b : ℕ} (N : MatrixMap (Fin a) (Fin b) ℂ)
    {v : ℝ} (hv : v ∈ eaCommValues N) :
    ∃ Ω : Matrix (Fin b × Fin a) (Fin b × Fin a) ℂ,
      Ω.PosSemidef ∧ partialTraceRight Ω = 1 ∧
      v = (trace (MatrixMap.choi_matrix N * Ω)).re := by
  rcases hv with ⟨a', r, n, n', hn, _, φ, E, M, hφ, hE, hM, hsM, rfl⟩
  let σ (x : Fin n) := MatrixMap.kron (E x) (MatrixMap.id (Fin r) ℂ) φ
  obtain ⟨f, hf⟩ := cv_argmax hn (fun y x =>
    (trace (M y * MatrixMap.kron (N ∘ₗ E x) (MatrixMap.id (Fin r) ℂ) φ)).re)
  refine ⟨∑ y, linkOp (σ (f y)) (M y), ?_, ?_, ?_⟩
  · apply Matrix.posSemidef_sum
    intro y _
    exact (((hE (f y)).1 r hφ.1).transpose.kronecker (hM y)).mul_mul_conjTranspose_same _
  · exact links_marginal σ M (partialTraceLeft φ) (fun x => encoding_marginal _ (hE x) φ)
      ((trace_partialTraceLeft φ).trans hφ.2) hsM f
  · rw [hf, Matrix.mul_sum, trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro y _
    exact congrArg Complex.re (link_pair_composed N (E (f y)) φ (M y)).symm

private theorem assisted_value_bound {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (N : MatrixMap (Fin a) (Fin b) ℂ) (hN : IsChannel N)
    {v : ℝ} (hv : v ∈ eaCommValues N) : v ≤ (b : ℝ) * commValue N := by
  obtain ⟨Ω, hΩ, hmarg, hvalue⟩ := assisted_operator N hv
  have hsep := depolarized_separable Ω hΩ
  have hbound := comm_value_bounds ha N hN
  have htrace : trace (partialTraceLeft Ω) = (b : ℂ) := by
    rw [trace_partialTraceLeft, ← trace_partialTraceRight Ω, hmarg]
    simp
  have hnormalized :
      partialTraceRight (((b : ℝ) + 1)⁻¹ •
        (Ω + (1 : Matrix (Fin b) (Fin b) ℂ) ⊗ₖ partialTraceLeft Ω)) = 1 := by
    have he : partialTraceRight
        (Ω + (1 : Matrix (Fin b) (Fin b) ℂ) ⊗ₖ partialTraceLeft Ω) =
        ((b : ℂ) + 1) • (1 : Matrix (Fin b) (Fin b) ℂ) := by
      rw [partialTraceRight_add, hmarg]
      change 1 + partialTraceRight (kronecker 1 (partialTraceLeft Ω)) = _
      rw [partialTraceRight_kronecker, htrace,
        add_smul, one_smul, add_comm]
    ext i j
    change (∑ k, (((b : ℝ) + 1)⁻¹ •
      (Ω + (1 : Matrix (Fin b) (Fin b) ℂ) ⊗ₖ partialTraceLeft Ω)) (i, k) (j, k)) = _
    simp only [Matrix.smul_apply, Complex.real_smul, ← Finset.mul_sum]
    change ((((b : ℝ) + 1)⁻¹ : ℝ) : ℂ) *
      partialTraceRight (Ω + (1 : Matrix (Fin b) (Fin b) ℂ) ⊗ₖ partialTraceLeft Ω) i j = _
    rw [he]
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    have hc : ((((b : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ((b : ℂ) + 1) = 1 := by
      have hb0 : (b : ℝ) + 1 ≠ 0 := by positivity
      exact_mod_cast inv_mul_cancel₀ hb0
    rw [hc, one_mul]
  have hs := separable_value_upper ha hb N hN _
    (D5.S3.Resource.EntanglementWitness.separableCone_smul (by positivity) hsep) hnormalized
  have hobj :
      (trace (MatrixMap.choi_matrix N * (((b : ℝ) + 1)⁻¹ •
        (Ω + (1 : Matrix (Fin b) (Fin b) ℂ) ⊗ₖ partialTraceLeft Ω)))).re =
      (v + b) / (b + 1) := by
    have ht := choi_tensor_pair N (1 : Matrix (Fin b) (Fin b) ℂ) (partialTraceLeft Ω)
    rw [Matrix.one_mul, hN.2, trace_transpose, htrace] at ht
    rw [Matrix.mul_smul, Matrix.mul_add, trace_smul, trace_add, ht,
      Complex.real_smul, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re, ← hvalue, Complex.natCast_re]
    exact (div_eq_inv_mul _ _).symm
  rw [hobj] at hs
  have hbpos : (0 : ℝ) < b + 1 := by positivity
  have hmul := (div_le_iff₀ hbpos).mp hs
  nlinarith [hbound.2.2.2]

theorem result : claim := by
  intro a b ha hb N hN
  apply Real.sSup_le
  · intro v hv
    exact assisted_value_bound ha hb N hN hv
  · exact mul_nonneg (Nat.cast_nonneg b) (le_trans zero_le_one
      (comm_value_bounds ha N hN).2.2.1)

end D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue
