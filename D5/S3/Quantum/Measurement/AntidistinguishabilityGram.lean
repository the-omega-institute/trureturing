/- GID: D5/S3/Quantum/Measurement/AntidistinguishabilityGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/AntidistinguishabilityGram
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: AntidistinguishabilityGram supports the overlap bound. -/

/-
proof_shape: IsAntidistinguishable: bind-only; consumer: IsTight, incoherent_gram_antidistinguishable, not_tight_of_quantitative
escape_witness: IsAntidistinguishable: none
Direct frozen dependencies: IsAntidistinguishable: none
proof_shape: cSq: bind-only; consumer: IsTight, cSq_lt_half, cSq_nonneg, not_tight_of_quantitative, overlap_excess_identity, overlap_target_distance_bound, quantitative_antidistinguishability, quantitative_rank_contradiction, quantitative_spectral_condition, quantitative_state_spectral_condition
escape_witness: cSq: none
Direct frozen dependencies: cSq: none
proof_shape: delta: bind-only; consumer: delta_budget, delta_overlap_budget, delta_pos, not_tight_of_quantitative, quantitative_antidistinguishability, quantitative_spectral_condition, quantitative_state_spectral_condition
escape_witness: delta: none
Direct frozen dependencies: delta: none
proof_shape: IsIncoherent: bind-only; consumer: incoherent_add, incoherent_closed, incoherent_gram_antidistinguishable, incoherent_separation, incoherent_smul, spectral_balanced_incoherent
escape_witness: IsIncoherent: none
Direct frozen dependencies: IsIncoherent: none
proof_shape: psd_summand_kills_kernel: bind-only; consumer: psd_summand_projection
escape_witness: psd_summand_kills_kernel: none
Direct frozen dependencies: psd_summand_kills_kernel: none
proof_shape: hermitian_projection_complement_psd: bind-only; consumer: incoherent_gram_antidistinguishable
escape_witness: hermitian_projection_complement_psd: none
Direct frozen dependencies: hermitian_projection_complement_psd: none
proof_shape: matrix_penrose_exists: bind-only; consumer: incoherent_gram_antidistinguishable
escape_witness: matrix_penrose_exists: none
Direct frozen dependencies: matrix_penrose_exists: F1, F2, F3, F4, F5, F6, F7
proof_shape: stateGram_matrix: bind-only; consumer: incoherent_gram_antidistinguishable
escape_witness: stateGram_matrix: none
Direct frozen dependencies: stateGram_matrix: none
proof_shape: quadratic_column: bind-only; consumer: incoherent_gram_antidistinguishable
escape_witness: quadratic_column: none
Direct frozen dependencies: quadratic_column: none
proof_shape: LocallyPsd: bind-only; consumer: incoherent_separation, local_psd_adjugate_diag_nonneg, local_psd_inverse_trace_nonpos, local_psd_isUnit_det, local_psd_kernel_eq_zero, local_psd_negIndex, local_psd_negative_spectrum, local_psd_principal, local_psd_reciprocal_budget, spectral_balanced_incoherent, spectral_balanced_pairing_nonneg
escape_witness: LocallyPsd: none
Direct frozen dependencies: LocallyPsd: F10
proof_shape: orderedSpectrum_antitone: bind-only; consumer: quantitative_spectral_condition, spectral_balanced_of_ordered, topThree_failure_distance
escape_witness: orderedSpectrum_antitone: none
Direct frozen dependencies: orderedSpectrum_antitone: F8, F9
proof_shape: orderedSpectrum_nonneg: bind-only; consumer: quantitative_spectral_condition, topThree_failure_distance, topThree_gram_factor
escape_witness: orderedSpectrum_nonneg: none
Direct frozen dependencies: orderedSpectrum_nonneg: F8
proof_shape: sum_orderedSpectrum: bind-only; consumer: quantitative_spectral_condition, spectral_balanced_of_ordered, topThree_failure_distance
escape_witness: sum_orderedSpectrum: none
Direct frozen dependencies: sum_orderedSpectrum: F8
proof_shape: gramPsd: bind-only; consumer: quantitative_state_spectral_condition, spectral_sufficient_antidistinguishable
escape_witness: gramPsd: none
Direct frozen dependencies: gramPsd: none
proof_shape: stateGram_diag: bind-only; consumer: quantitative_state_spectral_condition
escape_witness: stateGram_diag: none
Direct frozen dependencies: stateGram_diag: none
proof_shape: psd_summand_projection: bind-only; consumer: incoherent_gram_antidistinguishable
escape_witness: psd_summand_projection: none
Direct frozen dependencies: psd_summand_projection: none
proof_shape: incoherent_gram_antidistinguishable: content; consumer: spectral_sufficient_antidistinguishable
escape_witness: incoherent_gram_antidistinguishable: incoherent_gram_antidistinguishable
Direct frozen dependencies: incoherent_gram_antidistinguishable: F1, F2, F3, F4, F5, F6, F7
admission_basis: escape-witness
Frozen declaration identities:
F1: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse
  declaration statement_id: sha256:2a6c958072ca7dbf1881d1a83e4066dd700c1cbf16aa0e16badfd03daf7b570f
F2: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.comp_comp_self
  declaration statement_id: sha256:5d4cb4f02e32fbc6a78b9f61a1422f801c136bab622aa301506fd1fe73fb83e3
F3: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.comp_comp_self'
  declaration statement_id: sha256:96b5ec221bccb262c6327be49075e74bd10e17611a518a8716f2105adeba5e0a
F4: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.isSymmetric_comp
  declaration statement_id: sha256:6f091bad6d67a58d7e870f0ac224732ce51ad0562376da86bee4ab6097c546cc
F5: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.IsMoorePenroseInverse.isSymmetric_comp'
  declaration statement_id: sha256:6e455107e336f3d6977f59a532bc341a759522fedd448aa883c77865efa182f3
F6: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.isMoorePenroseInverse_moorePenroseInverse
  declaration statement_id: sha256:18736e4b1629c6ccacac40723a79c65171780f9e9f6296b93251162549f27768
F7: owner GID: D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse; declaration: D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.moorePenroseInverse
  declaration statement_id: sha256:d0c42c7ebe852755b1e0ac182e1eba16a13f9d7bc80db23d35a6e897dc56df5a
F8: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.eigEquiv
  declaration statement_id: sha256:654ba75dc9fc8ba7043bc07f2e652d247648fdb01580c0e2815eda462b33ec96
F9: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.eigenvalues_eigEquiv
  declaration statement_id: sha256:3a5feeadf2e296b0d896b6b5b9cbfcf77259c1c43366cd9c038d988f06920ea1
F10: owner GID: D5/S3/Weil/ZetaLinear/Sylvester; declaration: RHLinalg.hermForm
  declaration statement_id: sha256:80fb2c125caa6f180274d058b22d584cf1572b3089380febbc5dfae997f03ebf
Definition rows classify unfolding; they assert no proposition and supply no escape witness.
Utility: none; finite-dimensional symbolic mathematics for arbitrary parameters.
The Gram construction is Matrix.gram; state columns have no forwarding definition.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15730.
DTR reading: DTR-Unregistered for the public theorem targets in this module.
Registration gap: exact dependent source-family reconstruction, lawful template readout,
selection coordinates, whole-family variation, slot sensitivity and observational dependence
are not all established by the retained registration evidence.
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.Weil.ZetaLinear.Sylvester

open Matrix Finset Filter Unitary
open scoped BigOperators ComplexOrder Topology RealInnerProductSpace

namespace D5.S3.Quantum.Measurement.AntidistinguishabilityGram
noncomputable section

section


def IsAntidistinguishable {n d : ℕ}
    (ψ : Fin n → EuclideanSpace ℂ (Fin d)) : Prop :=
  ∃ M : Fin n → Matrix (Fin d) (Fin d) ℂ,
    (∀ i, (M i).PosSemidef) ∧ ∑ i, M i = 1 ∧
      ∀ i, star (ψ i : Fin d → ℂ) ⬝ᵥ
        (M i *ᵥ (ψ i : Fin d → ℂ)) = 0

end

section


def cSq (n : ℕ) : ℝ := ((n : ℝ) - 2) / (2 * ((n : ℝ) - 1))

end

section


def delta (n : ℕ) : ℝ :=
  ((n : ℝ) - 9) / (16 * (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 3))

end

section
variable {n d : ℕ}

def IsIncoherent (G : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ F : Fin n → Matrix (Fin n) (Fin n) ℂ,
    (∀ i, (F i).PosSemidef) ∧ ∑ i, F i = G ∧ ∀ i, F i i i = 0

end

section
variable {n d : ℕ}

theorem psd_summand_kills_kernel (F : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i, (F i).PosSemidef) (x : Fin n → ℂ)
    (hx : (∑ i, F i) *ᵥ x = 0) (i : Fin n) : F i *ᵥ x = 0 := by
  have hs : (∑ j, (star x ⬝ᵥ (F j *ᵥ x)).re) = 0 := by
    change (∑ j, Complex.reAddGroupHom (star x ⬝ᵥ (F j *ᵥ x))) = 0
    rw [← map_sum, ← dotProduct_sum, ← Matrix.sum_mulVec, hx]
    simp
  have hn : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ (star x ⬝ᵥ (F j *ᵥ x)).re := by
    intro j _
    exact (hF j).re_dotProduct_nonneg x
  have hri := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hs i (mem_univ i)
  have him := (Complex.nonneg_iff.mp ((hF i).dotProduct_mulVec_nonneg x)).2
  apply (hF i).dotProduct_mulVec_zero_iff |>.mp
  exact Complex.ext hri him.symm

end

section
variable {n d : ℕ}

theorem hermitian_projection_complement_psd (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) : (1-P).PosSemidef := by
  have he : (1-P)*(1-P)ᴴ = 1-P := by
    rw [(Matrix.isHermitian_one.sub hP).eq]
    simp only [Matrix.sub_mul, mul_sub, Matrix.one_mul, mul_one, hPP]
    abel
  rw [← he]
  exact Matrix.posSemidef_self_mul_conjTranspose _

end

section
variable {n d : ℕ}

theorem matrix_penrose_exists (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ B : Matrix (Fin n) (Fin d) ℂ,
      A*B*A=A ∧ B*A*B=B ∧ (A*B).IsHermitian ∧ (B*A).IsHermitian := by
  let a := A.toEuclideanLin
  let b := D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.moorePenroseInverse a
  let B : Matrix (Fin n) (Fin d) ℂ := Matrix.toEuclideanLin.symm b
  have hb : B.toEuclideanLin = b := Matrix.toEuclideanLin.apply_symm_apply b
  have hp := D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse.isMoorePenroseInverse_moorePenroseInverse a
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · apply Matrix.toEuclideanLin.injective
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, hb, LinearMap.comp_assoc, a] using hp.comp_comp_self
  · apply Matrix.toEuclideanLin.injective
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, hb, LinearMap.comp_assoc, a] using hp.comp_comp_self'
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, hb, a] using hp.isSymmetric_comp
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, hb, a] using hp.isSymmetric_comp'

end

section
variable {n d : ℕ}

private theorem stateGram_matrix (ψ : Fin n → EuclideanSpace ℂ (Fin d)) :
    (Matrix.gram ℂ ψ) = (Matrix.of (fun (k : Fin d) (i : Fin n) => (ψ i : Fin d → ℂ) k))ᴴ * Matrix.of (fun (k : Fin d) (i : Fin n) => (ψ i : Fin d → ℂ) k) := by
  simpa only [EuclideanSpace.basisFun_repr] using
    Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin d) ℂ) ψ

end

section
variable {n d : ℕ}

private theorem quadratic_column (A : Matrix (Fin d) (Fin n) ℂ)
    (C : Matrix (Fin d) (Fin d) ℂ) (i : Fin n) :
    star (A.col i) ⬝ᵥ (C *ᵥ A.col i) = (Aᴴ*C*A) i i := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
    Matrix.col, Matrix.transpose_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

end

section
variable {n : ℕ}

def LocallyPsd (Y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Y.IsHermitian ∧ ∀ j (x : Fin n → ℂ), x j=0 → 0 ≤ RHLinalg.hermForm Y x

end

section
variable {n : ℕ}

theorem orderedSpectrum_antitone {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    Antitone ((fun k : Fin n => hA.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k))) := by
  intro i j hij
  dsimp only
  simp only [Equiv.trans_apply, RHLinalg.eigenvalues_eigEquiv]
  apply hA.eigenvalues₀_antitone
  exact hij

end

section
variable {n : ℕ}

theorem orderedSpectrum_nonneg {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    ∀ k, 0 ≤ (fun k : Fin n => hA.isHermitian.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k :=
  fun k => hA.eigenvalues_nonneg _

end

section
variable {n : ℕ}

theorem sum_orderedSpectrum {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    (∑ k, f ((fun k : Fin n => hA.eigenvalues (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv) k)) k)) = ∑ j, f (hA.eigenvalues j) := by
  exact (((finCongr (Fintype.card_fin n).symm).trans RHLinalg.eigEquiv)).sum_comp (fun j => f (hA.eigenvalues j))

end

section
variable {n d : ℕ}

theorem gramPsd (ψ : Fin n → EuclideanSpace ℂ (Fin d)) :
    ((Matrix.gram ℂ ψ)).PosSemidef := by
  exact Matrix.posSemidef_gram ℂ ψ

end

section
variable {n d : ℕ}

theorem stateGram_diag (ψ : Fin n → EuclideanSpace ℂ (Fin d))
    (hnorm : ∀ i, ‖ψ i‖ = 1) (i : Fin n) : (Matrix.gram ℂ ψ) i i = 1 := by
  simp [Matrix.gram, Matrix.gram, inner_self_eq_norm_sq_to_K, hnorm]

end

section
variable {n d : ℕ}

theorem psd_summand_projection (F : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i, (F i).PosSemidef) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) (hGQ : (∑ i, F i)*Q = ∑ i, F i) (i : Fin n) :
    Q * F i * Q = F i := by
  have hGD : (∑ i, F i)*(1-Q) = 0 := by rw [mul_sub, mul_one, hGQ, sub_self]
  have hFD : F i*(1-Q) = 0 := by
    ext j k
    have hk : (∑ i, F i) *ᵥ (1-Q).col k = 0 := by
      rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hGD, Matrix.zero_mulVec]
    have hf := psd_summand_kills_kernel F hF ((1-Q).col k) hk i
    exact congrFun hf j
  have hFQ : F i*Q = F i := by
    rw [mul_sub, mul_one] at hFD
    exact (sub_eq_zero.mp hFD).symm
  have hQF : Q*F i = F i := by
    have ht := congrArg Matrix.conjTranspose hFQ
    simpa only [Matrix.conjTranspose_mul, hQ.eq, (hF i).isHermitian.eq] using ht
  rw [hQF, hFQ]

end

section
variable {n d : ℕ}

theorem incoherent_gram_antidistinguishable (hn : 1 ≤ n)
    (ψ : Fin n → EuclideanSpace ℂ (Fin d)) (hinc : IsIncoherent ((Matrix.gram ℂ ψ))) :
    IsAntidistinguishable ψ := by
  obtain ⟨F, hF, hsum, hzero⟩ := hinc
  let A : Matrix (Fin d) (Fin n) ℂ := Matrix.of (fun k i => (ψ i : Fin d → ℂ) k)
  obtain ⟨B, hABA, hBAB, hAB, hBA⟩ := matrix_penrose_exists A
  let P := A*B
  let Q := B*A
  let i0 : Fin n := ⟨0, by omega⟩
  let M : Fin n → Matrix (Fin d) (Fin d) ℂ :=
    fun i => Bᴴ*F i*B + if i=i0 then 1-P else 0
  have hsumG : ∑ i, F i = Aᴴ*A := hsum.trans (stateGram_matrix ψ)
  have hPP : P*P=P := by
    change (A*B)*(A*B) = A*B
    rw [← Matrix.mul_assoc, hABA]
  have hcomp : (1-P).PosSemidef := hermitian_projection_complement_psd P hAB hPP
  have hGQ : (∑ i, F i)*Q=∑ i, F i := by
    rw [hsumG]
    change (Aᴴ*A)*(B*A)=Aᴴ*A
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A B A, hABA]
  have hQF : ∀ i, Q*F i*Q=F i := psd_summand_projection F hF Q hBA hGQ
  have hbase : Bᴴ*(∑ i, F i)*B=P := by
    rw [hsumG]
    change Bᴴ*(Aᴴ*A)*B=A*B
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc,
      hAB.eq, ← Matrix.mul_assoc, hABA]
  have hsumM : ∑ i, M i = 1 := by
    simp only [M, Finset.sum_add_distrib]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hbase]
    simp [i0]
  have hCA : (1-P)*A=0 := by
    change (1-A*B)*A=0
    rw [Matrix.sub_mul, Matrix.one_mul, hABA, sub_self]
  have hMquad : ∀ i, Aᴴ*M i*A=F i := by
    intro i
    have hb : Aᴴ*(Bᴴ*F i*B)*A=F i := by
      change Aᴴ*(Bᴴ*F i*B)*A=F i
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul]
      rw [Matrix.mul_assoc ((B*A)ᴴ*F i) B A]
      change Qᴴ*F i*Q=F i
      rw [hBA.eq, hQF i]
    dsimp [M]
    rw [Matrix.mul_add, Matrix.add_mul, hb]
    split_ifs
    · rw [Matrix.mul_assoc, hCA, Matrix.mul_zero, add_zero]
    · simp
  refine ⟨M, ?_, hsumM, ?_⟩
  · intro i
    dsimp [M]
    apply ((hF i).conjTranspose_mul_mul_same B).add
    split_ifs
    · exact hcomp
    · exact Matrix.PosSemidef.zero
  · intro i
    change star (A.col i) ⬝ᵥ (M i *ᵥ A.col i)=0
    rw [quadratic_column A (M i) i, hMquad i]
    exact hzero i

end

end
end D5.S3.Quantum.Measurement.AntidistinguishabilityGram
