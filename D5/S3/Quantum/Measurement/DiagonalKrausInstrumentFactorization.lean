/- GID: D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Aggregate column orthogonality characterizes diagonal Kraus instrument factorization. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel

/-! Finite instrument branches preserve diagonal matrices exactly when the
Kraus-index Gram sums of distinct output rows vanish in every input column. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization

open D5.S3.Quantum.Foundation.FiniteKrausChannel
open PhyslibLeaf

variable {I O A B R : Type*}
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
  [Fintype B] [Fintype R]

/-- The weight from input coordinate `i` to output coordinate `o` in outcome `b`
at setting `a`. Summation discards only the Kraus index. -/
def weight (K : A → B → R → Matrix O I ℂ) (a : A) (b : B) (o : O) (i : I) : ℝ :=
  ∑ r, Complex.normSq (K a b r o i)

omit [Fintype O] [DecidableEq O] [Fintype B] in
private theorem diagonal_entry_expansion
    (K : R → Matrix O I ℂ) (p : I → ℂ) (o o' : O) :
    MatrixMap.of_kraus K K (Matrix.diagonal p) o o' =
      ∑ i, (∑ r, K r o i * (starRingEnd ℂ) (K r o' i)) * p i := by
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

omit [Fintype O] [Fintype B] in
private theorem diagonal_factorization_of_orthogonality
    (K : A → B → R → Matrix O I ℂ)
    (hgram : ∀ a b i o o', o ≠ o' →
      ∑ r, K a b r o i * (starRingEnd ℂ) (K a b r o' i) = 0)
    (p : I → ℂ) (a : A) (b : B) :
    MatrixMap.of_kraus (K a b) (K a b) (Matrix.diagonal p) =
      Matrix.diagonal fun o => (∑ i, (weight K a b o i : ℂ) * p i) := by
  ext o o'
  rw [diagonal_entry_expansion]
  by_cases hoo : o = o'
  · subst o'
    simp only [Matrix.diagonal_apply_eq, weight, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  · simp [Matrix.diagonal_apply_ne _ hoo, hgram a b _ _ _ hoo]

/-- Global completeness normalizes the weights over outcomes and output coordinates.
The aggregate Gram condition is equivalent to factorization of every complex diagonal
input through this nonnegative kernel. The last clause supplies the total channel,
without normalizing its individual outcome branches. -/
theorem diagonal_instrument_factorization
    (K : A → B → R → Matrix O I ℂ)
    (hcomplete : ∀ a, ∑ b, ∑ r, (K a b r).conjTranspose * K a b r = 1) :
    (∀ a b o i, 0 ≤ weight K a b o i) ∧
    (∀ a i, ∑ b, ∑ o, weight K a b o i = 1) ∧
    ((∀ a b i o o', o ≠ o' →
        ∑ r, K a b r o i * (starRingEnd ℂ) (K a b r o' i) = 0) ↔
      ∀ (p : I → ℂ) a b,
        MatrixMap.of_kraus (K a b) (K a b) (Matrix.diagonal p) =
          Matrix.diagonal fun o => (∑ i, (weight K a b o i : ℂ) * p i)) ∧
    (∀ a, ∃ channel : D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel I O,
      ∀ rho : Matrix I I ℂ,
        CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
          ∑ b, MatrixMap.of_kraus (K a b) (K a b) rho) := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro a b o i
    exact Finset.sum_nonneg fun r _ => Complex.normSq_nonneg _
  · intro a i
    have hi := congrArg (fun M : Matrix I I ℂ => M i i) (hcomplete a)
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq, Complex.star_def] at hi
    apply Complex.ofReal_injective
    push_cast
    unfold weight
    push_cast
    rw [show (∑ b, ∑ o, ∑ r, (Complex.normSq (K a b r o i) : ℂ)) =
        ∑ b, ∑ r, ∑ o, (Complex.normSq (K a b r o i) : ℂ) by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm]
    simpa only [Complex.normSq_eq_conj_mul_self] using hi
  · exact diagonal_factorization_of_orthogonality K
  · intro hfactor a b i o o' hoo
    have hi := congrArg (fun M : Matrix O O ℂ => M o o')
      (hfactor (fun j => if j = i then 1 else 0) a b)
    rw [diagonal_entry_expansion] at hi
    simpa [Matrix.diagonal_apply_ne _ hoo, apply_ite, mul_ite] using hi
  · intro a
    have hc : ∑ t : B × R, (K a t.1 t.2).conjTranspose * K a t.1 t.2 = 1 := by
      simpa only [Fintype.sum_prod_type] using hcomplete a
    obtain ⟨channel, hchannel⟩ := finite_kraus_quantum_channel
      (fun t : B × R => K a t.1 t.2) hc
    refine ⟨channel, fun rho => ?_⟩
    simpa only [Fintype.sum_prod_type, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk] using hchannel rho

#print axioms diagonal_instrument_factorization

end D5.S3.Quantum.Measurement.DiagonalKrausInstrumentFactorization
