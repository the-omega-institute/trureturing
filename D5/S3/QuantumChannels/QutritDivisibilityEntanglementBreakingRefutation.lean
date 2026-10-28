/- GID: D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.claim; result=D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.result; claim=D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.claim
   digest: A divisible qutrit channel outside P-divisibility is not entanglement breaking. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Resource.CompositeCones
import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite

/-! A fixed qutrit counterexample to the higher-dimensional divisibility claim. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Resource.CompositeCones
open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (partialTranspose)

namespace D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation

noncomputable section

private def IsCPTP (T : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  T.IsCompletelyPositive ∧ T.IsTracePreserving

private def IsUnitaryChannel (T : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  ∃ U : Matrix.unitaryGroup (Fin 3) ℂ, ∀ X,
    T X = (U : Matrix (Fin 3) (Fin 3) ℂ) * X *
      (U : Matrix (Fin 3) (Fin 3) ℂ).conjTranspose

private def IsDivisible (T : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  ∃ T₁ T₂, IsCPTP T₁ ∧ IsCPTP T₂ ∧ T = T₁.comp T₂ ∧
    ¬ IsUnitaryChannel T₁ ∧ ¬ IsUnitaryChannel T₂

private def IsPositiveTP (V : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  (∀ ⦃X⦄, X.PosSemidef → (V X).PosSemidef) ∧ V.IsTracePreserving

private noncomputable def transferMatrix (T : MatrixMap (Fin 3) (Fin 3) ℂ) :=
  LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin 3) (Fin 3))
    (Matrix.stdBasis ℂ (Fin 3) (Fin 3)) T

private def IsPDivisibleMap (E : ℝ → MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  E 0 = LinearMap.id ∧
    (∀ t, 0 ≤ t → IsCPTP (E t)) ∧
    ContinuousOn (fun t => transferMatrix (E t)) (Set.Ici (0 : ℝ)) ∧
    (∀ t s, 0 ≤ t → t < s → ∃ V, IsPositiveTP V ∧ E s = V.comp (E t))

private def pDivisibleSet : Set (MatrixMap (Fin 3) (Fin 3) ℂ) :=
  {T | transferMatrix T ∈ closure {M | ∃ E, IsPDivisibleMap E ∧ ∃ t, 0 ≤ t ∧
    M = transferMatrix (E t)}}

private def IsEntanglementBreaking (T : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ n : ℕ, ∀ rho : Matrix (Fin n × Fin 3) (Fin n × Fin 3) ℂ,
    rho.PosSemidef → rho.trace = 1 →
      separableCone (MatrixMap.kron (LinearMap.id : MatrixMap (Fin n) (Fin n) ℂ) T rho)

def claim : Prop :=
  ∀ T, IsCPTP T → IsDivisible T → T ∉ pDivisibleSet → IsEntanglementBreaking T

private def w : MatrixMap (Fin 3) (Fin 3) ℂ where
  toFun X := (1 / 2 : ℂ) • (X.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - X.transpose)
  map_add' X Y := by
    ext i j
    simp [Matrix.trace_add, Matrix.transpose_apply]
    ring
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul, Matrix.transpose_apply]
    ring

private def d : MatrixMap (Fin 3) (Fin 3) ℂ where
  toFun X := (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • (X.trace / 3) •
    (1 : Matrix (Fin 3) (Fin 3) ℂ)
  map_add' X Y := by
    ext i j
    simp [Matrix.trace_add]
    ring
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul]
    ring

private def t : MatrixMap (Fin 3) (Fin 3) ℂ := d.comp w

private lemma w_formula (X : Matrix (Fin 3) (Fin 3) ℂ) :
    w X = (1 / 2 : ℂ) • (X.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - X.transpose) := by rfl

private lemma d_formula (X : Matrix (Fin 3) (Fin 3) ℂ) :
    d X = (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • (X.trace / 3) •
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by rfl

private lemma t_formula (X : Matrix (Fin 3) (Fin 3) ℂ) :
    t X = (5 / 12 : ℂ) • X.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      (1 / 4 : ℂ) • X.transpose := by
  ext i j
  simp [t, d_formula, w_formula, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_transpose, Matrix.trace_one, Fintype.card_fin]
  ring

private lemma w_cptp : IsCPTP w := by sorry

private lemma d_cptp : IsCPTP d := by sorry

private lemma t_cptp : IsCPTP t := by sorry

private lemma w_not_unitary : ¬ IsUnitaryChannel w := by sorry

private lemma d_not_unitary : ¬ IsUnitaryChannel d := by sorry

private lemma t_divisible : IsDivisible t := by
  exact ⟨d, w, d_cptp, w_cptp, rfl, d_not_unitary, w_not_unitary⟩

private lemma hermiticity_preserving_det_real (T : MatrixMap (Fin 3) (Fin 3) ℂ)
    (hT : ∀ X, T X.conjTranspose = (T X).conjTranspose) :
    (Matrix.det (transferMatrix T)).im = 0 := by sorry

private lemma pdivisible_endpoint_det_nonneg {E : ℝ → MatrixMap (Fin 3) (Fin 3) ℂ}
    (hE : IsPDivisibleMap E) (u : ℝ) (hu : 0 ≤ u) :
    (Matrix.det (transferMatrix (E u))).im = 0 ∧
      0 ≤ (Matrix.det (transferMatrix (E u))).re := by sorry

private def nonnegativeDetSet : Set (MatrixMap (Fin 3) (Fin 3) ℂ) :=
  {T | (Matrix.det (transferMatrix T)).im = 0 ∧
    0 ≤ (Matrix.det (transferMatrix T)).re}

private lemma pdivisibleSet_subset_nonnegativeDet :
    pDivisibleSet ⊆ nonnegativeDetSet := by sorry

private lemma t_det : Matrix.det (transferMatrix t) = -(1 / 4 : ℂ) ^ 8 := by sorry

private lemma t_not_pdivisible : t ∉ pDivisibleSet := by
  intro ht
  have hnonneg := pdivisibleSet_subset_nonnegativeDet ht
  change (Matrix.det (transferMatrix t)).im = 0 ∧
    0 ≤ (Matrix.det (transferMatrix t)).re at hnonneg
  rw [t_det] at hnonneg
  norm_num at hnonneg

private def omega : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  ((1 / 3 : ℝ) : ℂ) • Matrix.vecMulVec
    (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0)
    (star (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0))

private def witnessVector : Fin 3 × Fin 3 → ℂ :=
  ((1 / Real.sqrt 3 : ℝ) : ℂ) •
    (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0)

private lemma omega_density : omega.PosSemidef ∧ omega.trace = 1 := by
  constructor
  · apply Matrix.PosSemidef.smul _ (Complex.zero_le_real.mpr (by norm_num))
    exact Matrix.posSemidef_vecMulVec_self_star _
  · have hpsi : star (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0) ⬝ᵥ
        (fun p : Fin 3 × Fin 3 => if p.1 = p.2 then 1 else 0) = (3 : ℂ) := by
      simp [dotProduct, Fintype.sum_prod_type]
    rw [omega, Matrix.trace_smul, Matrix.trace_vecMulVec]
    rw [dotProduct_comm, hpsi]
    norm_num

private lemma separableCone_partialTranspose_posSemidef {m n : ℕ}
    {rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hsep : separableCone rho) : (partialTranspose rho).PosSemidef := by
  rcases hsep with ⟨k, A, B, hAB, rfl⟩
  have hterm : ∀ i : Fin k, (partialTranspose (A i ⊗ₖ B i)).PosSemidef := by
    intro i
    have heq : partialTranspose (A i ⊗ₖ B i) = A i ⊗ₖ (B i).transpose := by
      ext ⟨a, b⟩ ⟨c, d⟩
      simp [partialTranspose, Matrix.kronecker_apply]
    rw [heq]
    exact (hAB i).1.kronecker (hAB i).2.transpose
  have hs := Matrix.posSemidef_sum (s := (Finset.univ : Finset (Fin k)))
    (x := fun i : Fin k => partialTranspose (A i ⊗ₖ B i)) (by
      intro i hi
      exact hterm i)
  have hlin : partialTranspose (∑ i, A i ⊗ₖ B i) =
      ∑ i, partialTranspose (A i ⊗ₖ B i) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [partialTranspose, Matrix.sum_apply]
  rw [hlin]
  exact hs

private lemma witness_partial_transpose_negative :
      RCLike.re (dotProduct (star witnessVector)
      (Matrix.mulVec (partialTranspose
        (MatrixMap.kron (LinearMap.id : MatrixMap (Fin 3) (Fin 3) ℂ) t omega))
        witnessVector)) = -1 / 9 := by sorry

private lemma t_not_entanglementBreaking : ¬ IsEntanglementBreaking t := by
  intro h
  have hs := h 3 omega omega_density.1 omega_density.2
  have hp := separableCone_partialTranspose_posSemidef hs
  have hn := hp.re_dotProduct_nonneg witnessVector
  rw [witness_partial_transpose_negative] at hn
  norm_num at hn

theorem result : ¬ claim := by
  intro h
  exact t_not_entanglementBreaking
    (h t t_cptp t_divisible t_not_pdivisible)

end
end D5.S3.QuantumChannels.QutritDivisibilityEntanglementBreakingRefutation
