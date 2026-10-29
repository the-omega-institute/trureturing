/- GID: D5/S3/Quantum/Foundation/FinitePreparationChannel
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FinitePreparationChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite family of actual density matrices has a canonical CPTP preparation map. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Foundation.FinitePreparationChannel
open _root_.Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel

/-- Measuring an input in the computational basis and preparing the selected density state
is a CPTP map on the entire complex matrix algebra, including singular output states. -/
theorem finite_preparation_quantum_channel
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho : a → DensityState b) :
    ∃ channel : QuantumChannel a b, ∀ X : Matrix a a ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      ∑ i, X i i • CStarMatrix.ofMatrix.symm (rho i).1 := by
  classical
  let V (i : a) : Matrix b b ℂ := CStarMatrix.ofMatrix.symm (CFC.sqrt (rho i).1)
  have hH (i : a) : (V i).conjTranspose = V i := by
    exact (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (CFC.sqrt_nonneg (rho i).1))).isHermitian.eq
  have hV (i : a) : V i * V i = CStarMatrix.ofMatrix.symm (rho i).1 := by
    exact congrArg CStarMatrix.ofMatrix.symm (CFC.sqrt_mul_sqrt_self (rho i).1 (rho i).2.1)
  have hnorm (i : a) : ∑ j, ∑ r, star (V i r j) * V i r j = 1 := by
    change (Matrix.trace ((V i).conjTranspose * V i)) = 1
    rw [hH, hV]
    exact (rho i).2.2
  let K (p : a × b) : Matrix b a ℂ := fun r u => if u = p.1 then V p.1 r p.2 else 0
  have hgram : (∑ p, (K p).conjTranspose * K p) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [K, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.one_apply] using hnorm i
    · simp [K, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.one_apply, hij]
  obtain ⟨channel, hchannel⟩ := finite_kraus_quantum_channel K hgram
  refine ⟨channel, ?_⟩
  intro X
  rw [hchannel]
  ext r s
  have he (i : a) : ∑ j, V i r j * star (V i s j) =
      CStarMatrix.ofMatrix.symm (rho i).1 r s := by
    change (V i * (V i).conjTranspose) r s = _
    rw [hH, hV]
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K]
  simp only [star_ite, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, ← he]
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms finite_preparation_quantum_channel
end D5.S3.Quantum.Foundation.FinitePreparationChannel
