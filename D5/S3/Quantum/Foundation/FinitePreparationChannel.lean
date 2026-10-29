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
open scoped MatrixOrder ComplexOrder CStarAlgebra
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
  have hrho (i : a) : 0 ≤ CStarMatrix.ofMatrix.symm (rho i).1 :=
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (rho i).2.1
  let V (i : a) : Matrix b b ℂ := CFC.sqrt (CStarMatrix.ofMatrix.symm (rho i).1)
  have hH (i : a) : (V i).conjTranspose = V i :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.eq
  have hV (i : a) : V i * V i = CStarMatrix.ofMatrix.symm (rho i).1 :=
    CFC.sqrt_mul_sqrt_self _ (hrho i)
  have hnorm (i : a) : ∑ j, ∑ r, star (V i r j) * V i r j = 1 := by
    change (Matrix.trace ((V i).conjTranspose * V i)) = 1
    rw [hH i, hV i]
    exact (rho i).2.2
  let K (p : a × b) : Matrix b a ℂ := fun r u => if u = p.1 then V p.1 r p.2 else 0
  have hgram : (∑ p, (K p).conjTranspose * K p) = 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simpa [K, Fintype.sum_prod_type, ite_mul, mul_ite, apply_ite] using hnorm i
    · simp [K, Fintype.sum_prod_type, ite_mul, mul_ite, apply_ite, hij]
  obtain ⟨channel, hchannel⟩ := finite_kraus_quantum_channel K hgram
  refine ⟨channel, ?_⟩
  intro X
  rw [hchannel]
  ext r s
  have he (i : a) : ∑ j, V i r j * star (V i s j) =
      CStarMatrix.ofMatrix.symm (rho i).1 r s := by
    change (V i * (V i).conjTranspose) r s = _
    rw [hH i, hV i]
  have haction (p : a × b) : (K p * X * (K p).conjTranspose) r s =
      X p.1 p.1 * (V p.1 r p.2 * star (V p.1 s p.2)) := by
    change (∑ u : a, (∑ v : a, K p r v * X v u) * star (K p s u)) = _
    simp [K, ite_mul, mul_ite, apply_ite]
    <;> ring
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul]
  simp_rw [haction]
  simp_rw [← Finset.mul_sum, he]

#print axioms finite_preparation_quantum_channel
end D5.S3.Quantum.Foundation.FinitePreparationChannel
