/- GID: D5/S3/Quantum/Information/OrthogonalRecordEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/OrthogonalRecordEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Orthogonal record states have an explicit classical plus conditional entropy split. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Entropy.MaxEntropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexOrder CStarAlgebra MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Entropy.MaxEntropy

namespace D5.S3.Quantum.Information.OrthogonalRecordEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem cfc_negMulLog_add {A B : CStarMatrix n n ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A * B = 0) :
    cfc Real.negMulLog (A + B) = cfc Real.negMulLog A + cfc Real.negMulLog B := by
  have hD : IsSelfAdjoint (A - B) :=
    (IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB)
  obtain ⟨ha, hb⟩ := CFC.posPart_negPart_unique (a := A - B) rfl hAB hA hB
  have ha' : cfc (fun x : ℝ => x⁺) (A - B) = A := by
    simpa only [CFC.posPart_def, cfcₙ_eq_cfc] using ha
  have hb' : cfc (fun x : ℝ => x⁻) (A - B) = B := by
    simpa only [CFC.negPart_def, cfcₙ_eq_cfc] using hb
  rw [← ha', ← hb', ← cfc_add, ← cfc_comp', ← cfc_comp', ← cfc_comp', ← cfc_add]
  apply cfc_congr
  intro x _
  rcases le_total 0 x with hx | hx
  · simp [posPart_eq_self.mpr hx, negPart_eq_zero.mpr hx]
  · simp [posPart_eq_zero.mpr hx, negPart_eq_neg.mpr hx]

private theorem cfc_negMulLog_smul (p : ℝ) (A : CStarMatrix n n ℂ)
    (hA : IsSelfAdjoint A) :
    cfc Real.negMulLog (p • A) =
      Real.negMulLog p • A + p • cfc Real.negMulLog A := by
  rw [← cfc_comp_const_mul p Real.negMulLog A]
  have hf : (fun x : ℝ => Real.negMulLog (p * x)) =
      fun x => Real.negMulLog p * x + p * Real.negMulLog x := by
    funext x
    rw [Real.negMulLog_mul, mul_comm x]
  rw [hf, cfc_add, cfc_const_mul, cfc_const_mul, cfc_id]

private theorem entropy_eq_trace_cfc (rho : DensityState n) :
    vonNeumannEntropy rho = (Matrix.trace (cfc Real.negMulLog rho.1)).re := by
  have hA : IsSelfAdjoint rho.1 := IsSelfAdjoint.of_nonneg rho.2.1
  have hlog : ContinuousOn Real.log (spectrum ℝ rho.1) := by
    change ContinuousOn Real.log (spectrum ℝ (CStarMatrix.ofMatrix.symm rho.1))
    exact (CStarMatrix.ofMatrix.symm rho.1).finite_real_spectrum.continuousOn _
  have hf : Real.negMulLog = fun x : ℝ => -(x * Real.log x) := by
    funext x
    simp [Real.negMulLog]
  rw [hf, cfc_neg, cfc_mul, cfc_id]
  change -(Matrix.trace (rho.1 * CFC.log rho.1)).re =
    (Matrix.trace (-(rho.1 * CFC.log rho.1))).re
  rw [Matrix.trace_neg, Complex.neg_re]

/-- A finite mixture with its positivity and trace normalization proved from the inputs. -/
noncomputable def mixtureState {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (rho : ι → DensityState n) : DensityState n := by
  refine ⟨∑ i, p i • (rho i).1, Finset.sum_nonneg (fun i _ => ?_), ?_⟩
  · exact smul_nonneg (hp i) (rho i).2.1
  · change Matrix.trace (∑ i, p i • (CStarMatrix.ofMatrix.symm (rho i).1)) = 1
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, (rho _).2.2]
    change (∑ i, (p i : ℂ)) = 1
    exact_mod_cast hs

private theorem cfc_negMulLog_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → CStarMatrix n n ℂ) (hA : ∀ i ∈ s, 0 ≤ A i)
    (ho : s.Pairwise (fun i j => A i * A j = 0)) :
    cfc Real.negMulLog (∑ i ∈ s, A i) = ∑ i ∈ s, cfc Real.negMulLog (A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    rw [cfc_negMulLog_add (hA i (by simp))
      (Finset.sum_nonneg (fun j hj => hA j (by simp [hj]))) ?_]
    · rw [ih (fun j hj => hA j (by simp [hj]))
        (ho.mono (Finset.subset_insert i s))]
    · rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => ho (by simp) (by simp [hj])
        (by intro hij; subst j; exact hi hj)

/-- Conditional on orthogonal supports, the mixture entropy contains all classical label entropy.
The named `hOrthogonal` is the unadopted physical record hypothesis; no entropy law is assumed. -/
theorem orthogonal_mixture_entropy {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (rho : ι → DensityState n)
    (hOrthogonal : Pairwise (fun i j => (rho i).1 * (rho j).1 = 0)) :
    vonNeumannEntropy (mixtureState p hp hs rho) =
      shannonEntropy p + ∑ i, p i * vonNeumannEntropy (rho i) := by
  classical
  rw [entropy_eq_trace_cfc]
  change (Matrix.trace (cfc Real.negMulLog (∑ i, p i • (rho i).1))).re = _
  rw [cfc_negMulLog_sum Finset.univ _
    (fun i _ => smul_nonneg (hp i) (rho i).2.1) (fun i _ j _ hij => ?_)]
  · simp_rw [cfc_negMulLog_smul _ _ (IsSelfAdjoint.of_nonneg (rho _).2.1)]
    change (Matrix.trace (∑ i, Real.negMulLog (p i) • (rho i).1 +
      p i • cfc Real.negMulLog (rho i).1)).re = _
    rw [Matrix.trace_sum, Complex.re_sum]
    simp only [Matrix.trace_add, Matrix.trace_smul, (rho _).2.2]
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.one_re, mul_one]
    simp_rw [← entropy_eq_trace_cfc]
    exact Finset.sum_add_distrib
  · rw [smul_mul_assoc, mul_smul_comm, hOrthogonal hij, smul_zero, smul_zero]

#print axioms orthogonal_mixture_entropy

end D5.S3.Quantum.Information.OrthogonalRecordEntropy
