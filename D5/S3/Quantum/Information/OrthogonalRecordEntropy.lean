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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ComplexOrder CStarAlgebra MatrixOrder Kronecker
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Entropy.MaxEntropy
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Information.OrthogonalRecordEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

private theorem cfc_negMulLog_add {A B : CStarMatrix n n ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A * B = 0) :
    cfc Real.negMulLog (A + B) = cfc Real.negMulLog A + cfc Real.negMulLog B := by
  have hD : IsSelfAdjoint (A - B) :=
    (IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB)
  obtain ⟨ha, hb⟩ := CFC.posPart_negPart_unique (a := A - B) rfl hAB hA hB
  have ha' : cfc (fun x : ℝ => x⁺) (A - B) = A := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc (by fun_prop) (by simp)] at ha
    exact ha
  have hb' : cfc (fun x : ℝ => x⁻) (A - B) = B := by
    rw [CFC.negPart_def, cfcₙ_eq_cfc (by fun_prop) (by simp)] at hb
    exact hb
  have hsum : cfc (fun x : ℝ => x⁺ + x⁻) (A - B) = A + B := by
    rw [cfc_add (A - B) (fun x : ℝ => x⁺) (fun x : ℝ => x⁻), ha', hb']
  calc
    _ = cfc (fun x : ℝ => Real.negMulLog (x⁺ + x⁻)) (A - B) := by
      rw [cfc_comp' Real.negMulLog (fun x : ℝ => x⁺ + x⁻) (A - B), hsum]
    _ = cfc (fun x : ℝ => Real.negMulLog x⁺ + Real.negMulLog x⁻) (A - B) := by
      apply cfc_congr
      intro x _
      rcases le_total 0 x with hx | hx
      · simp [posPart_eq_self.mpr hx, negPart_eq_zero.mpr hx]
      · simp [posPart_eq_zero.mpr hx, negPart_eq_neg.mpr hx]
    _ = _ := by
      rw [cfc_add (A - B) (fun x : ℝ => Real.negMulLog x⁺)
        (fun x : ℝ => Real.negMulLog x⁻),
        cfc_comp' Real.negMulLog (fun x : ℝ => x⁺) (A - B),
        cfc_comp' Real.negMulLog (fun x : ℝ => x⁻) (A - B), ha', hb']

private theorem cfc_negMulLog_smul (p : ℝ) (A : CStarMatrix n n ℂ)
    (hA : IsSelfAdjoint A) :
    cfc Real.negMulLog (p • A) =
      Real.negMulLog p • A + p • cfc Real.negMulLog A := by
  rw [← cfc_comp_const_mul p Real.negMulLog A]
  have hf : (fun x : ℝ => Real.negMulLog (p * x)) =
      fun x => Real.negMulLog p * x + p * Real.negMulLog x := by
    funext x
    rw [Real.negMulLog_mul, mul_comm x]
  rw [hf, cfc_add A (fun x : ℝ => Real.negMulLog p * x)
    (fun x : ℝ => p * Real.negMulLog x), cfc_const_mul (Real.negMulLog p) (fun x : ℝ => x) A,
    cfc_const_mul p Real.negMulLog A, cfc_id' ℝ A]

private noncomputable def realTrace (A : CStarMatrix n n ℂ) : ℝ :=
  (Matrix.trace (CStarMatrix.ofMatrix.symm A)).re

omit [DecidableEq n] in
private theorem realTrace_add (A B : CStarMatrix n n ℂ) :
    realTrace (A + B) = realTrace A + realTrace B := by
  unfold realTrace
  change (Matrix.trace (CStarMatrix.ofMatrix.symm A + CStarMatrix.ofMatrix.symm B)).re = _
  rw [Matrix.trace_add, Complex.add_re]

omit [DecidableEq n] in
private theorem realTrace_smul (p : ℝ) (A : CStarMatrix n n ℂ) :
    realTrace (p • A) = p * realTrace A := by
  unfold realTrace
  change (Matrix.trace (p • CStarMatrix.ofMatrix.symm A)).re = _
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

omit [DecidableEq n] in
private theorem realTrace_sum {ι : Type*} (s : Finset ι) (A : ι → CStarMatrix n n ℂ) :
    realTrace (∑ i ∈ s, A i) = ∑ i ∈ s, realTrace (A i) := by
  unfold realTrace
  change (Matrix.trace (∑ i ∈ s, CStarMatrix.ofMatrix.symm (A i))).re = _
  rw [Matrix.trace_sum, Complex.re_sum]

private theorem entropy_eq_trace_cfc (rho : DensityState n) :
    vonNeumannEntropy rho = realTrace (cfc Real.negMulLog rho.1) := by
  have hA : IsSelfAdjoint rho.1 := IsSelfAdjoint.of_nonneg rho.2.1
  have hlog : ContinuousOn Real.log (spectrum ℝ rho.1) := by
    change ContinuousOn Real.log (spectrum ℝ (CStarMatrix.ofMatrix.symm rho.1))
    exact (CStarMatrix.ofMatrix.symm rho.1).finite_real_spectrum.continuousOn _
  have hf : Real.negMulLog = fun x : ℝ => -(x * Real.log x) := by
    funext x
    simp [Real.negMulLog]
  rw [hf, cfc_neg (fun x : ℝ => x * Real.log x) rho.1,
    cfc_mul (fun x : ℝ => x) Real.log rho.1 continuousOn_id hlog, cfc_id' ℝ rho.1]
  change -(Matrix.trace (rho.1 * CFC.log rho.1)).re =
    (Matrix.trace (-(rho.1 * CFC.log rho.1))).re
  rw [Matrix.trace_neg, Complex.neg_re]

/-- A finite mixture with its positivity and trace normalization proved from the inputs. -/
noncomputable def mixtureState {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (rho : ι → DensityState n) : DensityState n := by
  refine ⟨∑ i, p i • (rho i).1, Finset.sum_nonneg (fun i _ => ?_), ?_⟩
  · exact smul_nonneg (hp i) (rho i).2.1
  · have ht (i : ι) : Matrix.trace (CStarMatrix.ofMatrix.symm (rho i).1) = 1 :=
      (rho i).2.2
    change Matrix.trace (∑ i, p i • (CStarMatrix.ofMatrix.symm (rho i).1)) = 1
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, ht, Complex.real_smul, mul_one]
    change (∑ i, (p i : ℂ)) = 1
    exact_mod_cast hs

private theorem cfc_negMulLog_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → CStarMatrix n n ℂ) (hA : ∀ i ∈ s, 0 ≤ A i)
    (ho : (s : Set ι).Pairwise (fun i j => A i * A j = 0)) :
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
  change realTrace (cfc Real.negMulLog (∑ i, p i • (rho i).1)) = _
  have ho : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (fun i j => (p i • (rho i).1) * (p j • (rho j).1) = 0) := by
    intro i _ j _ hij
    rw [smul_mul_assoc, mul_smul_comm, hOrthogonal hij, smul_zero, smul_zero]
  rw [cfc_negMulLog_sum Finset.univ _
    (fun i _ => smul_nonneg (hp i) (rho i).2.1) ho, realTrace_sum]
  have ht (i : ι) : realTrace (rho i).1 = 1 := by
    exact congrArg Complex.re (rho i).2.2
  simp_rw [cfc_negMulLog_smul _ _ (IsSelfAdjoint.of_nonneg (rho _).2.1),
    realTrace_add, realTrace_smul, ht, mul_one, ← entropy_eq_trace_cfc]
  exact Finset.sum_add_distrib

#print axioms orthogonal_mixture_entropy

private noncomputable def pointerState (i : n) : DensityState n := by
  refine ⟨CStarMatrix.ofMatrix (Matrix.diagonal (fun j => if j = i then 1 else 0)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    rw [Matrix.posSemidef_diagonal_iff]
    intro j
    split_ifs <;> simp
  · change Matrix.trace (Matrix.diagonal (fun j : n => if j = i then (1 : ℂ) else 0)) = 1
    simp

private theorem pointerState_idempotent (i : n) : IsIdempotentElem (pointerState i).1 := by
  change Matrix.diagonal (fun j : n => if j = i then (1 : ℂ) else 0) *
    Matrix.diagonal (fun j : n => if j = i then (1 : ℂ) else 0) = _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs <;> simp

private theorem pointerState_orthogonal :
    Pairwise (fun i j : n => (pointerState i).1 * (pointerState j).1 = 0) := by
  intro i j hij
  change Matrix.diagonal (fun a : n => if a = i then (1 : ℂ) else 0) *
    Matrix.diagonal (fun a : n => if a = j then (1 : ℂ) else 0) = 0
  rw [Matrix.diagonal_mul_diagonal]
  have hf : (fun a : n => (if a = i then (1 : ℂ) else 0) *
      (if a = j then 1 else 0)) = 0 := by
    funext a
    by_cases ha : a = i
    · subst a
      simp [hij]
    · simp [ha]
  rw [hf]
  ext a b
  simp [Matrix.diagonal_apply]

private theorem entropy_pointerState (i : n) : vonNeumannEntropy (pointerState i) = 0 := by
  rw [entropy_eq_trace_cfc]
  have hz : cfc Real.negMulLog (pointerState i).1 = 0 := by
    calc
      _ = cfc (fun _ : ℝ => 0) (pointerState i).1 := by
        apply cfc_congr
        intro x hx
        have h := (isIdempotentElem_iff_spectrum_subset ℝ (pointerState i).1
          (IsSelfAdjoint.of_nonneg (pointerState i).2.1)).mp
            (pointerState_idempotent i) hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
        rcases h with rfl | rfl <;> simp
      _ = 0 := by simp
  rw [hz]
  change (Matrix.trace (0 : Matrix n n ℂ)).re = 0
  simp

/-- The classical-quantum record state is the mixture of pointer basis states and fragment states.
Its definition requires only a probability distribution; orthogonality is a theorem hypothesis. -/
noncomputable def recordState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (rho : ι → DensityState n) : DensityState (ι × n) :=
  mixtureState p hp hs (fun i => productState (pointerState i) (rho i))

private theorem marginalLeft_mixture {ι A B : Type*} [Fintype ι]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (rho : ι → DensityState (A × B)) :
    marginalLeft (mixtureState p hp hs rho) =
      mixtureState p hp hs (fun i => marginalLeft (rho i)) := by
  apply Subtype.ext
  change CStarMatrix.ofMatrix (partialTraceLeft
    (∑ i, p i • CStarMatrix.ofMatrix.symm (rho i).1)) =
      CStarMatrix.ofMatrix (∑ i, p i • partialTraceLeft (CStarMatrix.ofMatrix.symm (rho i).1))
  congr 1
  ext b d
  simp only [partialTraceLeft, Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.smul_sum.symm

private theorem marginalRight_mixture {ι A B : Type*} [Fintype ι]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (rho : ι → DensityState (A × B)) :
    marginalRight (mixtureState p hp hs rho) =
      mixtureState p hp hs (fun i => marginalRight (rho i)) := by
  apply Subtype.ext
  change CStarMatrix.ofMatrix (partialTraceRight
    (∑ i, p i • CStarMatrix.ofMatrix.symm (rho i).1)) =
      CStarMatrix.ofMatrix (∑ i, p i • partialTraceRight (CStarMatrix.ofMatrix.symm (rho i).1))
  congr 1
  ext a c
  simp only [partialTraceRight, Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.smul_sum.symm

/-- Reading either factor uses its actual partial trace. Under the explicitly named orthogonal
record assumption, the fragment carries the entire classical entropy of the pointer. -/
theorem orthogonal_record_trace_gives_sbs_consensus
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (rho : ι → DensityState n)
    (hOrthogonal : Pairwise (fun i j => (rho i).1 * (rho j).1 = 0)) :
    quantumMutualInformation (recordState p hp hs rho) = shannonEntropy p := by
  have hprod : Pairwise (fun i j =>
      (productState (pointerState i) (rho i)).1 *
        (productState (pointerState j) (rho j)).1 = 0) := by
    intro i j hij
    change (CStarMatrix.ofMatrix.symm (pointerState i).1 ⊗ₖ
      CStarMatrix.ofMatrix.symm (rho i).1) *
        (CStarMatrix.ofMatrix.symm (pointerState j).1 ⊗ₖ
          CStarMatrix.ofMatrix.symm (rho j).1) = 0
    rw [← Matrix.mul_kronecker_mul]
    have hptr : (CStarMatrix.ofMatrix.symm (pointerState i).1) *
        (CStarMatrix.ofMatrix.symm (pointerState j).1) = 0 := pointerState_orthogonal hij
    rw [hptr, Matrix.zero_kronecker]
  have hsys : vonNeumannEntropy (mixtureState p hp hs pointerState) = shannonEntropy p := by
    rw [orthogonal_mixture_entropy p hp hs pointerState pointerState_orthogonal]
    simp only [entropy_pointerState, mul_zero, Finset.sum_const_zero, add_zero]
  have hjoint : vonNeumannEntropy (recordState p hp hs rho) =
      shannonEntropy p + ∑ i, p i * vonNeumannEntropy (rho i) := by
    unfold recordState
    rw [orthogonal_mixture_entropy p hp hs _ hprod]
    simp only [vonNeumannEntropy_productState, entropy_pointerState, zero_add]
  unfold quantumMutualInformation
  rw [hjoint]
  unfold recordState
  rw [marginalRight_mixture, marginalLeft_mixture]
  simp only [marginalRight_productState, marginalLeft_productState]
  rw [hsys, orthogonal_mixture_entropy p hp hs rho hOrthogonal]
  ring

#print axioms orthogonal_record_trace_gives_sbs_consensus

end D5.S3.Quantum.Information.OrthogonalRecordEntropy
