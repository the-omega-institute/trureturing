/- GID: D5/S3/Quantum/Measurement/ActualModeProtocol
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ActualModeProtocol
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite wait/read/stop trees and their unnormalized branch history laws. -/

import D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw
import D5.S3.TotalVariation.Metric
import Mathlib.Data.Matrix.Basis
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder MatrixOrder NNReal ENNReal

namespace D5.S3.Quantum.Measurement.ActualModeProtocol

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw (actualWait)
open D5.S3.TotalVariation.Pinsker (totalVariation)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The mode labels, in the order N, 2, 3, 5, 25. -/
abbrev Mode := Fin 5

/-- The actual five-mode generator. The label N is the first basis vector. -/
def generator : Matrix Mode Mode ℂ :=
  !![0, 1, 1, 1, 0; 1, 0, 0, 0, 1; 1, 0, 0, 0, 0;
     1, 0, 0, 0, 1; 0, 1, 0, 1, 0]

/-- A full coordinate read has one rank-one projector for every mode. -/
def projector (s : ι) : Matrix ι ι ℂ := Matrix.single s s 1

/-- The unnormalized Lüders branch, with no hidden outcome made visible. -/
def readBranch (s : ι) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  projector s * X * projector s

/-- Waiting uses the repository's actual matrix exponential. -/
def waitState (K : Matrix ι ι ℂ) (t : ℝ≥0) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  actualWait K t * X * (actualWait K t)ᴴ

/-- Every tree has a finite action bound. Branch selection sees only read outcomes;
the tree and all waiting times are fixed independently of the input state. -/
inductive Protocol (ι : Type) : ℕ → Type
  | stop {n} : Protocol ι n
  | wait {n} (time : ℝ≥0) (next : Protocol ι n) : Protocol ι (n + 1)
  | read {n} (next : ι → Protocol ι n) : Protocol ι (n + 1)

/-- Leaves retain the complete sequence of read results. At fixed tree, their
waits and stopping decisions are also determined; no read result is merged. -/
def Protocol.History : {n : ℕ} → Protocol ι n → Type
  | _, .stop => Unit
  | _, .wait _ next => next.History
  | _, .read next => (s : ι) × (next s).History

instance Protocol.historyFintype : {n : ℕ} → (π : Protocol ι n) → Fintype π.History
  | _, .stop => inferInstanceAs (Fintype Unit)
  | _, .wait _ next => next.historyFintype
  | _, .read next => by
      letI := fun s => (next s).historyFintype
      exact inferInstanceAs (Fintype ((s : ι) × (next s).History))

/-- Schrödinger evaluation on substates: no division by an outcome probability. -/
def historyWeight (K : Matrix ι ι ℂ) : {n : ℕ} → (π : Protocol ι n) →
    Matrix ι ι ℂ → π.History → ℝ
  | _, .stop, X, _ => (Matrix.trace X).re
  | _, .wait t next, X, h => historyWeight K next (waitState K t X) h
  | _, .read next, X, h => historyWeight K (next h.1) (readBranch h.1 X) h.2

/-- A history record contains every selected wait, every mode result, and Stop. -/
def Protocol.record : {n : ℕ} → (π : Protocol ι n) → π.History → List (ℝ≥0 ⊕ Option ι)
  | _, .stop, _ => [Sum.inr none]
  | _, .wait t next, h => Sum.inl t :: next.record h
  | _, .read next, h => Sum.inr (some h.1) :: (next h.1).record h.2

private theorem projector_adjoint (s : ι) : (projector s)ᴴ = projector s := by
  simp [projector]

private theorem projector_positive (s : ι) : (projector s).PosSemidef := by
  have h : projector s * (projector s)ᴴ = projector s := by
    simp [projector]
  rw [← h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

private theorem readBranch_positive (s : ι) {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) : (readBranch s X).PosSemidef := by
  simpa only [readBranch, projector_adjoint] using
    hX.mul_mul_conjTranspose_same (projector s)

private theorem wait_unitary (K : Matrix ι ι ℂ) (hK : K.IsHermitian) (t : ℝ≥0) :
    actualWait K t ∈ unitary (Matrix ι ι ℂ) := by
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.instL2OpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.instL2OpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix ι ι ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  change NormedSpace.exp ((-Complex.I * (t : ℂ)) • K) ∈ unitary (Matrix ι ι ℂ)
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff, star_smul]
  have hkstar : star K = K := hK.eq
  rw [hkstar]
  have hc : star (-Complex.I * (t : ℂ)) = -(-Complex.I * (t : ℂ)) := by simp
  rw [hc, neg_smul]

theorem waitState_trace (K : Matrix ι ι ℂ) (hK : K.IsHermitian)
    (t : ℝ≥0) (X : Matrix ι ι ℂ) : Matrix.trace (waitState K t X) = Matrix.trace X := by
  have hu := (wait_unitary K hK t).1
  change (actualWait K t)ᴴ * actualWait K t = 1 at hu
  rw [waitState, Matrix.trace_mul_cycle, hu, Matrix.one_mul]

private theorem readBranch_collapse (s : ι) (X : Matrix ι ι ℂ) :
    readBranch s X = X s s • projector s := by
  simp [readBranch, projector, Matrix.smul_single]

private theorem read_trace (s : ι) (X : Matrix ι ι ℂ) :
    Matrix.trace (readBranch s X) = X s s := by
  simp [readBranch, projector]

private theorem historyWeight_smul (K : Matrix ι ι ℂ) {n : ℕ}
    (π : Protocol ι n) (r : ℝ) (X : Matrix ι ι ℂ) (h : π.History) :
    historyWeight K π ((r : ℂ) • X) h = r * historyWeight K π X h := by
  induction π generalizing X with
  | stop => simp [historyWeight, Matrix.trace_smul]
  | wait t next ih =>
      simpa [historyWeight, waitState, Matrix.mul_smul, Matrix.smul_mul] using ih (waitState K t X) h
  | read next ih =>
      simpa [historyWeight, readBranch, Matrix.mul_smul, Matrix.smul_mul] using ih h.1 (readBranch h.1 X) h.2

/-- Every actual history has nonnegative weight for a positive input substate. -/
theorem historyWeight_nonnegative (K : Matrix ι ι ℂ) {n : ℕ}
    (π : Protocol ι n) (X : Matrix ι ι ℂ) (hX : X.PosSemidef) (h : π.History) :
    0 ≤ historyWeight K π X h := by
  induction π generalizing X with
  | stop => exact (Complex.nonneg_iff.mp hX.trace_nonneg).1
  | wait t next ih => exact ih (waitState K t X) (hX.mul_mul_conjTranspose_same _) h
  | read next ih => exact ih h.1 (readBranch h.1 X) (readBranch_positive _ hX) h.2

/-- Summing all terminal histories preserves the input mass, including Stop. -/
theorem historyWeight_mass (K : Matrix ι ι ℂ) (hK : K.IsHermitian) {n : ℕ}
    (π : Protocol ι n) (X : Matrix ι ι ℂ) :
    ∑ h, historyWeight K π X h = (Matrix.trace X).re := by
  induction π generalizing X with
  | stop =>
      change (∑ _ : Unit, (Matrix.trace X).re) = _
      simp
  | wait t next ih =>
      change (∑ h, historyWeight K next (waitState K t X) h) = _
      rw [ih, waitState_trace K hK]
  | read next ih =>
      change (∑ h : (s : ι) × (next s).History,
        historyWeight K (next h.1) (readBranch h.1 X) h.2) = _
      rw [Fintype.sum_sigma]
      simp_rw [ih, read_trace]
      simp [Matrix.trace]

/-- The actual history probability distribution for a canonical density state. -/
def historyLaw (K : Matrix ι ι ℂ) (hK : K.IsHermitian) {n : ℕ}
    (π : Protocol ι n) (ρ : DensityState ι) : PMF π.History :=
  PMF.ofFintype (fun h => ENNReal.ofReal
    (historyWeight K π (CStarMatrix.ofMatrix.symm ρ.1) h)) (by
      have hρ : (CStarMatrix.ofMatrix.symm ρ.1).PosSemidef :=
        Matrix.nonneg_iff_posSemidef.mp
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun h _ => historyWeight_nonnegative K π _ hρ h), historyWeight_mass K hK]
      change ENNReal.ofReal (Matrix.trace ρ.1).re = 1
      simp [ρ.2.2])

/-- The same law on a common record space, retaining controls and Stop. -/
def recordLaw (K : Matrix ι ι ℂ) (hK : K.IsHermitian) {n : ℕ}
    (π : Protocol ι n) (ρ : DensityState ι) : PMF (List (ℝ≥0 ⊕ Option ι)) :=
  (historyLaw K hK π ρ).map π.record

/-- Input-independent suffix laws, defined also on zero-probability first branches. -/
def suffixWeight (K : Matrix ι ι ℂ) {n : ℕ} (next : ι → Protocol ι n)
    (s : ι) : (next s).History → ℝ := historyWeight K (next s) (projector s)

/-- Actual Lüders history evaluation factors through one normalized suffix law
per first outcome, shared simultaneously by all positive input matrices. -/
theorem first_read_factorization (K : Matrix ι ι ℂ) (hK : K.IsHermitian) {n : ℕ}
    (next : ι → Protocol ι n) :
    (∀ s h, 0 ≤ suffixWeight K next s h) ∧
    (∀ s, ∑ h, suffixWeight K next s h = 1) ∧
    (∀ (X : Matrix ι ι ℂ), X.PosSemidef → ∀ h : (Protocol.read next).History,
      historyWeight K (.read next) X h = (X h.1 h.1).re * suffixWeight K next h.1 h.2) := by
  refine ⟨fun s h => historyWeight_nonnegative K _ _ (projector_positive s) h, ?_, ?_⟩
  · intro s
    simpa [suffixWeight, projector] using historyWeight_mass K hK (next s) (projector s)
  · intro X hX h
    change historyWeight K (next h.1) (readBranch h.1 X) h.2 = _
    rw [readBranch_collapse]
    have hr : X h.1 h.1 = ((X h.1 h.1).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using (Complex.nonneg_iff.mp (hX.diag_nonneg (i := h.1))).2.symm
    rw [hr, historyWeight_smul]
    simp only [Complex.ofReal_re, suffixWeight]

#print axioms first_read_factorization

end D5.S3.Quantum.Measurement.ActualModeProtocol
