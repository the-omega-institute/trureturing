/- GID: D5/S3/Quantum/Fibers/OriginalReferenceKraus
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalReferenceKraus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original jump outputs on arbitrary trace-class joint inputs. -/

import D5.S3.Quantum.Fibers.OriginalControlMarkedJump
import D5.S3.Quantum.Analysis.TraceClass.FiniteBlocks
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! The absorbing output retains the same reference in every original mode. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators Matrix
open TraceClassFiniteBlocks MeasureTheory Set

namespace D5.S3.Quantum.Fibers.OriginalReferenceKraus
open OriginalControlMarkedJump

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Amplification of the literal absorbing row by the unchanged reference. -/
def referenceJump (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) :
    Blocks (Fin 5) H →L[ℂ] H :=
  ∑ j : Fin 5, jumpKraus c a k S g i 0 j • coordinate j

def amplitude (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) : ℂ :=
  (Real.sqrt (g i) : ℂ) * (Real.sqrt S : ℂ) *
    (Real.sqrt (p c k i / p c a i) : ℂ)

def coefficient (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  g i * S * (p c k i / p c a i)

private theorem row_factor (c a k S : ℝ) (g : Fin 5 → ℝ) (i j : Fin 5) :
    jumpKraus c a k S g i 0 j = if j = i then amplitude c a k S g i else 0 := by
  simp [jumpKraus, absorbingRow, successfulKraus, Matrix.mul_apply,
    Matrix.diagonal, amplitude, mul_assoc]
  split_ifs with h
  · subst j
    rfl
  · rfl

private theorem referenceJump_factor (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) :
    referenceJump (H := H) c a k S g i = amplitude c a k S g i • coordinate i := by
  simp [referenceJump, row_factor, ite_smul]

private theorem amplitude_square (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c) (hk : k ∈ Ioo 0 c)
    (hS : 0 ≤ S) (hg : 0 ≤ g i) :
    amplitude c a k S g i * star (amplitude c a k S g i) =
      (coefficient c a k S g i : ℂ) := by
  have hs : (Real.sqrt (g i) * Real.sqrt S * Real.sqrt (p c k i / p c a i)) *
      (Real.sqrt (g i) * Real.sqrt S * Real.sqrt (p c k i / p c a i)) =
      g i * S * (p c k i / p c a i) := by
    calc
      _ = (Real.sqrt (g i) * Real.sqrt (g i)) *
          (Real.sqrt S * Real.sqrt S) *
          (Real.sqrt (p c k i / p c a i) * Real.sqrt (p c k i / p c a i)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hg, Real.mul_self_sqrt hS,
        Real.mul_self_sqrt (div_nonneg (p_pos c k hc hk i).le (p_pos c a hc ha i).le)]
  simpa only [amplitude, coefficient, star_mul, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    using congrArg Complex.ofReal hs

/-- The actual Kraus conjugation selects a diagonal block of the same joint input. -/
theorem actual_jump_operator (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c) (hk : k ∈ Ioo 0 c)
    (hS : 0 ≤ S) (hg : 0 ≤ g i) (rho : Blocks (Fin 5) H →L[ℂ] Blocks (Fin 5) H) :
    (referenceJump c a k S g i).comp (rho.comp (referenceJump c a k S g i).adjoint) =
      (coefficient c a k S g i : ℂ) • compression rho i := by
  rw [referenceJump_factor, map_smulₛₗ]
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, smul_smul, compression]
  change (star (amplitude c a k S g i) * amplitude c a k S g i) • _ = _
  rw [mul_comm, amplitude_square c a k S g i hc ha hk hS hg]
  rfl

/-- The genuine trace-class reference output, with its trace norm topology. -/
def failureOutput (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) : TraceClass H :=
  (coefficient c a k S g i : ℂ) • TraceClass.ofOperator (compression rho.1 i)
    (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)

/-- The trace norm of each retained mode density is its actual coefficient times
the mass of the corresponding reference block. -/
theorem actual_jump_trace_norm (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c) (hk : k ∈ Ioo 0 c)
    (hS : 0 ≤ S) (hg : 0 ≤ g i)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    (failureOutput c a k S g i rho hpos).1 =
      (referenceJump c a k S g i).comp (rho.1.comp (referenceJump c a k S g i).adjoint) ∧
    ‖failureOutput c a k S g i rho hpos‖ = coefficient c a k S g i *
      (trace (compression rho.1 i)
        (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)).re := by
  refine ⟨(actual_jump_operator c a k S g i hc ha hk hS hg rho.1).symm, ?_⟩
  have hn : 0 ≤ coefficient c a k S g i :=
    mul_nonneg (mul_nonneg hg hS)
      (div_nonneg (p_pos c k hc hk i).le (p_pos c a hc ha i).le)
  rw [failureOutput, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hn,
    TraceClass.norm_eq_traceNorm]
  change coefficient c a k S g i * traceNorm (compression rho.1 i) _ = _
  exact congrArg (fun r : ℝ => coefficient c a k S g i * r)
    (QuantumLogEnergy.traceNorm_eq_re_trace
      (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
      (compression_nonneg hpos i))

/-- The literal fixed absorbing successor, tensored with the reference. -/
def absorbingJump (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) :
    Blocks (Fin 5) H →L[ℂ] Blocks (Fin 6) H :=
  (insertion (5 : Fin 6)).comp (referenceJump c a k S g i)

def absorbingFailureOutput (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    TraceClass (Blocks (Fin 6) H) :=
  (coefficient c a k S g i : ℂ) • TraceClass.ofOperator
    (embedding (compression rho.1 i) (5 : Fin 6))
    (embedding_traceClass (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
      (compression_nonneg hpos i) (5 : Fin 6))

/-- Retaining the absorbing coordinate gives the actual six-coordinate output,
with the full reference and the unchanged positive trace norm. -/
theorem absorbing_jump_trace_norm (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c) (hk : k ∈ Ioo 0 c)
    (hS : 0 ≤ S) (hg : 0 ≤ g i)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1) :
    (absorbingFailureOutput c a k S g i rho hpos).1 =
      (absorbingJump c a k S g i).comp (rho.1.comp (absorbingJump c a k S g i).adjoint) ∧
    ‖absorbingFailureOutput c a k S g i rho hpos‖ = ‖failureOutput c a k S g i rho hpos‖ := by
  constructor
  · change (coefficient c a k S g i : ℂ) • embedding (compression rho.1 i) (5 : Fin 6) = _
    have he := congrArg (fun A : H →L[ℂ] H =>
        (insertion (5 : Fin 6)).comp (A.comp (coordinate (5 : Fin 6))))
      (actual_jump_operator c a k S g i hc ha hk hS hg rho.1)
    simpa only [absorbingJump, ContinuousLinearMap.adjoint_comp,
      insertion, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc,
      embedding, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul] using he.symm
  · simp only [absorbingFailureOutput, failureOutput, norm_smul, TraceClass.norm_eq_traceNorm]
    congr 1
    change traceNorm (embedding (compression rho.1 i) (5 : Fin 6)) _ =
      traceNorm (compression rho.1 i) _
    exact (embedding_trace_norm (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)
      (compression_nonneg hpos i) (5 : Fin 6)).2

/-- The actual block masses in all five mode outputs form the total joint mass. -/
theorem actual_output_mass_partition (rho : TraceClass (Blocks (Fin 5) H))
    (hpos : 0 ≤ rho.1) :
    (∑ i : Fin 5, ‖TraceClass.ofOperator (compression rho.1 i)
      (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)‖) = ‖rho‖ := by
  have hn (i : Fin 5) : ‖TraceClass.ofOperator (compression rho.1 i)
      (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)‖ =
      (trace (compression rho.1 i)
        (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)).re := by
    rw [TraceClass.norm_eq_traceNorm]
    change traceNorm (compression rho.1 i) _ = _
    exact QuantumLogEnergy.traceNorm_eq_re_trace _ (compression_nonneg hpos i)
  simp_rw [hn]
  have ht := congrArg (Complex.reCLM : ℂ → ℝ)
    (trace_compression_sum (TraceClass.isTraceClass_coe rho) hpos)
  have hsum : (∑ i : Fin 5, (trace (compression rho.1 i)
      (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)).re) =
        (trace rho.1 (TraceClass.isTraceClass_coe rho)).re := by
    simpa only [map_sum, Complex.reCLM_apply] using ht
  rw [hsum]
  exact (QuantumLogEnergy.traceNorm_eq_re_trace (TraceClass.isTraceClass_coe rho) hpos).symm

end D5.S3.Quantum.Fibers.OriginalReferenceKraus
