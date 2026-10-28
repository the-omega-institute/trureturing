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
  simpa only [amplitude, coefficient, star_mul, star_ofReal, ← Complex.ofReal_mul]
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
    TraceClass.norm_eq_traceNorm, TraceClass.ofOperator_coe,
    QuantumLogEnergy.traceNorm_eq_re_trace _ (compression_nonneg hpos i)]

end D5.S3.Quantum.Fibers.OriginalReferenceKraus
