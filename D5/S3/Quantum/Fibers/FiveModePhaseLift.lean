/- GID: D5/S3/Quantum/Fibers/FiveModePhaseLift
   generality: I
   mirror-B: D5/B/S3/Quantum/Fibers/FiveModePhaseLift
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Fibers/FiveModePhaseLift.claim; result=D5/S3/Quantum/Fibers/FiveModePhaseLift.result; claim=D5/S3/Quantum/Fibers/FiveModePhaseLift.claim
   digest: A two-coordinate phase mixture has constant actual responses and branch mass but an injective projective Born readout. -/

import D5.S3.Quantum.Fibers.FiveModeRealResponse
import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum.CoherenceBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Fibers.FiveModePhaseLift

open D5.S3.Quantum.Fibers.FiveModeRealResponse
open D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum.ReadoutInstrument
open D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum.CoherenceBoundary

/-- The rays `e₂ + sign i e₄` in the explicit five-coordinate basis. -/
def phaseRay (sign : ℝ) : Fin 5 → ℂ :=
  fun k => if k = 2 then 1 else if k = 4 then (sign : ℂ) * Complex.I else 0

/-- At signs plus and minus one these are normalized orthogonal pure states. -/
def phaseState (sign : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  (2 : ℂ)⁻¹ • Matrix.vecMulVec (phaseRay sign) (star (phaseRay sign))

/-- A convex mixture of the two opposite phase states. -/
def mixture (q : Set.Icc (0 : ℝ) 1) : Matrix (Fin 5) (Fin 5) ℂ :=
  ((q : ℝ) : ℂ) • phaseState 1 + (1 - ((q : ℝ) : ℂ)) • phaseState (-1)

/-- Born readout of the plus-phase rank-one projector. -/
def phaseProbability (rho : Matrix (Fin 5) (Fin 5) ℂ) : ℝ :=
  (Matrix.trace (rho * phaseState 1)).re

/-- The concrete odd-rejection branch, with its original Kraus family. -/
def branchMass (rho : Matrix (Fin 5) (Fin 5) ℂ) : ℂ :=
  Matrix.trace (MatrixMap.of_kraus (K () (7 : Fin 8)) (K () (7 : Fin 8)) rho)

private theorem phase_positive (s : ℝ) : (phaseState s).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star (phaseRay s)).smul
    (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)

private theorem pure_pair :
    Matrix.trace (phaseState 1) = 1 ∧ Matrix.trace (phaseState (-1)) = 1 ∧
    phaseState 1 * phaseState 1 = phaseState 1 ∧
    phaseState (-1) * phaseState (-1) = phaseState (-1) ∧
    phaseState 1 * phaseState (-1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [phaseState, phaseRay, Matrix.trace, Matrix.vecMulVec, Fin.sum_univ_succ]
  · norm_num [phaseState, phaseRay, Matrix.trace, Matrix.vecMulVec, Fin.sum_univ_succ]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [phaseState, phaseRay, Matrix.mul_apply, Matrix.vecMulVec,
        Fin.sum_univ_succ] <;> ring_nf <;> norm_num [Complex.I_mul_I]

private theorem mixture_positive (q : Set.Icc (0 : ℝ) 1) : (mixture q).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact (phase_positive 1).smul (Complex.nonneg_iff.mpr ⟨q.2.1, by simp⟩)
  · exact (phase_positive (-1)).smul
      (Complex.nonneg_iff.mpr ⟨by simpa using sub_nonneg.mpr q.2.2, by simp⟩)

private theorem mixture_real (q r : Set.Icc (0 : ℝ) 1) :
    realEntries (mixture q) = realEntries (mixture r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realEntries, mixture, phaseState, phaseRay, Matrix.vecMulVec] <;> ring

/-- Sufficiency of all old finite-menu responses together with the branch-7
trace for predicting the added plus-phase Born measurement on every density state. -/
def claim : Prop :=
  ∀ rho sigma : Matrix (Fin 5) (Fin 5) ℂ,
    rho.PosSemidef → Matrix.trace rho = 1 →
    sigma.PosSemidef → Matrix.trace sigma = 1 →
    (∀ (P : Protocol (Fin 5)) (h : Record P),
      ludersLaw menu P rho h = ludersLaw menu P sigma h) →
    branchMass rho = branchMass sigma → phaseProbability rho = phaseProbability sigma

/-- Neither the complete old responses nor their augmentation by the diagonal
odd-rejection branch determines the non-diagonal phase measurement. -/
theorem result : ¬ claim := by
  intro h
  let q : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let r : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have ht (x : Set.Icc (0 : ℝ) 1) : Matrix.trace (mixture x) = 1 := by
    simp [mixture, Matrix.trace_add, Matrix.trace_smul, pure_pair.1, pure_pair.2.1]
  have hb (x : Set.Icc (0 : ℝ) 1) : branchMass (mixture x) = (1 : ℂ) / 2 := by
    rw [branchMass, arbitrary_branch_trace_reads_diagonal]
    norm_num [mixture, phaseState, phaseRay, Matrix.vecMulVec]
    ring
  have he := h (mixture q) (mixture r) (mixture_positive q) (ht q)
    (mixture_positive r) (ht r)
    ((five_mode_real_response_fiber _ _ (mixture_positive q).isHermitian
      (mixture_positive r).isHermitian).1.mpr (mixture_real q r))
    ((hb q).trans (hb r).symm)
  norm_num [phaseProbability, mixture, phaseState, phaseRay, Matrix.trace,
    Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_succ, q, r] at he

/-- The opposite phase projectors are orthogonal density states. Their entire
convex segment lies in one actual response fiber and one branch-7 trace fiber,
while the plus projector reads the mixing parameter exactly. -/
theorem phase_lift_certificate (q : Set.Icc (0 : ℝ) 1) :
    (phaseState 1).PosSemidef ∧ Matrix.trace (phaseState 1) = 1 ∧
    (phaseState (-1)).PosSemidef ∧ Matrix.trace (phaseState (-1)) = 1 ∧
    phaseState 1 * phaseState 1 = phaseState 1 ∧
    phaseState (-1) * phaseState (-1) = phaseState (-1) ∧
    phaseState 1 * phaseState (-1) = 0 ∧
    (1 - phaseState 1).PosSemidef ∧ ¬ (phaseState 1).IsDiag ∧
    (mixture q).PosSemidef ∧ Matrix.trace (mixture q) = 1 ∧
    (∀ (r : Set.Icc (0 : ℝ) 1) (P : Protocol (Fin 5)) (h : Record P),
      ludersLaw menu P (mixture q) h = ludersLaw menu P (mixture r) h) ∧
    branchMass (mixture q) = (1 : ℂ) / 2 ∧
    phaseProbability (mixture q) = (q : ℝ) := by
  have hp := pure_pair
  have hc : (1 - phaseState 1).PosSemidef := by
    have hh := Matrix.posSemidef_conjTranspose_mul_self (1 - phaseState 1)
    have he : (1 - phaseState 1).conjTranspose * (1 - phaseState 1) =
        1 - phaseState 1 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        (phase_positive 1).isHermitian.eq]
      simp only [Matrix.sub_mul, Matrix.mul_sub, one_mul, mul_one, hp.2.2.1]
      abel
    rwa [he] at hh
  refine ⟨phase_positive 1, hp.1, phase_positive (-1), hp.2.1,
    hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, hc, ?_, mixture_positive q, ?_, ?_, ?_, ?_⟩
  · intro hd
    apply result
    intro rho sigma hrho _ hsigma _ hresponses _
    have hreal := (five_mode_real_response_fiber rho sigma
      hrho.isHermitian hsigma.isHermitian).1.mp hresponses
    have hdiag (i : Fin 5) : (phaseState 1 i i).im = 0 := by
      have hh := congrArg Complex.im ((phase_positive 1).isHermitian.apply i i)
      simp at hh
      linarith
    simp only [phaseProbability, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : j = i
    · subst j
      have he : (rho i i).re = (sigma i i).re := congrFun (congrFun hreal i) i
      simp [Complex.mul_re, he, hdiag]
    · simp [hd hij]
  · simp [mixture, Matrix.trace_add, Matrix.trace_smul, hp.1, hp.2.1]
  · intro r
    exact (five_mode_real_response_fiber _ _ (mixture_positive q).isHermitian
      (mixture_positive r).isHermitian).1.mpr (mixture_real q r)
  · rw [branchMass, arbitrary_branch_trace_reads_diagonal]
    norm_num [mixture, phaseState, phaseRay, Matrix.vecMulVec]
    ring
  · have hreverse : phaseState (-1) * phaseState 1 = 0 := by
      have h := congrArg Matrix.conjTranspose hp.2.2.2.2
      simpa [(phase_positive 1).isHermitian.eq,
        (phase_positive (-1)).isHermitian.eq] using h
    simp [phaseProbability, mixture, Matrix.add_mul, Matrix.smul_mul,
      hp.2.2.1, hreverse, Matrix.trace_add, Matrix.trace_smul, hp.1]

#print axioms phase_lift_certificate
#print axioms result

end D5.S3.Quantum.Fibers.FiveModePhaseLift
