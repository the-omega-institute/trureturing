/- GID: D5/S1/Recurrence/Periodic/BalaA281184TotientSquarePeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/BalaA281184TotientSquarePeriod
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Autonomous integral derivations yield prescribed totient-square tail periods. -/
/-
admission_basis: open-problem-resolution (#21643; Proved)
escape_witness: none
The claim retains the source expression; its proofs reuse the existing EGF
and primitive owners through compiled coefficient correspondences.
Escape audit unfinished:
https://github.com/the-omega-institute/trureturing/issues/21972
Direct frozen dependencies (declaration identities):
D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330
D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_derivative
statement_id: sha256:d8c528ef732aa837c3d79d7314200e072b40f5bcdc873683da352f1acf37c5c8
D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
statement_id: sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5
D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.linear_ode_unique
statement_id: sha256:3ee42d0d09e04d4498194d296af5f0f5a145cdae9192b759e0c6e4174d652ebe
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_ext
statement_id: sha256:be297942dba1d71d921d56e5059d2544375954e34dd6e505146ebcbbed2baaff
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840
Declaration names below are relative to this module.
claim: proof_shape: bind-only; consumer: result
result: proof_shape: content; consumer: settling result
-/

import D5.S1.Recurrence.Residue.IntegralEGFComposition
import D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod

namespace D5.S1.Recurrence.Periodic.BalaA281184TotientSquarePeriod
open D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod
open D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod.BalaEvenSource
open D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod.BalaLinearTruncation
open D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod.BalaOddBranch
open D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod.BalaPolynomialSystem
open D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod.BalaSecondOrderMatrix
open D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod.BalaTruncated


open D5.S1.Recurrence.Residue.IntegralEGFComposition
def claim : Prop :=
  ∃ (H C S : PowerSeries ℚ),
    PowerSeries.constantCoeff H = 0 ∧
    PowerSeries.derivative H = C ^ 3 ∧
    C = PowerSeries.C (1 / 2 : ℚ) *
      ((PowerSeries.exp ℚ).subst H + (PowerSeries.exp ℚ).subst (-H)) ∧
    PowerSeries.constantCoeff S = 0 ∧
    PowerSeries.derivative S = (1 + S ^ 2) ^ 2 ∧
    PowerSeries.derivative (PowerSeries.logOf (C + S)) = C ^ 3 ∧
    ∃ a : ℕ → ℤ,
      (∀ n : ℕ, (a n : ℚ) = eCoeff (C ^ 3) (2 * n)) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        Int.ModEq (k : ℤ) (a (n + (Nat.totient k) ^ 2)) (a n)
noncomputable section
theorem result : claim := by
  refine ⟨H 3,C 3,S 3,constant_H 3,derivative_H 3,cosh_identity 3,constant_S 3,
    A281180_ode,log_derivative 3,evenSequence 3 3,even_sequence_coefficient 3 3,?_⟩
  intro k hk
  obtain ⟨N,hN,hp⟩ := even_sequence_period 3 (by omega) 3 k hk
  exact ⟨N,hp⟩
end
end D5.S1.Recurrence.Periodic.BalaA281184TotientSquarePeriod
