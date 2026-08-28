/- GID: D5/S3/Quantum/Completion/OperationalReadoutQuotientRepresentation
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/OperationalReadoutQuotientRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Operational state classes are canonically represented by affine realized readouts. -/

import D5.S3.Quantum.Fibers.FutureStatisticsEquivalence
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-26):
   * Exact family hits `DensityState`, `MatrixOperatorSystem`, and
     `operatorSystemReadout` construct the source's positive trace-one state
     carrier and trace-pairing observation signature; they are imported.
   * Exact pinned-Mathlib hit `Setoid.quotientKerEquivRange` constructs the
     canonical equivalence from the observation-kernel quotient to its
     realized range and is named directly in the public statement.
   * Pinned Mathlib's `smul_nonneg`, `Matrix.trace_add`, and
     `Matrix.trace_smul` construct density-state mixtures and prove that the
     trace readout preserves them.
   * Repository and pinned-Mathlib searches found no theorem combining this
     exact density-state quotient representation with its affine law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Completion.OperationalReadoutQuotientRepresentation

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Fibers.FutureStatisticsEquivalence
open D5.S3.Quantum.Fibers.OperatorSystemTowerStability

private theorem cstar_trace_add {d : Type*} [Fintype d]
    (first second : MatrixAlgebra d) :
    Matrix.trace (first + second) = Matrix.trace first + Matrix.trace second := by
  simp [Matrix.trace, Finset.sum_add_distrib]

private theorem cstar_trace_real_smul {d : Type*} [Fintype d]
    (scalar : ℝ) (matrix : MatrixAlgebra d) :
    Matrix.trace (scalar • matrix) = scalar • Matrix.trace matrix := by
  simp [Matrix.trace, Finset.mul_sum]

/-- The quotient by equality of all operator-system trace readouts is
canonically represented by the realized readout range. The canonical
equivalence is uniquely determined by its value on state classes and carries
every binary density-state mixture to the same pointwise mixture of readouts. -/
theorem operational_readout_quotient_representation
    {d : Type*} [Fintype d] [DecidableEq d]
    (system : MatrixOperatorSystem d) :
    let readout := operatorSystemReadout system
    let quotientEquiv : Quotient (Setoid.ker readout) ≃ Set.range readout :=
      Setoid.quotientKerEquivRange readout
    (forall rho : DensityState d,
      quotientEquiv (Quotient.mk'' rho) =
        ⟨readout rho, ⟨rho, rfl⟩⟩) /\
      (forall other : Quotient (Setoid.ker readout) ≃ Set.range readout,
        (forall rho : DensityState d,
          other (Quotient.mk'' rho) = ⟨readout rho, ⟨rho, rfl⟩⟩) ->
            other = quotientEquiv) /\
      forall (t : ℝ) (rho sigma : DensityState d),
        0 ≤ t -> t ≤ 1 ->
          ExistsUnique fun mixture : DensityState d =>
            mixture.1 = t • rho.1 + (1 - t) • sigma.1 /\
              (quotientEquiv (Quotient.mk'' mixture)).1 =
                t • (quotientEquiv (Quotient.mk'' rho)).1 +
                  (1 - t) • (quotientEquiv (Quotient.mk'' sigma)).1 := by
  dsimp only
  constructor
  · intro rho
    rfl
  constructor
  · intro other hother
    apply Equiv.ext
    intro stateClass
    refine Quotient.inductionOn' stateClass ?_
    intro rho
    exact (hother rho).trans (by rfl)
  · intro t rho sigma ht0 ht1
    let mixture : DensityState d :=
      ⟨t • rho.1 + (1 - t) • sigma.1, by
        constructor
        · exact add_nonneg (smul_nonneg ht0 rho.2.1)
            (smul_nonneg (sub_nonneg.mpr ht1) sigma.2.1)
        · calc
            Matrix.trace (t • rho.1 + (1 - t) • sigma.1) =
                t • Matrix.trace rho.1 + (1 - t) • Matrix.trace sigma.1 := by
              rw [cstar_trace_add, cstar_trace_real_smul,
                cstar_trace_real_smul]
            _ = t • (1 : ℂ) + (1 - t) • (1 : ℂ) := by
              rw [rho.2.2, sigma.2.2]
            _ = 1 := by
              simp [Algebra.smul_def]⟩
    refine ⟨mixture, ⟨rfl, ?_⟩, ?_⟩
    · funext effect
      change Matrix.trace
          ((t • rho.1 + (1 - t) • sigma.1) * effect.1.1) =
        t • Matrix.trace (rho.1 * effect.1.1) +
          (1 - t) • Matrix.trace (sigma.1 * effect.1.1)
      rw [add_mul, smul_mul_assoc, smul_mul_assoc, cstar_trace_add,
        cstar_trace_real_smul, cstar_trace_real_smul]
    · intro other hother
      apply Subtype.ext
      exact hother.1

#print axioms operational_readout_quotient_representation

end D5.S3.Quantum.Completion.OperationalReadoutQuotientRepresentation
