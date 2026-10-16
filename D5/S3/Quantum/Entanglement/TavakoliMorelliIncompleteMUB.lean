/- GID: D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Incomplete mutually unbiased bases and Schmidt-number correlation bounds. -/

import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
import D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB

open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Tomography.RankOneContextCommutator
open D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Observer.Conditioning

/-- Arbitrary unitary bases with the prescribed overlaps between distinct bases. -/
abbrev MUBFamily (d m : ℕ) :=
  {U : Fin m → Matrix.unitaryGroup (Fin d) ℂ //
    ∀ l k, l ≠ k → ∀ a b,
      ‖((U l).valᴴ * (U k).val) a b‖ ^ 2 = 1 / (d : ℝ)}

def MUBFamily.ket {d m : ℕ} (A : MUBFamily d m) (l : Fin m) (a : Fin d) :
    Ket (Fin d) :=
  ⟨fun i => (A.val l).val i a, Matrix.unitaryGroup_row_norm (A.val l) a⟩

def MUBFamily.effect {d m : ℕ} (A : MUBFamily d m) (p : Fin m × Fin d) : Op d :=
  proj (A.ket p.1 p.2)

def Qm {d m : ℕ} (ρ : BipartiteOp d) (A B : MUBFamily d m) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ :=
  correlation ρ A.effect B.effect

theorem mub_effect_scaledPure {d m : ℕ} (A : MUBFamily d m) (p : Fin m × Fin d) :
    ScaledPure (A.effect p) :=
  ⟨1, A.ket p.1 p.2, zero_le_one, (one_smul ℂ _).symm⟩

theorem mub_effect_sum {d m : ℕ} (A : MUBFamily d m) (l : Fin m) :
    ∑ a, A.effect (l, a) = 1 := by
  ext i j
  change (∑ a, proj (A.ket l a)) i j = _
  simp only [Matrix.sum_apply, MState.pure_apply]
  change ∑ a, (A.val l).val i a * star ((A.val l).val j a) = _
  exact congrArg (fun M : Op d => M i j) (Unitary.mul_star_self_of_mem (A.val l).prop)

def MUBFamily.context {d m : ℕ} (A : MUBFamily d m) (l : Fin m) :
    RankOneContext d where
  projector a := A.effect (l, a)
  rankOne a := by
    refine ⟨(scaledPure_hermitian (mub_effect_scaledPure A (l, a))).eq, ?_, ?_, ?_⟩
    · rw [show A.effect (l, a) = proj (A.ket l a) by rfl, proj_eq_outer]
      exact (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake
        (A.ket l a).vec (ket_dot_self _) 1).1
    · exact MState.tr' (MState.pure (A.ket l a))
    · intro X
      rw [scaledPure_sandwich (mub_effect_scaledPure A (l, a)), Matrix.trace_mul_comm]
  resolvesIdentity := mub_effect_sum A l

theorem mub_column_inner {d m : ℕ} (A : MUBFamily d m) (l k : Fin m) (a b : Fin d) :
    star (A.ket l a).vec ⬝ᵥ (A.ket k b).vec =
      ((A.val l).valᴴ * (A.val k).val) a b := by
  rfl

theorem mub_context_record {d m : ℕ} (A : MUBFamily d m) (l : Fin m) :
    IsRecordMeasurement (A.context l).projector := by
  refine ⟨?_, fun a => ((A.context l).rankOne a).2.1, ?_, (A.context l).resolvesIdentity⟩
  · intro a
    exact ((A.context l).rankOne a).1
  · intro a b hab
    change proj (A.ket l a) * proj (A.ket l b) = 0
    rw [proj_eq_outer, proj_eq_outer, vecMulVec_mul_vecMulVec, mub_column_inner]
    have hUnitary : ((A.val l).valᴴ * (A.val l).val) a b = 0 := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.one_apply_ne hab] using
        congrArg (fun M : Op d => M a b) (Unitary.star_mul_self_of_mem (A.val l).prop)
    rw [hUnitary, zero_smul, vecMulVec_zero]

theorem mub_context_overlap {d m : ℕ} (A : MUBFamily d m) (l k : Fin m)
    (hlk : l ≠ k) (a b : Fin d) :
    overlap (A.context l) (A.context k) a b = (d : ℝ)⁻¹ := by
  change (proj (A.ket l a) * proj (A.ket k b)).trace.re = _
  rw [proj_overlap, Complex.ofReal_re, mub_column_inner, A.property l k hlk]
  exact one_div _

end D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB
