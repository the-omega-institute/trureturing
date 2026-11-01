/- GID: D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianVacuum
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/InfiniteGaussianVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native infinite-mode bilinear Gaussian vacuum sewing. -/

import D5.S3.VertexAlgebra.TwistedGround.CountableGaussianCutoff
import D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum

/-!
The classical Gaussian/Fock/Wick vacuum identity is obtained from the actual
finite-coordinate identities and two limits of the same finite-subset net.
The index type is arbitrary, including empty types; no enumeration is chosen.
The trace logarithm uses the original trace-class product's positive powers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open Filter Topology

namespace D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum

open InfiniteGaussianFock CountableGaussianCutoff
open FactorialFockMetric (Occupation weight)

universe u
variable {I : Type u} [DecidableEq I]

/-- Absolute convergence and the genuine trace-log formula for the whole
bilinear occupation vacuum of two native symmetric Hilbert-Schmidt strict
contractions. There is no conjugation, commutativity or positivity premise. -/
theorem vacuum_trace_log (A B : Data I) :
    Summable (fun d : Occupation I =>
      ‖(weight d : ℂ) * coefficient A.kernel d * coefficient B.kernel d‖) ∧
    Summable (fun m : ℕ => ‖TraceClassPowerSeries.logTerm (product A B) m‖) ∧
      (∑' d : Occupation I,
        (weight d : ℂ) * coefficient A.kernel d * coefficient B.kernel d) =
        Complex.exp (TraceClassPowerSeries.traceLog (product A B)) := by
  obtain ⟨hocc, hocclim, _, _, _, _, hlog, _, _, _, hloglim, htrace, hblock⟩ :=
    native_cutoff_bridge A B
  have hfinite (F : Finset I) := FiniteSqueezedVacuum.vacuum_trace_log
    (A.block F) (B.block F)
    (fun i j => A.symmetric i.val j.val) (fun i j => B.symmetric i.val j.val)
    ((A.block_opNorm_le F).trans_lt A.q_lt_one)
    ((B.block_opNorm_le F).trans_lt B.q_lt_one)
  have hcut (F : Finset I) : occupationCutoff A B F =
      Complex.exp (TraceClassPowerSeries.traceLog (cutoffProduct A B F)) := by
    rw [hblock F, (hfinite F).2.2]
    congr 1
    rw [TraceClassPowerSeries.traceLog, ← (hfinite F).2.1.tsum_mul_left (1 / 2 : ℂ)]
    apply tsum_congr
    intro m
    rw [TraceClassPowerSeries.logTerm, htrace F m]
    have hm : (m : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m
    field_simp [hm]
    <;> ring
  have hexp := (Complex.continuous_exp.tendsto _).comp hloglim
  refine ⟨hocc, hlog, ?_⟩
  exact tendsto_nhds_unique hocclim (by simpa only [Function.comp_def, ← hcut] using hexp)

end D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum
