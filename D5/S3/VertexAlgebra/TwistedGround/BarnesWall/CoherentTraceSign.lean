/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/CoherentTraceSign
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/CoherentTraceSign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: The normalized modular identity excludes the nonzero candidate. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Q8GroundTrace
import D5.S3.HomologicalAlgebra.BarnesWallQ8CyclicGauge
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.CyclicEtaTrace

/-! The rank-128 finite trace calculation forces the positive sign
for every coherent quaternion action implementing the two lift phases. -/

open scoped BigOperators Topology

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.CoherentTraceSign

open LatticeTwistedGroundRealization (Ground)
open LatticeTwistedGroundRealization.SignQuotient (complexSign)
open Q8TraceSign (Charge actionI actionJ phaseI phaseJ)
open Q8GroundTrace (groundOperator normalized_trace_mul_eq_two_pow_32)

local notation "tr" => LinearMap.trace ℂ (Ground 64)

theorem coherent_trace_product_positive
    {Ti Tj Tk : Module.End ℂ (Ground 64)} (hTi : Ti ≠ 0) (hTj : Tj ≠ 0)
    (hcovI : ∀ a : Charge, Ti * groundOperator a =
      complexSign (phaseI a) • (groundOperator (actionI a) * Ti))
    (hcovJ : ∀ a : Charge, Tj * groundOperator a =
      complexSign (phaseJ a) • (groundOperator (actionJ a) * Tj))
    (hcoherent : Ti * Tj = Tk)
    (hi : (tr Ti).im = 0) (hj : (tr Tj).im = 0) (hk : (tr Tk).im = 0) :
    0 < (tr Ti).re * (tr Tj).re * (tr Tk).re := by
  let x := (tr Ti).re
  let y := (tr Tj).re
  let z := (tr Tk).re
  have hx : tr Ti = (x : ℂ) := Complex.ext rfl (by simpa using hi)
  have hy : tr Tj = (y : ℂ) := Complex.ext rfl (by simpa using hj)
  have hz : tr Tk = (z : ℂ) := Complex.ext rfl (by simpa using hk)
  have h := normalized_trace_mul_eq_two_pow_32 hTi hTj hcovI hcovJ
  rw [hcoherent, hx, hy, hz] at h
  have hxy : (x : ℂ) * (y : ℂ) ≠ 0 := by
    intro hc
    rw [hc, div_zero] at h
    exact (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)) h.symm
  have hreal : (2 : ℝ) ^ 64 * z = (2 : ℝ) ^ 32 * (x * y) := by
    have h' := (div_eq_iff hxy).mp h
    exact Complex.ofReal_injective (by exact_mod_cast h')
  have hnz : x * y ≠ 0 := by
    exact_mod_cast hxy
  change 0 < x * y * z
  apply (mul_pos_iff_of_pos_left (by positivity : 0 < (2 : ℝ) ^ 64)).mp
  calc
    0 < (2 : ℝ) ^ 32 * (x * y) ^ 2 := mul_pos (by positivity) (sq_pos_of_ne_zero hnz)
    _ = (x * y) * ((2 : ℝ) ^ 32 * (x * y)) := by ring
    _ = (2 : ℝ) ^ 64 * (x * y * z) := by rw [← hreal]; ring

/-- Once modular transport gives the stated cyclic trace relation, the
rank-128 operators exclude the nonzero inflated anomaly. -/
theorem zero_candidate_of_cyclic_traces
    {Ti Tj Tk : Module.End ℂ (Ground 64)} (hTi : Ti ≠ 0) (hTj : Tj ≠ 0)
    (hcovI : ∀ a : Charge, Ti * groundOperator a =
      complexSign (phaseI a) • (groundOperator (actionI a) * Ti))
    (hcovJ : ∀ a : Charge, Tj * groundOperator a =
      complexSign (phaseJ a) • (groundOperator (actionJ a) * Tj))
    (hcoherent : Ti * Tj = Tk)
    (hi : (tr Ti).im = 0) (hj : (tr Tj).im = 0) (hk : (tr Tk).im = 0)
    (e : ZMod 2) (cyclicTrace : Fin 3 → ℝ)
    (hcyclic : ∀ r, 0 < cyclicTrace r)
    (htransport : ∀ r, cyclicTrace r =
      (-1 : ℝ) ^ ((HomologicalAlgebra.BarnesWallQ8CyclicGauge.beta e 1 2) -
        (HomologicalAlgebra.BarnesWallQ8CyclicGauge.beta e 2 1)).val *
        (![ (tr Ti).re, (tr Tj).re, (tr Tk).re ] : Fin 3 → ℝ) r) :
    e = 0 := by
  apply HomologicalAlgebra.BarnesWallQ8CyclicGauge.zero_exponent_of_positive_trace_product
    e _ cyclicTrace _ hcyclic htransport
  simpa [Fin.prod_univ_three] using
    coherent_trace_product_positive hTi hTj hcovI hcovJ hcoherent hi hj hk

open Filter UpperHalfPlane

/-- The finite trace and the cyclic modular formula determine the anomaly
candidate. The modular formula and transport here refer to the very same
twisted character as the ground-coefficient limit. -/
theorem zero_candidate_of_modular_identity
    {Ti Tj Tk : Module.End ℂ (Ground 64)} (hTi : Ti ≠ 0) (hTj : Tj ≠ 0)
    (hcovI : ∀ a : Charge, Ti * groundOperator a =
      complexSign (phaseI a) • (groundOperator (actionI a) * Ti))
    (hcovJ : ∀ a : Charge, Tj * groundOperator a =
      complexSign (phaseJ a) • (groundOperator (actionJ a) * Tj))
    (hcoherent : Ti * Tj = Tk)
    (hi : (tr Ti).im = 0) (hj : (tr Tj).im = 0) (hk : (tr Tk).im = 0)
    (e : ZMod 2) (cyclicTrace : Fin 3 → ℝ) (Z : Fin 3 → ℍ → ℂ)
    (hS : ∀ r z, Z r z = (2 : ℂ) ^ 32 *
      (ModularForm.eta ((-1 / (z : ℂ)) / 4) * ModularForm.eta (-1 / (z : ℂ)) /
        ModularForm.eta ((-1 / (z : ℂ)) / 2) ^ 2) ^ 64)
    (hground : ∀ r, Tendsto (fun z : ℍ => Z r z / Function.Periodic.qParam 24 z ^ 64)
      atImInfty (𝓝 ((cyclicTrace r : ℝ) : ℂ)))
    (htransport : ∀ r, cyclicTrace r =
      (-1 : ℝ) ^ ((HomologicalAlgebra.BarnesWallQ8CyclicGauge.beta e 1 2) -
        (HomologicalAlgebra.BarnesWallQ8CyclicGauge.beta e 2 1)).val *
        (![ (tr Ti).re, (tr Tj).re, (tr Tk).re ] : Fin 3 → ℝ) r) :
    e = 0 := by
  apply zero_candidate_of_cyclic_traces hTi hTj hcovI hcovJ hcoherent hi hj hk e cyclicTrace
    _ htransport
  intro r
  have h := CyclicEtaTrace.cyclic_ground_trace_eq_two_pow_32 (Z r) _ (hS r) (hground r)
  have hr : cyclicTrace r = (2 : ℝ) ^ 32 := by exact_mod_cast h
  rw [hr]
  positivity

#print axioms coherent_trace_product_positive

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.CoherentTraceSign
