/- GID: D5/S3/Quantum/Entanglement/EJM/EJMAmplitudeCertificates
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMAmplitudeCertificates
   mirror-E: none(waiver:exact-coefficient-amplitude-receipts)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMNoiseRegion.actual_noise_box; premises=D5/S3/Quantum/Entanglement/EJM/EJMAmplitudeCertificates.actual_F1_abs_bound,D5/S3/Quantum/Entanglement/EJM/EJMAmplitudeCertificates.actual_F1_real_abs_bound
   digest: The original full EJM triangle coefficient tree earns its uniform integer and real amplitude bound. -/

/-
admission_basis: escape-witness
triangle_amplitude_accepted: proof_shape: bind-only; the private numeric
receipt is consumed by actual_F1_abs_bound and has no independent delivery.
actual_F1_abs_bound: proof_shape: content after inlining the same-delivery
checker soundness; escape_witness: checked_get_abs_bound's structural induction
is on the live path to the bound on every original F1 outcome event.
actual_F1_real_abs_bound: proof_shape: content after inlining the same-delivery
integer bound and checker soundness; escape_witness: the same structural
soundness, followed only by Mathlib integer-to-real absolute-value transport.
The final cast is a consumed normalization, not additional escape content.
The concrete acceptance receipt inspects all original stored triangle
coefficients, not the function space of four-valued outcome assignments.
The numeric premises are the exact original integer and real F1 amplitude
bounds named in the utility header. The actual full-tree receipt and generic
soundness discharge those premises without an amplitude assumption.
These premises and EJMNoiseRegion.actual_noise_box belong to one concrete
certificate delivery after its actual global positivity premise is earned.
The amplitude module is not an independent conditional certificate delivery.
This receipt establishes coefficient amplitude only; it does not establish
positivity of the full inflation score or a triangle-nonlocality conclusion.
Four-slot source registration remains unfinished under issue #16309.
-/

import D5.S3.Quantum.Entanglement.EJM.EJMCoefficientTreeBounds
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMAmplitudeCertificates
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData
open D5.S3.Quantum.Entanglement.EJM.EJMCoefficientTreeBounds

set_option maxRecDepth 10000 in
set_option maxHeartbeats 100000000 in
set_option trace.profiler true in
private theorem triangle_amplitude_accepted :
    checkAbsBound 53480245575024 triangleCoefficients = true := by
  decide +kernel

theorem actual_F1_abs_bound (e : Fin 10 → Fin 4) :
    |F1 e| ≤ (53480245575024 : ℤ) :=
  checked_get_abs_bound 53480245575024 triangleCoefficients
    triangle_amplitude_accepted (orbitKey trianglePerm e)

theorem actual_F1_real_abs_bound (e : Fin 10 → Fin 4) :
    |(F1 e : ℝ)| ≤ (53480245575024 : ℝ) := by
  exact_mod_cast actual_F1_abs_bound e

#print axioms actual_F1_abs_bound
#print axioms actual_F1_real_abs_bound

end D5.S3.Quantum.Entanglement.EJM.EJMAmplitudeCertificates
