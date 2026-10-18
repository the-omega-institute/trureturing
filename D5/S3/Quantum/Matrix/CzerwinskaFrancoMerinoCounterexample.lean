/- GID: D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.conjecture; result=D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.result; claim=D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.conjecture
   digest: Radial convexity of order three does not characterize matrix monotonicity. -/

import D5.S3.Quantum.Matrix.CfmEndpointPositivity
import D5.S3.Quantum.Matrix.CfmMonotonicityCertificate

/-! A rational counterexample to Conjecture 4.10 on the whole positive cone. -/

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.CzerwinskaFrancoMerinoCounterexample

open RadialConvexity CayleyResolvent CfmRadialDerivative
open CfmEndpointPositivity CfmMonotonicityCertificate

/-- Conjecture 4.10, with both monotonicity directions allowed as in Definition 1.1. -/
def conjecture : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ f : ℝ → ℝ,
  RadiallyConvexOrder n f ↔ MatrixMonotoneDegree n f

private theorem cayley_functional_calculus {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    matFun scalarFunction A = resolventSum (1/20000 : ℝ) (cayley A) := by
  rw [matFun, cfc_rationalFunction hA]
  dsimp only [resolventSum]
  rw [cayley_resolvent 2 (by norm_num) A hA,
    cayley_resolvent 3 (by norm_num) A hA,
    cayley_resolvent 4 (by norm_num) A hA]
  norm_num [rationalFunction]
  simp only [← Algebra.algebraMap_eq_smul_one, map_ofNat]

private theorem radial_counterexample : RadiallyConvexOrder 3 scalarFunction := by
  intro A C B hA hC hB hAC hCB
  have ha := cayley_transport A hA
  have hc := cayley_transport C hC
  have hb := cayley_transport B hB
  have h := radial_of_endpoint_positive (1/20000 : ℝ)
    (fun U hU V hV hUV => endpoint_derivatives_positive U V hU hV hUV)
    (show cayley A ∈ cayleyDomain 3 from ⟨ha.1,ha.2.1⟩)
    (show cayley C ∈ cayleyDomain 3 from ⟨hc.1,hc.2.1⟩)
    (show cayley B ∈ cayleyDomain 3 from ⟨hb.1,hb.2.1⟩)
    (ha.2.2 C hC hAC) (hc.2.2 B hB hCB)
  rwa [cayley_functional_calculus A hA, cayley_functional_calculus C hC,
    cayley_functional_calculus B hB]

/-- The rational function is radially convex of order three and is monotone in
neither Loewner direction, refuting the universally quantified conjecture. -/
theorem result : ¬ conjecture := by
  intro h
  exact not_matrix_monotone ((h 3 (by norm_num) scalarFunction).mp radial_counterexample)

end D5.S3.Quantum.Matrix.CzerwinskaFrancoMerinoCounterexample
