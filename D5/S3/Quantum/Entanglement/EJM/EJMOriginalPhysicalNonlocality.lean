/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalPhysicalNonlocality
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalPhysicalNonlocality
   mirror-E: none(waiver:actual-independent-source-noise-refutation)
   anchors: []
   utility: kind=numeric-reduction; basis=refutes=gid:D5/S3/Quantum/Entanglement/EJM/EJMOriginalPhysicalNonlocality.claim; result=D5/S3/Quantum/Entanglement/EJM/EJMOriginalPhysicalNonlocality.result; claim=D5/S3/Quantum/Entanglement/EJM/EJMOriginalPhysicalNonlocality.claim
   digest: The original EJM certificate excludes continuous triangle locality in an explicit physical source-noise region. -/

import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierRoot
import D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseRobustness

/-
admission_basis: escape-witness
proof_shape: lookup_bounded: content (structural induction on the actual lookup tree);
triangle_dictionary_bounded: content (kernel reduction of all 4,588 literal nodes);
original_triangle_amplitude: content (the same-delivery dictionary bound is live);
result: content (the same-delivery complete original score margin and literal
amplitude bound are live numerical inputs, not frozen hypotheses).
Consumers: lookup_bounded and triangle_dictionary_bounded are used by
original_triangle_amplitude, which is used by result. The complete original
root and its new numerical inputs must first freeze in this same delivery.
The existing frozen physical-noise bridge supplies the analytic implication.

Question answered: the active formalization goal asks for a strictly nonlocal
region of the actual independent-source quantum noise model. The claim below
asserts the existence of a continuous triangle-local law inside that region.
It is refuted using the unchanged F1/F2, all twenty inflation coordinates,
all four outcomes, all thirty-two blocks and the original scale 6987435.
This prepared source is not acceptance evidence: its entire root dependency
closure and this result still require actual kernel and canonical validation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalPhysicalNonlocality

open EJMCertificateData (CoefficientTree triangleCoefficients F1 F2)
open EJMInflationScore (score)
open ElegantJointMeasurementInflation (Node)
open ElegantJointMeasurementSourceNoise (ejmProbability)
open ElegantJointMeasurementNoiseRobustness (positive_score_excludes_physical_noise)
open TriangleSymmetricLocalRefutation (IsTriangleLocal)

private def bounded : CoefficientTree → ℤ → Bool
  | .empty, amplitude => decide (0 ≤ amplitude)
  | .node _ value left right, amplitude =>
      decide (|value| ≤ amplitude) && (bounded left amplitude && bounded right amplitude)

private theorem lookup_bounded (tree : CoefficientTree) (amplitude : ℤ)
    (accepted : bounded tree amplitude = true) (key : ℕ) :
    |tree.get key| ≤ amplitude := by
  induction tree with
  | empty =>
      simpa only [bounded, decide_eq_true_eq, CoefficientTree.get, abs_zero] using accepted
  | node index value left right leftBound rightBound =>
      have h := Bool.and_eq_true_iff.mp accepted
      have children := Bool.and_eq_true_iff.mp h.2
      have hv : |value| ≤ amplitude := of_decide_eq_true h.1
      simp only [CoefficientTree.get]
      split_ifs
      · exact hv
      · exact leftBound children.1
      · exact rightBound children.2

set_option maxHeartbeats 10000000 in
private theorem triangle_dictionary_bounded :
    bounded triangleCoefficients 53480245575024 = true := by
  decide +kernel

private theorem original_triangle_amplitude (event : Fin 10 → Fin 4) :
    |F1 event| ≤ 53480245575024 :=
  lookup_bounded triangleCoefficients 53480245575024 triangle_dictionary_bounded _

/-- A continuous triangle-local realization exists at physical independent
source visibilities whose total deficit is below the explicit threshold. -/
def claim : Prop :=
  ∃ x y z : ℝ,
    x ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1 ∧ z ∈ Set.Icc (0 : ℝ) 1 ∧
    (1 - x) + (1 - y) + (1 - z) < (2329145 / 146036723916865536 : ℝ) ∧
    IsTriangleLocal (ejmProbability x y z)

/-- The original complete certificate refutes continuous triangle locality
throughout this strict physical independent-source noise region. -/
theorem result : ¬ claim := by
  rintro ⟨x, y, z, hx, hy, hz, deficits, hlocal⟩
  apply positive_score_excludes_physical_noise F1 F2 x y z
    53480245575024 6987435 hx hy hz (by norm_num) ?_ ?_ ?_ hlocal
  · intro event
    exact_mod_cast original_triangle_amplitude event
  · intro event
    have margin : (6987435 : ℤ) ≤ score F1 F2 event := by
      simpa only [EJMPartialBoundData.scale] using
        PreparedEJMCompleteFrontier.original_score_lower_bound event
    exact_mod_cast margin
  · have multiplied := mul_lt_mul_of_pos_left deficits
      (by norm_num : (0 : ℝ) < 8192 * 53480245575024)
    norm_num at multiplied ⊢
    exact multiplied

#print axioms original_triangle_amplitude
#print axioms result

end D5.S3.Quantum.Entanglement.EJM.EJMOriginalPhysicalNonlocality
