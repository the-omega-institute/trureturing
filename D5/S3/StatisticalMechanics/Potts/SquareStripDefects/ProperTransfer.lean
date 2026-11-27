/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.raw_successors
   digest: Saturated scanner fibres for the six-column square strip. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229457Strip.result)
between: proof_shape=bind-only; consumers=HardinA229457Strip.a, HardinA229457Strip.finite_certificate, HardinA229457Strip.finite_certificate._proof_3, HardinA229457Strip.result, HardinA229457Strip.result._proof_2, HardinA229457Strip.result._proof_5, HardinA229457StripClass0.transition_counts, HardinA229457StripClass0.transition_counts._proof_2 through HardinA229457StripClass0.transition_counts._proof_82, HardinA229457StripClass1.transition_counts, HardinA229457StripClass1.transition_counts._proof_2 through HardinA229457StripClass1.transition_counts._proof_82, HardinA229457StripClass2.transition_counts, HardinA229457StripClass2.transition_counts._proof_2 through HardinA229457StripClass2.transition_counts._proof_82, HardinA229457StripClass3.transition_counts, HardinA229457StripClass3.transition_counts._proof_2 through HardinA229457StripClass3.transition_counts._proof_82, HardinA229457StripClass4.transition_counts, HardinA229457StripClass4.transition_counts._proof_2 through HardinA229457StripClass4.transition_counts._proof_82, HardinA229457StripClass5.transition_counts, HardinA229457StripClass5.transition_counts._proof_2 through HardinA229457StripClass5.transition_counts._proof_82, HardinA229457StripClass6.transition_counts, HardinA229457StripClass6.transition_counts._proof_2 through HardinA229457StripClass6.transition_counts._proof_82, HardinA229457StripClass7.transition_counts, HardinA229457StripClass7.transition_counts._proof_2 through HardinA229457StripClass7.transition_counts._proof_82, HardinA229457StripClasses.transition_counts, HardinA229457StripCut.active_counts, HardinA229457StripCut.class_cut, HardinA229457StripCut.class_cut._proof_1 through HardinA229457StripCut.class_cut._proof_2, HardinA229457StripCut.proper_counts, HardinA229457StripCut.zero_cost, HardinA229604Strip.a, HardinA229604Strip.finite_certificate, HardinA229604Strip.finite_certificate._proof_2, HardinA229604Strip.result, HardinA229604Strip.result._proof_2, HardinA229604Strip.result._proof_5, HardinA229604StripClasses.transition_counts, HardinA229604StripCut.leading_counts, HardinA229604StripCut.one_defect_counts, HardinA229604StripCut.one_defect_counts._proof_1 through HardinA229604StripCut.one_defect_counts._proof_7, HardinA229604StripCut.one_defect_cut, HardinA229604StripCut.one_defect_cut._proof_1 through HardinA229604StripCut.one_defect_cut._proof_5, HardinA229604StripCut.terminal_counts, HardinA229604StripCut.terminal_counts._proof_3 through HardinA229604StripCut.terminal_counts._proof_5, HardinA229604StripCut.terminal_cut, HardinA229604StripCut.terminal_cut._proof_1 through HardinA229604StripCut.terminal_cut._proof_2, HardinA229604StripLastCut.transition_counts, HardinA229604StripLastCut.transition_counts._proof_1, between.eq_1, TwoDefects.First.HardinA229604StripClass0.transition_counts, TwoDefects.First.HardinA229604StripClass0.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass0.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass1.transition_counts, TwoDefects.First.HardinA229604StripClass1.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass1.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass10.transition_counts, TwoDefects.First.HardinA229604StripClass10.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass10.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass11.transition_counts, TwoDefects.First.HardinA229604StripClass11.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass11.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass12.transition_counts, TwoDefects.First.HardinA229604StripClass12.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass12.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass13.transition_counts, TwoDefects.First.HardinA229604StripClass13.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass13.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass2.transition_counts, TwoDefects.First.HardinA229604StripClass2.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass2.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass3.transition_counts, TwoDefects.First.HardinA229604StripClass3.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass3.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass4.transition_counts, TwoDefects.First.HardinA229604StripClass4.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass4.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass5.transition_counts, TwoDefects.First.HardinA229604StripClass5.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass5.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass6.transition_counts, TwoDefects.First.HardinA229604StripClass6.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass6.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass7.transition_counts, TwoDefects.First.HardinA229604StripClass7.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass7.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass8.transition_counts, TwoDefects.First.HardinA229604StripClass8.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass8.transition_counts._proof_82, TwoDefects.First.HardinA229604StripClass9.transition_counts, TwoDefects.First.HardinA229604StripClass9.transition_counts._proof_2 through TwoDefects.First.HardinA229604StripClass9.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass14.transition_counts, TwoDefects.Last.HardinA229604StripClass14.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass14.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass15.transition_counts, TwoDefects.Last.HardinA229604StripClass15.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass15.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass16.transition_counts, TwoDefects.Last.HardinA229604StripClass16.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass16.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass17.transition_counts, TwoDefects.Last.HardinA229604StripClass17.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass17.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass18.transition_counts, TwoDefects.Last.HardinA229604StripClass18.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass18.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass19.transition_counts, TwoDefects.Last.HardinA229604StripClass19.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass19.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass20.transition_counts, TwoDefects.Last.HardinA229604StripClass20.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass20.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass21.transition_counts, TwoDefects.Last.HardinA229604StripClass21.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass21.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass22.transition_counts, TwoDefects.Last.HardinA229604StripClass22.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass22.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass23.transition_counts, TwoDefects.Last.HardinA229604StripClass23.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass23.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass24.transition_counts, TwoDefects.Last.HardinA229604StripClass24.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass24.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass25.transition_counts, TwoDefects.Last.HardinA229604StripClass25.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass25.transition_counts._proof_82, TwoDefects.Last.HardinA229604StripClass26.transition_counts, TwoDefects.Last.HardinA229604StripClass26.transition_counts._proof_2 through TwoDefects.Last.HardinA229604StripClass26.transition_counts._proof_82
cl: proof_shape=bind-only; consumers=HardinA229457StripClasses.class_relabel, HardinA229457StripData.cl
T: proof_shape=bind-only; consumers=HardinA229457StripData.T, HardinA229457StripPowers.leading_steps
raw_successors: proof_shape=bind-only; consumers=HardinA229457StripCut.proper_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Certificate
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127CertificateZero
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport

/-! Exact residual-budget square-lattice strip transfer. -/

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row)
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def between : Finset (Fin 6 × Fin 6) := (Finset.univ : Finset (Fin 6)).diag
def cl (p : Row) : Fin 10 :=
  ⟨(HardinA233127SquareStrip.boundaryClass (true, true) p).val - 1, by
    have := (HardinA233127SquareStrip.boundaryClass (true, true) p).isLt
    have hz : ∀ p : Row, 0 < (HardinA233127SquareStrip.boundaryClass (true, true) p).val := by
      intro p
      simp only [HardinA233127SquareStrip.boundaryClass, Bool.true_eq, ↓reduceIte]
      split_ifs <;> decide
    have := hz p
    omega⟩
def T : Matrix (Fin 10) (Fin 10) ℤ := fun i j =>
  HardinA233127SquareStrip.transfer ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩ / 64

/-- The ten proper-row classes are the saturated scanner classes, divided by their fibre size. -/
theorem raw_successors (p : Row) (hp : HardinThinGraphTransport.proper p) (j : Fin 11) :
    64 * (∑ r : Row, if HardinThinGraphTransport.proper r ∧
      (∀ i : Fin 6, p i ≠ r i) ∧
      HardinA233127SquareStrip.boundaryClass (true, true) r = j then (1 : ℤ) else 0) =
      HardinA233127SquareStrip.transfer
        (HardinA233127SquareStrip.boundaryClass (true, true) p) j := by
  have ha : HardinA233127SquareStrip.Valid (true, true) p := ⟨rfl, hp, by simp⟩
  have ht := HardinA233127SquareStrip.row_counts (true, true) p ha j
  have hc := HardinA233127SquareStrip.class_fibres (true, true) p j
  simp_rw [(HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2] at hc
  norm_num only [show (2 : ℤ)^6 = 64 by norm_num] at hc
  rw [← Finset.mul_sum] at hc
  exact hc.symm.trans ht
end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
