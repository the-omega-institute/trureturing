/- GID: D5/S1/Words/Complexity/CassaigneSturmianCharacterization
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/CassaigneSturmianCharacterization
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/Complexity/CassaigneSturmianCharacterization.claim; result=D5/S1/Words/Complexity/CassaigneSturmianCharacterization.result; claim=D5/S1/Words/Complexity/CassaigneSturmianCharacterization.claim
   digest: Equal asymptotic indices do not characterize Sturmian words. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26320
admission_basis: open-problem-resolution (#23441; Refuted)
escape_witness: none
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
claim: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Words.Complexity.CassaigneSturmianCharacterization.result.
nominated_invariant_values: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window, _private.D5.S1.Words.Complexity.CassaigneRecurrenceTransport.0.D5.S1.Words.Complexity.CassaigneRecurrenceTransport.recurrence_bound_replicated, _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_bound_of_gap_max, _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.no_short_recurrence_of_periodic, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.removed_last_gap_ge_returns; consumers: D5.S1.Words.Complexity.CassaigneSturmianCharacterization.result.
result: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window, _private.D5.S1.Words.Complexity.CassaigneRecurrenceTransport.0.D5.S1.Words.Complexity.CassaigneRecurrenceTransport.recurrence_bound_replicated, _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_bound_of_gap_max, _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.no_short_recurrence_of_periodic, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.removed_last_gap_ge_returns; consumers: none.
-/


import D5.S1.Words.Complexity.CassaigneIndexTransport
import D5.S1.Words.Complexity.CassaigneRecurrenceTransport
import D5.S1.Words.GoldenWord
import D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence
import D5.S1.Words.ReturnWords.GoldenSharpRepetitions
set_option maxHeartbeats 1600000

open D5.S0.Computability.Coding.BiasedMassFrontier

namespace D5.S1.Words.Complexity.CassaigneSturmianCharacterization

open Set Filter D5.S1.Words D5.S1.Words.Mechanical D5.S1.Words.Powers
open scoped ENNReal Topology
open D5.S1.Words.Complexity.CassaigneRecurrenceTransport
open D5.S1.Words.Complexity.CassaigneIndexTransport
open D5.S1.Words.ReturnWords.GoldenSharpRepetitions
open D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence

def claim : Prop :=
  ∀ u : ℕ → Bool, indStar u = rhoStar u → IsSturmian u

private theorem nominated_invariant_values (k : ℕ) (hk : 2 ≤ k) :
    indStar ((replicated k D5.S1.Words.goldenWord)) = ENNReal.ofReal (2+Real.goldenRatio) ∧
      rhoStar ((replicated k D5.S1.Words.goldenWord)) = ENNReal.ofReal (2+Real.goldenRatio) := by
  change indStar (replicated k D5.S1.Words.goldenWord) = _ ∧
    rhoStar (replicated k D5.S1.Words.goldenWord) = _
  rw [golden_indStar_replicated k (by omega),rhoStar_replicated k (by omega)]
  exact ⟨golden_indStar_eq_sharp,golden_rhoStar_eq_sharp⟩

theorem result : ¬ claim := by
  intro hc
  have hv := nominated_invariant_values 2 (by decide)
  exact vk_not_sturmian 2 (by decide)
    (hc ((replicated 2 D5.S1.Words.goldenWord)) (hv.1.trans hv.2.symm))

end D5.S1.Words.Complexity.CassaigneSturmianCharacterization
