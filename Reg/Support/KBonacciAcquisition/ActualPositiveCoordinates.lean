import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace

namespace Reg.Support.KBonacciAcquisition.ActualPositiveCoordinates
open _root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge OriginalAcquiredTrace
open _root_.D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

def parent : Fin 1 → Bool := fun _ => true
private def initial : LiveRecord 3 := ⟨0, 0, 0⟩
private def current : LiveRecord 3 := ⟨1, 1, 1⟩
def acquired : NarrowWindowCost.Archive 1 :=
  [(parent, some ((0 : ZMod 2) + 1))]

private theorem initial_record : OriginalRecord 3 (by decide) [] = some initial := rfl

private theorem current_record :
    OriginalRecord 3 (by decide) (List.ofFn parent) = some current := by
  have step := OriginalExecutionBridge.record_append 3 (by decide) [] (List.ofFn parent)
  change OriginalRecord 3 (by decide) ([] ++ List.ofFn parent) =
    runWord (bitUpdate 3) (List.ofFn parent) (OriginalRecord 3 (by decide) []) at step
  rw [initial_record] at step
  simpa [parent, List.ofFn_succ, runWord, bitUpdate, coefficient, initial, current] using step

private theorem initial_output : NarrowWindowCost.output 3 (by decide) [] = some 0 := by
  calc
    NarrowWindowCost.output 3 (by decide) [] =
        endpointReading (OriginalRecord 3 (by decide) []) :=
      OriginalExecutionBridge.output_record 3 (by decide) []
    _ = some 0 := by rw [initial_record]; rfl

private theorem current_output :
    NarrowWindowCost.output 3 (by decide) (List.ofFn parent) = some 1 := by
  calc
    NarrowWindowCost.output 3 (by decide) (List.ofFn parent) =
        endpointReading (OriginalRecord 3 (by decide) (List.ofFn parent)) :=
      OriginalExecutionBridge.output_record 3 (by decide) (List.ofFn parent)
    _ = some 1 := by rw [current_record]; rfl

private theorem matched : ActualArchive 3 (by decide) [] acquired := by
  change NarrowWindowCost.output 3 (by decide) ([] ++ List.ofFn parent) =
    some ((0 : ZMod 2) + 1) ∧ True
  exact ⟨by simpa using current_output, trivial⟩

private theorem pair_member (localAlphabet : Bool) :
    (some initial, some current) ∈
      AcquiredPairs 3 1 (by decide) localAlphabet (some 0) acquired := by
  refine ⟨([] : List (AllowedBlock 3 1 localAlphabet)), ?_, ?_, ?_, ?_⟩
  · exact initial_output
  · exact matched
  · exact initial_record.symm
  · simpa [acquired, archiveWords] using current_record.symm

theorem support_member (localAlphabet : Bool) :
    (0 : ZMod 4) ∈ initialSupport 3 1 (by decide) localAlphabet 0 acquired := by
  refine ⟨initial, some current, pair_member localAlphabet, ?_⟩
  simp [initial]

end
end Reg.Support.KBonacciAcquisition.ActualPositiveCoordinates
