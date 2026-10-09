import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder
import Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge OriginalAcquiredTrace PhysicalWindowDecoder
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace

/-- The complete source telescope, replacing only the original execution readout. -/
@[reducible] def scriptArena : Arena where
  signature := traceSignature.{u}
  Law R := ∀ {Y : Type u} (k m : ℕ) (hk : 2 ≤ k)
    (words : List (Fin m → Bool)) (decode : NarrowWindowCost.Archive m → Y)
    (w : List Bool) (free : Option (ZMod 2)) (base : NarrowWindowCost.Archive m),
    let issued := scriptArchive words (OriginalRecord k (by omega) w)
    PaidTrace (finalSelector base.length words decode) free
      (OriginalRecord k (by omega) w) base issued (decode issued) ∧
    issued.map Prod.fst = words ∧ issued.length = words.length ∧
    R.readout () ⟨⟨k, hk⟩, m, Y⟩
      (w, finalSelector base.length words decode, words.length, free, base) =
      some (decode issued, words.length)

private theorem scriptPositive : scriptArena.{u}.Law traceActual := by
  intro Y k m hk words decode w free base
  exact original_final_script k m hk words decode w free base

private theorem scriptNegative : ¬ scriptArena.{u}.Law traceRejected := by
  intro law
  let label : ULift.{u} Unit := ⟨()⟩
  have impossible := (law 3 1 (by decide) [] (fun _ => label) [] (some 0) []).2.2.2
  cases impossible

def scriptEvidence : Registration scriptArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.original_final_script.{u})) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨scriptPositive, traceRejected, scriptNegative⟩
  sensitivity := ⟨fun i => ⟨traceRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, scriptNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let Y := ULift.{u} Bool
    let π₀ : NarrowWindowCost.Selector 1 Y := fun _ _ => .inl ⟨false⟩
    let π₁ : NarrowWindowCost.Selector 1 Y := fun _ _ => .inl ⟨true⟩
    refine ⟨⟨⟨3, by decide⟩, 1, Y⟩,
      ([], π₀, 0, some 0, []), ([], π₁, 0, some 0, []), ?_⟩
    simp [traceActual, realize, NarrowWindowCost.execute, π₀, π₁]
    intro h
    cases congrArg ULift.down h

#print axioms scriptEvidence

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder
