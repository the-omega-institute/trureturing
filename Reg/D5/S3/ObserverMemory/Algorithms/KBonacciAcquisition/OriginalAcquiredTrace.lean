import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge OriginalAcquiredTrace
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

@[reducible] def traceSignature : Signature where
  Params := Σ k : {k : ℕ // 2 ≤ k}, Σ m : ℕ, Type z
  State p := List Bool × NarrowWindowCost.Selector p.2.1 p.2.2 × ℕ ×
    Option (ZMod 2) × NarrowWindowCost.Archive p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (p.2.2 × ℕ)
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature.{z} := realize traceSignature
  (fun _ p state => NarrowWindowCost.execute p.1.val (by have := p.1.property; omega)
    state.2.1 state.2.2.1 state.1 state.2.2.2.1 state.2.2.2.2)
  (fun e => nomatch e)

def traceRejected : Realization traceSignature.{z} :=
  realize traceSignature (fun _ _ _ => none) (fun e => nomatch e)

@[reducible] def traceArena : Arena where
  signature := traceSignature.{z}
  Law R := ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
    (localAlphabet : Bool) (f : Option (LiveRecord k) → Y)
    (history : List (AllowedBlock k m localAlphabet))
    (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m)
    (free : NarrowWindowCost.output k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) = y₀)
    (matched : ActualArchive k (by omega)
      (history.flatMap (fun action => List.ofFn action.val)) archive)
    (π : NarrowWindowCost.Selector m Y) (d c : ℕ),
    let w := history.flatMap (fun action => List.ofFn action.val)
    let initial := OriginalRecord k (by omega) w
    let current := OriginalRecord k (by omega) (w ++ archiveWords archive)
    R.readout () ⟨⟨k, hk⟩, m, Y⟩ (w ++ archiveWords archive, π, d, y₀, archive) =
        some (f initial, c) ↔
      ∃ issued, PaidTrace π y₀ current archive issued (f initial) ∧
        issued.length = c ∧ c ≤ d ∧ ActualArchive k (by omega) w (archive ++ issued) ∧
        (initial, OriginalRecord k (by omega) (w ++ archiveWords (archive ++ issued))) ∈
          AcquiredPairs k m (by omega) localAlphabet y₀ (archive ++ issued)

private theorem traceActualPositive : traceArena.{z}.Law traceActual := by
  intro Y k m hk localAlphabet f history y₀ archive free matched π d c
  exact acquired_execution_trace k m hk localAlphabet f history y₀ archive free matched π d c

private theorem traceRejectedNegative : ¬ traceArena.{z}.Law traceRejected := by
  intro h
  let label : ULift.{z} Unit := ⟨()⟩
  have rejected := h 3 1 (by decide) false (fun _ => label) [] (some 0) []
    (by rfl) trivial (fun _ _ => .inl label) 0 0
  have rhs : ∃ issued, PaidTrace (fun _ _ => .inl label) (some 0)
      (OriginalRecord 3 (by decide) ([] ++ archiveWords ([] : NarrowWindowCost.Archive 1)))
      [] issued (label) ∧ issued.length = 0 ∧ 0 ≤ 0 ∧
      ActualArchive 3 (by decide) [] ([] ++ issued) ∧
      (OriginalRecord 3 (by decide) [],
        OriginalRecord 3 (by decide) ([] ++ archiveWords ([] ++ issued))) ∈
        AcquiredPairs 3 1 (by decide) false (some 0) ([] ++ issued) := by
    refine ⟨[], rfl, rfl, le_rfl, trivial, ?_⟩
    exact ⟨[], rfl, trivial, rfl, rfl⟩
  have impossible := rejected.mpr rhs
  cases impossible

def traceEvidence : Registration traceArena.{z}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace.acquired_execution_trace.{z})) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨traceActualPositive, traceRejected, traceRejectedNegative⟩
  sensitivity := ⟨fun i => ⟨traceRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, traceRejectedNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let Y := ULift.{z} Bool
    let π : NarrowWindowCost.Selector 1 Y := fun y₀ _ => .inl ⟨decide (y₀ = some 0)⟩
    refine ⟨⟨⟨3, by decide⟩, 1, Y⟩,
      ([], π, 0, some 0, []), ([true], π, 0, some 1, []), ?_⟩
    simp [traceActual, realize, NarrowWindowCost.execute, π]
    intro h
    cases congrArg ULift.down h


end

end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace
