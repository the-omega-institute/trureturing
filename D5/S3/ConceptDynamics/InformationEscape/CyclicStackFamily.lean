/- GID: D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/CyclicStackFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded recursive stack laws share their actual process readout. -/

import D5.S1.Words.Patterns.CyclicStackPreimages
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open D5.S1.Words.Patterns.CyclicStackPreimages
open DependentFamily

def signature : Signature where
  Params := List ℕ
  State := fun _ => List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ input stack => process input stack) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def runArena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ input stack, r.readout () input stack = (run input stack).1 ++ (run input stack).2

def permArena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (input stack : List ℕ), (r.readout () input stack).Perm (input ++ stack)

/-- One observable operation over the full parameter and state domains. -/
def singleObservation (Params State Output : Type) : Signature where
  Params := Params
  State := fun _ => State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Output
  Anchor := Empty
  finiteAnchor := inferInstance

namespace Append

def signature : Signature := singleObservation (Σ _ : List ℕ, List ℕ) (List ℕ) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ p stack => process (p.1 ++ p.2) stack) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (pre suffix stack : List ℕ),
    r.readout () ⟨pre, suffix⟩ stack =
      (run pre stack).1 ++ process suffix (run pre stack).2

end Append

namespace DrainLow

def signature : Signature := singleObservation (Σ _ : ℕ, ℕ) (List ℕ) (List ℕ × List ℕ)

def actual : Realization signature :=
  realize signature (fun _ p stack => drain p.1 (p.2 :: stack)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ([], [])) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {n low high : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) {input stack : List ℕ}
    (houtput : (process (low :: input) (high :: stack)).Sublist (target n)),
    r.readout () ⟨low, high⟩ stack = ([], high :: stack)

end DrainLow

namespace TwoLows

def signature : Signature := singleObservation (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, List ℕ) (List ℕ) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ p stack => process (p.1 :: p.2.1 :: p.2.2.2) (p.2.2.1 :: stack)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {n low₁ low₂ high : ℕ}
    (hlow₁ : low₁ ≤ n / 2) (hlow₂ : low₂ ≤ n / 2)
    (hne : low₁ ≠ low₂) (hhigh : n / 2 < high) {input stack : List ℕ}
    (houtput : (r.readout () ⟨low₁, low₂, high, input⟩ stack).Sublist
      (target n)),
    False

end TwoLows

namespace HighIncrease

def signature : Signature := singleObservation (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, List ℕ) (List ℕ) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ p stack => process (p.2.2.1 :: p.2.2.2) (p.1 :: p.2.1 :: stack)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {n low high next : ℕ}
    (hlow : low ≤ n / 2) (hnext : n / 2 < next)
    {input stack : List ℕ}
    (houtput : (r.readout () ⟨low, high, next, input⟩ stack).Sublist
      (target n)),
    high < next

end HighIncrease

namespace DrainHigh

def arena : DependentFamily.Arena where
  signature := DrainLow.signature
  Law r := ∀ {n x high futureLow : ℕ}
    (hhigh : n / 2 < high) (hlow : futureLow ≤ n / 2)
    {input stack : List ℕ} (hmem : futureLow ∈ input)
    (houtput : (process (x :: input) (high :: stack)).Sublist (target n)),
    r.readout () ⟨x, high⟩ stack = ([], high :: stack)

end DrainHigh

namespace DrainPending

def signature : Signature := singleObservation (Σ _ : ℕ, Σ _ : ℕ, ℕ) (List ℕ) (List ℕ × List ℕ)

def actual : Realization signature :=
  realize signature (fun _ p stack => drain p.2.2 (p.1 :: p.2.1 :: stack)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ([], [])) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀
    {n low high next futureLow : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    (hfutureLow : futureLow ≤ n / 2) {input stack : List ℕ}
    (hmem : futureLow ∈ input)
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)),
    r.readout () ⟨low, high, next⟩ stack = ([low], high :: stack)

end DrainPending

namespace ProcessPending

def arena : DependentFamily.Arena where
  signature := HighIncrease.signature
  Law r := ∀
    {n low high next futureLow : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    (hfutureLow : futureLow ≤ n / 2) {input stack : List ℕ}
    (hmem : futureLow ∈ input)
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)),
    r.readout () ⟨low, high, next, input⟩ stack =
      low :: process input (next :: high :: stack)

end ProcessPending

namespace InitialLows

def signature : Signature := singleObservation (Σ _ : ℕ, List ℕ) (List ℕ) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ p rest => cyclicStackSort (p.2 ++ p.1 :: rest)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [1, 2]) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {n high : ℕ} {pre rest : List ℕ}
    (hpre : ∀ low ∈ pre, low ≤ n / 2) (hhigh : n / 2 < high)
    (houtput : r.readout () ⟨high, pre⟩ rest = target n),
    pre = []

end InitialLows

namespace Gaps

def signature : Signature := singleObservation (ℕ) (List ℕ) (List (Option ℕ))

def actual : Realization signature :=
  realize signature (fun _ m input => gapSlots m input) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {m : ℕ} {input : List ℕ}
    (hgapped : Gapped m input),
    assembleGaps (highEntries m input) (r.readout () m input) = input ∧
      (r.readout () m input).length = (highEntries m input).length ∧
      (r.readout () m input).filterMap id = lowEntries m input

end Gaps

namespace SuccessPerm

def signature : Signature := singleObservation (Unit) (List ℕ) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ input => cyclicStackSort input) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {n : ℕ} {input : List ℕ}
    (houtput : r.readout () () input = target n),
    input.Perm (List.range' 1 n)

end SuccessPerm

namespace SuccessGapped

def rejected : Realization SuccessPerm.signature :=
  realize SuccessPerm.signature (fun _ _ _ => [1, 2]) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := SuccessPerm.signature
  Law r := ∀ {n : ℕ} (hn : 2 ≤ n) {input : List ℕ}
    (houtput : r.readout () () input = target n),
    Gapped (n / 2) input

end SuccessGapped

namespace LowOrder

def signature : Signature := singleObservation (ℕ) (List ℕ) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ (n : ℕ) input => lowEntries (n / 2) input) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [1, 0]) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input)
    (houtput : cyclicStackSort input = target n),
    (r.readout () n input).Pairwise (fun x y => x < y)

end LowOrder

namespace OneNone

def signature : Signature := singleObservation (Unit) (List (Option ℕ)) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ slots => slots.filterMap id) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {slots : List (Option ℕ)} {lows : List ℕ}
    (hfilter : r.readout () () slots = lows)
    (hlen : slots.length = lows.length + 1),
    ∃ omitted < lows.length + 1, slots = insertNone omitted lows

end OneNone

namespace EvenSlots

def signature : Signature := singleObservation (Unit) (ℕ) (List (Option ℕ))

def actual : Realization signature :=
  realize signature (fun _ _ m => candidateSlots m 0 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (m : ℕ),
    r.readout () () m = (List.range' 1 m).map some

end EvenSlots

namespace OddSlots

def signature : Signature := singleObservation (ℕ) (ℕ) (List (Option ℕ))

def actual : Realization signature :=
  realize signature (fun _ (m : ℕ) omitted => candidateSlots omitted 0 (m + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (m omitted : ℕ) (homitted : omitted < m + 1),
    r.readout () m omitted = insertNone omitted (List.range' 1 m)

end OddSlots

namespace CandidateAssembly

def signature : Signature := singleObservation (Σ _ : ℕ, ℕ) (ℕ) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ p omitted => candidate p.1 p.2 omitted) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (m highCount omitted : ℕ),
    r.readout () ⟨m, highCount⟩ omitted =
      assembleGaps (List.range' (m + 1) highCount)
        (candidateSlots omitted 0 highCount)

end CandidateAssembly

namespace FilledSome

def signature : Signature := singleObservation (Unit) (List ℕ) (List (Option ℕ))

def actual : Realization signature :=
  realize signature (fun _ _ lows => lows.map some) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [none, none]) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (lows : List ℕ),
    FilledUntilLast (r.readout () () lows)

end FilledSome

namespace FilledLast

def signature : Signature := singleObservation (Unit) (List ℕ) (List (Option ℕ))

def actual : Realization signature :=
  realize signature (fun _ _ lows => insertNone lows.length lows) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [none, none]) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (lows : List ℕ),
    FilledUntilLast (r.readout () () lows)

end FilledLast

namespace HighOrder

def signature : Signature := singleObservation (ℕ) (List ℕ) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ (n : ℕ) input => highEntries (n / 2) input) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [1, 0]) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input)
    (hfilled : FilledUntilLast (gapSlots (n / 2) input))
    (houtput : cyclicStackSort input = target n),
    (r.readout () n input).Pairwise (fun x y => x < y)

end HighOrder

namespace FinalHighs

def rejected : Realization HighOrder.signature :=
  realize HighOrder.signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := HighOrder.signature
  Law r := ∀ {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input) (hlast : EndsWithLow (n / 2) input)
    (houtput : cyclicStackSort input = target n),
    r.readout () n input = List.range' (n / 2 + 1) (n - n / 2)

end FinalHighs

namespace AssemblyEnds

def signature : Signature := singleObservation (Σ _ : ℕ, List ℕ) (List ℕ) (List ℕ)

def actual : Realization signature :=
  realize signature (fun _ p lows => assembleGaps p.2 (insertNone p.1 lows)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ {m omitted : ℕ} {highs lows : List ℕ}
    (hlen : highs.length = lows.length + 1) (homitted : omitted < lows.length)
    (hlow : ∀ low ∈ lows, low ≤ m),
    EndsWithLow m (r.readout () ⟨omitted, highs⟩ lows)

end AssemblyEnds

namespace OddFibre

def signature : Signature := singleObservation (Unit) (ℕ) (List (List ℕ))

def actual : Realization signature :=
  realize signature (fun _ _ (m : ℕ) => fibre (2 * m + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (m : ℕ) (hm : 0 < m),
    m + 1 ≤ (r.readout () () m).length

end OddFibre

namespace EvenFibre

def signature : Signature := singleObservation (Unit) (ℕ) (List (List ℕ))

def actual : Realization signature :=
  realize signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (m : ℕ) (hm : 0 < m),
    1 ≤ (r.readout () () m).length

end EvenFibre

namespace FibreCount

def arena : DependentFamily.Arena where
  signature := EvenFibre.signature
  Law r := ∀ (m : ℕ) (hm : 2 ≤ m),
    (r.readout () () m).length = 1 ∧ (fibre (2 * m + 1)).length = m + 1

end FibreCount

end D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
