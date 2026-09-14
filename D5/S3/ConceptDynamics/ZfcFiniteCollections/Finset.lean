/- GID: D5/S3/ConceptDynamics/ZfcFiniteCollections/Finset
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcFiniteCollections/Finset
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fin.VecNotation]
   utility: none
   digest: Vorspiel.Finset.Basic for first-order set definition elimination. -/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Set.Finite.Range

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/Finset/Basic.lean, original lines 1-88.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose]
public section

namespace Finset

variable {α : Type*} {a b : α} {s : Finset α}

/-
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539367015
-/

section

end

lemma biUnion_eq_empty [DecidableEq β] {s : Finset α} {f : α → Finset β} :
    s.biUnion f = ∅ ↔ ∀ i ∈ s, f i = ∅ := by
  constructor
  · intro h a ha; ext b
    have := by simpa using congrFun (congrArg Membership.mem h) b
    simpa using this a ha
  · intro h; ext b
    suffices ∀ x ∈ s, b ∉ f x by simpa
    intro a ha; simpa using congrFun (congrArg Membership.mem (h a ha)) b

end Finset

end
