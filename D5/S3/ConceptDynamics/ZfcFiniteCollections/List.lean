/- GID: D5/S3/ConceptDynamics/ZfcFiniteCollections/List
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcFiniteCollections/List
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Sigma]
   utility: none
   digest: Vorspiel.List.Basic for first-order set definition elimination. -/
module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.GetD
public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Matrix

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/List/Basic.lean, original lines 1-300.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose]
public section

namespace List

variable {l : List α}

variable {α : Type u} {β: Type v}

section finset

variable [DecidableEq α] [DecidableEq β]

end finset

section sup

variable [SemilatticeSup α] [OrderBot α]

end sup

variable {m : Type _ → Type _} {α : Type _} {β : Type _} [Monad m]

section remove

variable [DecidableEq α]

end remove

@[elab_as_elim]
lemma induction_with_singleton
  {motive : List F → Prop}
  (hnil : motive [])
  (hsingle : ∀ a, motive [a])
  (hcons : ∀ a as, as ≠ [] → motive as → motive (a :: as)) : ∀ as, motive as := by
  intro as;
  induction as with
  | nil => exact hnil;
  | cons a as ih => cases as with
    | nil => exact hsingle a;
    | cons b bs => exact hcons a (b :: bs) (by simp) ih;

section suffix

end suffix

namespace Vector

variable {α : Type*}

end Vector

end List

end
