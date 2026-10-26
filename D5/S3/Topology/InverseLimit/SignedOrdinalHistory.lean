/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalHistory
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalHistory
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: A single coherent run over strict well-founded ordinal pasts. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryEvent

/-! Strict-past recursion selects one run before any global semantic readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalHistory

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent
open D5.S3.Topology.Measures

section StrictPastRecursion

universe u v
variable {ι : Type u} [LT ι] (wf : WellFounded ((· < ·) : ι → ι → Prop))
  {Cell : ι → Type v}
  (compatible : ∀ (b a : ι), b < a → Cell b → Cell a → Prop)

private def GoodPast (a : ι) (past : ∀ b, b < a → Option (Cell b)) : Prop :=
  ∃ f : ∀ b, b < a → Cell b,
    (∀ b hb, past b hb = some (f b hb)) ∧
    ∀ b c (hb : b < a) (hc : c < a) (hbc : b < c),
      compatible b c hbc (f b hb) (f c hc)

variable (advance : ∀ a (f : ∀ b, b < a → Cell b),
    (∀ b c (hb : b < a) (hc : c < a) (hbc : b < c),
      compatible b c hbc (f b hb) (f c hc)) →
    Nonempty {x : Cell a // ∀ b hb, compatible b a hb (f b hb) x})

private noncomputable def guardedStep (a : ι)
    (past : ∀ b, b < a → Option (Cell b)) : Option (Cell a) := by
  classical
  exact if h : GoodPast compatible a past then
    some (Classical.choice (advance a (Classical.choose h) (Classical.choose_spec h).2)).1
  else none

private noncomputable def guardedRun : ∀ a, Option (Cell a) :=
  wf.fix (guardedStep compatible advance)

private theorem guardedStep_spec (a : ι) (past : ∀ b, b < a → Option (Cell b))
    (h : GoodPast compatible a past) :
    ∃ x, guardedStep compatible advance a past = some x ∧
      ∀ b hb, ∃ y, past b hb = some y ∧ compatible b a hb y x := by
  classical
  let f := Classical.choose h
  have hf := Classical.choose_spec h
  let x := Classical.choice (advance a f hf.2)
  refine ⟨x.1, ?_, ?_⟩
  · simp only [guardedStep, dif_pos h]
    rfl
  · intro b hb
    exact ⟨f b hb, hf.1 b hb, x.2 b hb⟩

private theorem guardedRun_total (a : ι) :
    ∃ x, guardedRun wf compatible advance a = some x ∧
      ∀ b hb, ∃ y, guardedRun wf compatible advance b = some y ∧
        compatible b a hb y x := by
  classical
  induction a using wf.induction with
  | h a ih =>
    let f : ∀ b, b < a → Cell b := fun b hb => Classical.choose (ih b hb)
    have hf (b : ι) (hb : b < a) := Classical.choose_spec (ih b hb)
    have good : GoodPast compatible a (fun b _ => guardedRun wf compatible advance b) := by
      refine ⟨f, fun b hb => (hf b hb).1, ?_⟩
      intro b c hb hc hbc
      obtain ⟨y, hy, hcoh⟩ := (hf c hc).2 b hbc
      have he : y = f b hb := Option.some.inj (hy.symm.trans (hf b hb).1)
      exact he ▸ hcoh
    obtain ⟨x, hx, hrel⟩ := guardedStep_spec compatible advance a
      (fun b _ => guardedRun wf compatible advance b) good
    refine ⟨x, ?_, hrel⟩
    rw [guardedRun, WellFounded.fix_eq]
    exact hx

end StrictPastRecursion

end D5.S3.Topology.InverseLimit.SignedOrdinalHistory
