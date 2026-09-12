/- GID: D5/S3/ConceptDynamics/ZfcSupport/UniqueChoice
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcSupport/UniqueChoice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.IsEmpty.Basic]
   utility: none
   digest: Unique existence determines a chosen value and its defining predicate. -/
module

public import Mathlib.Logic.IsEmpty.Basic

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/ExistsUnique.lean, original lines 1-50.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained mathematical commands: upstream lines 11-18.
   Attribution: FormalizedFormalLogic contributors; Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose]
public section

namespace Classical
variable {α : Sort*} {p : α → Prop} {r : α → α → Prop}

noncomputable def choose! (h : ∃! x, p x) : α := choose h.exists

lemma choose!_spec (h : ∃! x, p x) : p (choose! h) := choose_spec h.exists

lemma choose_uniq (h : ∃! x, p x) (hx : p x) : x = choose! h := h.unique hx (choose!_spec h)

@[simp] lemma choose!_eq_iff_right (h : ∃! x, p x) : x = choose! h ↔ p x :=
  ⟨by rintro rfl; exact choose!_spec h, choose_uniq _⟩

end Classical

end
