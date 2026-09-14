/- GID: D5/S3/ConceptDynamics/ZfcLanguageSupport/Empty
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcLanguageSupport/Empty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Basic]
   utility: none
   digest: Every map from Empty equals its eliminator. -/
module

public import Mathlib.Data.Fintype.Basic

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/Empty.lean, original lines 1-13.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained mathematical command: upstream line 9.
   Attribution: FormalizedFormalLogic contributors; Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace Empty

lemma eq_elim {α : Sort u} (f : Empty → α) : f = elim := funext (by rintro ⟨⟩)

end Empty

end
