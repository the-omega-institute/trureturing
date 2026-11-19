/- GID: D5/S3/Combinatorics/Graph/StarForming/CubicCertificate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CubicCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rewiring outside a selection preserves formation and inclusion-minimality. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularBound

/-!
Proof bodies received from the-omega-institute/subquorum-colorings,
revision 48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/CubicCertificate.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
The arbitrary vertex domain and edge-agreement hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Cubic

open Regular

set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 128

open Subcubic

theorem forms_rewiring {Vertex : Type}
    (original modified : Vertex → Vertex → Prop)
    (selection smaller : Vertex → Prop)
    (hsubset : ∀ vertex, smaller vertex → selection vertex)
    (hagreement : ∀ first second, selection first ∨ selection second →
      (original first second ↔ modified first second))
    (hforms : Forms original smaller) : Forms modified smaller := by
  intro outside houtside
  rcases hforms outside houtside with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · exact Or.inl ⟨first, second, hf, hs, hne,
      (hagreement outside first (Or.inr (hsubset _ hf))).mp ha,
      (hagreement outside second (Or.inr (hsubset _ hs))).mp hb⟩
  · exact Or.inr ⟨center, leaf, hc, hl,
      (hagreement outside center (Or.inr (hsubset _ hc))).mp ha,
      (hagreement center leaf (Or.inl (hsubset _ hc))).mp hb⟩

theorem minimal_rewiring_forward {Vertex : Type}
    (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hagreement : ∀ first second, selection first ∨ selection second →
      (original first second ↔ modified first second))
    (hminimal : Minimal original selection) : Minimal modified selection := by
  refine ⟨forms_rewiring original modified selection selection (fun _ hvertex => hvertex)
    hagreement hminimal.1, ?_⟩
  intro smaller hsubset hexists hforms
  apply hminimal.2 smaller hsubset hexists
  exact forms_rewiring modified original selection smaller hsubset
    (fun first second hselected => (hagreement first second hselected).symm) hforms

theorem minimal_rewiring {Vertex : Type}
    (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hagreement : ∀ first second, selection first ∨ selection second →
      (original first second ↔ modified first second)) :
    Minimal original selection ↔ Minimal modified selection := by
  constructor
  · exact minimal_rewiring_forward original modified selection hagreement
  · exact minimal_rewiring_forward modified original selection
      (fun first second hselected => (hagreement first second hselected).symm)

end D5.S3.Combinatorics.Graph.StarForming.Cubic
