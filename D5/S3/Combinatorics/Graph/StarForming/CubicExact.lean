/- GID: D5/S3/Combinatorics/Graph/StarForming/CubicExact
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CubicExact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact finite local certificates and ambient graph deletion proofs. -/

import D5.S3.Combinatorics.Graph.StarForming.CubicDense
import D5.S3.Combinatorics.Graph.StarForming.SubcubicExact

/-!
Proof bodies received from the-omega-institute/subquorum-colorings,
revision 48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/CubicExact.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
The local certificate domains and original embedding hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Cubic

open Regular

open Subcubic

theorem lift_broken_star {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (embedding : Fin 14 → Vertex) (mask : Fin 16384)
    (hinjective : ∀ first second, embedding first = embedding second → first = second)
    (hsound : ∀ first second, BrokenAdj first second → adjacency (embedding first) (embedding second))
    (hselection : ∀ vertex, selection (embedding vertex) ↔ chosen mask.val vertex = true)
    (deleted outside : Fin 14)
    (hstar : TwoAt BrokenAdj (fun vertex => chosen mask.val vertex = true ∧ vertex ≠ deleted) outside) :
    TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ embedding deleted) (embedding outside) := by
  have hkeep : ∀ vertex, chosen mask.val vertex = true ∧ vertex ≠ deleted →
      selection (embedding vertex) ∧ embedding vertex ≠ embedding deleted := by
    intro vertex hvertex
    exact ⟨(hselection vertex).mpr hvertex.1, fun hequal => hvertex.2 (hinjective _ _ hequal)⟩
  rcases hstar with ⟨first, second, hf, hs, hne, ha, hb⟩ | ⟨center, leaf, hc, hl, ha, hb⟩
  · exact Or.inl ⟨embedding first, embedding second, hkeep first hf, hkeep second hs,
      fun hequal => hne (hinjective _ _ hequal), hsound _ _ ha, hsound _ _ hb⟩
  · exact Or.inr ⟨embedding center, embedding leaf, hkeep center hc, hkeep leaf hl,
      hsound _ _ ha, hsound _ _ hb⟩

theorem ambient_heawood_cap {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (embedding : Fin 14 → Vertex) (mask : Fin 16384)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (hinjective : ∀ first second, embedding first = embedding second → first = second)
    (hsound : ∀ first second, BrokenAdj first second → adjacency (embedding first) (embedding second))
    (hselection : ∀ vertex, selection (embedding vertex) ↔ chosen mask.val vertex = true)
    (hnonport : ∀ vertex, vertex ≠ 0 → vertex ≠ 8 → ∀ outside,
      adjacency (embedding vertex) outside → ∃ other, outside = embedding other ∧ BrokenAdj vertex other)
    (hminimal : Minimal adjacency selection) : selectedCard mask.val ≤ 8 := by
  classical
  by_cases hcap : selectedCard mask.val ≤ 8
  · exact hcap
  apply False.elim
  obtain ⟨deleted, hselected, hports, hnew, hreplace, hadjacent⟩ :=
    dense_certificate mask (by omega)
  have hglobal : Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ embedding deleted) := by
    apply supported_deletion adjacency selection (embedding deleted) hminimal.1
    · exact lift_broken_star adjacency selection embedding mask hinjective hsound hselection
        deleted deleted hnew
    · intro outside houtside hedge
      obtain ⟨localOutside, rfl, hlocal⟩ :=
        hnonport deleted hports.1 hports.2 outside (hsymmetric _ _ hedge)
      apply lift_broken_star adjacency selection embedding mask hinjective hsound hselection
        deleted localOutside
      exact hadjacent localOutside (fun hchosen => houtside ((hselection _).mpr hchosen)) hlocal
    · intro center hc hedge
      obtain ⟨localCenter, rfl, hlocal⟩ :=
        hnonport deleted hports.1 hports.2 center (hsymmetric _ _ hedge)
      obtain ⟨leaf, hl, hleaf⟩ := hreplace localCenter ((hselection _).mp hc) hlocal
      exact ⟨embedding leaf, ⟨(hselection _).mpr hl.1,
        fun hequal => hl.2 (hinjective _ _ hequal)⟩, hsound _ _ hleaf⟩
  exact hminimal.2 _ (fun _ hvertex => hvertex.1)
    ⟨embedding deleted, (hselection _).mpr hselected, fun hvertex => hvertex.2 rfl⟩ hglobal


end D5.S3.Combinatorics.Graph.StarForming.Cubic
