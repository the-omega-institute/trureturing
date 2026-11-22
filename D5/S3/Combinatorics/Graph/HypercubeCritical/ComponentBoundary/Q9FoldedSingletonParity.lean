/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSingletonParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSingletonParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Odd fixed rows force a residual incidence quota for folded singleton completions. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! A finite parity obstruction for completing the singleton sites of a fold. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity

open Finset

/-- If every row has odd degree on the fixed sites and even degree on the
completion, each needs a residual incidence. A cap on the number of rows
incident to each residual site bounds the size of any completion. -/
theorem card_rows_le_residual_quota {Row Site : Type*} [DecidableEq Site]
    (rows : Finset Row) (neighbors : Row → Finset Site) (fixed : Finset Site)
    (cap : ℕ) (chosen : Finset Site)
    (hfixed : fixed ⊆ chosen)
    (hodd : ∀ row ∈ rows, Odd (neighbors row ∩ fixed).card)
    (heven : ∀ row ∈ rows, Even (neighbors row ∩ chosen).card)
    (hcap : ∀ site ∈ chosen \ fixed, (rows.filter fun row => site ∈ neighbors row).card ≤ cap) :
    rows.card ≤ cap * (chosen.card - fixed.card) := by
  let incident (row : Row) (site : Site) : Prop := site ∈ neighbors row
  have hrow (row : Row) (hr : row ∈ rows) :
      1 ≤ ((chosen \ fixed).bipartiteAbove incident row).card := by
    have hsub : neighbors row ∩ fixed ⊆ neighbors row ∩ chosen := by
      intro site hs
      obtain ⟨hn, hf⟩ := mem_inter.mp hs
      exact mem_inter.mpr ⟨hn, hfixed hf⟩
    have hresidual : (neighbors row ∩ chosen) \ (neighbors row ∩ fixed) =
        (chosen \ fixed).bipartiteAbove incident row := by
      ext site
      simp only [mem_sdiff, mem_inter, mem_bipartiteAbove, incident]
      tauto
    have hadd := card_sdiff_add_card_eq_card hsub
    rw [hresidual] at hadd
    have hsum := heven row hr
    rw [← hadd, Nat.even_add'] at hsum
    obtain ⟨k, hk⟩ := hsum.mpr (hodd row hr)
    omega
  have hcount :=
    card_mul_le_card_mul incident (s := rows) (t := chosen \ fixed) hrow hcap
  simpa only [mul_one, card_sdiff_of_subset hfixed,
    Nat.mul_comm (chosen.card - fixed.card) cap] using hcount

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity
