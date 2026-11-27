/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSingletonParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSingletonParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Exact Q8 residual masks exclude parity completions within the Q9 singleton quota. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin

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

/-- Odd singleton sites fixed by the signed shadow and one pass of parity forcing.
The indices 0, 1 and 2 refer to archive cases 2, 3 and 6. -/
def archivedFixed : Fin 3 → Finset (Fin 256)
  | 0 => ([1, 2, 4, 8, 21, 22, 25, 26, 28, 37, 38, 41,
      42, 44, 52, 56, 61, 62, 69, 70, 73, 74, 93, 94,
      109, 110, 145, 146, 148, 152, 161, 162, 164, 168, 193, 194,
      196, 200, 213, 214, 220, 233, 234, 236, 244, 248, 253, 254] : List (Fin 256)).toFinset
  | 1 => ([1, 2, 4, 8, 21, 22, 25, 26, 28, 37, 38, 41,
      42, 44, 52, 56, 61, 62, 69, 70, 73, 74, 93, 94,
      109, 110, 145, 146, 148, 152, 161, 162, 164, 168, 193, 194,
      196, 200, 217, 218, 220, 229, 230, 236, 244, 248, 253, 254] : List (Fin 256)).toFinset
  | _ => ([1, 2, 4, 8, 21, 22, 25, 26, 35, 38, 41, 44,
      55, 59, 61, 62, 67, 70, 73, 76, 87, 91, 93, 94,
      97, 98, 100, 104, 117, 118, 121, 122, 145, 146, 148, 152,
      179, 182, 185, 188, 211, 214, 217, 220, 241, 242, 244, 248] : List (Fin 256)).toFinset

/-- Odd sites outside both the signed shadow and the fixed sites.
The indices 0, 1 and 2 refer to archive cases 2, 3 and 6. -/
def archivedFree : Fin 3 → Finset (Fin 256)
  | 0 => ([7, 11, 13, 14, 31, 47, 55, 59, 67, 79, 91, 103,
      112, 115, 131, 133, 134, 137, 138, 140, 143, 151, 155, 157,
      158, 167, 171, 173, 174, 179, 181, 182, 185, 186, 188, 191,
      199, 203, 205, 206, 211, 217, 218, 223, 227, 229, 230, 239,
      241, 242, 247, 251] : List (Fin 256)).toFinset
  | 1 => ([7, 11, 13, 14, 31, 47, 55, 59, 67, 79, 87, 107,
      112, 115, 131, 133, 134, 137, 138, 140, 143, 151, 155, 157,
      158, 167, 171, 173, 174, 179, 181, 182, 185, 186, 188, 191,
      199, 203, 205, 206, 211, 213, 214, 223, 227, 233, 234, 239,
      241, 242, 247, 251] : List (Fin 256)).toFinset
  | _ => ([7, 11, 13, 14, 28, 31, 42, 47, 56, 69, 79, 84,
      103, 107, 109, 110, 124, 127, 131, 133, 134, 137, 138, 140,
      143, 151, 155, 157, 158, 162, 167, 168, 171, 173, 174, 186,
      191, 193, 196, 199, 203, 205, 206, 213, 223, 224, 227, 229,
      230, 233, 234, 236, 239, 247, 251, 253, 254] : List (Fin 256)).toFinset

private def directions : List (Fin 256) := [1, 2, 4, 8, 16, 32, 64, 128]

/-- The eight transverse neighbours in Q8, with sites encoded by their binary digits. -/
def transverseNeighbors (row : Fin 256) : Finset (Fin 256) :=
  (directions.map (row ^^^ ·)).toFinset

/-- The centres whose binary digits have even sum. -/
def evenCenters : Finset (Fin 256) :=
  univ.filter fun row => (directions.filter fun axis => (row.val &&& axis.val) != 0).length % 2 = 0

private def badRows (case : Fin 3) : Finset (Fin 256) :=
  evenCenters.filter fun row => (transverseNeighbors row ∩ archivedFixed case).card % 2 = 1

private theorem fixed_card : ∀ case : Fin 3, (archivedFixed case).card = 48 := by decide

private theorem badRows_card : ∀ case : Fin 3,
    (badRows case).card = if case = 2 then 32 else 24 := by decide

private def badRowDegree (case : Fin 3) (site : Fin 256) : ℕ :=
  ((badRows case).filter fun row => site ∈ transverseNeighbors row).card

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
private theorem free_incidence_cap : ∀ case : Fin 3,
    (archivedFree case).sup (badRowDegree case) = 4 := by
  decide

/-- With the archived fixed and admissible free odd sites, satisfying every even-centre
parity constraint requires at least 54 singletons in cases 2 and 3 and 56 in case 6. -/
theorem archived_completion_card_lower_bound (case : Fin 3) (chosen : Finset (Fin 256))
    (hfixed : archivedFixed case ⊆ chosen)
    (hfree : chosen \ archivedFixed case ⊆ archivedFree case)
    (heven : ∀ row ∈ evenCenters, Even (transverseNeighbors row ∩ chosen).card) :
    (if case = 2 then 56 else 54) ≤ chosen.card := by
  have hcount := card_rows_le_residual_quota (badRows case) transverseNeighbors
    (archivedFixed case) 4 chosen hfixed
    (fun _ hr => Nat.odd_iff.mpr (mem_filter.mp hr).2)
    (fun row hr => heven row (mem_filter.mp hr).1)
    (fun _ hs => (free_incidence_cap case) ▸ le_sup (f := badRowDegree case) (hfree hs))
  rw [fixed_card case, badRows_card case] at hcount
  split_ifs at hcount ⊢ <;> omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity
