/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion.claim
   digest: Exclude actual symmetric twenty-two-point induced finite-cube slices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricAAExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricBBExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedExclusion
import Batteries.Tactic.OpenPrivate

/-! Complete symmetric twenty-two-point exclusion for an actual induced finite
cube embedding. The high-side profiles are derived from the original graph. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSliceExclusion

open SimpleGraph GirthSliceCounting

attribute [local instance] Classical.propDecidable

open private symmetric_high_profiles from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles
open private actual_aa_excluded from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricAAExclusion
open private actual_ab_excluded actual_ba_excluded from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedExclusion
open private actual_bb_cube_excluded from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricBBExclusion

/-- No graph satisfying the actual symmetric eleven/eleven and four/four slice
conditions admits an induced embedding in any finite Boolean hypercube. -/
private theorem actual_symmetric_cube_excluded
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (n : ℕ) (q : V → (Fin n → Bool)) (hq : Function.Injective q)
    (hqe : ∀ x y, G.Adj x y ↔ (Hypercube.hypercube n).Adj (q x) (q y)) : False := by
  obtain ⟨_, _, hLp, hRp, _⟩ :=
    symmetric_high_profiles hpart hdeg hlow hg hL hR hL2 hR2
  rcases hLp.2.1 with hLA | hLB
  · rcases hRp.2.1 with hRA | hRB
    · exact actual_aa_excluded hpart hdeg hlow hg hL hR hL2 hR2 hLA hRA
    · exact actual_ab_excluded hpart hdeg hlow hg hL hR hL2 hR2 hLA hRB
  · rcases hRp.2.1 with hRA | hRB
    · exact actual_ba_excluded hpart hdeg hlow hg hL hR hL2 hR2 hLB hRA
    · exact actual_bb_cube_excluded hpart hdeg hlow hg hL hR hL2 hR2 hLB hRB n q hq hqe

/-- A genuine induced finite-cube slice with the original symmetric parameters. -/
def claim : Prop :=
  ∃ (n : ℕ) (S : Finset (Fin n → Bool)),
    ∃ L R : Finset {x : Fin n → Bool // x ∈ S},
      let G := (Hypercube.hypercube n).induce {x | x ∈ S}
      G.IsBipartiteWith (L : Set {x : Fin n → Bool // x ∈ S})
        (R : Set {x : Fin n → Bool // x ∈ S}) ∧
      (∀ x, G.degree x = 2 ∨ G.degree x = 3) ∧
      (∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) ∧
      (8 : ℕ∞) ≤ G.egirth ∧
      L.card = 11 ∧ R.card = 11 ∧
      (degreeTwo G L).card = 4 ∧ (degreeTwo G R).card = 4

/-- No finite cube contains an induced slice with parameters (11,11;4,4). -/
theorem result : ¬ claim := by
  rintro ⟨n, S, L, R, hpart, hdeg, hlow, hg, hL, hR, hL2, hR2⟩
  exact actual_symmetric_cube_excluded hpart hdeg hlow hg hL hR hL2 hR2
    n Subtype.val Subtype.val_injective (fun _ _ => Iff.rfl)

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSliceExclusion
