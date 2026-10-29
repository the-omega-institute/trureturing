/- GID: D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMobile
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The attained mobile general position number of every positive dimensional integer lattice. -/

import D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeStatic
import D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeFiniteMotion

namespace D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMobile

open IntegerLatticeMotion

/-- One common infinite sequence of finite occupied sets, with a legal
single-robot move at every step and a finite visit time for every lattice vertex.
No cardinality invariant is assumed in this source mobility predicate. -/
def IsMobile {k : ℕ} (S : Finset (Vertex k)) : Prop :=
  CylinderSevenTen.IsGeneralPosition (lattice k) S ∧
    ∃ c : ℕ → Finset (Vertex k), c 0 = S ∧
      (∀ t, CylinderSevenTen.LegalMove (lattice k) (c t) (c (t + 1))) ∧
      (∀ t, CylinderSevenTen.IsGeneralPosition (lattice k) (c t)) ∧
      ∀ x, ∃ t, x ∈ c t

/-- The exact attained mobile general-position bound on every positive
dimensional signed-unit integer lattice. -/
theorem result (k : ℕ) (hk : 1 ≤ k) :
    (∀ S : Finset (Fin k → ℤ), IsMobile S → S.card ≤ 2 ^ (2 ^ (k - 1))) ∧
      ∃ S : Finset (Fin k → ℤ), IsMobile S ∧ S.card = 2 ^ (2 ^ (k - 1)) := by
  classical
  cases k with
  | zero => omega
  | succ n =>
    constructor
    · intro S hS
      have hg : IntegerLatticeStatic.CoordinateGP S := by
        intro x hx y hy z hz hxy hyz hxz hbetween
        exact hS.1 x hx y hy z hz hxy hyz hxz
          ((between_iff_geodesic x y z).mp hbetween)
      simpa only [Nat.add_sub_cancel] using IntegerLatticeStatic.card_le hg
    · obtain ⟨S, hg, hcard, hne, _, _⟩ := IntegerLatticeStatic.exists_attaining n
      obtain ⟨hmobile, hscaledcard⟩ :=
        IntegerLatticeFiniteMotion.scaled_finset_mobile (by omega) S hne hg
      obtain ⟨hinitial, c, hzero, hstep, hgp, hcover, _⟩ := hmobile
      refine ⟨S.image (fun x j => 4 * x j),
        ⟨hinitial, c, hzero, hstep, hgp, hcover⟩, ?_⟩
      simpa only [Nat.add_sub_cancel] using hscaledcard.trans hcard

end D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMobile
