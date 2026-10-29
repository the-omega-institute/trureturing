/- GID: D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeFiniteMotion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeFiniteMotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One infinite legal finite-configuration trajectory from a scaled lattice set. -/

import D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion
import D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen

namespace D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeFiniteMotion

open IntegerLatticeMotion

/-- Mobility of a finite configuration on a possibly infinite graph. One common
natural-number-indexed trajectory visits every vertex, with one legal move at
each step, general position at all times, and constant cardinality. -/
def IsInfinitelyMobile {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) : Prop :=
  CylinderSevenTen.IsGeneralPosition G S ∧
    ∃ c : ℕ → Finset V, c 0 = S ∧
      (∀ t, CylinderSevenTen.LegalMove G (c t) (c (t + 1))) ∧
      (∀ t, CylinderSevenTen.IsGeneralPosition G (c t)) ∧
      (∀ x, ∃ t, x ∈ c t) ∧
      ∀ t, (c t).card = S.card

/-- Fourfold scaling of a nonempty finite coordinate general-position set
admits one infinite covering trajectory of actual finite lattice configurations.
Its exact cardinality is the cardinality of the original set. -/
theorem scaled_finset_mobile {k : ℕ} (hk : 1 ≤ k) (S : Finset (Vertex k))
    (hne : S.Nonempty)
    (hgp : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a ≠ b → b ≠ c → a ≠ c → ¬ Between a b c) :
    IsInfinitelyMobile (lattice k) (S.image (fun x j => 4 * x j)) ∧
      (S.image (fun x j => 4 * x j)).card = S.card := by
  classical
  obtain ⟨s, p, _, hs, hstart, hinj, hlabelgp, hstep, hcover⟩ :=
    scaled_finset_trace hk S hne hgp
  let c : ℕ → Finset (Vertex k) := fun t => Finset.univ.image (p t)
  have hzero : c 0 = S.image (fun x j => 4 * x j) := by
    rw [← hs, Finset.image_image]
    apply Finset.image_congr
    intro i _
    exact hstart i
  have hcgp : ∀ t, CylinderSevenTen.IsGeneralPosition (lattice k) (c t) := by
    intro t
    exact CylinderSevenTen.labelled_gp (p t) (hlabelgp t)
  have hcmove : ∀ t, CylinderSevenTen.LegalMove (lattice k) (c t) (c (t + 1)) := by
    intro t
    obtain ⟨i, ha, he, _⟩ := hstep t
    exact CylinderSevenTen.labelled_move (p t) (p (t + 1)) i
      (hinj t) (hinj (t + 1)) he ha (hcgp (t + 1))
  have hccard : ∀ t, (c t).card = S.card := by
    intro t
    exact CylinderSevenTen.configuration_card (p t) (hinj t)
  have hscaledcard : (S.image (fun x j => 4 * x j)).card = S.card := by
    rw [← hzero]
    exact hccard 0
  refine ⟨⟨hzero ▸ hcgp 0, c, hzero, hcmove, hcgp, ?_, ?_⟩, hscaledcard⟩
  · intro x
    let i : Fin S.card := ⟨0, Finset.card_pos.mpr hne⟩
    obtain ⟨t, ht⟩ := hcover i x
    exact ⟨t, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ht⟩⟩
  · intro t
    exact (hccard t).trans hscaledcard.symm

end D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeFiniteMotion
