/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodHigherCovers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodHigherCovers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual arbitrary-fiber covers above connected Heawood double quotients. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodAllDoubleCovers

/-! The connected-double-quotient transfer in HEAWOOD_HIGHER_COVER_BOUNDS,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The intermediate graph is an arbitrary actual neighborhood cover,
with no original signing, sheet labels or chosen dissociation set. Deck-group
quotient existence and the character-space threshold are separate obligations. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodHigherCovers
open StarFormingDissociationRefutation
open scoped BigOperators

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (Q : SimpleGraph V) (H : SimpleGraph W)
variable [DecidableRel Q.Adj] [DecidableRel H.Adj]

/-- An arbitrary uniform cover above an actual connected Heawood double
quotient has density at least fifteen twenty-eighths and gap at most nine
one-hundred-ninety-sixths of its order. Zero higher fibers are included. -/
theorem connected_double_quotient (p : V → Fin 14)
    (double : CoverPullback.NeighborhoodCover HeawoodLift.base.Adj Q.Adj p)
    (two : ∀ v, (Finset.univ.filter (fun x => p x=v)).card=2)
    (connected : Q.Preconnected) (q : W → V)
    (higher : CoverPullback.NeighborhoodCover Q.Adj H.Adj q) (k : ℕ)
    (fibers : ∀ v, (Finset.univ.filter (fun x => q x=v)).card=k) :
    15*Fintype.card W ≤ 28*beta H 2 ∧
      196*(SF H 2-beta H 2) ≤ 9*Fintype.card W := by
  classical
  have two' : ∀ v, Nat.card {x // p x=v}=2 := by
    intro v
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using two v
  have parameters := HeawoodAllDoubleCovers.parameters Q p double two'
  have lower : 15 ≤ beta Q 2 := by
    rcases (parameters.2.2 connected).1 with h | h <;> omega
  have order : Fintype.card V=28 := by
    have hc := CoverDensity.card_cover p 2 two
    simpa using hc
  have color : Q.Colorable 2 :=
    CoverDensity.colorable_cover HeawoodLift.base Q p double
      ((SimpleGraph.colorable_congr HeawoodCoverParameters.cyclicIso).mp
        HeawoodParameters.graph_class.1)
  have regular : ∀ v, DegreeCapacity.degree Q v=3 := fun v =>
    (CoverDensity.degree_cover HeawoodLift.base Q p double v).trans
      (HeawoodCoverParameters.base_regular (p v))
  obtain ⟨A,hA,cardA⟩ := beta_attained Q 2
  have density := CoverDensity.certificate_density Q H q higher k fibers A hA
  have gap := CoverDensity.cubic_certificate_gap Q H q higher k fibers color regular A hA
  rw [order,cardA] at density gap
  have density' := (Nat.mul_le_mul_right (Fintype.card W) lower).trans density
  have coefficient : 3*28-5*beta Q 2 ≤ 9 := by omega
  have gap' := gap.trans (Nat.mul_le_mul_right (Fintype.card W) coefficient)
  norm_num at gap'
  exact ⟨density',gap'⟩

end D5.S3.Combinatorics.Graph.StarForming.HeawoodHigherCovers
