/- GID: D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Uniform covers above Heawood lifts in which both optional matching lines occur. -/

import D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodMatching

/-! Density and gap bounds for covers above the two-extra-line gain form. -/

namespace D5.S3.Combinatorics.Graph.StarForming.CoverDensity

open StarFormingDissociationRefutation HeawoodSwitching HeawoodLift
open D5.S3.Combinatorics.Graph.StarForming.Families

/-- An actual uniform cover of a double lift in the two-extra-line gain form has
density at least four sevenths and gap at most one forty-ninth of its order.
The quotient can have any vertex labels, and the uniform fiber size can be zero. -/
theorem both_lines_cover_bound {V W : Type} [Fintype W]
    [DecidableEq V] [DecidableEq W] (Q : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj] (s : Signing) (iso : Q ≃g graph s)
    (g : Matˣ) (a b c : F2)
    (gain_eq : phi s = (g : Mat) * HeawoodMatching.gain 0 1 a b c * (↑g⁻¹ : Mat))
    (p : W → V) (cover : CoverPullback.NeighborhoodCover Q.Adj H.Adj p)
    (k : ℕ) (fibers : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) :
    4 * Fintype.card W ≤ 7 * beta H 2 ∧
      49 * (SF H 2 - beta H 2) ≤ Fintype.card W := by
  classical
  letI : Fintype V := Fintype.ofEquiv _ iso.toEquiv.symm
  have hb := HeawoodMatching.beta_bounds s g 0 1 a b c gain_eq
  have exactBeta : beta Q 2 = 16 := by
    rw [(Isomorphism.parameters iso).1]
    simp at hb
    omega
  have order : Fintype.card V = 28 := by
    rw [Fintype.card_congr iso.toEquiv]
    simp [Fintype.card_prod, ZMod.card]
  have color : Q.Colorable 2 :=
    (SimpleGraph.colorable_congr iso).mpr <|
      colorable_cover base (graph s) Prod.fst (BinaryLift.cover base (voltage s))
        ((SimpleGraph.colorable_congr HeawoodCoverParameters.cyclicIso).mp
          HeawoodParameters.graph_class.1)
  have regular : ∀ v, DegreeCapacity.degree Q v = 3 := by
    intro v
    have liftRegular := (degree_cover base (graph s) Prod.fst
      (BinaryLift.cover base (voltage s)) (iso v)).trans
      (HeawoodCoverParameters.base_regular (iso v).1)
    have degree_eq := iso.degree_eq v
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] at degree_eq
    simp only [DegreeCapacity.degree] at liftRegular ⊢
    exact degree_eq.symm.trans liftRegular
  obtain ⟨A, hA, cardA⟩ := beta_attained Q 2
  rw [exactBeta] at cardA
  have density := certificate_density Q H p cover k fibers A hA
  have gap := cubic_certificate_gap Q H p cover k fibers color regular A hA
  rw [order, cardA] at density gap
  norm_num at density gap
  constructor <;> omega

end D5.S3.Combinatorics.Graph.StarForming.CoverDensity
