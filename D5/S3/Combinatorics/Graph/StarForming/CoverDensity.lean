/- GID: D5/S3/Combinatorics/Graph/StarForming/CoverDensity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CoverDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual finite fibers and dissociation witnesses give higher-cover density and gap bounds. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodCertificates

namespace D5.S3.Combinatorics.Graph.StarForming.CoverDensity
open StarFormingDissociationRefutation
open scoped BigOperators
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (H : SimpleGraph W)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Neighborhood bijections preserve actual finite degrees, without assuming
global surjectivity or positive fiber size. -/
theorem degree_cover (p : W → V)
    (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (v : W) :
    DegreeCapacity.degree H v = DegreeCapacity.degree G (p v) := by
  classical
  apply Finset.card_bij (fun w _ => p w)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      cover.map_edge v w (Finset.mem_filter.mp hw).2⟩
  · intro a ha b hb he
    exact cover.neighbor_injective v a b (Finset.mem_filter.mp ha).2
      (Finset.mem_filter.mp hb).2 he
  · intro a ha
    obtain ⟨w,hw,he⟩ := cover.neighbor_surjective v a (Finset.mem_filter.mp ha).2
    exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,he⟩

/-- The pullback of an actual two-coloring colors the whole lift. -/
theorem colorable_cover (p : W → V)
    (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p)
    (hG : G.Colorable 2) : H.Colorable 2 := by
  obtain ⟨C⟩ := hG
  exact ⟨SimpleGraph.Coloring.mk (fun v => C (p v))
    (fun h => C.valid (cover.map_edge _ _ h))⟩

/-- The whole-order fiber identity includes zero-sheet and empty-base cases. -/
theorem card_cover (p : W → V) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) :
    Fintype.card W = k * Fintype.card V := by
  have h := card_preimage_uniform p k hk (Finset.univ : Finset V)
  simpa using h

/-- Lift an actual dissociation certificate and count its density exactly. -/
theorem certificate_density (p : W → V)
    (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k)
    (A : Finset V) (hA : IsKIndependent G 2 A) :
    A.card * Fintype.card W ≤ Fintype.card V * beta H 2 := by
  have ha : A.card ≤ beta G 2 := Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hA⟩)
  have hb := beta_mul_le G H p cover k hk
  have hl := (Nat.mul_le_mul_left k ha).trans hb
  have hs := Nat.mul_le_mul_left (Fintype.card V) hl
  have ht := card_cover p k hk
  nlinarith

/-- A cubic bipartite lift combines certificate density with the actual sharp
SF compensation theorem. The base certificate itself supplies its coefficient
nonnegativity through the cubic dissociation cut bound. -/
theorem cubic_certificate_gap (p : W → V)
    (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k)
    (hG : G.Colorable 2) (hr : ∀ v, DegreeCapacity.degree G v = 3)
    (A : Finset V) (hA : IsKIndependent G 2 A) :
    (7 * Fintype.card V) * (SF H 2 - beta H 2) ≤
      (3 * Fintype.card V - 5 * A.card) * Fintype.card W := by
  have hhG := colorable_cover G H p cover hG
  have hhr : ∀ v, DegreeCapacity.degree H v = 3 := fun v =>
    (degree_cover G H p cover v).trans (hr (p v))
  have hc := RegularCompensation.sf_regular_bound H hhG 3 hhr
  have hden := certificate_density G H p cover k hk A hA
  have hcut := DegreeCapacity.dissociation_cut_bound G A hA
  have hsum : (∑ v ∈ A, DegreeCapacity.degree G v) = 3 * A.card := by
    simp [hr,Nat.mul_comm]
  have htotal : (∑ v : V, DegreeCapacity.degree G v) = 3 * Fintype.card V := by
    simp [hr,Nat.mul_comm]
  rw [hsum,htotal] at hcut
  have hbase : 5 * A.card ≤ 3 * Fintype.card V := by omega
  have hbase' := Nat.sub_add_cancel hbase
  have hgap := Nat.sub_add_cancel (beta_le_sf H)
  have hscaled := Nat.mul_le_mul_left (Fintype.card V) hc
  nlinarith

/-- Every uniform cover above either original S or J two-lift has the stronger
four-sevenths density and one-forty-ninth gap bounds. No deck-group or switching
classification is assumed or claimed. -/
theorem scalar_cover_bound {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28)
    (cover : CoverPullback.NeighborhoodCover
      HeawoodCertificates.scalarGraph.Adj H.Adj p) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) :
    4 * Fintype.card U ≤ 7 * beta H 2 ∧
      49 * (SF H 2 - beta H 2) ≤ Fintype.card U := by
  have hd := certificate_density HeawoodCertificates.scalarGraph H p cover k hk
    HeawoodCertificates.scalarSet HeawoodCertificates.scalar_selection.1
  have hg := cubic_certificate_gap HeawoodCertificates.scalarGraph H p cover k hk
    HeawoodCertificates.scalar_class.1 HeawoodCertificates.scalar_class.2
    HeawoodCertificates.scalarSet HeawoodCertificates.scalar_selection.1
  rw [HeawoodCertificates.scalar_selection.2] at hd hg
  norm_num at hd hg
  constructor <;> omega

theorem jordan_cover_bound {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28)
    (cover : CoverPullback.NeighborhoodCover
      HeawoodCertificates.jordanGraph.Adj H.Adj p) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) :
    4 * Fintype.card U ≤ 7 * beta H 2 ∧
      49 * (SF H 2 - beta H 2) ≤ Fintype.card U := by
  have hd := certificate_density HeawoodCertificates.jordanGraph H p cover k hk
    HeawoodCertificates.jordanSet HeawoodCertificates.jordan_selection.1
  have hg := cubic_certificate_gap HeawoodCertificates.jordanGraph H p cover k hk
    HeawoodCertificates.jordan_class.1 HeawoodCertificates.jordan_class.2
    HeawoodCertificates.jordanSet HeawoodCertificates.jordan_selection.1
  rw [HeawoodCertificates.jordan_selection.2] at hd hg
  norm_num at hd hg
  constructor <;> omega

end D5.S3.Combinatorics.Graph.StarForming.CoverDensity
