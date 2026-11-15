/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth,
     mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Joint endpoint bounds for actual one-step and nonbacktracking three-step paths.
-/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

open scoped BigOperators Classical
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A degree-two slice of a finite set of vertices. -/
def degreeTwo (G : SimpleGraph V) (S : Finset V) : Finset V :=
  S.filter (fun v => G.degree v = 2)

/-- A degree-three slice of a finite set of vertices. -/
def degreeThree (G : SimpleGraph V) (S : Finset V) : Finset V :=
  S.filter (fun v => G.degree v = 3)

/-- Explicit triples `(root, first, second, endpoint)` satisfying the two actual
nonbacktracking conditions.  No endpoint or layer cardinality is assumed here. -/
structure ThreeStep (V : Type*) where
  root : V
  first : V
  second : V
  endpoint : V
  deriving DecidableEq, Fintype

private def threePaths (G : SimpleGraph V) (roots : Finset V) : Finset (ThreeStep V) :=
  (Finset.univ : Finset (ThreeStep V)).filter fun q =>
    q.root ∈ roots ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
      G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint

/-- The actual length-one path family, retaining the root label. -/
private def onePaths (G : SimpleGraph V) (roots : Finset V) : Finset (Σ a : V, V) :=
  roots.sigma (fun a => G.neighborFinset a)

private def oneEndpoint (q : Σ a : V, V) : V × V := (q.1, q.2)

private def oneWalk {a b : V} (hab : G.Adj a b) : G.Walk a b :=
  Walk.cons hab Walk.nil

private def threeWalk {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) : G.Walk a d :=
  Walk.cons hab (Walk.cons hbc (Walk.cons hcd Walk.nil))

private lemma oneWalk_isPath {a b : V} (hab : G.Adj a b) :
    (oneWalk hab).IsPath := by
  simp [oneWalk, Walk.cons_isPath_iff, G.ne_of_adj hab]

private lemma threeWalk_isPath
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {a b c d : V} (ha : a ∈ L)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : a ≠ c) (hbd : b ≠ d) :
    (threeWalk hab hbc hcd).IsPath := by
  have hb : b ∈ (R : Set V) := hpart.mem_of_mem_adj (show a ∈ (L : Set V) from ha) hab
  have hc : c ∈ (L : Set V) := hpart.mem_of_mem_adj' (show b ∈ (R : Set V) from hb) hbc.symm
  have hd : d ∈ (R : Set V) := hpart.mem_of_mem_adj (show c ∈ (L : Set V) from hc) hcd
  have had : a ≠ d := by
    intro had
    subst d
    exact Set.disjoint_left.mp hpart.disjoint (show a ∈ (L : Set V) from ha) hd
  simp [threeWalk, Walk.cons_isPath_iff, G.ne_of_adj hab, G.ne_of_adj hbc,
    G.ne_of_adj hcd, hac, hbd, had]

private lemma girth_forbids_two_paths
    (hg : (8 : ℕ∞) ≤ G.egirth) {u w : V} {p q : G.Walk u w}
    (hp : p.IsPath) (hq : q.IsPath) (hpq : p ≠ q)
    (hlen : p.length + q.length ≤ 6) : False := by
  obtain ⟨z, _, _, c, hc, hcl⟩ := hp.exists_isCycle_length_le_add_of_ne hq hpq
  have h8 : 8 ≤ c.length := by
    exact ENat.natCast_le_natCast.mp (hg.trans hc.egirth_le_length)
  omega

/-- Any two distinct simple paths of lengths at most three with common endpoints
would create a cycle of length at most six.  This is the exact girth input used by
all endpoint disjointness arguments below. -/
private lemma endpoint_eq_of_short_paths
    (hg : (8 : ℕ∞) ≤ G.egirth) {u w : V}
    {p q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length ≤ 6) : p = q := by
  by_contra hpq
  exact girth_forbids_two_paths hg hp hq hpq hlen

private lemma three_walk_endpoint_injective
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {a b c d a' b' c' d' : V}
    (ha : a ∈ L) (ha' : a' ∈ L)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hab' : G.Adj a' b') (hbc' : G.Adj b' c') (hcd' : G.Adj c' d')
    (hac : a ≠ c) (hbd : b ≠ d) (hac' : a' ≠ c') (hbd' : b' ≠ d')
    (hend : a = a' ∧ d = d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  rcases hend with ⟨rfl, rfl⟩
  have hp : (threeWalk hab hbc hcd).IsPath :=
    threeWalk_isPath hpart ha hab hbc hcd hac hbd
  have hq : (threeWalk hab' hbc' hcd').IsPath :=
    threeWalk_isPath hpart ha' hab' hbc' hcd' hac' hbd'
  have heq : threeWalk hab hbc hcd = threeWalk hab' hbc' hcd' :=
    endpoint_eq_of_short_paths hg hp hq (by simp [threeWalk])
  have hs := congrArg Walk.support heq
  have hxyz : [a, b, c, d] = [a, b', c', d] := by simpa [threeWalk] using hs
  simpa using hxyz

private lemma one_three_cross_impossible
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {a b a' b' c' d' : V}
    (ha : a ∈ L) (ha' : a' ∈ L)
    (hab : G.Adj a b)
    (hab' : G.Adj a' b') (hb'c' : G.Adj b' c') (hc'd' : G.Adj c' d')
    (ha'c' : a' ≠ c') (hb'd' : b' ≠ d')
    (hend : a = a' ∧ b = d') : False := by
  rcases hend with ⟨rfl, rfl⟩
  have hp : (oneWalk hab).IsPath := oneWalk_isPath hab
  have hq : (threeWalk hab' hb'c' hc'd').IsPath :=
    threeWalk_isPath hpart ha' hab' hb'c' hc'd' ha'c' hb'd'
  have heq : oneWalk hab = threeWalk hab' hb'c' hc'd' :=
    endpoint_eq_of_short_paths hg hp hq (by simp [oneWalk, threeWalk])
  have hlen := congrArg Walk.length heq
  simp [oneWalk, threeWalk] at hlen

/-- Actual nonbacktracking three-step paths are determined by their root and endpoint. -/
private theorem three_endpoint_injective
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    {q q' : ThreeStep V}
    (hq : q.root ∈ L ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
      G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint)
    (hq' : q'.root ∈ L ∧ G.Adj q'.root q'.first ∧ G.Adj q'.first q'.second ∧
      G.Adj q'.second q'.endpoint ∧ q'.root ≠ q'.second ∧ q'.first ≠ q'.endpoint)
    (hend : (q.root, q.endpoint) = (q'.root, q'.endpoint)) : q = q' := by
  rcases q with ⟨a, b, c, d⟩
  rcases q' with ⟨a', b', c', d'⟩
  simp only at hq hq' hend ⊢
  rcases hq with ⟨ha, hab, hbc, hcd, hac, hbd⟩
  rcases hq' with ⟨ha', hab', hbc', hcd', hac', hbd'⟩
  obtain ⟨haa, hbb, hcc, hdd⟩ :=
    three_walk_endpoint_injective hpart hg ha ha' hab hbc hcd hab' hbc' hcd' hac hbd hac' hbd'
      (by simpa using hend)
  subst a'; subst b'; subst c'; subst d'
  rfl

/-- The finite endpoint image of actual length-three paths is contained in the
root-by-right-side rectangle. -/
private lemma three_endpoint_mem_rectangle
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    {q : ThreeStep V}
    (hq : q.root ∈ L ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
      G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint) :
    (q.root, q.endpoint) ∈ L.product R := by
  rcases hq with ⟨ha, hab, hbc, hcd, hac, hbd⟩
  have hb : q.first ∈ (R : Set V) := hpart.mem_of_mem_adj (show q.root ∈ (L : Set V) from ha) hab
  have hc : q.second ∈ (L : Set V) := hpart.mem_of_mem_adj'
    (show q.first ∈ (R : Set V) from hb) hbc.symm
  have hd : q.endpoint ∈ (R : Set V) := hpart.mem_of_mem_adj
    (show q.second ∈ (L : Set V) from hc) hcd
  simp [ha, hd]

private def endpoint (q : ThreeStep V) : V × V := (q.root, q.endpoint)

/-- Retaining the root makes the length-one path count an exact degree sum. -/
theorem one_paths_card_eq_three_mul
    (roots : Finset V) (hdeg : ∀ v ∈ roots, G.degree v = 3) :
    (onePaths G roots).card = 3 * roots.card := by
  rw [Finset.card_sigma]
  calc
    (∑ a ∈ roots, (G.neighborFinset a).card) = ∑ a ∈ roots, G.degree a := by
      simp only [SimpleGraph.card_neighborFinset_eq_degree]
    _ = ∑ _a ∈ roots, 3 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hdeg a ha
    _ = 3 * roots.card := by simp [Nat.mul_comm]

/-- The joint endpoint map of the actual one-step and nonbacktracking three-step
families is injective: equal endpoints in the mixed case would give a short cycle. -/
private lemma endpoint_images_disjoint
    {L R : Finset V} (roots : Finset V) (hroots : roots ⊆ L)
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    Disjoint ((onePaths G roots).image oneEndpoint)
      ((threePaths G roots).image endpoint) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨q, hq, hqz⟩ := Finset.mem_image.mp hz
  obtain ⟨q', hq', hq'z⟩ := Finset.mem_image.mp hz'
  have hq0 : q.1 ∈ roots ∧ G.Adj q.1 q.2 := by
    simpa [onePaths] using hq
  have hq'0 : q'.root ∈ roots ∧ G.Adj q'.root q'.first ∧
      G.Adj q'.first q'.second ∧ G.Adj q'.second q'.endpoint ∧
      q'.root ≠ q'.second ∧ q'.first ≠ q'.endpoint := by
    simpa [threePaths] using hq'
  rcases hq'0 with ⟨hr, h01, h12, h23, h02, h13⟩
  exact one_three_cross_impossible hpart hg (hroots hq0.1) (hroots hr)
    hq0.2 h01 h12 h23 h02 h13 (by
      have he : oneEndpoint q = endpoint q' := hqz.trans hq'z.symm
      exact Prod.mk.inj he)

/-- Actual one-step and three-step path counts fit jointly in the root-by-right
rectangle.  All endpoint uniqueness is derived from girth, not assumed. -/
theorem one_three_paths_card_le_rectangle
    {L R : Finset V} (roots : Finset V) (hroots : roots ⊆ L)
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    (onePaths G roots).card + (threePaths G roots).card ≤ roots.card * R.card := by
  have hone : Function.Injective (oneEndpoint : (Σ a : V, V) → V × V) := by
    intro x y h
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  have hthree : Set.InjOn endpoint (↑(threePaths G roots) : Set (ThreeStep V)) := by
    intro q hq q' hq' he
    have hp : q.root ∈ roots ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
        G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
      simpa [threePaths] using hq
    have hp' : q'.root ∈ roots ∧ G.Adj q'.root q'.first ∧ G.Adj q'.first q'.second ∧
        G.Adj q'.second q'.endpoint ∧ q'.root ≠ q'.second ∧ q'.first ≠ q'.endpoint := by
      simpa [threePaths] using hq'
    exact three_endpoint_injective hpart hg ⟨hroots hp.1, hp.2⟩
      ⟨hroots hp'.1, hp'.2⟩ he
  have hsub : ((onePaths G roots).image oneEndpoint) ∪
      ((threePaths G roots).image endpoint) ⊆ roots.product R := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hqr : q.1 ∈ roots ∧ G.Adj q.1 q.2 := by
        simpa [onePaths] using hq
      have hR := hpart.mem_of_mem_adj (hroots hqr.1) hqr.2
      exact Finset.mem_product.mpr ⟨hqr.1, hR⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hp : q.root ∈ roots ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
          G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
        simpa [threePaths] using hq
      have hrect := three_endpoint_mem_rectangle hpart ⟨hroots hp.1, hp.2⟩
      exact Finset.mem_product.mpr ⟨hp.1, (Finset.mem_product.mp hrect).2⟩
  calc
    (onePaths G roots).card + (threePaths G roots).card =
        ((onePaths G roots).image oneEndpoint).card +
          ((threePaths G roots).image endpoint).card := by
      rw [Finset.card_image_of_injective _ hone, Finset.card_image_of_injOn hthree]
    _ = (((onePaths G roots).image oneEndpoint) ∪
          ((threePaths G roots).image endpoint)).card :=
      (Finset.card_union_of_disjoint (endpoint_images_disjoint roots hroots hpart hg)).symm
    _ ≤ (roots.product R).card := Finset.card_le_card hsub
    _ = roots.card * R.card := Finset.card_product roots R

/-- The geometric half of the cubic slice estimate, using actual path families. -/
theorem high_root_three_paths_bound
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    3 * (degreeThree G L).card + (threePaths G (degreeThree G L)).card ≤
      (degreeThree G L).card * R.card := by
  have h := one_three_paths_card_le_rectangle (degreeThree G L)
    (Finset.filter_subset _ _) hpart hg
  rw [one_paths_card_eq_three_mul _ (by
    intro v hv
    exact (Finset.mem_filter.mp hv).2)] at h
  exact h

end D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
