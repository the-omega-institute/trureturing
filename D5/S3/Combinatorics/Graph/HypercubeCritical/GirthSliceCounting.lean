/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth, mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Cubic bipartite slice bounds from actual short-path injection and weighted incidence counting. -/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Degree-two/degree-three bipartite graphs of extended girth at least eight
satisfy both cubic slice inequalities by actual path and incidence counting. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

open scoped BigOperators Classical
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

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
  exact Finset.mem_product.mpr ⟨ha, hd⟩

private def endpoint (q : ThreeStep V) : V × V := (q.root, q.endpoint)

/-- Retaining the root makes the length-one path count an exact degree sum. -/
private theorem one_paths_card_eq_three_mul
    (roots : Finset V) (hdeg : ∀ v ∈ roots, G.degree v = 3) :
    (onePaths G roots).card = 3 * roots.card := by
  rw [onePaths, Finset.card_sigma]
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
private theorem one_three_paths_card_le_rectangle
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
private theorem high_root_three_paths_bound
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

private lemma degree_parts_disjoint (S : Finset V) :
    Disjoint (degreeTwo G S) (degreeThree G S) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have h2 := (Finset.mem_filter.mp hv).2
  have h3 := (Finset.mem_filter.mp hw).2
  omega

private lemma degree_parts_union
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (S : Finset V) :
    degreeTwo G S ∪ degreeThree G S = S := by
  ext v
  simp only [degreeTwo, degreeThree, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
  · intro hv
    rcases hdeg v with h2 | h3
    · exact Or.inl ⟨hv, h2⟩
    · exact Or.inr ⟨hv, h3⟩

private lemma sum_degree_parts
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (S : Finset V) (f : V → ℕ) :
    (∑ v ∈ S, f v) =
      (∑ v ∈ degreeTwo G S, f v) + ∑ v ∈ degreeThree G S, f v := by
  calc
    (∑ v ∈ S, f v) = ∑ v ∈ degreeTwo G S ∪ degreeThree G S, f v := by
      rw [degree_parts_union hdeg]
    _ = _ := Finset.sum_union (degree_parts_disjoint S)

private def forwardWeight (G : SimpleGraph V) (y w : V) : ℕ :=
  ((G.neighborFinset w).erase y).card

private lemma forwardWeight_add_one {y w : V} (hw : w ∈ G.neighborFinset y) :
    forwardWeight G y w + 1 = G.degree w := by
  have hy : y ∈ G.neighborFinset w := (G.mem_neighborFinset _ _).mpr
    ((G.mem_neighborFinset _ _).mp hw).symm
  simpa [forwardWeight, SimpleGraph.card_neighborFinset_eq_degree] using
    (Finset.card_erase_add_one hy)

private lemma neighbor_weight_sum
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (y : V) :
    (∑ w ∈ G.neighborFinset y, forwardWeight G y w) =
      (degreeTwo G (G.neighborFinset y)).card +
        2 * (degreeThree G (G.neighborFinset y)).card := by
  have hlow : (∑ w ∈ degreeTwo G (G.neighborFinset y), forwardWeight G y w) =
      (degreeTwo G (G.neighborFinset y)).card := by
    calc
      _ = ∑ _w ∈ degreeTwo G (G.neighborFinset y), 1 := by
        apply Finset.sum_congr rfl
        intro w hw
        have hm := Finset.mem_filter.mp hw
        have hc := forwardWeight_add_one hm.1
        omega
      _ = _ := by simp
  have hhigh : (∑ w ∈ degreeThree G (G.neighborFinset y), forwardWeight G y w) =
      2 * (degreeThree G (G.neighborFinset y)).card := by
    calc
      _ = ∑ _w ∈ degreeThree G (G.neighborFinset y), 2 := by
        apply Finset.sum_congr rfl
        intro w hw
        have hm := Finset.mem_filter.mp hw
        have hc := forwardWeight_add_one hm.1
        omega
      _ = _ := by simp [Nat.mul_comm]
  rw [sum_degree_parts hdeg, hlow, hhigh]

private def localThreeCount (G : SimpleGraph V) (y : V) : ℕ :=
  ∑ v ∈ degreeThree G (G.neighborFinset y),
    ∑ w ∈ (G.neighborFinset y).erase v, forwardWeight G y w

/-- Erasing the chosen high-degree root removes exactly two forward extensions. -/
private lemma local_three_count_identity
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (y : V) :
    localThreeCount G y + 2 * (degreeThree G (G.neighborFinset y)).card =
      (degreeThree G (G.neighborFinset y)).card *
        ((degreeTwo G (G.neighborFinset y)).card +
          2 * (degreeThree G (G.neighborFinset y)).card) := by
  have hi (v : V) (hv : v ∈ degreeThree G (G.neighborFinset y)) :
      (∑ w ∈ (G.neighborFinset y).erase v, forwardWeight G y w) + 2 =
        (degreeTwo G (G.neighborFinset y)).card +
          2 * (degreeThree G (G.neighborFinset y)).card := by
    have hm := Finset.mem_filter.mp hv
    have hc := forwardWeight_add_one hm.1
    have hw : forwardWeight G y v = 2 := by omega
    have he := Finset.sum_erase_add (G.neighborFinset y) (forwardWeight G y) hm.1
    simpa [hw, neighbor_weight_sum hdeg y] using he
  have hs := Finset.sum_congr (s₁ := degreeThree G (G.neighborFinset y)) rfl hi
  simpa [localThreeCount, Finset.sum_add_distrib, Nat.mul_comm] using hs

/-- Partitioning the actual three-step path family by its first middle vertex
gives the local extension counts, with every root and every extension retained. -/
private lemma three_paths_card_eq_sum_local
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V)) :
    (threePaths G (degreeThree G L)).card = ∑ y ∈ R, localThreeCount G y := by
  let S : Finset (Σ _y : V, Σ _v : V, Σ _w : V, V) :=
    R.sigma fun y => (degreeThree G (G.neighborFinset y)).sigma fun v =>
      ((G.neighborFinset y).erase v).sigma fun w => (G.neighborFinset w).erase y
  have hbij : (threePaths G (degreeThree G L)).card = S.card := by
    apply Finset.card_bij (fun q _ => ⟨q.first, q.root, q.second, q.endpoint⟩)
    · intro q hq
      have hp : q.root ∈ degreeThree G L ∧ G.Adj q.root q.first ∧
          G.Adj q.first q.second ∧ G.Adj q.second q.endpoint ∧
          q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
        simpa [threePaths] using hq
      have hr := Finset.mem_filter.mp hp.1
      have hy : q.first ∈ R := hpart.mem_of_mem_adj hr.1 hp.2.1
      apply Finset.mem_sigma.mpr
      refine ⟨hy, Finset.mem_sigma.mpr ⟨?_, Finset.mem_sigma.mpr ⟨?_, ?_⟩⟩⟩
      · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hp.2.1.symm, hr.2⟩
      · exact Finset.mem_erase.mpr ⟨hp.2.2.2.2.1.symm,
          (G.mem_neighborFinset _ _).mpr hp.2.2.1⟩
      · exact Finset.mem_erase.mpr ⟨hp.2.2.2.2.2.symm,
          (G.mem_neighborFinset _ _).mpr hp.2.2.2.1⟩
    · intro q hq q' hq' he
      have hroot : q.root = q'.root := congrArg (fun t : Σ _y : V, Σ _v : V,
        Σ _w : V, V => t.2.1) he
      have hfirst : q.first = q'.first := congrArg (fun t : Σ _y : V, Σ _v : V,
        Σ _w : V, V => t.1) he
      have hsecond : q.second = q'.second := congrArg (fun t : Σ _y : V, Σ _v : V,
        Σ _w : V, V => t.2.2.1) he
      have hend : q.endpoint = q'.endpoint := congrArg (fun t : Σ _y : V, Σ _v : V,
        Σ _w : V, V => t.2.2.2) he
      cases q
      cases q'
      simp_all
    · rintro ⟨y, v, w, z⟩ hx
      rcases Finset.mem_sigma.mp hx with ⟨hy, hx⟩
      rcases Finset.mem_sigma.mp hx with ⟨hv, hx⟩
      rcases Finset.mem_sigma.mp hx with ⟨hw, hz⟩
      have hv0 := Finset.mem_filter.mp hv
      have hvy := ((G.mem_neighborFinset _ _).mp hv0.1).symm
      have hvL : v ∈ L := hpart.mem_of_mem_adj' hy hvy
      have hw0 := Finset.mem_erase.mp hw
      have hz0 := Finset.mem_erase.mp hz
      refine ⟨⟨v, y, w, z⟩, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨Finset.mem_filter.mpr ⟨hvL, hv0.2⟩, hvy,
        (G.mem_neighborFinset _ _).mp hw0.2, (G.mem_neighborFinset _ _).mp hz0.2,
        hw0.1.symm, hz0.1.symm⟩
  simpa [S, Finset.card_sigma, localThreeCount, forwardWeight] using hbij

private lemma neighbor_parts_card
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (y : V) :
    (degreeTwo G (G.neighborFinset y)).card +
      (degreeThree G (G.neighborFinset y)).card = G.degree y := by
  have h := congrArg Finset.card (degree_parts_union hdeg (G.neighborFinset y))
  simpa [Finset.card_union_of_disjoint (degree_parts_disjoint (G.neighborFinset y)),
    SimpleGraph.card_neighborFinset_eq_degree] using h

/-- The local three-step count loses at most four at a low middle vertex and
at most two at a high middle vertex. -/
private lemma local_three_count_bound
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (y : V) :
    4 * (degreeThree G (G.neighborFinset y)).card ≤
      localThreeCount G y + if G.degree y = 2 then 4 else 2 := by
  let g := (degreeThree G (G.neighborFinset y)).card
  let j := (degreeTwo G (G.neighborFinset y)).card
  have hd : j + g = G.degree y := neighbor_parts_card hdeg y
  have he : localThreeCount G y + 2 * g = g * (j + 2 * g) :=
    local_three_count_identity hdeg y
  change 4 * g ≤ localThreeCount G y + if G.degree y = 2 then 4 else 2
  rcases hdeg y with hy | hy
  · have hj : j = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hm := Finset.mem_filter.mp hw
      exact hlow ((G.mem_neighborFinset _ _).mp hm.1) hy hm.2
    have hg : g = 2 := by omega
    rw [ite_eq_left hy]
    rw [hj, hg] at he
    omega
  · have hd' : j + g = 3 := hd.trans hy
    have hjg : j * g ≤ 2 := by
      have hc : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by omega
      rcases hc with hg | hg | hg | hg <;> rw [hg] at hd' ⊢ <;> omega
    have hm := congrArg (fun n : ℕ => g * n) hd'
    have he' : localThreeCount G y + j * g = 4 * g := by nlinarith
    have hy2 : G.degree y ≠ 2 := by omega
    rw [ite_eq_right hy2]
    omega

/-- Double-count actual incidences from high left vertices to the right side. -/
private lemma sum_high_neighbors
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V)) :
    (∑ y ∈ R, (degreeThree G (G.neighborFinset y)).card) =
      3 * (degreeThree G L).card := by
  have hleft (v : V) (hv : v ∈ degreeThree G L) :
      R.bipartiteAbove G.Adj v = G.neighborFinset v := by
    ext w
    simp only [Finset.mem_bipartiteAbove, SimpleGraph.mem_neighborFinset]
    constructor
    · exact And.right
    · intro hvw
      exact ⟨hpart.mem_of_mem_adj (Finset.mem_filter.mp hv).1 hvw, hvw⟩
  have hright (y : V) (hy : y ∈ R) :
      (degreeThree G L).bipartiteBelow G.Adj y = degreeThree G (G.neighborFinset y) := by
    ext v
    simp only [Finset.mem_bipartiteBelow, degreeThree, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨hv, h3⟩, hvy⟩
      exact ⟨hvy.symm, h3⟩
    · rintro ⟨hyv, h3⟩
      exact ⟨⟨hpart.mem_of_mem_adj' hy hyv.symm, h3⟩, hyv.symm⟩
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := G.Adj) (s := degreeThree G L) (t := R)
  calc
    _ = ∑ y ∈ R, ((degreeThree G L).bipartiteBelow G.Adj y).card := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hright y hy]
    _ = ∑ v ∈ degreeThree G L, (R.bipartiteAbove G.Adj v).card := hdc.symm
    _ = ∑ v ∈ degreeThree G L, 3 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hleft v hv, SimpleGraph.card_neighborFinset_eq_degree]
      exact (Finset.mem_filter.mp hv).2
    _ = _ := by simp [Nat.mul_comm]

private lemma middle_penalty_sum
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (R : Finset V) :
    (∑ y ∈ R, if G.degree y = 2 then 4 else 2) =
      4 * (degreeTwo G R).card + 2 * (degreeThree G R).card := by
  rw [sum_degree_parts hdeg R]
  have h2 : (∑ y ∈ degreeTwo G R, if G.degree y = 2 then 4 else 2) =
      4 * (degreeTwo G R).card := by
    calc
      _ = ∑ _y ∈ degreeTwo G R, 4 := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [ite_eq_left (Finset.mem_filter.mp hy).2]
      _ = _ := by simp [Nat.mul_comm]
  have h3 : (∑ y ∈ degreeThree G R, if G.degree y = 2 then 4 else 2) =
      2 * (degreeThree G R).card := by
    calc
      _ = ∑ _y ∈ degreeThree G R, 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hy3 := (Finset.mem_filter.mp hy).2
        rw [ite_eq_right (by omega)]
      _ = _ := by simp [Nat.mul_comm]
  rw [h2, h3]

private lemma one_side_counting
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    15 * (degreeThree G L).card ≤ (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card := by
  have hsum := Finset.sum_le_sum (s := R)
    (fun y _ => local_three_count_bound hdeg hlow y)
  have hcount : 12 * (degreeThree G L).card ≤
      (threePaths G (degreeThree G L)).card +
        4 * (degreeTwo G R).card + 2 * (degreeThree G R).card := by
    calc
      12 * (degreeThree G L).card = 4 * (3 * (degreeThree G L).card) := by omega
      _ = ∑ y ∈ R, 4 * (degreeThree G (G.neighborFinset y)).card := by
        rw [← sum_high_neighbors hpart, Finset.mul_sum]
      _ ≤ ∑ y ∈ R, (localThreeCount G y + if G.degree y = 2 then 4 else 2) := hsum
      _ = _ := by
        rw [Finset.sum_add_distrib, ← three_paths_card_eq_sum_local hpart,
          middle_penalty_sum hdeg R]
        omega
  have hgeom := high_root_three_paths_bound hpart hg
  omega

/-- A finite bipartite graph of degrees two and three, with independent degree-two
vertices and extended girth at least eight, satisfies both cubic slice bounds.
The path injection and the weighted incidence count are derived in the proof. -/
theorem cubic_slice_counting
    {L R : Finset V} (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    (15 * (degreeThree G L).card ≤ (degreeThree G L).card * R.card +
      2 * (degreeThree G R).card + 4 * (degreeTwo G R).card) ∧
    (15 * (degreeThree G R).card ≤ (degreeThree G R).card * L.card +
      2 * (degreeThree G L).card + 4 * (degreeTwo G L).card) := by
  exact ⟨one_side_counting hpart hdeg hlow hg,
    one_side_counting hpart.symm hdeg hlow hg⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
