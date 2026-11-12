/- GID: D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Actual cycle flips transport Pfaffian coefficients and imply uniform signs. -/

import D5.S0.Certificates.Combinatorics.NormalizedPfaffian
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.ZMod.IntUnitsPower
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-! Actual alternating-cycle flips, integer orientation signs and matching weights. -/

open scoped BigOperators symmDiff

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian

open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation (P)

noncomputable def matchingMate {V : Type*} (M : (⊤ : SimpleGraph V).Subgraph)
    (hM : M.IsPerfectMatching) (v : V) : V :=
  ((SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) v).choose

theorem matchingMate_adj {V : Type*} (M : (⊤ : SimpleGraph V).Subgraph)
    (hM : M.IsPerfectMatching) (v : V) : M.Adj v (matchingMate M hM v) :=
  ((SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) v).choose_spec.1

theorem matchingMate_eq_iff {V : Type*} (M : (⊤ : SimpleGraph V).Subgraph)
    (hM : M.IsPerfectMatching) (v w : V) : matchingMate M hM v = w ↔ M.Adj v w := by
  constructor
  · rintro rfl
    exact matchingMate_adj M hM v
  · intro h
    exact hM.1.eq_of_adj_left (matchingMate_adj M hM v) h

theorem matchingMate_involutive {V : Type*} (M : (⊤ : SimpleGraph V).Subgraph)
    (hM : M.IsPerfectMatching) : Function.Involutive (matchingMate M hM) := by
  intro v
  apply (matchingMate_eq_iff M hM _ _).mpr
  exact (matchingMate_adj M hM v).symm

theorem matchingMate_ne {V : Type*} (M : (⊤ : SimpleGraph V).Subgraph)
    (hM : M.IsPerfectMatching) (v : V) : matchingMate M hM v ≠ v := by
  have h := M.adj_sub (matchingMate_adj M hM v)
  simpa only [SimpleGraph.top_adj, ne_comm] using h

noncomputable def matchingToPairing (n : ℕ)
    (M : {M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph // M.IsPerfectMatching}) : P n :=
  ⟨matchingMate M.val M.property, matchingMate_involutive M.val M.property,
    matchingMate_ne M.val M.property⟩

noncomputable def pairingGraph {n : ℕ} (p : P n) : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph where
  verts := Set.univ
  Adj v w := p.val v = w
  adj_sub := by
    intro v w h
    rw [SimpleGraph.top_adj]
    intro he
    exact p.property.2 v (h.trans he.symm)
  edge_vert := by simp
  symm := ⟨by
    intro v w h
    rw [← h]
    exact p.property.1 v⟩

theorem pairingGraph_perfect {n : ℕ} (p : P n) : (pairingGraph p).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  refine ⟨p.val v, rfl, ?_⟩
  intro w h
  change p.val v = w at h
  exact h.symm

noncomputable def pairingToMatching {n : ℕ} (p : P n) :
    {M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph // M.IsPerfectMatching} :=
  ⟨pairingGraph p, pairingGraph_perfect p⟩

theorem pairing_matching_inverse {n : ℕ} (p : P n) : matchingToPairing n (pairingToMatching p) = p := by
  apply Subtype.ext
  funext v
  apply (matchingMate_eq_iff (pairingGraph p) (pairingGraph_perfect p) v (p.val v)).mpr
  rfl

theorem matching_pairing_inverse (n : ℕ)
    (M : {M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph // M.IsPerfectMatching}) :
    pairingToMatching (matchingToPairing n M) = M := by
  apply Subtype.ext
  ext v w
  · simp only [pairingToMatching, pairingGraph, Set.mem_univ, true_iff]
    exact M.property.2 v
  · exact matchingMate_eq_iff M.val M.property v w

noncomputable def matchingEquiv (n : ℕ) :
    {M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph // M.IsPerfectMatching} ≃ P n where
  toFun := matchingToPairing n
  invFun := pairingToMatching
  left_inv := matching_pairing_inverse n
  right_inv := pairing_matching_inverse

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian


namespace D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian

variable {V : Type*} {G : SimpleGraph V}

/-- Reverse darts receive complementary bits; bit one denotes opposition. -/
def Reverses (epsilon : G.Dart → ZMod 2) : Prop :=
  ∀ d, epsilon d.symm = 1 + epsilon d

/-- Signs are integer units before any change of coefficient ring. -/
def dartSign (epsilon : G.Dart → ZMod 2) (d : G.Dart) : ℤˣ :=
  (-1 : ℤˣ) ^ epsilon d

private theorem dartSign_symm {epsilon : G.Dart → ZMod 2} (he : Reverses epsilon)
    (d : G.Dart) : dartSign epsilon d.symm = -dartSign epsilon d := by
  simp only [dartSign, he d, uzpow_add, uzpow_one, neg_one_mul]

/-- The orientation condition quantifies over actual cycles and actual induced complements. -/
def NiceOdd (epsilon : G.Dart → ZMod 2) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → Even p.length →
    (∃ N : (G.induce p.toSubgraph.vertsᶜ).Subgraph, N.IsPerfectMatching) →
    (p.darts.map epsilon).sum = 1

private theorem cycle_saturated {M : G.Subgraph} {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    (ha : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe) {x : V} (hx : x ∈ p.toSubgraph.verts) :
    ∃ y, p.toSubgraph.Adj x y ∧ M.Adj x y := by
  classical
  have hc := hp.isCycles_spanningCoe_toSubgraph
  have hn : (p.toSubgraph.neighborSet x).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hx)]
    decide
  obtain ⟨y, hy⟩ := hn
  obtain ⟨z, hzy, hz⟩ := hc.other_adj_of_adj hy
  by_cases hxy : M.Adj x y
  · exact ⟨y, hy, hxy⟩
  · refine ⟨z, hz, ?_⟩
    by_contra hn
    exact hxy ((ha hzy hy hz).mpr hn)

private theorem matching_stays_outside {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) (ha : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe)
    {x y : V} (hx : x ∉ p.toSubgraph.verts) (hxy : M.Adj x y) : y ∉ p.toSubgraph.verts := by
  intro hy
  obtain ⟨z, hyz, hmz⟩ := cycle_saturated hp ha hy
  have he : z = x := hM.1.eq_of_adj_left hmz hxy.symm
  exact hx (he ▸ hyz.snd_mem)

private def cycleVertex {v : V} {p : G.Walk v v} (hp : p.IsCycle) : Fin p.length ↪ V where
  toFun i := p.getVert i.val
  inj' := by
    intro i j hij
    have hi : i.val < p.support.dropLast.length := by simp
    have hj : j.val < p.support.dropLast.length := by simp
    have h : p.support.dropLast[i.val] = p.support.dropLast[j.val] := by
      simpa only [List.getElem_dropLast, p.support_getElem_eq_getVert] using hij
    exact Fin.ext ((hp.nodup_dropLast_support.getElem_inj_iff).mp h)

private theorem cycleVertex_range {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    Set.range (cycleVertex hp) = p.toSubgraph.verts := by
  ext x
  rw [p.mem_verts_toSubgraph, SimpleGraph.Walk.mem_support_iff_exists_getVert]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, rfl, i.isLt.le⟩
  · rintro ⟨i, rfl, hi⟩
    by_cases hil : i < p.length
    · exact ⟨⟨i, hil⟩, rfl⟩
    · have he : i = p.length := by omega
      subst i
      refine ⟨⟨0, by have := hp.three_le_length; omega⟩, ?_⟩
      change p.getVert 0 = p.getVert p.length
      simp

private def insideMatching (M : G.Subgraph) {v : V} (p : G.Walk v v) :
    (G.induce p.toSubgraph.verts).Subgraph where
  verts := Set.univ
  Adj x y := M.Adj x.val y.val
  adj_sub h := M.adj_sub h
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun _ _ h => h.symm⟩

private theorem insideMatching_perfect {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) (ha : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe) :
    (insideMatching M p).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro x
  obtain ⟨y, hxy, hm⟩ := cycle_saturated hp ha x.property
  refine ⟨⟨y, hxy.snd_mem⟩, hm, ?_⟩
  intro z hz
  exact Subtype.ext (hM.1.eq_of_adj_left hz hm)

private theorem alternating_even {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    (ha : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe) : Even p.length := by
  classical
  let eqv : Fin p.length ≃ p.toSubgraph.verts :=
    (Equiv.ofInjective (cycleVertex hp) (cycleVertex hp).injective).trans
      (Set.equivOfEq (cycleVertex_range hp))
  letI : Fintype p.toSubgraph.verts := Fintype.ofEquiv _ eqv
  have hr : Fintype.card p.toSubgraph.verts = p.length := by
    rw [← Fintype.card_congr eqv, Fintype.card_fin]
  rw [← hr]
  exact (insideMatching_perfect hM hp ha).even_card

private def outsideMatching (M : G.Subgraph) {v : V} (p : G.Walk v v) :
    (G.induce p.toSubgraph.vertsᶜ).Subgraph where
  verts := Set.univ
  Adj x y := M.Adj x.val y.val
  adj_sub h := M.adj_sub h
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun _ _ h => h.symm⟩

private theorem outsideMatching_perfect {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) (ha : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe) :
    (outsideMatching M p).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro x
  obtain ⟨y, hy, hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM x.val
  refine ⟨⟨y, matching_stays_outside hM hp ha x.property hy⟩, hy, ?_⟩
  intro z hz
  apply Subtype.ext
  exact hu z.val hz

private theorem flip_le (M : G.Subgraph) {v : V} (p : G.Walk v v) :
    M.spanningCoe ∆ p.toSubgraph.spanningCoe ≤ G := by
  intro x y h
  rcases h with h | h
  · exact M.adj_sub h.1
  · exact p.toSubgraph.adj_sub h.1

/-- An actual flip toggles exactly the cycle edges, preserves every other edge,
and leaves a perfect matching on the actual vertex-deleted induced graph. -/
theorem alternating_cycle_flip {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) (ha : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe) :
    Even p.length ∧ (∃ N : G.Subgraph, N.IsPerfectMatching ∧
      (∀ x y, N.Adj x y ↔
        (M.Adj x y ∧ ¬ p.toSubgraph.Adj x y) ∨
        (p.toSubgraph.Adj x y ∧ ¬ M.Adj x y))) ∧
    ∃ N : (G.induce p.toSubgraph.vertsᶜ).Subgraph, N.IsPerfectMatching := by
  refine ⟨alternating_even hM hp ha, ?_, outsideMatching M p, outsideMatching_perfect hM hp ha⟩
  · let H := M.spanningCoe ∆ p.toSubgraph.spanningCoe
    have ht : (⊤ : H.Subgraph).IsPerfectMatching :=
      hM.symmDiff_of_isAlternating ha hp.isCycles_spanningCoe_toSubgraph
    refine ⟨G.toSubgraph H (flip_le M p), ?_, ?_⟩
    · exact (SimpleGraph.Subgraph.IsPerfectMatching.toSubgraph_iff (flip_le M p)).mpr ht
    · intro x y
      rfl


open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation (P)
open D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian
open D5.S3.Combinatorics.PerfectMatchings.CanonicalPairListing

private def labelHom {n : ℕ} (label : V ≃ Fin (2 * n)) : G →g (⊤ : SimpleGraph (Fin (2 * n))) where
  toFun := label
  map_rel' h := by
    rw [SimpleGraph.top_adj]
    exact fun he => h.ne (label.injective he)

private def labeledMatching {n : ℕ} (label : V ≃ Fin (2 * n))
    (M : G.Subgraph) : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph :=
  M.map (labelHom label)

private theorem labeledMatching_perfect {n : ℕ} (label : V ≃ Fin (2 * n))
    (M : G.Subgraph) (hM : M.IsPerfectMatching) : (labeledMatching label M).IsPerfectMatching := by
  refine ⟨hM.1.map (labelHom label) label.injective, ?_⟩
  intro x
  exact ⟨label.symm x, hM.2 _, label.apply_symm_apply x⟩

/-- The original matching bijection applied after the actual vertex enumeration. -/
noncomputable def matchingPairing {n : ℕ} (label : V ≃ Fin (2 * n))
    (M : {M : G.Subgraph // M.IsPerfectMatching}) : P n :=
  matchingToPairing n ⟨labeledMatching label M.val,
    labeledMatching_perfect label M.val M.property⟩

/-- The supplied partner map recognizes exactly the edges of the actual matching. -/
theorem matchingPairing_adj {n : ℕ} (label : V ≃ Fin (2 * n))
    (M : {M : G.Subgraph // M.IsPerfectMatching}) (x y : V) :
    (matchingPairing label M).val (label x) = label y ↔ M.val.Adj x y := by
  change matchingMate _ (labeledMatching_perfect label M.val M.property) (label x) =
    label y ↔ _
  rw [matchingMate_eq_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hax : a = x := label.injective ha
    have hby : b = y := label.injective hb
    simpa only [hax, hby] using hab
  · intro hxy
    exact ⟨x, y, hxy, rfl, rfl⟩

theorem canonical_adj {n : ℕ} (label : V ≃ Fin (2 * n))
    (M : {M : G.Subgraph // M.IsPerfectMatching}) (i : Fin n) : M.val.Adj
      (label.symm (canonicalListing (matchingPairing label M) ⟨2 * i.val, by omega⟩))
      (label.symm (canonicalListing (matchingPairing label M) ⟨2 * i.val + 1, by omega⟩)) := by
  have h := canonical_mate (matchingPairing label M) i
  have ha := (matchingMate_eq_iff _ (labeledMatching_perfect label M.val M.property) _ _).mp h
  obtain ⟨v, w, hvw, hv, hw⟩ := ha
  change label v = _ at hv
  change label w = _ at hw
  simpa only [← hv, ← hw, label.symm_apply_apply] using hvw

/-- The genuine normalized Pfaffian coefficient, including actual directed-edge signs. -/
noncomputable def matchingTau {n : ℕ} (label : V ≃ Fin (2 * n)) (epsilon : G.Dart → ZMod 2)
    (M : {M : G.Subgraph // M.IsPerfectMatching}) : ℤˣ :=
  Equiv.Perm.sign (canonicalListing (matchingPairing label M)) *
    ∏ i : Fin n, dartSign epsilon
      ⟨(label.symm (canonicalListing (matchingPairing label M) ⟨2 * i.val, by omega⟩),
        label.symm (canonicalListing (matchingPairing label M) ⟨2 * i.val + 1, by omega⟩)),
        M.val.adj_sub (canonical_adj label M i)⟩

private noncomputable def extendedSign {n : ℕ} (label : V ≃ Fin (2 * n))
    (epsilon : G.Dart → ZMod 2) (x y : Fin (2 * n)) : ℤˣ := by
  classical
  exact if h : G.Adj (label.symm x) (label.symm y) then
    dartSign epsilon ⟨(label.symm x, label.symm y), h⟩
  else if x < y then 1 else -1

private theorem extendedSign_skew {n : ℕ} (label : V ≃ Fin (2 * n))
    {epsilon : G.Dart → ZMod 2} (he : Reverses epsilon) (x y : Fin (2 * n)) (hxy : x ≠ y) :
    extendedSign label epsilon y x = -extendedSign label epsilon x y := by
  classical
  unfold extendedSign
  by_cases h : G.Adj (label.symm x) (label.symm y)
  · rw [dite_eq_left h, dite_eq_left h.symm]
    exact dartSign_symm he ⟨(label.symm x, label.symm y), h⟩
  · have h' : ¬G.Adj (label.symm y) (label.symm x) := fun hy => h hy.symm
    rw [dite_eq_right h, dite_eq_right h']
    rcases lt_or_gt_of_ne hxy with h | h
    · simp [h, not_lt_of_gt h]
    · simp [h, not_lt_of_gt h]

private theorem tau_listing {n : ℕ} (label : V ≃ Fin (2 * n))
    {epsilon : G.Dart → ZMod 2} (he : Reverses epsilon)
    (M : {M : G.Subgraph // M.IsPerfectMatching}) (s : Equiv.Perm (Fin (2 * n))) (hs : ∀ i : Fin n, M.val.Adj
      (label.symm (s ⟨2 * i.val, by omega⟩))
      (label.symm (s ⟨2 * i.val + 1, by omega⟩))) :
    listingValue (extendedSign label epsilon) s = matchingTau label epsilon M := by
  have hp : pairingOfListing s = matchingPairing label M := by
    apply (pairing_eq_iff s _).mpr
    intro i
    apply (matchingMate_eq_iff _ (labeledMatching_perfect label M.val M.property) _ _).mpr
    exact ⟨label.symm _, label.symm _, hs i, label.apply_symm_apply _, label.apply_symm_apply _⟩
  rw [listing_value_canonical _ (extendedSign_skew label he), hp]
  unfold listingValue matchingTau
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact dite_eq_left (M.val.adj_sub (canonical_adj label M i))

/-- A graph-supported skew matrix, with its diagonal explicitly zero in every characteristic. -/
noncomputable def orientedMatrix {R : Type*} [CommRing R] {n : ℕ}
    (label : V ≃ Fin (2 * n)) (epsilon : G.Dart → ZMod 2)
    (w : G.edgeSet → R) : Matrix (Fin (2 * n)) (Fin (2 * n)) R := by
  classical
  exact fun x y => if x = y then 0 else
    if h : G.Adj (label.symm x) (label.symm y) then
      ((dartSign epsilon ⟨(label.symm x, label.symm y), h⟩ : ℤˣ) : ℤ) *
        w ⟨s(label.symm x, label.symm y), h⟩ else 0

/-- Each actual undirected edge of the matching occurs exactly once in this product. -/
noncomputable def matchingWeight [Fintype V] {R : Type*} [CommRing R]
    (w : G.edgeSet → R) (M : G.Subgraph) : R := by
  classical
  letI : Fintype M.edgeSet := Fintype.ofFinite _
  exact ∏ edge : M.edgeSet, w ⟨edge.val, M.edgeSet_subset edge.property⟩

/-- The partition function sums over actual perfect-matching subgraphs. -/
noncomputable def partitionFunction [Fintype V] {R : Type*} [CommRing R] (w : G.edgeSet → R) : R := by
  classical
  letI : Fintype {M : G.Subgraph // M.IsPerfectMatching} := Fintype.ofFinite _
  exact ∑ M : {M : G.Subgraph // M.IsPerfectMatching}, matchingWeight w M.val

section CycleTransport

variable [DecidableEq V]

private noncomputable def cycleRotation {v : V} (p : G.Walk v v) : Equiv.Perm V := by
  classical
  exact p.support.dropLast.formPerm

private theorem cycleRotation_get {v : V} {p : G.Walk v v} (hp : p.IsCycle) (i : ℕ) (hi : i < p.length) :
    cycleRotation p (p.getVert i) = p.getVert (i + 1) := by
  classical
  have h := List.formPerm_apply_getElem p.support.dropLast hp.nodup_dropLast_support i
    (by simpa using hi)
  simp only [List.getElem_dropLast, p.support_getElem_eq_getVert,
    List.length_dropLast, p.length_support, Nat.add_sub_cancel] at h
  change p.support.dropLast.formPerm (p.getVert i) = _
  rw [h]
  by_cases hnext : i + 1 < p.length
  · rw [Nat.mod_eq_of_lt hnext]
  · have he : i + 1 = p.length := by omega
    simp [he]

private theorem cycleRotation_outside {v : V} {p : G.Walk v v}
    {x : V} (hx : x ∉ p.toSubgraph.verts) : cycleRotation p x = x := by
  classical
  apply List.formPerm_apply_of_notMem
  intro h
  exact hx (p.mem_verts_toSubgraph.mpr (List.mem_of_mem_dropLast h))

private theorem cycleRotation_adj {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    {x : V} (hx : x ∈ p.toSubgraph.verts) : p.toSubgraph.Adj x (cycleRotation p x) := by
  rw [← cycleVertex_range hp] at hx
  obtain ⟨i, rfl⟩ := hx
  change p.toSubgraph.Adj (p.getVert i.val) (cycleRotation p (p.getVert i.val))
  rw [cycleRotation_get hp i.val i.isLt]
  exact p.toSubgraph_adj_getVert i.isLt

private theorem cycle_adj_iff {v : V} {p : G.Walk v v} (hp : p.IsCycle) (x y : V) : p.toSubgraph.Adj x y ↔
      x ∈ p.toSubgraph.verts ∧ (cycleRotation p x = y ∨ cycleRotation p y = x) := by
  classical
  constructor
  · intro hxy
    refine ⟨hxy.fst_mem, ?_⟩
    obtain ⟨i, hi, hil⟩ := p.toSubgraph_adj_iff.mp hxy
    rcases Sym2.eq_iff.mp hi with h | h
    · left
      rw [← h.1, cycleRotation_get hp i hil, h.2]
    · right
      rw [← h.1, cycleRotation_get hp i hil, h.2]
  · rintro ⟨hx, h | h⟩
    · exact h ▸ cycleRotation_adj hp hx
    · have hy : y ∈ p.toSubgraph.verts := by
        by_contra hy
        have he := cycleRotation_outside hy
        rw [he] at h
        exact hy (h ▸ hx)
      exact (h ▸ cycleRotation_adj hp hy).symm

private theorem cycleRotation_inside {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    {x : V} (hx : x ∈ p.toSubgraph.verts) : cycleRotation p x ∈ p.toSubgraph.verts :=
  (cycleRotation_adj hp hx).snd_mem

private theorem cycleRotation_sq_ne {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    {x : V} (hx : x ∈ p.toSubgraph.verts) : cycleRotation p (cycleRotation p x) ≠ x := by
  classical
  rw [← cycleVertex_range hp] at hx
  obtain ⟨i, rfl⟩ := hx
  change cycleRotation p (cycleRotation p (p.getVert i.val)) ≠ p.getVert i.val
  rw [cycleRotation_get hp i.val i.isLt]
  have hl := hp.three_le_length
  by_cases hnext : i.val + 1 < p.length
  · rw [cycleRotation_get hp (i.val + 1) hnext]
    by_cases hnext2 : i.val + 2 < p.length
    · intro h
      have he := (cycleVertex hp).injective (show
        cycleVertex hp ⟨i.val + 2, hnext2⟩ = cycleVertex hp i from h)
      have hv := congrArg Fin.val he
      dsimp only at hv
      omega
    · have he : i.val + 1 + 1 = p.length := by omega
      rw [he, show p.getVert p.length = p.getVert 0 by simp]
      intro h
      have he := (cycleVertex hp).injective (show
        cycleVertex hp ⟨0, by omega⟩ = cycleVertex hp i from h)
      have hv := congrArg Fin.val he
      dsimp only at hv
      omega
  · have he : i.val + 1 = p.length := by omega
    rw [he, show p.getVert p.length = p.getVert 0 by simp, cycleRotation_get hp 0 (by omega)]
    intro h
    have he := (cycleVertex hp).injective (show
      cycleVertex hp ⟨1, by omega⟩ = cycleVertex hp i from h)
    have hv := congrArg Fin.val he
    dsimp only at hv
    omega

private theorem cycleRotation_matching {M N : G.Subgraph} (hM : M.IsPerfectMatching)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) (ha : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe)
    (hN : ∀ x y, N.Adj x y ↔
      (M.Adj x y ∧ ¬p.toSubgraph.Adj x y) ∨
      (p.toSubgraph.Adj x y ∧ ¬M.Adj x y)) {x y : V} (hxy : M.Adj x y) :
    N.Adj (cycleRotation p x) (cycleRotation p y) := by
  classical
  have forward (z : V) (hz : z ∈ p.toSubgraph.verts)
      (hm : M.Adj z (cycleRotation p z)) :
      N.Adj (cycleRotation p z) (cycleRotation p (cycleRotation p z)) := by
    apply (hN _ _).mpr
    right
    have hc := cycleRotation_adj hp hz
    have hc' := cycleRotation_adj hp (cycleRotation_inside hp hz)
    refine ⟨hc', ?_⟩
    exact (ha (cycleRotation_sq_ne hp hz).symm hc.symm hc').mp hm.symm
  by_cases hx : x ∈ p.toSubgraph.verts
  · obtain ⟨z, hxz, hmz⟩ := cycle_saturated hp ha hx
    have hzy : z = y := hM.1.eq_of_adj_left hmz hxy
    subst z
    rcases (cycle_adj_iff hp x y).mp hxz |>.2 with h | h
    · subst y
      exact forward x hx hxy
    · have hy := hxz.snd_mem
      have hn := forward y hy (h ▸ hxy.symm)
      simpa only [h] using hn.symm
  · have hy := matching_stays_outside hM hp ha hx hxy
    rw [cycleRotation_outside hx, cycleRotation_outside hy]
    exact (hN _ _).mpr (Or.inl ⟨hxy, fun hc => hx hc.fst_mem⟩)

private theorem cycleRotation_sign [Fintype V] {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (heven : Even p.length) : Equiv.Perm.sign (cycleRotation p) = -1 := by
  classical
  have hlen : p.support.dropLast.length = p.length := by simp
  have hn := hp.nodup_dropLast_support
  have hc := List.isCycle_formPerm hn (by rw [hlen]; have := hp.three_le_length; omega)
  have hs := List.support_formPerm_of_nodup p.support.dropLast hn (by
    intro x hx
    have := congrArg List.length hx
    simp only [hlen, List.length_singleton] at this
    have := hp.three_le_length
    omega)
  change Equiv.Perm.sign p.support.dropLast.formPerm = -1
  rw [hc.sign, hs, List.toFinset_card_of_nodup hn, hlen,
    heven.neg_one_pow]

private noncomputable def rotationFactor {v : V} (p : G.Walk v v)
    (f : V → V → ℤˣ) (x : V) : ℤˣ := by
  classical
  exact if x ∈ p.toSubgraph.verts then f x (cycleRotation p x) else 1

private theorem rotationFactor_pair {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) (ha : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe)
    (f : V → V → ℤˣ) (hf : ∀ x y, x ≠ y → f y x = -f x y) {x y : V} (hxy : M.Adj x y) :
    rotationFactor p f x * rotationFactor p f y =
      f x y * f (cycleRotation p x) (cycleRotation p y) := by
  classical
  by_cases hx : x ∈ p.toSubgraph.verts
  · obtain ⟨z, hxz, hmz⟩ := cycle_saturated hp ha hx
    have hzy : z = y := hM.1.eq_of_adj_left hmz hxy
    subst z
    have hy := hxz.snd_mem
    simp only [rotationFactor, ite_eq_left hx, ite_eq_left hy]
    rcases (cycle_adj_iff hp x y).mp hxz |>.2 with h | h
    · rw [h]
    · rw [h, hf y x hxy.ne.symm,
        hf x (cycleRotation p x) (cycleRotation_adj hp hx).ne, neg_mul_neg]
      exact mul_comm _ _
  · have hy := matching_stays_outside hM hp ha hx hxy
    simp only [rotationFactor, ite_eq_right hx, ite_eq_right hy, one_mul,
      cycleRotation_outside hx, cycleRotation_outside hy]
    exact (Int.units_mul_self (f x y)).symm

private theorem rotationFactor_prod [Fintype V] {v : V} {p : G.Walk v v} (hp : p.IsCycle) (f : V → V → ℤˣ) :
    (∏ x : V, rotationFactor p f x) =
      (p.darts.map (fun d => f d.fst d.snd)).prod := by
  classical
  have hlist : p.support.dropLast.map (rotationFactor p f) =
      p.darts.map (fun d => f d.fst d.snd) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    have hil : i < p.length := by simpa using hi
    simp only [List.getElem_map, List.getElem_dropLast,
      p.support_getElem_eq_getVert, p.darts_getElem_eq_getVert]
    have hx := (p.toSubgraph_adj_getVert hil).fst_mem
    simp only [rotationFactor, ite_eq_left hx, cycleRotation_get hp i hil]
  calc
    (∏ x : V, rotationFactor p f x) =
        ∏ x ∈ p.support.dropLast.toFinset, rotationFactor p f x := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro x _ hx
      apply ite_eq_right
      intro hv
      rw [← cycleVertex_range hp] at hv
      obtain ⟨i, rfl⟩ := hv
      apply hx
      rw [List.mem_toFinset]
      exact List.mem_iff_getElem.mpr ⟨i.val, by simp, by
        simp only [List.getElem_dropLast, p.support_getElem_eq_getVert]; rfl⟩
    _ = (p.support.dropLast.map (rotationFactor p f)).prod :=
      List.prod_toFinset _ hp.nodup_dropLast_support
    _ = _ := congrArg List.prod hlist

omit [DecidableEq V] in
private theorem prod_listed_pairs [Fintype V] {n : ℕ} (label : V ≃ Fin (2 * n))
    (s : Equiv.Perm (Fin (2 * n))) (f : V → ℤˣ) : (∏ x : V, f x) = ∏ i : Fin n,
      f (label.symm (s ⟨2 * i.val, by omega⟩)) *
      f (label.symm (s ⟨2 * i.val + 1, by omega⟩)) := by
  let slots : Fin n × Fin 2 ≃ Fin (2 * n) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))
  have h := Equiv.prod_comp ((slots.trans s).trans label.symm) f
  rw [Fintype.prod_prod_type] at h
  simp only [Fin.prod_univ_two] at h
  have hzero (i : Fin n) : slots (i, 0) = ⟨2 * i.val, by omega⟩ := by
    apply Fin.ext
    simp [slots]
  have hone (i : Fin n) : slots (i, 1) = ⟨2 * i.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [slots, Nat.add_comm]
  simpa only [Equiv.trans_apply, hzero, hone] using h.symm

end CycleTransport

/-- Flipping an actual alternating cycle transports its genuine Pfaffian coefficient.
The rotation fixes every outside vertex, so the same outside pairing occurs on both sides. -/
theorem alternating_cycle_transport {n : ℕ} (label : V ≃ Fin (2 * n))
    {epsilon : G.Dart → ZMod 2} (he : Reverses epsilon) (M : {M : G.Subgraph // M.IsPerfectMatching})
    {v : V} {p : G.Walk v v} (hp : p.IsCycle)
    (ha : p.toSubgraph.spanningCoe.IsAlternating M.val.spanningCoe) :
    ∃ N : {N : G.Subgraph // N.IsPerfectMatching},
      (∀ x y, N.val.Adj x y ↔
        (M.val.Adj x y ∧ ¬p.toSubgraph.Adj x y) ∨
        (p.toSubgraph.Adj x y ∧ ¬M.val.Adj x y)) ∧
      matchingTau label epsilon M * matchingTau label epsilon N =
        -(p.darts.map (dartSign epsilon)).prod := by
  classical
  letI : Fintype V := Fintype.ofEquiv _ label.symm
  obtain ⟨heven, ⟨N, hN, hflip⟩, _⟩ := alternating_cycle_flip M.property hp ha
  refine ⟨⟨N, hN⟩, hflip, ?_⟩
  let rho := cycleRotation p
  let q : Equiv.Perm (Fin (2 * n)) := label.permCongr rho
  let s := canonicalListing (matchingPairing label M)
  let f := extendedSign label epsilon
  let g : V → V → ℤˣ := fun x y => f (label x) (label y)
  have hskew : ∀ x y, x ≠ y → g y x = -g x y := by
    intro x y hxy
    exact extendedSign_skew label he _ _ (fun h => hxy (label.injective h))
  have hs : ∀ i : Fin n, M.val.Adj
      (label.symm (s ⟨2 * i.val, by omega⟩))
      (label.symm (s ⟨2 * i.val + 1, by omega⟩)) := canonical_adj label M
  have ht : ∀ i : Fin n, N.Adj
      (label.symm ((q * s) ⟨2 * i.val, by omega⟩))
      (label.symm ((q * s) ⟨2 * i.val + 1, by omega⟩)) := by
    intro i
    simpa only [q, Equiv.Perm.mul_apply, Equiv.permCongr_apply,
      label.symm_apply_apply] using cycleRotation_matching M.property hp ha hflip (hs i)
  have hprod : (∏ i : Fin n,
      f (s ⟨2 * i.val, by omega⟩) (s ⟨2 * i.val + 1, by omega⟩) *
      f (q (s ⟨2 * i.val, by omega⟩)) (q (s ⟨2 * i.val + 1, by omega⟩))) =
      (p.darts.map (dartSign epsilon)).prod := by
    have h := prod_listed_pairs label s (rotationFactor p g)
    rw [rotationFactor_prod hp g] at h
    have hd : (fun d : G.Dart => g d.fst d.snd) = dartSign epsilon := by
      funext d
      simp only [g, f, extendedSign, label.symm_apply_apply, dite_eq_left d.adj]
    rw [hd] at h
    rw [h]
    apply Finset.prod_congr rfl
    intro i _
    have hr := rotationFactor_pair M.property hp ha g hskew (hs i)
    simpa only [g, q, Equiv.permCongr_apply, label.apply_symm_apply] using hr.symm
  have hsign : Equiv.Perm.sign q = -1 := by
    dsimp only [q]
    rw [Equiv.Perm.sign_permCongr]
    exact cycleRotation_sign hp heven
  rw [← tau_listing label he M s hs,
    ← tau_listing label he ⟨N, hN⟩ (q * s) ht]
  unfold listingValue
  simp only [map_mul, Equiv.Perm.mul_apply]
  rw [hsign]
  have hsq := Int.units_mul_self (Equiv.Perm.sign s)
  calc
    Equiv.Perm.sign s *
          (∏ i : Fin n, f (s ⟨2 * i.val, by omega⟩) (s ⟨2 * i.val + 1, by omega⟩)) *
        (-1 * Equiv.Perm.sign s *
          ∏ i : Fin n, f (q (s ⟨2 * i.val, by omega⟩))
            (q (s ⟨2 * i.val + 1, by omega⟩))) =
        -(Equiv.Perm.sign s * Equiv.Perm.sign s) *
          (∏ i : Fin n, f (s ⟨2 * i.val, by omega⟩)
            (s ⟨2 * i.val + 1, by omega⟩) *
            f (q (s ⟨2 * i.val, by omega⟩)) (q (s ⟨2 * i.val + 1, by omega⟩))) := by
      rw [Finset.prod_mul_distrib]
      simp only [neg_mul, mul_neg]
      congr 1
      ac_rfl
    _ = _ := by rw [hsq, neg_one_mul, hprod]

private theorem dartSign_prod (epsilon : G.Dart → ZMod 2) (l : List G.Dart) :
    (l.map (dartSign epsilon)).prod = (-1 : ℤˣ) ^ (l.map epsilon).sum := by
  induction l with
  | nil => simp
  | cons d l ih => simp only [List.map_cons, List.prod_cons, List.sum_cons,
      uzpow_add, dartSign, ih]

/-- Odd opposition on actual nice cycles forces all actual matching coefficients to agree. -/
theorem niceOdd_matching_tau_eq {n : ℕ} (label : V ≃ Fin (2 * n))
    {epsilon : G.Dart → ZMod 2} (he : Reverses epsilon) (ho : NiceOdd epsilon)
    (M N : {M : G.Subgraph // M.IsPerfectMatching}) :
    matchingTau label epsilon M = matchingTau label epsilon N := by
  classical
  letI : Fintype V := Fintype.ofEquiv _ label.symm
  suffices ∀ k (M : {M : G.Subgraph // M.IsPerfectMatching}),
      (M.val.spanningCoe ∆ N.val.spanningCoe).edgeFinset.card = k →
      matchingTau label epsilon M = matchingTau label epsilon N from this _ M rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro M hk
    by_cases heq : M = N
    · rw [heq]
    let H := M.val.spanningCoe ∆ N.val.spanningCoe
    have hne : H ≠ ⊥ := by
      intro hbot
      have hspan : M.val.spanningCoe = N.val.spanningCoe := symmDiff_eq_bot.mp hbot
      apply heq
      apply Subtype.ext
      apply SimpleGraph.Subgraph.ext
      · exact Set.eq_univ_of_forall M.property.2 |>.trans
          (Set.eq_univ_of_forall N.property.2).symm
      · exact SimpleGraph.Subgraph.spanningCoe_inj.mp hspan
    obtain ⟨v, w, hvw⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
    have hcyc : H.IsCycles := M.property.symmDiff_isCycles N.property
    obtain ⟨p, hp, _⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := H.connectedComponentMk v) (by simp) ⟨w, hvw⟩
    have hHG : H ≤ G := by
      intro x y hxy
      rcases hxy with h | h
      · exact M.val.adj_sub h.1
      · exact N.val.adj_sub h.1
    let q := p.mapLe hHG
    have hq : q.IsCycle := hp.mapLe hHG
    have hC : q.toSubgraph.spanningCoe ≤ H := by
      intro x y hxy
      exact p.toSubgraph.adj_sub
        ((SimpleGraph.Walk.adj_toSubgraph_mapLe hHG).mp hxy)
    have ha := (M.property.isAlternating_symmDiff_left N.property).mono hC
    obtain ⟨K, hflip, ht⟩ := alternating_cycle_transport label he M hq ha
    obtain ⟨heven, _, hcompl⟩ := alternating_cycle_flip M.property hq ha
    have hod := ho v q hq heven hcompl
    rw [dartSign_prod, hod, uzpow_one, neg_neg] at ht
    have hMK : matchingTau label epsilon M = matchingTau label epsilon K := by
      apply mul_right_cancel (b := matchingTau label epsilon K)
      rw [ht, Int.units_mul_self]
    have hKspan : K.val.spanningCoe = M.val.spanningCoe ∆ q.toSubgraph.spanningCoe := by
      ext x y
      exact hflip x y
    have hnew : K.val.spanningCoe ∆ N.val.spanningCoe = H \ q.toSubgraph.spanningCoe := by
      rw [hKspan, symmDiff_right_comm, symmDiff_of_ge hC]
    have hCne : q.toSubgraph.spanningCoe ≠ ⊥ := by
      intro hb
      have hlen := hq.three_le_length
      have ha := q.toSubgraph_adj_getVert (i := 0) (by omega)
      change q.toSubgraph.spanningCoe.Adj _ _ at ha
      rw [hb] at ha
      exact ha
    have hglt : K.val.spanningCoe ∆ N.val.spanningCoe < H := by
      rw [hnew]
      exact sdiff_lt hC hCne
    have hlt : (K.val.spanningCoe ∆ N.val.spanningCoe).edgeFinset.card < k := by
      rw [← hk]
      exact Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hglt)
    exact hMK.trans (ih _ hlt K rfl)

end D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
namespace D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching

open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation (P)
open D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation
open D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian
open D5.S3.Combinatorics.PerfectMatchings.CanonicalPairListing
open D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

private def Supported (label : V ≃ Fin (2 * n)) (p : P n) : Prop :=
  ∀ x, G.Adj (label.symm x) (label.symm (p.val x))

private noncomputable def supportedMatching (label : V ≃ Fin (2 * n))
    (p : P n) (hp : Supported (G := G) label p) : G.Subgraph where
  verts := Set.univ
  Adj x y := (pairingGraph p).Adj (label x) (label y)
  adj_sub := by
    intro x y hxy
    have h : p.val (label x) = label y := hxy
    simpa only [h, label.symm_apply_apply] using hp (label x)
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun _ _ h => h.symm⟩

private theorem supportedMatching_perfect (label : V ≃ Fin (2 * n))
    (p : P n) (hp : Supported (G := G) label p) :
    (supportedMatching label p hp).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro x
  obtain ⟨y, hy, hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp
    (pairingGraph_perfect p) (label x)
  refine ⟨label.symm y, ?_, ?_⟩
  · change (pairingGraph p).Adj (label x) (label (label.symm y))
    simpa using hy
  · intro z hz
    exact label.injective ((hu (label z) hz).trans (label.apply_symm_apply y).symm)

private theorem matchingPairing_supported (label : V ≃ Fin (2 * n))
    (M : {M : G.Subgraph // M.IsPerfectMatching}) : Supported (G := G) label (matchingPairing label M) := by
  intro x
  apply M.val.adj_sub
  apply (matchingPairing_adj label M _ _).mp
  simp only [label.apply_symm_apply]

private theorem pairing_supportedMatching (label : V ≃ Fin (2 * n))
    (p : P n) (hp : Supported (G := G) label p) :
    matchingPairing label
      ⟨supportedMatching label p hp, supportedMatching_perfect label p hp⟩ = p := by
  apply Subtype.ext
  funext x
  have h := (matchingPairing_adj label
    ⟨supportedMatching label p hp, supportedMatching_perfect label p hp⟩
    (label.symm x) (label.symm (p.val x))).mpr
    (show (pairingGraph p).Adj (label (label.symm x))
      (label (label.symm (p.val x))) by simp [pairingGraph])
  simpa only [label.apply_symm_apply] using h

private theorem matchingPairing_injective (label : V ≃ Fin (2 * n)) :
    Function.Injective (matchingPairing (G := G) label) := by
  intro M N h
  apply Subtype.ext
  ext x y
  · exact iff_of_true (M.property.2 x) (N.property.2 x)
  · rw [← matchingPairing_adj label M x y, ← matchingPairing_adj label N x y, h]

private noncomputable def supportedEquiv (label : V ≃ Fin (2 * n)) :
    {p : P n // Supported (G := G) label p} ≃
      {M : G.Subgraph // M.IsPerfectMatching} where
  toFun p := ⟨supportedMatching label p.val p.property,
    supportedMatching_perfect label p.val p.property⟩
  invFun M := ⟨matchingPairing label M, matchingPairing_supported label M⟩
  left_inv p := Subtype.ext (pairing_supportedMatching label p.val p.property)
  right_inv M := matchingPairing_injective label
    (pairing_supportedMatching label (matchingPairing label M) _)

private theorem matchingWeight_listing [Fintype V] {R : Type*} [CommRing R]
    (label : V ≃ Fin (2 * n)) (w : G.edgeSet → R) (M : {M : G.Subgraph // M.IsPerfectMatching}) :
    matchingWeight w M.val = ∏ i : Fin n,
      w ⟨s(label.symm (canonicalListing (matchingPairing label M) (first i)),
        label.symm (canonicalListing (matchingPairing label M) (second i))),
        M.val.adj_sub (canonical_adj label M i)⟩ := by
  classical
  letI : Fintype M.val.edgeSet := Fintype.ofFinite _
  let s := canonicalListing (matchingPairing label M)
  let edge (i : Fin n) : M.val.edgeSet :=
    ⟨s(label.symm (s (first i)), label.symm (s (second i))), canonical_adj label M i⟩
  have hinj : Function.Injective edge := by
    intro i j hij
    rcases Sym2.eq_iff.mp (congrArg Subtype.val hij) with h | h
    · have he := s.injective (label.symm.injective h.1)
      exact Fin.ext (by have := congrArg Fin.val he; simpa [first] using this)
    · have he := s.injective (label.symm.injective h.1)
      have hv := congrArg Fin.val he
      simp only [first, second] at hv
      omega
  have hsurj : Function.Surjective edge := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      obtain ⟨i, hi | hi⟩ := index_cases (s.symm (label x))
      · have hx : label.symm (s (first i)) = x := by rw [← hi]; simp
        have ha := canonical_adj label M i
        change M.val.Adj (label.symm (s (first i))) (label.symm (s (second i))) at ha
        rw [hx] at ha
        have hy := M.property.1.eq_of_adj_left ha he
        exact ⟨i, Subtype.ext (Sym2.eq_iff.mpr (Or.inl ⟨hx, hy⟩))⟩
      · have hx : label.symm (s (second i)) = x := by rw [← hi]; simp
        have ha := (canonical_adj label M i).symm
        change M.val.Adj (label.symm (s (second i))) (label.symm (s (first i))) at ha
        rw [hx] at ha
        have hy := M.property.1.eq_of_adj_left ha he
        exact ⟨i, Subtype.ext (Sym2.eq_iff.mpr (Or.inr ⟨hy, hx⟩))⟩
  exact (Fintype.prod_bijective edge ⟨hinj, hsurj⟩ _
    (fun e : M.val.edgeSet => w ⟨e.val, M.val.edgeSet_subset e.property⟩)
    (fun _ => rfl)).symm

private theorem supported_iff_listing (label : V ≃ Fin (2 * n)) (p : P n) :
    Supported (G := G) label p ↔ ∀ i : Fin n,
      G.Adj (label.symm (canonicalListing p (first i)))
        (label.symm (canonicalListing p (second i))) := by
  constructor
  · intro hp i
    have hm : p.val (canonicalListing p (first i)) = canonicalListing p (second i) :=
      canonical_mate p i
    simpa only [hm] using hp (canonicalListing p (first i))
  · intro hp x
    let c := canonicalListing p
    obtain ⟨i, hi | hi⟩ := index_cases (c.symm x)
    · have hx : c (first i) = x := by rw [← hi]; simp
      have hm : p.val (c (first i)) = c (second i) := canonical_mate p i
      rw [← hx, hm]
      exact hp i
    · have hx : c (second i) = x := by rw [← hi]; simp
      have hm : p.val (c (second i)) = c (first i) := by
        have hm : p.val (c (first i)) = c (second i) := canonical_mate p i
        rw [← hm, p.property.1]
      rw [← hx, hm]
      exact (hp i).symm

private noncomputable def pairingTerm {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) (p : P n) : R :=
  ((Equiv.Perm.sign (canonicalListing p) : ℤ) : R) *
    ∏ i : Fin n, A (canonicalListing p (first i)) (canonicalListing p (second i))

private theorem pfaffian_pairings [Fintype (P n)] {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) : pfaffian A = ∑ p : P n, pairingTerm A p := by
  classical
  unfold pfaffian
  rw [Finset.sum_subtype (normalizedListings n) (fun _ => Iff.rfl)]
  apply Fintype.sum_equiv (listingEquiv n)
  intro s
  have hc := congrArg Subtype.val ((listingEquiv n).left_inv s)
  change canonicalListing ((listingEquiv n) s) = s.val at hc
  simp only [pairingTerm, hc, first, second]

private theorem unsupported_term_zero {R : Type*} [CommRing R]
    (label : V ≃ Fin (2 * n)) (epsilon : G.Dart → ZMod 2) (w : G.edgeSet → R)
    (p : P n) (hp : ¬ Supported (G := G) label p) :
    pairingTerm (orientedMatrix label epsilon w) p = 0 := by
  classical
  rw [supported_iff_listing] at hp
  push Not at hp
  obtain ⟨i, hi⟩ := hp
  unfold pairingTerm
  have hz : orientedMatrix label epsilon w
      (canonicalListing p (first i)) (canonicalListing p (second i)) = 0 := by
    simp [orientedMatrix, hi]
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]

private theorem actual_matching_term [Fintype V] {R : Type*} [CommRing R]
    (label : V ≃ Fin (2 * n)) (epsilon : G.Dart → ZMod 2) (w : G.edgeSet → R)
    (M : {M : G.Subgraph // M.IsPerfectMatching}) :
    pairingTerm (orientedMatrix label epsilon w) (matchingPairing label M) =
      ((matchingTau label epsilon M : ℤ) : R) * matchingWeight w M.val := by
  classical
  have hentry (i : Fin n) : orientedMatrix label epsilon w
      (canonicalListing (matchingPairing label M) (first i))
      (canonicalListing (matchingPairing label M) (second i)) =
      ((dartSign epsilon ⟨(label.symm (canonicalListing (matchingPairing label M) (first i)),
        label.symm (canonicalListing (matchingPairing label M) (second i))),
        M.val.adj_sub (canonical_adj label M i)⟩ : ℤ) : R) *
        w ⟨s(label.symm (canonicalListing (matchingPairing label M) (first i)),
          label.symm (canonicalListing (matchingPairing label M) (second i))),
          M.val.adj_sub (canonical_adj label M i)⟩ := by
    have hd : canonicalListing (matchingPairing label M) (first i) ≠
        canonicalListing (matchingPairing label M) (second i) :=
      fun h => (canonical_adj label M i).ne (congrArg label.symm h)
    have hg : G.Adj
        (label.symm (canonicalListing (matchingPairing label M) (first i)))
        (label.symm (canonicalListing (matchingPairing label M) (second i))) :=
      M.val.adj_sub (canonical_adj label M i)
    simp only [orientedMatrix, ite_eq_right hd, dite_eq_left hg]
  unfold pairingTerm
  simp_rw [hentry]
  rw [Finset.prod_mul_distrib, matchingWeight_listing label w M]
  unfold matchingTau
  push_cast
  rw [mul_assoc]
  rfl

private theorem pfaffian_matching_sum [Fintype V] {R : Type*} [CommRing R]
    (label : V ≃ Fin (2 * n)) (epsilon : G.Dart → ZMod 2) (w : G.edgeSet → R) :
    letI : Fintype {M : G.Subgraph // M.IsPerfectMatching} := Fintype.ofFinite _
    pfaffian (orientedMatrix label epsilon w) =
      ∑ M : {M : G.Subgraph // M.IsPerfectMatching},
        ((matchingTau label epsilon M : ℤ) : R) * matchingWeight w M.val := by
  classical
  letI : Fintype (P n) := Fintype.ofFinite _
  letI : Fintype {M : G.Subgraph // M.IsPerfectMatching} := Fintype.ofFinite _
  rw [pfaffian_pairings]
  let term := pairingTerm (orientedMatrix label epsilon w)
  calc
    ∑ p : P n, term p =
        ∑ p ∈ Finset.univ.filter (Supported (G := G) label), term p := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p _ hp
      exact unsupported_term_zero label epsilon w p (by simpa using hp)
    _ = ∑ p : {p : P n // Supported (G := G) label p}, term p.val :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      apply Fintype.sum_equiv (supportedEquiv (G := G) label)
      intro p
      have hp := pairing_supportedMatching label p.val p.property
      rw [← hp]
      exact actual_matching_term label epsilon w _

/-- This integer unit depends only on the graph, vertex enumeration and orientation. -/
noncomputable def orientationUnit (label : V ≃ Fin (2 * n)) (epsilon : G.Dart → ZMod 2) : ℤˣ := by
  classical
  exact if h : Nonempty {M : G.Subgraph // M.IsPerfectMatching} then
    matchingTau label epsilon h.some else 1

/-- The independently defined standard Pfaffian equals a fixed integer unit times the
actual edge-once matching partition function over every commutative coefficient ring. -/
theorem weighted_pfaffian_identity [Fintype V] {R : Type*} [CommRing R]
    (label : V ≃ Fin (2 * n)) {epsilon : G.Dart → ZMod 2}
    (he : Reverses epsilon) (ho : NiceOdd epsilon) (w : G.edgeSet → R) :
    pfaffian (orientedMatrix label epsilon w) =
      ((orientationUnit label epsilon : ℤ) : R) * partitionFunction w := by
  classical
  rw [pfaffian_matching_sum]
  unfold partitionFunction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  have ht : matchingTau label epsilon M = orientationUnit label epsilon := by
    unfold orientationUnit
    rw [dite_eq_left (show Nonempty {M : G.Subgraph // M.IsPerfectMatching} from ⟨M⟩)]
    exact niceOdd_matching_tau_eq label he ho M _
  rw [ht]

end D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching
