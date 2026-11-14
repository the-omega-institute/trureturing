/- GID: D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual representative maxima, C4-free thresholds and support rigidity. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularCompensation
import D5.S3.Combinatorics.Graph.SubQuorum.DissociationColoring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card

/-! General representative proofs from Sahbi source revision
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
All declarations concern arbitrary graph predicates, exact finite suprema or
symbolic bounds and their graph-level derivation. No finite instance table,
bounded enumeration, checker, or conditional arithmetic interface is supplied
as new content in this module: utility fields are not-applicable(kind=none).
The actual finite Pappus/Heawood instances remain in C4FreeRepresentatives.
The split preserves every mathematical statement and proof body. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
open StarFormingDissociationRefutation
open StarForming
open scoped BigOperators

def NoFourCycle {Vertex : Type} (adjacency : Vertex → Vertex → Prop) : Prop :=
  ∀ first second left right, first ≠ second → left ≠ right →
    first ≠ left → first ≠ right → second ≠ left → second ≠ right →
    adjacency first left → adjacency first right →
    adjacency second left → adjacency second right → False

theorem neighbor_pair_unique_owner {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} (hfree : NoFourCycle adjacency)
    (first second left right : Vertex) (hpair : left ≠ right)
    (hfirstLeft : first ≠ left) (hfirstRight : first ≠ right)
    (hsecondLeft : second ≠ left) (hsecondRight : second ≠ right)
    (hfirstEdge : adjacency first left) (hfirstOther : adjacency first right)
    (hsecondEdge : adjacency second left) (hsecondOther : adjacency second right) :
    first = second := by
  apply Classical.byContradiction
  intro hdifferent
  exact hfree first second left right hdifferent hpair hfirstLeft hfirstRight
    hsecondLeft hsecondRight hfirstEdge hfirstOther hsecondEdge hsecondOther

/-- Distinct selected owners receive disjoint sets of ordered neighbor pairs.
This is the unbounded graph-to-counting step behind the C4-free packing bound. -/
theorem pair_packing {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hfree : NoFourCycle G.Adj)
    (U B : Finset V) (hUB : Disjoint U B) :
    (∑ u ∈ U, ((B.filter (G.Adj u)).card * ((B.filter (G.Adj u)).card - 1))) ≤
      B.card * (B.card - 1) := by
  classical
  let Q : V → Finset (V × V) := fun u => (B.filter (G.Adj u)).offDiag
  have hdisj : (↑U : Set V).PairwiseDisjoint Q := by
    intro u hu v hv hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := Finset.mem_offDiag.mp hp
    have hq' := Finset.mem_offDiag.mp hq
    have hleftB := (Finset.mem_filter.mp hp'.1).1
    have hrightB := (Finset.mem_filter.mp hp'.2.1).1
    have unequal (a : V) (ha : a ∈ U) (b : V) (hb : b ∈ B) : a ≠ b := by
      intro he
      exact Finset.disjoint_left.mp hUB ha (he ▸ hb)
    exact hne (neighbor_pair_unique_owner hfree u v p.1 p.2 hp'.2.2
      (unequal u hu p.1 hleftB) (unequal u hu p.2 hrightB)
      (unequal v hv p.1 hleftB) (unequal v hv p.2 hrightB)
      (Finset.mem_filter.mp hp'.1).2 (Finset.mem_filter.mp hp'.2.1).2
      (Finset.mem_filter.mp hq'.1).2 (Finset.mem_filter.mp hq'.2.1).2)
  have hsub : U.biUnion Q ⊆ B.offDiag := by
    intro p hp
    obtain ⟨u,hu,hp⟩ := Finset.mem_biUnion.mp hp
    have hh := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr ⟨(Finset.mem_filter.mp hh.1).1,
      (Finset.mem_filter.mp hh.2.1).1,hh.2.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hc
  simpa only [Q,Finset.offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one] using hc

/-- Uniform lower neighborhood capacity is summed over actual vertices, with
pair ownership preventing reuse. -/
theorem pair_packing_lower {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hfree : NoFourCycle G.Adj)
    (U B : Finset V) (hUB : Disjoint U B) (k : ℕ)
    (hk : ∀ u ∈ U, k ≤ (B.filter (G.Adj u)).card) :
    k * (k - 1) * U.card ≤ B.card * (B.card - 1) := by
  calc
    _ = ∑ _u ∈ U, k * (k - 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ U, (B.filter (G.Adj u)).card * ((B.filter (G.Adj u)).card - 1) := by
      apply Finset.sum_le_sum
      intro u hu
      exact Nat.mul_le_mul (hk u hu) (Nat.sub_le_sub_right (hk u hu) 1)
    _ ≤ _ := pair_packing G hfree U B hUB

private theorem packing_forces_many_unused (capacity unused excess : Int)
    (hcapacity : 0 < capacity) (hunused : 0 ≤ unused) (hexcess : 0 < excess)
    (hpacking : capacity * (unused + excess) ≤ unused * (unused - 1)) :
    capacity + 2 ≤ unused := by
  apply Classical.byContradiction
  intro hsmall
  have hfactor : unused - 1 ≤ capacity := by omega
  have hproduct := Int.mul_le_mul_of_nonneg_left hfactor hunused
  have hpositive : 0 < capacity * excess := Int.mul_pos hcapacity hexcess
  have hexpand : capacity * (unused + excess) =
      unused * capacity + capacity * excess := by
    simp [Int.mul_add, Int.mul_comm]
  omega

private theorem positive_excess_size_threshold (capacity left right matching excess order : Int)
    (hcapacity : 0 < capacity) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hmatching : 0 ≤ matching) (hexcess : 0 < excess)
    (hleftPacking : capacity * (left + excess) ≤ left * (left - 1))
    (hrightPacking : capacity * (right + excess) ≤ right * (right - 1))
    (hpartition : matching + left + right + excess = order) :
    2 * capacity + 5 ≤ order := by
  have hleftBound := packing_forces_many_unused capacity left excess
    hcapacity hleft hexcess hleftPacking
  have hrightBound := packing_forces_many_unused capacity right excess
    hcapacity hright hexcess hrightPacking
  omega

private theorem no_positive_excess_below_threshold (capacity left right matching excess order : Int)
    (hcapacity : 0 < capacity) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hmatching : 0 ≤ matching) (hexcess : 0 < excess)
    (hleftPacking : capacity * (left + excess) ≤ left * (left - 1))
    (hrightPacking : capacity * (right + excess) ≤ right * (right - 1))
    (hpartition : matching + left + right + excess = order)
    (horder : order ≤ 2 * capacity + 4) : False := by
  have hthreshold := positive_excess_size_threshold capacity left right matching excess order
    hcapacity hleft hright hmatching hexcess hleftPacking hrightPacking hpartition
  omega

private theorem positive_excess_matching_budget (capacity left right matching excess order : Int)
    (hcapacity : 0 < capacity) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hexcess : 0 < excess)
    (hleftPacking : capacity * (left + excess) ≤ left * (left - 1))
    (hrightPacking : capacity * (right + excess) ≤ right * (right - 1))
    (hpartition : matching + left + right + excess = order) :
    matching + excess ≤ order - 2 * capacity - 4 := by
  have hleftBound := packing_forces_many_unused capacity left excess
    hcapacity hleft hexcess hleftPacking
  have hrightBound := packing_forces_many_unused capacity right excess
    hcapacity hright hexcess hrightPacking
  omega

private theorem zero_excess_packing (capacity unused : Int) (hunused : 0 ≤ unused)
    (hpacking : capacity * unused ≤ unused * (unused - 1)) :
    unused = 0 ∨ capacity + 1 ≤ unused := by
  by_cases hzero : unused = 0
  · exact Or.inl hzero
  · apply Or.inr
    apply Classical.byContradiction
    intro hsmall
    have hfactor : unused - 1 ≤ capacity - 1 := by omega
    have hproduct := Int.mul_le_mul_of_nonneg_left hfactor hunused
    have hexpand : unused * (capacity - 1) = capacity * unused - unused := by
      simp [Int.mul_sub, Int.mul_comm]
    omega

private theorem optimal_support_one_side (capacity left right matching order : Int)
    (hleft : 0 ≤ left) (hright : 0 ≤ right) (hmatching : 0 ≤ matching)
    (hleftPacking : capacity * left ≤ left * (left - 1))
    (hrightPacking : capacity * right ≤ right * (right - 1))
    (hpartition : matching + left + right = order)
    (horder : order ≤ 2 * capacity + 1) : left = 0 ∨ right = 0 := by
  rcases zero_excess_packing capacity left hleft hleftPacking with hzero | hbound
  · exact Or.inl hzero
  · rcases zero_excess_packing capacity right hright hrightPacking with hzero | hother
    · exact Or.inr hzero
    · omega

section Representatives
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Endpoint support of an oriented list of matching edges. The feasibility
condition excludes repeated or reversed copies sharing any endpoint. -/
def endpoints (M : Finset (V × V)) : Finset V := M.biUnion (fun e => {e.1,e.2})

/-- Sahbi's actual representative pair: matching edges, disjoint singleton
vertices, and induced degree at most one at every singleton. Matching endpoints
have no imposed degree restriction in the occupied induced graph. -/
structure Feasible (T : Finset V) (M : Finset (V × V)) : Prop where
  edge : ∀ e ∈ M, G.Adj e.1 e.2
  matching : (↑M : Set (V × V)).PairwiseDisjoint (fun e => ({e.1,e.2} : Finset V))
  disjoint : Disjoint T (endpoints M)
  capacity : ∀ v ∈ T, ((T ∪ endpoints M).filter (G.Adj v)).card ≤ 1

/-- The exact finite representative maximum, over all singleton/matching pairs. -/
noncomputable def Omega : ℕ := by
  classical
  exact ((Finset.univ.powerset.product Finset.univ.powerset).filter
    (fun p : Finset V × Finset (V × V) => Feasible G p.1 p.2)).sup
      (fun p => p.1.card + p.2.card)

theorem objective_le_omega (T : Finset V) (M : Finset (V × V)) (h : Feasible G T M) :
    T.card + M.card ≤ Omega G := by
  classical
  have hm : (T,M) ∈ (Finset.univ.powerset.product Finset.univ.powerset).filter
      (fun p : Finset V × Finset (V × V) => Feasible G p.1 p.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨by simp,by simp⟩,h⟩
  exact Finset.le_sup (f := fun p : Finset V × Finset (V × V) => p.1.card + p.2.card) hm

theorem omega_upper_of_objective_bound (n : ℕ)
    (h : ∀ T M, Feasible G T M → T.card + M.card ≤ n) : Omega G ≤ n := by
  classical
  apply Finset.sup_le
  intro p hp
  exact h p.1 p.2 (Finset.mem_filter.mp hp).2

/-- Every actual dissociation selection is a feasible empty-matching pair. -/
theorem dissociation_feasible (T : Finset V) (hT : IsKIndependent G 2 T) :
    Feasible G T ∅ := by
  refine ⟨by simp,by simp,by simp [endpoints],?_⟩
  intro v hv
  simpa only [endpoints,Finset.biUnion_empty,Finset.union_empty] using
    (Nat.lt_succ_iff.mp (hT v hv))

private theorem endpoints_side_card (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (c : Bool) :
    ((endpoints M).filter (fun v => color v = c)).card = M.card := by
  classical
  unfold endpoints
  rw [Finset.filter_biUnion]
  have hd : (↑M : Set (V × V)).PairwiseDisjoint
      (fun e => ({e.1,e.2} : Finset V).filter (fun v => color v = c)) := by
    intro e he f hff hne
    exact (hf.matching he hff hne).mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
  rw [Finset.card_biUnion hd]
  have hcard (e : V × V) (he : e ∈ M) :
      (({e.1,e.2} : Finset V).filter (fun v => color v = c)).card = 1 := by
    have hc := hcolor _ _ (hf.edge e he)
    cases ha : color e.1 <;> cases hb : color e.2 <;> cases c <;>
      simp_all [Finset.filter_insert,Finset.filter_singleton]
  calc
    _ = ∑ _e ∈ M, 1 := Finset.sum_congr rfl (fun e he => hcard e he)
    _ = _ := by simp

private noncomputable def unusedSide (T : Finset V) (M : Finset (V × V))
    (color : V → Bool) (c : Bool) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ∉ T ∪ endpoints M ∧ color v = c)

private theorem side_partition (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) (c : Bool) :
    (T.filter (fun v => color v = c)).card + M.card +
      (unusedSide T M color c).card = (Finset.univ.filter (fun v => color v = c)).card := by
  classical
  let Tc := T.filter (fun v => color v = c)
  let Ec := (endpoints M).filter (fun v => color v = c)
  have he : Tc ∪ Ec ∪ unusedSide T M color c =
      Finset.univ.filter (fun v => color v = c) := by
    ext v
    simp only [Tc,Ec,unusedSide,Finset.mem_union,Finset.mem_filter,
      Finset.mem_univ,true_and]
    tauto
  have h1 : Disjoint Tc Ec := hf.disjoint.mono (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)
  have h2 : Disjoint (Tc ∪ Ec) (unusedSide T M color c) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hn := (Finset.mem_filter.mp hw).2.1
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hn (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hv).1))
    · exact hn (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mp hv).1))
  have hc := congrArg Finset.card he
  rw [Finset.card_union_of_disjoint h2,Finset.card_union_of_disjoint h1] at hc
  rw [endpoints_side_card G color hcolor T M hf c] at hc
  exact hc

private theorem unused_neighbor_capacity (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M)
    (D : ℕ) (hr : ∀ v, DegreeCapacity.degree G v = D)
    (c : Bool) (v : V) (hv : v ∈ T) (hvc : color v ≠ c) :
    D - 1 ≤ ((unusedSide T M color c).filter (G.Adj v)).card := by
  classical
  let A := T ∪ endpoints M
  let B := unusedSide T M color c
  have hwc (w : V) (hvw : G.Adj v w) : color w = c := by
    have hc := hcolor v w hvw
    cases ha : color v <;> cases hb : color w <;> cases c <;> simp_all
  have he : Finset.univ.filter (G.Adj v) =
      A.filter (G.Adj v) ∪ B.filter (G.Adj v) := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,B,unusedSide]
    constructor
    · intro hadj
      by_cases hw : w ∈ A
      · exact Or.inl ⟨hw,hadj⟩
      · exact Or.inr ⟨by simpa only [Finset.mem_filter,Finset.mem_univ,true_and,A,Finset.mem_union]
            using And.intro hw (hwc w hadj),hadj⟩
    · rintro (⟨_,h⟩ | ⟨_,h⟩) <;> exact h
  have hd : Disjoint (A.filter (G.Adj v)) (B.filter (G.Adj v)) := by
    apply Finset.disjoint_left.mpr
    intro w hw hh
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).2.1
      (Finset.mem_filter.mp hw).1
  have hc := congrArg Finset.card he
  rw [Finset.card_union_of_disjoint hd] at hc
  have hdeg := hr v
  change (Finset.univ.filter (G.Adj v)).card = D at hdeg
  have hcap := hf.capacity v hv
  change (A.filter (G.Adj v)).card ≤ 1 at hcap
  change D - 1 ≤ (B.filter (G.Adj v)).card
  omega

private theorem representative_pack (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (T : Finset V) (M : Finset (V × V))
    (hf : Feasible G T M) (D : ℕ) (hr : ∀ v, DegreeCapacity.degree G v = D)
    (c : Bool) :
    (D - 1) * (D - 2) * (T.filter (fun v => color v ≠ c)).card ≤
      (unusedSide T M color c).card * ((unusedSide T M color c).card - 1) := by
  classical
  have hdisj : Disjoint (T.filter (fun v => color v ≠ c)) (unusedSide T M color c) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_filter.mp hw).2.1
      (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hv).1))
  have h := pair_packing_lower G hfree (T.filter (fun v => color v ≠ c))
    (unusedSide T M color c) hdisj (D - 1) (by
      intro v hv
      exact unused_neighbor_capacity G color hcolor T M hf D hr c v
        (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2)
  simpa only [Nat.sub_sub] using h

private theorem mul_pred_cast (b : ℕ) : ((b * (b - 1) : ℕ) : ℤ) = (b : ℤ) * (b - 1) := by
  by_cases hb : b = 0
  · simp [hb]
  · rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ b)]
    simp

/-- Positive representative excess forces the exact matching/excess budget,
obtained from both actual C4-free pair counts. -/
theorem positive_excess_budget (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D)
    (hr : ∀ v, DegreeCapacity.degree G v = D)
    (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M)
    (hexcess : N < T.card + M.card) :
    (M.card : ℤ) + ((T.card : ℤ) + M.card - N) ≤
      (N : ℤ) - 2 * ((D - 1) * (D - 2) : ℕ) - 4 := by
  classical
  let b0 := (unusedSide T M color false).card
  let b1 := (unusedSide T M color true).card
  let t0 := (T.filter (fun v => color v = false)).card
  let t1 := (T.filter (fun v => color v = true)).card
  let a := (D - 1) * (D - 2)
  have ha : 0 < a := Nat.mul_pos (by omega) (by omega)
  have hp0 := side_partition G color hcolor T M hf false
  have hp1 := side_partition G color hcolor T M hf true
  rw [hsides] at hp0 hp1
  change t0 + M.card + b0 = N at hp0
  change t1 + M.card + b1 = N at hp1
  have ht : t0 + t1 = T.card := by
    have h : T.filter (fun v => color v = true) = T.filter (fun v => ¬ color v = false) := by
      ext v
      cases color v <;> simp
    change (T.filter (fun v => color v = false)).card +
      (T.filter (fun v => color v = true)).card = T.card
    rw [h]
    exact Finset.card_filter_add_card_filter_not _
  have hp0' : (t0 : ℤ) + M.card + b0 = N := by exact_mod_cast hp0
  have hp1' : (t1 : ℤ) + M.card + b1 = N := by exact_mod_cast hp1
  have ht' : (t0 : ℤ) + t1 = T.card := by exact_mod_cast ht
  have h0 := representative_pack G color hcolor hfree T M hf D hr false
  have h1 := representative_pack G color hcolor hfree T M hf D hr true
  have hnfalse (v : V) : (color v ≠ false) ↔ color v = true := by cases color v <;> simp
  have hntrue (v : V) : (color v ≠ true) ↔ color v = false := by cases color v <;> simp
  simp_rw [hnfalse] at h0
  simp_rw [hntrue] at h1
  change a * t1 ≤ b0 * (b0 - 1) at h0
  change a * t0 ≤ b1 * (b1 - 1) at h1
  have h0' : (a : ℤ) * t1 ≤ (b0 : ℤ) * (b0 - 1) := by
    have hh : ((a * t1 : ℕ) : ℤ) ≤ ((b0 * (b0 - 1) : ℕ) : ℤ) := by exact_mod_cast h0
    rw [mul_pred_cast] at hh
    simpa only [Nat.cast_mul] using hh
  have h1' : (a : ℤ) * t0 ≤ (b1 : ℤ) * (b1 - 1) := by
    have hh : ((a * t0 : ℕ) : ℤ) ≤ ((b1 * (b1 - 1) : ℕ) : ℤ) := by exact_mod_cast h1
    rw [mul_pred_cast] at hh
    simpa only [Nat.cast_mul] using hh
  apply positive_excess_matching_budget (a : ℤ) b0 b1 M.card
    ((T.card : ℤ) + M.card - N) N
    (by exact_mod_cast ha) (by exact Int.natCast_nonneg _) (by exact Int.natCast_nonneg _) (by
      have h : (N : ℤ) < (T.card : ℤ) + M.card := by exact_mod_cast hexcess
      omega)
  · have he : (b0 : ℤ) + ((T.card : ℤ) + M.card - N) = t1 := by omega
    rwa [he]
  · have he : (b1 : ℤ) + ((T.card : ℤ) + M.card - N) = t0 := by omega
    rwa [he]
  · omega

/-- Under the exact source size threshold every actual representative objective
is at most one bipartition side. No connectedness hypothesis is needed. -/
theorem objective_threshold (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D)
    (hr : ∀ v, DegreeCapacity.degree G v = D)
    (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N)
    (hN : N ≤ 2 * (D - 1) * (D - 2) + 4)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) :
    T.card + M.card ≤ N := by
  by_contra hn
  have h := positive_excess_budget G color hcolor hfree D N hD hr hsides T M hf (by omega)
  have hn' : (N : ℤ) ≤ 2 * ((D - 1) * (D - 2) : ℕ) + 4 := by
    exact_mod_cast (show N ≤ 2 * ((D - 1) * (D - 2)) + 4 by
      simpa only [Nat.mul_assoc] using hN)
  omega

/-- The same packing gives the full upper envelope, without the threshold
hypothesis. This keeps positive excess and matching costs distinct. -/
theorem objective_general_bound (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D)
    (hr : ∀ v, DegreeCapacity.degree G v = D)
    (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M) :
    T.card + M.card ≤ max N (2*N - 2*((D-1)*(D-2)) - 4) := by
  by_cases he : T.card + M.card ≤ N
  · exact he.trans (le_max_left _ _)
  · have hh := positive_excess_budget G color hcolor hfree D N hD hr hsides T M hf
      (by omega)
    have hu : T.card + M.card ≤ 2*N - 2*((D-1)*(D-2)) - 4 := by omega
    exact hu.trans (le_max_right _ _)

/-- At the first possible order, excess one forces the matching part empty. -/
theorem first_excess_matching_empty (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D)
    (hr : ∀ v, DegreeCapacity.degree G v = D)
    (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N)
    (hN : N = 2*((D-1)*(D-2))+5)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M)
    (hc : T.card + M.card = N+1) : M = ∅ := by
  have hh := positive_excess_budget G color hcolor hfree D N hD hr hsides T M hf
    (by omega)
  apply Finset.card_eq_zero.mp
  omega

/-- Objective N forces each actual unused-side count to vanish or be at
least (D-1)(D-2)+1. There is no assertion that matching edges vanish. -/
theorem zero_excess_unused (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (D N : ℕ)
    (hr : ∀ v, DegreeCapacity.degree G v = D)
    (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M)
    (hc : T.card + M.card = N) (c : Bool) :
    (unusedSide T M color c).card = 0 ∨
      (D-1)*(D-2)+1 ≤ (unusedSide T M color c).card := by
  classical
  have hp := side_partition G color hcolor T M hf c
  rw [hsides] at hp
  have ht : (T.filter (fun v => color v = c)).card +
      (T.filter (fun v => color v ≠ c)).card = T.card :=
    Finset.card_filter_add_card_filter_not _
  have he : (T.filter (fun v => color v ≠ c)).card =
      (unusedSide T M color c).card := by omega
  have hh := representative_pack G color hcolor hfree T M hf D hr c
  rw [he] at hh
  have hi : (((D-1)*(D-2) : ℕ) : ℤ) * (unusedSide T M color c).card ≤
      ((unusedSide T M color c).card : ℤ) * ((unusedSide T M color c).card - 1) := by
    have hh' : (((D-1)*(D-2)*(unusedSide T M color c).card : ℕ) : ℤ) ≤
        (((unusedSide T M color c).card * ((unusedSide T M color c).card-1) : ℕ) : ℤ) :=
      by exact_mod_cast hh
    rw [mul_pred_cast] at hh'
    simpa only [Nat.cast_mul] using hh'
  rcases zero_excess_packing (((D-1)*(D-2) : ℕ) : ℤ)
    (unusedSide T M color c).card (Int.natCast_nonneg _) hi with hz | hb
  · left; exact_mod_cast hz
  · right; exact_mod_cast hb

/-- Every objective-N representative below the support threshold has all
singletons in one side and occupies every vertex of that side. -/
theorem objective_one_side_support (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (D N : ℕ)
    (hr : ∀ v, DegreeCapacity.degree G v = D)
    (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N)
    (hN : N ≤ 2*((D-1)*(D-2))+1)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M)
    (hc : T.card + M.card = N) :
    ∃ c : Bool, (∀ v ∈ T, color v = c) ∧
      (∀ v, color v = c → v ∈ T ∪ endpoints M) := by
  classical
  have h0 := zero_excess_unused G color hcolor hfree D N hr hsides T M hf hc false
  have h1 := zero_excess_unused G color hcolor hfree D N hr hsides T M hf hc true
  have hp0 := side_partition G color hcolor T M hf false
  have hp1 := side_partition G color hcolor T M hf true
  rw [hsides] at hp0 hp1
  have ht : (T.filter (fun v => color v = false)).card +
      (T.filter (fun v => color v = true)).card = T.card := by
    have he : T.filter (fun v => color v = true) =
        T.filter (fun v => ¬ color v = false) := by ext v; cases color v <;> simp
    rw [he]
    exact Finset.card_filter_add_card_filter_not _
  have hz : (unusedSide T M color false).card = 0 ∨
      (unusedSide T M color true).card = 0 := by
    rcases h0 with h0 | h0
    · exact Or.inl h0
    · rcases h1 with h1 | h1
      · exact Or.inr h1
      · omega
  rcases hz with hz | hz
  · refine ⟨false,?_,?_⟩
    · have he : T.filter (fun v => color v = true) = ∅ := Finset.card_eq_zero.mp (by omega)
      intro v hv
      cases hc' : color v
      · rfl
      · have hh : v ∈ T.filter (fun v => color v = true) := Finset.mem_filter.mpr ⟨hv,hc'⟩
        rw [he] at hh
        exact (Finset.notMem_empty _ hh).elim
    · intro v hv
      by_contra hn
      have hh : v ∈ unusedSide T M color false := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn,hv⟩
      rw [Finset.card_eq_zero.mp hz] at hh
      exact Finset.notMem_empty _ hh
  · refine ⟨true,?_,?_⟩
    · have he : T.filter (fun v => color v = false) = ∅ := Finset.card_eq_zero.mp (by omega)
      intro v hv
      cases hc' : color v
      · have hh : v ∈ T.filter (fun v => color v = false) := Finset.mem_filter.mpr ⟨hv,hc'⟩
        rw [he] at hh
        exact (Finset.notMem_empty _ hh).elim
      · rfl
    · intro v hv
      by_contra hn
      have hh : v ∈ unusedSide T M color true := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn,hv⟩
      rw [Finset.card_eq_zero.mp hz] at hh
      exact Finset.notMem_empty _ hh

end Representatives


section RepresentativeReduction
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
open DoubleStarGrafting

/-- Sahbi's representative reduction uses the actual finite palette. Each
edge-containing class supplies one matching edge; each remaining class supplies
one singleton whose entire colored neighborhood has degree at most one. -/
theorem coloring_representatives {C : Type} [DecidableEq C] (c : V → Option C)
    (hc : IsSubQuorum G c) :
    ∃ T : Finset V, ∃ M : Finset (V × V), Feasible G T M ∧
      T.card + M.card = (palette c Finset.univ).card ∧
      (M = ∅ → ∀ v w, c v ≠ none → c w = c v → ¬ G.Adj v w) := by
  classical
  let P := palette c Finset.univ
  let EdgeClass : ↥P → Prop := fun r => ∃ v w, c v = r.val ∧ c w = r.val ∧ G.Adj v w
  have hr (r : ↥P) : ∃ v, c v = r.val ∧ c v ≠ none := by
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp r.property
    exact ⟨v,he,(Finset.mem_filter.mp hv).2⟩
  have hq (r : ↥P) : ∃ q : V × V, c q.1 = r.val ∧ c q.2 = r.val ∧
      (EdgeClass r → G.Adj q.1 q.2) := by
    by_cases he : EdgeClass r
    · obtain ⟨v,w,hv,hw,hadj⟩ := he
      exact ⟨(v,w),hv,hw,fun _ => hadj⟩
    · obtain ⟨v,hv,_⟩ := hr r
      exact ⟨(v,v),hv,hv,fun h => (he h).elim⟩
  choose q hq using hq
  let E := Finset.univ.filter EdgeClass
  let K := Finset.univ \ E
  let T : Finset V := K.image (fun r => (q r).1)
  let M : Finset (V × V) := E.image q
  have hleft : Function.Injective (fun r : ↥P => (q r).1) := by
    intro r s he
    apply Subtype.ext
    exact (hq r).1.symm.trans ((congrArg c he).trans (hq s).1)
  have hpair : Function.Injective q := by
    intro r s he
    exact hleft (congrArg Prod.fst he)
  have hcolor (r : ↥P) (v : V) (hv : v ∈ ({(q r).1,(q r).2} : Finset V)) :
      c v = r.val := by
    rcases Finset.mem_insert.mp hv with he | he
    · exact he ▸ (hq r).1
    · exact (Finset.mem_singleton.mp he) ▸ (hq r).2.1
  have hnonempty (r : ↥P) : r.val ≠ none := by
    obtain ⟨v,hv,hn⟩ := hr r
    exact hv ▸ hn
  have hocc : T ∪ endpoints M ⊆ coloredSupport c Finset.univ := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
      rw [(hq r).1]
      exact hnonempty r
    · obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp he
      rw [hcolor r v hv]
      exact hnonempty r
  refine ⟨T,M,?_,?_⟩
  · refine ⟨?_,?_,?_,?_⟩
    · intro e he
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp he
      exact (hq r).2.2 (Finset.mem_filter.mp hr).2
    · intro e he f hf hne
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hf
      apply Finset.disjoint_left.mpr
      intro v hv hw
      have heq : r = s := Subtype.ext ((hcolor r v hv).symm.trans (hcolor s v hw))
      exact hne (congrArg q heq)
    · apply Finset.disjoint_left.mpr
      intro v hv hw
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp he
      have heq : r = s := Subtype.ext ((hq r).1.symm.trans (hcolor s (q r).1 hv))
      exact (Finset.mem_sdiff.mp hr).2 (heq.symm ▸ hs)
    · intro v hv
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
      have hnot : ¬ EdgeClass r := by
        intro he
        exact (Finset.mem_sdiff.mp hr).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
      have hsame : ((Finset.univ.filter (G.Adj (q r).1)).filter
          (fun w => c w = c (q r).1)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro w hw he
        exact hnot ⟨(q r).1,w,(hq r).1,he.trans (hq r).1,(Finset.mem_filter.mp hw).2⟩
      have hh := hc (q r).1 (by rw [(hq r).1]; exact hnonempty r)
      have hneigh : @Finset.filter V (G.Adj (q r).1) (fun _ => Classical.propDecidable _) Finset.univ =
          Finset.univ.filter (G.Adj (q r).1) := by ext w; simp
      rw [hneigh,hsame] at hh
      simp only [Finset.card_empty] at hh
      have hsub : (T ∪ endpoints M).filter (G.Adj (q r).1) ⊆
          (Finset.univ.filter (G.Adj (q r).1)).filter (fun w => c w ≠ none) := by
        intro w hw
        have hh := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hh.2⟩,(Finset.mem_filter.mp (hocc hh.1)).2⟩
      have hbound := Finset.card_le_card hsub
      omega
  · constructor
    · have hT : T.card = K.card := Finset.card_image_of_injective K hleft
      have hM : M.card = E.card := Finset.card_image_of_injective E hpair
      rw [hT,hM]
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
      simpa only [K,Finset.card_univ,Fintype.card_coe] using h
    · intro hM v w hv he hadj
      let r : ↥P := ⟨c v,Finset.mem_image.mpr ⟨v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩⟩
      have hr : r ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,w,rfl,he,hadj⟩
      have hqm : q r ∈ M := Finset.mem_image.mpr ⟨r,hr,rfl⟩
      rw [hM] at hqm
      exact Finset.notMem_empty _ hqm

/-- Every actual admissible palette is bounded by the representative maximum. -/
theorem palette_le_omega {C : Type} [DecidableEq C] (c : V → Option C)
    (hc : IsSubQuorum G c) : (palette c Finset.univ).card ≤ Omega G := by
  obtain ⟨T,M,hf,he,_⟩ := coloring_representatives G c hc
  rw [← he]
  exact objective_le_omega G T M hf

/-- The canonical sub-quorum maximum obeys the original representative upper
comparison, including the empty graph and empty coloring. -/
theorem psiSq_le_omega : psiSq G ≤ Omega G := by
  classical
  let P : ℕ → Prop := fun n => ∃ c : V → Option ℕ,
    IsSubQuorum G c ∧ (palette c Finset.univ).card = n
  have h0 : P 0 := ⟨fun _ => none,by simp [IsSubQuorum,goodAt],by simp [palette,coloredSupport]⟩
  have hmax : P (psiSq G) := Nat.findGreatest_spec (Nat.zero_le _) h0
  obtain ⟨c,hc,he⟩ := hmax
  rw [← he]
  exact palette_le_omega G c hc

/-- The three distinct parameters satisfy the exact received comparison chain. -/
theorem parameter_comparison : beta G 2 ≤ psiSq G ∧ psiSq G ≤ Omega G :=
  ⟨DissociationColoring.beta_le_psiSq G,psiSq_le_omega G⟩

end RepresentativeReduction

section RepresentativeConsequences
open DoubleStarGrafting
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem side_dissociation (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (c : Bool) :
    IsKIndependent G 2 (Finset.univ.filter (fun v => color v = c)) := by
  classical
  intro v hv
  have he : (Finset.univ.filter (fun v => color v = c)).filter (G.Adj v) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro w hw hadj
    exact hcolor v w hadj ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)
  rw [he]
  simp

/-- The complete three-parameter C4-free threshold follows from actual pair
packing and the representative reduction. The equal-side, regular, C4-free and
D>=3 hypotheses are all retained; connectedness is unnecessary. -/
theorem threshold_parameters (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (D N : ℕ) (hD : 3 ≤ D)
    (hr : ∀ v, DegreeCapacity.degree G v = D)
    (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = N)
    (hN : N ≤ 2 * (D - 1) * (D - 2) + 4) :
    beta G 2 = N ∧ psiSq G = N ∧ Omega G = N := by
  classical
  have hu : Omega G ≤ N := by
    apply Finset.sup_le
    intro p hp
    exact objective_threshold G color hcolor hfree D N hD hr hsides hN
      p.1 p.2 (Finset.mem_filter.mp hp).2
  have hl : N ≤ beta G 2 := by
    rw [← hsides false]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,side_dissociation G color hcolor false⟩)
  have hp := parameter_comparison G
  omega

/-- Projective-plane parameter specialization is valid for every incidence
structure with the exact plane cardinalities, degrees and unique-pair property;
no finite-field or Desarguesian hypothesis occurs. -/
theorem plane_parameter_specialization (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (q : ℕ) (hq : 2 ≤ q)
    (hr : ∀ v, DegreeCapacity.degree G v = q + 1)
    (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = q*q+q+1) :
    beta G 2 = q*q+q+1 ∧ psiSq G = q*q+q+1 ∧ Omega G = q*q+q+1 := by
  apply threshold_parameters G color hcolor hfree (q+1) (q*q+q+1) (by omega) hr hsides
  have h1 : q + 1 - 1 = q := by omega
  have h2 : q + 1 - 2 = q - 1 := by omega
  have h3 : q - 1 + 1 = q := by omega
  rw [h1,h2]
  nlinarith

/-- The support conclusion for every projective plane of order at least three.
It concerns singleton support; the matching part may remain nonempty. -/
theorem plane_optimal_support (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (hfree : NoFourCycle G.Adj) (q : ℕ) (hq : 3 ≤ q)
    (hr : ∀ v, DegreeCapacity.degree G v = q+1)
    (hsides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = q*q+q+1)
    (T : Finset V) (M : Finset (V × V)) (hf : Feasible G T M)
    (hc : T.card+M.card = q*q+q+1) :
    ∃ c : Bool, (∀ v ∈ T, color v = c) ∧
      (∀ v, color v = c → v ∈ T ∪ endpoints M) := by
  apply objective_one_side_support G color hcolor hfree (q+1) (q*q+q+1) hr hsides
    ?_ T M hf hc
  have h1 : q+1-1 = q := by omega
  have h2 : q+1-2 = q-1 := by omega
  have h3 : q-1+1 = q := by omega
  rw [h1,h2]
  nlinarith

end RepresentativeConsequences

end D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
